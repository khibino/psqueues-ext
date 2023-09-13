module Data.OrdPSQ.Tests
    ( tests
    ) where

import           Control.Monad         (replicateM)
import           Data.List             (isInfixOf)
import           Data.Maybe
import           Prelude               hiding (null)
import           Test.QuickCheck
import           Test.HUnit            (Assertion, assert)
import           Test.Tasty            (TestTree)
import           Test.Tasty.HUnit      (testCase)
import           Test.Tasty.QuickCheck (testProperty)

import           Data.OrdPSQ.Internal
import           Data.PSQ.Class.Gen    ()
import           Data.PSQ.Class.Util

--------------------------------------------------------------------------------
-- Index of tests
--------------------------------------------------------------------------------

tests :: [TestTree]
tests =
    [ testCase     "showElem"      test_showElem
    , testCase     "showLTree"     test_showLTree
    , testCase     "invalidLTree"  test_invalidLTree
    , testCase     "balanceErrors" test_balanceErrors
    , testProperty "toAscList"     prop_toAscList
    , testProperty "lookupLE"      prop_lookupLE
    , testProperty "lookupGT"      prop_lookupGT
    , testProperty "lookupLT"      prop_lookupLT
    , testProperty "lookupGE"      prop_lookupGE
    ]


--------------------------------------------------------------------------------
-- Tests the result of 'moduleError' for internal issues
--------------------------------------------------------------------------------

assertModuleError :: String -> String -> a -> Assertion
assertModuleError fun msg = assertErrorCall $ \e -> do
    assert $ fun `isInfixOf` e
    assert $ msg `isInfixOf` e


--------------------------------------------------------------------------------
-- HUnit tests
--------------------------------------------------------------------------------

test_showElem :: Assertion
test_showElem =
    assert $ length (coverShowInstance (E 0 0 'A' :: Elem Int Int Char)) > 0

test_showLTree :: Assertion
test_showLTree = do
    assert $ length (coverShowInstance t1) > 0
    assert $ length (coverShowInstance t2) > 0
    assert $ length (coverShowInstance t3) > 0
  where
    t1, t2, t3 :: LTree Int Int Char
    t1 = Start
    t2 = LLoser 1 e Start 0 Start
    t3 = RLoser 1 e Start 0 Start
    e  = E 0 0 'A'

test_invalidLTree :: Assertion
test_invalidLTree = do
    assertModuleError "left"   "empty" (left   (Start :: LTree Int Int Char))
    assertModuleError "right"  "empty" (right  (Start :: LTree Int Int Char))
    assertModuleError "maxKey" "empty" (maxKey (empty :: OrdPSQ Int Int Char))

test_balanceErrors :: Assertion
test_balanceErrors = do
    assertModuleError "lsingleLeft"  msg (lsingleLeft  0 0 'A' nil 0 nil)
    assertModuleError "rsingleLeft"  msg (rsingleLeft  0 0 'A' nil 0 nil)
    assertModuleError "lsingleRight" msg (lsingleRight 0 0 'A' nil 0 nil)
    assertModuleError "rsingleRight" msg (rsingleRight 0 0 'A' nil 0 nil)
    assertModuleError "ldoubleLeft"  msg (ldoubleLeft  0 0 'A' nil 0 nil)
    assertModuleError "rdoubleLeft"  msg (rdoubleLeft  0 0 'A' nil 0 nil)
    assertModuleError "ldoubleRight" msg (ldoubleRight 0 0 'A' nil 0 nil)
    assertModuleError "rdoubleRight" msg (rdoubleRight 0 0 'A' nil 0 nil)
  where
    nil = Start :: LTree Int Int Char
    msg = "malformed"


--------------------------------------------------------------------------------
-- QuickCheck properties
--------------------------------------------------------------------------------

prop_toAscList :: OrdPSQ Int Int Char -> Bool
prop_toAscList t = isUniqueSorted [k | (k, _, _) <- toAscList t]
  where
    isUniqueSorted (x : y : zs) = x < y && isUniqueSorted (y : zs)
    isUniqueSorted [_]          = True
    isUniqueSorted []           = True

---

rangeElems :: Gen [Int] -> Int -> (Int, Int) -> Gen [Int]
rangeElems absurd gsize (n, x)
    | n > x                            = absurd
    | toI x - toI n < toI (gsize + 2)  = return [n..x]
    | otherwise                        = do
          es <- replicateM gsize $ choose (n + 1, x - 1)
          return $ n : es ++ [x]
  where
    toI i = fromIntegral i :: Integer

type Range k = (k, k)
type WithLookup k p v a = String -> (k -> OrdPSQ k p v -> Maybe (k, p, v)) -> a
type LGRanges k = ([(Range k, k)], Range k)

onFail :: Testable prop => (a -> String) -> (a -> prop) -> a -> Property
onFail em p x = whenFail' (putStrLn $ em x) (p x)

lookupLG_expectJust'
    :: (Show k, Eq k, Show p, Show v)
    => WithLookup k p v (OrdPSQ k p v -> ([k], k) -> Property)
lookupLG_expectJust' name lookup' psq (qks, ek) =
    conjoin [ propJust lk | lk <- lookups ]
    .&&.
    conjoin [ p | (Just p, _qk) <- lookups ]
  where
    lookups = [ (match qk, qk) | qk <- qks ]

    propJust = onFail failNothing (isJust . fst)
    failNothing (_, qk) = "expect Just result of " ++ name ++ ": Nothing result for range: " ++
                          show (qks, ek) ++ " key: " ++ show qk
    match qk = (\(rk, _, _) -> onFail failUnmatch (== ek) rk) <$> lookup' qk psq
      where
        failUnmatch rk = "expect match result of " ++ name ++ ": unmatch result for case: " ++ show (qks, ek) ++
                         " key: " ++ show qk ++ " result:" ++ show rk ++ " =/= " ++ "expect:" ++ show ek

lookupLG_expectJust
    :: (Show p, Show v)
    => WithLookup Int p v (OrdPSQ Int p v -> (Range Int, Int) -> Property)
lookupLG_expectJust name lookup' psq (jrange, expect) =
    {- ioProperty just to generate -}
    ioProperty $ (\es -> lookupLG_expectJust' name lookup' psq (es, expect)) <$> generate genElems
  where
    gsize = 2
    genElems = rangeElems assertion gsize jrange
    assertion = error $ "lookupLG_expectJust: inverted range: " ++ show jrange

lookupLG_expectNothing'
    :: (Show k, Eq k, Show p, Show v)
    => WithLookup k p v (OrdPSQ k p v -> [k] -> Property)
lookupLG_expectNothing' name lookup' psq qks =
    conjoin [ propNothing qk | qk <- qks ]
  where
    propNothing = onFail failJust (\qk -> isNothing $ lookup' qk psq)
    failJust qk =  "expect Nothing result of " ++ name ++ ": Just result for case: " ++
                   show qks ++ " key: " ++ show qk

lookupLG_expectNothing
    :: (Show p, Show v)
    => WithLookup Int p v (OrdPSQ Int p v -> Range Int -> Property)
lookupLG_expectNothing name lookup' psq nrange =
    {- ioProperty just to generate -}
    ioProperty $ lookupLG_expectNothing' name lookup' psq <$> generate genElems
  where
    gsize = 2
    genElems = rangeElems assertion gsize nrange
    assertion = error $ "lookupLG_expectNothing: inverted range: " ++ show nrange

lookupLG_expects
    :: (Show p, Show v)
    => WithLookup Int p v ((OrdPSQ Int p v -> ([(Range Int, Int)], Range Int)) -> OrdPSQ Int p v -> Property)
lookupLG_expects name lookup' getRanges psq =
    conjoin [exJust j | j <- jranges ]
    .&&.
    exNothing nrange
  where
    exJust    = lookupLG_expectJust    name lookup' psq
    exNothing = lookupLG_expectNothing name lookup' psq
    (jranges, nrange) = getRanges psq

---

keyIntervals :: Bounded k => OrdPSQ k p v -> ((k, k), [(k, k)], (k, k))
keyIntervals psq = (head closed, init $ tail closed, last closed)
  where
    ks = [ k | (k, _, _) <- toAscList psq ]
    closed = zip (minBound : ks) (ks ++ [maxBound])

nothingsNullPSQ :: Bounded k => OrdPSQ k p v -> ([(Range k, k)], Range k) -> ([(Range k, k)], Range k)
nothingsNullPSQ psq notNull
    | null psq  =  ([], (minBound, maxBound))
    | otherwise =  notNull

---

prop_lookupLE :: OrdPSQ Int Int Char -> Property
prop_lookupLE = lookupLG_expects "lookupLE" lookupLE rangesLE

rangesLE :: OrdPSQ Int p v -> LGRanges Int
rangesLE psq = nothingsNullPSQ psq $ ([just cr | cr <- crs] ++ [justEnd maxRange], nothing minRange)
  where
    (minRange, crs, maxRange) = keyIntervals psq
    just    (n, x)  = ((n, x - 1), n)
    justEnd (n, x)  = ((n, x)    , n)
    nothing (n, x)  =  (n, x - 1)

prop_lookupGT :: OrdPSQ Int Int Char -> Property
prop_lookupGT = lookupLG_expects "lookupGT" lookupGT rangesGT

rangesGT :: OrdPSQ Int p v -> LGRanges Int
rangesGT psq = nothingsNullPSQ psq $ ([justEnd minRange] ++ [just cr | cr <- crs], nothing maxRange)
  where
    (minRange, crs, maxRange) = keyIntervals psq
    just    (n, x)  = ((n, x - 1), x)
    justEnd         = just
    nothing (n, x)  =  (n, x)

---

prop_lookupLT :: OrdPSQ Int Int Char -> Property
prop_lookupLT = lookupLG_expects "lookupLT" lookupLT rangesLT

rangesLT :: OrdPSQ Int p v -> LGRanges Int
rangesLT psq = nothingsNullPSQ psq ([just r | r <- rs] ++ [justEnd maxRange], nothing minRange)
  where
    (minRange, rs, maxRange) = keyIntervals psq
    just    (n, x)  = ((n + 1, x), n)
    justEnd         = just
    nothing (n, x)  =  (n    , x)

prop_lookupGE :: OrdPSQ Int Int Char -> Property
prop_lookupGE = lookupLG_expects "lookupGE" lookupGE rangesGE

rangesGE :: OrdPSQ Int p v -> LGRanges Int
rangesGE psq = nothingsNullPSQ psq ([justEnd minRange] ++ [just r | r <- rs], nothing maxRange)
  where
    (minRange, rs, maxRange) = keyIntervals psq
    just    (n, x)  = ((n + 1, x), x)
    justEnd (n, x)  = ((n    , x), x)
    nothing (n, x)  =  (n + 1, x)
