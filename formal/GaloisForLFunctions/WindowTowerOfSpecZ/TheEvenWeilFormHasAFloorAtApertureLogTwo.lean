import GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo.Data.EvenDataA
import GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo.Data.EvenDataB

/-!
# The even Weil quadratic form has a positive floor and sharp upper witness at aperture `log 2`

This module proves two complementary unconditional results on the critical two-prime
window `[-log 2, log 2]`:

1. **Positive floor (`1 / 10 ^ 13`):** Every real even `C²` test `F` supported in
   `[-log 2, log 2]` satisfies `(1 / 10 ^ 13) * ∫ x, F x ^ 2 ≤ weilQuad F`, proved by
   retaining 12 low even Legendre moment charges (`P_0, P_2, ..., P_22` on `[0, 1]`),
   the regional logarithmic gap above degree 24, the degree-22 local Gamma moments,
   the exact mean-square and `cosh` pole charges, 10 + 2 fiberwise tridiagonal
   subinterval certificates with Bernstein–Jensen `L²` residuals (`FiberCert.bound`),
   and an exact `12 × 12` `LDLᵀ` plus strict diagonal dominance matrix certificate
   (`quad_nonneg_of_ldlCheck`).
2. **Sharp upper bound (`< 1 / 10 ^ 9`) and degree-14 Gamma insufficiency:** The explicit
   smooth `C²` even degree-18 polynomial family `twoPrimeScaleTest s` (`s ∈ [1 - 10⁻²⁰, 1]`)
   satisfies `weilQuad (twoPrimeScaleTest s) < (1 / 10 ^ 9) * ∫ (twoPrimeScaleTest s) ^ 2`,
   while `twoPrimeDegree14GammaForm twoPrimeUpperTest < 0`, proving that degree-14 local
   Gamma truncations cannot certify positivity on the two-prime window.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology Finset Zeta23
open scoped BigOperators
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.ArchimedeanExactForm
open _root_.RHTower.WeilMarkovPole _root_.RHTower.WeilLevyPoleGauss
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open LatticeSectionTheory ArithmeticIncidencePositivity ArithmeticCriticalityTheory
open BiScaleUncertainty SpacingScaleHarmonicAnalysis SelectivePositivityAndThresholdLaws

/-! ### 1. Finite indexing, polynomial evaluation, and Legendre basis identities -/

private theorem sum_finK (f : Fin 12 → ℝ) :
    (∑ i : Fin 12, f i) = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ + f ⟨2, by omega⟩ + f ⟨3, by omega⟩ + f ⟨4, by omega⟩ + f ⟨5, by omega⟩ + f ⟨6, by omega⟩ + f ⟨7, by omega⟩ + f ⟨8, by omega⟩ + f ⟨9, by omega⟩ + f ⟨10, by omega⟩ + f ⟨11, by omega⟩ := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f ⟨0, by omega⟩ + (f ⟨1, by omega⟩ + (f ⟨2, by omega⟩ + (f ⟨3, by omega⟩ + (f ⟨4, by omega⟩ + (f ⟨5, by omega⟩ + (f ⟨6, by omega⟩ + (f ⟨7, by omega⟩ + (f ⟨8, by omega⟩ + (f ⟨9, by omega⟩ + (f ⟨10, by omega⟩ + (f ⟨11, by omega⟩))))))))))) = _
  ring

private theorem sum_range_12 (f : ℕ → ℝ) :
    (∑ p ∈ Finset.range 12, f p) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

private theorem sum_range_24 (f : ℕ → ℝ) :
    (∑ p ∈ Finset.range 24, f p) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

private def polyEval : List ℝ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => c + x * polyEval cs x

private def coeffAt : List ℝ → ℕ → ℝ
  | [], _ => 0
  | c :: _, 0 => c
  | _ :: cs, p + 1 => coeffAt cs p

private def listAt : List (List ℝ) → ℕ → List ℝ
  | [], _ => []
  | r :: _, 0 => r
  | _ :: rs, i + 1 => listAt rs i

private def matAt (M : List (List ℝ)) (i j : ℕ) : ℝ :=
  coeffAt (listAt M i) j

private def qcoeffAt : List ℚ → ℕ → ℚ
  | [], _ => 0
  | c :: _, 0 => c
  | _ :: cs, p + 1 => qcoeffAt cs p

private def qlistAt : List (List ℚ) → ℕ → List ℚ
  | [], _ => []
  | r :: _, 0 => r
  | _ :: rs, i + 1 => qlistAt rs i

private theorem qcoeffAt_eq_getD : ∀ (l : List ℚ) (n : ℕ), qcoeffAt l n = l.getD n 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: cs, p + 1 => qcoeffAt_eq_getD cs p

private theorem qlistAt_eq_getD : ∀ (M : List (List ℚ)) (i : ℕ), qlistAt M i = M.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: rs, i + 1 => qlistAt_eq_getD rs i

private theorem matQ_eq_qcoeffAt (M : List (List ℚ)) (i j : ℕ) :
    ApertureLogTwo.matQ M i j = qcoeffAt (qlistAt M i) j := by
  unfold ApertureLogTwo.matQ
  rw [← qlistAt_eq_getD, ← qcoeffAt_eq_getD]

private theorem gammaAlphaEven_eq_0 : gammaAlphaEven 0 = (-105091 / 5000000000000000000 : ℝ) := rfl
private theorem gammaAlphaEven_eq_1 : gammaAlphaEven 1 = (550751 / 400000000000000000 : ℝ) := rfl
private theorem gammaAlphaEven_eq_2 : gammaAlphaEven 2 = (65104166242035063 / 10000000000000000000 : ℝ) := rfl
private theorem gammaAlphaEven_eq_3 : gammaAlphaEven 3 = (-3309458785969429 / 5000000000000000000 : ℝ) := rfl
private theorem gammaAlphaEven_eq_4 : gammaAlphaEven 4 = (5366589076364431 / 80000000000000000000 : ℝ) := rfl
private theorem gammaAlphaEven_eq_5 : gammaAlphaEven 5 = (-8726421052567571 / 1280000000000000000000 : ℝ) := rfl
private theorem gammaAlphaEven_eq_6 : gammaAlphaEven 6 = (7163072980652803 / 10240000000000000000000 : ℝ) := rfl
private theorem gammaAlphaEven_eq_7 : gammaAlphaEven 7 = (-6237272726078909 / 81920000000000000000000 : ℝ) := rfl
private theorem gammaAlphaEven_eq_8 : gammaAlphaEven 8 = (3260029542583927 / 327680000000000000000000 : ℝ) := rfl
private theorem gammaAlphaEven_eq_9 : gammaAlphaEven 9 = (-519878183231709 / 327680000000000000000000 : ℝ) := rfl
private theorem gammaAlphaEven_eq_10 : gammaAlphaEven 10 = (4669432996809649 / 20971520000000000000000000 : ℝ) := rfl
private theorem gammaAlphaEven_eq_11 : gammaAlphaEven 11 = (-1377431922843341 / 83886080000000000000000000 : ℝ) := rfl

private theorem continuous_polyEval : ∀ cs : List ℝ, Continuous (polyEval cs)
  | [] => continuous_const
  | _ :: cs => continuous_const.add (continuous_id.mul (continuous_polyEval cs))

private def polyAdd : List ℝ → List ℝ → List ℝ
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a + b) :: polyAdd as bs

private theorem polyEval_add : ∀ (as bs : List ℝ) (x : ℝ),
    polyEval (polyAdd as bs) x = polyEval as x + polyEval bs x
  | [], bs, _ => by simp [polyAdd, polyEval]
  | a :: as, [], _ => by simp [polyAdd, polyEval]
  | a :: as, b :: bs, x => by simp only [polyAdd, polyEval, polyEval_add as bs x]; ring

private def polyDeriv : List ℝ → List ℝ
  | [] => []
  | _ :: cs => polyAdd cs (0 :: polyDeriv cs)

private theorem hasDerivAt_polyEval : ∀ (cs : List ℝ) (x : ℝ),
    HasDerivAt (polyEval cs) (polyEval (polyDeriv cs) x) x
  | [], x => by simpa [polyEval, polyDeriv] using hasDerivAt_const x (0 : ℝ)
  | c :: cs, x => by
    have hd := ((hasDerivAt_id x).mul (hasDerivAt_polyEval cs x)).const_add c
    refine hd.congr_deriv ?_
    simp only [polyDeriv, polyEval_add, polyEval, id_eq]
    ring

private theorem iterPrim_succ_of_polyEval {f : ℝ → ℝ} (s : ℕ) (ps qs : List ℝ)
    (hps : ∀ y, iterPrim s f y = polyEval ps y)
    (h0 : polyEval qs (-1) = 0)
    (hd : ∀ y, polyEval (polyDeriv qs) y = polyEval ps y) :
    ∀ y, iterPrim (s + 1) f y = polyEval qs y := by
  intro y
  simp only [iterPrim, hps]
  have hderiv : ∀ u ∈ uIcc (-1 : ℝ) y, HasDerivAt (polyEval qs) (polyEval ps u) u :=
    fun u _ => (hasDerivAt_polyEval qs u).congr_deriv (hd u)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_polyEval ps).intervalIntegrable _ _), h0, sub_zero]

private theorem polyEval_eq_sum_of_le : ∀ (cs : List ℝ) {D : ℕ}, cs.length ≤ D →
    ∀ x : ℝ, polyEval cs x = ∑ p ∈ Finset.range D, coeffAt cs p * x ^ p
  | [], D, _, x => by simp [polyEval, coeffAt]
  | c :: cs, 0, h, _ => by simp at h
  | c :: cs, D + 1, h, x => by
    have ih := polyEval_eq_sum_of_le cs (D := D) (by simp at h; omega) x
    rw [polyEval, ih, Finset.sum_range_succ' _ D, coeffAt, pow_zero, mul_one, Finset.mul_sum]
    have hmul : (∑ k ∈ Finset.range D, x * (coeffAt cs k * x ^ k)) =
        ∑ k ∈ Finset.range D, coeffAt (c :: cs) (k + 1) * x ^ (k + 1) :=
      Finset.sum_congr rfl fun k _ => by dsimp [coeffAt]; ring
    rw [hmul, add_comm]

private def qintSymm (p : List ℚ) : ℚ :=
  ApertureLogTwo.qevalQ (ApertureLogTwo.qprim p) 1 -
    ApertureLogTwo.qevalQ (ApertureLogTwo.qprim p) (-1)

private theorem integral_qeval_symm (p : List ℚ) :
    (∫ y in (-1 : ℝ)..1, ApertureLogTwo.qeval p y) = (qintSymm p : ℝ) := by
  have h1 : ApertureLogTwo.qeval (ApertureLogTwo.qprim p) (1 : ℝ) =
      (ApertureLogTwo.qevalQ (ApertureLogTwo.qprim p) 1 : ℝ) :=
    (congrArg (ApertureLogTwo.qeval (ApertureLogTwo.qprim p)) (by push_cast; rfl)).trans
      (ApertureLogTwo.qeval_ratCast (ApertureLogTwo.qprim p) 1)
  have hm1 : ApertureLogTwo.qeval (ApertureLogTwo.qprim p) (-1 : ℝ) =
      (ApertureLogTwo.qevalQ (ApertureLogTwo.qprim p) (-1) : ℝ) :=
    (congrArg (ApertureLogTwo.qeval (ApertureLogTwo.qprim p)) (by push_cast; rfl)).trans
      (ApertureLogTwo.qeval_ratCast (ApertureLogTwo.qprim p) (-1))
  rw [ApertureLogTwo.integral_qeval, h1, hm1, qintSymm]; push_cast; rfl

private theorem integral_qeval_mul_symm (p q : List ℚ) :
    (∫ y in (-1 : ℝ)..1, ApertureLogTwo.qeval p y * ApertureLogTwo.qeval q y) =
      (qintSymm (ApertureLogTwo.qmul p q) : ℝ) := by
  simp_rw [← ApertureLogTwo.qeval_qmul]
  exact integral_qeval_symm _

private def legList_0 : List ℝ := ([1] : List ℝ)
private theorem legP_eq_0 (x : ℝ) : legP 0 x = polyEval legList_0 x := by
  rw [legP_zero]; dsimp [legList_0, polyEval]; ring
private def legList_1 : List ℝ := ([0, 1] : List ℝ)
private theorem legP_eq_1 (x : ℝ) : legP 1 x = polyEval legList_1 x := by
  rw [legP_one]; dsimp [legList_1, polyEval]; ring
private def legList_2 : List ℝ := ([-1 / 2, 0, 3 / 2] : List ℝ)
private theorem legP_eq_2 (x : ℝ) : legP 2 x = polyEval legList_2 x := by
  rw [legP_succ_succ 0 x, legP_eq_1 x, legP_eq_0 x]
  dsimp [legList_2, legList_1, legList_0, polyEval]; ring
private def legList_3 : List ℝ := ([0, -3 / 2, 0, 5 / 2] : List ℝ)
private theorem legP_eq_3 (x : ℝ) : legP 3 x = polyEval legList_3 x := by
  rw [legP_succ_succ 1 x, legP_eq_2 x, legP_eq_1 x]
  dsimp [legList_3, legList_2, legList_1, polyEval]; ring
private def legList_4 : List ℝ := ([3 / 8, 0, -15 / 4, 0, 35 / 8] : List ℝ)
private theorem legP_eq_4 (x : ℝ) : legP 4 x = polyEval legList_4 x := by
  rw [legP_succ_succ 2 x, legP_eq_3 x, legP_eq_2 x]
  dsimp [legList_4, legList_3, legList_2, polyEval]; ring
private def legList_5 : List ℝ := ([0, 15 / 8, 0, -35 / 4, 0, 63 / 8] : List ℝ)
private theorem legP_eq_5 (x : ℝ) : legP 5 x = polyEval legList_5 x := by
  rw [legP_succ_succ 3 x, legP_eq_4 x, legP_eq_3 x]
  dsimp [legList_5, legList_4, legList_3, polyEval]; ring
private def legList_6 : List ℝ := ([-5 / 16, 0, 105 / 16, 0, -315 / 16, 0, 231 / 16] : List ℝ)
private theorem legP_eq_6 (x : ℝ) : legP 6 x = polyEval legList_6 x := by
  rw [legP_succ_succ 4 x, legP_eq_5 x, legP_eq_4 x]
  dsimp [legList_6, legList_5, legList_4, polyEval]; ring
private def legList_7 : List ℝ := ([0, -35 / 16, 0, 315 / 16, 0, -693 / 16, 0, 429 / 16] : List ℝ)
private theorem legP_eq_7 (x : ℝ) : legP 7 x = polyEval legList_7 x := by
  rw [legP_succ_succ 5 x, legP_eq_6 x, legP_eq_5 x]
  dsimp [legList_7, legList_6, legList_5, polyEval]; ring
private def legList_8 : List ℝ := ([35 / 128, 0, -315 / 32, 0, 3465 / 64, 0, -3003 / 32, 0, 6435 / 128] : List ℝ)
private theorem legP_eq_8 (x : ℝ) : legP 8 x = polyEval legList_8 x := by
  rw [legP_succ_succ 6 x, legP_eq_7 x, legP_eq_6 x]
  dsimp [legList_8, legList_7, legList_6, polyEval]; ring
private def legList_9 : List ℝ := ([0, 315 / 128, 0, -1155 / 32, 0, 9009 / 64, 0, -6435 / 32, 0, 12155 / 128] : List ℝ)
private theorem legP_eq_9 (x : ℝ) : legP 9 x = polyEval legList_9 x := by
  rw [legP_succ_succ 7 x, legP_eq_8 x, legP_eq_7 x]
  dsimp [legList_9, legList_8, legList_7, polyEval]; ring
private def legList_10 : List ℝ := ([-63 / 256, 0, 3465 / 256, 0, -15015 / 128, 0, 45045 / 128, 0, -109395 / 256, 0, 46189 / 256] : List ℝ)
private theorem legP_eq_10 (x : ℝ) : legP 10 x = polyEval legList_10 x := by
  rw [legP_succ_succ 8 x, legP_eq_9 x, legP_eq_8 x]
  dsimp [legList_10, legList_9, legList_8, polyEval]; ring
private def legList_11 : List ℝ := ([0, -693 / 256, 0, 15015 / 256, 0, -45045 / 128, 0, 109395 / 128, 0, -230945 / 256, 0, 88179 / 256] : List ℝ)
private theorem legP_eq_11 (x : ℝ) : legP 11 x = polyEval legList_11 x := by
  rw [legP_succ_succ 9 x, legP_eq_10 x, legP_eq_9 x]
  dsimp [legList_11, legList_10, legList_9, polyEval]; ring
private def legList_12 : List ℝ := ([231 / 1024, 0, -9009 / 512, 0, 225225 / 1024, 0, -255255 / 256, 0, 2078505 / 1024, 0, -969969 / 512, 0, 676039 / 1024] : List ℝ)
private theorem legP_eq_12 (x : ℝ) : legP 12 x = polyEval legList_12 x := by
  rw [legP_succ_succ 10 x, legP_eq_11 x, legP_eq_10 x]
  dsimp [legList_12, legList_11, legList_10, polyEval]; ring
private def legList_13 : List ℝ := ([0, 3003 / 1024, 0, -45045 / 512, 0, 765765 / 1024, 0, -692835 / 256, 0, 4849845 / 1024, 0, -2028117 / 512, 0, 1300075 / 1024] : List ℝ)
private theorem legP_eq_13 (x : ℝ) : legP 13 x = polyEval legList_13 x := by
  rw [legP_succ_succ 11 x, legP_eq_12 x, legP_eq_11 x]
  dsimp [legList_13, legList_12, legList_11, polyEval]; ring
private def legList_14 : List ℝ := ([-429 / 2048, 0, 45045 / 2048, 0, -765765 / 2048, 0, 4849845 / 2048, 0, -14549535 / 2048, 0, 22309287 / 2048, 0, -16900975 / 2048, 0, 5014575 / 2048] : List ℝ)
private theorem legP_eq_14 (x : ℝ) : legP 14 x = polyEval legList_14 x := by
  rw [legP_succ_succ 12 x, legP_eq_13 x, legP_eq_12 x]
  dsimp [legList_14, legList_13, legList_12, polyEval]; ring
private def legList_15 : List ℝ := ([0, -6435 / 2048, 0, 255255 / 2048, 0, -2909907 / 2048, 0, 14549535 / 2048, 0, -37182145 / 2048, 0, 50702925 / 2048, 0, -35102025 / 2048, 0, 9694845 / 2048] : List ℝ)
private theorem legP_eq_15 (x : ℝ) : legP 15 x = polyEval legList_15 x := by
  rw [legP_succ_succ 13 x, legP_eq_14 x, legP_eq_13 x]
  dsimp [legList_15, legList_14, legList_13, polyEval]; ring
private def legList_16 : List ℝ := ([6435 / 32768, 0, -109395 / 4096, 0, 4849845 / 8192, 0, -20369349 / 4096, 0, 334639305 / 16384, 0, -185910725 / 4096, 0, 456326325 / 8192, 0, -145422675 / 4096, 0, 300540195 / 32768] : List ℝ)
private theorem legP_eq_16 (x : ℝ) : legP 16 x = polyEval legList_16 x := by
  rw [legP_succ_succ 14 x, legP_eq_15 x, legP_eq_14 x]
  dsimp [legList_16, legList_15, legList_14, polyEval]; ring
private def legList_17 : List ℝ := ([0, 109395 / 32768, 0, -692835 / 4096, 0, 20369349 / 8192, 0, -66927861 / 4096, 0, 929553625 / 16384, 0, -456326325 / 4096, 0, 1017958725 / 8192, 0, -300540195 / 4096, 0, 583401555 / 32768] : List ℝ)
private theorem legP_eq_17 (x : ℝ) : legP 17 x = polyEval legList_17 x := by
  rw [legP_succ_succ 15 x, legP_eq_16 x, legP_eq_15 x]
  dsimp [legList_17, legList_16, legList_15, polyEval]; ring
private def legList_18 : List ℝ := ([-12155 / 65536, 0, 2078505 / 65536, 0, -14549535 / 16384, 0, 156165009 / 16384, 0, -1673196525 / 32768, 0, 5019589575 / 32768, 0, -4411154475 / 16384, 0, 4508102925 / 16384, 0, -9917826435 / 65536, 0, 2268783825 / 65536] : List ℝ)
private theorem legP_eq_18 (x : ℝ) : legP 18 x = polyEval legList_18 x := by
  rw [legP_succ_succ 16 x, legP_eq_17 x, legP_eq_16 x]
  dsimp [legList_18, legList_17, legList_16, polyEval]; ring
private def legList_19 : List ℝ := ([0, -230945 / 65536, 0, 14549535 / 65536, 0, -66927861 / 16384, 0, 557732175 / 16384, 0, -5019589575 / 32768, 0, 13233463425 / 32768, 0, -10518906825 / 16384, 0, 9917826435 / 16384, 0, -20419054425 / 65536, 0, 4418157975 / 65536] : List ℝ)
private theorem legP_eq_19 (x : ℝ) : legP 19 x = polyEval legList_19 x := by
  rw [legP_succ_succ 17 x, legP_eq_18 x, legP_eq_17 x]
  dsimp [legList_19, legList_18, legList_17, polyEval]; ring
private def legList_20 : List ℝ := ([46189 / 262144, 0, -4849845 / 131072, 0, 334639305 / 262144, 0, -557732175 / 32768, 0, 15058768725 / 131072, 0, -29113619535 / 65536, 0, 136745788725 / 131072, 0, -49589132175 / 32768, 0, 347123925225 / 262144, 0, -83945001525 / 131072, 0, 34461632205 / 262144] : List ℝ)
private theorem legP_eq_20 (x : ℝ) : legP 20 x = polyEval legList_20 x := by
  rw [legP_succ_succ 18 x, legP_eq_19 x, legP_eq_18 x]
  dsimp [legList_20, legList_19, legList_18, polyEval]; ring
private def legList_21 : List ℝ := ([0, 969969 / 262144, 0, -37182145 / 131072, 0, 1673196525 / 262144, 0, -2151252675 / 32768, 0, 48522699225 / 131072, 0, -82047473235 / 65536, 0, 347123925225 / 131072, 0, -115707975075 / 32768, 0, 755505013725 / 262144, 0, -172308161025 / 131072, 0, 67282234305 / 262144] : List ℝ)
private theorem legP_eq_21 (x : ℝ) : legP 21 x = polyEval legList_21 x := by
  rw [legP_succ_succ 19 x, legP_eq_20 x, legP_eq_19 x]
  dsimp [legList_21, legList_20, legList_19, polyEval]; ring
private def legList_22 : List ℝ := ([-88179 / 524288, 0, 22309287 / 524288, 0, -929553625 / 524288, 0, 15058768725 / 524288, 0, -62386327575 / 262144, 0, 300840735195 / 262144, 0, -902522205585 / 262144, 0, 1735619626125 / 262144, 0, -4281195077775 / 524288, 0, 3273855059475 / 524288, 0, -1412926920405 / 524288, 0, 263012370465 / 524288] : List ℝ)
private theorem legP_eq_22 (x : ℝ) : legP 22 x = polyEval legList_22 x := by
  rw [legP_succ_succ 20 x, legP_eq_21 x, legP_eq_20 x]
  dsimp [legList_22, legList_21, legList_20, polyEval]; ring
private def legList_23 : List ℝ := ([0, -2028117 / 524288, 0, 185910725 / 524288, 0, -5019589575 / 524288, 0, 62386327575 / 524288, 0, -214886239425 / 262144, 0, 902522205585 / 262144, 0, -2429867476575 / 262144, 0, 4281195077775 / 262144, 0, -9821565178425 / 524288, 0, 7064634602025 / 524288, 0, -2893136075115 / 524288, 0, 514589420475 / 524288] : List ℝ)
private theorem legP_eq_23 (x : ℝ) : legP 23 x = polyEval legList_23 x := by
  rw [legP_succ_succ 21 x, legP_eq_22 x, legP_eq_21 x]
  dsimp [legList_23, legList_22, legList_21, polyEval]; ring
private def legList_24 : List ℝ := ([676039 / 4194304, 0, -50702925 / 1048576, 0, 5019589575 / 2097152, 0, -48522699225 / 1048576, 0, 1933976154825 / 4194304, 0, -1418249180205 / 524288, 0, 10529425731825 / 1048576, 0, -12843585233325 / 524288, 0, 166966608033225 / 4194304, 0, -44742685812825 / 1048576, 0, 60755857577415 / 2097152, 0, -11835556670925 / 1048576, 0, 8061900920775 / 4194304] : List ℝ)
private theorem legP_eq_24 (x : ℝ) : legP 24 x = polyEval legList_24 x := by
  rw [legP_succ_succ 22 x, legP_eq_23 x, legP_eq_22 x]
  dsimp [legList_24, legList_23, legList_22, polyEval]; ring
private def legList_25 : List ℝ := ([0, 16900975 / 4194304, 0, -456326325 / 1048576, 0, 29113619535 / 2097152, 0, -214886239425 / 1048576, 0, 7091245901025 / 4194304, 0, -4512611027925 / 524288, 0, 29968365544425 / 1048576, 0, -33393321606645 / 524288, 0, 402684172315425 / 4194304, 0, -101259762629025 / 1048576, 0, 130191123380175 / 2097152, 0, -24185702762325 / 1048576, 0, 15801325804719 / 4194304] : List ℝ)
private theorem legP_eq_25 (x : ℝ) : legP 25 x = polyEval legList_25 x := by
  rw [legP_succ_succ 23 x, legP_eq_24 x, legP_eq_23 x]
  dsimp [legList_25, legList_24, legList_23, polyEval]; ring
private def legList_26 : List ℝ := ([-1300075 / 8388608, 0, 456326325 / 8388608, 0, -13233463425 / 4194304, 0, 300840735195 / 4194304, 0, -7091245901025 / 8388608, 0, 49638721307175 / 8388608, 0, -55655536011075 / 2097152, 0, 166966608033225 / 2097152, 0, -1369126185872445 / 8388608, 0, 1923935489951475 / 8388608, 0, -911337863661225 / 4194304, 0, 556271163533475 / 4194304, 0, -395033145117975 / 8388608, 0, 61989816618513 / 8388608] : List ℝ)
private theorem legP_eq_26 (x : ℝ) : legP 26 x = polyEval legList_26 x := by
  rw [legP_succ_succ 24 x, legP_eq_25 x, legP_eq_24 x]
  dsimp [legList_26, legList_25, legList_24, polyEval]; ring
private def legList_27 : List ℝ := ([0, -35102025 / 8388608, 0, 4411154475 / 8388608, 0, -82047473235 / 4194304, 0, 1418249180205 / 4194304, 0, -27577067392875 / 8388608, 0, 166966608033225 / 8388608, 0, -166966608033225 / 2097152, 0, 456375395290815 / 2097152, 0, -3463083881912655 / 8388608, 0, 4556689318306125 / 8388608, 0, -2039660932956075 / 4194304, 0, 1185099435353925 / 4194304, 0, -805867616040669 / 8388608, 0, 121683714103007 / 8388608] : List ℝ)
private theorem legP_eq_27 (x : ℝ) : legP 27 x = polyEval legList_27 x := by
  rw [legP_succ_succ 25 x, legP_eq_26 x, legP_eq_25 x]
  dsimp [legList_27, legList_26, legList_25, polyEval]; ring
private def legList_28 : List ℝ := ([5014575 / 33554432, 0, -1017958725 / 16777216, 0, 136745788725 / 33554432, 0, -902522205585 / 8388608, 0, 49638721307175 / 33554432, 0, -204070298707275 / 16777216, 0, 2170565904431925 / 33554432, 0, -977947275623175 / 4194304, 0, 19624141997505045 / 33554432, 0, -17315419409563275 / 16777216, 0, 42832879592077575 / 33554432, 0, -9085762337713425 / 8388608, 0, 20146690401016725 / 33554432, 0, -3285460280781189 / 16777216, 0, 956086325095055 / 33554432] : List ℝ)
private theorem legP_eq_28 (x : ℝ) : legP 28 x = polyEval legList_28 x := by
  rw [legP_succ_succ 26 x, legP_eq_27 x, legP_eq_26 x]
  dsimp [legList_28, legList_27, legList_26, polyEval]; ring
private def legList_29 : List ℝ := ([0, 145422675 / 33554432, 0, -10518906825 / 16777216, 0, 902522205585 / 33554432, 0, -4512611027925 / 8388608, 0, 204070298707275 / 33554432, 0, -723521968143975 / 16777216, 0, 6845630929362225 / 33554432, 0, -2803448856786435 / 4194304, 0, 51946258228689825 / 33554432, 0, -42832879592077575 / 16777216, 0, 99943385714847675 / 33554432, 0, -20146690401016725 / 8388608, 0, 42710983650155457 / 33554432, 0, -6692604275665385 / 16777216, 0, 1879204156221315 / 33554432] : List ℝ)
private theorem legP_eq_29 (x : ℝ) : legP 29 x = polyEval legList_29 x := by
  rw [legP_succ_succ 27 x, legP_eq_28 x, legP_eq_27 x]
  dsimp [legList_29, legList_28, legList_27, polyEval]; ring
private def legList_30 : List ℝ := ([-9694845 / 67108864, 0, 4508102925 / 67108864, 0, -347123925225 / 67108864, 0, 10529425731825 / 67108864, 0, -166966608033225 / 67108864, 0, 1591748329916745 / 67108864, 0, -9888133564634325 / 67108864, 0, 42051732851796525 / 67108864, 0, -126155198555389575 / 67108864, 0, 271274904083157975 / 67108864, 0, -419762220002360235 / 67108864, 0, 463373879223384675 / 67108864, 0, -355924863751295475 / 67108864, 0, 180700315442965395 / 67108864, 0, -54496920530418135 / 67108864, 0, 7391536347803839 / 67108864] : List ℝ)
private theorem legP_eq_30 (x : ℝ) : legP 30 x = polyEval legList_30 x := by
  rw [legP_succ_succ 28 x, legP_eq_29 x, legP_eq_28 x]
  dsimp [legList_30, legList_29, legList_28, polyEval]; ring

/-! ### 2. Retained archimedean moments, Wirtinger damping, and `B_clean` bound -/

private def degAt (k : Fin 12) : ℕ := 2 * k.1
private def halfMoment (G : ℝ → ℝ) (k : Fin 12) : ℝ := ∫ u in (0 : ℝ)..1, G u * legP (degAt k) u

private def cGammaLo : ℝ := (-7864196698840726104596979160266970163194919963811697843753668674575282353265833306357125048490006836897386104701810053800842752734680071169055410698402724687026841856424717483586175699833352406603138893267187605573847734014332200070745739125094958386638471108456001908215152660703630550333682628526817740242387843202857756068113489958109335661809959558787635891477211885702275195898621078783507822247008684816336172420526027721623256148488735452195063600835540672912481288008202182941320632870980805711122512251282158684669518450858917525778555664328024258927591093993364803899858827473324067074564516792511953577068216643231 / 2868336900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
private theorem cGammaLo_le_twoPrimeGammaMassExact : cGammaLo ≤ twoPrimeGammaMassExact := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  obtain ⟨hgbl, _⟩ := gammaBracket_zero_bounds
  obtain ⟨hlevl, _⟩ := archLevyAntideriv_two_mul_log_two_bounds
  unfold twoPrimeGammaMassExact apertureLogTwo
  dsimp only
  set r := 2 * Real.log 2
  have hr_lo : 2 * logTwoLo ≤ r := by dsimp [r]; linarith
  have hr_hi : r ≤ 2 * logTwoHi := by dsimp [r]; linarith
  have hr0_nn : (0 : ℝ) ≤ 2 * logTwoLo := by norm_num [logTwoLo]
  have hr_nn : 0 ≤ r := hr0_nn.trans hr_lo
  have hp : ∀ k : ℕ, (2 * logTwoLo) ^ k ≤ r ^ k ∧ r ^ k ≤ (2 * logTwoHi) ^ k := fun k =>
    ⟨pow_le_pow_left₀ hr0_nn hr_lo k, pow_le_pow_left₀ hr_nn hr_hi k⟩
  rw [sum_range_12]
  have hnum : cGammaLo ≤ gammaBracketZeroLo + (2 * logTwoLo) / 2 - (2 * logTwoHi) ^ 2 / 48 -
      (2 * logTwoHi) ^ 3 / 48 + 2 * archLevyTwoLogTwoLo +
      7 * (2 * logTwoLo) ^ 4 / (4 * 5760) - 31 * (2 * logTwoHi) ^ 6 / (6 * 967680) +
      127 * (2 * logTwoLo) ^ 8 / (8 * 154828800) + (
      gammaAlphaEven 0 * (2 * logTwoHi) ^ 1 / (2 * (0 : ℝ) + 1) +
      gammaAlphaEven 1 * (2 * logTwoLo) ^ 3 / (2 * (1 : ℝ) + 1) +
      gammaAlphaEven 2 * (2 * logTwoLo) ^ 5 / (2 * (2 : ℝ) + 1) +
      gammaAlphaEven 3 * (2 * logTwoHi) ^ 7 / (2 * (3 : ℝ) + 1) +
      gammaAlphaEven 4 * (2 * logTwoLo) ^ 9 / (2 * (4 : ℝ) + 1) +
      gammaAlphaEven 5 * (2 * logTwoHi) ^ 11 / (2 * (5 : ℝ) + 1) +
      gammaAlphaEven 6 * (2 * logTwoLo) ^ 13 / (2 * (6 : ℝ) + 1) +
      gammaAlphaEven 7 * (2 * logTwoHi) ^ 15 / (2 * (7 : ℝ) + 1) +
      gammaAlphaEven 8 * (2 * logTwoLo) ^ 17 / (2 * (8 : ℝ) + 1) +
      gammaAlphaEven 9 * (2 * logTwoHi) ^ 19 / (2 * (9 : ℝ) + 1) +
      gammaAlphaEven 10 * (2 * logTwoLo) ^ 21 / (2 * (10 : ℝ) + 1) +
      gammaAlphaEven 11 * (2 * logTwoHi) ^ 23 / (2 * (11 : ℝ) + 1)) := by
    rw [gammaAlphaEven_eq_0, gammaAlphaEven_eq_1, gammaAlphaEven_eq_2, gammaAlphaEven_eq_3, gammaAlphaEven_eq_4, gammaAlphaEven_eq_5, gammaAlphaEven_eq_6, gammaAlphaEven_eq_7, gammaAlphaEven_eq_8, gammaAlphaEven_eq_9, gammaAlphaEven_eq_10, gammaAlphaEven_eq_11]
    norm_num [cGammaLo, gammaBracketZeroLo, archLevyTwoLogTwoLo, logTwoLo, logTwoHi]
  rw [gammaAlphaEven_eq_0, gammaAlphaEven_eq_1, gammaAlphaEven_eq_2, gammaAlphaEven_eq_3, gammaAlphaEven_eq_4, gammaAlphaEven_eq_5, gammaAlphaEven_eq_6, gammaAlphaEven_eq_7, gammaAlphaEven_eq_8, gammaAlphaEven_eq_9, gammaAlphaEven_eq_10, gammaAlphaEven_eq_11] at hnum ⊢
  linarith [hgbl, hlevl, hnum, (hp 1).1, (hp 1).2, (hp 2).1, (hp 2).2, (hp 3).1, (hp 3).2, (hp 4).1, (hp 4).2, (hp 5).1, (hp 5).2, (hp 6).1, (hp 6).2, (hp 7).1, (hp 7).2, (hp 8).1, (hp 8).2, (hp 9).1, (hp 9).2, (hp 11).1, (hp 11).2, (hp 13).1, (hp 13).2, (hp 15).1, (hp 15).2, (hp 17).1, (hp 17).2, (hp 19).1, (hp 19).2, (hp 21).1, (hp 21).2, (hp 23).1, (hp 23).2]

private def monToLegMat (j k : Fin 12) : ℝ :=
  matAt ([([1] : List ℝ),
    ([1 / 3, 2 / 3] : List ℝ),
    ([1 / 5, 4 / 7, 8 / 35] : List ℝ),
    ([1 / 7, 10 / 21, 24 / 77, 16 / 231] : List ℝ),
    ([1 / 9, 40 / 99, 48 / 143, 64 / 495, 128 / 6435] : List ℝ),
    ([1 / 11, 50 / 143, 48 / 143, 32 / 187, 128 / 2717, 256 / 46189] : List ℝ),
    ([1 / 13, 4 / 13, 72 / 221, 64 / 323, 128 / 1729, 1536 / 96577, 1024 / 676039] : List ℝ),
    ([1 / 15, 14 / 51, 504 / 1615, 208 / 969, 128 / 1311, 5376 / 185725, 1024 / 200583, 2048 / 5014575] : List ℝ),
    ([1 / 17, 80 / 323, 96 / 323, 1664 / 7429, 256 / 2185, 14336 / 334305, 20480 / 1938969, 16384 / 10363455, 32768 / 300540195] : List ℝ),
    ([1 / 19, 30 / 133, 864 / 3059, 2496 / 10925, 4352 / 32775, 3584 / 63365, 20480 / 1178589, 8192 / 2235255, 32768 / 68751025, 65536 / 2268783825] : List ℝ),
    ([1 / 21, 100 / 483, 216 / 805, 1664 / 7245, 4352 / 30015, 7168 / 103385, 51200 / 2047023, 16384 / 2470545, 32768 / 26776715, 131072 / 931395465, 262144 / 34461632205] : List ℝ),
    ([1 / 23, 22 / 115, 88 / 345, 2288 / 10005, 47872 / 310155, 25088 / 310155, 2048 / 62031, 4096 / 395715, 360448 / 149184555, 65536 / 165312615, 262144 / 6414935865, 524288 / 263012370465] : List ℝ)] : List (List ℝ)) j.1 k.1

private theorem pow_eq_leg_sum_0 (u : ℝ) :
    u ^ 0 = ∑ k : Fin 12, monToLegMat ⟨0, by omega⟩ k * legP (degAt k) u := by
  rw [sum_finK]; dsimp only [monToLegMat, matAt, listAt, coeffAt, degAt]
  rw [legP_eq_0 u]
  dsimp only [legList_0, polyEval]; ring
private theorem pow_eq_leg_sum_1 (u : ℝ) :
    u ^ 2 = ∑ k : Fin 12, monToLegMat ⟨1, by omega⟩ k * legP (degAt k) u := by
  rw [sum_finK]; dsimp only [monToLegMat, matAt, listAt, coeffAt, degAt]
  rw [legP_eq_0 u, legP_eq_2 u]
  dsimp only [legList_0, legList_2, polyEval]; ring
private theorem pow_eq_leg_sum_2 (u : ℝ) :
    u ^ 4 = ∑ k : Fin 12, monToLegMat ⟨2, by omega⟩ k * legP (degAt k) u := by
  rw [sum_finK]; dsimp only [monToLegMat, matAt, listAt, coeffAt, degAt]
  rw [legP_eq_0 u, legP_eq_2 u, legP_eq_4 u]
  dsimp only [legList_0, legList_2, legList_4, polyEval]; ring
private theorem pow_eq_leg_sum_3 (u : ℝ) :
    u ^ 6 = ∑ k : Fin 12, monToLegMat ⟨3, by omega⟩ k * legP (degAt k) u := by
  rw [sum_finK]; dsimp only [monToLegMat, matAt, listAt, coeffAt, degAt]
  rw [legP_eq_0 u, legP_eq_2 u, legP_eq_4 u, legP_eq_6 u]
  dsimp only [legList_0, legList_2, legList_4, legList_6, polyEval]; ring
private theorem pow_eq_leg_sum_4 (u : ℝ) :
    u ^ 8 = ∑ k : Fin 12, monToLegMat ⟨4, by omega⟩ k * legP (degAt k) u := by
  rw [sum_finK]; dsimp only [monToLegMat, matAt, listAt, coeffAt, degAt]
  rw [legP_eq_0 u, legP_eq_2 u, legP_eq_4 u, legP_eq_6 u, legP_eq_8 u]
  dsimp only [legList_0, legList_2, legList_4, legList_6, legList_8, polyEval]; ring
private theorem pow_eq_leg_sum_5 (u : ℝ) :
    u ^ 10 = ∑ k : Fin 12, monToLegMat ⟨5, by omega⟩ k * legP (degAt k) u := by
  rw [sum_finK]; dsimp only [monToLegMat, matAt, listAt, coeffAt, degAt]
  rw [legP_eq_0 u, legP_eq_2 u, legP_eq_4 u, legP_eq_6 u, legP_eq_8 u, legP_eq_10 u]
  dsimp only [legList_0, legList_2, legList_4, legList_6, legList_8, legList_10, polyEval]; ring
private theorem pow_eq_leg_sum_6 (u : ℝ) :
    u ^ 12 = ∑ k : Fin 12, monToLegMat ⟨6, by omega⟩ k * legP (degAt k) u := by
  rw [sum_finK]; dsimp only [monToLegMat, matAt, listAt, coeffAt, degAt]
  rw [legP_eq_0 u, legP_eq_2 u, legP_eq_4 u, legP_eq_6 u, legP_eq_8 u, legP_eq_10 u, legP_eq_12 u]
  dsimp only [legList_0, legList_2, legList_4, legList_6, legList_8, legList_10, legList_12, polyEval]; ring
private theorem pow_eq_leg_sum_7 (u : ℝ) :
    u ^ 14 = ∑ k : Fin 12, monToLegMat ⟨7, by omega⟩ k * legP (degAt k) u := by
  rw [sum_finK]; dsimp only [monToLegMat, matAt, listAt, coeffAt, degAt]
  rw [legP_eq_0 u, legP_eq_2 u, legP_eq_4 u, legP_eq_6 u, legP_eq_8 u, legP_eq_10 u, legP_eq_12 u, legP_eq_14 u]
  dsimp only [legList_0, legList_2, legList_4, legList_6, legList_8, legList_10, legList_12, legList_14, polyEval]; ring
private theorem pow_eq_leg_sum_8 (u : ℝ) :
    u ^ 16 = ∑ k : Fin 12, monToLegMat ⟨8, by omega⟩ k * legP (degAt k) u := by
  rw [sum_finK]; dsimp only [monToLegMat, matAt, listAt, coeffAt, degAt]
  rw [legP_eq_0 u, legP_eq_2 u, legP_eq_4 u, legP_eq_6 u, legP_eq_8 u, legP_eq_10 u, legP_eq_12 u, legP_eq_14 u, legP_eq_16 u]
  dsimp only [legList_0, legList_2, legList_4, legList_6, legList_8, legList_10, legList_12, legList_14, legList_16, polyEval]; ring
private theorem pow_eq_leg_sum_9 (u : ℝ) :
    u ^ 18 = ∑ k : Fin 12, monToLegMat ⟨9, by omega⟩ k * legP (degAt k) u := by
  rw [sum_finK]; dsimp only [monToLegMat, matAt, listAt, coeffAt, degAt]
  rw [legP_eq_0 u, legP_eq_2 u, legP_eq_4 u, legP_eq_6 u, legP_eq_8 u, legP_eq_10 u, legP_eq_12 u, legP_eq_14 u, legP_eq_16 u, legP_eq_18 u]
  dsimp only [legList_0, legList_2, legList_4, legList_6, legList_8, legList_10, legList_12, legList_14, legList_16, legList_18, polyEval]; ring
private theorem pow_eq_leg_sum_10 (u : ℝ) :
    u ^ 20 = ∑ k : Fin 12, monToLegMat ⟨10, by omega⟩ k * legP (degAt k) u := by
  rw [sum_finK]; dsimp only [monToLegMat, matAt, listAt, coeffAt, degAt]
  rw [legP_eq_0 u, legP_eq_2 u, legP_eq_4 u, legP_eq_6 u, legP_eq_8 u, legP_eq_10 u, legP_eq_12 u, legP_eq_14 u, legP_eq_16 u, legP_eq_18 u, legP_eq_20 u]
  dsimp only [legList_0, legList_2, legList_4, legList_6, legList_8, legList_10, legList_12, legList_14, legList_16, legList_18, legList_20, polyEval]; ring
private theorem pow_eq_leg_sum_11 (u : ℝ) :
    u ^ 22 = ∑ k : Fin 12, monToLegMat ⟨11, by omega⟩ k * legP (degAt k) u := by
  rw [sum_finK]; dsimp only [monToLegMat, matAt, listAt, coeffAt, degAt]
  rw [legP_eq_0 u, legP_eq_2 u, legP_eq_4 u, legP_eq_6 u, legP_eq_8 u, legP_eq_10 u, legP_eq_12 u, legP_eq_14 u, legP_eq_16 u, legP_eq_18 u, legP_eq_20 u, legP_eq_22 u]
  dsimp only [legList_0, legList_2, legList_4, legList_6, legList_8, legList_10, legList_12, legList_14, legList_16, legList_18, legList_20, legList_22, polyEval]; ring

private theorem mon_moment_eq_leg_sum {G : ℝ → ℝ} (hGc : Continuous G) (j : Fin 12) :
    (∫ u in (0 : ℝ)..1, u ^ (degAt j) * G u) = ∑ k : Fin 12, monToLegMat j k * halfMoment G k := by
  have hpow : ∀ u : ℝ, u ^ (degAt j) = ∑ k : Fin 12, monToLegMat j k * legP (degAt k) u := by
    rcases j with ⟨jv, hjv⟩; interval_cases jv
    · exact pow_eq_leg_sum_0
    · exact pow_eq_leg_sum_1
    · exact pow_eq_leg_sum_2
    · exact pow_eq_leg_sum_3
    · exact pow_eq_leg_sum_4
    · exact pow_eq_leg_sum_5
    · exact pow_eq_leg_sum_6
    · exact pow_eq_leg_sum_7
    · exact pow_eq_leg_sum_8
    · exact pow_eq_leg_sum_9
    · exact pow_eq_leg_sum_10
    · exact pow_eq_leg_sum_11
  have hfn : ∀ u : ℝ, u ^ (degAt j) * G u =
      ∑ k : Fin 12, monToLegMat j k * (G u * legP (degAt k) u) := fun u => by
    rw [hpow u, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [hfn]
  rw [intervalIntegral.integral_finsetSum fun k _ =>
    (show Continuous fun u : ℝ => monToLegMat j k * (G u * legP (degAt k) u) from
      continuous_const.mul (hGc.mul (continuous_legP _))).intervalIntegrable 0 1]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul]; rfl

private def apow0_1 : ℝ := (5545177444479562475337857 / 8000000000000000000000000 : ℝ)
private def errApow_1 : ℝ := (1 / 200000000000000000000000000 : ℝ)
private theorem abs_aperture_pow_1_sub : |apertureLogTwo ^ 1 - apow0_1| ≤ errApow_1 := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  unfold apertureLogTwo
  have hl0 : (0 : ℝ) ≤ logTwoLo := by norm_num [logTwoLo]
  have ha0 : (0 : ℝ) ≤ Real.log 2 := by linarith
  have hlo : logTwoLo ^ 1 ≤ (Real.log 2) ^ 1 := pow_le_pow_left₀ hl0 h2l 1
  have hhi : (Real.log 2) ^ 1 ≤ logTwoHi ^ 1 := pow_le_pow_left₀ ha0 h2u 1
  have c1 : apow0_1 - errApow_1 ≤ logTwoLo ^ 1 := by norm_num [apow0_1, errApow_1, logTwoLo]
  have c2 : logTwoHi ^ 1 ≤ apow0_1 + errApow_1 := by norm_num [apow0_1, errApow_1, logTwoHi]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private def apow0_2 : ℝ := (480453013918201424667102531237 / 1000000000000000000000000000000 : ℝ)
private def errApow_2 : ℝ := (1733 / 250000000000000000000000000000 : ℝ)
private theorem abs_aperture_pow_2_sub : |apertureLogTwo ^ 2 - apow0_2| ≤ errApow_2 := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  unfold apertureLogTwo
  have hl0 : (0 : ℝ) ≤ logTwoLo := by norm_num [logTwoLo]
  have ha0 : (0 : ℝ) ≤ Real.log 2 := by linarith
  have hlo : logTwoLo ^ 2 ≤ (Real.log 2) ^ 2 := pow_le_pow_left₀ hl0 h2l 2
  have hhi : (Real.log 2) ^ 2 ≤ logTwoHi ^ 2 := pow_le_pow_left₀ ha0 h2u 2
  have c1 : apow0_2 - errApow_2 ≤ logTwoLo ^ 2 := by norm_num [apow0_2, errApow_2, logTwoLo]
  have c2 : logTwoHi ^ 2 ≤ apow0_2 + errApow_2 := by norm_num [apow0_2, errApow_2, logTwoHi]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private def apow0_3 : ℝ := (333024651988929479718853587717 / 1000000000000000000000000000000 : ℝ)
private def errApow_3 : ℝ := (901 / 125000000000000000000000000000 : ℝ)
private theorem abs_aperture_pow_3_sub : |apertureLogTwo ^ 3 - apow0_3| ≤ errApow_3 := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  unfold apertureLogTwo
  have hl0 : (0 : ℝ) ≤ logTwoLo := by norm_num [logTwoLo]
  have ha0 : (0 : ℝ) ≤ Real.log 2 := by linarith
  have hlo : logTwoLo ^ 3 ≤ (Real.log 2) ^ 3 := pow_le_pow_left₀ hl0 h2l 3
  have hhi : (Real.log 2) ^ 3 ≤ logTwoHi ^ 3 := pow_le_pow_left₀ ha0 h2u 3
  have c1 : apow0_3 - errApow_3 ≤ logTwoLo ^ 3 := by norm_num [apow0_3, errApow_3, logTwoLo]
  have c2 : logTwoHi ^ 3 ≤ apow0_3 + errApow_3 := by norm_num [apow0_3, errApow_3, logTwoHi]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private def apow0_4 : ℝ := (115417549291541725943748861243 / 500000000000000000000000000000 : ℝ)
private def errApow_4 : ℝ := (6661 / 1000000000000000000000000000000 : ℝ)
private theorem abs_aperture_pow_4_sub : |apertureLogTwo ^ 4 - apow0_4| ≤ errApow_4 := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  unfold apertureLogTwo
  have hl0 : (0 : ℝ) ≤ logTwoLo := by norm_num [logTwoLo]
  have ha0 : (0 : ℝ) ≤ Real.log 2 := by linarith
  have hlo : logTwoLo ^ 4 ≤ (Real.log 2) ^ 4 := pow_le_pow_left₀ hl0 h2l 4
  have hhi : (Real.log 2) ^ 4 ≤ logTwoHi ^ 4 := pow_le_pow_left₀ ha0 h2u 4
  have c1 : apow0_4 - errApow_4 ≤ logTwoLo ^ 4 := by norm_num [apow0_4, errApow_4, logTwoLo]
  have c2 : logTwoHi ^ 4 ≤ apow0_4 + errApow_4 := by norm_num [apow0_4, errApow_4, logTwoHi]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private def apow0_5 : ℝ := (20000337219642665135118333493 / 125000000000000000000000000000 : ℝ)
private def errApow_5 : ℝ := (1443 / 250000000000000000000000000000 : ℝ)
private theorem abs_aperture_pow_5_sub : |apertureLogTwo ^ 5 - apow0_5| ≤ errApow_5 := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  unfold apertureLogTwo
  have hl0 : (0 : ℝ) ≤ logTwoLo := by norm_num [logTwoLo]
  have ha0 : (0 : ℝ) ≤ Real.log 2 := by linarith
  have hlo : logTwoLo ^ 5 ≤ (Real.log 2) ^ 5 := pow_le_pow_left₀ hl0 h2l 5
  have hhi : (Real.log 2) ^ 5 ≤ logTwoHi ^ 5 := pow_le_pow_left₀ ha0 h2u 5
  have c1 : apow0_5 - errApow_5 ≤ logTwoLo ^ 5 := by norm_num [apow0_5, errApow_5, logTwoLo]
  have c2 : logTwoHi ^ 5 ≤ apow0_5 + errApow_5 := by norm_num [apow0_5, errApow_5, logTwoHi]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private def apow0_6 : ℝ := (27726354708086897917986776049 / 250000000000000000000000000000 : ℝ)
private def errApow_6 : ℝ := (4801 / 1000000000000000000000000000000 : ℝ)
private theorem abs_aperture_pow_6_sub : |apertureLogTwo ^ 6 - apow0_6| ≤ errApow_6 := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  unfold apertureLogTwo
  have hl0 : (0 : ℝ) ≤ logTwoLo := by norm_num [logTwoLo]
  have ha0 : (0 : ℝ) ≤ Real.log 2 := by linarith
  have hlo : logTwoLo ^ 6 ≤ (Real.log 2) ^ 6 := pow_le_pow_left₀ hl0 h2l 6
  have hhi : (Real.log 2) ^ 6 ≤ logTwoHi ^ 6 := pow_le_pow_left₀ ha0 h2u 6
  have c1 : apow0_6 - errApow_6 ≤ logTwoLo ^ 6 := by norm_num [apow0_6, errApow_6, logTwoLo]
  have c2 : logTwoHi ^ 6 ≤ apow0_6 + errApow_6 := by norm_num [apow0_6, errApow_6, logTwoHi]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private def apow0_7 : ℝ := (7687377837246159501132821537 / 100000000000000000000000000000 : ℝ)
private def errApow_7 : ℝ := (1941 / 500000000000000000000000000000 : ℝ)
private theorem abs_aperture_pow_7_sub : |apertureLogTwo ^ 7 - apow0_7| ≤ errApow_7 := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  unfold apertureLogTwo
  have hl0 : (0 : ℝ) ≤ logTwoLo := by norm_num [logTwoLo]
  have ha0 : (0 : ℝ) ≤ Real.log 2 := by linarith
  have hlo : logTwoLo ^ 7 ≤ (Real.log 2) ^ 7 := pow_le_pow_left₀ hl0 h2l 7
  have hhi : (Real.log 2) ^ 7 ≤ logTwoHi ^ 7 := pow_le_pow_left₀ ha0 h2u 7
  have c1 : apow0_7 - errApow_7 ≤ logTwoLo ^ 7 := by norm_num [apow0_7, errApow_7, logTwoLo]
  have c2 : logTwoHi ^ 7 ≤ apow0_7 + errApow_7 := by norm_num [apow0_7, errApow_7, logTwoHi]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private def apow0_8 : ℝ := (10656968547572371171448791071 / 200000000000000000000000000000 : ℝ)
private def errApow_8 : ℝ := (769 / 250000000000000000000000000000 : ℝ)
private theorem abs_aperture_pow_8_sub : |apertureLogTwo ^ 8 - apow0_8| ≤ errApow_8 := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  unfold apertureLogTwo
  have hl0 : (0 : ℝ) ≤ logTwoLo := by norm_num [logTwoLo]
  have ha0 : (0 : ℝ) ≤ Real.log 2 := by linarith
  have hlo : logTwoLo ^ 8 ≤ (Real.log 2) ^ 8 := pow_le_pow_left₀ hl0 h2l 8
  have hhi : (Real.log 2) ^ 8 ≤ logTwoHi ^ 8 := pow_le_pow_left₀ ha0 h2u 8
  have c1 : apow0_8 - errApow_8 ≤ logTwoLo ^ 8 := by norm_num [apow0_8, errApow_8, logTwoLo]
  have c2 : logTwoHi ^ 8 ≤ apow0_8 + errApow_8 := by norm_num [apow0_8, errApow_8, logTwoHi]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private def apow0_9 : ℝ := (36934238510329022371115741269 / 1000000000000000000000000000000 : ℝ)
private def errApow_9 : ℝ := (2399 / 1000000000000000000000000000000 : ℝ)
private theorem abs_aperture_pow_9_sub : |apertureLogTwo ^ 9 - apow0_9| ≤ errApow_9 := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  unfold apertureLogTwo
  have hl0 : (0 : ℝ) ≤ logTwoLo := by norm_num [logTwoLo]
  have ha0 : (0 : ℝ) ≤ Real.log 2 := by linarith
  have hlo : logTwoLo ^ 9 ≤ (Real.log 2) ^ 9 := pow_le_pow_left₀ hl0 h2l 9
  have hhi : (Real.log 2) ^ 9 ≤ logTwoHi ^ 9 := pow_le_pow_left₀ ha0 h2u 9
  have c1 : apow0_9 - errApow_9 ≤ logTwoLo ^ 9 := by norm_num [apow0_9, errApow_9, logTwoLo]
  have c2 : logTwoHi ^ 9 ≤ apow0_9 + errApow_9 := by norm_num [apow0_9, errApow_9, logTwoHi]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private def apow0_10 : ℝ := (25600863289563116339451824457 / 1000000000000000000000000000000 : ℝ)
private def errApow_10 : ℝ := (231 / 125000000000000000000000000000 : ℝ)
private theorem abs_aperture_pow_10_sub : |apertureLogTwo ^ 10 - apow0_10| ≤ errApow_10 := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  unfold apertureLogTwo
  have hl0 : (0 : ℝ) ≤ logTwoLo := by norm_num [logTwoLo]
  have ha0 : (0 : ℝ) ≤ Real.log 2 := by linarith
  have hlo : logTwoLo ^ 10 ≤ (Real.log 2) ^ 10 := pow_le_pow_left₀ hl0 h2l 10
  have hhi : (Real.log 2) ^ 10 ≤ logTwoHi ^ 10 := pow_le_pow_left₀ ha0 h2u 10
  have c1 : apow0_10 - errApow_10 ≤ logTwoLo ^ 10 := by norm_num [apow0_10, errApow_10, logTwoLo]
  have c2 : logTwoHi ^ 10 ≤ apow0_10 + errApow_10 := by norm_num [apow0_10, errApow_10, logTwoHi]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private def apow0_11 : ℝ := (8872583104530640419362816557 / 500000000000000000000000000000 : ℝ)
private def errApow_11 : ℝ := (1409 / 1000000000000000000000000000000 : ℝ)
private theorem abs_aperture_pow_11_sub : |apertureLogTwo ^ 11 - apow0_11| ≤ errApow_11 := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  unfold apertureLogTwo
  have hl0 : (0 : ℝ) ≤ logTwoLo := by norm_num [logTwoLo]
  have ha0 : (0 : ℝ) ≤ Real.log 2 := by linarith
  have hlo : logTwoLo ^ 11 ≤ (Real.log 2) ^ 11 := pow_le_pow_left₀ hl0 h2l 11
  have hhi : (Real.log 2) ^ 11 ≤ logTwoHi ^ 11 := pow_le_pow_left₀ ha0 h2u 11
  have c1 : apow0_11 - errApow_11 ≤ logTwoLo ^ 11 := by norm_num [apow0_11, errApow_11, logTwoLo]
  have c2 : logTwoHi ^ 11 ≤ apow0_11 + errApow_11 := by norm_num [apow0_11, errApow_11, logTwoHi]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private def apow0_12 : ℝ := (3075002981594609961035934573 / 250000000000000000000000000000 : ℝ)
private def errApow_12 : ℝ := (533 / 500000000000000000000000000000 : ℝ)
private theorem abs_aperture_pow_12_sub : |apertureLogTwo ^ 12 - apow0_12| ≤ errApow_12 := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  unfold apertureLogTwo
  have hl0 : (0 : ℝ) ≤ logTwoLo := by norm_num [logTwoLo]
  have ha0 : (0 : ℝ) ≤ Real.log 2 := by linarith
  have hlo : logTwoLo ^ 12 ≤ (Real.log 2) ^ 12 := pow_le_pow_left₀ hl0 h2l 12
  have hhi : (Real.log 2) ^ 12 ≤ logTwoHi ^ 12 := pow_le_pow_left₀ ha0 h2u 12
  have c1 : apow0_12 - errApow_12 ≤ logTwoLo ^ 12 := by norm_num [apow0_12, errApow_12, logTwoLo]
  have c2 : logTwoHi ^ 12 ≤ apow0_12 + errApow_12 := by norm_num [apow0_12, errApow_12, logTwoHi]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private def apow0_13 : ℝ := (4262859293811458587359746287 / 500000000000000000000000000000 : ℝ)
private def errApow_13 : ℝ := (1 / 1250000000000000000000000000 : ℝ)
private theorem abs_aperture_pow_13_sub : |apertureLogTwo ^ 13 - apow0_13| ≤ errApow_13 := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  unfold apertureLogTwo
  have hl0 : (0 : ℝ) ≤ logTwoLo := by norm_num [logTwoLo]
  have ha0 : (0 : ℝ) ≤ Real.log 2 := by linarith
  have hlo : logTwoLo ^ 13 ≤ (Real.log 2) ^ 13 := pow_le_pow_left₀ hl0 h2l 13
  have hhi : (Real.log 2) ^ 13 ≤ logTwoHi ^ 13 := pow_le_pow_left₀ ha0 h2u 13
  have c1 : apow0_13 - errApow_13 ≤ logTwoLo ^ 13 := by norm_num [apow0_13, errApow_13, logTwoLo]
  have c2 : logTwoHi ^ 13 ≤ apow0_13 + errApow_13 := by norm_num [apow0_13, errApow_13, logTwoHi]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private def apow0_14 : ℝ := (1181915560251668815116229037 / 200000000000000000000000000000 : ℝ)
private def errApow_14 : ℝ := (299 / 500000000000000000000000000000 : ℝ)
private theorem abs_aperture_pow_14_sub : |apertureLogTwo ^ 14 - apow0_14| ≤ errApow_14 := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  unfold apertureLogTwo
  have hl0 : (0 : ℝ) ≤ logTwoLo := by norm_num [logTwoLo]
  have ha0 : (0 : ℝ) ≤ Real.log 2 := by linarith
  have hlo : logTwoLo ^ 14 ≤ (Real.log 2) ^ 14 := pow_le_pow_left₀ hl0 h2l 14
  have hhi : (Real.log 2) ^ 14 ≤ logTwoHi ^ 14 := pow_le_pow_left₀ ha0 h2u 14
  have c1 : apow0_14 - errApow_14 ≤ logTwoLo ^ 14 := by norm_num [apow0_14, errApow_14, logTwoLo]
  have c2 : logTwoHi ^ 14 ≤ apow0_14 + errApow_14 := by norm_num [apow0_14, errApow_14, logTwoHi]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private def apow0_15 : ℝ := (4096207191241862017909587413 / 1000000000000000000000000000000 : ℝ)
private def errApow_15 : ℝ := (111 / 250000000000000000000000000000 : ℝ)
private theorem abs_aperture_pow_15_sub : |apertureLogTwo ^ 15 - apow0_15| ≤ errApow_15 := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  unfold apertureLogTwo
  have hl0 : (0 : ℝ) ≤ logTwoLo := by norm_num [logTwoLo]
  have ha0 : (0 : ℝ) ≤ Real.log 2 := by linarith
  have hlo : logTwoLo ^ 15 ≤ (Real.log 2) ^ 15 := pow_le_pow_left₀ hl0 h2l 15
  have hhi : (Real.log 2) ^ 15 ≤ logTwoHi ^ 15 := pow_le_pow_left₀ ha0 h2u 15
  have c1 : apow0_15 - errApow_15 ≤ logTwoLo ^ 15 := by norm_num [apow0_15, errApow_15, logTwoLo]
  have c2 : logTwoHi ^ 15 ≤ apow0_15 + errApow_15 := by norm_num [apow0_15, errApow_15, logTwoHi]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private def apow0_16 : ℝ := (1419637232799334679400077881 / 500000000000000000000000000000 : ℝ)
private def errApow_16 : ℝ := (41 / 125000000000000000000000000000 : ℝ)
private theorem abs_aperture_pow_16_sub : |apertureLogTwo ^ 16 - apow0_16| ≤ errApow_16 := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  unfold apertureLogTwo
  have hl0 : (0 : ℝ) ≤ logTwoLo := by norm_num [logTwoLo]
  have ha0 : (0 : ℝ) ≤ Real.log 2 := by linarith
  have hlo : logTwoLo ^ 16 ≤ (Real.log 2) ^ 16 := pow_le_pow_left₀ hl0 h2l 16
  have hhi : (Real.log 2) ^ 16 ≤ logTwoHi ^ 16 := pow_le_pow_left₀ ha0 h2u 16
  have c1 : apow0_16 - errApow_16 ≤ logTwoLo ^ 16 := by norm_num [apow0_16, errApow_16, logTwoLo]
  have c2 : logTwoHi ^ 16 ≤ apow0_16 + errApow_16 := by norm_num [apow0_16, errApow_16, logTwoHi]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private def apow0_17 : ℝ := (1968035090665563096964829453 / 1000000000000000000000000000000 : ℝ)
private def errApow_17 : ℝ := (121 / 500000000000000000000000000000 : ℝ)
private theorem abs_aperture_pow_17_sub : |apertureLogTwo ^ 17 - apow0_17| ≤ errApow_17 := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  unfold apertureLogTwo
  have hl0 : (0 : ℝ) ≤ logTwoLo := by norm_num [logTwoLo]
  have ha0 : (0 : ℝ) ≤ Real.log 2 := by linarith
  have hlo : logTwoLo ^ 17 ≤ (Real.log 2) ^ 17 := pow_le_pow_left₀ hl0 h2l 17
  have hhi : (Real.log 2) ^ 17 ≤ logTwoHi ^ 17 := pow_le_pow_left₀ ha0 h2u 17
  have c1 : apow0_17 - errApow_17 ≤ logTwoLo ^ 17 := by norm_num [apow0_17, errApow_17, logTwoLo]
  have c2 : logTwoHi ^ 17 ≤ apow0_17 + errApow_17 := by norm_num [apow0_17, errApow_17, logTwoHi]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private def apow0_18 : ℝ := (1364137974337871401559937301 / 1000000000000000000000000000000 : ℝ)
private def errApow_18 : ℝ := (89 / 500000000000000000000000000000 : ℝ)
private theorem abs_aperture_pow_18_sub : |apertureLogTwo ^ 18 - apow0_18| ≤ errApow_18 := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  unfold apertureLogTwo
  have hl0 : (0 : ℝ) ≤ logTwoLo := by norm_num [logTwoLo]
  have ha0 : (0 : ℝ) ≤ Real.log 2 := by linarith
  have hlo : logTwoLo ^ 18 ≤ (Real.log 2) ^ 18 := pow_le_pow_left₀ hl0 h2l 18
  have hhi : (Real.log 2) ^ 18 ≤ logTwoHi ^ 18 := pow_le_pow_left₀ ha0 h2u 18
  have c1 : apow0_18 - errApow_18 ≤ logTwoLo ^ 18 := by norm_num [apow0_18, errApow_18, logTwoLo]
  have c2 : logTwoHi ^ 18 ≤ apow0_18 + errApow_18 := by norm_num [apow0_18, errApow_18, logTwoHi]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private def apow0_19 : ℝ := (4727741954035252946611669 / 5000000000000000000000000000 : ℝ)
private def errApow_19 : ℝ := (13 / 100000000000000000000000000000 : ℝ)
private theorem abs_aperture_pow_19_sub : |apertureLogTwo ^ 19 - apow0_19| ≤ errApow_19 := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  unfold apertureLogTwo
  have hl0 : (0 : ℝ) ≤ logTwoLo := by norm_num [logTwoLo]
  have ha0 : (0 : ℝ) ≤ Real.log 2 := by linarith
  have hlo : logTwoLo ^ 19 ≤ (Real.log 2) ^ 19 := pow_le_pow_left₀ hl0 h2l 19
  have hhi : (Real.log 2) ^ 19 ≤ logTwoHi ^ 19 := pow_le_pow_left₀ ha0 h2u 19
  have c1 : apow0_19 - errApow_19 ≤ logTwoLo ^ 19 := by norm_num [apow0_19, errApow_19, logTwoLo]
  have c2 : logTwoHi ^ 19 ≤ apow0_19 + errApow_19 := by norm_num [apow0_19, errApow_19, logTwoHi]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private def apow0_20 : ℝ := (13108084023418008527310673 / 20000000000000000000000000000 : ℝ)
private def errApow_20 : ℝ := (19 / 200000000000000000000000000000 : ℝ)
private theorem abs_aperture_pow_20_sub : |apertureLogTwo ^ 20 - apow0_20| ≤ errApow_20 := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  unfold apertureLogTwo
  have hl0 : (0 : ℝ) ≤ logTwoLo := by norm_num [logTwoLo]
  have ha0 : (0 : ℝ) ≤ Real.log 2 := by linarith
  have hlo : logTwoLo ^ 20 ≤ (Real.log 2) ^ 20 := pow_le_pow_left₀ hl0 h2l 20
  have hhi : (Real.log 2) ^ 20 ≤ logTwoHi ^ 20 := pow_le_pow_left₀ ha0 h2u 20
  have c1 : apow0_20 - errApow_20 ≤ logTwoLo ^ 20 := by norm_num [apow0_20, errApow_20, logTwoLo]
  have c2 : logTwoHi ^ 20 ≤ apow0_20 + errApow_20 := by norm_num [apow0_20, errApow_20, logTwoHi]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private def apow0_21 : ℝ := (454291574168752836814060987 / 1000000000000000000000000000000 : ℝ)
private def errApow_21 : ℝ := (7 / 100000000000000000000000000000 : ℝ)
private theorem abs_aperture_pow_21_sub : |apertureLogTwo ^ 21 - apow0_21| ≤ errApow_21 := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  unfold apertureLogTwo
  have hl0 : (0 : ℝ) ≤ logTwoLo := by norm_num [logTwoLo]
  have ha0 : (0 : ℝ) ≤ Real.log 2 := by linarith
  have hlo : logTwoLo ^ 21 ≤ (Real.log 2) ^ 21 := pow_le_pow_left₀ hl0 h2l 21
  have hhi : (Real.log 2) ^ 21 ≤ logTwoHi ^ 21 := pow_le_pow_left₀ ha0 h2u 21
  have c1 : apow0_21 - errApow_21 ≤ logTwoLo ^ 21 := by norm_num [apow0_21, errApow_21, logTwoLo]
  have c2 : logTwoHi ^ 21 ≤ apow0_21 + errApow_21 := by norm_num [apow0_21, errApow_21, logTwoHi]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private def apow0_22 : ℝ := (157445461893605154509115161 / 500000000000000000000000000000 : ℝ)
private def errApow_22 : ℝ := (51 / 1000000000000000000000000000000 : ℝ)
private theorem abs_aperture_pow_22_sub : |apertureLogTwo ^ 22 - apow0_22| ≤ errApow_22 := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  unfold apertureLogTwo
  have hl0 : (0 : ℝ) ≤ logTwoLo := by norm_num [logTwoLo]
  have ha0 : (0 : ℝ) ≤ Real.log 2 := by linarith
  have hlo : logTwoLo ^ 22 ≤ (Real.log 2) ^ 22 := pow_le_pow_left₀ hl0 h2l 22
  have hhi : (Real.log 2) ^ 22 ≤ logTwoHi ^ 22 := pow_le_pow_left₀ ha0 h2u 22
  have c1 : apow0_22 - errApow_22 ≤ logTwoLo ^ 22 := by norm_num [apow0_22, errApow_22, logTwoLo]
  have c2 : logTwoHi ^ 22 ≤ apow0_22 + errApow_22 := by norm_num [apow0_22, errApow_22, logTwoHi]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
private def apow0_23 : ℝ := (54566439001755360378905613 / 250000000000000000000000000000 : ℝ)
private def errApow_23 : ℝ := (37 / 1000000000000000000000000000000 : ℝ)
private theorem abs_aperture_pow_23_sub : |apertureLogTwo ^ 23 - apow0_23| ≤ errApow_23 := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  unfold apertureLogTwo
  have hl0 : (0 : ℝ) ≤ logTwoLo := by norm_num [logTwoLo]
  have ha0 : (0 : ℝ) ≤ Real.log 2 := by linarith
  have hlo : logTwoLo ^ 23 ≤ (Real.log 2) ^ 23 := pow_le_pow_left₀ hl0 h2l 23
  have hhi : (Real.log 2) ^ 23 ≤ logTwoHi ^ 23 := pow_le_pow_left₀ ha0 h2u 23
  have c1 : apow0_23 - errApow_23 ≤ logTwoLo ^ 23 := by norm_num [apow0_23, errApow_23, logTwoLo]
  have c2 : logTwoHi ^ 23 ≤ apow0_23 + errApow_23 := by norm_num [apow0_23, errApow_23, logTwoHi]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private def qEvMat_0 (i j : Fin 12) : ℝ :=
  matAt ([([105091 / 5000000000000000000] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qEvMat_0_sym (i j : Fin 12) : qEvMat_0 i j = qEvMat_0 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qEvRowAbs_0 (i : Fin 12) : ℝ := coeffAt ([105091 / 5000000000000000000] : List ℝ) i.1
private theorem qEvRowAbs_0_eq (i : Fin 12) :
    (∑ j : Fin 12, |qEvMat_0 i j|) = qEvRowAbs_0 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qEvMat_0, qEvRowAbs_0, matAt, listAt, coeffAt]; norm_num)

private def qEvMat_1 (i j : Fin 12) : ℝ :=
  matAt ([([24999999999449249 / 600000000000000000, 24999999999449249 / 600000000000000000] : List ℝ),
    ([24999999999449249 / 600000000000000000] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qEvMat_1_sym (i j : Fin 12) : qEvMat_1 i j = qEvMat_1 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qEvRowAbs_1 (i : Fin 12) : ℝ := coeffAt ([24999999999449249 / 300000000000000000, 24999999999449249 / 600000000000000000] : List ℝ) i.1
private theorem qEvRowAbs_1_eq (i : Fin 12) :
    (∑ j : Fin 12, |qEvMat_1 i j|) = qEvRowAbs_1 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qEvMat_1, qEvRowAbs_1, matAt, listAt, coeffAt]; norm_num)

private def qEvMat_2 (i j : Fin 12) : ℝ :=
  matAt ([([-21701388747345021 / 3125000000000000000, -21701388747345021 / 1750000000000000000, -65104166242035063 / 43750000000000000000] : List ℝ),
    ([-21701388747345021 / 1750000000000000000, -21701388747345021 / 1250000000000000000] : List ℝ),
    ([-65104166242035063 / 43750000000000000000] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qEvMat_2_sym (i j : Fin 12) : qEvMat_2 i j = qEvMat_2 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qEvRowAbs_2 (i : Fin 12) : ℝ := coeffAt ([65104166242035063 / 3125000000000000000, 65104166242035063 / 2187500000000000000, 65104166242035063 / 43750000000000000000] : List ℝ) i.1
private theorem qEvRowAbs_2_eq (i : Fin 12) :
    (∑ j : Fin 12, |qEvMat_2 i j|) = qEvRowAbs_2 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qEvMat_2, qEvRowAbs_2, matAt, listAt, coeffAt]; norm_num)

private def qEvMat_3 (i j : Fin 12) : ℝ :=
  matAt ([([3309458785969429 / 2187500000000000000, 3309458785969429 / 937500000000000000, 3309458785969429 / 3437500000000000000, 3309458785969429 / 72187500000000000000] : List ℝ),
    ([3309458785969429 / 937500000000000000, 3309458785969429 / 437500000000000000, 3309458785969429 / 2187500000000000000] : List ℝ),
    ([3309458785969429 / 3437500000000000000, 3309458785969429 / 2187500000000000000] : List ℝ),
    ([3309458785969429 / 72187500000000000000] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qEvMat_3_sym (i j : Fin 12) : qEvMat_3 i j = qEvMat_3 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qEvRowAbs_3 (i : Fin 12) : ℝ := coeffAt ([3309458785969429 / 546875000000000000, 3309458785969429 / 262500000000000000, 29785129073724861 / 12031250000000000000, 3309458785969429 / 72187500000000000000] : List ℝ) i.1
private theorem qEvRowAbs_3_eq (i : Fin 12) :
    (∑ j : Fin 12, |qEvMat_3 i j|) = qEvRowAbs_3 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qEvMat_3, qEvRowAbs_3, matAt, listAt, coeffAt]; norm_num)

private def qEvMat_4 (i j : Fin 12) : ℝ :=
  matAt ([([-5366589076364431 / 14062500000000000000, -5366589076364431 / 5156250000000000000, -48299301687279879 / 111718750000000000000, -5366589076364431 / 103125000000000000000, -5366589076364431 / 4021875000000000000000] : List ℝ),
    ([-5366589076364431 / 5156250000000000000, -5366589076364431 / 1968750000000000000, -48299301687279879 / 48125000000000000000, -5366589076364431 / 61875000000000000000] : List ℝ),
    ([-48299301687279879 / 111718750000000000000, -48299301687279879 / 48125000000000000000, -5366589076364431 / 21875000000000000000] : List ℝ),
    ([-5366589076364431 / 103125000000000000000, -5366589076364431 / 61875000000000000000] : List ℝ),
    ([-5366589076364431 / 4021875000000000000000] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qEvMat_4_sym (i j : Fin 12) : qEvMat_4 i j = qEvMat_4 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qEvRowAbs_4 (i : Fin 12) : ℝ := coeffAt ([5366589076364431 / 2812500000000000000, 37566123534551017 / 7734375000000000000, 37566123534551017 / 22343750000000000000, 5366589076364431 / 38671875000000000000, 5366589076364431 / 4021875000000000000000] : List ℝ) i.1
private theorem qEvRowAbs_4_eq (i : Fin 12) :
    (∑ j : Fin 12, |qEvMat_4 i j|) = qEvRowAbs_4 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qEvMat_4, qEvRowAbs_4, matAt, listAt, coeffAt]; norm_num)

private def qEvMat_5 (i j : Fin 12) : ℝ :=
  matAt ([([8726421052567571 / 82500000000000000000, 8726421052567571 / 27300000000000000000, 78537789473108139 / 455000000000000000000, 8726421052567571 / 255000000000000000000, 8726421052567571 / 3705000000000000000000, 8726421052567571 / 230945000000000000000000] : List ℝ),
    ([8726421052567571 / 27300000000000000000, 8726421052567571 / 9240000000000000000, 8726421052567571 / 18200000000000000000, 8726421052567571 / 105000000000000000000, 8726421052567571 / 2145000000000000000000] : List ℝ),
    ([78537789473108139 / 455000000000000000000, 8726421052567571 / 18200000000000000000, 78537789473108139 / 385000000000000000000, 8726421052567571 / 385000000000000000000] : List ℝ),
    ([8726421052567571 / 255000000000000000000, 8726421052567571 / 105000000000000000000, 8726421052567571 / 385000000000000000000] : List ℝ),
    ([8726421052567571 / 3705000000000000000000, 8726421052567571 / 2145000000000000000000] : List ℝ),
    ([8726421052567571 / 230945000000000000000000] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qEvMat_5_sym (i j : Fin 12) : qEvMat_5 i j = qEvMat_5 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qEvRowAbs_5 (i : Fin 12) : ℝ := coeffAt ([8726421052567571 / 13750000000000000000, 26179263157702713 / 14300000000000000000, 78537789473108139 / 89375000000000000000, 26179263157702713 / 187000000000000000000, 8726421052567571 / 1358500000000000000000, 8726421052567571 / 230945000000000000000000] : List ℝ) i.1
private theorem qEvRowAbs_5_eq (i : Fin 12) :
    (∑ j : Fin 12, |qEvMat_5 i j|) = qEvRowAbs_5 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qEvMat_5, qEvRowAbs_5, matAt, listAt, coeffAt]; norm_num)

private def qEvMat_6 (i j : Fin 12) : ℝ :=
  matAt ([([-7163072980652803 / 227500000000000000000, -7163072980652803 / 70000000000000000000, -78793802787180833 / 1190000000000000000000, -1024319436233350829 / 56525000000000000000000, -7163072980652803 / 3325000000000000000000, -7163072980652803 / 74290000000000000000000, -7163072980652803 / 6760390000000000000000000] : List ℝ),
    ([-7163072980652803 / 70000000000000000000, -7163072980652803 / 21840000000000000000, -7163072980652803 / 35000000000000000000, -93119948748486439 / 1785000000000000000000, -7163072980652803 / 1330000000000000000000, -7163072980652803 / 41990000000000000000000] : List ℝ),
    ([-78793802787180833 / 1190000000000000000000, -7163072980652803 / 35000000000000000000, -580208911432877043 / 5005000000000000000000, -93119948748486439 / 3850000000000000000000, -7163072980652803 / 4550000000000000000000] : List ℝ),
    ([-1024319436233350829 / 56525000000000000000000, -93119948748486439 / 1785000000000000000000, -93119948748486439 / 3850000000000000000000, -7163072980652803 / 2310000000000000000000] : List ℝ),
    ([-7163072980652803 / 3325000000000000000000, -7163072980652803 / 1330000000000000000000, -7163072980652803 / 4550000000000000000000] : List ℝ),
    ([-7163072980652803 / 74290000000000000000000, -7163072980652803 / 41990000000000000000000] : List ℝ),
    ([-7163072980652803 / 6760390000000000000000000] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qEvMat_6_sym (i j : Fin 12) : qEvMat_6 i j = qEvMat_6 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qEvRowAbs_6 (i : Fin 12) : ℝ := coeffAt ([7163072980652803 / 32500000000000000000, 78793802787180833 / 113750000000000000000, 6382298025761647473 / 15470000000000000000000, 78793802787180833 / 807500000000000000000, 78793802787180833 / 8645000000000000000000, 64467656825875227 / 241442500000000000000000, 7163072980652803 / 6760390000000000000000000] : List ℝ) i.1
private theorem qEvRowAbs_6_eq (i : Fin 12) :
    (∑ j : Fin 12, |qEvMat_6 i j|) = qEvRowAbs_6 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qEvMat_6, qEvRowAbs_6, matAt, listAt, coeffAt]; norm_num)

private def qEvMat_7 (i j : Fin 12) : ℝ :=
  matAt ([([6237272726078909 / 600000000000000000000, 43660909082552363 / 1224000000000000000000, 1702775454219542157 / 64600000000000000000000, 1054099090707335621 / 116280000000000000000000, 3525415019088079 / 2280000000000000000000, 39864308292765201 / 323000000000000000000000, 271185770699083 / 69768000000000000000000, 271185770699083 / 8721000000000000000000000] : List ℝ),
    ([43660909082552363 / 1224000000000000000000, 43660909082552363 / 360000000000000000000, 130982727247657089 / 1496000000000000000000, 7378693634951349347 / 255816000000000000000000, 6237272726078909 / 1368000000000000000000, 813557312097249 / 2584000000000000000000, 271185770699083 / 38760000000000000000000] : List ℝ),
    ([1702775454219542157 / 64600000000000000000000, 130982727247657089 / 1496000000000000000000, 130982727247657089 / 2200000000000000000000, 130982727247657089 / 7480000000000000000000, 18711818178236727 / 8360000000000000000000, 6237272726078909 / 64600000000000000000000] : List ℝ),
    ([1054099090707335621 / 116280000000000000000000, 7378693634951349347 / 255816000000000000000000, 130982727247657089 / 7480000000000000000000, 81084545439025817 / 19800000000000000000000, 6237272726078909 / 19800000000000000000000] : List ℝ),
    ([3525415019088079 / 2280000000000000000000, 6237272726078909 / 1368000000000000000000, 18711818178236727 / 8360000000000000000000, 6237272726078909 / 19800000000000000000000] : List ℝ),
    ([39864308292765201 / 323000000000000000000000, 813557312097249 / 2584000000000000000000, 6237272726078909 / 64600000000000000000000] : List ℝ),
    ([271185770699083 / 69768000000000000000000, 271185770699083 / 38760000000000000000000] : List ℝ),
    ([271185770699083 / 8721000000000000000000000] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qEvMat_7_sym (i j : Fin 12) : qEvMat_7 i j = qEvMat_7 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qEvRowAbs_7 (i : Fin 12) : ℝ := coeffAt ([6237272726078909 / 75000000000000000000, 567591818073180719 / 2040000000000000000000, 6243509998804987909 / 32300000000000000000000, 11595089997780691831 / 193800000000000000000000, 24677905133616553 / 2850000000000000000000, 172745335935315871 / 323000000000000000000000, 1898300394893581 / 174420000000000000000000, 271185770699083 / 8721000000000000000000000] : List ℝ) i.1
private theorem qEvRowAbs_7_eq (i : Fin 12) :
    (∑ j : Fin 12, |qEvMat_7 i j|) = qEvRowAbs_7 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qEvMat_7, qEvRowAbs_7, matAt, listAt, coeffAt]; norm_num)

private def qEvMat_8 (i j : Fin 12) : ℝ :=
  matAt ([([-3260029542583927 / 765000000000000000000, -3260029542583927 / 213750000000000000000, -3260029542583927 / 261250000000000000000, -550944992696683663 / 108157500000000000000000, -55420502223926759 / 49162500000000000000000, -3260029542583927 / 24581250000000000000000, -3260029542583927 / 427713750000000000000000, -3260029542583927 / 18288450000000000000000000, -3260029542583927 / 3005401950000000000000000000] : List ℝ),
    ([-3260029542583927 / 213750000000000000000, -22820206798087489 / 420750000000000000000, -22820206798087489 / 522500000000000000000, -3260029542583927 / 188100000000000000000, -55420502223926759 / 15142050000000000000000, -3260029542583927 / 8193750000000000000000, -3260029542583927 / 165186000000000000000000, -3260029542583927 / 10029150000000000000000000] : List ℝ),
    ([-3260029542583927 / 261250000000000000000, -22820206798087489 / 522500000000000000000, -205381861182787401 / 6077500000000000000000, -3260029542583927 / 261250000000000000000, -55420502223926759 / 23773750000000000000000, -9780088627751781 / 48070000000000000000000, -3260029542583927 / 520030000000000000000000] : List ℝ),
    ([-550944992696683663 / 108157500000000000000000, -3260029542583927 / 188100000000000000000, -3260029542583927 / 261250000000000000000, -42380384053591051 / 10518750000000000000000, -55420502223926759 / 94050000000000000000000, -3260029542583927 / 106590000000000000000000] : List ℝ),
    ([-55420502223926759 / 49162500000000000000000, -55420502223926759 / 15142050000000000000000, -55420502223926759 / 23773750000000000000000, -55420502223926759 / 94050000000000000000000, -3260029542583927 / 64350000000000000000000] : List ℝ),
    ([-3260029542583927 / 24581250000000000000000, -3260029542583927 / 8193750000000000000000, -9780088627751781 / 48070000000000000000000, -3260029542583927 / 106590000000000000000000] : List ℝ),
    ([-3260029542583927 / 427713750000000000000000, -3260029542583927 / 165186000000000000000000, -3260029542583927 / 520030000000000000000000] : List ℝ),
    ([-3260029542583927 / 18288450000000000000000000, -3260029542583927 / 10029150000000000000000000] : List ℝ),
    ([-3260029542583927 / 3005401950000000000000000000] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qEvMat_8_sym (i j : Fin 12) : qEvMat_8 i j = qEvMat_8 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qEvRowAbs_8 (i : Fin 12) : ℝ := coeffAt ([3260029542583927 / 85000000000000000000, 3260029542583927 / 24225000000000000000, 42380384053591051 / 403750000000000000000, 550944992696683663 / 13929375000000000000000, 42380384053591051 / 5462500000000000000000, 159741447586612423 / 208940625000000000000000, 3260029542583927 / 96948450000000000000000, 3260029542583927 / 6477159375000000000000000, 3260029542583927 / 3005401950000000000000000000] : List ℝ) i.1
private theorem qEvRowAbs_8_eq (i : Fin 12) :
    (∑ j : Fin 12, |qEvMat_8 i j|) = qEvRowAbs_8 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qEvMat_8, qEvRowAbs_8, matAt, listAt, coeffAt]; norm_num)

private def qEvMat_9 (i j : Fin 12) : ℝ :=
  matAt ([([519878183231709 / 237500000000000000000, 1559634549695127 / 192500000000000000000, 79541362034451477 / 11068750000000000000000, 26513787344817159 / 7906250000000000000000, 50081598317987967 / 55343750000000000000000, 2945976371646351 / 20843750000000000000000, 8837929114939053 / 723695000000000000000000, 519878183231709 / 980375000000000000000000, 173292727743903 / 18092375000000000000000000, 173292727743903 / 3781306375000000000000000000] : List ℝ),
    ([1559634549695127 / 192500000000000000000, 1559634549695127 / 52250000000000000000, 4678903649085381 / 178750000000000000000, 26513787344817159 / 2213750000000000000000, 450734384861891703 / 143893750000000000000000, 2945976371646351 / 6325000000000000000000, 173292727743903 / 4669000000000000000000, 173292727743903 / 124775000000000000000000, 173292727743903 / 9821575000000000000000000] : List ℝ),
    ([79541362034451477 / 11068750000000000000000, 4678903649085381 / 178750000000000000000, 378991195575915861 / 16981250000000000000000, 4678903649085381 / 481250000000000000000, 1352203154585675109 / 575575000000000000000000, 126330398525305287 / 411125000000000000000000, 173292727743903 / 8855000000000000000000, 173292727743903 / 382375000000000000000000] : List ℝ),
    ([26513787344817159 / 7906250000000000000000, 26513787344817159 / 2213750000000000000000, 4678903649085381 / 481250000000000000000, 20275249146036651 / 5225000000000000000000, 1559634549695127 / 1925000000000000000000, 519878183231709 / 6325000000000000000000, 519878183231709 / 168245000000000000000000] : List ℝ),
    ([50081598317987967 / 55343750000000000000000, 450734384861891703 / 143893750000000000000000, 1352203154585675109 / 575575000000000000000000, 1559634549695127 / 1925000000000000000000, 8837929114939053 / 67925000000000000000000, 519878183231709 / 67925000000000000000000] : List ℝ),
    ([2945976371646351 / 20843750000000000000000, 2945976371646351 / 6325000000000000000000, 126330398525305287 / 411125000000000000000000, 519878183231709 / 6325000000000000000000, 519878183231709 / 67925000000000000000000] : List ℝ),
    ([8837929114939053 / 723695000000000000000000, 173292727743903 / 4669000000000000000000, 173292727743903 / 8855000000000000000000, 519878183231709 / 168245000000000000000000] : List ℝ),
    ([519878183231709 / 980375000000000000000000, 173292727743903 / 124775000000000000000000, 173292727743903 / 382375000000000000000000] : List ℝ),
    ([173292727743903 / 18092375000000000000000000, 173292727743903 / 9821575000000000000000000] : List ℝ),
    ([173292727743903 / 3781306375000000000000000000] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qEvMat_9_sym (i j : Fin 12) : qEvMat_9 i j = qEvMat_9 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qEvRowAbs_9 (i : Fin 12) : ℝ := coeffAt ([519878183231709 / 23750000000000000000, 26513787344817159 / 332500000000000000000, 715872258310063293 / 10515312500000000000000, 4480830061274099871 / 150218750000000000000000, 50081598317987967 / 6828125000000000000000, 79541362034451477 / 79206250000000000000000, 8837929114939053 / 122769687500000000000000, 8837929114939053 / 3725425000000000000000000, 4678903649085381 / 171877562500000000000000000, 173292727743903 / 3781306375000000000000000000] : List ℝ) i.1
private theorem qEvRowAbs_9_eq (i : Fin 12) :
    (∑ j : Fin 12, |qEvMat_9 i j|) = qEvRowAbs_9 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qEvMat_9, qEvRowAbs_9, matAt, listAt, coeffAt]; norm_num)

private def qEvMat_10 (i j : Fin 12) : ℝ :=
  matAt ([([-4669432996809649 / 4620000000000000000000, -4669432996809649 / 1214400000000000000000, -2395419127363349937 / 657800000000000000000000, -1508226857969516627 / 796950000000000000000000, -25639856585481782659 / 42921450000000000000000000, -10557588005786616389 / 90978800000000000000000000, -88719226939383331 / 6550473600000000000000000, -88719226939383331 / 98821800000000000000000000, -4669432996809649 / 153009800000000000000000000, -4669432996809649 / 10644519600000000000000000000, -4669432996809649 / 2756930576400000000000000000000] : List ℝ),
    ([-4669432996809649 / 1214400000000000000000, -4669432996809649 / 320320000000000000000, -126074690913860523 / 9209200000000000000000, -88719226939383331 / 12650000000000000000000, -25639856585481782659 / 11840400000000000000000000, -621034588575683317 / 1526096000000000000000000, -88719226939383331 / 1965142080000000000000000, -4669432996809649 / 1694088000000000000000000, -4669432996809649 / 57895600000000000000000000, -4669432996809649 / 5731664400000000000000000000] : List ℝ),
    ([-2395419127363349937 / 657800000000000000000000, -126074690913860523 / 9209200000000000000000, -126074690913860523 / 10010000000000000000000, -126074690913860523 / 20240000000000000000000, -2395419127363349937 / 1315600000000000000000000, -621034588575683317 / 1973400000000000000000000, -4669432996809649 / 152609600000000000000000, -4669432996809649 / 3137200000000000000000000, -4669432996809649 / 173686800000000000000000000] : List ℝ),
    ([-1508226857969516627 / 796950000000000000000000, -88719226939383331 / 12650000000000000000000, -126074690913860523 / 20240000000000000000000, -3570742879913261 / 1232000000000000000000, -4669432996809649 / 6072000000000000000000, -5768123113706037 / 50600000000000000000000, -4669432996809649 / 546480000000000000000000, -4669432996809649 / 19126800000000000000000000] : List ℝ),
    ([-25639856585481782659 / 42921450000000000000000000, -25639856585481782659 / 11840400000000000000000000, -2395419127363349937 / 1315600000000000000000000, -4669432996809649 / 6072000000000000000000, -79380360945764033 / 456456000000000000000000, -98058092933002629 / 4999280000000000000000000, -4669432996809649 / 5525520000000000000000000] : List ℝ),
    ([-10557588005786616389 / 90978800000000000000000000, -621034588575683317 / 1526096000000000000000000, -621034588575683317 / 1973400000000000000000000, -5768123113706037 / 50600000000000000000000, -98058092933002629 / 4999280000000000000000000, -274672529224097 / 217360000000000000000000] : List ℝ),
    ([-88719226939383331 / 6550473600000000000000000, -88719226939383331 / 1965142080000000000000000, -4669432996809649 / 152609600000000000000000, -4669432996809649 / 546480000000000000000000, -4669432996809649 / 5525520000000000000000000] : List ℝ),
    ([-88719226939383331 / 98821800000000000000000000, -4669432996809649 / 1694088000000000000000000, -4669432996809649 / 3137200000000000000000000, -4669432996809649 / 19126800000000000000000000] : List ℝ),
    ([-4669432996809649 / 153009800000000000000000000, -4669432996809649 / 57895600000000000000000000, -4669432996809649 / 173686800000000000000000000] : List ℝ),
    ([-4669432996809649 / 10644519600000000000000000000, -4669432996809649 / 5731664400000000000000000000] : List ℝ),
    ([-4669432996809649 / 2756930576400000000000000000000] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qEvMat_10_sym (i j : Fin 12) : qEvMat_10 i j = qEvMat_10 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qEvRowAbs_10 (i : Fin 12) : ℝ := coeffAt ([4669432996809649 / 420000000000000000000, 88719226939383331 / 2125200000000000000000, 13574041721725649643 / 354200000000000000000000, 1508226857969516627 / 79695000000000000000000, 25639856585481782659 / 4622310000000000000000000, 1508226857969516627 / 1550775000000000000000000, 1508226857969516627 / 15284438400000000000000000, 88719226939383331 / 16470300000000000000000000, 88719226939383331 / 642641160000000000000000000, 4669432996809649 / 3725581860000000000000000000, 4669432996809649 / 2756930576400000000000000000000] : List ℝ) i.1
private theorem qEvRowAbs_10_eq (i : Fin 12) :
    (∑ j : Fin 12, |qEvMat_10 i j|) = qEvRowAbs_10 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qEvMat_10, qEvRowAbs_10, matAt, listAt, coeffAt]; norm_num)

private def qEvMat_11 (i j : Fin 12) : ℝ :=
  matAt ([([1377431922843341 / 5520000000000000000000, 15151751151276751 / 15600000000000000000000, 15151751151276751 / 15600000000000000000000, 287883271874258269 / 522000000000000000000000, 83198265571660639741 / 420732000000000000000000000, 1282389120167150471 / 28048800000000000000000000, 26171206534023479 / 3883680000000000000000000, 15151751151276751 / 24775200000000000000000000, 166669262664044261 / 5189028000000000000000000000, 15151751151276751 / 17250012000000000000000000000, 1377431922843341 / 133876922400000000000000000000, 1377431922843341 / 42081979274400000000000000000000] : List ℝ),
    ([15151751151276751 / 15600000000000000000000, 15151751151276751 / 4018560000000000000000, 136365760361490759 / 36400000000000000000000, 15151751151276751 / 7200000000000000000000, 2015182903119807883 / 2714400000000000000000000, 14106280321838655181 / 84146400000000000000000000, 9642023459903387 / 403902720000000000000000, 1377431922843341 / 669600000000000000000000, 166669262664044261 / 1676455200000000000000000000, 1377431922843341 / 589024800000000000000000000, 1377431922843341 / 71608586400000000000000000000] : List ℝ),
    ([15151751151276751 / 15600000000000000000000, 136365760361490759 / 36400000000000000000000, 1227291843253416831 / 334880000000000000000000, 136365760361490759 / 68000000000000000000000, 106062258058937257 / 156000000000000000000000, 742435806412560799 / 5127200000000000000000000, 106062258058937257 / 5609760000000000000000000, 1377431922843341 / 967200000000000000000000, 1377431922843341 / 25172000000000000000000000, 1377431922843341 / 1736868000000000000000000000] : List ℝ),
    ([287883271874258269 / 522000000000000000000000, 15151751151276751 / 7200000000000000000000, 136365760361490759 / 68000000000000000000000, 196972764966597763 / 187680000000000000000000, 15151751151276751 / 45600000000000000000000, 742435806412560799 / 11628000000000000000000000, 15151751151276751 / 2129760000000000000000000, 1377431922843341 / 3348000000000000000000000, 1377431922843341 / 148874400000000000000000000] : List ℝ),
    ([83198265571660639741 / 420732000000000000000000000, 2015182903119807883 / 2714400000000000000000000, 106062258058937257 / 156000000000000000000000, 15151751151276751 / 45600000000000000000000, 257579769571704767 / 2726880000000000000000000, 15151751151276751 / 988000000000000000000000, 1377431922843341 / 1067040000000000000000000, 1377431922843341 / 32292000000000000000000000] : List ℝ),
    ([1282389120167150471 / 28048800000000000000000000, 14106280321838655181 / 84146400000000000000000000, 742435806412560799 / 5127200000000000000000000, 742435806412560799 / 11628000000000000000000000, 15151751151276751 / 988000000000000000000000, 28926070379710161 / 15452320000000000000000000, 1377431922843341 / 15452320000000000000000000] : List ℝ),
    ([26171206534023479 / 3883680000000000000000000, 9642023459903387 / 403902720000000000000000, 106062258058937257 / 5609760000000000000000000, 15151751151276751 / 2129760000000000000000000, 1377431922843341 / 1067040000000000000000000, 1377431922843341 / 15452320000000000000000000] : List ℝ),
    ([15151751151276751 / 24775200000000000000000000, 1377431922843341 / 669600000000000000000000, 1377431922843341 / 967200000000000000000000, 1377431922843341 / 3348000000000000000000000, 1377431922843341 / 32292000000000000000000000] : List ℝ),
    ([166669262664044261 / 5189028000000000000000000000, 166669262664044261 / 1676455200000000000000000000, 1377431922843341 / 25172000000000000000000000, 1377431922843341 / 148874400000000000000000000] : List ℝ),
    ([15151751151276751 / 17250012000000000000000000000, 1377431922843341 / 589024800000000000000000000, 1377431922843341 / 1736868000000000000000000000] : List ℝ),
    ([1377431922843341 / 133876922400000000000000000000, 1377431922843341 / 71608586400000000000000000000] : List ℝ),
    ([1377431922843341 / 42081979274400000000000000000000] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qEvMat_11_sym (i j : Fin 12) : qEvMat_11 i j = qEvMat_11 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qEvRowAbs_11 (i : Fin 12) : ℝ := coeffAt ([1377431922843341 / 460000000000000000000, 106062258058937257 / 9200000000000000000000, 2015182903119807883 / 179400000000000000000000, 4894015621862390573 / 800400000000000000000000, 83198265571660639741 / 40320150000000000000000000, 21800615042841558007 / 49624800000000000000000000, 287883271874258269 / 4962480000000000000000000, 287883271874258269 / 63314400000000000000000000, 1166684838648309827 / 5967382200000000000000000000, 106062258058937257 / 26450018400000000000000000000, 15151751151276751 / 513194869200000000000000000000, 1377431922843341 / 42081979274400000000000000000000] : List ℝ) i.1
private theorem qEvRowAbs_11_eq (i : Fin 12) :
    (∑ j : Fin 12, |qEvMat_11 i j|) = qEvRowAbs_11 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qEvMat_11, qEvRowAbs_11, matAt, listAt, coeffAt]; norm_num)

private def basisFn (k : Fin 12) (y : ℝ) : ℝ := (2 * (degAt k : ℝ) + 1) * legP (degAt k) y

private def iBasis_0_0 : List ℝ := ([1] : List ℝ)
private def iBasis_1_0 : List ℝ := ([1, 1] : List ℝ)
private def iBasis_2_0 : List ℝ := ([1 / 2, 1, 1 / 2] : List ℝ)
private def iBasis_3_0 : List ℝ := ([1 / 6, 1 / 2, 1 / 2, 1 / 6] : List ℝ)
private def iBasis_4_0 : List ℝ := ([1 / 24, 1 / 6, 1 / 4, 1 / 6, 1 / 24] : List ℝ)
private def iBasis_5_0 : List ℝ := ([1 / 120, 1 / 24, 1 / 12, 1 / 12, 1 / 24, 1 / 120] : List ℝ)
private def iBasis_6_0 : List ℝ := ([1 / 720, 1 / 120, 1 / 48, 1 / 36, 1 / 48, 1 / 120, 1 / 720] : List ℝ)
private def iBasis_7_0 : List ℝ := ([1 / 5040, 1 / 720, 1 / 240, 1 / 144, 1 / 144, 1 / 240, 1 / 720, 1 / 5040] : List ℝ)
private def iBasis_8_0 : List ℝ := ([1 / 40320, 1 / 5040, 1 / 1440, 1 / 720, 1 / 576, 1 / 720, 1 / 1440, 1 / 5040, 1 / 40320] : List ℝ)
private theorem iterPrim_basis_0_0 (y : ℝ) : iterPrim 0 (basisFn ⟨0, by omega⟩) y = polyEval iBasis_0_0 y := by
  dsimp only [iterPrim, basisFn, degAt]; rw [legP_eq_0 y]
  dsimp only [legList_0, iBasis_0_0, polyEval]; ring
private theorem iterPrim_basis_1_0 (y : ℝ) :
    iterPrim 1 (basisFn ⟨0, by omega⟩) y = polyEval iBasis_1_0 y := by
  refine iterPrim_succ_of_polyEval 0 iBasis_0_0 iBasis_1_0 iterPrim_basis_0_0 ?_ ?_ y
  · dsimp [iBasis_1_0, polyEval]; norm_num
  · intro u; dsimp [iBasis_1_0, iBasis_0_0, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_2_0 (y : ℝ) :
    iterPrim 2 (basisFn ⟨0, by omega⟩) y = polyEval iBasis_2_0 y := by
  refine iterPrim_succ_of_polyEval 1 iBasis_1_0 iBasis_2_0 iterPrim_basis_1_0 ?_ ?_ y
  · dsimp [iBasis_2_0, polyEval]; norm_num
  · intro u; dsimp [iBasis_2_0, iBasis_1_0, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_3_0 (y : ℝ) :
    iterPrim 3 (basisFn ⟨0, by omega⟩) y = polyEval iBasis_3_0 y := by
  refine iterPrim_succ_of_polyEval 2 iBasis_2_0 iBasis_3_0 iterPrim_basis_2_0 ?_ ?_ y
  · dsimp [iBasis_3_0, polyEval]; norm_num
  · intro u; dsimp [iBasis_3_0, iBasis_2_0, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_4_0 (y : ℝ) :
    iterPrim 4 (basisFn ⟨0, by omega⟩) y = polyEval iBasis_4_0 y := by
  refine iterPrim_succ_of_polyEval 3 iBasis_3_0 iBasis_4_0 iterPrim_basis_3_0 ?_ ?_ y
  · dsimp [iBasis_4_0, polyEval]; norm_num
  · intro u; dsimp [iBasis_4_0, iBasis_3_0, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_5_0 (y : ℝ) :
    iterPrim 5 (basisFn ⟨0, by omega⟩) y = polyEval iBasis_5_0 y := by
  refine iterPrim_succ_of_polyEval 4 iBasis_4_0 iBasis_5_0 iterPrim_basis_4_0 ?_ ?_ y
  · dsimp [iBasis_5_0, polyEval]; norm_num
  · intro u; dsimp [iBasis_5_0, iBasis_4_0, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_6_0 (y : ℝ) :
    iterPrim 6 (basisFn ⟨0, by omega⟩) y = polyEval iBasis_6_0 y := by
  refine iterPrim_succ_of_polyEval 5 iBasis_5_0 iBasis_6_0 iterPrim_basis_5_0 ?_ ?_ y
  · dsimp [iBasis_6_0, polyEval]; norm_num
  · intro u; dsimp [iBasis_6_0, iBasis_5_0, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_7_0 (y : ℝ) :
    iterPrim 7 (basisFn ⟨0, by omega⟩) y = polyEval iBasis_7_0 y := by
  refine iterPrim_succ_of_polyEval 6 iBasis_6_0 iBasis_7_0 iterPrim_basis_6_0 ?_ ?_ y
  · dsimp [iBasis_7_0, polyEval]; norm_num
  · intro u; dsimp [iBasis_7_0, iBasis_6_0, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_8_0 (y : ℝ) :
    iterPrim 8 (basisFn ⟨0, by omega⟩) y = polyEval iBasis_8_0 y := by
  refine iterPrim_succ_of_polyEval 7 iBasis_7_0 iBasis_8_0 iterPrim_basis_7_0 ?_ ?_ y
  · dsimp [iBasis_8_0, polyEval]; norm_num
  · intro u; dsimp [iBasis_8_0, iBasis_7_0, polyDeriv, polyAdd, polyEval]; ring
private def iBasis_0_1 : List ℝ := ([-5 / 2, 0, 15 / 2] : List ℝ)
private def iBasis_1_1 : List ℝ := ([0, -5 / 2, 0, 5 / 2] : List ℝ)
private def iBasis_2_1 : List ℝ := ([5 / 8, 0, -5 / 4, 0, 5 / 8] : List ℝ)
private def iBasis_3_1 : List ℝ := ([1 / 3, 5 / 8, 0, -5 / 12, 0, 1 / 8] : List ℝ)
private def iBasis_4_1 : List ℝ := ([5 / 48, 1 / 3, 5 / 16, 0, -5 / 48, 0, 1 / 48] : List ℝ)
private def iBasis_5_1 : List ℝ := ([1 / 42, 5 / 48, 1 / 6, 5 / 48, 0, -1 / 48, 0, 1 / 336] : List ℝ)
private def iBasis_6_1 : List ℝ := ([5 / 1152, 1 / 42, 5 / 96, 1 / 18, 5 / 192, 0, -1 / 288, 0, 1 / 2688] : List ℝ)
private def iBasis_7_1 : List ℝ := ([1 / 1512, 5 / 1152, 1 / 84, 5 / 288, 1 / 72, 1 / 192, 0, -1 / 2016, 0, 1 / 24192] : List ℝ)
private def iBasis_8_1 : List ℝ := ([1 / 11520, 1 / 1512, 5 / 2304, 1 / 252, 5 / 1152, 1 / 360, 1 / 1152, 0, -1 / 16128, 0, 1 / 241920] : List ℝ)
private theorem iterPrim_basis_0_1 (y : ℝ) : iterPrim 0 (basisFn ⟨1, by omega⟩) y = polyEval iBasis_0_1 y := by
  dsimp only [iterPrim, basisFn, degAt]; rw [legP_eq_2 y]
  dsimp only [legList_2, iBasis_0_1, polyEval]; ring
private theorem iterPrim_basis_1_1 (y : ℝ) :
    iterPrim 1 (basisFn ⟨1, by omega⟩) y = polyEval iBasis_1_1 y := by
  refine iterPrim_succ_of_polyEval 0 iBasis_0_1 iBasis_1_1 iterPrim_basis_0_1 ?_ ?_ y
  · dsimp [iBasis_1_1, polyEval]; norm_num
  · intro u; dsimp [iBasis_1_1, iBasis_0_1, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_2_1 (y : ℝ) :
    iterPrim 2 (basisFn ⟨1, by omega⟩) y = polyEval iBasis_2_1 y := by
  refine iterPrim_succ_of_polyEval 1 iBasis_1_1 iBasis_2_1 iterPrim_basis_1_1 ?_ ?_ y
  · dsimp [iBasis_2_1, polyEval]; norm_num
  · intro u; dsimp [iBasis_2_1, iBasis_1_1, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_3_1 (y : ℝ) :
    iterPrim 3 (basisFn ⟨1, by omega⟩) y = polyEval iBasis_3_1 y := by
  refine iterPrim_succ_of_polyEval 2 iBasis_2_1 iBasis_3_1 iterPrim_basis_2_1 ?_ ?_ y
  · dsimp [iBasis_3_1, polyEval]; norm_num
  · intro u; dsimp [iBasis_3_1, iBasis_2_1, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_4_1 (y : ℝ) :
    iterPrim 4 (basisFn ⟨1, by omega⟩) y = polyEval iBasis_4_1 y := by
  refine iterPrim_succ_of_polyEval 3 iBasis_3_1 iBasis_4_1 iterPrim_basis_3_1 ?_ ?_ y
  · dsimp [iBasis_4_1, polyEval]; norm_num
  · intro u; dsimp [iBasis_4_1, iBasis_3_1, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_5_1 (y : ℝ) :
    iterPrim 5 (basisFn ⟨1, by omega⟩) y = polyEval iBasis_5_1 y := by
  refine iterPrim_succ_of_polyEval 4 iBasis_4_1 iBasis_5_1 iterPrim_basis_4_1 ?_ ?_ y
  · dsimp [iBasis_5_1, polyEval]; norm_num
  · intro u; dsimp [iBasis_5_1, iBasis_4_1, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_6_1 (y : ℝ) :
    iterPrim 6 (basisFn ⟨1, by omega⟩) y = polyEval iBasis_6_1 y := by
  refine iterPrim_succ_of_polyEval 5 iBasis_5_1 iBasis_6_1 iterPrim_basis_5_1 ?_ ?_ y
  · dsimp [iBasis_6_1, polyEval]; norm_num
  · intro u; dsimp [iBasis_6_1, iBasis_5_1, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_7_1 (y : ℝ) :
    iterPrim 7 (basisFn ⟨1, by omega⟩) y = polyEval iBasis_7_1 y := by
  refine iterPrim_succ_of_polyEval 6 iBasis_6_1 iBasis_7_1 iterPrim_basis_6_1 ?_ ?_ y
  · dsimp [iBasis_7_1, polyEval]; norm_num
  · intro u; dsimp [iBasis_7_1, iBasis_6_1, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_8_1 (y : ℝ) :
    iterPrim 8 (basisFn ⟨1, by omega⟩) y = polyEval iBasis_8_1 y := by
  refine iterPrim_succ_of_polyEval 7 iBasis_7_1 iBasis_8_1 iterPrim_basis_7_1 ?_ ?_ y
  · dsimp [iBasis_8_1, polyEval]; norm_num
  · intro u; dsimp [iBasis_8_1, iBasis_7_1, polyDeriv, polyAdd, polyEval]; ring
private def iBasis_0_2 : List ℝ := ([27 / 8, 0, -135 / 4, 0, 315 / 8] : List ℝ)
private def iBasis_1_2 : List ℝ := ([0, 27 / 8, 0, -45 / 4, 0, 63 / 8] : List ℝ)
private def iBasis_2_2 : List ℝ := ([-3 / 16, 0, 27 / 16, 0, -45 / 16, 0, 21 / 16] : List ℝ)
private def iBasis_3_2 : List ℝ := ([0, -3 / 16, 0, 9 / 16, 0, -9 / 16, 0, 3 / 16] : List ℝ)
private def iBasis_4_2 : List ℝ := ([3 / 128, 0, -3 / 32, 0, 9 / 64, 0, -3 / 32, 0, 3 / 128] : List ℝ)
private def iBasis_5_2 : List ℝ := ([1 / 105, 3 / 128, 0, -1 / 32, 0, 9 / 320, 0, -3 / 224, 0, 1 / 384] : List ℝ)
private def iBasis_6_2 : List ℝ := ([3 / 1280, 1 / 105, 3 / 256, 0, -1 / 128, 0, 3 / 640, 0, -3 / 1792, 0, 1 / 3840] : List ℝ)
private def iBasis_7_2 : List ℝ := ([1 / 2310, 3 / 1280, 1 / 210, 1 / 256, 0, -1 / 640, 0, 3 / 4480, 0, -1 / 5376, 0, 1 / 42240] : List ℝ)
private def iBasis_8_2 : List ℝ := ([1 / 15360, 1 / 2310, 3 / 2560, 1 / 630, 1 / 1024, 0, -1 / 3840, 0, 3 / 35840, 0, -1 / 53760, 0, 1 / 506880] : List ℝ)
private theorem iterPrim_basis_0_2 (y : ℝ) : iterPrim 0 (basisFn ⟨2, by omega⟩) y = polyEval iBasis_0_2 y := by
  dsimp only [iterPrim, basisFn, degAt]; rw [legP_eq_4 y]
  dsimp only [legList_4, iBasis_0_2, polyEval]; ring
private theorem iterPrim_basis_1_2 (y : ℝ) :
    iterPrim 1 (basisFn ⟨2, by omega⟩) y = polyEval iBasis_1_2 y := by
  refine iterPrim_succ_of_polyEval 0 iBasis_0_2 iBasis_1_2 iterPrim_basis_0_2 ?_ ?_ y
  · dsimp [iBasis_1_2, polyEval]; norm_num
  · intro u; dsimp [iBasis_1_2, iBasis_0_2, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_2_2 (y : ℝ) :
    iterPrim 2 (basisFn ⟨2, by omega⟩) y = polyEval iBasis_2_2 y := by
  refine iterPrim_succ_of_polyEval 1 iBasis_1_2 iBasis_2_2 iterPrim_basis_1_2 ?_ ?_ y
  · dsimp [iBasis_2_2, polyEval]; norm_num
  · intro u; dsimp [iBasis_2_2, iBasis_1_2, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_3_2 (y : ℝ) :
    iterPrim 3 (basisFn ⟨2, by omega⟩) y = polyEval iBasis_3_2 y := by
  refine iterPrim_succ_of_polyEval 2 iBasis_2_2 iBasis_3_2 iterPrim_basis_2_2 ?_ ?_ y
  · dsimp [iBasis_3_2, polyEval]; norm_num
  · intro u; dsimp [iBasis_3_2, iBasis_2_2, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_4_2 (y : ℝ) :
    iterPrim 4 (basisFn ⟨2, by omega⟩) y = polyEval iBasis_4_2 y := by
  refine iterPrim_succ_of_polyEval 3 iBasis_3_2 iBasis_4_2 iterPrim_basis_3_2 ?_ ?_ y
  · dsimp [iBasis_4_2, polyEval]; norm_num
  · intro u; dsimp [iBasis_4_2, iBasis_3_2, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_5_2 (y : ℝ) :
    iterPrim 5 (basisFn ⟨2, by omega⟩) y = polyEval iBasis_5_2 y := by
  refine iterPrim_succ_of_polyEval 4 iBasis_4_2 iBasis_5_2 iterPrim_basis_4_2 ?_ ?_ y
  · dsimp [iBasis_5_2, polyEval]; norm_num
  · intro u; dsimp [iBasis_5_2, iBasis_4_2, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_6_2 (y : ℝ) :
    iterPrim 6 (basisFn ⟨2, by omega⟩) y = polyEval iBasis_6_2 y := by
  refine iterPrim_succ_of_polyEval 5 iBasis_5_2 iBasis_6_2 iterPrim_basis_5_2 ?_ ?_ y
  · dsimp [iBasis_6_2, polyEval]; norm_num
  · intro u; dsimp [iBasis_6_2, iBasis_5_2, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_7_2 (y : ℝ) :
    iterPrim 7 (basisFn ⟨2, by omega⟩) y = polyEval iBasis_7_2 y := by
  refine iterPrim_succ_of_polyEval 6 iBasis_6_2 iBasis_7_2 iterPrim_basis_6_2 ?_ ?_ y
  · dsimp [iBasis_7_2, polyEval]; norm_num
  · intro u; dsimp [iBasis_7_2, iBasis_6_2, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_8_2 (y : ℝ) :
    iterPrim 8 (basisFn ⟨2, by omega⟩) y = polyEval iBasis_8_2 y := by
  refine iterPrim_succ_of_polyEval 7 iBasis_7_2 iBasis_8_2 iterPrim_basis_7_2 ?_ ?_ y
  · dsimp [iBasis_8_2, polyEval]; norm_num
  · intro u; dsimp [iBasis_8_2, iBasis_7_2, polyDeriv, polyAdd, polyEval]; ring
private def iBasis_0_3 : List ℝ := ([-65 / 16, 0, 1365 / 16, 0, -4095 / 16, 0, 3003 / 16] : List ℝ)
private def iBasis_1_3 : List ℝ := ([0, -65 / 16, 0, 455 / 16, 0, -819 / 16, 0, 429 / 16] : List ℝ)
private def iBasis_2_3 : List ℝ := ([13 / 128, 0, -65 / 32, 0, 455 / 64, 0, -273 / 32, 0, 429 / 128] : List ℝ)
private def iBasis_3_3 : List ℝ := ([0, 13 / 128, 0, -65 / 96, 0, 91 / 64, 0, -39 / 32, 0, 143 / 384] : List ℝ)
private def iBasis_4_3 : List ℝ := ([-13 / 3840, 0, 13 / 256, 0, -65 / 384, 0, 91 / 384, 0, -39 / 256, 0, 143 / 3840] : List ℝ)
private def iBasis_5_3 : List ℝ := ([0, -13 / 3840, 0, 13 / 768, 0, -13 / 384, 0, 13 / 384, 0, -13 / 768, 0, 13 / 3840] : List ℝ)
private def iBasis_6_3 : List ℝ := ([13 / 46080, 0, -13 / 7680, 0, 13 / 3072, 0, -13 / 2304, 0, 13 / 3072, 0, -13 / 7680, 0, 13 / 46080] : List ℝ)
private def iBasis_7_3 : List ℝ := ([1 / 10395, 13 / 46080, 0, -13 / 23040, 0, 13 / 15360, 0, -13 / 16128, 0, 13 / 27648, 0, -13 / 84480, 0, 1 / 46080] : List ℝ)
private def iBasis_8_3 : List ℝ := ([13 / 645120, 1 / 10395, 13 / 92160, 0, -13 / 92160, 0, 13 / 92160, 0, -13 / 129024, 0, 13 / 276480, 0, -13 / 1013760, 0, 1 / 645120] : List ℝ)
private theorem iterPrim_basis_0_3 (y : ℝ) : iterPrim 0 (basisFn ⟨3, by omega⟩) y = polyEval iBasis_0_3 y := by
  dsimp only [iterPrim, basisFn, degAt]; rw [legP_eq_6 y]
  dsimp only [legList_6, iBasis_0_3, polyEval]; ring
private theorem iterPrim_basis_1_3 (y : ℝ) :
    iterPrim 1 (basisFn ⟨3, by omega⟩) y = polyEval iBasis_1_3 y := by
  refine iterPrim_succ_of_polyEval 0 iBasis_0_3 iBasis_1_3 iterPrim_basis_0_3 ?_ ?_ y
  · dsimp [iBasis_1_3, polyEval]; norm_num
  · intro u; dsimp [iBasis_1_3, iBasis_0_3, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_2_3 (y : ℝ) :
    iterPrim 2 (basisFn ⟨3, by omega⟩) y = polyEval iBasis_2_3 y := by
  refine iterPrim_succ_of_polyEval 1 iBasis_1_3 iBasis_2_3 iterPrim_basis_1_3 ?_ ?_ y
  · dsimp [iBasis_2_3, polyEval]; norm_num
  · intro u; dsimp [iBasis_2_3, iBasis_1_3, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_3_3 (y : ℝ) :
    iterPrim 3 (basisFn ⟨3, by omega⟩) y = polyEval iBasis_3_3 y := by
  refine iterPrim_succ_of_polyEval 2 iBasis_2_3 iBasis_3_3 iterPrim_basis_2_3 ?_ ?_ y
  · dsimp [iBasis_3_3, polyEval]; norm_num
  · intro u; dsimp [iBasis_3_3, iBasis_2_3, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_4_3 (y : ℝ) :
    iterPrim 4 (basisFn ⟨3, by omega⟩) y = polyEval iBasis_4_3 y := by
  refine iterPrim_succ_of_polyEval 3 iBasis_3_3 iBasis_4_3 iterPrim_basis_3_3 ?_ ?_ y
  · dsimp [iBasis_4_3, polyEval]; norm_num
  · intro u; dsimp [iBasis_4_3, iBasis_3_3, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_5_3 (y : ℝ) :
    iterPrim 5 (basisFn ⟨3, by omega⟩) y = polyEval iBasis_5_3 y := by
  refine iterPrim_succ_of_polyEval 4 iBasis_4_3 iBasis_5_3 iterPrim_basis_4_3 ?_ ?_ y
  · dsimp [iBasis_5_3, polyEval]; norm_num
  · intro u; dsimp [iBasis_5_3, iBasis_4_3, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_6_3 (y : ℝ) :
    iterPrim 6 (basisFn ⟨3, by omega⟩) y = polyEval iBasis_6_3 y := by
  refine iterPrim_succ_of_polyEval 5 iBasis_5_3 iBasis_6_3 iterPrim_basis_5_3 ?_ ?_ y
  · dsimp [iBasis_6_3, polyEval]; norm_num
  · intro u; dsimp [iBasis_6_3, iBasis_5_3, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_7_3 (y : ℝ) :
    iterPrim 7 (basisFn ⟨3, by omega⟩) y = polyEval iBasis_7_3 y := by
  refine iterPrim_succ_of_polyEval 6 iBasis_6_3 iBasis_7_3 iterPrim_basis_6_3 ?_ ?_ y
  · dsimp [iBasis_7_3, polyEval]; norm_num
  · intro u; dsimp [iBasis_7_3, iBasis_6_3, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_8_3 (y : ℝ) :
    iterPrim 8 (basisFn ⟨3, by omega⟩) y = polyEval iBasis_8_3 y := by
  refine iterPrim_succ_of_polyEval 7 iBasis_7_3 iBasis_8_3 iterPrim_basis_7_3 ?_ ?_ y
  · dsimp [iBasis_8_3, polyEval]; norm_num
  · intro u; dsimp [iBasis_8_3, iBasis_7_3, polyDeriv, polyAdd, polyEval]; ring
private def iBasis_0_4 : List ℝ := ([595 / 128, 0, -5355 / 32, 0, 58905 / 64, 0, -51051 / 32, 0, 109395 / 128] : List ℝ)
private def iBasis_1_4 : List ℝ := ([0, 595 / 128, 0, -1785 / 32, 0, 11781 / 64, 0, -7293 / 32, 0, 12155 / 128] : List ℝ)
private def iBasis_2_4 : List ℝ := ([-17 / 256, 0, 595 / 256, 0, -1785 / 128, 0, 3927 / 128, 0, -7293 / 256, 0, 2431 / 256] : List ℝ)
private def iBasis_3_4 : List ℝ := ([0, -17 / 256, 0, 595 / 768, 0, -357 / 128, 0, 561 / 128, 0, -2431 / 768, 0, 221 / 256] : List ℝ)
private def iBasis_4_4 : List ℝ := ([17 / 15360, 0, -17 / 512, 0, 595 / 3072, 0, -119 / 256, 0, 561 / 1024, 0, -2431 / 7680, 0, 221 / 3072] : List ℝ)
private def iBasis_5_4 : List ℝ := ([0, 17 / 15360, 0, -17 / 1536, 0, 119 / 3072, 0, -17 / 256, 0, 187 / 3072, 0, -221 / 7680, 0, 17 / 3072] : List ℝ)
private def iBasis_6_4 : List ℝ := ([-17 / 645120, 0, 17 / 30720, 0, -17 / 6144, 0, 119 / 18432, 0, -17 / 2048, 0, 187 / 30720, 0, -221 / 92160, 0, 17 / 43008] : List ℝ)
private def iBasis_7_4 : List ℝ := ([0, -17 / 645120, 0, 17 / 92160, 0, -17 / 30720, 0, 17 / 18432, 0, -17 / 18432, 0, 17 / 30720, 0, -17 / 92160, 0, 17 / 645120] : List ℝ)
private def iBasis_8_4 : List ℝ := ([17 / 10321920, 0, -17 / 1290240, 0, 17 / 368640, 0, -17 / 184320, 0, 17 / 147456, 0, -17 / 184320, 0, 17 / 368640, 0, -17 / 1290240, 0, 17 / 10321920] : List ℝ)
private theorem iterPrim_basis_0_4 (y : ℝ) : iterPrim 0 (basisFn ⟨4, by omega⟩) y = polyEval iBasis_0_4 y := by
  dsimp only [iterPrim, basisFn, degAt]; rw [legP_eq_8 y]
  dsimp only [legList_8, iBasis_0_4, polyEval]; ring
private theorem iterPrim_basis_1_4 (y : ℝ) :
    iterPrim 1 (basisFn ⟨4, by omega⟩) y = polyEval iBasis_1_4 y := by
  refine iterPrim_succ_of_polyEval 0 iBasis_0_4 iBasis_1_4 iterPrim_basis_0_4 ?_ ?_ y
  · dsimp [iBasis_1_4, polyEval]; norm_num
  · intro u; dsimp [iBasis_1_4, iBasis_0_4, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_2_4 (y : ℝ) :
    iterPrim 2 (basisFn ⟨4, by omega⟩) y = polyEval iBasis_2_4 y := by
  refine iterPrim_succ_of_polyEval 1 iBasis_1_4 iBasis_2_4 iterPrim_basis_1_4 ?_ ?_ y
  · dsimp [iBasis_2_4, polyEval]; norm_num
  · intro u; dsimp [iBasis_2_4, iBasis_1_4, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_3_4 (y : ℝ) :
    iterPrim 3 (basisFn ⟨4, by omega⟩) y = polyEval iBasis_3_4 y := by
  refine iterPrim_succ_of_polyEval 2 iBasis_2_4 iBasis_3_4 iterPrim_basis_2_4 ?_ ?_ y
  · dsimp [iBasis_3_4, polyEval]; norm_num
  · intro u; dsimp [iBasis_3_4, iBasis_2_4, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_4_4 (y : ℝ) :
    iterPrim 4 (basisFn ⟨4, by omega⟩) y = polyEval iBasis_4_4 y := by
  refine iterPrim_succ_of_polyEval 3 iBasis_3_4 iBasis_4_4 iterPrim_basis_3_4 ?_ ?_ y
  · dsimp [iBasis_4_4, polyEval]; norm_num
  · intro u; dsimp [iBasis_4_4, iBasis_3_4, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_5_4 (y : ℝ) :
    iterPrim 5 (basisFn ⟨4, by omega⟩) y = polyEval iBasis_5_4 y := by
  refine iterPrim_succ_of_polyEval 4 iBasis_4_4 iBasis_5_4 iterPrim_basis_4_4 ?_ ?_ y
  · dsimp [iBasis_5_4, polyEval]; norm_num
  · intro u; dsimp [iBasis_5_4, iBasis_4_4, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_6_4 (y : ℝ) :
    iterPrim 6 (basisFn ⟨4, by omega⟩) y = polyEval iBasis_6_4 y := by
  refine iterPrim_succ_of_polyEval 5 iBasis_5_4 iBasis_6_4 iterPrim_basis_5_4 ?_ ?_ y
  · dsimp [iBasis_6_4, polyEval]; norm_num
  · intro u; dsimp [iBasis_6_4, iBasis_5_4, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_7_4 (y : ℝ) :
    iterPrim 7 (basisFn ⟨4, by omega⟩) y = polyEval iBasis_7_4 y := by
  refine iterPrim_succ_of_polyEval 6 iBasis_6_4 iBasis_7_4 iterPrim_basis_6_4 ?_ ?_ y
  · dsimp [iBasis_7_4, polyEval]; norm_num
  · intro u; dsimp [iBasis_7_4, iBasis_6_4, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_8_4 (y : ℝ) :
    iterPrim 8 (basisFn ⟨4, by omega⟩) y = polyEval iBasis_8_4 y := by
  refine iterPrim_succ_of_polyEval 7 iBasis_7_4 iBasis_8_4 iterPrim_basis_7_4 ?_ ?_ y
  · dsimp [iBasis_8_4, polyEval]; norm_num
  · intro u; dsimp [iBasis_8_4, iBasis_7_4, polyDeriv, polyAdd, polyEval]; ring
private def iBasis_0_5 : List ℝ := ([-1323 / 256, 0, 72765 / 256, 0, -315315 / 128, 0, 945945 / 128, 0, -2297295 / 256, 0, 969969 / 256] : List ℝ)
private def iBasis_1_5 : List ℝ := ([0, -1323 / 256, 0, 24255 / 256, 0, -63063 / 128, 0, 135135 / 128, 0, -255255 / 256, 0, 88179 / 256] : List ℝ)
private def iBasis_2_5 : List ℝ := ([49 / 1024, 0, -1323 / 512, 0, 24255 / 1024, 0, -21021 / 256, 0, 135135 / 1024, 0, -51051 / 512, 0, 29393 / 1024] : List ℝ)
private def iBasis_3_5 : List ℝ := ([0, 49 / 1024, 0, -441 / 512, 0, 4851 / 1024, 0, -3003 / 256, 0, 15015 / 1024, 0, -4641 / 512, 0, 2261 / 1024] : List ℝ)
private def iBasis_4_5 : List ℝ := ([-1 / 2048, 0, 49 / 2048, 0, -441 / 2048, 0, 1617 / 2048, 0, -3003 / 2048, 0, 3003 / 2048, 0, -1547 / 2048, 0, 323 / 2048] : List ℝ)
private def iBasis_5_5 : List ℝ := ([0, -1 / 2048, 0, 49 / 6144, 0, -441 / 10240, 0, 231 / 2048, 0, -1001 / 6144, 0, 273 / 2048, 0, -119 / 2048, 0, 323 / 30720] : List ℝ)
private def iBasis_6_5 : List ℝ := ([1 / 163840, 0, -1 / 4096, 0, 49 / 24576, 0, -147 / 20480, 0, 231 / 16384, 0, -1001 / 61440, 0, 91 / 8192, 0, -17 / 4096, 0, 323 / 491520] : List ℝ)
private def iBasis_7_5 : List ℝ := ([0, 1 / 163840, 0, -1 / 12288, 0, 49 / 122880, 0, -21 / 20480, 0, 77 / 49152, 0, -91 / 61440, 0, 7 / 8192, 0, -17 / 61440, 0, 19 / 491520] : List ℝ)
private def iBasis_8_5 : List ℝ := ([-1 / 8847360, 0, 1 / 327680, 0, -1 / 49152, 0, 49 / 737280, 0, -21 / 163840, 0, 77 / 491520, 0, -91 / 737280, 0, 1 / 16384, 0, -17 / 983040, 0, 19 / 8847360] : List ℝ)
private theorem iterPrim_basis_0_5 (y : ℝ) : iterPrim 0 (basisFn ⟨5, by omega⟩) y = polyEval iBasis_0_5 y := by
  dsimp only [iterPrim, basisFn, degAt]; rw [legP_eq_10 y]
  dsimp only [legList_10, iBasis_0_5, polyEval]; ring
private theorem iterPrim_basis_1_5 (y : ℝ) :
    iterPrim 1 (basisFn ⟨5, by omega⟩) y = polyEval iBasis_1_5 y := by
  refine iterPrim_succ_of_polyEval 0 iBasis_0_5 iBasis_1_5 iterPrim_basis_0_5 ?_ ?_ y
  · dsimp [iBasis_1_5, polyEval]; norm_num
  · intro u; dsimp [iBasis_1_5, iBasis_0_5, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_2_5 (y : ℝ) :
    iterPrim 2 (basisFn ⟨5, by omega⟩) y = polyEval iBasis_2_5 y := by
  refine iterPrim_succ_of_polyEval 1 iBasis_1_5 iBasis_2_5 iterPrim_basis_1_5 ?_ ?_ y
  · dsimp [iBasis_2_5, polyEval]; norm_num
  · intro u; dsimp [iBasis_2_5, iBasis_1_5, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_3_5 (y : ℝ) :
    iterPrim 3 (basisFn ⟨5, by omega⟩) y = polyEval iBasis_3_5 y := by
  refine iterPrim_succ_of_polyEval 2 iBasis_2_5 iBasis_3_5 iterPrim_basis_2_5 ?_ ?_ y
  · dsimp [iBasis_3_5, polyEval]; norm_num
  · intro u; dsimp [iBasis_3_5, iBasis_2_5, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_4_5 (y : ℝ) :
    iterPrim 4 (basisFn ⟨5, by omega⟩) y = polyEval iBasis_4_5 y := by
  refine iterPrim_succ_of_polyEval 3 iBasis_3_5 iBasis_4_5 iterPrim_basis_3_5 ?_ ?_ y
  · dsimp [iBasis_4_5, polyEval]; norm_num
  · intro u; dsimp [iBasis_4_5, iBasis_3_5, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_5_5 (y : ℝ) :
    iterPrim 5 (basisFn ⟨5, by omega⟩) y = polyEval iBasis_5_5 y := by
  refine iterPrim_succ_of_polyEval 4 iBasis_4_5 iBasis_5_5 iterPrim_basis_4_5 ?_ ?_ y
  · dsimp [iBasis_5_5, polyEval]; norm_num
  · intro u; dsimp [iBasis_5_5, iBasis_4_5, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_6_5 (y : ℝ) :
    iterPrim 6 (basisFn ⟨5, by omega⟩) y = polyEval iBasis_6_5 y := by
  refine iterPrim_succ_of_polyEval 5 iBasis_5_5 iBasis_6_5 iterPrim_basis_5_5 ?_ ?_ y
  · dsimp [iBasis_6_5, polyEval]; norm_num
  · intro u; dsimp [iBasis_6_5, iBasis_5_5, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_7_5 (y : ℝ) :
    iterPrim 7 (basisFn ⟨5, by omega⟩) y = polyEval iBasis_7_5 y := by
  refine iterPrim_succ_of_polyEval 6 iBasis_6_5 iBasis_7_5 iterPrim_basis_6_5 ?_ ?_ y
  · dsimp [iBasis_7_5, polyEval]; norm_num
  · intro u; dsimp [iBasis_7_5, iBasis_6_5, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_8_5 (y : ℝ) :
    iterPrim 8 (basisFn ⟨5, by omega⟩) y = polyEval iBasis_8_5 y := by
  refine iterPrim_succ_of_polyEval 7 iBasis_7_5 iBasis_8_5 iterPrim_basis_7_5 ?_ ?_ y
  · dsimp [iBasis_8_5, polyEval]; norm_num
  · intro u; dsimp [iBasis_8_5, iBasis_7_5, polyDeriv, polyAdd, polyEval]; ring
private def iBasis_0_6 : List ℝ := ([5775 / 1024, 0, -225225 / 512, 0, 5630625 / 1024, 0, -6381375 / 256, 0, 51962625 / 1024, 0, -24249225 / 512, 0, 16900975 / 1024] : List ℝ)
private def iBasis_1_6 : List ℝ := ([0, 5775 / 1024, 0, -75075 / 512, 0, 1126125 / 1024, 0, -911625 / 256, 0, 5773625 / 1024, 0, -2204475 / 512, 0, 1300075 / 1024] : List ℝ)
private def iBasis_2_6 : List ℝ := ([-75 / 2048, 0, 5775 / 2048, 0, -75075 / 2048, 0, 375375 / 2048, 0, -911625 / 2048, 0, 1154725 / 2048, 0, -734825 / 2048, 0, 185725 / 2048] : List ℝ)
private def iBasis_3_6 : List ℝ := ([0, -75 / 2048, 0, 1925 / 2048, 0, -15015 / 2048, 0, 53625 / 2048, 0, -303875 / 6144, 0, 104975 / 2048, 0, -56525 / 2048, 0, 37145 / 6144] : List ℝ)
private def iBasis_4_6 : List ℝ := ([25 / 98304, 0, -75 / 4096, 0, 1925 / 8192, 0, -5005 / 4096, 0, 53625 / 16384, 0, -60775 / 12288, 0, 104975 / 24576, 0, -8075 / 4096, 0, 37145 / 98304] : List ℝ)
private def iBasis_5_6 : List ℝ := ([0, 25 / 98304, 0, -25 / 4096, 0, 385 / 8192, 0, -715 / 4096, 0, 17875 / 49152, 0, -5525 / 12288, 0, 8075 / 24576, 0, -1615 / 12288, 0, 2185 / 98304] : List ℝ)
private def iBasis_6_6 : List ℝ := ([-25 / 12386304, 0, 25 / 196608, 0, -25 / 16384, 0, 385 / 49152, 0, -715 / 32768, 0, 3575 / 98304, 0, -5525 / 147456, 0, 8075 / 344064, 0, -1615 / 196608, 0, 2185 / 1769472] : List ℝ)
private def iBasis_7_6 : List ℝ := ([0, -25 / 12386304, 0, 25 / 589824, 0, -5 / 16384, 0, 55 / 49152, 0, -715 / 294912, 0, 325 / 98304, 0, -425 / 147456, 0, 1615 / 1032192, 0, -95 / 196608, 0, 115 / 1769472] : List ℝ)
private def iBasis_8_6 : List ℝ := ([1 / 49545216, 0, -25 / 24772608, 0, 25 / 2359296, 0, -5 / 98304, 0, 55 / 393216, 0, -143 / 589824, 0, 325 / 1179648, 0, -425 / 2064384, 0, 1615 / 16515072, 0, -95 / 3538944, 0, 23 / 7077888] : List ℝ)
private theorem iterPrim_basis_0_6 (y : ℝ) : iterPrim 0 (basisFn ⟨6, by omega⟩) y = polyEval iBasis_0_6 y := by
  dsimp only [iterPrim, basisFn, degAt]; rw [legP_eq_12 y]
  dsimp only [legList_12, iBasis_0_6, polyEval]; ring
private theorem iterPrim_basis_1_6 (y : ℝ) :
    iterPrim 1 (basisFn ⟨6, by omega⟩) y = polyEval iBasis_1_6 y := by
  refine iterPrim_succ_of_polyEval 0 iBasis_0_6 iBasis_1_6 iterPrim_basis_0_6 ?_ ?_ y
  · dsimp [iBasis_1_6, polyEval]; norm_num
  · intro u; dsimp [iBasis_1_6, iBasis_0_6, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_2_6 (y : ℝ) :
    iterPrim 2 (basisFn ⟨6, by omega⟩) y = polyEval iBasis_2_6 y := by
  refine iterPrim_succ_of_polyEval 1 iBasis_1_6 iBasis_2_6 iterPrim_basis_1_6 ?_ ?_ y
  · dsimp [iBasis_2_6, polyEval]; norm_num
  · intro u; dsimp [iBasis_2_6, iBasis_1_6, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_3_6 (y : ℝ) :
    iterPrim 3 (basisFn ⟨6, by omega⟩) y = polyEval iBasis_3_6 y := by
  refine iterPrim_succ_of_polyEval 2 iBasis_2_6 iBasis_3_6 iterPrim_basis_2_6 ?_ ?_ y
  · dsimp [iBasis_3_6, polyEval]; norm_num
  · intro u; dsimp [iBasis_3_6, iBasis_2_6, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_4_6 (y : ℝ) :
    iterPrim 4 (basisFn ⟨6, by omega⟩) y = polyEval iBasis_4_6 y := by
  refine iterPrim_succ_of_polyEval 3 iBasis_3_6 iBasis_4_6 iterPrim_basis_3_6 ?_ ?_ y
  · dsimp [iBasis_4_6, polyEval]; norm_num
  · intro u; dsimp [iBasis_4_6, iBasis_3_6, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_5_6 (y : ℝ) :
    iterPrim 5 (basisFn ⟨6, by omega⟩) y = polyEval iBasis_5_6 y := by
  refine iterPrim_succ_of_polyEval 4 iBasis_4_6 iBasis_5_6 iterPrim_basis_4_6 ?_ ?_ y
  · dsimp [iBasis_5_6, polyEval]; norm_num
  · intro u; dsimp [iBasis_5_6, iBasis_4_6, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_6_6 (y : ℝ) :
    iterPrim 6 (basisFn ⟨6, by omega⟩) y = polyEval iBasis_6_6 y := by
  refine iterPrim_succ_of_polyEval 5 iBasis_5_6 iBasis_6_6 iterPrim_basis_5_6 ?_ ?_ y
  · dsimp [iBasis_6_6, polyEval]; norm_num
  · intro u; dsimp [iBasis_6_6, iBasis_5_6, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_7_6 (y : ℝ) :
    iterPrim 7 (basisFn ⟨6, by omega⟩) y = polyEval iBasis_7_6 y := by
  refine iterPrim_succ_of_polyEval 6 iBasis_6_6 iBasis_7_6 iterPrim_basis_6_6 ?_ ?_ y
  · dsimp [iBasis_7_6, polyEval]; norm_num
  · intro u; dsimp [iBasis_7_6, iBasis_6_6, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_8_6 (y : ℝ) :
    iterPrim 8 (basisFn ⟨6, by omega⟩) y = polyEval iBasis_8_6 y := by
  refine iterPrim_succ_of_polyEval 7 iBasis_7_6 iBasis_8_6 iterPrim_basis_7_6 ?_ ?_ y
  · dsimp [iBasis_8_6, polyEval]; norm_num
  · intro u; dsimp [iBasis_8_6, iBasis_7_6, polyDeriv, polyAdd, polyEval]; ring
private def iBasis_0_7 : List ℝ := ([-12441 / 2048, 0, 1306305 / 2048, 0, -22207185 / 2048, 0, 140645505 / 2048, 0, -421936515 / 2048, 0, 646969323 / 2048, 0, -490128275 / 2048, 0, 145422675 / 2048] : List ℝ)
private def iBasis_1_7 : List ℝ := ([0, -12441 / 2048, 0, 435435 / 2048, 0, -4441437 / 2048, 0, 20092215 / 2048, 0, -46881835 / 2048, 0, 58815393 / 2048, 0, -37702175 / 2048, 0, 9694845 / 2048] : List ℝ)
private def iBasis_2_7 : List ℝ := ([957 / 32768, 0, -12441 / 4096, 0, 435435 / 8192, 0, -1480479 / 4096, 0, 20092215 / 16384, 0, -9376367 / 4096, 0, 19605131 / 8192, 0, -5386025 / 4096, 0, 9694845 / 32768] : List ℝ)
private def iBasis_3_7 : List ℝ := ([0, 957 / 32768, 0, -4147 / 4096, 0, 87087 / 8192, 0, -211497 / 4096, 0, 6697405 / 49152, 0, -852397 / 4096, 0, 1508087 / 8192, 0, -1077205 / 12288, 0, 570285 / 32768] : List ℝ)
private def iBasis_4_7 : List ℝ := ([-29 / 196608, 0, 957 / 65536, 0, -4147 / 16384, 0, 29029 / 16384, 0, -211497 / 32768, 0, 1339481 / 98304, 0, -852397 / 49152, 0, 215441 / 16384, 0, -1077205 / 196608, 0, 63365 / 65536] : List ℝ)
private def iBasis_5_7 : List ℝ := ([0, -29 / 196608, 0, 319 / 65536, 0, -4147 / 81920, 0, 4147 / 16384, 0, -70499 / 98304, 0, 121771 / 98304, 0, -65569 / 49152, 0, 215441 / 245760, 0, -63365 / 196608, 0, 3335 / 65536] : List ℝ)
private def iBasis_6_7 : List ℝ := ([29 / 35389440, 0, -29 / 393216, 0, 319 / 262144, 0, -4147 / 491520, 0, 4147 / 131072, 0, -70499 / 983040, 0, 121771 / 1179648, 0, -9367 / 98304, 0, 215441 / 3932160, 0, -63365 / 3538944, 0, 667 / 262144] : List ℝ)
private def iBasis_7_7 : List ℝ := ([0, 29 / 35389440, 0, -29 / 1179648, 0, 319 / 1310720, 0, -4147 / 3440640, 0, 4147 / 1179648, 0, -6409 / 983040, 0, 9367 / 1179648, 0, -9367 / 1474560, 0, 12673 / 3932160, 0, -3335 / 3538944, 0, 667 / 5505024] : List ℝ)
private def iBasis_8_7 : List ℝ := ([-29 / 5449973760, 0, 29 / 70778880, 0, -29 / 4718592, 0, 319 / 7864320, 0, -4147 / 27525120, 0, 4147 / 11796480, 0, -6409 / 11796480, 0, 9367 / 16515072, 0, -9367 / 23592960, 0, 12673 / 70778880, 0, -667 / 14155776, 0, 667 / 121110528] : List ℝ)
private theorem iterPrim_basis_0_7 (y : ℝ) : iterPrim 0 (basisFn ⟨7, by omega⟩) y = polyEval iBasis_0_7 y := by
  dsimp only [iterPrim, basisFn, degAt]; rw [legP_eq_14 y]
  dsimp only [legList_14, iBasis_0_7, polyEval]; ring
private theorem iterPrim_basis_1_7 (y : ℝ) :
    iterPrim 1 (basisFn ⟨7, by omega⟩) y = polyEval iBasis_1_7 y := by
  refine iterPrim_succ_of_polyEval 0 iBasis_0_7 iBasis_1_7 iterPrim_basis_0_7 ?_ ?_ y
  · dsimp [iBasis_1_7, polyEval]; norm_num
  · intro u; dsimp [iBasis_1_7, iBasis_0_7, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_2_7 (y : ℝ) :
    iterPrim 2 (basisFn ⟨7, by omega⟩) y = polyEval iBasis_2_7 y := by
  refine iterPrim_succ_of_polyEval 1 iBasis_1_7 iBasis_2_7 iterPrim_basis_1_7 ?_ ?_ y
  · dsimp [iBasis_2_7, polyEval]; norm_num
  · intro u; dsimp [iBasis_2_7, iBasis_1_7, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_3_7 (y : ℝ) :
    iterPrim 3 (basisFn ⟨7, by omega⟩) y = polyEval iBasis_3_7 y := by
  refine iterPrim_succ_of_polyEval 2 iBasis_2_7 iBasis_3_7 iterPrim_basis_2_7 ?_ ?_ y
  · dsimp [iBasis_3_7, polyEval]; norm_num
  · intro u; dsimp [iBasis_3_7, iBasis_2_7, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_4_7 (y : ℝ) :
    iterPrim 4 (basisFn ⟨7, by omega⟩) y = polyEval iBasis_4_7 y := by
  refine iterPrim_succ_of_polyEval 3 iBasis_3_7 iBasis_4_7 iterPrim_basis_3_7 ?_ ?_ y
  · dsimp [iBasis_4_7, polyEval]; norm_num
  · intro u; dsimp [iBasis_4_7, iBasis_3_7, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_5_7 (y : ℝ) :
    iterPrim 5 (basisFn ⟨7, by omega⟩) y = polyEval iBasis_5_7 y := by
  refine iterPrim_succ_of_polyEval 4 iBasis_4_7 iBasis_5_7 iterPrim_basis_4_7 ?_ ?_ y
  · dsimp [iBasis_5_7, polyEval]; norm_num
  · intro u; dsimp [iBasis_5_7, iBasis_4_7, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_6_7 (y : ℝ) :
    iterPrim 6 (basisFn ⟨7, by omega⟩) y = polyEval iBasis_6_7 y := by
  refine iterPrim_succ_of_polyEval 5 iBasis_5_7 iBasis_6_7 iterPrim_basis_5_7 ?_ ?_ y
  · dsimp [iBasis_6_7, polyEval]; norm_num
  · intro u; dsimp [iBasis_6_7, iBasis_5_7, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_7_7 (y : ℝ) :
    iterPrim 7 (basisFn ⟨7, by omega⟩) y = polyEval iBasis_7_7 y := by
  refine iterPrim_succ_of_polyEval 6 iBasis_6_7 iBasis_7_7 iterPrim_basis_6_7 ?_ ?_ y
  · dsimp [iBasis_7_7, polyEval]; norm_num
  · intro u; dsimp [iBasis_7_7, iBasis_6_7, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_8_7 (y : ℝ) :
    iterPrim 8 (basisFn ⟨7, by omega⟩) y = polyEval iBasis_8_7 y := by
  refine iterPrim_succ_of_polyEval 7 iBasis_7_7 iBasis_8_7 iterPrim_basis_7_7 ?_ ?_ y
  · dsimp [iBasis_8_7, polyEval]; norm_num
  · intro u; dsimp [iBasis_8_7, iBasis_7_7, polyDeriv, polyAdd, polyEval]; ring
private def iBasis_0_8 : List ℝ := ([212355 / 32768, 0, -3610035 / 4096, 0, 160044885 / 8192, 0, -672188517 / 4096, 0, 11043097065 / 16384, 0, -6135053925 / 4096, 0, 15058768725 / 8192, 0, -4798948275 / 4096, 0, 9917826435 / 32768] : List ℝ)
private def iBasis_1_8 : List ℝ := ([0, 212355 / 32768, 0, -1203345 / 4096, 0, 32008977 / 8192, 0, -96026931 / 4096, 0, 1227010785 / 16384, 0, -557732175 / 4096, 0, 1158366825 / 8192, 0, -319929885 / 4096, 0, 583401555 / 32768] : List ℝ)
private def iBasis_2_8 : List ℝ := ([-1573 / 65536, 0, 212355 / 65536, 0, -1203345 / 16384, 0, 10669659 / 16384, 0, -96026931 / 32768, 0, 245402157 / 32768, 0, -185910725 / 16384, 0, 165480975 / 16384, 0, -319929885 / 65536, 0, 64822395 / 65536] : List ℝ)
private def iBasis_3_8 : List ℝ := ([0, -1573 / 65536, 0, 70785 / 65536, 0, -240669 / 16384, 0, 1524237 / 16384, 0, -10669659 / 32768, 0, 22309287 / 32768, 0, -14300825 / 16384, 0, 11032065 / 16384, 0, -18819405 / 65536, 0, 3411705 / 65536] : List ℝ)
private def iBasis_4_8 : List ℝ := ([121 / 1310720, 0, -1573 / 131072, 0, 70785 / 262144, 0, -80223 / 32768, 0, 1524237 / 131072, 0, -10669659 / 327680, 0, 7436429 / 131072, 0, -2042975 / 32768, 0, 11032065 / 262144, 0, -2091045 / 131072, 0, 682341 / 262144] : List ℝ)
private def iBasis_5_8 : List ℝ := ([0, 121 / 1310720, 0, -1573 / 393216, 0, 14157 / 262144, 0, -80223 / 229376, 0, 508079 / 393216, 0, -969969 / 327680, 0, 572033 / 131072, 0, -408595 / 98304, 0, 648945 / 262144, 0, -110055 / 131072, 0, 227447 / 1835008] : List ℝ)
private def iBasis_6_8 : List ℝ := ([-1 / 2621440, 0, 121 / 2621440, 0, -1573 / 1572864, 0, 4719 / 524288, 0, -80223 / 1835008, 0, 508079 / 3932160, 0, -323323 / 1310720, 0, 81719 / 262144, 0, -408595 / 1572864, 0, 72105 / 524288, 0, -22011 / 524288, 0, 20677 / 3670016] : List ℝ)
private def iBasis_7_8 : List ℝ := ([0, -1 / 2621440, 0, 121 / 7864320, 0, -1573 / 7864320, 0, 4719 / 3670016, 0, -26741 / 5505024, 0, 46189 / 3932160, 0, -24871 / 1310720, 0, 81719 / 3932160, 0, -24035 / 1572864, 0, 3795 / 524288, 0, -7337 / 3670016, 0, 899 / 3670016] : List ℝ)
private def iBasis_8_8 : List ℝ := ([1 / 566231040, 0, -1 / 5242880, 0, 121 / 31457280, 0, -1573 / 47185920, 0, 4719 / 29360128, 0, -26741 / 55050240, 0, 46189 / 47185920, 0, -3553 / 2621440, 0, 81719 / 62914560, 0, -24035 / 28311552, 0, 759 / 2097152, 0, -667 / 7340032, 0, 899 / 88080384] : List ℝ)
private theorem iterPrim_basis_0_8 (y : ℝ) : iterPrim 0 (basisFn ⟨8, by omega⟩) y = polyEval iBasis_0_8 y := by
  dsimp only [iterPrim, basisFn, degAt]; rw [legP_eq_16 y]
  dsimp only [legList_16, iBasis_0_8, polyEval]; ring
private theorem iterPrim_basis_1_8 (y : ℝ) :
    iterPrim 1 (basisFn ⟨8, by omega⟩) y = polyEval iBasis_1_8 y := by
  refine iterPrim_succ_of_polyEval 0 iBasis_0_8 iBasis_1_8 iterPrim_basis_0_8 ?_ ?_ y
  · dsimp [iBasis_1_8, polyEval]; norm_num
  · intro u; dsimp [iBasis_1_8, iBasis_0_8, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_2_8 (y : ℝ) :
    iterPrim 2 (basisFn ⟨8, by omega⟩) y = polyEval iBasis_2_8 y := by
  refine iterPrim_succ_of_polyEval 1 iBasis_1_8 iBasis_2_8 iterPrim_basis_1_8 ?_ ?_ y
  · dsimp [iBasis_2_8, polyEval]; norm_num
  · intro u; dsimp [iBasis_2_8, iBasis_1_8, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_3_8 (y : ℝ) :
    iterPrim 3 (basisFn ⟨8, by omega⟩) y = polyEval iBasis_3_8 y := by
  refine iterPrim_succ_of_polyEval 2 iBasis_2_8 iBasis_3_8 iterPrim_basis_2_8 ?_ ?_ y
  · dsimp [iBasis_3_8, polyEval]; norm_num
  · intro u; dsimp [iBasis_3_8, iBasis_2_8, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_4_8 (y : ℝ) :
    iterPrim 4 (basisFn ⟨8, by omega⟩) y = polyEval iBasis_4_8 y := by
  refine iterPrim_succ_of_polyEval 3 iBasis_3_8 iBasis_4_8 iterPrim_basis_3_8 ?_ ?_ y
  · dsimp [iBasis_4_8, polyEval]; norm_num
  · intro u; dsimp [iBasis_4_8, iBasis_3_8, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_5_8 (y : ℝ) :
    iterPrim 5 (basisFn ⟨8, by omega⟩) y = polyEval iBasis_5_8 y := by
  refine iterPrim_succ_of_polyEval 4 iBasis_4_8 iBasis_5_8 iterPrim_basis_4_8 ?_ ?_ y
  · dsimp [iBasis_5_8, polyEval]; norm_num
  · intro u; dsimp [iBasis_5_8, iBasis_4_8, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_6_8 (y : ℝ) :
    iterPrim 6 (basisFn ⟨8, by omega⟩) y = polyEval iBasis_6_8 y := by
  refine iterPrim_succ_of_polyEval 5 iBasis_5_8 iBasis_6_8 iterPrim_basis_5_8 ?_ ?_ y
  · dsimp [iBasis_6_8, polyEval]; norm_num
  · intro u; dsimp [iBasis_6_8, iBasis_5_8, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_7_8 (y : ℝ) :
    iterPrim 7 (basisFn ⟨8, by omega⟩) y = polyEval iBasis_7_8 y := by
  refine iterPrim_succ_of_polyEval 6 iBasis_6_8 iBasis_7_8 iterPrim_basis_6_8 ?_ ?_ y
  · dsimp [iBasis_7_8, polyEval]; norm_num
  · intro u; dsimp [iBasis_7_8, iBasis_6_8, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_8_8 (y : ℝ) :
    iterPrim 8 (basisFn ⟨8, by omega⟩) y = polyEval iBasis_8_8 y := by
  refine iterPrim_succ_of_polyEval 7 iBasis_7_8 iBasis_8_8 iterPrim_basis_7_8 ?_ ?_ y
  · dsimp [iBasis_8_8, polyEval]; norm_num
  · intro u; dsimp [iBasis_8_8, iBasis_7_8, polyDeriv, polyAdd, polyEval]; ring
private def iBasis_0_9 : List ℝ := ([-449735 / 65536, 0, 76904685 / 65536, 0, -538332795 / 16384, 0, 5778105333 / 16384, 0, -61908271425 / 32768, 0, 185724814275 / 32768, 0, -163212715575 / 16384, 0, 166799808225 / 16384, 0, -366959578095 / 65536, 0, 83945001525 / 65536] : List ℝ)
private def iBasis_1_9 : List ℝ := ([0, -449735 / 65536, 0, 25634895 / 65536, 0, -107666559 / 16384, 0, 825443619 / 16384, 0, -6878696825 / 32768, 0, 16884074025 / 32768, 0, -12554824275 / 16384, 0, 11119987215 / 16384, 0, -21585857535 / 65536, 0, 4418157975 / 65536] : List ℝ)
private def iBasis_2_9 : List ℝ := ([5291 / 262144, 0, -449735 / 131072, 0, 25634895 / 262144, 0, -35888853 / 32768, 0, 825443619 / 131072, 0, -1375739365 / 65536, 0, 5628024675 / 131072, 0, -1793546325 / 32768, 0, 11119987215 / 262144, 0, -2398428615 / 131072, 0, 883631595 / 262144] : List ℝ)
private def iBasis_3_9 : List ℝ := ([0, 5291 / 262144, 0, -449735 / 393216, 0, 5126979 / 262144, 0, -5126979 / 32768, 0, 275147873 / 393216, 0, -125067215 / 65536, 0, 432924975 / 131072, 0, -119569755 / 32768, 0, 654116895 / 262144, 0, -126233085 / 131072, 0, 42077695 / 262144] : List ℝ)
private def iBasis_4_9 : List ℝ := ([-481 / 7864320, 0, 5291 / 524288, 0, -449735 / 1572864, 0, 1708993 / 524288, 0, -5126979 / 262144, 0, 275147873 / 3932160, 0, -125067215 / 786432, 0, 61846425 / 262144, 0, -119569755 / 524288, 0, 72679655 / 524288, 0, -25246617 / 524288, 0, 3825245 / 524288] : List ℝ)
private def iBasis_5_9 : List ℝ := ([0, -481 / 7864320, 0, 5291 / 1572864, 0, -89947 / 1572864, 0, 1708993 / 3670016, 0, -1708993 / 786432, 0, 25013443 / 3932160, 0, -9620555 / 786432, 0, 4123095 / 262144, 0, -7033515 / 524288, 0, 3825245 / 524288, 0, -8415539 / 3670016, 0, 166315 / 524288] : List ℝ)
private def iBasis_6_9 : List ℝ := ([37 / 188743680, 0, -481 / 15728640, 0, 5291 / 6291456, 0, -89947 / 9437184, 0, 1708993 / 29360128, 0, -1708993 / 7864320, 0, 25013443 / 47185920, 0, -1374365 / 1572864, 0, 4123095 / 4194304, 0, -2344505 / 3145728, 0, 765049 / 2097152, 0, -765049 / 7340032, 0, 166315 / 12582912] : List ℝ)
private def iBasis_7_9 : List ℝ := ([0, 37 / 188743680, 0, -481 / 47185920, 0, 5291 / 31457280, 0, -89947 / 66060288, 0, 1708993 / 264241152, 0, -155363 / 7864320, 0, 1924111 / 47185920, 0, -274873 / 4718592, 0, 242535 / 4194304, 0, -123395 / 3145728, 0, 765049 / 44040192, 0, -33263 / 7340032, 0, 33263 / 62914560] : List ℝ)
private def iBasis_8_9 : List ℝ := ([-37 / 53980692480, 0, 37 / 377487360, 0, -481 / 188743680, 0, 5291 / 188743680, 0, -89947 / 528482304, 0, 1708993 / 2642411520, 0, -155363 / 94371840, 0, 274873 / 94371840, 0, -274873 / 75497472, 0, 80845 / 25165824, 0, -24679 / 12582912, 0, 765049 / 968884224, 0, -33263 / 176160768, 0, 33263 / 1635778560] : List ℝ)
private theorem iterPrim_basis_0_9 (y : ℝ) : iterPrim 0 (basisFn ⟨9, by omega⟩) y = polyEval iBasis_0_9 y := by
  dsimp only [iterPrim, basisFn, degAt]; rw [legP_eq_18 y]
  dsimp only [legList_18, iBasis_0_9, polyEval]; ring
private theorem iterPrim_basis_1_9 (y : ℝ) :
    iterPrim 1 (basisFn ⟨9, by omega⟩) y = polyEval iBasis_1_9 y := by
  refine iterPrim_succ_of_polyEval 0 iBasis_0_9 iBasis_1_9 iterPrim_basis_0_9 ?_ ?_ y
  · dsimp [iBasis_1_9, polyEval]; norm_num
  · intro u; dsimp [iBasis_1_9, iBasis_0_9, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_2_9 (y : ℝ) :
    iterPrim 2 (basisFn ⟨9, by omega⟩) y = polyEval iBasis_2_9 y := by
  refine iterPrim_succ_of_polyEval 1 iBasis_1_9 iBasis_2_9 iterPrim_basis_1_9 ?_ ?_ y
  · dsimp [iBasis_2_9, polyEval]; norm_num
  · intro u; dsimp [iBasis_2_9, iBasis_1_9, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_3_9 (y : ℝ) :
    iterPrim 3 (basisFn ⟨9, by omega⟩) y = polyEval iBasis_3_9 y := by
  refine iterPrim_succ_of_polyEval 2 iBasis_2_9 iBasis_3_9 iterPrim_basis_2_9 ?_ ?_ y
  · dsimp [iBasis_3_9, polyEval]; norm_num
  · intro u; dsimp [iBasis_3_9, iBasis_2_9, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_4_9 (y : ℝ) :
    iterPrim 4 (basisFn ⟨9, by omega⟩) y = polyEval iBasis_4_9 y := by
  refine iterPrim_succ_of_polyEval 3 iBasis_3_9 iBasis_4_9 iterPrim_basis_3_9 ?_ ?_ y
  · dsimp [iBasis_4_9, polyEval]; norm_num
  · intro u; dsimp [iBasis_4_9, iBasis_3_9, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_5_9 (y : ℝ) :
    iterPrim 5 (basisFn ⟨9, by omega⟩) y = polyEval iBasis_5_9 y := by
  refine iterPrim_succ_of_polyEval 4 iBasis_4_9 iBasis_5_9 iterPrim_basis_4_9 ?_ ?_ y
  · dsimp [iBasis_5_9, polyEval]; norm_num
  · intro u; dsimp [iBasis_5_9, iBasis_4_9, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_6_9 (y : ℝ) :
    iterPrim 6 (basisFn ⟨9, by omega⟩) y = polyEval iBasis_6_9 y := by
  refine iterPrim_succ_of_polyEval 5 iBasis_5_9 iBasis_6_9 iterPrim_basis_5_9 ?_ ?_ y
  · dsimp [iBasis_6_9, polyEval]; norm_num
  · intro u; dsimp [iBasis_6_9, iBasis_5_9, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_7_9 (y : ℝ) :
    iterPrim 7 (basisFn ⟨9, by omega⟩) y = polyEval iBasis_7_9 y := by
  refine iterPrim_succ_of_polyEval 6 iBasis_6_9 iBasis_7_9 iterPrim_basis_6_9 ?_ ?_ y
  · dsimp [iBasis_7_9, polyEval]; norm_num
  · intro u; dsimp [iBasis_7_9, iBasis_6_9, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_8_9 (y : ℝ) :
    iterPrim 8 (basisFn ⟨9, by omega⟩) y = polyEval iBasis_8_9 y := by
  refine iterPrim_succ_of_polyEval 7 iBasis_7_9 iBasis_8_9 iterPrim_basis_7_9 ?_ ?_ y
  · dsimp [iBasis_8_9, polyEval]; norm_num
  · intro u; dsimp [iBasis_8_9, iBasis_7_9, polyDeriv, polyAdd, polyEval]; ring
private def iBasis_0_10 : List ℝ := ([1893749 / 262144, 0, -198843645 / 131072, 0, 13720211505 / 262144, 0, -22867019175 / 32768, 0, 617409517725 / 131072, 0, -1193658400935 / 65536, 0, 5606577337725 / 131072, 0, -2033154419175 / 32768, 0, 14232080934225 / 262144, 0, -3441745062525 / 131072, 0, 1412926920405 / 262144] : List ℝ)
private def iBasis_1_10 : List ℝ := ([0, 1893749 / 262144, 0, -66281215 / 131072, 0, 2744042301 / 262144, 0, -3266717025 / 32768, 0, 68601057525 / 131072, 0, -108514400085 / 65536, 0, 431275179825 / 131072, 0, -135543627945 / 32768, 0, 837181231425 / 262144, 0, -181144476975 / 131072, 0, 67282234305 / 262144] : List ℝ)
private def iBasis_2_10 : List ℝ := ([-9061 / 524288, 0, 1893749 / 524288, 0, -66281215 / 524288, 0, 914680767 / 524288, 0, -3266717025 / 262144, 0, 13720211505 / 262144, 0, -36171466695 / 262144, 0, 61610739975 / 262144, 0, -135543627945 / 524288, 0, 93020136825 / 524288, 0, -36228895395 / 524288, 0, 6116566755 / 524288] : List ℝ)
private def iBasis_3_10 : List ℝ := ([0, -9061 / 524288, 0, 1893749 / 1572864, 0, -13256243 / 524288, 0, 130668681 / 524288, 0, -1088905675 / 786432, 0, 1247291955 / 262144, 0, -2782420515 / 262144, 0, 4107382665 / 262144, 0, -7973154585 / 524288, 0, 4895796675 / 524288, 0, -1725185495 / 524288, 0, 265937685 / 524288] : List ℝ)
private def iBasis_4_10 : List ℝ := ([533 / 12582912, 0, -9061 / 1048576, 0, 1893749 / 6291456, 0, -13256243 / 3145728, 0, 130668681 / 4194304, 0, -217781135 / 1572864, 0, 415763985 / 1048576, 0, -397488645 / 524288, 0, 4107382665 / 4194304, 0, -885906065 / 1048576, 0, 979159335 / 2097152, 0, -156835045 / 1048576, 0, 88645895 / 4194304] : List ℝ)
private def iBasis_5_10 : List ℝ := ([0, 533 / 12582912, 0, -9061 / 3145728, 0, 1893749 / 31457280, 0, -1893749 / 3145728, 0, 43556227 / 12582912, 0, -19798285 / 1572864, 0, 31981845 / 1048576, 0, -26499243 / 524288, 0, 241610745 / 4194304, 0, -46626635 / 1048576, 0, 46626635 / 2097152, 0, -6818915 / 1048576, 0, 17729179 / 20971520] : List ℝ)
private def iBasis_6_10 : List ℝ := ([-41 / 377487360, 0, 533 / 25165824, 0, -9061 / 12582912, 0, 1893749 / 188743680, 0, -1893749 / 25165824, 0, 43556227 / 125829120, 0, -19798285 / 18874368, 0, 4568835 / 2097152, 0, -26499243 / 8388608, 0, 80536915 / 25165824, 0, -9325327 / 4194304, 0, 4238785 / 4194304, 0, -6818915 / 25165824, 0, 1363783 / 41943040] : List ℝ)
private def iBasis_7_10 : List ℝ := ([0, -41 / 377487360, 0, 533 / 75497472, 0, -9061 / 62914560, 0, 1893749 / 1321205760, 0, -1893749 / 226492416, 0, 3959657 / 125829120, 0, -1522945 / 18874368, 0, 304589 / 2097152, 0, -1558779 / 8388608, 0, 4238785 / 25165824, 0, -9325327 / 88080384, 0, 184295 / 4194304, 0, -1363783 / 125829120, 0, 1363783 / 1132462080] : List ℝ)
private def iBasis_8_10 : List ℝ := ([41 / 137405399040, 0, -41 / 754974720, 0, 533 / 301989888, 0, -9061 / 377487360, 0, 1893749 / 10569646080, 0, -1893749 / 2264924160, 0, 3959657 / 1509949440, 0, -1522945 / 264241152, 0, 304589 / 33554432, 0, -519593 / 50331648, 0, 847757 / 100663296, 0, -847757 / 176160768, 0, 184295 / 100663296, 0, -1363783 / 3271557120, 0, 1363783 / 31708938240] : List ℝ)
private theorem iterPrim_basis_0_10 (y : ℝ) : iterPrim 0 (basisFn ⟨10, by omega⟩) y = polyEval iBasis_0_10 y := by
  dsimp only [iterPrim, basisFn, degAt]; rw [legP_eq_20 y]
  dsimp only [legList_20, iBasis_0_10, polyEval]; ring
private theorem iterPrim_basis_1_10 (y : ℝ) :
    iterPrim 1 (basisFn ⟨10, by omega⟩) y = polyEval iBasis_1_10 y := by
  refine iterPrim_succ_of_polyEval 0 iBasis_0_10 iBasis_1_10 iterPrim_basis_0_10 ?_ ?_ y
  · dsimp [iBasis_1_10, polyEval]; norm_num
  · intro u; dsimp [iBasis_1_10, iBasis_0_10, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_2_10 (y : ℝ) :
    iterPrim 2 (basisFn ⟨10, by omega⟩) y = polyEval iBasis_2_10 y := by
  refine iterPrim_succ_of_polyEval 1 iBasis_1_10 iBasis_2_10 iterPrim_basis_1_10 ?_ ?_ y
  · dsimp [iBasis_2_10, polyEval]; norm_num
  · intro u; dsimp [iBasis_2_10, iBasis_1_10, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_3_10 (y : ℝ) :
    iterPrim 3 (basisFn ⟨10, by omega⟩) y = polyEval iBasis_3_10 y := by
  refine iterPrim_succ_of_polyEval 2 iBasis_2_10 iBasis_3_10 iterPrim_basis_2_10 ?_ ?_ y
  · dsimp [iBasis_3_10, polyEval]; norm_num
  · intro u; dsimp [iBasis_3_10, iBasis_2_10, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_4_10 (y : ℝ) :
    iterPrim 4 (basisFn ⟨10, by omega⟩) y = polyEval iBasis_4_10 y := by
  refine iterPrim_succ_of_polyEval 3 iBasis_3_10 iBasis_4_10 iterPrim_basis_3_10 ?_ ?_ y
  · dsimp [iBasis_4_10, polyEval]; norm_num
  · intro u; dsimp [iBasis_4_10, iBasis_3_10, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_5_10 (y : ℝ) :
    iterPrim 5 (basisFn ⟨10, by omega⟩) y = polyEval iBasis_5_10 y := by
  refine iterPrim_succ_of_polyEval 4 iBasis_4_10 iBasis_5_10 iterPrim_basis_4_10 ?_ ?_ y
  · dsimp [iBasis_5_10, polyEval]; norm_num
  · intro u; dsimp [iBasis_5_10, iBasis_4_10, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_6_10 (y : ℝ) :
    iterPrim 6 (basisFn ⟨10, by omega⟩) y = polyEval iBasis_6_10 y := by
  refine iterPrim_succ_of_polyEval 5 iBasis_5_10 iBasis_6_10 iterPrim_basis_5_10 ?_ ?_ y
  · dsimp [iBasis_6_10, polyEval]; norm_num
  · intro u; dsimp [iBasis_6_10, iBasis_5_10, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_7_10 (y : ℝ) :
    iterPrim 7 (basisFn ⟨10, by omega⟩) y = polyEval iBasis_7_10 y := by
  refine iterPrim_succ_of_polyEval 6 iBasis_6_10 iBasis_7_10 iterPrim_basis_6_10 ?_ ?_ y
  · dsimp [iBasis_7_10, polyEval]; norm_num
  · intro u; dsimp [iBasis_7_10, iBasis_6_10, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_8_10 (y : ℝ) :
    iterPrim 8 (basisFn ⟨10, by omega⟩) y = polyEval iBasis_8_10 y := by
  refine iterPrim_succ_of_polyEval 7 iBasis_7_10 iBasis_8_10 iterPrim_basis_7_10 ?_ ?_ y
  · dsimp [iBasis_8_10, polyEval]; norm_num
  · intro u; dsimp [iBasis_8_10, iBasis_7_10, polyDeriv, polyAdd, polyEval]; ring
private def iBasis_0_11 : List ℝ := ([-3968055 / 524288, 0, 1003917915 / 524288, 0, -41829913125 / 524288, 0, 677644592625 / 524288, 0, -2807384740875 / 262144, 0, 13537833083775 / 262144, 0, -40613499251325 / 262144, 0, 78102883175625 / 262144, 0, -192653778499875 / 524288, 0, 147323477676375 / 524288, 0, -63581711418225 / 524288, 0, 11835556670925 / 524288] : List ℝ)
private def iBasis_1_11 : List ℝ := ([0, -3968055 / 524288, 0, 334639305 / 524288, 0, -8365982625 / 524288, 0, 96806370375 / 524288, 0, -311931637875 / 262144, 0, 1230712098525 / 262144, 0, -3124115327025 / 262144, 0, 5206858878375 / 262144, 0, -11332575205875 / 524288, 0, 7753867246125 / 524288, 0, -3027700543725 / 524288, 0, 514589420475 / 524288] : List ℝ)
private def iBasis_2_11 : List ℝ := ([62985 / 4194304, 0, -3968055 / 1048576, 0, 334639305 / 2097152, 0, -2788660875 / 1048576, 0, 96806370375 / 4194304, 0, -62386327575 / 524288, 0, 410237366175 / 1048576, 0, -446302189575 / 524288, 0, 5206858878375 / 4194304, 0, -1259175022875 / 1048576, 0, 1550773449225 / 2097152, 0, -275245503975 / 1048576, 0, 171529806825 / 4194304] : List ℝ)
private def iBasis_3_11 : List ℝ := ([0, 62985 / 4194304, 0, -1322685 / 1048576, 0, 66927861 / 2097152, 0, -398380125 / 1048576, 0, 10756263375 / 4194304, 0, -5671484325 / 524288, 0, 31556720475 / 1048576, 0, -29753479305 / 524288, 0, 306285816375 / 4194304, 0, -66272369625 / 1048576, 0, 73846354725 / 2097152, 0, -11967195825 / 1048576, 0, 6861192273 / 4194304] : List ℝ)
private def iBasis_4_11 : List ℝ := ([-255 / 8388608, 0, 62985 / 8388608, 0, -1322685 / 4194304, 0, 22309287 / 4194304, 0, -398380125 / 8388608, 0, 2151252675 / 8388608, 0, -1890494775 / 2097152, 0, 4508102925 / 2097152, 0, -29753479305 / 8388608, 0, 34031757375 / 8388608, 0, -13254473925 / 4194304, 0, 6713304975 / 4194304, 0, -3989065275 / 8388608, 0, 527784021 / 8388608] : List ℝ)
private def iBasis_5_11 : List ℝ := ([0, -255 / 8388608, 0, 20995 / 8388608, 0, -264537 / 4194304, 0, 3187041 / 4194304, 0, -132793375 / 25165824, 0, 195568425 / 8388608, 0, -145422675 / 2097152, 0, 300540195 / 2097152, 0, -1750204665 / 8388608, 0, 1791145125 / 8388608, 0, -631165425 / 4194304, 0, 291882825 / 4194304, 0, -159562611 / 8388608, 0, 58642669 / 25165824] : List ℝ)
private def iBasis_6_11 : List ℝ := ([15 / 234881024, 0, -255 / 16777216, 0, 20995 / 33554432, 0, -88179 / 8388608, 0, 3187041 / 33554432, 0, -26558675 / 50331648, 0, 65189475 / 33554432, 0, -145422675 / 29360128, 0, 300540195 / 33554432, 0, -194467185 / 16777216, 0, 358229025 / 33554432, 0, -57378675 / 8388608, 0, 97294275 / 33554432, 0, -12274047 / 16777216, 0, 58642669 / 704643072] : List ℝ)
private def iBasis_7_11 : List ℝ := ([0, 15 / 234881024, 0, -85 / 16777216, 0, 4199 / 33554432, 0, -12597 / 8388608, 0, 1062347 / 100663296, 0, -2414425 / 50331648, 0, 5014575 / 33554432, 0, -9694845 / 29360128, 0, 17678835 / 33554432, 0, -10235115 / 16777216, 0, 17058525 / 33554432, 0, -2494725 / 8388608, 0, 3891771 / 33554432, 0, -1363783 / 50331648, 0, 2022161 / 704643072] : List ℝ)
private def iBasis_8_11 : List ℝ := ([-1 / 7046430720, 0, 15 / 469762048, 0, -85 / 67108864, 0, 4199 / 201326592, 0, -12597 / 67108864, 0, 1062347 / 1006632960, 0, -2414425 / 603979776, 0, 5014575 / 469762048, 0, -9694845 / 469762048, 0, 1964315 / 67108864, 0, -2047023 / 67108864, 0, 1550775 / 67108864, 0, -831575 / 67108864, 0, 299367 / 67108864, 0, -1363783 / 1409286144, 0, 2022161 / 21139292160] : List ℝ)
private theorem iterPrim_basis_0_11 (y : ℝ) : iterPrim 0 (basisFn ⟨11, by omega⟩) y = polyEval iBasis_0_11 y := by
  dsimp only [iterPrim, basisFn, degAt]; rw [legP_eq_22 y]
  dsimp only [legList_22, iBasis_0_11, polyEval]; ring
private theorem iterPrim_basis_1_11 (y : ℝ) :
    iterPrim 1 (basisFn ⟨11, by omega⟩) y = polyEval iBasis_1_11 y := by
  refine iterPrim_succ_of_polyEval 0 iBasis_0_11 iBasis_1_11 iterPrim_basis_0_11 ?_ ?_ y
  · dsimp [iBasis_1_11, polyEval]; norm_num
  · intro u; dsimp [iBasis_1_11, iBasis_0_11, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_2_11 (y : ℝ) :
    iterPrim 2 (basisFn ⟨11, by omega⟩) y = polyEval iBasis_2_11 y := by
  refine iterPrim_succ_of_polyEval 1 iBasis_1_11 iBasis_2_11 iterPrim_basis_1_11 ?_ ?_ y
  · dsimp [iBasis_2_11, polyEval]; norm_num
  · intro u; dsimp [iBasis_2_11, iBasis_1_11, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_3_11 (y : ℝ) :
    iterPrim 3 (basisFn ⟨11, by omega⟩) y = polyEval iBasis_3_11 y := by
  refine iterPrim_succ_of_polyEval 2 iBasis_2_11 iBasis_3_11 iterPrim_basis_2_11 ?_ ?_ y
  · dsimp [iBasis_3_11, polyEval]; norm_num
  · intro u; dsimp [iBasis_3_11, iBasis_2_11, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_4_11 (y : ℝ) :
    iterPrim 4 (basisFn ⟨11, by omega⟩) y = polyEval iBasis_4_11 y := by
  refine iterPrim_succ_of_polyEval 3 iBasis_3_11 iBasis_4_11 iterPrim_basis_3_11 ?_ ?_ y
  · dsimp [iBasis_4_11, polyEval]; norm_num
  · intro u; dsimp [iBasis_4_11, iBasis_3_11, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_5_11 (y : ℝ) :
    iterPrim 5 (basisFn ⟨11, by omega⟩) y = polyEval iBasis_5_11 y := by
  refine iterPrim_succ_of_polyEval 4 iBasis_4_11 iBasis_5_11 iterPrim_basis_4_11 ?_ ?_ y
  · dsimp [iBasis_5_11, polyEval]; norm_num
  · intro u; dsimp [iBasis_5_11, iBasis_4_11, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_6_11 (y : ℝ) :
    iterPrim 6 (basisFn ⟨11, by omega⟩) y = polyEval iBasis_6_11 y := by
  refine iterPrim_succ_of_polyEval 5 iBasis_5_11 iBasis_6_11 iterPrim_basis_5_11 ?_ ?_ y
  · dsimp [iBasis_6_11, polyEval]; norm_num
  · intro u; dsimp [iBasis_6_11, iBasis_5_11, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_7_11 (y : ℝ) :
    iterPrim 7 (basisFn ⟨11, by omega⟩) y = polyEval iBasis_7_11 y := by
  refine iterPrim_succ_of_polyEval 6 iBasis_6_11 iBasis_7_11 iterPrim_basis_6_11 ?_ ?_ y
  · dsimp [iBasis_7_11, polyEval]; norm_num
  · intro u; dsimp [iBasis_7_11, iBasis_6_11, polyDeriv, polyAdd, polyEval]; ring
private theorem iterPrim_basis_8_11 (y : ℝ) :
    iterPrim 8 (basisFn ⟨11, by omega⟩) y = polyEval iBasis_8_11 y := by
  refine iterPrim_succ_of_polyEval 7 iBasis_7_11 iBasis_8_11 iterPrim_basis_7_11 ?_ ?_ y
  · dsimp [iBasis_8_11, polyEval]; norm_num
  · intro u; dsimp [iBasis_8_11, iBasis_7_11, polyDeriv, polyAdd, polyEval]; ring
private def iBasis0Q : List (List ℚ) := ([[1],
    [-5 / 2, 0, 15 / 2],
    [27 / 8, 0, -135 / 4, 0, 315 / 8],
    [-65 / 16, 0, 1365 / 16, 0, -4095 / 16, 0, 3003 / 16],
    [595 / 128, 0, -5355 / 32, 0, 58905 / 64, 0, -51051 / 32, 0, 109395 / 128],
    [-1323 / 256, 0, 72765 / 256, 0, -315315 / 128, 0, 945945 / 128, 0, -2297295 / 256, 0, 969969 / 256],
    [5775 / 1024, 0, -225225 / 512, 0, 5630625 / 1024, 0, -6381375 / 256, 0, 51962625 / 1024, 0, -24249225 / 512, 0, 16900975 / 1024],
    [-12441 / 2048, 0, 1306305 / 2048, 0, -22207185 / 2048, 0, 140645505 / 2048, 0, -421936515 / 2048, 0, 646969323 / 2048, 0, -490128275 / 2048, 0, 145422675 / 2048],
    [212355 / 32768, 0, -3610035 / 4096, 0, 160044885 / 8192, 0, -672188517 / 4096, 0, 11043097065 / 16384, 0, -6135053925 / 4096, 0, 15058768725 / 8192, 0, -4798948275 / 4096, 0, 9917826435 / 32768],
    [-449735 / 65536, 0, 76904685 / 65536, 0, -538332795 / 16384, 0, 5778105333 / 16384, 0, -61908271425 / 32768, 0, 185724814275 / 32768, 0, -163212715575 / 16384, 0, 166799808225 / 16384, 0, -366959578095 / 65536, 0, 83945001525 / 65536],
    [1893749 / 262144, 0, -198843645 / 131072, 0, 13720211505 / 262144, 0, -22867019175 / 32768, 0, 617409517725 / 131072, 0, -1193658400935 / 65536, 0, 5606577337725 / 131072, 0, -2033154419175 / 32768, 0, 14232080934225 / 262144, 0, -3441745062525 / 131072, 0, 1412926920405 / 262144],
    [-3968055 / 524288, 0, 1003917915 / 524288, 0, -41829913125 / 524288, 0, 677644592625 / 524288, 0, -2807384740875 / 262144, 0, 13537833083775 / 262144, 0, -40613499251325 / 262144, 0, 78102883175625 / 262144, 0, -192653778499875 / 524288, 0, 147323477676375 / 524288, 0, -63581711418225 / 524288, 0, 11835556670925 / 524288]] : List (List ℚ))
private theorem polyEval_iBasis_0 (i : Fin 12) (y : ℝ) :
    polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y =
      ApertureLogTwo.qeval (iBasis0Q.getD i.1 []) y := by
  rcases i with ⟨iv, hiv⟩; dsimp only; interval_cases iv <;>
    (dsimp [iBasis_0_0, iBasis_0_1, iBasis_0_2, iBasis_0_3, iBasis_0_4, iBasis_0_5, iBasis_0_6, iBasis_0_7, iBasis_0_8, iBasis_0_9, iBasis_0_10, iBasis_0_11, iBasis0Q, List.getD, polyEval, ApertureLogTwo.qeval]; norm_num; dsimp [polyEval]; ring)

private theorem iterPrim_const_mul {f : ℝ → ℝ} (hf : Continuous f) (c : ℝ) :
    ∀ (s : ℕ) (y : ℝ), iterPrim s (fun u => c * f u) y = c * iterPrim s f y
  | 0, _ => rfl
  | s + 1, y => by
    simp only [iterPrim]
    simp_rw [iterPrim_const_mul hf c s]
    exact intervalIntegral.integral_const_mul c _

private theorem iterPrim_finset_sum {ι : Type*} (S : Finset ι) {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ S, Continuous (f i)) :
    ∀ (s : ℕ) (y : ℝ), iterPrim s (fun u => ∑ i ∈ S, f i u) y = ∑ i ∈ S, iterPrim s (f i) y := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro s y; simp only [Finset.sum_empty]
    induction s generalizing y with
    | zero => rfl
    | succ s ih => simp only [iterPrim, ih, intervalIntegral.integral_zero]
  | @insert a S ha ihS =>
    intro s y
    have hfa : Continuous (f a) := hf a (Finset.mem_insert_self a S)
    have hfS : Continuous (fun u => ∑ i ∈ S, f i u) :=
      continuous_finsetSum S fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hfun : (fun u => ∑ i ∈ insert a S, f i u) = fun u => f a u + ∑ i ∈ S, f i u :=
      funext fun u => Finset.sum_insert ha
    rw [hfun, iterPrim_linear_add hfa hfS s y,
      ihS (fun i hi => hf i (Finset.mem_insert_of_mem hi)) s y, Finset.sum_insert ha]

private def iBasisStepQ_0 : List (List ℚ) := ([[1 / 2, 1, 1 / 2],
    [5 / 8, 0, -5 / 4, 0, 5 / 8],
    [-3 / 16, 0, 27 / 16, 0, -45 / 16, 0, 21 / 16],
    [13 / 128, 0, -65 / 32, 0, 455 / 64, 0, -273 / 32, 0, 429 / 128],
    [-17 / 256, 0, 595 / 256, 0, -1785 / 128, 0, 3927 / 128, 0, -7293 / 256, 0, 2431 / 256],
    [49 / 1024, 0, -1323 / 512, 0, 24255 / 1024, 0, -21021 / 256, 0, 135135 / 1024, 0, -51051 / 512, 0, 29393 / 1024],
    [-75 / 2048, 0, 5775 / 2048, 0, -75075 / 2048, 0, 375375 / 2048, 0, -911625 / 2048, 0, 1154725 / 2048, 0, -734825 / 2048, 0, 185725 / 2048],
    [957 / 32768, 0, -12441 / 4096, 0, 435435 / 8192, 0, -1480479 / 4096, 0, 20092215 / 16384, 0, -9376367 / 4096, 0, 19605131 / 8192, 0, -5386025 / 4096, 0, 9694845 / 32768],
    [-1573 / 65536, 0, 212355 / 65536, 0, -1203345 / 16384, 0, 10669659 / 16384, 0, -96026931 / 32768, 0, 245402157 / 32768, 0, -185910725 / 16384, 0, 165480975 / 16384, 0, -319929885 / 65536, 0, 64822395 / 65536],
    [5291 / 262144, 0, -449735 / 131072, 0, 25634895 / 262144, 0, -35888853 / 32768, 0, 825443619 / 131072, 0, -1375739365 / 65536, 0, 5628024675 / 131072, 0, -1793546325 / 32768, 0, 11119987215 / 262144, 0, -2398428615 / 131072, 0, 883631595 / 262144],
    [-9061 / 524288, 0, 1893749 / 524288, 0, -66281215 / 524288, 0, 914680767 / 524288, 0, -3266717025 / 262144, 0, 13720211505 / 262144, 0, -36171466695 / 262144, 0, 61610739975 / 262144, 0, -135543627945 / 524288, 0, 93020136825 / 524288, 0, -36228895395 / 524288, 0, 6116566755 / 524288],
    [62985 / 4194304, 0, -3968055 / 1048576, 0, 334639305 / 2097152, 0, -2788660875 / 1048576, 0, 96806370375 / 4194304, 0, -62386327575 / 524288, 0, 410237366175 / 1048576, 0, -446302189575 / 524288, 0, 5206858878375 / 4194304, 0, -1259175022875 / 1048576, 0, 1550773449225 / 2097152, 0, -275245503975 / 1048576, 0, 171529806825 / 4194304]] : List (List ℚ))
private theorem polyEval_iBasisStep_0 (j : Fin 12) (y : ℝ) :
    polyEval (match j.1 with | 0 => iBasis_2_0 | 1 => iBasis_2_1 | 2 => iBasis_2_2 | 3 => iBasis_2_3 | 4 => iBasis_2_4 | 5 => iBasis_2_5 | 6 => iBasis_2_6 | 7 => iBasis_2_7 | 8 => iBasis_2_8 | 9 => iBasis_2_9 | 10 => iBasis_2_10 | 11 => iBasis_2_11 | _ => []) y =
      ApertureLogTwo.qeval (iBasisStepQ_0.getD j.1 []) y := by
  rcases j with ⟨jv, hjv⟩; interval_cases jv <;>
    (dsimp [iBasis_2_0, iBasis_2_1, iBasis_2_2, iBasis_2_3, iBasis_2_4, iBasis_2_5, iBasis_2_6, iBasis_2_7, iBasis_2_8, iBasis_2_9, iBasis_2_10, iBasis_2_11, iBasisStepQ_0, List.getD, polyEval, ApertureLogTwo.qeval]; norm_num; dsimp [polyEval]; ring)
private def mPPRawQ_0 : List (List ℚ) := ([[4 / 3, 2 / 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [2 / 3, -20 / 21, 2 / 7, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 2 / 7, -36 / 77, 2 / 11, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 2 / 11, -52 / 165, 2 / 15, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 2 / 15, -68 / 285, 2 / 19, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 2 / 19, -84 / 437, 2 / 23, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 2 / 23, -100 / 621, 2 / 27, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 2 / 27, -116 / 837, 2 / 31, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 2 / 31, -132 / 1085, 2 / 35, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 2 / 35, -148 / 1365, 2 / 39, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 2 / 39, -164 / 1677, 2 / 43],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2 / 43, -180 / 2021]] : List (List ℚ))
private theorem mPPRawQ_0_ok :
    (List.range 12).all (fun i => (List.range 12).all (fun j =>
      decide (qintSymm (ApertureLogTwo.qmul (iBasis0Q.getD i []) (iBasisStepQ_0.getD j [])) =
        ApertureLogTwo.matQ mPPRawQ_0 i j))) = true := by
  decide +kernel
private theorem int_pp_0 (i j : Fin 12) :
    (∫ y in (-1 : ℝ)..1,
      polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y *
        polyEval (match j.1 with | 0 => iBasis_2_0 | 1 => iBasis_2_1 | 2 => iBasis_2_2 | 3 => iBasis_2_3 | 4 => iBasis_2_4 | 5 => iBasis_2_5 | 6 => iBasis_2_6 | 7 => iBasis_2_7 | 8 => iBasis_2_8 | 9 => iBasis_2_9 | 10 => iBasis_2_10 | 11 => iBasis_2_11 | _ => []) y) =
      (ApertureLogTwo.matQ mPPRawQ_0 i.1 j.1 : ℝ) := by
  simp_rw [polyEval_iBasis_0 i, polyEval_iBasisStep_0 j, integral_qeval_mul_symm]
  have h1 := List.all_eq_true.mp mPPRawQ_0_ok i.1 (List.mem_range.mpr i.2)
  have h2 := List.all_eq_true.mp h1 j.1 (List.mem_range.mpr j.2)
  exact_mod_cast of_decide_eq_true h2
private def qOddMat_0 (i j : Fin 12) : ℝ := matAt ([([1 / 36, 1 / 72] : List ℝ),
    ([1 / 72, -5 / 252, 1 / 168] : List ℝ),
    ([0, 1 / 168, -3 / 308, 1 / 264] : List ℝ),
    ([0, 0, 1 / 264, -13 / 1980, 1 / 360] : List ℝ),
    ([0, 0, 0, 1 / 360, -17 / 3420, 1 / 456] : List ℝ),
    ([0, 0, 0, 0, 1 / 456, -7 / 1748, 1 / 552] : List ℝ),
    ([0, 0, 0, 0, 0, 1 / 552, -25 / 7452, 1 / 648] : List ℝ),
    ([0, 0, 0, 0, 0, 0, 1 / 648, -29 / 10044, 1 / 744] : List ℝ),
    ([0, 0, 0, 0, 0, 0, 0, 1 / 744, -11 / 4340, 1 / 840] : List ℝ),
    ([0, 0, 0, 0, 0, 0, 0, 0, 1 / 840, -37 / 16380, 1 / 936] : List ℝ),
    ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1 / 936, -41 / 20124, 1 / 1032] : List ℝ),
    ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 / 1032, -15 / 8084] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qOddMat_0_sym (i j : Fin 12) : qOddMat_0 i j = qOddMat_0 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qOddRowAbs_0 (i : Fin 12) : ℝ := coeffAt ([1 / 24, 5 / 126, 3 / 154, 13 / 990, 17 / 1710, 7 / 874, 25 / 3726, 29 / 5022, 11 / 2170, 37 / 8190, 41 / 10062, 137 / 48504] : List ℝ) i.1
private theorem qOddRowAbs_0_eq (i : Fin 12) :
    (∑ j : Fin 12, |qOddMat_0 i j|) = qOddRowAbs_0 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qOddMat_0, qOddRowAbs_0, matAt, listAt, coeffAt]; norm_num)
private def gHiQ_0 : List (List ℚ) := ([[0],
    [0],
    [0],
    [0],
    [0],
    [0],
    [0],
    [0],
    [0],
    [0],
    [0],
    [2 / 2303]] : List (List ℚ))
private def gHi_0 (i : Fin 12) (r : ℕ) : ℝ := matAt ([([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([2 / 2303] : List ℝ)] : List (List ℝ)) i.1 r
private theorem gHiQ_0_ok :
    (List.range 12).all (fun i => (List.range 1).all (fun r =>
      decide (qintSymm (ApertureLogTwo.qmul (iBasisStepQ_0.getD i [])
        (ApertureLogTwo.qleg (24 + 2 * r))) =
        ApertureLogTwo.matQ gHiQ_0 i r))) = true := by
  decide +kernel
private theorem gHi_eq_0 (i : Fin 12) (r : ℕ) (hr : r ∈ Finset.range 1) :
    regionalLegendreMoment
      (polyEval (match i.1 with | 0 => iBasis_2_0 | 1 => iBasis_2_1 | 2 => iBasis_2_2 | 3 => iBasis_2_3 | 4 => iBasis_2_4 | 5 => iBasis_2_5 | 6 => iBasis_2_6 | 7 => iBasis_2_7 | 8 => iBasis_2_8 | 9 => iBasis_2_9 | 10 => iBasis_2_10 | 11 => iBasis_2_11 | _ => [])) (24 + 2 * r) =
      gHi_0 i r := by
  unfold regionalLegendreMoment
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  simp_rw [polyEval_iBasisStep_0 i, ApertureLogTwo.legP_eq_qeval_qleg, integral_qeval_mul_symm]
  rw [Finset.mem_range] at hr
  have h1 := List.all_eq_true.mp gHiQ_0_ok i.1 (List.mem_range.mpr i.2)
  have h2 := List.all_eq_true.mp h1 r (List.mem_range.mpr hr)
  have h3 : (qintSymm (ApertureLogTwo.qmul (iBasisStepQ_0.getD i.1 [])
      (ApertureLogTwo.qleg (24 + 2 * r))) : ℝ) =
      (ApertureLogTwo.matQ gHiQ_0 i.1 r : ℝ) := by
    exact_mod_cast of_decide_eq_true h2
  have h4 : (ApertureLogTwo.matQ gHiQ_0 i.1 r : ℝ) = gHi_0 i r := by
    rcases i with ⟨iv, hiv⟩; interval_cases iv <;> interval_cases r <;>
      norm_num [gHiQ_0, gHi_0, ApertureLogTwo.matQ, matAt, listAt, coeffAt]
  exact h3.trans h4

private def iBasisStepQ_1 : List (List ℚ) := ([[1 / 24, 1 / 6, 1 / 4, 1 / 6, 1 / 24],
    [5 / 48, 1 / 3, 5 / 16, 0, -5 / 48, 0, 1 / 48],
    [3 / 128, 0, -3 / 32, 0, 9 / 64, 0, -3 / 32, 0, 3 / 128],
    [-13 / 3840, 0, 13 / 256, 0, -65 / 384, 0, 91 / 384, 0, -39 / 256, 0, 143 / 3840],
    [17 / 15360, 0, -17 / 512, 0, 595 / 3072, 0, -119 / 256, 0, 561 / 1024, 0, -2431 / 7680, 0, 221 / 3072],
    [-1 / 2048, 0, 49 / 2048, 0, -441 / 2048, 0, 1617 / 2048, 0, -3003 / 2048, 0, 3003 / 2048, 0, -1547 / 2048, 0, 323 / 2048],
    [25 / 98304, 0, -75 / 4096, 0, 1925 / 8192, 0, -5005 / 4096, 0, 53625 / 16384, 0, -60775 / 12288, 0, 104975 / 24576, 0, -8075 / 4096, 0, 37145 / 98304],
    [-29 / 196608, 0, 957 / 65536, 0, -4147 / 16384, 0, 29029 / 16384, 0, -211497 / 32768, 0, 1339481 / 98304, 0, -852397 / 49152, 0, 215441 / 16384, 0, -1077205 / 196608, 0, 63365 / 65536],
    [121 / 1310720, 0, -1573 / 131072, 0, 70785 / 262144, 0, -80223 / 32768, 0, 1524237 / 131072, 0, -10669659 / 327680, 0, 7436429 / 131072, 0, -2042975 / 32768, 0, 11032065 / 262144, 0, -2091045 / 131072, 0, 682341 / 262144],
    [-481 / 7864320, 0, 5291 / 524288, 0, -449735 / 1572864, 0, 1708993 / 524288, 0, -5126979 / 262144, 0, 275147873 / 3932160, 0, -125067215 / 786432, 0, 61846425 / 262144, 0, -119569755 / 524288, 0, 72679655 / 524288, 0, -25246617 / 524288, 0, 3825245 / 524288],
    [533 / 12582912, 0, -9061 / 1048576, 0, 1893749 / 6291456, 0, -13256243 / 3145728, 0, 130668681 / 4194304, 0, -217781135 / 1572864, 0, 415763985 / 1048576, 0, -397488645 / 524288, 0, 4107382665 / 4194304, 0, -885906065 / 1048576, 0, 979159335 / 2097152, 0, -156835045 / 1048576, 0, 88645895 / 4194304],
    [-255 / 8388608, 0, 62985 / 8388608, 0, -1322685 / 4194304, 0, 22309287 / 4194304, 0, -398380125 / 8388608, 0, 2151252675 / 8388608, 0, -1890494775 / 2097152, 0, 4508102925 / 2097152, 0, -29753479305 / 8388608, 0, 34031757375 / 8388608, 0, -13254473925 / 4194304, 0, 6713304975 / 4194304, 0, -3989065275 / 8388608, 0, 527784021 / 8388608]] : List (List ℚ))
private theorem polyEval_iBasisStep_1 (j : Fin 12) (y : ℝ) :
    polyEval (match j.1 with | 0 => iBasis_4_0 | 1 => iBasis_4_1 | 2 => iBasis_4_2 | 3 => iBasis_4_3 | 4 => iBasis_4_4 | 5 => iBasis_4_5 | 6 => iBasis_4_6 | 7 => iBasis_4_7 | 8 => iBasis_4_8 | 9 => iBasis_4_9 | 10 => iBasis_4_10 | 11 => iBasis_4_11 | _ => []) y =
      ApertureLogTwo.qeval (iBasisStepQ_1.getD j.1 []) y := by
  rcases j with ⟨jv, hjv⟩; interval_cases jv <;>
    (dsimp [iBasis_4_0, iBasis_4_1, iBasis_4_2, iBasis_4_3, iBasis_4_4, iBasis_4_5, iBasis_4_6, iBasis_4_7, iBasis_4_8, iBasis_4_9, iBasis_4_10, iBasis_4_11, iBasisStepQ_1, List.getD, polyEval, ApertureLogTwo.qeval]; norm_num; dsimp [polyEval]; ring)
private def mPPRawQ_1 : List (List ℚ) := ([[4 / 15, 8 / 21, 2 / 105, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [8 / 21, 20 / 63, -8 / 231, 2 / 693, 0, 0, 0, 0, 0, 0, 0, 0],
    [2 / 105, -8 / 231, 108 / 5005, -8 / 1155, 2 / 2145, 0, 0, 0, 0, 0, 0, 0],
    [0, 2 / 693, -8 / 1155, 52 / 8415, -8 / 3135, 2 / 4845, 0, 0, 0, 0, 0, 0],
    [0, 0, 2 / 2145, -8 / 3135, 68 / 25935, -8 / 6555, 2 / 9177, 0, 0, 0, 0, 0],
    [0, 0, 0, 2 / 4845, -8 / 6555, 252 / 185725, -8 / 11799, 2 / 15525, 0, 0, 0, 0],
    [0, 0, 0, 0, 2 / 9177, -8 / 11799, 100 / 126063, -8 / 19251, 2 / 24273, 0, 0, 0],
    [0, 0, 0, 0, 0, 2 / 15525, -8 / 19251, 116 / 230175, -8 / 29295, 2 / 35805, 0, 0],
    [0, 0, 0, 0, 0, 0, 2 / 24273, -8 / 29295, 396 / 1164205, -8 / 42315, 2 / 50505, 0],
    [0, 0, 0, 0, 0, 0, 0, 2 / 35805, -8 / 42315, 148 / 615615, -8 / 58695, 2 / 68757],
    [0, 0, 0, 0, 0, 0, 0, 0, 2 / 50505, -8 / 58695, 164 / 930735, -8 / 78819],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 2 / 68757, -8 / 78819, 540 / 4060189]] : List (List ℚ))
private theorem mPPRawQ_1_ok :
    (List.range 12).all (fun i => (List.range 12).all (fun j =>
      decide (qintSymm (ApertureLogTwo.qmul (iBasis0Q.getD i []) (iBasisStepQ_1.getD j [])) =
        ApertureLogTwo.matQ mPPRawQ_1 i j))) = true := by
  decide +kernel
private theorem int_pp_1 (i j : Fin 12) :
    (∫ y in (-1 : ℝ)..1,
      polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y *
        polyEval (match j.1 with | 0 => iBasis_4_0 | 1 => iBasis_4_1 | 2 => iBasis_4_2 | 3 => iBasis_4_3 | 4 => iBasis_4_4 | 5 => iBasis_4_5 | 6 => iBasis_4_6 | 7 => iBasis_4_7 | 8 => iBasis_4_8 | 9 => iBasis_4_9 | 10 => iBasis_4_10 | 11 => iBasis_4_11 | _ => []) y) =
      (ApertureLogTwo.matQ mPPRawQ_1 i.1 j.1 : ℝ) := by
  simp_rw [polyEval_iBasis_0 i, polyEval_iBasisStep_1 j, integral_qeval_mul_symm]
  have h1 := List.all_eq_true.mp mPPRawQ_1_ok i.1 (List.mem_range.mpr i.2)
  have h2 := List.all_eq_true.mp h1 j.1 (List.mem_range.mpr j.2)
  exact_mod_cast of_decide_eq_true h2
private def qOddMat_1 (i j : Fin 12) : ℝ := matAt ([([-7 / 7200, -1 / 720, -1 / 14400] : List ℝ),
    ([-1 / 720, -1 / 864, 1 / 7920, -1 / 95040] : List ℝ),
    ([-1 / 14400, 1 / 7920, -9 / 114400, 1 / 39600, -7 / 2059200] : List ℝ),
    ([0, -1 / 95040, 1 / 39600, -91 / 4039200, 7 / 752400, -7 / 4651200] : List ℝ),
    ([0, 0, -7 / 2059200, 7 / 752400, -17 / 1778400, 7 / 1573200, -1 / 1258560] : List ℝ),
    ([0, 0, 0, -7 / 4651200, 7 / 1573200, -147 / 29716000, 7 / 2831760, -7 / 14904000] : List ℝ),
    ([0, 0, 0, 0, -1 / 1258560, 7 / 2831760, -5 / 1728864, 7 / 4620240, -7 / 23302080] : List ℝ),
    ([0, 0, 0, 0, 0, -7 / 14904000, 7 / 4620240, -203 / 110484000, 1 / 1004400, -1 / 4910400] : List ℝ),
    ([0, 0, 0, 0, 0, 0, -7 / 23302080, 1 / 1004400, -33 / 26610400, 1 / 1450800, -1 / 6926400] : List ℝ),
    ([0, 0, 0, 0, 0, 0, 0, -1 / 4910400, 1 / 1450800, -37 / 42213600, 1 / 2012400, -7 / 66006720] : List ℝ),
    ([0, 0, 0, 0, 0, 0, 0, 0, -1 / 6926400, 1 / 2012400, -287 / 446752800, 7 / 18916560] : List ℝ),
    ([0, 0, 0, 0, 0, 0, 0, 0, 0, -7 / 66006720, 7 / 18916560, -9 / 18560864] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qOddMat_1_sym (i j : Fin 12) : qOddMat_1 i j = qOddMat_1 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qOddRowAbs_1 (i : Fin 12) : ℝ := coeffAt ([7 / 2880, 17 / 6336, 1 / 3300, 13 / 188100, 119 / 4326300, 49 / 3539700, 35 / 4389228, 29 / 5775300, 11 / 3264300, 37 / 15596100, 1877 / 1134993600, 509 / 529663680] : List ℝ) i.1
private theorem qOddRowAbs_1_eq (i : Fin 12) :
    (∑ j : Fin 12, |qOddMat_1 i j|) = qOddRowAbs_1 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qOddMat_1, qOddRowAbs_1, matAt, listAt, coeffAt]; norm_num)
private def gHiQ_1 : List (List ℚ) := ([[0, 0],
    [0, 0],
    [0, 0],
    [0, 0],
    [0, 0],
    [0, 0],
    [0, 0],
    [0, 0],
    [0, 0],
    [0, 0],
    [2 / 4456305, 0],
    [-8 / 5050479, 2 / 6225009]] : List (List ℚ))
private def gHi_1 (i : Fin 12) (r : ℕ) : ℝ := matAt ([([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([2 / 4456305] : List ℝ),
    ([-8 / 5050479, 2 / 6225009] : List ℝ)] : List (List ℝ)) i.1 r
private theorem gHiQ_1_ok :
    (List.range 12).all (fun i => (List.range 2).all (fun r =>
      decide (qintSymm (ApertureLogTwo.qmul (iBasisStepQ_1.getD i [])
        (ApertureLogTwo.qleg (24 + 2 * r))) =
        ApertureLogTwo.matQ gHiQ_1 i r))) = true := by
  decide +kernel
private theorem gHi_eq_1 (i : Fin 12) (r : ℕ) (hr : r ∈ Finset.range 2) :
    regionalLegendreMoment
      (polyEval (match i.1 with | 0 => iBasis_4_0 | 1 => iBasis_4_1 | 2 => iBasis_4_2 | 3 => iBasis_4_3 | 4 => iBasis_4_4 | 5 => iBasis_4_5 | 6 => iBasis_4_6 | 7 => iBasis_4_7 | 8 => iBasis_4_8 | 9 => iBasis_4_9 | 10 => iBasis_4_10 | 11 => iBasis_4_11 | _ => [])) (24 + 2 * r) =
      gHi_1 i r := by
  unfold regionalLegendreMoment
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  simp_rw [polyEval_iBasisStep_1 i, ApertureLogTwo.legP_eq_qeval_qleg, integral_qeval_mul_symm]
  rw [Finset.mem_range] at hr
  have h1 := List.all_eq_true.mp gHiQ_1_ok i.1 (List.mem_range.mpr i.2)
  have h2 := List.all_eq_true.mp h1 r (List.mem_range.mpr hr)
  have h3 : (qintSymm (ApertureLogTwo.qmul (iBasisStepQ_1.getD i.1 [])
      (ApertureLogTwo.qleg (24 + 2 * r))) : ℝ) =
      (ApertureLogTwo.matQ gHiQ_1 i.1 r : ℝ) := by
    exact_mod_cast of_decide_eq_true h2
  have h4 : (ApertureLogTwo.matQ gHiQ_1 i.1 r : ℝ) = gHi_1 i r := by
    rcases i with ⟨iv, hiv⟩; interval_cases iv <;> interval_cases r <;>
      norm_num [gHiQ_1, gHi_1, ApertureLogTwo.matQ, matAt, listAt, coeffAt]
  exact h3.trans h4

private def iBasisStepQ_2 : List (List ℚ) := ([[1 / 720, 1 / 120, 1 / 48, 1 / 36, 1 / 48, 1 / 120, 1 / 720],
    [5 / 1152, 1 / 42, 5 / 96, 1 / 18, 5 / 192, 0, -1 / 288, 0, 1 / 2688],
    [3 / 1280, 1 / 105, 3 / 256, 0, -1 / 128, 0, 3 / 640, 0, -3 / 1792, 0, 1 / 3840],
    [13 / 46080, 0, -13 / 7680, 0, 13 / 3072, 0, -13 / 2304, 0, 13 / 3072, 0, -13 / 7680, 0, 13 / 46080],
    [-17 / 645120, 0, 17 / 30720, 0, -17 / 6144, 0, 119 / 18432, 0, -17 / 2048, 0, 187 / 30720, 0, -221 / 92160, 0, 17 / 43008],
    [1 / 163840, 0, -1 / 4096, 0, 49 / 24576, 0, -147 / 20480, 0, 231 / 16384, 0, -1001 / 61440, 0, 91 / 8192, 0, -17 / 4096, 0, 323 / 491520],
    [-25 / 12386304, 0, 25 / 196608, 0, -25 / 16384, 0, 385 / 49152, 0, -715 / 32768, 0, 3575 / 98304, 0, -5525 / 147456, 0, 8075 / 344064, 0, -1615 / 196608, 0, 2185 / 1769472],
    [29 / 35389440, 0, -29 / 393216, 0, 319 / 262144, 0, -4147 / 491520, 0, 4147 / 131072, 0, -70499 / 983040, 0, 121771 / 1179648, 0, -9367 / 98304, 0, 215441 / 3932160, 0, -63365 / 3538944, 0, 667 / 262144],
    [-1 / 2621440, 0, 121 / 2621440, 0, -1573 / 1572864, 0, 4719 / 524288, 0, -80223 / 1835008, 0, 508079 / 3932160, 0, -323323 / 1310720, 0, 81719 / 262144, 0, -408595 / 1572864, 0, 72105 / 524288, 0, -22011 / 524288, 0, 20677 / 3670016],
    [37 / 188743680, 0, -481 / 15728640, 0, 5291 / 6291456, 0, -89947 / 9437184, 0, 1708993 / 29360128, 0, -1708993 / 7864320, 0, 25013443 / 47185920, 0, -1374365 / 1572864, 0, 4123095 / 4194304, 0, -2344505 / 3145728, 0, 765049 / 2097152, 0, -765049 / 7340032, 0, 166315 / 12582912],
    [-41 / 377487360, 0, 533 / 25165824, 0, -9061 / 12582912, 0, 1893749 / 188743680, 0, -1893749 / 25165824, 0, 43556227 / 125829120, 0, -19798285 / 18874368, 0, 4568835 / 2097152, 0, -26499243 / 8388608, 0, 80536915 / 25165824, 0, -9325327 / 4194304, 0, 4238785 / 4194304, 0, -6818915 / 25165824, 0, 1363783 / 41943040],
    [15 / 234881024, 0, -255 / 16777216, 0, 20995 / 33554432, 0, -88179 / 8388608, 0, 3187041 / 33554432, 0, -26558675 / 50331648, 0, 65189475 / 33554432, 0, -145422675 / 29360128, 0, 300540195 / 33554432, 0, -194467185 / 16777216, 0, 358229025 / 33554432, 0, -57378675 / 8388608, 0, 97294275 / 33554432, 0, -12274047 / 16777216, 0, 58642669 / 704643072]] : List (List ℚ))
private theorem polyEval_iBasisStep_2 (j : Fin 12) (y : ℝ) :
    polyEval (match j.1 with | 0 => iBasis_6_0 | 1 => iBasis_6_1 | 2 => iBasis_6_2 | 3 => iBasis_6_3 | 4 => iBasis_6_4 | 5 => iBasis_6_5 | 6 => iBasis_6_6 | 7 => iBasis_6_7 | 8 => iBasis_6_8 | 9 => iBasis_6_9 | 10 => iBasis_6_10 | 11 => iBasis_6_11 | _ => []) y =
      ApertureLogTwo.qeval (iBasisStepQ_2.getD j.1 []) y := by
  rcases j with ⟨jv, hjv⟩; interval_cases jv <;>
    (dsimp [iBasis_6_0, iBasis_6_1, iBasis_6_2, iBasis_6_3, iBasis_6_4, iBasis_6_5, iBasis_6_6, iBasis_6_7, iBasis_6_8, iBasis_6_9, iBasis_6_10, iBasis_6_11, iBasisStepQ_2, List.getD, polyEval, ApertureLogTwo.qeval]; norm_num; dsimp [polyEval]; ring)
private def mPPRawQ_2 : List (List ℚ) := ([[8 / 315, 10 / 189, 4 / 385, 2 / 10395, 0, 0, 0, 0, 0, 0, 0, 0],
    [10 / 189, 200 / 2079, 10 / 1001, -4 / 10395, 2 / 135135, 0, 0, 0, 0, 0, 0, 0],
    [4 / 385, 10 / 1001, -8 / 5005, 2 / 6545, -4 / 95095, 2 / 692835, 0, 0, 0, 0, 0, 0],
    [2 / 10395, -4 / 10395, 2 / 6545, -104 / 671517, 2 / 39501, -4 / 408595, 2 / 2340135, 0, 0, 0, 0, 0],
    [0, 2 / 135135, -4 / 95095, 2 / 39501, -136 / 3936933, 2 / 142025, -4 / 1238895, 2 / 6194475, 0, 0, 0, 0],
    [0, 0, 2 / 692835, -4 / 408595, 2 / 142025, -56 / 5014575, 10 / 1938969, -4 / 3048075, 2 / 13956975, 0, 0, 0],
    [0, 0, 0, 2 / 2340135, -4 / 1238895, 10 / 1938969, -1000 / 222753321, 10 / 4446981, -4 / 6513255, 2 / 28035315, 0, 0],
    [0, 0, 0, 0, 2 / 6194475, -4 / 3048075, 10 / 4446981, -232 / 111174525, 2 / 1806525, -4 / 12567555, 2 / 51666615, 0],
    [0, 0, 0, 0, 0, 2 / 13956975, -4 / 6513255, 2 / 1806525, -88 / 81727191, 2 / 3354169, -4 / 22441055, 2 / 89040315],
    [0, 0, 0, 0, 0, 0, 2 / 28035315, -4 / 12567555, 2 / 3354169, -296 / 492368877, 2 / 5810805, -4 / 37701755],
    [0, 0, 0, 0, 0, 0, 0, 2 / 51666615, -4 / 22441055, 2 / 5810805, -328 / 918635445, 10 / 47632949],
    [0, 0, 0, 0, 0, 0, 0, 0, 2 / 89040315, -4 / 37701755, 10 / 47632949, -200 / 897301769]] : List (List ℚ))
private theorem mPPRawQ_2_ok :
    (List.range 12).all (fun i => (List.range 12).all (fun j =>
      decide (qintSymm (ApertureLogTwo.qmul (iBasis0Q.getD i []) (iBasisStepQ_2.getD j [])) =
        ApertureLogTwo.matQ mPPRawQ_2 i j))) = true := by
  decide +kernel
private theorem int_pp_2 (i j : Fin 12) :
    (∫ y in (-1 : ℝ)..1,
      polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y *
        polyEval (match j.1 with | 0 => iBasis_6_0 | 1 => iBasis_6_1 | 2 => iBasis_6_2 | 3 => iBasis_6_3 | 4 => iBasis_6_4 | 5 => iBasis_6_5 | 6 => iBasis_6_6 | 7 => iBasis_6_7 | 8 => iBasis_6_8 | 9 => iBasis_6_9 | 10 => iBasis_6_10 | 11 => iBasis_6_11 | _ => []) y) =
      (ApertureLogTwo.matQ mPPRawQ_2 i.1 j.1 : ℝ) := by
  simp_rw [polyEval_iBasis_0 i, polyEval_iBasisStep_2 j, integral_qeval_mul_symm]
  have h1 := List.all_eq_true.mp mPPRawQ_2_ok i.1 (List.mem_range.mpr i.2)
  have h2 := List.all_eq_true.mp h1 j.1 (List.mem_range.mpr j.2)
  exact_mod_cast of_decide_eq_true h2
private def qOddMat_2 (i j : Fin 12) : ℝ := matAt ([([31 / 635040, 155 / 1524096, 31 / 1552320, 31 / 83825280] : List ℝ),
    ([155 / 1524096, 775 / 4191264, 155 / 8072064, -31 / 41912640, 31 / 1089728640] : List ℝ),
    ([31 / 1552320, 155 / 8072064, -31 / 10090080, 31 / 52778880, -31 / 383423040, 31 / 5587021440] : List ℝ),
    ([31 / 83825280, -31 / 41912640, 31 / 52778880, -403 / 1353778272, 31 / 318536064, -31 / 1647455040, 31 / 18870848640] : List ℝ),
    ([0, 31 / 1089728640, -31 / 383423040, 31 / 318536064, -527 / 7936856928, 31 / 1145289600, -31 / 4995224640, 31 / 49952246400] : List ℝ),
    ([0, 0, 31 / 5587021440, -31 / 1647455040, 31 / 1145289600, -31 / 1444197600, 155 / 15635846016, -1 / 396446400, 1 / 3630614400] : List ℝ),
    ([0, 0, 0, 31 / 18870848640, -31 / 4995224640, 155 / 15635846016, -125 / 14486151456, 5 / 1156788864, -1 / 847143360, 1 / 7292799360] : List ℝ),
    ([0, 0, 0, 0, 31 / 49952246400, -1 / 396446400, 5 / 1156788864, -29 / 7229930400, 1 / 469929600, -1 / 1634592960, 1 / 13439986560] : List ℝ),
    ([0, 0, 0, 0, 0, 1 / 3630614400, -1 / 847143360, 1 / 469929600, -11 / 5314903776, 1 / 872516736, -1 / 2918784960, 31 / 718021100160] : List ℝ),
    ([0, 0, 0, 0, 0, 0, 1 / 7292799360, -1 / 1634592960, 1 / 872516736, -37 / 32019859872, 31 / 46858331520, -31 / 152013476160] : List ℝ),
    ([0, 0, 0, 0, 0, 0, 0, 1 / 13439986560, -1 / 2918784960, 31 / 46858331520, -1271 / 1851969057120, 155 / 384112100736] : List ℝ),
    ([0, 0, 0, 0, 0, 0, 0, 0, 31 / 718021100160, -31 / 152013476160, 155 / 384112100736, -775 / 1808960366304] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qOddMat_2_sym (i j : Fin 12) : qOddMat_2 i j = qOddMat_2 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qOddRowAbs_2 (i : Fin 12) : ℝ := coeffAt ([31 / 181440, 25699 / 83825280, 31 / 722304, 403 / 190789830, 527 / 1717108470, 1 / 11681010, 1 / 31220154, 29 / 2029310010, 11 / 1530882990, 96437 / 24626183137920, 1013 / 467163365760, 58559 / 54268810989120] : List ℝ) i.1
private theorem qOddRowAbs_2_eq (i : Fin 12) :
    (∑ j : Fin 12, |qOddMat_2 i j|) = qOddRowAbs_2 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qOddMat_2, qOddRowAbs_2, matAt, listAt, coeffAt]; norm_num)
private def gHiQ_2 : List (List ℚ) := ([[0, 0, 0],
    [0, 0, 0],
    [0, 0, 0],
    [0, 0, 0],
    [0, 0, 0],
    [0, 0, 0],
    [0, 0, 0],
    [0, 0, 0],
    [0, 0, 0],
    [2 / 7125631695, 0, 0],
    [-4 / 2954530215, 2 / 12045392415, 0],
    [10 / 3658230289, -4 / 4907382095, 2 / 19515403215]] : List (List ℚ))
private def gHi_2 (i : Fin 12) (r : ℕ) : ℝ := matAt ([([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([2 / 7125631695] : List ℝ),
    ([-4 / 2954530215, 2 / 12045392415] : List ℝ),
    ([10 / 3658230289, -4 / 4907382095, 2 / 19515403215] : List ℝ)] : List (List ℝ)) i.1 r
private theorem gHiQ_2_ok :
    (List.range 12).all (fun i => (List.range 3).all (fun r =>
      decide (qintSymm (ApertureLogTwo.qmul (iBasisStepQ_2.getD i [])
        (ApertureLogTwo.qleg (24 + 2 * r))) =
        ApertureLogTwo.matQ gHiQ_2 i r))) = true := by
  decide +kernel
private theorem gHi_eq_2 (i : Fin 12) (r : ℕ) (hr : r ∈ Finset.range 3) :
    regionalLegendreMoment
      (polyEval (match i.1 with | 0 => iBasis_6_0 | 1 => iBasis_6_1 | 2 => iBasis_6_2 | 3 => iBasis_6_3 | 4 => iBasis_6_4 | 5 => iBasis_6_5 | 6 => iBasis_6_6 | 7 => iBasis_6_7 | 8 => iBasis_6_8 | 9 => iBasis_6_9 | 10 => iBasis_6_10 | 11 => iBasis_6_11 | _ => [])) (24 + 2 * r) =
      gHi_2 i r := by
  unfold regionalLegendreMoment
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  simp_rw [polyEval_iBasisStep_2 i, ApertureLogTwo.legP_eq_qeval_qleg, integral_qeval_mul_symm]
  rw [Finset.mem_range] at hr
  have h1 := List.all_eq_true.mp gHiQ_2_ok i.1 (List.mem_range.mpr i.2)
  have h2 := List.all_eq_true.mp h1 r (List.mem_range.mpr hr)
  have h3 : (qintSymm (ApertureLogTwo.qmul (iBasisStepQ_2.getD i.1 [])
      (ApertureLogTwo.qleg (24 + 2 * r))) : ℝ) =
      (ApertureLogTwo.matQ gHiQ_2 i.1 r : ℝ) := by
    exact_mod_cast of_decide_eq_true h2
  have h4 : (ApertureLogTwo.matQ gHiQ_2 i.1 r : ℝ) = gHi_2 i r := by
    rcases i with ⟨iv, hiv⟩; interval_cases iv <;> interval_cases r <;>
      norm_num [gHiQ_2, gHi_2, ApertureLogTwo.matQ, matAt, listAt, coeffAt]
  exact h3.trans h4

private def iBasisStepQ_3 : List (List ℚ) := ([[1 / 40320, 1 / 5040, 1 / 1440, 1 / 720, 1 / 576, 1 / 720, 1 / 1440, 1 / 5040, 1 / 40320],
    [1 / 11520, 1 / 1512, 5 / 2304, 1 / 252, 5 / 1152, 1 / 360, 1 / 1152, 0, -1 / 16128, 0, 1 / 241920],
    [1 / 15360, 1 / 2310, 3 / 2560, 1 / 630, 1 / 1024, 0, -1 / 3840, 0, 3 / 35840, 0, -1 / 53760, 0, 1 / 506880],
    [13 / 645120, 1 / 10395, 13 / 92160, 0, -13 / 92160, 0, 13 / 92160, 0, -13 / 129024, 0, 13 / 276480, 0, -13 / 1013760, 0, 1 / 645120],
    [17 / 10321920, 0, -17 / 1290240, 0, 17 / 368640, 0, -17 / 184320, 0, 17 / 147456, 0, -17 / 184320, 0, 17 / 368640, 0, -17 / 1290240, 0, 17 / 10321920],
    [-1 / 8847360, 0, 1 / 327680, 0, -1 / 49152, 0, 49 / 737280, 0, -21 / 163840, 0, 77 / 491520, 0, -91 / 737280, 0, 1 / 16384, 0, -17 / 983040, 0, 19 / 8847360],
    [1 / 49545216, 0, -25 / 24772608, 0, 25 / 2359296, 0, -5 / 98304, 0, 55 / 393216, 0, -143 / 589824, 0, 325 / 1179648, 0, -425 / 2064384, 0, 1615 / 16515072, 0, -95 / 3538944, 0, 23 / 7077888],
    [-29 / 5449973760, 0, 29 / 70778880, 0, -29 / 4718592, 0, 319 / 7864320, 0, -4147 / 27525120, 0, 4147 / 11796480, 0, -6409 / 11796480, 0, 9367 / 16515072, 0, -9367 / 23592960, 0, 12673 / 70778880, 0, -667 / 14155776, 0, 667 / 121110528],
    [1 / 566231040, 0, -1 / 5242880, 0, 121 / 31457280, 0, -1573 / 47185920, 0, 4719 / 29360128, 0, -26741 / 55050240, 0, 46189 / 47185920, 0, -3553 / 2621440, 0, 81719 / 62914560, 0, -24035 / 28311552, 0, 759 / 2097152, 0, -667 / 7340032, 0, 899 / 88080384],
    [-37 / 53980692480, 0, 37 / 377487360, 0, -481 / 188743680, 0, 5291 / 188743680, 0, -89947 / 528482304, 0, 1708993 / 2642411520, 0, -155363 / 94371840, 0, 274873 / 94371840, 0, -274873 / 75497472, 0, 80845 / 25165824, 0, -24679 / 12582912, 0, 765049 / 968884224, 0, -33263 / 176160768, 0, 33263 / 1635778560],
    [41 / 137405399040, 0, -41 / 754974720, 0, 533 / 301989888, 0, -9061 / 377487360, 0, 1893749 / 10569646080, 0, -1893749 / 2264924160, 0, 3959657 / 1509949440, 0, -1522945 / 264241152, 0, 304589 / 33554432, 0, -519593 / 50331648, 0, 847757 / 100663296, 0, -847757 / 176160768, 0, 184295 / 100663296, 0, -1363783 / 3271557120, 0, 1363783 / 31708938240],
    [-1 / 7046430720, 0, 15 / 469762048, 0, -85 / 67108864, 0, 4199 / 201326592, 0, -12597 / 67108864, 0, 1062347 / 1006632960, 0, -2414425 / 603979776, 0, 5014575 / 469762048, 0, -9694845 / 469762048, 0, 1964315 / 67108864, 0, -2047023 / 67108864, 0, 1550775 / 67108864, 0, -831575 / 67108864, 0, 299367 / 67108864, 0, -1363783 / 1409286144, 0, 2022161 / 21139292160]] : List (List ℚ))
private theorem polyEval_iBasisStep_3 (j : Fin 12) (y : ℝ) :
    polyEval (match j.1 with | 0 => iBasis_8_0 | 1 => iBasis_8_1 | 2 => iBasis_8_2 | 3 => iBasis_8_3 | 4 => iBasis_8_4 | 5 => iBasis_8_5 | 6 => iBasis_8_6 | 7 => iBasis_8_7 | 8 => iBasis_8_8 | 9 => iBasis_8_9 | 10 => iBasis_8_10 | 11 => iBasis_8_11 | _ => []) y =
      ApertureLogTwo.qeval (iBasisStepQ_3.getD j.1 []) y := by
  rcases j with ⟨jv, hjv⟩; interval_cases jv <;>
    (dsimp [iBasis_8_0, iBasis_8_1, iBasis_8_2, iBasis_8_3, iBasis_8_4, iBasis_8_5, iBasis_8_6, iBasis_8_7, iBasis_8_8, iBasis_8_9, iBasis_8_10, iBasis_8_11, iBasisStepQ_3, List.getD, polyEval, ApertureLogTwo.qeval]; norm_num; dsimp [polyEval]; ring)
private def mPPRawQ_3 : List (List ℚ) := ([[4 / 2835, 16 / 4455, 8 / 6435, 16 / 155925, 2 / 2027025, 0, 0, 0, 0, 0, 0, 0],
    [16 / 4455, 100 / 11583, 16 / 6435, 8 / 75735, -16 / 7702695, 2 / 43648605, 0, 0, 0, 0, 0, 0],
    [8 / 6435, 16 / 6435, 4 / 12155, -16 / 799425, 8 / 4279275, -16 / 111546435, 2 / 334639305, 0, 0, 0, 0, 0],
    [16 / 155925, 8 / 75735, -16 / 799425, 52 / 10072755, -16 / 13627845, 56 / 275801625, -16 / 695020095, 2 / 1579591125, 0, 0, 0, 0],
    [2 / 2027025, -16 / 7702695, 8 / 4279275, -16 / 13627845, 68 / 126544275, -112 / 632721375, 8 / 200170035, -16 / 2880430875, 2 / 5568833025, 0, 0, 0],
    [0, 2 / 43648605, -16 / 111546435, 56 / 275801625, -112 / 632721375, 196 / 1890494775, -112 / 2704861755, 56 / 5129910225, -16 / 9281388375, 2 / 16120306125, 0, 0],
    [0, 0, 2 / 334639305, -16 / 695020095, 8 / 200170035, -112 / 2704861755, 500 / 17852087583, -16 / 1267389585, 8 / 2168913915, -16 / 25147677555, 2 / 40454959545, 0],
    [0, 0, 0, 2 / 1579591125, -16 / 2880430875, 56 / 5129910225, -16 / 1267389585, 116 / 12340372275, -16 / 3472399125, 8 / 5520747375, -16 / 59984940015, 2 / 91088242245],
    [0, 0, 0, 0, 2 / 5568833025, -16 / 9281388375, 8 / 2168913915, -16 / 3472399125, 44 / 11967195825, -16 / 8344693305, 8 / 12550961475, -16 / 129731738955],
    [0, 0, 0, 0, 0, 2 / 16120306125, -16 / 25147677555, 8 / 5520747375, -16 / 8344693305, 148 / 91791626355, -16 / 18142163325, 8 / 26127316215],
    [0, 0, 0, 0, 0, 0, 2 / 40454959545, -16 / 59984940015, 8 / 12550961475, -16 / 18142163325, 164 / 212204787795, -16 / 36439205985],
    [0, 0, 0, 0, 0, 0, 0, 2 / 91088242245, -16 / 129731738955, 8 / 26127316215, -16 / 36439205985, 100 / 251372681287]] : List (List ℚ))
private theorem mPPRawQ_3_ok :
    (List.range 12).all (fun i => (List.range 12).all (fun j =>
      decide (qintSymm (ApertureLogTwo.qmul (iBasis0Q.getD i []) (iBasisStepQ_3.getD j [])) =
        ApertureLogTwo.matQ mPPRawQ_3 i j))) = true := by
  decide +kernel
private theorem int_pp_3 (i j : Fin 12) :
    (∫ y in (-1 : ℝ)..1,
      polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y *
        polyEval (match j.1 with | 0 => iBasis_8_0 | 1 => iBasis_8_1 | 2 => iBasis_8_2 | 3 => iBasis_8_3 | 4 => iBasis_8_4 | 5 => iBasis_8_5 | 6 => iBasis_8_6 | 7 => iBasis_8_7 | 8 => iBasis_8_8 | 9 => iBasis_8_9 | 10 => iBasis_8_10 | 11 => iBasis_8_11 | _ => []) y) =
      (ApertureLogTwo.matQ mPPRawQ_3 i.1 j.1 : ℝ) := by
  simp_rw [polyEval_iBasis_0 i, polyEval_iBasisStep_3 j, integral_qeval_mul_symm]
  have h1 := List.all_eq_true.mp mPPRawQ_3_ok i.1 (List.mem_range.mpr i.2)
  have h2 := List.all_eq_true.mp h1 j.1 (List.mem_range.mpr j.2)
  exact_mod_cast of_decide_eq_true h2
private def qOddMat_3 (i j : Fin 12) : ℝ := matAt ([([-127 / 43545600, -127 / 17107200, -127 / 49420800, -127 / 598752000, -127 / 62270208000] : List ℝ),
    ([-127 / 17107200, -635 / 35582976, -127 / 24710400, -127 / 581644800, 127 / 29578348800, -127 / 1340885145600] : List ℝ),
    ([-127 / 49420800, -127 / 24710400, -127 / 186700800, 127 / 3069792000, -127 / 32864832000, 127 / 428338310400, -127 / 10280119449600] : List ℝ),
    ([-127 / 598752000, -127 / 581644800, 127 / 3069792000, -1651 / 154717516800, 127 / 52330924800, -889 / 2118156480000, 127 / 2668877164800, -127 / 48525039360000] : List ℝ),
    ([-127 / 62270208000, 127 / 29578348800, -127 / 32864832000, 127 / 52330924800, -2159 / 1943720064000, 889 / 2429650080000, -127 / 1537305868800, 127 / 11060854560000, -127 / 171074550528000] : List ℝ),
    ([0, -127 / 1340885145600, 127 / 428338310400, -889 / 2118156480000, 889 / 2429650080000, -6223 / 29037999744000, 889 / 10386669139200, -889 / 39397710528000, 127 / 35640531360000, -127 / 495215804160000] : List ℝ),
    ([0, 0, -127 / 10280119449600, 127 / 2668877164800, -127 / 1537305868800, 889 / 10386669139200, -3175 / 54841613054976, 127 / 4866776006400, -127 / 16657258867200, 127 / 96567081811200, -127 / 1242776357222400] : List ℝ),
    ([0, 0, 0, -127 / 48525039360000, 127 / 11060854560000, -889 / 39397710528000, 127 / 4866776006400, -3683 / 189548118144000, 127 / 13334012640000, -127 / 42399339840000, 127 / 230342169657600, -127 / 2798230801766400] : List ℝ),
    ([0, 0, 0, 0, -127 / 171074550528000, 127 / 35640531360000, -127 / 16657258867200, 127 / 13334012640000, -1397 / 183816127872000, 127 / 32043622291200, -127 / 96391384128000, 127 / 498169877587200] : List ℝ),
    ([0, 0, 0, 0, 0, -127 / 495215804160000, 127 / 96567081811200, -127 / 42399339840000, 127 / 32043622291200, -4699 / 1409919380812800, 127 / 69665907168000, -127 / 200657788531200] : List ℝ),
    ([0, 0, 0, 0, 0, 0, -127 / 1242776357222400, 127 / 230342169657600, -127 / 96391384128000, 127 / 69665907168000, -5207 / 3259465540531200, 127 / 139926550982400] : List ℝ),
    ([0, 0, 0, 0, 0, 0, 0, -127 / 2798230801766400, 127 / 498169877587200, -127 / 200657788531200, 127 / 139926550982400, -635 / 772216876913664] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qOddMat_3_sym (i j : Fin 12) : qOddMat_3 i j = qOddMat_3 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qOddRowAbs_3 (i : Fin 12) : ℝ := coeffAt ([127 / 9676800, 7248271 / 236626790400, 25504013 / 3023564544000, 3048127 / 6279710976000, 2159 / 152086750200, 127 / 84492639000, 127 / 395425550520, 3683 / 38643860619000, 301213139 / 8708009460224256000, 100567871 / 7023387430934784000, 29510101 / 4684740926890752000, 5427599 / 2038026433259980800] : List ℝ) i.1
private theorem qOddRowAbs_3_eq (i : Fin 12) :
    (∑ j : Fin 12, |qOddMat_3 i j|) = qOddRowAbs_3 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qOddMat_3, qOddRowAbs_3, matAt, listAt, coeffAt]; norm_num)
private def gHiQ_3 : List (List ℚ) := ([[0, 0, 0, 0],
    [0, 0, 0, 0],
    [0, 0, 0, 0],
    [0, 0, 0, 0],
    [0, 0, 0, 0],
    [0, 0, 0, 0],
    [0, 0, 0, 0],
    [0, 0, 0, 0],
    [2 / 9227693045025, 0, 0, 0],
    [-16 / 12719252575575, 2 / 19260582471585, 0, 0],
    [8 / 2483071607835, -16 / 25837366730175, 2 / 37762305221025, 0],
    [-16 / 3362958844245, 8 / 4915093695435, -16 / 49510577956455, 2 / 70235936170785]] : List (List ℚ))
private def gHi_3 (i : Fin 12) (r : ℕ) : ℝ := matAt ([([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([2 / 9227693045025] : List ℝ),
    ([-16 / 12719252575575, 2 / 19260582471585] : List ℝ),
    ([8 / 2483071607835, -16 / 25837366730175, 2 / 37762305221025] : List ℝ),
    ([-16 / 3362958844245, 8 / 4915093695435, -16 / 49510577956455, 2 / 70235936170785] : List ℝ)] : List (List ℝ)) i.1 r
private theorem gHiQ_3_ok :
    (List.range 12).all (fun i => (List.range 4).all (fun r =>
      decide (qintSymm (ApertureLogTwo.qmul (iBasisStepQ_3.getD i [])
        (ApertureLogTwo.qleg (24 + 2 * r))) =
        ApertureLogTwo.matQ gHiQ_3 i r))) = true := by
  decide +kernel
private theorem gHi_eq_3 (i : Fin 12) (r : ℕ) (hr : r ∈ Finset.range 4) :
    regionalLegendreMoment
      (polyEval (match i.1 with | 0 => iBasis_8_0 | 1 => iBasis_8_1 | 2 => iBasis_8_2 | 3 => iBasis_8_3 | 4 => iBasis_8_4 | 5 => iBasis_8_5 | 6 => iBasis_8_6 | 7 => iBasis_8_7 | 8 => iBasis_8_8 | 9 => iBasis_8_9 | 10 => iBasis_8_10 | 11 => iBasis_8_11 | _ => [])) (24 + 2 * r) =
      gHi_3 i r := by
  unfold regionalLegendreMoment
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  simp_rw [polyEval_iBasisStep_3 i, ApertureLogTwo.legP_eq_qeval_qleg, integral_qeval_mul_symm]
  rw [Finset.mem_range] at hr
  have h1 := List.all_eq_true.mp gHiQ_3_ok i.1 (List.mem_range.mpr i.2)
  have h2 := List.all_eq_true.mp h1 r (List.mem_range.mpr hr)
  have h3 : (qintSymm (ApertureLogTwo.qmul (iBasisStepQ_3.getD i.1 [])
      (ApertureLogTwo.qleg (24 + 2 * r))) : ℝ) =
      (ApertureLogTwo.matQ gHiQ_3 i.1 r : ℝ) := by
    exact_mod_cast of_decide_eq_true h2
  have h4 : (ApertureLogTwo.matQ gHiQ_3 i.1 r : ℝ) = gHi_3 i r := by
    rcases i with ⟨iv, hiv⟩; interval_cases iv <;> interval_cases r <;>
      norm_num [gHiQ_3, gHi_3, ApertureLogTwo.matQ, matAt, listAt, coeffAt]
  exact h3.trans h4

private theorem regLogEig_0 : regionalLogEigenvalue 0 = (0 : ℝ) := by
  exact regionalLogEigenvalue_zero
private theorem regLogEig_1 : regionalLogEigenvalue 1 = (2 : ℝ) := by
  rw [regionalLogEigenvalue_succ 0, regLogEig_0]; norm_num
private theorem regLogEig_2 : regionalLogEigenvalue 2 = (3 : ℝ) := by
  rw [regionalLogEigenvalue_succ 1, regLogEig_1]; norm_num
private theorem regLogEig_3 : regionalLogEigenvalue 3 = (11 / 3 : ℝ) := by
  rw [regionalLogEigenvalue_succ 2, regLogEig_2]; norm_num
private theorem regLogEig_4 : regionalLogEigenvalue 4 = (25 / 6 : ℝ) := by
  rw [regionalLogEigenvalue_succ 3, regLogEig_3]; norm_num
private theorem regLogEig_5 : regionalLogEigenvalue 5 = (137 / 30 : ℝ) := by
  rw [regionalLogEigenvalue_succ 4, regLogEig_4]; norm_num
private theorem regLogEig_6 : regionalLogEigenvalue 6 = (49 / 10 : ℝ) := by
  rw [regionalLogEigenvalue_succ 5, regLogEig_5]; norm_num
private theorem regLogEig_7 : regionalLogEigenvalue 7 = (363 / 70 : ℝ) := by
  rw [regionalLogEigenvalue_succ 6, regLogEig_6]; norm_num
private theorem regLogEig_8 : regionalLogEigenvalue 8 = (761 / 140 : ℝ) := by
  rw [regionalLogEigenvalue_succ 7, regLogEig_7]; norm_num
private theorem regLogEig_9 : regionalLogEigenvalue 9 = (7129 / 1260 : ℝ) := by
  rw [regionalLogEigenvalue_succ 8, regLogEig_8]; norm_num
private theorem regLogEig_10 : regionalLogEigenvalue 10 = (7381 / 1260 : ℝ) := by
  rw [regionalLogEigenvalue_succ 9, regLogEig_9]; norm_num
private theorem regLogEig_11 : regionalLogEigenvalue 11 = (83711 / 13860 : ℝ) := by
  rw [regionalLogEigenvalue_succ 10, regLogEig_10]; norm_num
private theorem regLogEig_12 : regionalLogEigenvalue 12 = (86021 / 13860 : ℝ) := by
  rw [regionalLogEigenvalue_succ 11, regLogEig_11]; norm_num
private theorem regLogEig_13 : regionalLogEigenvalue 13 = (1145993 / 180180 : ℝ) := by
  rw [regionalLogEigenvalue_succ 12, regLogEig_12]; norm_num
private theorem regLogEig_14 : regionalLogEigenvalue 14 = (1171733 / 180180 : ℝ) := by
  rw [regionalLogEigenvalue_succ 13, regLogEig_13]; norm_num
private theorem regLogEig_15 : regionalLogEigenvalue 15 = (1195757 / 180180 : ℝ) := by
  rw [regionalLogEigenvalue_succ 14, regLogEig_14]; norm_num
private theorem regLogEig_16 : regionalLogEigenvalue 16 = (2436559 / 360360 : ℝ) := by
  rw [regionalLogEigenvalue_succ 15, regLogEig_15]; norm_num
private theorem regLogEig_17 : regionalLogEigenvalue 17 = (42142223 / 6126120 : ℝ) := by
  rw [regionalLogEigenvalue_succ 16, regLogEig_16]; norm_num
private theorem regLogEig_18 : regionalLogEigenvalue 18 = (14274301 / 2042040 : ℝ) := by
  rw [regionalLogEigenvalue_succ 17, regLogEig_17]; norm_num
private theorem regLogEig_19 : regionalLogEigenvalue 19 = (275295799 / 38798760 : ℝ) := by
  rw [regionalLogEigenvalue_succ 18, regLogEig_18]; norm_num
private theorem regLogEig_20 : regionalLogEigenvalue 20 = (55835135 / 7759752 : ℝ) := by
  rw [regionalLogEigenvalue_succ 19, regLogEig_19]; norm_num
private theorem regLogEig_21 : regionalLogEigenvalue 21 = (18858053 / 2586584 : ℝ) := by
  rw [regionalLogEigenvalue_succ 20, regLogEig_20]; norm_num
private theorem regLogEig_22 : regionalLogEigenvalue 22 = (19093197 / 2586584 : ℝ) := by
  rw [regionalLogEigenvalue_succ 21, regLogEig_21]; norm_num
private theorem regLogEig_23 : regionalLogEigenvalue 23 = (444316699 / 59491432 : ℝ) := by
  rw [regionalLogEigenvalue_succ 22, regLogEig_22]; norm_num
private theorem regLogEig_24 : regionalLogEigenvalue 24 = (1347822955 / 178474296 : ℝ) := by
  rw [regionalLogEigenvalue_succ 23, regLogEig_23]; norm_num

private def poleA0 : ℝ := (6931471805599453094172321 / 10000000000000000000000000 : ℝ)
private def vPoleTrue (k : Fin 12) : ℝ := coeffAt ([2957801199659823083001290978033721647946667356038681246469236780193012154553067994816656881820742963287295662140001962401471403330661462994574224517640941799608442519700370578119550445427894115162678745224214047575706241765096690222050877161912344243075878859820897709845896471654774704478156504367068768898154321713647499502864678893888673887901525189180495386622492784246613340953435113471591817853221330108832622299403185134746240110185861767913482034466650885054594110781860762493404600333493179879780736178873599379515391984204360381518992827368731056606442071478734633 / 2899408712727579852800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 26610248606390485773244032346996218956155578432466476257328809761371913233500795398403957607991313672076428518561470323934585051414261709379032123163239763513392068835811854462573059409817635633299008164815587698858333601462225124000905246383559447413079627028493156338904646465391806793914883912535633241074753978647720150960372596322778085132868321481899351427952261024804105054137269618560908438017418018342700978239338506724237024578707517269856188885774264186497479754643828082118018077909682239198270266248183173644191984204360381518992827368731056606442071478734633 / 658956525619904512000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 22759329013207140175554758466169900402474410743610865982026612369529653807603320251294313419232385429001990277265586546034625446382927630964952610890124957532209983846973817366611495656535902292866927634814845167696125363235218643184723982667251091389885868472661765474720887501096264019737565378030005032787876499874924954682666378954555767314210824045910350685382092464141342345010545040946812129639327400687672704892030377606645706801519270318647951980502665244626808156993707483108716071618137057505490040737342203797328068120127172997609122910352202147357159578211 / 164739131404976128000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 30754461601455613431509901688354518478738860179110567024624243698682035327117594873078682297702624223277689912882186195292265212750538141669467585637058748917860487042854429860256145667270424953252798658926153104965044203358346259148424846358680872807211371431266747642611772662506963513773198807973817625938249745051962164630108028439996001827477740962382952157967726912003342117714624611262581835676992006125282580402491935039103696530146575148852821026161937269383780740538132841514802898798567824930165228646138997328068120127172997609122910352202147357159578211 / 183747492720934912000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 28043662119651465261066103061410899438340946903590287708967554779672921189466881284241335665911305295622826889669640717543178164918937577373585610123547951514477747631170831181822696432100816800283946389458506613941724704409211276654855372911689746237965279548054099778787587104382308992716041562745903986593802089118842617914935619180242493903646733757616000615389768470293529189511687959125720557145524387479883500229253662883659143620263737997513710077891061405085849852655204422163736064263715075789534969686997328068120127172997609122910352202147357159578211 / 272243527818149888000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 19888407697695115470973036055591648298605165774257145492321876909357048162473819704512038475824620885976150960995302053031109714816664721537244712240340917477083705277914548376033859174723082568515739603879278681385250039620143812407076035886554867363684337697744328259246557753681561987256208039107106107430606459508947044991107991779622240849325309292054447672711212730796623539128979676680451786564373215417980378002709546787003193487377658423170129897785272072321651050197438154129934145175926913656312847797328068120127172997609122910352202147357159578211 / 519485098999939072000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 12112727335991273832552026542242886909331059951561644254319248637873428972148166414910780218428671487312530775052198678735015054700633050792776380782601653471874126411472915758424230782715410129057613080176750692948269332460828252252287219416472553884721110195206588221439110034020353598869237131805536189543544634824898755441282165852972880345225115053403195309426651739639200170352806352282022342180858844941536873089593203790635576486713877919559227032024740155933317820562774080408212207483537592675621397328068120127172997609122910352202147357159578211 / 1272738492549850726400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 6873029566736684584772168585894277854668747741838048993622261125473954784685813829503643166751232228839781063906190518273699272570259239841553768432130517767562546475455297371433620597851310844639151987245750824340121554040909585771859303515082099219818086879585226640516485773885572535900402004242984965768843863540148286474708437667977788355773621042182043576584813494208870925892374494237362216105749924114806431523059225983088940648170369131626201343089352699458073796023587486464809745661344058007797328068120127172997609122910352202147357159578211 / 4059596915891765248000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 3933163391914175573687173695541248893757051616095887527547239242031253896042772741468232668095431257805753556745140221639705273608231984807746763244316160135483001289643964426090809516268226241336974753177247269616473536722966469630915067706057071004475902143039687058772897911107832620422762953620927077809645553638185837996911912105514435871698180026667420193343625236133100247033114103631130194602910330995081836529067539810071551556827137320501547119911949470957137902651168902982713284910460006997328068120127172997609122910352202147357159578211 / 17391682241945403392000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 146612302167147383757048765812925999814560879943701228144246724448648633428637406726903829470938140247602189867940089740366767932617202665083101937042341187677950096225709988800211613966856433304316957143506584638678983302317448511807691035218869381461610704594533169846949803767166409347946262491988301830188729583848732359443885336444733917263718564089142331004048070907836753103912099504321517548483228359119636183051573686360015147023000761740990107863726851211083015967972160375671075993036411607533418831010176329948406491306008668068210483 / 6235014857803956224000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 2012369175346585101746556990762322622314857446242635299268304203576322530854169617383928888121006941828484004402844169891938043867703863289572338290915436441140601721949123910033114015157930562568804630117574920728142088980929457600430349838307336847177990549013525471589689175608523024384315061649183687140901896495830368989452602977210456003610274210168900759430667107308782661380475764262775031606161283615145193832156975656456489231884371092225117901114614147549448346336040765031488322843797328068120127172997609122910352202147357159578211 / 1028283212555021975552000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 2806687076007439931851692057581555364694509726103163451621192295377494928952215276079601126108637083776018455747935893753675418655374987985938112718850909964267067820868138928315203036348510400399165600844552514509180142802097765012825620281196473208587564825720051771875024979563516801814855262388155020848684152183546106149238965739272179088662114533176704748894266176027545471978873175216340154777118080773186511490696068301797523593400273299764602745387815317181841330925849154499783681397328068120127172997609122910352202147357159578211 / 21079805857377950498816000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000] : List ℝ) k.1
private def vPoleClean (k : Fin 12) : ℝ := coeffAt ([510069723298394740874139552139 / 500000000000000000000000000000, 20191201977518358556439005049 / 500000000000000000000000000000, 27630750288780106345382521 / 200000000000000000000000000000, 10460843963788023931179 / 62500000000000000000000000000, 10300947223393222161 / 100000000000000000000000000000, 19142423657562359 / 500000000000000000000000000000, 1189632376063 / 125000000000000000000000000000, 1693032513 / 1000000000000000000000000000000, 28269 / 125000000000000000000000000000, 3 / 125000000000000000000000000000] : List ℝ) k.1
private def bFastQ : List (List ℚ) := ([[741596882435157469398270446786680538852770753723165273299301022576333469170285854677178749925583261018988210758593922860619474670350749 / 618089062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -874332352062810510498548708876181194955241237855815453535279375089549022775541350554308719121582342453932348711308136362578722822741275619 / 6588211317187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -5306133847910685107488678023220113022404093542224992224957459247456098844415185970607787351580031104042042696333612567310029729982849 / 26619035625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -432164864896908134915230395774483502585788710221230989417595392070352192757640431304417502668522399322431258439761522857236490540747 / 167008853320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 208339425020337040100146379256182586227860863116285363557559326573437050838152965825095553720299651777652124016611082012386260317689 / 9954289032187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -2471371755835822019554409799120609271896104627835035858697891821614261252305729871643427911847449506087070562027495692652722303231 / 13430389964062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 87915380335088053680792254984332124566854419344685392791696457337138270109177710218562852165608778317763886527807950371326450093 / 70509547311328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -28515262245600936075351194610264246247151987374193136141679177925312758876611055923120968246431306371641894025448207561176431 / 7908611596875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -5437546648706524043990006822172625113856837007617475918555704246278840374245079060748178871469443566527205491436383630617549 / 79056159106640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -2027336306953422142153237388819959845672419623090327953640775213544080361671090360655008190167418846294213271028763098007397 / 56684145877734375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -25001001847912946625239965266819725120992811 / 16935430683600000000000000000000000000000000000000000000000000, -25053851665633920884899324716161608191011 / 3506831606200000000000000000000000000000000000000000000000000],
    [-874332352062810510498548708876181194955241237855815453535279375089549022775541350554308719121582342453932348711308136362578722822741275619 / 6588211317187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 24883041341376611805591068342371251327074098400177653451067261921225275579918260264991211823313779232281908256773595879896405692861293476757 / 2196070439062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -876260998301576138243601831701639357888910453678060687660584320667702357361329413908030893670543983403961630418952359943585875953712249 / 292809391875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 290420054932815465592826126517801877252803543239571966962001439009717504123056796063734956359610717734683023477021790642395742308657 / 63348185742187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -97289190653417641089755341417871349221398845099486013910833393237634692248164962414186809844888959476844113780994214419812689627397 / 2247742684687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 186334512992624577648036069979850989168899999845168532072645200672848475817151638719921289751337673616599540287615707458012341721959 / 282038189245312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -225971331383783137964002367348363820417160318339550930796565493212708312866878153957442939500338801688299798658969753816294495579 / 23503182437109375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 64675969690215318060659412924602864168489944527283210570029935094788966628721376262145744194022650735010147672382157113372723 / 498741271875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -207834890565525450375830111506683114069829325251766856562052410283317684223211662126831923992605008266812811108436301225993 / 119240058984375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -10210013635431884563699139640455905041153218036725961443492220992521935792908238928576051680604270014026462399054992131813 / 72765270703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -25053851665633920884899324716161608191011 / 5967382200000000000000000000000000000000000000000000000000, 0],
    [-5306133847910685107488678023220113022404093542224992224957459247456098844415185970607787351580031104042042696333612567310029729982849 / 26619035625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -876260998301576138243601831701639357888910453678060687660584320667702357361329413908030893670543983403961630418952359943585875953712249 / 292809391875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 104284311495296900658928953030720964932754970164471219252298626169001023213546377897772690759914399601587022457521019292224607887282001687 / 6889632750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -5141182020568224451879503236469299392657848887810799794665407028787463597255266718144433952410287345801755098938046778368439267900183 / 2815474921875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 2759874521498676570178997170062456337403075218628633564933630091399365069913111959223786539953428505559693476617939643113772352767 / 3444816375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -325685663992711727716756853404919380011556730154164615546727238879873845297041833531753908397091613810016240246393460179192861391 / 404355826875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 3084122336534158617128697279211151904944563943309465369233845008802450557586293767437521433136474356791346530254758949127590393 / 723174844218750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -1071184350991739537140284126371312234078617576951616234555333810564128183441469729152622051868575436435592239152713823987793 / 16950683750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 18291073703776871894265719201391277457598891629425902405369064851548846141827639826563557280112275982967452671573062601 / 67846406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -3914664322755300346170536800026130830539752890719359513870127381058702152671059194176427763370472521985816001532718771 / 22615468750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0, 0],
    [-432164864896908134915230395774483502585788710221230989417595392070352192757640431304417502668522399322431258439761522857236490540747 / 167008853320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 290420054932815465592826126517801877252803543239571966962001439009717504123056796063734956359610717734683023477021790642395742308657 / 63348185742187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -5141182020568224451879503236469299392657848887810799794665407028787463597255266718144433952410287345801755098938046778368439267900183 / 2815474921875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 35327525111276826381236870770797251796251243596040388928092747631941158417221386785658228614627114293281705233255273463697714640077780599967 / 2066734559838867187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -996244003340682935525854461869305263311454689671813470997287969433733901949923607162813279541677264406832085871411460438289364125831 / 745272773437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 62023308732656753285521697278074876086430529593162633096356070017344754908496469679176296487313363718160011616668560597677355091 / 177445898437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -255335124039418606415203620028654611083968528645836783551717404427158472062471809762571740437133855691160524735652930564848686367 / 1377823039892578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 270271337191230094578657887852179387772138549869761085630748320021055997018378359063586235575448263280651321539124490511448291 / 1683251792578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -6116663004305156783911250379754606129098831487640651191643160264285866562932919095854281349799814674014701019464881843 / 3028857421875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -543817837483289356174904859733175883963827071795610663245491109521621071389792525854566120211 / 48828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0, 0],
    [208339425020337040100146379256182586227860863116285363557559326573437050838152965825095553720299651777652124016611082012386260317689 / 9954289032187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -97289190653417641089755341417871349221398845099486013910833393237634692248164962414186809844888959476844113780994214419812689627397 / 2247742684687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 2759874521498676570178997170062456337403075218628633564933630091399365069913111959223786539953428505559693476617939643113772352767 / 3444816375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -996244003340682935525854461869305263311454689671813470997287969433733901949923607162813279541677264406832085871411460438289364125831 / 745272773437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 57237093057398948374965746881502488809832263369220540679307397626526273895918346982983485509708411122000832923097517108659255189451692447987 / 3216001071937500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -11677800115782072124247148560426476106733704058628799704158485128859324454843672222817014848849425493767384554377307926406854555375009 / 11072624062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 23874249544185070242277116563979735846799755713284106295486829206409324677692597096242884151852014430074307106714228368772145709091 / 129677462578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -91018559775712057187194746005979337272847897281372206021210092984494993216688142234992369566643821269489104516332036751308910183 / 1310596048125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 688392641978806121201470202818661070591837975959650048527501437897932810078441677247706301124928189683697467562367820203233 / 17402603203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -535505439374385678917456280016056737637079843374763198021283733945226487960344531864875849 / 78125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0, 0],
    [-2471371755835822019554409799120609271896104627835035858697891821614261252305729871643427911847449506087070562027495692652722303231 / 13430389964062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 186334512992624577648036069979850989168899999845168532072645200672848475817151638719921289751337673616599540287615707458012341721959 / 282038189245312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -325685663992711727716756853404919380011556730154164615546727238879873845297041833531753908397091613810016240246393460179192861391 / 404355826875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 62023308732656753285521697278074876086430529593162633096356070017344754908496469679176296487313363718160011616668560597677355091 / 177445898437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -11677800115782072124247148560426476106733704058628799704158485128859324454843672222817014848849425493767384554377307926406854555375009 / 11072624062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 4050021204404120489963144888302344590287254255777120862443666802991446813950508906701370366527183178765540048422842540267847061411581665255411 / 230758518473437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -16748407390552605228927283381170560764607552416037499136657251310586825301032277335699110596334707115942863499375571168175514857546438391 / 19229876539453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 487909004991847124139052652358712697435384103160302275634164114867132444416904491629341738759729991395352794648677615474396389224837 / 4488671446875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -891510988958268755919176477899623869735090592168668071429834323649674490501786371910151321471901464229952243705490015472779891 / 29004338671875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 688392641978806121202594231040792884572500959066751306393736866231900343579489433619670830004006164538121036197650929636881 / 50375956640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0, 0],
    [87915380335088053680792254984332124566854419344685392791696457337138270109177710218562852165608778317763886527807950371326450093 / 70509547311328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -225971331383783137964002367348363820417160318339550930796565493212708312866878153957442939500338801688299798658969753816294495579 / 23503182437109375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 3084122336534158617128697279211151904944563943309465369233845008802450557586293767437521433136474356791346530254758949127590393 / 723174844218750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -255335124039418606415203620028654611083968528645836783551717404427158472062471809762571740437133855691160524735652930564848686367 / 1377823039892578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 23874249544185070242277116563979735846799755713284106295486829206409324677692597096242884151852014430074307106714228368772145709091 / 129677462578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -16748407390552605228927283381170560764607552416037499136657251310586825301032277335699110596334707115942863499375571168175514857546438391 / 19229876539453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 55094928669713327736827332524932759741245398685008388670641639327179477745364722027421257879040692610695360754115827342420774583777583340585909 / 3331576110460253906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -1028274824501262709766694729041783810211540068089150160680637305553896037606231785041322019558451002756019921602815266884247011919476783 / 1386207358593750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 20601425994259429027107921891404640450008928453794872946932080951636491516486313166564509356633963168170424024509082500265973446879 / 296531199316406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -52526822391582526967009821391997453959562387607996964029261746766101187546937687405295913351758720901000966850763667987144443559 / 3438159040722656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 451145001847230379591332155339 / 82851757148160000000000000000000000000000000, 0],
    [-28515262245600936075351194610264246247151987374193136141679177925312758876611055923120968246431306371641894025448207561176431 / 7908611596875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 64675969690215318060659412924602864168489944527283210570029935094788966628721376262145744194022650735010147672382157113372723 / 498741271875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -1071184350991739537140284126371312234078617576951616234555333810564128183441469729152622051868575436435592239152713823987793 / 16950683750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 270271337191230094578657887852179387772138549869761085630748320021055997018378359063586235575448263280651321539124490511448291 / 1683251792578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -91018559775712057187194746005979337272847897281372206021210092984494993216688142234992369566643821269489104516332036751308910183 / 1310596048125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 487909004991847124139052652358712697435384103160302275634164114867132444416904491629341738759729991395352794648677615474396389224837 / 4488671446875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -1028274824501262709766694729041783810211540068089150160680637305553896037606231785041322019558451002756019921602815266884247011919476783 / 1386207358593750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 174067809030441898277569284159067968522509130504891667858743131450023079350729958411152731071519377799269149553289770525202402567414440482083030911 / 11697738133500168750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -686971017520772444151535975948633785483668121091258798483729587447356308432129572204235274385151652033412351410598086792846716564559087 / 1063422232031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 79595182900359210459851601800838586071777153275884966273301315291088636249470934595698186508034110452646877417028438500700575059693 / 1690728883593750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -890179554834046650849372264446981 / 107493012506880000000000000000000000000000000, 451145001847230379591332155339 / 186548720117760000000000000000000000000000000],
    [-5437546648706524043990006822172625113856837007617475918555704246278840374245079060748178871469443566527205491436383630617549 / 79056159106640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -207834890565525450375830111506683114069829325251766856562052410283317684223211662126831923992605008266812811108436301225993 / 119240058984375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 18291073703776871894265719201391277457598891629425902405369064851548846141827639826563557280112275982967452671573062601 / 67846406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -6116663004305156783911250379754606129098831487640651191643160264285866562932919095854281349799814674014701019464881843 / 3028857421875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 688392641978806121201470202818661070591837975959650048527501437897932810078441677247706301124928189683697467562367820203233 / 17402603203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -891510988958268755919176477899623869735090592168668071429834323649674490501786371910151321471901464229952243705490015472779891 / 29004338671875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 20601425994259429027107921891404640450008928453794872946932080951636491516486313166564509356633963168170424024509082500265973446879 / 296531199316406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -686971017520772444151535975948633785483668121091258798483729587447356308432129572204235274385151652033412351410598086792846716564559087 / 1063422232031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 22976283709551095551956714041215905094225589387598971596278137034756246287852146881700614911153511356078298680165032427073320761543125630817777777266238920443 / 1813427824298253150957940398339843750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -192500071755423938602012545883126945208288503807547877434336539578795275998941090520924814263290363017578855333436304379757185439887856932005387119833 / 336463817978524302855700488281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 5478934290502899132359567386486494103492634675418375117833102816593976459 / 164212430825257879019419775390625000000000000000000000000000000000000000000000000, -18412719123261729963524455260350523376532708273069038291260917033671 / 3834514150470710543531030273437500000000000000000000000000000000000000000000000],
    [-2027336306953422142153237388819959845672419623090327953640775213544080361671090360655008190167418846294213271028763098007397 / 56684145877734375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -10210013635431884563699139640455905041153218036725961443492220992521935792908238928576051680604270014026462399054992131813 / 72765270703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -3914664322755300346170536800026130830539752890719359513870127381058702152671059194176427763370472521985816001532718771 / 22615468750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -543817837483289356174904859733175883963827071795610663245491109521621071389792525854566120211 / 48828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -535505439374385678917456280016056737637079843374763198021283733945226487960344531864875849 / 78125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 688392641978806121202594231040792884572500959066751306393736866231900343579489433619670830004006164538121036197650929636881 / 50375956640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -52526822391582526967009821391997453959562387607996964029261746766101187546937687405295913351758720901000966850763667987144443559 / 3438159040722656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 79595182900359210459851601800838586071777153275884966273301315291088636249470934595698186508034110452646877417028438500700575059693 / 1690728883593750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -192500071755423938602012545883126945208288503807547877434336539578795275998941090520924814263290363017578855333436304379757185439887856932005387119833 / 336463817978524302855700488281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 2100600884710502820914414240544563306378994779228382364304079844702966376084410731610033989958397873082055987649128015185046806865443747549146124915239677837 / 210617256437854091309212946191406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -79720186322807921059968278751852695929672323813377128128837886758515426907851 / 155273066546463894376785937500000000000000000000000000000000000000000000000000000, 1394510929850175075938153622925011077122012436914406814513439936741713007 / 56912614557640258320028125000000000000000000000000000000000000000000000000000000],
    [-25001001847912946625239965266819725120992811 / 16935430683600000000000000000000000000000000000000000000000000, -25053851665633920884899324716161608191011 / 5967382200000000000000000000000000000000000000000000000000, 0, 0, 0, 0, 451145001847230379591332155339 / 82851757148160000000000000000000000000000000, -890179554834046650849372264446981 / 107493012506880000000000000000000000000000000, 5478934290502899132359567386486494103492634675418375117833102816593976459 / 164212430825257879019419775390625000000000000000000000000000000000000000000000000, -79720186322807921059968278751852695929672323813377128128837886758515426907851 / 155273066546463894376785937500000000000000000000000000000000000000000000000000000, 351219787369039833763089311339486061266207928384781312073694422028389102561286032127432623 / 51320546817237321534736411054218750000000000000000000000000000000000000000000000000000000, -559699690071880242039367779330444242779564261698844121960591740346917724492257 / 1201999046499196210211540343750000000000000000000000000000000000000000000000000000],
    [-25053851665633920884899324716161608191011 / 3506831606200000000000000000000000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 451145001847230379591332155339 / 186548720117760000000000000000000000000000000, -18412719123261729963524455260350523376532708273069038291260917033671 / 3834514150470710543531030273437500000000000000000000000000000000000000000000000, 1394510929850175075938153622925011077122012436914406814513439936741713007 / 56912614557640258320028125000000000000000000000000000000000000000000000000000000, -559699690071880242039367779330444242779564261698844121960591740346917724492257 / 1201999046499196210211540343750000000000000000000000000000000000000000000000000000, 7819178899981724512979387695828793498741724286702016672128371688941860730119576431777230111427 / 2353169314720386207677946744047273906250000000000000000000000000000000000000000000000000000000]] : List (List ℚ))
private def bFastMat (i j : Fin 12) : ℝ := matAt ([([741596882435157469398270446786680538852770753723165273299301022576333469170285854677178749925583261018988210758593922860619474670350749 / 618089062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -874332352062810510498548708876181194955241237855815453535279375089549022775541350554308719121582342453932348711308136362578722822741275619 / 6588211317187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -5306133847910685107488678023220113022404093542224992224957459247456098844415185970607787351580031104042042696333612567310029729982849 / 26619035625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -432164864896908134915230395774483502585788710221230989417595392070352192757640431304417502668522399322431258439761522857236490540747 / 167008853320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 208339425020337040100146379256182586227860863116285363557559326573437050838152965825095553720299651777652124016611082012386260317689 / 9954289032187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -2471371755835822019554409799120609271896104627835035858697891821614261252305729871643427911847449506087070562027495692652722303231 / 13430389964062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 87915380335088053680792254984332124566854419344685392791696457337138270109177710218562852165608778317763886527807950371326450093 / 70509547311328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -28515262245600936075351194610264246247151987374193136141679177925312758876611055923120968246431306371641894025448207561176431 / 7908611596875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -5437546648706524043990006822172625113856837007617475918555704246278840374245079060748178871469443566527205491436383630617549 / 79056159106640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -2027336306953422142153237388819959845672419623090327953640775213544080361671090360655008190167418846294213271028763098007397 / 56684145877734375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -25001001847912946625239965266819725120992811 / 16935430683600000000000000000000000000000000000000000000000000, -25053851665633920884899324716161608191011 / 3506831606200000000000000000000000000000000000000000000000000] : List ℝ),
    ([-874332352062810510498548708876181194955241237855815453535279375089549022775541350554308719121582342453932348711308136362578722822741275619 / 6588211317187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 24883041341376611805591068342371251327074098400177653451067261921225275579918260264991211823313779232281908256773595879896405692861293476757 / 2196070439062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -876260998301576138243601831701639357888910453678060687660584320667702357361329413908030893670543983403961630418952359943585875953712249 / 292809391875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 290420054932815465592826126517801877252803543239571966962001439009717504123056796063734956359610717734683023477021790642395742308657 / 63348185742187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -97289190653417641089755341417871349221398845099486013910833393237634692248164962414186809844888959476844113780994214419812689627397 / 2247742684687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 186334512992624577648036069979850989168899999845168532072645200672848475817151638719921289751337673616599540287615707458012341721959 / 282038189245312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -225971331383783137964002367348363820417160318339550930796565493212708312866878153957442939500338801688299798658969753816294495579 / 23503182437109375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 64675969690215318060659412924602864168489944527283210570029935094788966628721376262145744194022650735010147672382157113372723 / 498741271875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -207834890565525450375830111506683114069829325251766856562052410283317684223211662126831923992605008266812811108436301225993 / 119240058984375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -10210013635431884563699139640455905041153218036725961443492220992521935792908238928576051680604270014026462399054992131813 / 72765270703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -25053851665633920884899324716161608191011 / 5967382200000000000000000000000000000000000000000000000000] : List ℝ),
    ([-5306133847910685107488678023220113022404093542224992224957459247456098844415185970607787351580031104042042696333612567310029729982849 / 26619035625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -876260998301576138243601831701639357888910453678060687660584320667702357361329413908030893670543983403961630418952359943585875953712249 / 292809391875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 104284311495296900658928953030720964932754970164471219252298626169001023213546377897772690759914399601587022457521019292224607887282001687 / 6889632750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -5141182020568224451879503236469299392657848887810799794665407028787463597255266718144433952410287345801755098938046778368439267900183 / 2815474921875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 2759874521498676570178997170062456337403075218628633564933630091399365069913111959223786539953428505559693476617939643113772352767 / 3444816375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -325685663992711727716756853404919380011556730154164615546727238879873845297041833531753908397091613810016240246393460179192861391 / 404355826875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 3084122336534158617128697279211151904944563943309465369233845008802450557586293767437521433136474356791346530254758949127590393 / 723174844218750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -1071184350991739537140284126371312234078617576951616234555333810564128183441469729152622051868575436435592239152713823987793 / 16950683750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 18291073703776871894265719201391277457598891629425902405369064851548846141827639826563557280112275982967452671573062601 / 67846406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -3914664322755300346170536800026130830539752890719359513870127381058702152671059194176427763370472521985816001532718771 / 22615468750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000] : List ℝ),
    ([-432164864896908134915230395774483502585788710221230989417595392070352192757640431304417502668522399322431258439761522857236490540747 / 167008853320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 290420054932815465592826126517801877252803543239571966962001439009717504123056796063734956359610717734683023477021790642395742308657 / 63348185742187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -5141182020568224451879503236469299392657848887810799794665407028787463597255266718144433952410287345801755098938046778368439267900183 / 2815474921875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 35327525111276826381236870770797251796251243596040388928092747631941158417221386785658228614627114293281705233255273463697714640077780599967 / 2066734559838867187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -996244003340682935525854461869305263311454689671813470997287969433733901949923607162813279541677264406832085871411460438289364125831 / 745272773437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 62023308732656753285521697278074876086430529593162633096356070017344754908496469679176296487313363718160011616668560597677355091 / 177445898437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -255335124039418606415203620028654611083968528645836783551717404427158472062471809762571740437133855691160524735652930564848686367 / 1377823039892578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 270271337191230094578657887852179387772138549869761085630748320021055997018378359063586235575448263280651321539124490511448291 / 1683251792578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -6116663004305156783911250379754606129098831487640651191643160264285866562932919095854281349799814674014701019464881843 / 3028857421875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -543817837483289356174904859733175883963827071795610663245491109521621071389792525854566120211 / 48828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000] : List ℝ),
    ([208339425020337040100146379256182586227860863116285363557559326573437050838152965825095553720299651777652124016611082012386260317689 / 9954289032187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -97289190653417641089755341417871349221398845099486013910833393237634692248164962414186809844888959476844113780994214419812689627397 / 2247742684687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 2759874521498676570178997170062456337403075218628633564933630091399365069913111959223786539953428505559693476617939643113772352767 / 3444816375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -996244003340682935525854461869305263311454689671813470997287969433733901949923607162813279541677264406832085871411460438289364125831 / 745272773437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 57237093057398948374965746881502488809832263369220540679307397626526273895918346982983485509708411122000832923097517108659255189451692447987 / 3216001071937500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -11677800115782072124247148560426476106733704058628799704158485128859324454843672222817014848849425493767384554377307926406854555375009 / 11072624062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 23874249544185070242277116563979735846799755713284106295486829206409324677692597096242884151852014430074307106714228368772145709091 / 129677462578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -91018559775712057187194746005979337272847897281372206021210092984494993216688142234992369566643821269489104516332036751308910183 / 1310596048125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 688392641978806121201470202818661070591837975959650048527501437897932810078441677247706301124928189683697467562367820203233 / 17402603203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -535505439374385678917456280016056737637079843374763198021283733945226487960344531864875849 / 78125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000] : List ℝ),
    ([-2471371755835822019554409799120609271896104627835035858697891821614261252305729871643427911847449506087070562027495692652722303231 / 13430389964062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 186334512992624577648036069979850989168899999845168532072645200672848475817151638719921289751337673616599540287615707458012341721959 / 282038189245312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -325685663992711727716756853404919380011556730154164615546727238879873845297041833531753908397091613810016240246393460179192861391 / 404355826875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 62023308732656753285521697278074876086430529593162633096356070017344754908496469679176296487313363718160011616668560597677355091 / 177445898437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -11677800115782072124247148560426476106733704058628799704158485128859324454843672222817014848849425493767384554377307926406854555375009 / 11072624062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 4050021204404120489963144888302344590287254255777120862443666802991446813950508906701370366527183178765540048422842540267847061411581665255411 / 230758518473437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -16748407390552605228927283381170560764607552416037499136657251310586825301032277335699110596334707115942863499375571168175514857546438391 / 19229876539453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 487909004991847124139052652358712697435384103160302275634164114867132444416904491629341738759729991395352794648677615474396389224837 / 4488671446875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -891510988958268755919176477899623869735090592168668071429834323649674490501786371910151321471901464229952243705490015472779891 / 29004338671875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 688392641978806121202594231040792884572500959066751306393736866231900343579489433619670830004006164538121036197650929636881 / 50375956640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000] : List ℝ),
    ([87915380335088053680792254984332124566854419344685392791696457337138270109177710218562852165608778317763886527807950371326450093 / 70509547311328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -225971331383783137964002367348363820417160318339550930796565493212708312866878153957442939500338801688299798658969753816294495579 / 23503182437109375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 3084122336534158617128697279211151904944563943309465369233845008802450557586293767437521433136474356791346530254758949127590393 / 723174844218750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -255335124039418606415203620028654611083968528645836783551717404427158472062471809762571740437133855691160524735652930564848686367 / 1377823039892578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 23874249544185070242277116563979735846799755713284106295486829206409324677692597096242884151852014430074307106714228368772145709091 / 129677462578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -16748407390552605228927283381170560764607552416037499136657251310586825301032277335699110596334707115942863499375571168175514857546438391 / 19229876539453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 55094928669713327736827332524932759741245398685008388670641639327179477745364722027421257879040692610695360754115827342420774583777583340585909 / 3331576110460253906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -1028274824501262709766694729041783810211540068089150160680637305553896037606231785041322019558451002756019921602815266884247011919476783 / 1386207358593750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 20601425994259429027107921891404640450008928453794872946932080951636491516486313166564509356633963168170424024509082500265973446879 / 296531199316406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -52526822391582526967009821391997453959562387607996964029261746766101187546937687405295913351758720901000966850763667987144443559 / 3438159040722656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 451145001847230379591332155339 / 82851757148160000000000000000000000000000000] : List ℝ),
    ([-28515262245600936075351194610264246247151987374193136141679177925312758876611055923120968246431306371641894025448207561176431 / 7908611596875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 64675969690215318060659412924602864168489944527283210570029935094788966628721376262145744194022650735010147672382157113372723 / 498741271875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -1071184350991739537140284126371312234078617576951616234555333810564128183441469729152622051868575436435592239152713823987793 / 16950683750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 270271337191230094578657887852179387772138549869761085630748320021055997018378359063586235575448263280651321539124490511448291 / 1683251792578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -91018559775712057187194746005979337272847897281372206021210092984494993216688142234992369566643821269489104516332036751308910183 / 1310596048125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 487909004991847124139052652358712697435384103160302275634164114867132444416904491629341738759729991395352794648677615474396389224837 / 4488671446875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -1028274824501262709766694729041783810211540068089150160680637305553896037606231785041322019558451002756019921602815266884247011919476783 / 1386207358593750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 174067809030441898277569284159067968522509130504891667858743131450023079350729958411152731071519377799269149553289770525202402567414440482083030911 / 11697738133500168750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -686971017520772444151535975948633785483668121091258798483729587447356308432129572204235274385151652033412351410598086792846716564559087 / 1063422232031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 79595182900359210459851601800838586071777153275884966273301315291088636249470934595698186508034110452646877417028438500700575059693 / 1690728883593750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -890179554834046650849372264446981 / 107493012506880000000000000000000000000000000, 451145001847230379591332155339 / 186548720117760000000000000000000000000000000] : List ℝ),
    ([-5437546648706524043990006822172625113856837007617475918555704246278840374245079060748178871469443566527205491436383630617549 / 79056159106640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -207834890565525450375830111506683114069829325251766856562052410283317684223211662126831923992605008266812811108436301225993 / 119240058984375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 18291073703776871894265719201391277457598891629425902405369064851548846141827639826563557280112275982967452671573062601 / 67846406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -6116663004305156783911250379754606129098831487640651191643160264285866562932919095854281349799814674014701019464881843 / 3028857421875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 688392641978806121201470202818661070591837975959650048527501437897932810078441677247706301124928189683697467562367820203233 / 17402603203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -891510988958268755919176477899623869735090592168668071429834323649674490501786371910151321471901464229952243705490015472779891 / 29004338671875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 20601425994259429027107921891404640450008928453794872946932080951636491516486313166564509356633963168170424024509082500265973446879 / 296531199316406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -686971017520772444151535975948633785483668121091258798483729587447356308432129572204235274385151652033412351410598086792846716564559087 / 1063422232031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 22976283709551095551956714041215905094225589387598971596278137034756246287852146881700614911153511356078298680165032427073320761543125630817777777266238920443 / 1813427824298253150957940398339843750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -192500071755423938602012545883126945208288503807547877434336539578795275998941090520924814263290363017578855333436304379757185439887856932005387119833 / 336463817978524302855700488281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 5478934290502899132359567386486494103492634675418375117833102816593976459 / 164212430825257879019419775390625000000000000000000000000000000000000000000000000, -18412719123261729963524455260350523376532708273069038291260917033671 / 3834514150470710543531030273437500000000000000000000000000000000000000000000000] : List ℝ),
    ([-2027336306953422142153237388819959845672419623090327953640775213544080361671090360655008190167418846294213271028763098007397 / 56684145877734375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -10210013635431884563699139640455905041153218036725961443492220992521935792908238928576051680604270014026462399054992131813 / 72765270703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -3914664322755300346170536800026130830539752890719359513870127381058702152671059194176427763370472521985816001532718771 / 22615468750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -543817837483289356174904859733175883963827071795610663245491109521621071389792525854566120211 / 48828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -535505439374385678917456280016056737637079843374763198021283733945226487960344531864875849 / 78125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 688392641978806121202594231040792884572500959066751306393736866231900343579489433619670830004006164538121036197650929636881 / 50375956640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -52526822391582526967009821391997453959562387607996964029261746766101187546937687405295913351758720901000966850763667987144443559 / 3438159040722656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 79595182900359210459851601800838586071777153275884966273301315291088636249470934595698186508034110452646877417028438500700575059693 / 1690728883593750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -192500071755423938602012545883126945208288503807547877434336539578795275998941090520924814263290363017578855333436304379757185439887856932005387119833 / 336463817978524302855700488281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 2100600884710502820914414240544563306378994779228382364304079844702966376084410731610033989958397873082055987649128015185046806865443747549146124915239677837 / 210617256437854091309212946191406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -79720186322807921059968278751852695929672323813377128128837886758515426907851 / 155273066546463894376785937500000000000000000000000000000000000000000000000000000, 1394510929850175075938153622925011077122012436914406814513439936741713007 / 56912614557640258320028125000000000000000000000000000000000000000000000000000000] : List ℝ),
    ([-25001001847912946625239965266819725120992811 / 16935430683600000000000000000000000000000000000000000000000000, -25053851665633920884899324716161608191011 / 5967382200000000000000000000000000000000000000000000000000, 0, 0, 0, 0, 451145001847230379591332155339 / 82851757148160000000000000000000000000000000, -890179554834046650849372264446981 / 107493012506880000000000000000000000000000000, 5478934290502899132359567386486494103492634675418375117833102816593976459 / 164212430825257879019419775390625000000000000000000000000000000000000000000000000, -79720186322807921059968278751852695929672323813377128128837886758515426907851 / 155273066546463894376785937500000000000000000000000000000000000000000000000000000, 351219787369039833763089311339486061266207928384781312073694422028389102561286032127432623 / 51320546817237321534736411054218750000000000000000000000000000000000000000000000000000000, -559699690071880242039367779330444242779564261698844121960591740346917724492257 / 1201999046499196210211540343750000000000000000000000000000000000000000000000000000] : List ℝ),
    ([-25053851665633920884899324716161608191011 / 3506831606200000000000000000000000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 451145001847230379591332155339 / 186548720117760000000000000000000000000000000, -18412719123261729963524455260350523376532708273069038291260917033671 / 3834514150470710543531030273437500000000000000000000000000000000000000000000000, 1394510929850175075938153622925011077122012436914406814513439936741713007 / 56912614557640258320028125000000000000000000000000000000000000000000000000000000, -559699690071880242039367779330444242779564261698844121960591740346917724492257 / 1201999046499196210211540343750000000000000000000000000000000000000000000000000000, 7819178899981724512979387695828793498741724286702016672128371688941860730119576431777230111427 / 2353169314720386207677946744047273906250000000000000000000000000000000000000000000000000000000] : List ℝ)] : List (List ℝ)) i.1 j.1
private def bCleanMat (i j : Fin 12) : ℝ := (ApertureLogTwo.matQ ApertureLogTwo.evenBClean i.1 j.1 : ℝ)

private theorem bFast_to_bClean_le (m : Fin 12 → ℝ) :
    (∑ i : Fin 12, ∑ j : Fin 12, bFastMat i j * m i * m j) ≤
      ∑ i : Fin 12, ∑ j : Fin 12, bCleanMat i j * m i * m j := by
  have h := ApertureLogTwo.quad_le_of_domCheck_sub (Q := bFastQ) (Q' := ApertureLogTwo.evenBClean) (by decide +kernel) m
  refine le_trans (le_of_eq ?_) h
  simp_rw [ApertureLogTwo.quadR, sum_finK, matQ_eq_qcoeffAt]
  dsimp only [bFastMat, bFastQ, qcoeffAt, qlistAt, matAt, listAt, coeffAt]
  simp only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_zero]

private theorem cross_spillover_young {Y W A_val M_r ε : ℝ}
    (_hW : 0 ≤ W) (hA : 0 ≤ A_val) (hM : 0 ≤ M_r) (hε : 0 < ε)
    (hcs : Y ^ 2 ≤ W ^ 2 * (A_val * (2 * M_r))) :
    -((2 * W ^ 2 / ε) * A_val + ε * M_r) ≤ 2 * Y ∧
      -((2 * W ^ 2 / ε) * A_val + ε * M_r) ≤ -2 * Y := by
  set U := (2 * W ^ 2 / ε) * A_val
  set V := ε * M_r
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hUV : U * V = 2 * W ^ 2 * A_val * M_r := by dsimp [U, V]; field_simp [hε.ne']; try ring
  have hdiff : 0 ≤ (U + V) ^ 2 - (2 * Y) ^ 2 := by
    have h1 : (U + V) ^ 2 - (2 * Y) ^ 2 = (U - V) ^ 2 + 4 * (U * V - Y ^ 2) := by ring
    rw [h1, hUV]; nlinarith [sq_nonneg (U - V), hcs]
  have habs : |2 * Y| ≤ U + V := by
    have hsq : |2 * Y| ^ 2 ≤ (U + V) ^ 2 := by rw [sq_abs]; linarith
    nlinarith [abs_nonneg (2 * Y)]
  exact ⟨by linarith [abs_le.mp habs], by linarith [abs_le.mp habs]⟩

private def c0Rat : ℝ := (10229070456652153 / 10000000000000000 : ℝ)
private def e2Mid : ℝ := (-1225322679335683989642377 / 2500000000000000000000000 : ℝ)
private def e3Mid : ℝ := (-3171420502987819885931939 / 5000000000000000000000000 : ℝ)
private def deltaResRat : ℝ := (11324140799014169 / 1000000000000000000 : ℝ)

private theorem hEv_bound_0 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hGpar : ∀ u, dilateLogTwo F (-u) = dilateLogTwo F u) :
    let m := halfMoment (dilateLogTwo F)
    apow0_1 * (∑ i : Fin 12, ∑ j : Fin 12, qEvMat_0 i j * m i * m j) -
      (∑ i : Fin 12, (errApow_1 * qEvRowAbs_0 i) * m i ^ 2) ≤
      ((105091 / 5000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 0 * autocorr F t) /
        (2 * apertureLogTwo) := by
  intro m
  set G := dilateLogTwo F
  have hA_pos : 0 < apertureLogTwo := apertureLogTwo_pos
  have hdil := dilated_correlation_moment_log_two F 0
  have hdiv : ((105091 / 5000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 0 * autocorr F t) /
      (2 * apertureLogTwo) =
      apertureLogTwo ^ 1 * (((105091 / 5000000000000000000 : ℝ) / 2) * ∫ t in Ioc (0 : ℝ) 2, t ^ 0 * autocorr G t) := by
    rw [hdil]; field_simp [hA_pos.ne']; ring
  rw [hdiv]
  have hexp : ((105091 / 5000000000000000000 : ℝ) / 2) * (∫ t in Ioc (0 : ℝ) 2, t ^ 0 * autocorr G t) =
      ∑ i : Fin 12, ∑ j : Fin 12, qEvMat_0 i j * m i * m j := by
    have hevm := even_lag_moment_of_even hGc hsG hGpar 0
    rw [hevm]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [show ((0 : ℕ).choose 0 : ℝ) = 1 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]]
    have hm_0 := mon_moment_eq_leg_sum hGc ⟨0, by omega⟩
    dsimp only [degAt] at hm_0
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_0
    rw [sum_finK] at hm_0; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_0
    rw [hm_0]
    simp_rw [sum_finK]; dsimp only [qEvMat_0, matAt, listAt, coeffAt, m]; ring
  rw [hexp]
  have hpert := symm_quad_scale_pert qEvMat_0 qEvMat_0_sym abs_aperture_pow_1_sub m
  simp_rw [qEvRowAbs_0_eq] at hpert
  exact hpert

private theorem hEv_bound_1 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hGpar : ∀ u, dilateLogTwo F (-u) = dilateLogTwo F u) :
    let m := halfMoment (dilateLogTwo F)
    apow0_3 * (∑ i : Fin 12, ∑ j : Fin 12, qEvMat_1 i j * m i * m j) -
      (∑ i : Fin 12, (errApow_3 * qEvRowAbs_1 i) * m i ^ 2) ≤
      ((24999999999449249 / 400000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 2 * autocorr F t) /
        (2 * apertureLogTwo) := by
  intro m
  set G := dilateLogTwo F
  have hA_pos : 0 < apertureLogTwo := apertureLogTwo_pos
  have hdil := dilated_correlation_moment_log_two F 2
  have hdiv : ((24999999999449249 / 400000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 2 * autocorr F t) /
      (2 * apertureLogTwo) =
      apertureLogTwo ^ 3 * (((24999999999449249 / 400000000000000000 : ℝ) / 2) * ∫ t in Ioc (0 : ℝ) 2, t ^ 2 * autocorr G t) := by
    rw [hdil]; field_simp [hA_pos.ne']; ring
  rw [hdiv]
  have hexp : ((24999999999449249 / 400000000000000000 : ℝ) / 2) * (∫ t in Ioc (0 : ℝ) 2, t ^ 2 * autocorr G t) =
      ∑ i : Fin 12, ∑ j : Fin 12, qEvMat_1 i j * m i * m j := by
    have hevm := even_lag_moment_of_even hGc hsG hGpar 1
    rw [hevm]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [show ((2 : ℕ).choose 0 : ℝ) = 1 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((2 : ℕ).choose 2 : ℝ) = 1 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]]
    have hm_0 := mon_moment_eq_leg_sum hGc ⟨0, by omega⟩
    dsimp only [degAt] at hm_0
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_0
    rw [sum_finK] at hm_0; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_0
    have hm_1 := mon_moment_eq_leg_sum hGc ⟨1, by omega⟩
    dsimp only [degAt] at hm_1
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_1
    rw [sum_finK] at hm_1; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_1
    rw [hm_0, hm_1]
    simp_rw [sum_finK]; dsimp only [qEvMat_1, matAt, listAt, coeffAt, m]; ring
  rw [hexp]
  have hpert := symm_quad_scale_pert qEvMat_1 qEvMat_1_sym abs_aperture_pow_3_sub m
  simp_rw [qEvRowAbs_1_eq] at hpert
  exact hpert

private theorem hEv_bound_2 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hGpar : ∀ u, dilateLogTwo F (-u) = dilateLogTwo F u) :
    let m := halfMoment (dilateLogTwo F)
    apow0_5 * (∑ i : Fin 12, ∑ j : Fin 12, qEvMat_2 i j * m i * m j) -
      (∑ i : Fin 12, (errApow_5 * qEvRowAbs_2 i) * m i ^ 2) ≤
      ((-65104166242035063 / 10000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 4 * autocorr F t) /
        (2 * apertureLogTwo) := by
  intro m
  set G := dilateLogTwo F
  have hA_pos : 0 < apertureLogTwo := apertureLogTwo_pos
  have hdil := dilated_correlation_moment_log_two F 4
  have hdiv : ((-65104166242035063 / 10000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 4 * autocorr F t) /
      (2 * apertureLogTwo) =
      apertureLogTwo ^ 5 * (((-65104166242035063 / 10000000000000000000 : ℝ) / 2) * ∫ t in Ioc (0 : ℝ) 2, t ^ 4 * autocorr G t) := by
    rw [hdil]; field_simp [hA_pos.ne']; ring
  rw [hdiv]
  have hexp : ((-65104166242035063 / 10000000000000000000 : ℝ) / 2) * (∫ t in Ioc (0 : ℝ) 2, t ^ 4 * autocorr G t) =
      ∑ i : Fin 12, ∑ j : Fin 12, qEvMat_2 i j * m i * m j := by
    have hevm := even_lag_moment_of_even hGc hsG hGpar 2
    rw [hevm]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [show ((4 : ℕ).choose 0 : ℝ) = 1 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((4 : ℕ).choose 2 : ℝ) = 6 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((4 : ℕ).choose 4 : ℝ) = 1 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]]
    have hm_0 := mon_moment_eq_leg_sum hGc ⟨0, by omega⟩
    dsimp only [degAt] at hm_0
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_0
    rw [sum_finK] at hm_0; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_0
    have hm_1 := mon_moment_eq_leg_sum hGc ⟨1, by omega⟩
    dsimp only [degAt] at hm_1
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_1
    rw [sum_finK] at hm_1; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_1
    have hm_2 := mon_moment_eq_leg_sum hGc ⟨2, by omega⟩
    dsimp only [degAt] at hm_2
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_2
    rw [sum_finK] at hm_2; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_2
    rw [hm_0, hm_1, hm_2]
    simp_rw [sum_finK]; dsimp only [qEvMat_2, matAt, listAt, coeffAt, m]; ring
  rw [hexp]
  have hpert := symm_quad_scale_pert qEvMat_2 qEvMat_2_sym abs_aperture_pow_5_sub m
  simp_rw [qEvRowAbs_2_eq] at hpert
  exact hpert

private theorem hEv_bound_3 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hGpar : ∀ u, dilateLogTwo F (-u) = dilateLogTwo F u) :
    let m := halfMoment (dilateLogTwo F)
    apow0_7 * (∑ i : Fin 12, ∑ j : Fin 12, qEvMat_3 i j * m i * m j) -
      (∑ i : Fin 12, (errApow_7 * qEvRowAbs_3 i) * m i ^ 2) ≤
      ((3309458785969429 / 5000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 6 * autocorr F t) /
        (2 * apertureLogTwo) := by
  intro m
  set G := dilateLogTwo F
  have hA_pos : 0 < apertureLogTwo := apertureLogTwo_pos
  have hdil := dilated_correlation_moment_log_two F 6
  have hdiv : ((3309458785969429 / 5000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 6 * autocorr F t) /
      (2 * apertureLogTwo) =
      apertureLogTwo ^ 7 * (((3309458785969429 / 5000000000000000000 : ℝ) / 2) * ∫ t in Ioc (0 : ℝ) 2, t ^ 6 * autocorr G t) := by
    rw [hdil]; field_simp [hA_pos.ne']; ring
  rw [hdiv]
  have hexp : ((3309458785969429 / 5000000000000000000 : ℝ) / 2) * (∫ t in Ioc (0 : ℝ) 2, t ^ 6 * autocorr G t) =
      ∑ i : Fin 12, ∑ j : Fin 12, qEvMat_3 i j * m i * m j := by
    have hevm := even_lag_moment_of_even hGc hsG hGpar 3
    rw [hevm]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [show ((6 : ℕ).choose 0 : ℝ) = 1 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((6 : ℕ).choose 2 : ℝ) = 15 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((6 : ℕ).choose 4 : ℝ) = 15 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((6 : ℕ).choose 6 : ℝ) = 1 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]]
    have hm_0 := mon_moment_eq_leg_sum hGc ⟨0, by omega⟩
    dsimp only [degAt] at hm_0
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_0
    rw [sum_finK] at hm_0; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_0
    have hm_1 := mon_moment_eq_leg_sum hGc ⟨1, by omega⟩
    dsimp only [degAt] at hm_1
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_1
    rw [sum_finK] at hm_1; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_1
    have hm_2 := mon_moment_eq_leg_sum hGc ⟨2, by omega⟩
    dsimp only [degAt] at hm_2
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_2
    rw [sum_finK] at hm_2; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_2
    have hm_3 := mon_moment_eq_leg_sum hGc ⟨3, by omega⟩
    dsimp only [degAt] at hm_3
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_3
    rw [sum_finK] at hm_3; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_3
    rw [hm_0, hm_1, hm_2, hm_3]
    simp_rw [sum_finK]; dsimp only [qEvMat_3, matAt, listAt, coeffAt, m]; ring
  rw [hexp]
  have hpert := symm_quad_scale_pert qEvMat_3 qEvMat_3_sym abs_aperture_pow_7_sub m
  simp_rw [qEvRowAbs_3_eq] at hpert
  exact hpert

private theorem hEv_bound_4 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hGpar : ∀ u, dilateLogTwo F (-u) = dilateLogTwo F u) :
    let m := halfMoment (dilateLogTwo F)
    apow0_9 * (∑ i : Fin 12, ∑ j : Fin 12, qEvMat_4 i j * m i * m j) -
      (∑ i : Fin 12, (errApow_9 * qEvRowAbs_4 i) * m i ^ 2) ≤
      ((-5366589076364431 / 80000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 8 * autocorr F t) /
        (2 * apertureLogTwo) := by
  intro m
  set G := dilateLogTwo F
  have hA_pos : 0 < apertureLogTwo := apertureLogTwo_pos
  have hdil := dilated_correlation_moment_log_two F 8
  have hdiv : ((-5366589076364431 / 80000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 8 * autocorr F t) /
      (2 * apertureLogTwo) =
      apertureLogTwo ^ 9 * (((-5366589076364431 / 80000000000000000000 : ℝ) / 2) * ∫ t in Ioc (0 : ℝ) 2, t ^ 8 * autocorr G t) := by
    rw [hdil]; field_simp [hA_pos.ne']; ring
  rw [hdiv]
  have hexp : ((-5366589076364431 / 80000000000000000000 : ℝ) / 2) * (∫ t in Ioc (0 : ℝ) 2, t ^ 8 * autocorr G t) =
      ∑ i : Fin 12, ∑ j : Fin 12, qEvMat_4 i j * m i * m j := by
    have hevm := even_lag_moment_of_even hGc hsG hGpar 4
    rw [hevm]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [show ((8 : ℕ).choose 0 : ℝ) = 1 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((8 : ℕ).choose 2 : ℝ) = 28 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((8 : ℕ).choose 4 : ℝ) = 70 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((8 : ℕ).choose 6 : ℝ) = 28 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((8 : ℕ).choose 8 : ℝ) = 1 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]]
    have hm_0 := mon_moment_eq_leg_sum hGc ⟨0, by omega⟩
    dsimp only [degAt] at hm_0
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_0
    rw [sum_finK] at hm_0; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_0
    have hm_1 := mon_moment_eq_leg_sum hGc ⟨1, by omega⟩
    dsimp only [degAt] at hm_1
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_1
    rw [sum_finK] at hm_1; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_1
    have hm_2 := mon_moment_eq_leg_sum hGc ⟨2, by omega⟩
    dsimp only [degAt] at hm_2
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_2
    rw [sum_finK] at hm_2; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_2
    have hm_3 := mon_moment_eq_leg_sum hGc ⟨3, by omega⟩
    dsimp only [degAt] at hm_3
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_3
    rw [sum_finK] at hm_3; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_3
    have hm_4 := mon_moment_eq_leg_sum hGc ⟨4, by omega⟩
    dsimp only [degAt] at hm_4
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_4
    rw [sum_finK] at hm_4; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_4
    rw [hm_0, hm_1, hm_2, hm_3, hm_4]
    simp_rw [sum_finK]; dsimp only [qEvMat_4, matAt, listAt, coeffAt, m]; ring
  rw [hexp]
  have hpert := symm_quad_scale_pert qEvMat_4 qEvMat_4_sym abs_aperture_pow_9_sub m
  simp_rw [qEvRowAbs_4_eq] at hpert
  exact hpert

private theorem hEv_bound_5 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hGpar : ∀ u, dilateLogTwo F (-u) = dilateLogTwo F u) :
    let m := halfMoment (dilateLogTwo F)
    apow0_11 * (∑ i : Fin 12, ∑ j : Fin 12, qEvMat_5 i j * m i * m j) -
      (∑ i : Fin 12, (errApow_11 * qEvRowAbs_5 i) * m i ^ 2) ≤
      ((8726421052567571 / 1280000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 10 * autocorr F t) /
        (2 * apertureLogTwo) := by
  intro m
  set G := dilateLogTwo F
  have hA_pos : 0 < apertureLogTwo := apertureLogTwo_pos
  have hdil := dilated_correlation_moment_log_two F 10
  have hdiv : ((8726421052567571 / 1280000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 10 * autocorr F t) /
      (2 * apertureLogTwo) =
      apertureLogTwo ^ 11 * (((8726421052567571 / 1280000000000000000000 : ℝ) / 2) * ∫ t in Ioc (0 : ℝ) 2, t ^ 10 * autocorr G t) := by
    rw [hdil]; field_simp [hA_pos.ne']; ring
  rw [hdiv]
  have hexp : ((8726421052567571 / 1280000000000000000000 : ℝ) / 2) * (∫ t in Ioc (0 : ℝ) 2, t ^ 10 * autocorr G t) =
      ∑ i : Fin 12, ∑ j : Fin 12, qEvMat_5 i j * m i * m j := by
    have hevm := even_lag_moment_of_even hGc hsG hGpar 5
    rw [hevm]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [show ((10 : ℕ).choose 0 : ℝ) = 1 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((10 : ℕ).choose 2 : ℝ) = 45 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((10 : ℕ).choose 4 : ℝ) = 210 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((10 : ℕ).choose 6 : ℝ) = 210 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((10 : ℕ).choose 8 : ℝ) = 45 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((10 : ℕ).choose 10 : ℝ) = 1 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]]
    have hm_0 := mon_moment_eq_leg_sum hGc ⟨0, by omega⟩
    dsimp only [degAt] at hm_0
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_0
    rw [sum_finK] at hm_0; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_0
    have hm_1 := mon_moment_eq_leg_sum hGc ⟨1, by omega⟩
    dsimp only [degAt] at hm_1
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_1
    rw [sum_finK] at hm_1; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_1
    have hm_2 := mon_moment_eq_leg_sum hGc ⟨2, by omega⟩
    dsimp only [degAt] at hm_2
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_2
    rw [sum_finK] at hm_2; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_2
    have hm_3 := mon_moment_eq_leg_sum hGc ⟨3, by omega⟩
    dsimp only [degAt] at hm_3
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_3
    rw [sum_finK] at hm_3; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_3
    have hm_4 := mon_moment_eq_leg_sum hGc ⟨4, by omega⟩
    dsimp only [degAt] at hm_4
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_4
    rw [sum_finK] at hm_4; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_4
    have hm_5 := mon_moment_eq_leg_sum hGc ⟨5, by omega⟩
    dsimp only [degAt] at hm_5
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_5
    rw [sum_finK] at hm_5; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_5
    rw [hm_0, hm_1, hm_2, hm_3, hm_4, hm_5]
    simp_rw [sum_finK]; dsimp only [qEvMat_5, matAt, listAt, coeffAt, m]; ring
  rw [hexp]
  have hpert := symm_quad_scale_pert qEvMat_5 qEvMat_5_sym abs_aperture_pow_11_sub m
  simp_rw [qEvRowAbs_5_eq] at hpert
  exact hpert

private theorem hEv_bound_6 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hGpar : ∀ u, dilateLogTwo F (-u) = dilateLogTwo F u) :
    let m := halfMoment (dilateLogTwo F)
    apow0_13 * (∑ i : Fin 12, ∑ j : Fin 12, qEvMat_6 i j * m i * m j) -
      (∑ i : Fin 12, (errApow_13 * qEvRowAbs_6 i) * m i ^ 2) ≤
      ((-7163072980652803 / 10240000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 12 * autocorr F t) /
        (2 * apertureLogTwo) := by
  intro m
  set G := dilateLogTwo F
  have hA_pos : 0 < apertureLogTwo := apertureLogTwo_pos
  have hdil := dilated_correlation_moment_log_two F 12
  have hdiv : ((-7163072980652803 / 10240000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 12 * autocorr F t) /
      (2 * apertureLogTwo) =
      apertureLogTwo ^ 13 * (((-7163072980652803 / 10240000000000000000000 : ℝ) / 2) * ∫ t in Ioc (0 : ℝ) 2, t ^ 12 * autocorr G t) := by
    rw [hdil]; field_simp [hA_pos.ne']; ring
  rw [hdiv]
  have hexp : ((-7163072980652803 / 10240000000000000000000 : ℝ) / 2) * (∫ t in Ioc (0 : ℝ) 2, t ^ 12 * autocorr G t) =
      ∑ i : Fin 12, ∑ j : Fin 12, qEvMat_6 i j * m i * m j := by
    have hevm := even_lag_moment_of_even hGc hsG hGpar 6
    rw [hevm]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [show ((12 : ℕ).choose 0 : ℝ) = 1 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((12 : ℕ).choose 2 : ℝ) = 66 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((12 : ℕ).choose 4 : ℝ) = 495 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((12 : ℕ).choose 6 : ℝ) = 924 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((12 : ℕ).choose 8 : ℝ) = 495 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((12 : ℕ).choose 10 : ℝ) = 66 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((12 : ℕ).choose 12 : ℝ) = 1 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]]
    have hm_0 := mon_moment_eq_leg_sum hGc ⟨0, by omega⟩
    dsimp only [degAt] at hm_0
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_0
    rw [sum_finK] at hm_0; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_0
    have hm_1 := mon_moment_eq_leg_sum hGc ⟨1, by omega⟩
    dsimp only [degAt] at hm_1
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_1
    rw [sum_finK] at hm_1; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_1
    have hm_2 := mon_moment_eq_leg_sum hGc ⟨2, by omega⟩
    dsimp only [degAt] at hm_2
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_2
    rw [sum_finK] at hm_2; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_2
    have hm_3 := mon_moment_eq_leg_sum hGc ⟨3, by omega⟩
    dsimp only [degAt] at hm_3
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_3
    rw [sum_finK] at hm_3; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_3
    have hm_4 := mon_moment_eq_leg_sum hGc ⟨4, by omega⟩
    dsimp only [degAt] at hm_4
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_4
    rw [sum_finK] at hm_4; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_4
    have hm_5 := mon_moment_eq_leg_sum hGc ⟨5, by omega⟩
    dsimp only [degAt] at hm_5
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_5
    rw [sum_finK] at hm_5; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_5
    have hm_6 := mon_moment_eq_leg_sum hGc ⟨6, by omega⟩
    dsimp only [degAt] at hm_6
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_6
    rw [sum_finK] at hm_6; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_6
    rw [hm_0, hm_1, hm_2, hm_3, hm_4, hm_5, hm_6]
    simp_rw [sum_finK]; dsimp only [qEvMat_6, matAt, listAt, coeffAt, m]; ring
  rw [hexp]
  have hpert := symm_quad_scale_pert qEvMat_6 qEvMat_6_sym abs_aperture_pow_13_sub m
  simp_rw [qEvRowAbs_6_eq] at hpert
  exact hpert

private theorem hEv_bound_7 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hGpar : ∀ u, dilateLogTwo F (-u) = dilateLogTwo F u) :
    let m := halfMoment (dilateLogTwo F)
    apow0_15 * (∑ i : Fin 12, ∑ j : Fin 12, qEvMat_7 i j * m i * m j) -
      (∑ i : Fin 12, (errApow_15 * qEvRowAbs_7 i) * m i ^ 2) ≤
      ((6237272726078909 / 81920000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 14 * autocorr F t) /
        (2 * apertureLogTwo) := by
  intro m
  set G := dilateLogTwo F
  have hA_pos : 0 < apertureLogTwo := apertureLogTwo_pos
  have hdil := dilated_correlation_moment_log_two F 14
  have hdiv : ((6237272726078909 / 81920000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 14 * autocorr F t) /
      (2 * apertureLogTwo) =
      apertureLogTwo ^ 15 * (((6237272726078909 / 81920000000000000000000 : ℝ) / 2) * ∫ t in Ioc (0 : ℝ) 2, t ^ 14 * autocorr G t) := by
    rw [hdil]; field_simp [hA_pos.ne']; ring
  rw [hdiv]
  have hexp : ((6237272726078909 / 81920000000000000000000 : ℝ) / 2) * (∫ t in Ioc (0 : ℝ) 2, t ^ 14 * autocorr G t) =
      ∑ i : Fin 12, ∑ j : Fin 12, qEvMat_7 i j * m i * m j := by
    have hevm := even_lag_moment_of_even hGc hsG hGpar 7
    rw [hevm]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [show ((14 : ℕ).choose 0 : ℝ) = 1 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((14 : ℕ).choose 2 : ℝ) = 91 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((14 : ℕ).choose 4 : ℝ) = 1001 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((14 : ℕ).choose 6 : ℝ) = 3003 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((14 : ℕ).choose 8 : ℝ) = 3003 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((14 : ℕ).choose 10 : ℝ) = 1001 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((14 : ℕ).choose 12 : ℝ) = 91 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((14 : ℕ).choose 14 : ℝ) = 1 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]]
    have hm_0 := mon_moment_eq_leg_sum hGc ⟨0, by omega⟩
    dsimp only [degAt] at hm_0
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_0
    rw [sum_finK] at hm_0; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_0
    have hm_1 := mon_moment_eq_leg_sum hGc ⟨1, by omega⟩
    dsimp only [degAt] at hm_1
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_1
    rw [sum_finK] at hm_1; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_1
    have hm_2 := mon_moment_eq_leg_sum hGc ⟨2, by omega⟩
    dsimp only [degAt] at hm_2
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_2
    rw [sum_finK] at hm_2; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_2
    have hm_3 := mon_moment_eq_leg_sum hGc ⟨3, by omega⟩
    dsimp only [degAt] at hm_3
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_3
    rw [sum_finK] at hm_3; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_3
    have hm_4 := mon_moment_eq_leg_sum hGc ⟨4, by omega⟩
    dsimp only [degAt] at hm_4
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_4
    rw [sum_finK] at hm_4; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_4
    have hm_5 := mon_moment_eq_leg_sum hGc ⟨5, by omega⟩
    dsimp only [degAt] at hm_5
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_5
    rw [sum_finK] at hm_5; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_5
    have hm_6 := mon_moment_eq_leg_sum hGc ⟨6, by omega⟩
    dsimp only [degAt] at hm_6
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_6
    rw [sum_finK] at hm_6; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_6
    have hm_7 := mon_moment_eq_leg_sum hGc ⟨7, by omega⟩
    dsimp only [degAt] at hm_7
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_7
    rw [sum_finK] at hm_7; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_7
    rw [hm_0, hm_1, hm_2, hm_3, hm_4, hm_5, hm_6, hm_7]
    simp_rw [sum_finK]; dsimp only [qEvMat_7, matAt, listAt, coeffAt, m]; ring
  rw [hexp]
  have hpert := symm_quad_scale_pert qEvMat_7 qEvMat_7_sym abs_aperture_pow_15_sub m
  simp_rw [qEvRowAbs_7_eq] at hpert
  exact hpert

private theorem hEv_bound_8 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hGpar : ∀ u, dilateLogTwo F (-u) = dilateLogTwo F u) :
    let m := halfMoment (dilateLogTwo F)
    apow0_17 * (∑ i : Fin 12, ∑ j : Fin 12, qEvMat_8 i j * m i * m j) -
      (∑ i : Fin 12, (errApow_17 * qEvRowAbs_8 i) * m i ^ 2) ≤
      ((-3260029542583927 / 327680000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 16 * autocorr F t) /
        (2 * apertureLogTwo) := by
  intro m
  set G := dilateLogTwo F
  have hA_pos : 0 < apertureLogTwo := apertureLogTwo_pos
  have hdil := dilated_correlation_moment_log_two F 16
  have hdiv : ((-3260029542583927 / 327680000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 16 * autocorr F t) /
      (2 * apertureLogTwo) =
      apertureLogTwo ^ 17 * (((-3260029542583927 / 327680000000000000000000 : ℝ) / 2) * ∫ t in Ioc (0 : ℝ) 2, t ^ 16 * autocorr G t) := by
    rw [hdil]; field_simp [hA_pos.ne']; ring
  rw [hdiv]
  have hexp : ((-3260029542583927 / 327680000000000000000000 : ℝ) / 2) * (∫ t in Ioc (0 : ℝ) 2, t ^ 16 * autocorr G t) =
      ∑ i : Fin 12, ∑ j : Fin 12, qEvMat_8 i j * m i * m j := by
    have hevm := even_lag_moment_of_even hGc hsG hGpar 8
    rw [hevm]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [show ((16 : ℕ).choose 0 : ℝ) = 1 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((16 : ℕ).choose 2 : ℝ) = 120 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((16 : ℕ).choose 4 : ℝ) = 1820 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((16 : ℕ).choose 6 : ℝ) = 8008 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((16 : ℕ).choose 8 : ℝ) = 12870 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((16 : ℕ).choose 10 : ℝ) = 8008 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((16 : ℕ).choose 12 : ℝ) = 1820 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((16 : ℕ).choose 14 : ℝ) = 120 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((16 : ℕ).choose 16 : ℝ) = 1 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]]
    have hm_0 := mon_moment_eq_leg_sum hGc ⟨0, by omega⟩
    dsimp only [degAt] at hm_0
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_0
    rw [sum_finK] at hm_0; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_0
    have hm_1 := mon_moment_eq_leg_sum hGc ⟨1, by omega⟩
    dsimp only [degAt] at hm_1
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_1
    rw [sum_finK] at hm_1; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_1
    have hm_2 := mon_moment_eq_leg_sum hGc ⟨2, by omega⟩
    dsimp only [degAt] at hm_2
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_2
    rw [sum_finK] at hm_2; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_2
    have hm_3 := mon_moment_eq_leg_sum hGc ⟨3, by omega⟩
    dsimp only [degAt] at hm_3
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_3
    rw [sum_finK] at hm_3; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_3
    have hm_4 := mon_moment_eq_leg_sum hGc ⟨4, by omega⟩
    dsimp only [degAt] at hm_4
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_4
    rw [sum_finK] at hm_4; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_4
    have hm_5 := mon_moment_eq_leg_sum hGc ⟨5, by omega⟩
    dsimp only [degAt] at hm_5
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_5
    rw [sum_finK] at hm_5; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_5
    have hm_6 := mon_moment_eq_leg_sum hGc ⟨6, by omega⟩
    dsimp only [degAt] at hm_6
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_6
    rw [sum_finK] at hm_6; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_6
    have hm_7 := mon_moment_eq_leg_sum hGc ⟨7, by omega⟩
    dsimp only [degAt] at hm_7
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_7
    rw [sum_finK] at hm_7; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_7
    have hm_8 := mon_moment_eq_leg_sum hGc ⟨8, by omega⟩
    dsimp only [degAt] at hm_8
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_8
    rw [sum_finK] at hm_8; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_8
    rw [hm_0, hm_1, hm_2, hm_3, hm_4, hm_5, hm_6, hm_7, hm_8]
    simp_rw [sum_finK]; dsimp only [qEvMat_8, matAt, listAt, coeffAt, m]; ring
  rw [hexp]
  have hpert := symm_quad_scale_pert qEvMat_8 qEvMat_8_sym abs_aperture_pow_17_sub m
  simp_rw [qEvRowAbs_8_eq] at hpert
  exact hpert

private theorem hEv_bound_9 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hGpar : ∀ u, dilateLogTwo F (-u) = dilateLogTwo F u) :
    let m := halfMoment (dilateLogTwo F)
    apow0_19 * (∑ i : Fin 12, ∑ j : Fin 12, qEvMat_9 i j * m i * m j) -
      (∑ i : Fin 12, (errApow_19 * qEvRowAbs_9 i) * m i ^ 2) ≤
      ((519878183231709 / 327680000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 18 * autocorr F t) /
        (2 * apertureLogTwo) := by
  intro m
  set G := dilateLogTwo F
  have hA_pos : 0 < apertureLogTwo := apertureLogTwo_pos
  have hdil := dilated_correlation_moment_log_two F 18
  have hdiv : ((519878183231709 / 327680000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 18 * autocorr F t) /
      (2 * apertureLogTwo) =
      apertureLogTwo ^ 19 * (((519878183231709 / 327680000000000000000000 : ℝ) / 2) * ∫ t in Ioc (0 : ℝ) 2, t ^ 18 * autocorr G t) := by
    rw [hdil]; field_simp [hA_pos.ne']; ring
  rw [hdiv]
  have hexp : ((519878183231709 / 327680000000000000000000 : ℝ) / 2) * (∫ t in Ioc (0 : ℝ) 2, t ^ 18 * autocorr G t) =
      ∑ i : Fin 12, ∑ j : Fin 12, qEvMat_9 i j * m i * m j := by
    have hevm := even_lag_moment_of_even hGc hsG hGpar 9
    rw [hevm]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [show ((18 : ℕ).choose 0 : ℝ) = 1 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((18 : ℕ).choose 2 : ℝ) = 153 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((18 : ℕ).choose 4 : ℝ) = 3060 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((18 : ℕ).choose 6 : ℝ) = 18564 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((18 : ℕ).choose 8 : ℝ) = 43758 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((18 : ℕ).choose 10 : ℝ) = 43758 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((18 : ℕ).choose 12 : ℝ) = 18564 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((18 : ℕ).choose 14 : ℝ) = 3060 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((18 : ℕ).choose 16 : ℝ) = 153 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((18 : ℕ).choose 18 : ℝ) = 1 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]]
    have hm_0 := mon_moment_eq_leg_sum hGc ⟨0, by omega⟩
    dsimp only [degAt] at hm_0
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_0
    rw [sum_finK] at hm_0; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_0
    have hm_1 := mon_moment_eq_leg_sum hGc ⟨1, by omega⟩
    dsimp only [degAt] at hm_1
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_1
    rw [sum_finK] at hm_1; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_1
    have hm_2 := mon_moment_eq_leg_sum hGc ⟨2, by omega⟩
    dsimp only [degAt] at hm_2
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_2
    rw [sum_finK] at hm_2; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_2
    have hm_3 := mon_moment_eq_leg_sum hGc ⟨3, by omega⟩
    dsimp only [degAt] at hm_3
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_3
    rw [sum_finK] at hm_3; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_3
    have hm_4 := mon_moment_eq_leg_sum hGc ⟨4, by omega⟩
    dsimp only [degAt] at hm_4
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_4
    rw [sum_finK] at hm_4; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_4
    have hm_5 := mon_moment_eq_leg_sum hGc ⟨5, by omega⟩
    dsimp only [degAt] at hm_5
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_5
    rw [sum_finK] at hm_5; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_5
    have hm_6 := mon_moment_eq_leg_sum hGc ⟨6, by omega⟩
    dsimp only [degAt] at hm_6
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_6
    rw [sum_finK] at hm_6; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_6
    have hm_7 := mon_moment_eq_leg_sum hGc ⟨7, by omega⟩
    dsimp only [degAt] at hm_7
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_7
    rw [sum_finK] at hm_7; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_7
    have hm_8 := mon_moment_eq_leg_sum hGc ⟨8, by omega⟩
    dsimp only [degAt] at hm_8
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_8
    rw [sum_finK] at hm_8; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_8
    have hm_9 := mon_moment_eq_leg_sum hGc ⟨9, by omega⟩
    dsimp only [degAt] at hm_9
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_9
    rw [sum_finK] at hm_9; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_9
    rw [hm_0, hm_1, hm_2, hm_3, hm_4, hm_5, hm_6, hm_7, hm_8, hm_9]
    simp_rw [sum_finK]; dsimp only [qEvMat_9, matAt, listAt, coeffAt, m]; ring
  rw [hexp]
  have hpert := symm_quad_scale_pert qEvMat_9 qEvMat_9_sym abs_aperture_pow_19_sub m
  simp_rw [qEvRowAbs_9_eq] at hpert
  exact hpert

private theorem hEv_bound_10 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hGpar : ∀ u, dilateLogTwo F (-u) = dilateLogTwo F u) :
    let m := halfMoment (dilateLogTwo F)
    apow0_21 * (∑ i : Fin 12, ∑ j : Fin 12, qEvMat_10 i j * m i * m j) -
      (∑ i : Fin 12, (errApow_21 * qEvRowAbs_10 i) * m i ^ 2) ≤
      ((-4669432996809649 / 20971520000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 20 * autocorr F t) /
        (2 * apertureLogTwo) := by
  intro m
  set G := dilateLogTwo F
  have hA_pos : 0 < apertureLogTwo := apertureLogTwo_pos
  have hdil := dilated_correlation_moment_log_two F 20
  have hdiv : ((-4669432996809649 / 20971520000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 20 * autocorr F t) /
      (2 * apertureLogTwo) =
      apertureLogTwo ^ 21 * (((-4669432996809649 / 20971520000000000000000000 : ℝ) / 2) * ∫ t in Ioc (0 : ℝ) 2, t ^ 20 * autocorr G t) := by
    rw [hdil]; field_simp [hA_pos.ne']; ring
  rw [hdiv]
  have hexp : ((-4669432996809649 / 20971520000000000000000000 : ℝ) / 2) * (∫ t in Ioc (0 : ℝ) 2, t ^ 20 * autocorr G t) =
      ∑ i : Fin 12, ∑ j : Fin 12, qEvMat_10 i j * m i * m j := by
    have hevm := even_lag_moment_of_even hGc hsG hGpar 10
    rw [hevm]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [show ((20 : ℕ).choose 0 : ℝ) = 1 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((20 : ℕ).choose 2 : ℝ) = 190 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((20 : ℕ).choose 4 : ℝ) = 4845 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((20 : ℕ).choose 6 : ℝ) = 38760 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((20 : ℕ).choose 8 : ℝ) = 125970 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((20 : ℕ).choose 10 : ℝ) = 184756 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((20 : ℕ).choose 12 : ℝ) = 125970 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((20 : ℕ).choose 14 : ℝ) = 38760 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((20 : ℕ).choose 16 : ℝ) = 4845 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((20 : ℕ).choose 18 : ℝ) = 190 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((20 : ℕ).choose 20 : ℝ) = 1 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]]
    have hm_0 := mon_moment_eq_leg_sum hGc ⟨0, by omega⟩
    dsimp only [degAt] at hm_0
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_0
    rw [sum_finK] at hm_0; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_0
    have hm_1 := mon_moment_eq_leg_sum hGc ⟨1, by omega⟩
    dsimp only [degAt] at hm_1
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_1
    rw [sum_finK] at hm_1; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_1
    have hm_2 := mon_moment_eq_leg_sum hGc ⟨2, by omega⟩
    dsimp only [degAt] at hm_2
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_2
    rw [sum_finK] at hm_2; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_2
    have hm_3 := mon_moment_eq_leg_sum hGc ⟨3, by omega⟩
    dsimp only [degAt] at hm_3
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_3
    rw [sum_finK] at hm_3; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_3
    have hm_4 := mon_moment_eq_leg_sum hGc ⟨4, by omega⟩
    dsimp only [degAt] at hm_4
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_4
    rw [sum_finK] at hm_4; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_4
    have hm_5 := mon_moment_eq_leg_sum hGc ⟨5, by omega⟩
    dsimp only [degAt] at hm_5
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_5
    rw [sum_finK] at hm_5; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_5
    have hm_6 := mon_moment_eq_leg_sum hGc ⟨6, by omega⟩
    dsimp only [degAt] at hm_6
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_6
    rw [sum_finK] at hm_6; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_6
    have hm_7 := mon_moment_eq_leg_sum hGc ⟨7, by omega⟩
    dsimp only [degAt] at hm_7
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_7
    rw [sum_finK] at hm_7; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_7
    have hm_8 := mon_moment_eq_leg_sum hGc ⟨8, by omega⟩
    dsimp only [degAt] at hm_8
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_8
    rw [sum_finK] at hm_8; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_8
    have hm_9 := mon_moment_eq_leg_sum hGc ⟨9, by omega⟩
    dsimp only [degAt] at hm_9
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_9
    rw [sum_finK] at hm_9; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_9
    have hm_10 := mon_moment_eq_leg_sum hGc ⟨10, by omega⟩
    dsimp only [degAt] at hm_10
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_10
    rw [sum_finK] at hm_10; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_10
    rw [hm_0, hm_1, hm_2, hm_3, hm_4, hm_5, hm_6, hm_7, hm_8, hm_9, hm_10]
    simp_rw [sum_finK]; dsimp only [qEvMat_10, matAt, listAt, coeffAt, m]; ring
  rw [hexp]
  have hpert := symm_quad_scale_pert qEvMat_10 qEvMat_10_sym abs_aperture_pow_21_sub m
  simp_rw [qEvRowAbs_10_eq] at hpert
  exact hpert

private theorem hEv_bound_11 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hGpar : ∀ u, dilateLogTwo F (-u) = dilateLogTwo F u) :
    let m := halfMoment (dilateLogTwo F)
    apow0_23 * (∑ i : Fin 12, ∑ j : Fin 12, qEvMat_11 i j * m i * m j) -
      (∑ i : Fin 12, (errApow_23 * qEvRowAbs_11 i) * m i ^ 2) ≤
      ((1377431922843341 / 83886080000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 22 * autocorr F t) /
        (2 * apertureLogTwo) := by
  intro m
  set G := dilateLogTwo F
  have hA_pos : 0 < apertureLogTwo := apertureLogTwo_pos
  have hdil := dilated_correlation_moment_log_two F 22
  have hdiv : ((1377431922843341 / 83886080000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 22 * autocorr F t) /
      (2 * apertureLogTwo) =
      apertureLogTwo ^ 23 * (((1377431922843341 / 83886080000000000000000000 : ℝ) / 2) * ∫ t in Ioc (0 : ℝ) 2, t ^ 22 * autocorr G t) := by
    rw [hdil]; field_simp [hA_pos.ne']; ring
  rw [hdiv]
  have hexp : ((1377431922843341 / 83886080000000000000000000 : ℝ) / 2) * (∫ t in Ioc (0 : ℝ) 2, t ^ 22 * autocorr G t) =
      ∑ i : Fin 12, ∑ j : Fin 12, qEvMat_11 i j * m i * m j := by
    have hevm := even_lag_moment_of_even hGc hsG hGpar 11
    rw [hevm]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [show ((22 : ℕ).choose 0 : ℝ) = 1 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((22 : ℕ).choose 2 : ℝ) = 231 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((22 : ℕ).choose 4 : ℝ) = 7315 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((22 : ℕ).choose 6 : ℝ) = 74613 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((22 : ℕ).choose 8 : ℝ) = 319770 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((22 : ℕ).choose 10 : ℝ) = 646646 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((22 : ℕ).choose 12 : ℝ) = 646646 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((22 : ℕ).choose 14 : ℝ) = 319770 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((22 : ℕ).choose 16 : ℝ) = 74613 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((22 : ℕ).choose 18 : ℝ) = 7315 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((22 : ℕ).choose 20 : ℝ) = 231 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((22 : ℕ).choose 22 : ℝ) = 1 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]]
    have hm_0 := mon_moment_eq_leg_sum hGc ⟨0, by omega⟩
    dsimp only [degAt] at hm_0
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_0
    rw [sum_finK] at hm_0; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_0
    have hm_1 := mon_moment_eq_leg_sum hGc ⟨1, by omega⟩
    dsimp only [degAt] at hm_1
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_1
    rw [sum_finK] at hm_1; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_1
    have hm_2 := mon_moment_eq_leg_sum hGc ⟨2, by omega⟩
    dsimp only [degAt] at hm_2
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_2
    rw [sum_finK] at hm_2; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_2
    have hm_3 := mon_moment_eq_leg_sum hGc ⟨3, by omega⟩
    dsimp only [degAt] at hm_3
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_3
    rw [sum_finK] at hm_3; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_3
    have hm_4 := mon_moment_eq_leg_sum hGc ⟨4, by omega⟩
    dsimp only [degAt] at hm_4
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_4
    rw [sum_finK] at hm_4; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_4
    have hm_5 := mon_moment_eq_leg_sum hGc ⟨5, by omega⟩
    dsimp only [degAt] at hm_5
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_5
    rw [sum_finK] at hm_5; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_5
    have hm_6 := mon_moment_eq_leg_sum hGc ⟨6, by omega⟩
    dsimp only [degAt] at hm_6
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_6
    rw [sum_finK] at hm_6; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_6
    have hm_7 := mon_moment_eq_leg_sum hGc ⟨7, by omega⟩
    dsimp only [degAt] at hm_7
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_7
    rw [sum_finK] at hm_7; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_7
    have hm_8 := mon_moment_eq_leg_sum hGc ⟨8, by omega⟩
    dsimp only [degAt] at hm_8
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_8
    rw [sum_finK] at hm_8; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_8
    have hm_9 := mon_moment_eq_leg_sum hGc ⟨9, by omega⟩
    dsimp only [degAt] at hm_9
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_9
    rw [sum_finK] at hm_9; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_9
    have hm_10 := mon_moment_eq_leg_sum hGc ⟨10, by omega⟩
    dsimp only [degAt] at hm_10
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_10
    rw [sum_finK] at hm_10; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_10
    have hm_11 := mon_moment_eq_leg_sum hGc ⟨11, by omega⟩
    dsimp only [degAt] at hm_11
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_11
    rw [sum_finK] at hm_11; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_11
    rw [hm_0, hm_1, hm_2, hm_3, hm_4, hm_5, hm_6, hm_7, hm_8, hm_9, hm_10, hm_11]
    simp_rw [sum_finK]; dsimp only [qEvMat_11, matAt, listAt, coeffAt, m]; ring
  rw [hexp]
  have hpert := symm_quad_scale_pert qEvMat_11 qEvMat_11_sym abs_aperture_pow_23_sub m
  simp_rw [qEvRowAbs_11_eq] at hpert
  exact hpert

private theorem hIterP_eq_0 {G : ℝ → ℝ}
    (hLowProj : ∀ y : ℝ, lowProj G 24 y = ∑ k : Fin 12, halfMoment G k * basisFn k y) (y : ℝ) :
    iterPrim 2 (lowProj G 24) y =
      ∑ j : Fin 12, halfMoment G j * polyEval (match j.1 with | 0 => iBasis_2_0 | 1 => iBasis_2_1 | 2 => iBasis_2_2 | 3 => iBasis_2_3 | 4 => iBasis_2_4 | 5 => iBasis_2_5 | 6 => iBasis_2_6 | 7 => iBasis_2_7 | 8 => iBasis_2_8 | 9 => iBasis_2_9 | 10 => iBasis_2_10 | 11 => iBasis_2_11 | _ => []) y := by
  have hlp_eq : lowProj G 24 = fun u => ∑ j : Fin 12, halfMoment G j * basisFn j u := funext hLowProj
  rw [hlp_eq, iterPrim_finset_sum Finset.univ (f := fun j u => halfMoment G j * basisFn j u)
    (fun j _ => continuous_const.mul (continuous_const.mul (continuous_legP _))) 2 y]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iterPrim_const_mul (f := basisFn j) (continuous_const.mul (continuous_legP _)) (halfMoment G j) 2 y]
  congr 1; rcases j with ⟨jv, hjv⟩; interval_cases jv
  · exact iterPrim_basis_2_0 y
  · exact iterPrim_basis_2_1 y
  · exact iterPrim_basis_2_2 y
  · exact iterPrim_basis_2_3 y
  · exact iterPrim_basis_2_4 y
  · exact iterPrim_basis_2_5 y
  · exact iterPrim_basis_2_6 y
  · exact iterPrim_basis_2_7 y
  · exact iterPrim_basis_2_8 y
  · exact iterPrim_basis_2_9 y
  · exact iterPrim_basis_2_10 y
  · exact iterPrim_basis_2_11 y

private theorem hPP_eq_0 {G : ℝ → ℝ}
    (hLowProj : ∀ y : ℝ, lowProj G 24 y = ∑ k : Fin 12, halfMoment G k * basisFn k y) :
    ((1 / 48 : ℝ) * ((1 : ℕ).factorial : ℝ)) *
      (∫ y in (-1 : ℝ)..1, lowProj G 24 y * iterPrim 2 (lowProj G 24) y) =
      ∑ i : Fin 12, ∑ j : Fin 12, qOddMat_0 i j * halfMoment G i * halfMoment G j := by
  set m := halfMoment G
  have hfn : ∀ y : ℝ, lowProj G 24 y * iterPrim 2 (lowProj G 24) y =
      ∑ i : Fin 12, ∑ j : Fin 12, (m i * m j) *
        (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y *
         polyEval (match j.1 with | 0 => iBasis_2_0 | 1 => iBasis_2_1 | 2 => iBasis_2_2 | 3 => iBasis_2_3 | 4 => iBasis_2_4 | 5 => iBasis_2_5 | 6 => iBasis_2_6 | 7 => iBasis_2_7 | 8 => iBasis_2_8 | 9 => iBasis_2_9 | 10 => iBasis_2_10 | 11 => iBasis_2_11 | _ => []) y) := fun y => by
    rw [hLowProj y, hIterP_eq_0 hLowProj y, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    have hb : basisFn i y = polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y := by
      rcases i with ⟨iv, hiv⟩; interval_cases iv
      · exact iterPrim_basis_0_0 y
      · exact iterPrim_basis_0_1 y
      · exact iterPrim_basis_0_2 y
      · exact iterPrim_basis_0_3 y
      · exact iterPrim_basis_0_4 y
      · exact iterPrim_basis_0_5 y
      · exact iterPrim_basis_0_6 y
      · exact iterPrim_basis_0_7 y
      · exact iterPrim_basis_0_8 y
      · exact iterPrim_basis_0_9 y
      · exact iterPrim_basis_0_10 y
      · exact iterPrim_basis_0_11 y
    rw [hb]; dsimp only [m]; ring
  simp_rw [hfn]
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (show Continuous fun y : ℝ => ∑ j : Fin 12, (m i * m j) *
      (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y *
       polyEval (match j.1 with | 0 => iBasis_2_0 | 1 => iBasis_2_1 | 2 => iBasis_2_2 | 3 => iBasis_2_3 | 4 => iBasis_2_4 | 5 => iBasis_2_5 | 6 => iBasis_2_6 | 7 => iBasis_2_7 | 8 => iBasis_2_8 | 9 => iBasis_2_9 | 10 => iBasis_2_10 | 11 => iBasis_2_11 | _ => []) y) from
      continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_polyEval _).mul (continuous_polyEval _))).intervalIntegrable (-1) 1]
  have hEach : ∀ (i j : Fin 12), (∫ y in (-1 : ℝ)..1,
      (m i * m j) * (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y *
        polyEval (match j.1 with | 0 => iBasis_2_0 | 1 => iBasis_2_1 | 2 => iBasis_2_2 | 3 => iBasis_2_3 | 4 => iBasis_2_4 | 5 => iBasis_2_5 | 6 => iBasis_2_6 | 7 => iBasis_2_7 | 8 => iBasis_2_8 | 9 => iBasis_2_9 | 10 => iBasis_2_10 | 11 => iBasis_2_11 | _ => []) y)) =
      (m i * m j) * (ApertureLogTwo.matQ mPPRawQ_0 i.1 j.1 : ℝ) := fun i j => by
    rw [intervalIntegral.integral_const_mul, int_pp_0 i j]
  have hSumI : ∀ i : Fin 12, (∫ y in (-1 : ℝ)..1, ∑ j : Fin 12,
      (m i * m j) * (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y *
        polyEval (match j.1 with | 0 => iBasis_2_0 | 1 => iBasis_2_1 | 2 => iBasis_2_2 | 3 => iBasis_2_3 | 4 => iBasis_2_4 | 5 => iBasis_2_5 | 6 => iBasis_2_6 | 7 => iBasis_2_7 | 8 => iBasis_2_8 | 9 => iBasis_2_9 | 10 => iBasis_2_10 | 11 => iBasis_2_11 | _ => []) y)) =
      ∑ j : Fin 12, (m i * m j) * (ApertureLogTwo.matQ mPPRawQ_0 i.1 j.1 : ℝ) := fun i => by
    rw [intervalIntegral.integral_finsetSum fun j _ =>
      (show Continuous fun y : ℝ => (m i * m j) *
        (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y *
         polyEval (match j.1 with | 0 => iBasis_2_0 | 1 => iBasis_2_1 | 2 => iBasis_2_2 | 3 => iBasis_2_3 | 4 => iBasis_2_4 | 5 => iBasis_2_5 | 6 => iBasis_2_6 | 7 => iBasis_2_7 | 8 => iBasis_2_8 | 9 => iBasis_2_9 | 10 => iBasis_2_10 | 11 => iBasis_2_11 | _ => []) y) from
        continuous_const.mul ((continuous_polyEval _).mul (continuous_polyEval _))).intervalIntegrable (-1) 1]
    exact Finset.sum_congr rfl fun j _ => hEach i j
  rw [show ((1 : ℕ).factorial : ℝ) = 1 by norm_num [Nat.factorial]]
  simp_rw [hSumI, sum_finK, matQ_eq_qcoeffAt]
  dsimp only [mPPRawQ_0, qcoeffAt, qlistAt, qOddMat_0, matAt, listAt, coeffAt, m]
  simp only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_zero]
  ring

private theorem hOdd_bound_0 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hLowProj : ∀ y : ℝ, lowProj (dilateLogTwo F) 24 y =
      ∑ k : Fin 12, halfMoment (dilateLogTwo F) k * basisFn k y)
    (hHopp : ∀ r : ℕ, regionalLegendreMoment (dilateLogTwo F) (24 + (2 * r + 1)) = 0) :
    let G := dilateLogTwo F
    let m := halfMoment G
    let M_res := (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 24 x) ^ 2) / 2
    apow0_2 * (∑ i : Fin 12, ∑ j : Fin 12, qOddMat_0 i j * m i * m j) -
      (∑ i : Fin 12, (errApow_2 * qOddRowAbs_0 i) * m i ^ 2) -
      ((6261802804445623152330125031301818197576522398243856809 / 62500000000000000000000000000000000000000000000000000000 : ℝ) * ∑ r ∈ Finset.range 1,
        ((2 * ↑(24 + 2 * r) + 1) / 2) * (∑ i : Fin 12, m i * gHi_0 i r) ^ 2) -
      ((1 / 500 : ℝ) + (1601510046394004748890341793893822096964129967681123 / 197392088021787172376357642657862688463432000000000000 : ℝ)) * M_res ≤
      ((1 / 24 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 1 * autocorr F t) /
        (2 * apertureLogTwo) := by
  intro G m M_res
  have hA_pos : 0 < apertureLogTwo := apertureLogTwo_pos
  set R_res : ℝ → ℝ := fun x => G x - lowProj G 24 x
  have hRc : Continuous R_res := hGc.sub (contDiff_lowProj G _ (k := 0)).continuous
  have hMres_nn : 0 ≤ M_res := div_nonneg (setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _) (by norm_num)
  have hIntR2 : (∫ x in Icc (-1 : ℝ) 1, R_res x ^ 2) = 2 * M_res := by dsimp [R_res, M_res]; ring
  have hpi_lo : piLo ≤ Real.pi := (pi_bounds_d20).1
  have hpi_pos : 0 < piLo := by norm_num [piLo]
  have h4pi : 4 / Real.pi ^ 2 ≤ 4 / piLo ^ 2 := by
    have hp2 : piLo ^ 2 ≤ Real.pi ^ 2 := pow_le_pow_left₀ hpi_pos.le hpi_lo 2
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hp2
  have hdil := dilated_correlation_moment_log_two F 1
  have hdec := odd_lag_moment_lowProj_decomp hGc hsG (m := 24) (q := 0) (by omega)
  change (∫ t in Ioc (0 : ℝ) 2, t ^ 1 * autocorr G t) =
    ((1 : ℕ).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, lowProj G 24 y * iterPrim 2 (lowProj G 24) y) +
    2 * ((1 : ℕ).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, R_res y * iterPrim 2 (lowProj G 24) y) +
    (-1 : ℝ) ^ (0 + 1) * ((1 : ℕ).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, iterPrim (0 + 1) R_res y ^ 2) at hdec
  have hPP := hPP_eq_0 hLowProj
  have hPP_pert := symm_quad_scale_pert qOddMat_0 qOddMat_0_sym abs_aperture_pow_2_sub m
  simp_rw [qOddRowAbs_0_eq] at hPP_pert
  have hWirt := iterPrim_sq_le_wirtinger hRc (m := 24) (fun n hn => sub_lowProj_moment_lt hGc hn) (0 + 1) (by omega)
  have hWirt' : (∫ y in (-1 : ℝ)..1, iterPrim (0 + 1) R_res y ^ 2) ≤ (4 / piLo ^ 2) ^ (0 + 1) * (2 * M_res) := by
    rw [hIntR2] at hWirt
    exact hWirt.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h4pi (0 + 1)) (by positivity))
  have hCross := high_mode_cross_sq_le hGc (m := 24) (q := 0) (by omega) hHopp
  change (∫ y in (-1 : ℝ)..1, R_res y * iterPrim 2 (lowProj G 24) y) ^ 2 ≤
    (∑ r ∈ Finset.range (0 + 1), ((2 * ↑(24 + 2 * r) + 1) / 2) *
      regionalLegendreMoment (iterPrim 2 (lowProj G 24)) (24 + 2 * r) ^ 2) *
    (∫ y in Icc (-1 : ℝ) 1, R_res y ^ 2) at hCross
  rw [hIntR2] at hCross
  have hMomLin : ∀ r ∈ Finset.range (0 + 1), regionalLegendreMoment (iterPrim 2 (lowProj G 24)) (24 + 2 * r) =
      ∑ i : Fin 12, m i * gHi_0 i r := fun r hr => by
    have hlin : regionalLegendreMoment (iterPrim 2 (lowProj G 24)) (24 + 2 * r) =
        ∑ i : Fin 12, m i * regionalLegendreMoment (polyEval (match i.1 with | 0 => iBasis_2_0 | 1 => iBasis_2_1 | 2 => iBasis_2_2 | 3 => iBasis_2_3 | 4 => iBasis_2_4 | 5 => iBasis_2_5 | 6 => iBasis_2_6 | 7 => iBasis_2_7 | 8 => iBasis_2_8 | 9 => iBasis_2_9 | 10 => iBasis_2_10 | 11 => iBasis_2_11 | _ => [])) (24 + 2 * r) := by
      unfold regionalLegendreMoment
      have hfn : ∀ x : ℝ, iterPrim 2 (lowProj G 24) x * legP (24 + 2 * r) x =
          ∑ i : Fin 12, m i * (polyEval (match i.1 with | 0 => iBasis_2_0 | 1 => iBasis_2_1 | 2 => iBasis_2_2 | 3 => iBasis_2_3 | 4 => iBasis_2_4 | 5 => iBasis_2_5 | 6 => iBasis_2_6 | 7 => iBasis_2_7 | 8 => iBasis_2_8 | 9 => iBasis_2_9 | 10 => iBasis_2_10 | 11 => iBasis_2_11 | _ => []) x * legP (24 + 2 * r) x) := fun x => by
        rw [hIterP_eq_0 hLowProj x, Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by dsimp only [m]; ring
      simp_rw [hfn]
      rw [integral_finsetSum _ fun i _ =>
        (show Continuous fun x : ℝ => m i * (polyEval (match i.1 with | 0 => iBasis_2_0 | 1 => iBasis_2_1 | 2 => iBasis_2_2 | 3 => iBasis_2_3 | 4 => iBasis_2_4 | 5 => iBasis_2_5 | 6 => iBasis_2_6 | 7 => iBasis_2_7 | 8 => iBasis_2_8 | 9 => iBasis_2_9 | 10 => iBasis_2_10 | 11 => iBasis_2_11 | _ => []) x * legP (24 + 2 * r) x) from
          continuous_const.mul ((continuous_polyEval _).mul (continuous_legP _))).integrableOn_Icc]
      exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    rw [hlin]; exact Finset.sum_congr rfl fun i _ => by rw [gHi_eq_0 i r hr]
  set A_sp : ℝ := ∑ r ∈ Finset.range (0 + 1), ((2 * ↑(24 + 2 * r) + 1) / 2) *
    (∑ i : Fin 12, m i * gHi_0 i r) ^ 2
  have hAsp_eq : (∑ r ∈ Finset.range (0 + 1), ((2 * ↑(24 + 2 * r) + 1) / 2) *
      regionalLegendreMoment (iterPrim 2 (lowProj G 24)) (24 + 2 * r) ^ 2) = A_sp :=
    Finset.sum_congr rfl fun r hr => by rw [hMomLin r hr]
  rw [hAsp_eq] at hCross
  set w_true : ℝ := ((1 / 48 : ℝ) * ((1 : ℕ).factorial : ℝ)) * apertureLogTwo ^ 2
  have hw_nn : 0 ≤ w_true := by dsimp [w_true]; positivity
  have hw_le : w_true ≤ (2502359447490632420141159053 / 250000000000000000000000000000 : ℝ) := by
    obtain ⟨_, h2u⟩ := log_two_bounds_d26; dsimp only [w_true]; unfold apertureLogTwo
    have hp : (Real.log 2) ^ 2 ≤ logTwoHi ^ 2 := pow_le_pow_left₀ (apertureLogTwo_pos.le) h2u 2
    have hc : ((1 / 48 : ℝ) * ((1 : ℕ).factorial : ℝ)) * logTwoHi ^ 2 ≤ (2502359447490632420141159053 / 250000000000000000000000000000 : ℝ) := by
      norm_num [Nat.factorial, logTwoHi]
    nlinarith [hp, hc, (show (0 : ℝ) ≤ (1 / 48 : ℝ) * ((1 : ℕ).factorial : ℝ) by positivity)]
  have hAsp_nn : 0 ≤ A_sp := Finset.sum_nonneg fun r _ => mul_nonneg (by positivity) (sq_nonneg _)
  set I_RP : ℝ := ∫ y in (-1 : ℝ)..1, R_res y * iterPrim 2 (lowProj G 24) y
  have hY2 : (w_true * I_RP) ^ 2 ≤ ((2502359447490632420141159053 / 250000000000000000000000000000 : ℝ)) ^ 2 * (A_sp * (2 * M_res)) := by
    rw [mul_pow]
    have hw2 : w_true ^ 2 ≤ ((2502359447490632420141159053 / 250000000000000000000000000000 : ℝ)) ^ 2 := pow_le_pow_left₀ hw_nn hw_le 2
    exact (mul_le_mul_of_nonneg_right hw2 (sq_nonneg I_RP)).trans (mul_le_mul_of_nonneg_left hCross (sq_nonneg _))
  have hy := cross_spillover_young (by norm_num : (0 : ℝ) ≤ (2502359447490632420141159053 / 250000000000000000000000000000 : ℝ)) hAsp_nn hMres_nn
    (by norm_num : (0 : ℝ) < (1 / 500 : ℝ)) hY2
  have hw_wirt : w_true * (∫ y in (-1 : ℝ)..1, iterPrim (0 + 1) R_res y ^ 2) ≤ (1601510046394004748890341793893822096964129967681123 / 197392088021787172376357642657862688463432000000000000 : ℝ) * M_res := by
    have hw_ex : w_true ≤ (1601510046394004748890341793893822096964129967681123 / 160000000000000000000000000000000000000000000000000000 : ℝ) := by
      obtain ⟨_, h2u⟩ := log_two_bounds_d26; dsimp only [w_true]; unfold apertureLogTwo
      have hp : (Real.log 2) ^ 2 ≤ logTwoHi ^ 2 := pow_le_pow_left₀ (apertureLogTwo_pos.le) h2u 2
      have hc : ((1 / 48 : ℝ) * ((1 : ℕ).factorial : ℝ)) * logTwoHi ^ 2 = (1601510046394004748890341793893822096964129967681123 / 160000000000000000000000000000000000000000000000000000 : ℝ) := by
        norm_num [Nat.factorial, logTwoHi]
      nlinarith [hp, hc, (show (0 : ℝ) ≤ (1 / 48 : ℝ) * ((1 : ℕ).factorial : ℝ) by positivity)]
    have h1 := mul_le_mul hw_ex hWirt' (by rw [intervalIntegral.integral_of_le (by norm_num)]; exact setIntegral_nonneg measurableSet_Ioc fun _ _ => sq_nonneg _) (by norm_num)
    have h2 : (1601510046394004748890341793893822096964129967681123 / 160000000000000000000000000000000000000000000000000000 : ℝ) * ((4 / piLo ^ 2) ^ (0 + 1) * (2 * M_res)) = (1601510046394004748890341793893822096964129967681123 / 197392088021787172376357642657862688463432000000000000 : ℝ) * M_res := by
      norm_num [piLo]; ring
    linarith
  have hdiv_tot : ((1 / 24 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 1 * autocorr F t) / (2 * apertureLogTwo) =
      apertureLogTwo ^ 2 * (((1 / 48 : ℝ) * ((1 : ℕ).factorial : ℝ)) *
        (∫ y in (-1 : ℝ)..1, lowProj G 24 y * iterPrim 2 (lowProj G 24) y)) +
      (1 : ℝ) * (2 * (w_true * I_RP)) -
      w_true * (∫ y in (-1 : ℝ)..1, iterPrim (0 + 1) R_res y ^ 2) := by
    rw [hdil, hdec]; dsimp [w_true, I_RP]; field_simp [hA_pos.ne']; norm_num; ring
  rw [hdiv_tot, hPP]
  have hsc_eq : (2 * ((2502359447490632420141159053 / 250000000000000000000000000000 : ℝ)) ^ 2 / (1 / 500 : ℝ)) = (6261802804445623152330125031301818197576522398243856809 / 62500000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num
  rw [hsc_eq] at hy
  linarith [hPP_pert, hy.1, hw_wirt]

private theorem hIterP_eq_1 {G : ℝ → ℝ}
    (hLowProj : ∀ y : ℝ, lowProj G 24 y = ∑ k : Fin 12, halfMoment G k * basisFn k y) (y : ℝ) :
    iterPrim 4 (lowProj G 24) y =
      ∑ j : Fin 12, halfMoment G j * polyEval (match j.1 with | 0 => iBasis_4_0 | 1 => iBasis_4_1 | 2 => iBasis_4_2 | 3 => iBasis_4_3 | 4 => iBasis_4_4 | 5 => iBasis_4_5 | 6 => iBasis_4_6 | 7 => iBasis_4_7 | 8 => iBasis_4_8 | 9 => iBasis_4_9 | 10 => iBasis_4_10 | 11 => iBasis_4_11 | _ => []) y := by
  have hlp_eq : lowProj G 24 = fun u => ∑ j : Fin 12, halfMoment G j * basisFn j u := funext hLowProj
  rw [hlp_eq, iterPrim_finset_sum Finset.univ (f := fun j u => halfMoment G j * basisFn j u)
    (fun j _ => continuous_const.mul (continuous_const.mul (continuous_legP _))) 4 y]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iterPrim_const_mul (f := basisFn j) (continuous_const.mul (continuous_legP _)) (halfMoment G j) 4 y]
  congr 1; rcases j with ⟨jv, hjv⟩; interval_cases jv
  · exact iterPrim_basis_4_0 y
  · exact iterPrim_basis_4_1 y
  · exact iterPrim_basis_4_2 y
  · exact iterPrim_basis_4_3 y
  · exact iterPrim_basis_4_4 y
  · exact iterPrim_basis_4_5 y
  · exact iterPrim_basis_4_6 y
  · exact iterPrim_basis_4_7 y
  · exact iterPrim_basis_4_8 y
  · exact iterPrim_basis_4_9 y
  · exact iterPrim_basis_4_10 y
  · exact iterPrim_basis_4_11 y

private theorem hPP_eq_1 {G : ℝ → ℝ}
    (hLowProj : ∀ y : ℝ, lowProj G 24 y = ∑ k : Fin 12, halfMoment G k * basisFn k y) :
    ((-7 / 11520 : ℝ) * ((3 : ℕ).factorial : ℝ)) *
      (∫ y in (-1 : ℝ)..1, lowProj G 24 y * iterPrim 4 (lowProj G 24) y) =
      ∑ i : Fin 12, ∑ j : Fin 12, qOddMat_1 i j * halfMoment G i * halfMoment G j := by
  set m := halfMoment G
  have hfn : ∀ y : ℝ, lowProj G 24 y * iterPrim 4 (lowProj G 24) y =
      ∑ i : Fin 12, ∑ j : Fin 12, (m i * m j) *
        (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y *
         polyEval (match j.1 with | 0 => iBasis_4_0 | 1 => iBasis_4_1 | 2 => iBasis_4_2 | 3 => iBasis_4_3 | 4 => iBasis_4_4 | 5 => iBasis_4_5 | 6 => iBasis_4_6 | 7 => iBasis_4_7 | 8 => iBasis_4_8 | 9 => iBasis_4_9 | 10 => iBasis_4_10 | 11 => iBasis_4_11 | _ => []) y) := fun y => by
    rw [hLowProj y, hIterP_eq_1 hLowProj y, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    have hb : basisFn i y = polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y := by
      rcases i with ⟨iv, hiv⟩; interval_cases iv
      · exact iterPrim_basis_0_0 y
      · exact iterPrim_basis_0_1 y
      · exact iterPrim_basis_0_2 y
      · exact iterPrim_basis_0_3 y
      · exact iterPrim_basis_0_4 y
      · exact iterPrim_basis_0_5 y
      · exact iterPrim_basis_0_6 y
      · exact iterPrim_basis_0_7 y
      · exact iterPrim_basis_0_8 y
      · exact iterPrim_basis_0_9 y
      · exact iterPrim_basis_0_10 y
      · exact iterPrim_basis_0_11 y
    rw [hb]; dsimp only [m]; ring
  simp_rw [hfn]
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (show Continuous fun y : ℝ => ∑ j : Fin 12, (m i * m j) *
      (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y *
       polyEval (match j.1 with | 0 => iBasis_4_0 | 1 => iBasis_4_1 | 2 => iBasis_4_2 | 3 => iBasis_4_3 | 4 => iBasis_4_4 | 5 => iBasis_4_5 | 6 => iBasis_4_6 | 7 => iBasis_4_7 | 8 => iBasis_4_8 | 9 => iBasis_4_9 | 10 => iBasis_4_10 | 11 => iBasis_4_11 | _ => []) y) from
      continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_polyEval _).mul (continuous_polyEval _))).intervalIntegrable (-1) 1]
  have hEach : ∀ (i j : Fin 12), (∫ y in (-1 : ℝ)..1,
      (m i * m j) * (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y *
        polyEval (match j.1 with | 0 => iBasis_4_0 | 1 => iBasis_4_1 | 2 => iBasis_4_2 | 3 => iBasis_4_3 | 4 => iBasis_4_4 | 5 => iBasis_4_5 | 6 => iBasis_4_6 | 7 => iBasis_4_7 | 8 => iBasis_4_8 | 9 => iBasis_4_9 | 10 => iBasis_4_10 | 11 => iBasis_4_11 | _ => []) y)) =
      (m i * m j) * (ApertureLogTwo.matQ mPPRawQ_1 i.1 j.1 : ℝ) := fun i j => by
    rw [intervalIntegral.integral_const_mul, int_pp_1 i j]
  have hSumI : ∀ i : Fin 12, (∫ y in (-1 : ℝ)..1, ∑ j : Fin 12,
      (m i * m j) * (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y *
        polyEval (match j.1 with | 0 => iBasis_4_0 | 1 => iBasis_4_1 | 2 => iBasis_4_2 | 3 => iBasis_4_3 | 4 => iBasis_4_4 | 5 => iBasis_4_5 | 6 => iBasis_4_6 | 7 => iBasis_4_7 | 8 => iBasis_4_8 | 9 => iBasis_4_9 | 10 => iBasis_4_10 | 11 => iBasis_4_11 | _ => []) y)) =
      ∑ j : Fin 12, (m i * m j) * (ApertureLogTwo.matQ mPPRawQ_1 i.1 j.1 : ℝ) := fun i => by
    rw [intervalIntegral.integral_finsetSum fun j _ =>
      (show Continuous fun y : ℝ => (m i * m j) *
        (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y *
         polyEval (match j.1 with | 0 => iBasis_4_0 | 1 => iBasis_4_1 | 2 => iBasis_4_2 | 3 => iBasis_4_3 | 4 => iBasis_4_4 | 5 => iBasis_4_5 | 6 => iBasis_4_6 | 7 => iBasis_4_7 | 8 => iBasis_4_8 | 9 => iBasis_4_9 | 10 => iBasis_4_10 | 11 => iBasis_4_11 | _ => []) y) from
        continuous_const.mul ((continuous_polyEval _).mul (continuous_polyEval _))).intervalIntegrable (-1) 1]
    exact Finset.sum_congr rfl fun j _ => hEach i j
  rw [show ((3 : ℕ).factorial : ℝ) = 6 by norm_num [Nat.factorial]]
  simp_rw [hSumI, sum_finK, matQ_eq_qcoeffAt]
  dsimp only [mPPRawQ_1, qcoeffAt, qlistAt, qOddMat_1, matAt, listAt, coeffAt, m]
  simp only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_zero]
  ring

private theorem hOdd_bound_1 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hLowProj : ∀ y : ℝ, lowProj (dilateLogTwo F) 24 y =
      ∑ k : Fin 12, halfMoment (dilateLogTwo F) k * basisFn k y)
    (hHopp : ∀ r : ℕ, regionalLegendreMoment (dilateLogTwo F) (24 + (2 * r + 1)) = 0) :
    let G := dilateLogTwo F
    let m := halfMoment G
    let M_res := (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 24 x) ^ 2) / 2
    apow0_4 * (∑ i : Fin 12, ∑ j : Fin 12, qOddMat_1 i j * m i * m j) -
      (∑ i : Fin 12, (errApow_4 * qOddRowAbs_1 i) * m i ^ 2) -
      ((28330699806371863465765559550147688507568454001005121 / 10000000000000000000000000000000000000000000000000000000 : ℝ) * ∑ r ∈ Finset.range 2,
        ((2 * ↑(24 + 2 * r) + 1) / 2) * (∑ i : Fin 12, m i * gHi_1 i r) ^ 2) -
      ((1 / 2000 : ℝ) + (53861523002719472107082803467484904070644308185446063804726431212902824004833568504936804890286021363709 / 194818182068004874472224973590719464580142832654429411005735291835112933326006093120000000000000000000000000 : ℝ)) * M_res ≤
      ((-7 / 5760 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 3 * autocorr F t) /
        (2 * apertureLogTwo) := by
  intro G m M_res
  have hA_pos : 0 < apertureLogTwo := apertureLogTwo_pos
  set R_res : ℝ → ℝ := fun x => G x - lowProj G 24 x
  have hRc : Continuous R_res := hGc.sub (contDiff_lowProj G _ (k := 0)).continuous
  have hMres_nn : 0 ≤ M_res := div_nonneg (setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _) (by norm_num)
  have hIntR2 : (∫ x in Icc (-1 : ℝ) 1, R_res x ^ 2) = 2 * M_res := by dsimp [R_res, M_res]; ring
  have hpi_lo : piLo ≤ Real.pi := (pi_bounds_d20).1
  have hpi_pos : 0 < piLo := by norm_num [piLo]
  have h4pi : 4 / Real.pi ^ 2 ≤ 4 / piLo ^ 2 := by
    have hp2 : piLo ^ 2 ≤ Real.pi ^ 2 := pow_le_pow_left₀ hpi_pos.le hpi_lo 2
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hp2
  have hdil := dilated_correlation_moment_log_two F 3
  have hdec := odd_lag_moment_lowProj_decomp hGc hsG (m := 24) (q := 1) (by omega)
  change (∫ t in Ioc (0 : ℝ) 2, t ^ 3 * autocorr G t) =
    ((3 : ℕ).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, lowProj G 24 y * iterPrim 4 (lowProj G 24) y) +
    2 * ((3 : ℕ).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, R_res y * iterPrim 4 (lowProj G 24) y) +
    (-1 : ℝ) ^ (1 + 1) * ((3 : ℕ).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, iterPrim (1 + 1) R_res y ^ 2) at hdec
  have hPP := hPP_eq_1 hLowProj
  have hPP_pert := symm_quad_scale_pert qOddMat_1 qOddMat_1_sym abs_aperture_pow_4_sub m
  simp_rw [qOddRowAbs_1_eq] at hPP_pert
  have hWirt := iterPrim_sq_le_wirtinger hRc (m := 24) (fun n hn => sub_lowProj_moment_lt hGc hn) (1 + 1) (by omega)
  have hWirt' : (∫ y in (-1 : ℝ)..1, iterPrim (1 + 1) R_res y ^ 2) ≤ (4 / piLo ^ 2) ^ (1 + 1) * (2 * M_res) := by
    rw [hIntR2] at hWirt
    exact hWirt.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h4pi (1 + 1)) (by positivity))
  have hCross := high_mode_cross_sq_le hGc (m := 24) (q := 1) (by omega) hHopp
  change (∫ y in (-1 : ℝ)..1, R_res y * iterPrim 4 (lowProj G 24) y) ^ 2 ≤
    (∑ r ∈ Finset.range (1 + 1), ((2 * ↑(24 + 2 * r) + 1) / 2) *
      regionalLegendreMoment (iterPrim 4 (lowProj G 24)) (24 + 2 * r) ^ 2) *
    (∫ y in Icc (-1 : ℝ) 1, R_res y ^ 2) at hCross
  rw [hIntR2] at hCross
  have hMomLin : ∀ r ∈ Finset.range (1 + 1), regionalLegendreMoment (iterPrim 4 (lowProj G 24)) (24 + 2 * r) =
      ∑ i : Fin 12, m i * gHi_1 i r := fun r hr => by
    have hlin : regionalLegendreMoment (iterPrim 4 (lowProj G 24)) (24 + 2 * r) =
        ∑ i : Fin 12, m i * regionalLegendreMoment (polyEval (match i.1 with | 0 => iBasis_4_0 | 1 => iBasis_4_1 | 2 => iBasis_4_2 | 3 => iBasis_4_3 | 4 => iBasis_4_4 | 5 => iBasis_4_5 | 6 => iBasis_4_6 | 7 => iBasis_4_7 | 8 => iBasis_4_8 | 9 => iBasis_4_9 | 10 => iBasis_4_10 | 11 => iBasis_4_11 | _ => [])) (24 + 2 * r) := by
      unfold regionalLegendreMoment
      have hfn : ∀ x : ℝ, iterPrim 4 (lowProj G 24) x * legP (24 + 2 * r) x =
          ∑ i : Fin 12, m i * (polyEval (match i.1 with | 0 => iBasis_4_0 | 1 => iBasis_4_1 | 2 => iBasis_4_2 | 3 => iBasis_4_3 | 4 => iBasis_4_4 | 5 => iBasis_4_5 | 6 => iBasis_4_6 | 7 => iBasis_4_7 | 8 => iBasis_4_8 | 9 => iBasis_4_9 | 10 => iBasis_4_10 | 11 => iBasis_4_11 | _ => []) x * legP (24 + 2 * r) x) := fun x => by
        rw [hIterP_eq_1 hLowProj x, Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by dsimp only [m]; ring
      simp_rw [hfn]
      rw [integral_finsetSum _ fun i _ =>
        (show Continuous fun x : ℝ => m i * (polyEval (match i.1 with | 0 => iBasis_4_0 | 1 => iBasis_4_1 | 2 => iBasis_4_2 | 3 => iBasis_4_3 | 4 => iBasis_4_4 | 5 => iBasis_4_5 | 6 => iBasis_4_6 | 7 => iBasis_4_7 | 8 => iBasis_4_8 | 9 => iBasis_4_9 | 10 => iBasis_4_10 | 11 => iBasis_4_11 | _ => []) x * legP (24 + 2 * r) x) from
          continuous_const.mul ((continuous_polyEval _).mul (continuous_legP _))).integrableOn_Icc]
      exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    rw [hlin]; exact Finset.sum_congr rfl fun i _ => by rw [gHi_eq_1 i r hr]
  set A_sp : ℝ := ∑ r ∈ Finset.range (1 + 1), ((2 * ↑(24 + 2 * r) + 1) / 2) *
    (∑ i : Fin 12, m i * gHi_1 i r) ^ 2
  have hAsp_eq : (∑ r ∈ Finset.range (1 + 1), ((2 * ↑(24 + 2 * r) + 1) / 2) *
      regionalLegendreMoment (iterPrim 4 (lowProj G 24)) (24 + 2 * r) ^ 2) = A_sp :=
    Finset.sum_congr rfl fun r hr => by rw [hMomLin r hr]
  rw [hAsp_eq] at hCross
  set w_true : ℝ := ((7 / 11520 : ℝ) * ((3 : ℕ).factorial : ℝ)) * apertureLogTwo ^ 4
  have hw_nn : 0 ≤ w_true := by dsimp [w_true]; positivity
  have hw_le : w_true ≤ (168317259383498350334633761 / 200000000000000000000000000000 : ℝ) := by
    obtain ⟨_, h2u⟩ := log_two_bounds_d26; dsimp only [w_true]; unfold apertureLogTwo
    have hp : (Real.log 2) ^ 4 ≤ logTwoHi ^ 4 := pow_le_pow_left₀ (apertureLogTwo_pos.le) h2u 4
    have hc : ((7 / 11520 : ℝ) * ((3 : ℕ).factorial : ℝ)) * logTwoHi ^ 4 ≤ (168317259383498350334633761 / 200000000000000000000000000000 : ℝ) := by
      norm_num [Nat.factorial, logTwoHi]
    nlinarith [hp, hc, (show (0 : ℝ) ≤ (7 / 11520 : ℝ) * ((3 : ℕ).factorial : ℝ) by positivity)]
  have hAsp_nn : 0 ≤ A_sp := Finset.sum_nonneg fun r _ => mul_nonneg (by positivity) (sq_nonneg _)
  set I_RP : ℝ := ∫ y in (-1 : ℝ)..1, R_res y * iterPrim 4 (lowProj G 24) y
  have hY2 : (w_true * I_RP) ^ 2 ≤ ((168317259383498350334633761 / 200000000000000000000000000000 : ℝ)) ^ 2 * (A_sp * (2 * M_res)) := by
    rw [mul_pow]
    have hw2 : w_true ^ 2 ≤ ((168317259383498350334633761 / 200000000000000000000000000000 : ℝ)) ^ 2 := pow_le_pow_left₀ hw_nn hw_le 2
    exact (mul_le_mul_of_nonneg_right hw2 (sq_nonneg I_RP)).trans (mul_le_mul_of_nonneg_left hCross (sq_nonneg _))
  have hy := cross_spillover_young (by norm_num : (0 : ℝ) ≤ (168317259383498350334633761 / 200000000000000000000000000000 : ℝ)) hAsp_nn hMres_nn
    (by norm_num : (0 : ℝ) < (1 / 2000 : ℝ)) hY2
  have hw_wirt : w_true * (∫ y in (-1 : ℝ)..1, iterPrim (1 + 1) R_res y ^ 2) ≤ (53861523002719472107082803467484904070644308185446063804726431212902824004833568504936804890286021363709 / 194818182068004874472224973590719464580142832654429411005735291835112933326006093120000000000000000000000000 : ℝ) * M_res := by
    have hw_ex : w_true ≤ (53861523002719472107082803467484904070644308185446063804726431212902824004833568504936804890286021363709 / 64000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
      obtain ⟨_, h2u⟩ := log_two_bounds_d26; dsimp only [w_true]; unfold apertureLogTwo
      have hp : (Real.log 2) ^ 4 ≤ logTwoHi ^ 4 := pow_le_pow_left₀ (apertureLogTwo_pos.le) h2u 4
      have hc : ((7 / 11520 : ℝ) * ((3 : ℕ).factorial : ℝ)) * logTwoHi ^ 4 = (53861523002719472107082803467484904070644308185446063804726431212902824004833568504936804890286021363709 / 64000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
        norm_num [Nat.factorial, logTwoHi]
      nlinarith [hp, hc, (show (0 : ℝ) ≤ (7 / 11520 : ℝ) * ((3 : ℕ).factorial : ℝ) by positivity)]
    have h1 := mul_le_mul hw_ex hWirt' (by rw [intervalIntegral.integral_of_le (by norm_num)]; exact setIntegral_nonneg measurableSet_Ioc fun _ _ => sq_nonneg _) (by norm_num)
    have h2 : (53861523002719472107082803467484904070644308185446063804726431212902824004833568504936804890286021363709 / 64000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * ((4 / piLo ^ 2) ^ (1 + 1) * (2 * M_res)) = (53861523002719472107082803467484904070644308185446063804726431212902824004833568504936804890286021363709 / 194818182068004874472224973590719464580142832654429411005735291835112933326006093120000000000000000000000000 : ℝ) * M_res := by
      norm_num [piLo]; ring
    linarith
  have hdiv_tot : ((-7 / 5760 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 3 * autocorr F t) / (2 * apertureLogTwo) =
      apertureLogTwo ^ 4 * (((-7 / 11520 : ℝ) * ((3 : ℕ).factorial : ℝ)) *
        (∫ y in (-1 : ℝ)..1, lowProj G 24 y * iterPrim 4 (lowProj G 24) y)) +
      (-1 : ℝ) * (2 * (w_true * I_RP)) -
      w_true * (∫ y in (-1 : ℝ)..1, iterPrim (1 + 1) R_res y ^ 2) := by
    rw [hdil, hdec]; dsimp [w_true, I_RP]; field_simp [hA_pos.ne']; norm_num; ring
  rw [hdiv_tot, hPP]
  have hsc_eq : (2 * ((168317259383498350334633761 / 200000000000000000000000000000 : ℝ)) ^ 2 / (1 / 2000 : ℝ)) = (28330699806371863465765559550147688507568454001005121 / 10000000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num
  rw [hsc_eq] at hy
  linarith [hPP_pert, hy.2, hw_wirt]

private theorem hIterP_eq_2 {G : ℝ → ℝ}
    (hLowProj : ∀ y : ℝ, lowProj G 24 y = ∑ k : Fin 12, halfMoment G k * basisFn k y) (y : ℝ) :
    iterPrim 6 (lowProj G 24) y =
      ∑ j : Fin 12, halfMoment G j * polyEval (match j.1 with | 0 => iBasis_6_0 | 1 => iBasis_6_1 | 2 => iBasis_6_2 | 3 => iBasis_6_3 | 4 => iBasis_6_4 | 5 => iBasis_6_5 | 6 => iBasis_6_6 | 7 => iBasis_6_7 | 8 => iBasis_6_8 | 9 => iBasis_6_9 | 10 => iBasis_6_10 | 11 => iBasis_6_11 | _ => []) y := by
  have hlp_eq : lowProj G 24 = fun u => ∑ j : Fin 12, halfMoment G j * basisFn j u := funext hLowProj
  rw [hlp_eq, iterPrim_finset_sum Finset.univ (f := fun j u => halfMoment G j * basisFn j u)
    (fun j _ => continuous_const.mul (continuous_const.mul (continuous_legP _))) 6 y]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iterPrim_const_mul (f := basisFn j) (continuous_const.mul (continuous_legP _)) (halfMoment G j) 6 y]
  congr 1; rcases j with ⟨jv, hjv⟩; interval_cases jv
  · exact iterPrim_basis_6_0 y
  · exact iterPrim_basis_6_1 y
  · exact iterPrim_basis_6_2 y
  · exact iterPrim_basis_6_3 y
  · exact iterPrim_basis_6_4 y
  · exact iterPrim_basis_6_5 y
  · exact iterPrim_basis_6_6 y
  · exact iterPrim_basis_6_7 y
  · exact iterPrim_basis_6_8 y
  · exact iterPrim_basis_6_9 y
  · exact iterPrim_basis_6_10 y
  · exact iterPrim_basis_6_11 y

private theorem hPP_eq_2 {G : ℝ → ℝ}
    (hLowProj : ∀ y : ℝ, lowProj G 24 y = ∑ k : Fin 12, halfMoment G k * basisFn k y) :
    ((31 / 1935360 : ℝ) * ((5 : ℕ).factorial : ℝ)) *
      (∫ y in (-1 : ℝ)..1, lowProj G 24 y * iterPrim 6 (lowProj G 24) y) =
      ∑ i : Fin 12, ∑ j : Fin 12, qOddMat_2 i j * halfMoment G i * halfMoment G j := by
  set m := halfMoment G
  have hfn : ∀ y : ℝ, lowProj G 24 y * iterPrim 6 (lowProj G 24) y =
      ∑ i : Fin 12, ∑ j : Fin 12, (m i * m j) *
        (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y *
         polyEval (match j.1 with | 0 => iBasis_6_0 | 1 => iBasis_6_1 | 2 => iBasis_6_2 | 3 => iBasis_6_3 | 4 => iBasis_6_4 | 5 => iBasis_6_5 | 6 => iBasis_6_6 | 7 => iBasis_6_7 | 8 => iBasis_6_8 | 9 => iBasis_6_9 | 10 => iBasis_6_10 | 11 => iBasis_6_11 | _ => []) y) := fun y => by
    rw [hLowProj y, hIterP_eq_2 hLowProj y, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    have hb : basisFn i y = polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y := by
      rcases i with ⟨iv, hiv⟩; interval_cases iv
      · exact iterPrim_basis_0_0 y
      · exact iterPrim_basis_0_1 y
      · exact iterPrim_basis_0_2 y
      · exact iterPrim_basis_0_3 y
      · exact iterPrim_basis_0_4 y
      · exact iterPrim_basis_0_5 y
      · exact iterPrim_basis_0_6 y
      · exact iterPrim_basis_0_7 y
      · exact iterPrim_basis_0_8 y
      · exact iterPrim_basis_0_9 y
      · exact iterPrim_basis_0_10 y
      · exact iterPrim_basis_0_11 y
    rw [hb]; dsimp only [m]; ring
  simp_rw [hfn]
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (show Continuous fun y : ℝ => ∑ j : Fin 12, (m i * m j) *
      (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y *
       polyEval (match j.1 with | 0 => iBasis_6_0 | 1 => iBasis_6_1 | 2 => iBasis_6_2 | 3 => iBasis_6_3 | 4 => iBasis_6_4 | 5 => iBasis_6_5 | 6 => iBasis_6_6 | 7 => iBasis_6_7 | 8 => iBasis_6_8 | 9 => iBasis_6_9 | 10 => iBasis_6_10 | 11 => iBasis_6_11 | _ => []) y) from
      continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_polyEval _).mul (continuous_polyEval _))).intervalIntegrable (-1) 1]
  have hEach : ∀ (i j : Fin 12), (∫ y in (-1 : ℝ)..1,
      (m i * m j) * (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y *
        polyEval (match j.1 with | 0 => iBasis_6_0 | 1 => iBasis_6_1 | 2 => iBasis_6_2 | 3 => iBasis_6_3 | 4 => iBasis_6_4 | 5 => iBasis_6_5 | 6 => iBasis_6_6 | 7 => iBasis_6_7 | 8 => iBasis_6_8 | 9 => iBasis_6_9 | 10 => iBasis_6_10 | 11 => iBasis_6_11 | _ => []) y)) =
      (m i * m j) * (ApertureLogTwo.matQ mPPRawQ_2 i.1 j.1 : ℝ) := fun i j => by
    rw [intervalIntegral.integral_const_mul, int_pp_2 i j]
  have hSumI : ∀ i : Fin 12, (∫ y in (-1 : ℝ)..1, ∑ j : Fin 12,
      (m i * m j) * (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y *
        polyEval (match j.1 with | 0 => iBasis_6_0 | 1 => iBasis_6_1 | 2 => iBasis_6_2 | 3 => iBasis_6_3 | 4 => iBasis_6_4 | 5 => iBasis_6_5 | 6 => iBasis_6_6 | 7 => iBasis_6_7 | 8 => iBasis_6_8 | 9 => iBasis_6_9 | 10 => iBasis_6_10 | 11 => iBasis_6_11 | _ => []) y)) =
      ∑ j : Fin 12, (m i * m j) * (ApertureLogTwo.matQ mPPRawQ_2 i.1 j.1 : ℝ) := fun i => by
    rw [intervalIntegral.integral_finsetSum fun j _ =>
      (show Continuous fun y : ℝ => (m i * m j) *
        (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y *
         polyEval (match j.1 with | 0 => iBasis_6_0 | 1 => iBasis_6_1 | 2 => iBasis_6_2 | 3 => iBasis_6_3 | 4 => iBasis_6_4 | 5 => iBasis_6_5 | 6 => iBasis_6_6 | 7 => iBasis_6_7 | 8 => iBasis_6_8 | 9 => iBasis_6_9 | 10 => iBasis_6_10 | 11 => iBasis_6_11 | _ => []) y) from
        continuous_const.mul ((continuous_polyEval _).mul (continuous_polyEval _))).intervalIntegrable (-1) 1]
    exact Finset.sum_congr rfl fun j _ => hEach i j
  rw [show ((5 : ℕ).factorial : ℝ) = 120 by norm_num [Nat.factorial]]
  simp_rw [hSumI, sum_finK, matQ_eq_qcoeffAt]
  dsimp only [mPPRawQ_2, qcoeffAt, qlistAt, qOddMat_2, matAt, listAt, coeffAt, m]
  simp only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_zero]
  ring

private theorem hOdd_bound_2 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hLowProj : ∀ y : ℝ, lowProj (dilateLogTwo F) 24 y =
      ∑ k : Fin 12, halfMoment (dilateLogTwo F) k * basisFn k y)
    (hHopp : ∀ r : ℕ, regionalLegendreMoment (dilateLogTwo F) (24 + (2 * r + 1)) = 0) :
    let G := dilateLogTwo F
    let m := halfMoment G
    let M_res := (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 24 x) ^ 2) / 2
    apow0_6 * (∑ i : Fin 12, ∑ j : Fin 12, qOddMat_2 i j * m i * m j) -
      (∑ i : Fin 12, (errApow_6 * qOddRowAbs_2 i) * m i ^ 2) -
      ((1817723751476543414437681449293926857541879379346961 / 2000000000000000000000000000000000000000000000000000000 : ℝ) * ∑ r ∈ Finset.range 3,
        ((2 * ↑(24 + 2 * r) + 1) / 2) * (∑ i : Fin 12, m i * gHi_2 i r) ^ 2) -
      ((1 / 10000 : ℝ) + (382007553755863926870040042097449282156357447299937480899016149154433081824883286535181352428961783385936212243165829737413357202226711792633500829201931631 / 13459448710054262118355122316425225466502542667336215127570474536177358766844660236371912877458932196995890038503706807375744000000000000000000000000000000000000 : ℝ)) * M_res ≤
      ((31 / 967680 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 5 * autocorr F t) /
        (2 * apertureLogTwo) := by
  intro G m M_res
  have hA_pos : 0 < apertureLogTwo := apertureLogTwo_pos
  set R_res : ℝ → ℝ := fun x => G x - lowProj G 24 x
  have hRc : Continuous R_res := hGc.sub (contDiff_lowProj G _ (k := 0)).continuous
  have hMres_nn : 0 ≤ M_res := div_nonneg (setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _) (by norm_num)
  have hIntR2 : (∫ x in Icc (-1 : ℝ) 1, R_res x ^ 2) = 2 * M_res := by dsimp [R_res, M_res]; ring
  have hpi_lo : piLo ≤ Real.pi := (pi_bounds_d20).1
  have hpi_pos : 0 < piLo := by norm_num [piLo]
  have h4pi : 4 / Real.pi ^ 2 ≤ 4 / piLo ^ 2 := by
    have hp2 : piLo ^ 2 ≤ Real.pi ^ 2 := pow_le_pow_left₀ hpi_pos.le hpi_lo 2
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hp2
  have hdil := dilated_correlation_moment_log_two F 5
  have hdec := odd_lag_moment_lowProj_decomp hGc hsG (m := 24) (q := 2) (by omega)
  change (∫ t in Ioc (0 : ℝ) 2, t ^ 5 * autocorr G t) =
    ((5 : ℕ).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, lowProj G 24 y * iterPrim 6 (lowProj G 24) y) +
    2 * ((5 : ℕ).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, R_res y * iterPrim 6 (lowProj G 24) y) +
    (-1 : ℝ) ^ (2 + 1) * ((5 : ℕ).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, iterPrim (2 + 1) R_res y ^ 2) at hdec
  have hPP := hPP_eq_2 hLowProj
  have hPP_pert := symm_quad_scale_pert qOddMat_2 qOddMat_2_sym abs_aperture_pow_6_sub m
  simp_rw [qOddRowAbs_2_eq] at hPP_pert
  have hWirt := iterPrim_sq_le_wirtinger hRc (m := 24) (fun n hn => sub_lowProj_moment_lt hGc hn) (2 + 1) (by omega)
  have hWirt' : (∫ y in (-1 : ℝ)..1, iterPrim (2 + 1) R_res y ^ 2) ≤ (4 / piLo ^ 2) ^ (2 + 1) * (2 * M_res) := by
    rw [hIntR2] at hWirt
    exact hWirt.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h4pi (2 + 1)) (by positivity))
  have hCross := high_mode_cross_sq_le hGc (m := 24) (q := 2) (by omega) hHopp
  change (∫ y in (-1 : ℝ)..1, R_res y * iterPrim 6 (lowProj G 24) y) ^ 2 ≤
    (∑ r ∈ Finset.range (2 + 1), ((2 * ↑(24 + 2 * r) + 1) / 2) *
      regionalLegendreMoment (iterPrim 6 (lowProj G 24)) (24 + 2 * r) ^ 2) *
    (∫ y in Icc (-1 : ℝ) 1, R_res y ^ 2) at hCross
  rw [hIntR2] at hCross
  have hMomLin : ∀ r ∈ Finset.range (2 + 1), regionalLegendreMoment (iterPrim 6 (lowProj G 24)) (24 + 2 * r) =
      ∑ i : Fin 12, m i * gHi_2 i r := fun r hr => by
    have hlin : regionalLegendreMoment (iterPrim 6 (lowProj G 24)) (24 + 2 * r) =
        ∑ i : Fin 12, m i * regionalLegendreMoment (polyEval (match i.1 with | 0 => iBasis_6_0 | 1 => iBasis_6_1 | 2 => iBasis_6_2 | 3 => iBasis_6_3 | 4 => iBasis_6_4 | 5 => iBasis_6_5 | 6 => iBasis_6_6 | 7 => iBasis_6_7 | 8 => iBasis_6_8 | 9 => iBasis_6_9 | 10 => iBasis_6_10 | 11 => iBasis_6_11 | _ => [])) (24 + 2 * r) := by
      unfold regionalLegendreMoment
      have hfn : ∀ x : ℝ, iterPrim 6 (lowProj G 24) x * legP (24 + 2 * r) x =
          ∑ i : Fin 12, m i * (polyEval (match i.1 with | 0 => iBasis_6_0 | 1 => iBasis_6_1 | 2 => iBasis_6_2 | 3 => iBasis_6_3 | 4 => iBasis_6_4 | 5 => iBasis_6_5 | 6 => iBasis_6_6 | 7 => iBasis_6_7 | 8 => iBasis_6_8 | 9 => iBasis_6_9 | 10 => iBasis_6_10 | 11 => iBasis_6_11 | _ => []) x * legP (24 + 2 * r) x) := fun x => by
        rw [hIterP_eq_2 hLowProj x, Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by dsimp only [m]; ring
      simp_rw [hfn]
      rw [integral_finsetSum _ fun i _ =>
        (show Continuous fun x : ℝ => m i * (polyEval (match i.1 with | 0 => iBasis_6_0 | 1 => iBasis_6_1 | 2 => iBasis_6_2 | 3 => iBasis_6_3 | 4 => iBasis_6_4 | 5 => iBasis_6_5 | 6 => iBasis_6_6 | 7 => iBasis_6_7 | 8 => iBasis_6_8 | 9 => iBasis_6_9 | 10 => iBasis_6_10 | 11 => iBasis_6_11 | _ => []) x * legP (24 + 2 * r) x) from
          continuous_const.mul ((continuous_polyEval _).mul (continuous_legP _))).integrableOn_Icc]
      exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    rw [hlin]; exact Finset.sum_congr rfl fun i _ => by rw [gHi_eq_2 i r hr]
  set A_sp : ℝ := ∑ r ∈ Finset.range (2 + 1), ((2 * ↑(24 + 2 * r) + 1) / 2) *
    (∑ i : Fin 12, m i * gHi_2 i r) ^ 2
  have hAsp_eq : (∑ r ∈ Finset.range (2 + 1), ((2 * ↑(24 + 2 * r) + 1) / 2) *
      regionalLegendreMoment (iterPrim 6 (lowProj G 24)) (24 + 2 * r) ^ 2) = A_sp :=
    Finset.sum_congr rfl fun r hr => by rw [hMomLin r hr]
  rw [hAsp_eq] at hCross
  set w_true : ℝ := ((31 / 1935360 : ℝ) * ((5 : ℕ).factorial : ℝ)) * apertureLogTwo ^ 6
  have hw_nn : 0 ≤ w_true := by dsimp [w_true]; positivity
  have hw_le : w_true ≤ (42634771624538384695316969 / 200000000000000000000000000000 : ℝ) := by
    obtain ⟨_, h2u⟩ := log_two_bounds_d26; dsimp only [w_true]; unfold apertureLogTwo
    have hp : (Real.log 2) ^ 6 ≤ logTwoHi ^ 6 := pow_le_pow_left₀ (apertureLogTwo_pos.le) h2u 6
    have hc : ((31 / 1935360 : ℝ) * ((5 : ℕ).factorial : ℝ)) * logTwoHi ^ 6 ≤ (42634771624538384695316969 / 200000000000000000000000000000 : ℝ) := by
      norm_num [Nat.factorial, logTwoHi]
    nlinarith [hp, hc, (show (0 : ℝ) ≤ (31 / 1935360 : ℝ) * ((5 : ℕ).factorial : ℝ) by positivity)]
  have hAsp_nn : 0 ≤ A_sp := Finset.sum_nonneg fun r _ => mul_nonneg (by positivity) (sq_nonneg _)
  set I_RP : ℝ := ∫ y in (-1 : ℝ)..1, R_res y * iterPrim 6 (lowProj G 24) y
  have hY2 : (w_true * I_RP) ^ 2 ≤ ((42634771624538384695316969 / 200000000000000000000000000000 : ℝ)) ^ 2 * (A_sp * (2 * M_res)) := by
    rw [mul_pow]
    have hw2 : w_true ^ 2 ≤ ((42634771624538384695316969 / 200000000000000000000000000000 : ℝ)) ^ 2 := pow_le_pow_left₀ hw_nn hw_le 2
    exact (mul_le_mul_of_nonneg_right hw2 (sq_nonneg I_RP)).trans (mul_le_mul_of_nonneg_left hCross (sq_nonneg _))
  have hy := cross_spillover_young (by norm_num : (0 : ℝ) ≤ (42634771624538384695316969 / 200000000000000000000000000000 : ℝ)) hAsp_nn hMres_nn
    (by norm_num : (0 : ℝ) < (1 / 10000 : ℝ)) hY2
  have hw_wirt : w_true * (∫ y in (-1 : ℝ)..1, iterPrim (2 + 1) R_res y ^ 2) ≤ (382007553755863926870040042097449282156357447299937480899016149154433081824883286535181352428961783385936212243165829737413357202226711792633500829201931631 / 13459448710054262118355122316425225466502542667336215127570474536177358766844660236371912877458932196995890038503706807375744000000000000000000000000000000000000 : ℝ) * M_res := by
    have hw_ex : w_true ≤ (382007553755863926870040042097449282156357447299937480899016149154433081824883286535181352428961783385936212243165829737413357202226711792633500829201931631 / 1792000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
      obtain ⟨_, h2u⟩ := log_two_bounds_d26; dsimp only [w_true]; unfold apertureLogTwo
      have hp : (Real.log 2) ^ 6 ≤ logTwoHi ^ 6 := pow_le_pow_left₀ (apertureLogTwo_pos.le) h2u 6
      have hc : ((31 / 1935360 : ℝ) * ((5 : ℕ).factorial : ℝ)) * logTwoHi ^ 6 = (382007553755863926870040042097449282156357447299937480899016149154433081824883286535181352428961783385936212243165829737413357202226711792633500829201931631 / 1792000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
        norm_num [Nat.factorial, logTwoHi]
      nlinarith [hp, hc, (show (0 : ℝ) ≤ (31 / 1935360 : ℝ) * ((5 : ℕ).factorial : ℝ) by positivity)]
    have h1 := mul_le_mul hw_ex hWirt' (by rw [intervalIntegral.integral_of_le (by norm_num)]; exact setIntegral_nonneg measurableSet_Ioc fun _ _ => sq_nonneg _) (by norm_num)
    have h2 : (382007553755863926870040042097449282156357447299937480899016149154433081824883286535181352428961783385936212243165829737413357202226711792633500829201931631 / 1792000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * ((4 / piLo ^ 2) ^ (2 + 1) * (2 * M_res)) = (382007553755863926870040042097449282156357447299937480899016149154433081824883286535181352428961783385936212243165829737413357202226711792633500829201931631 / 13459448710054262118355122316425225466502542667336215127570474536177358766844660236371912877458932196995890038503706807375744000000000000000000000000000000000000 : ℝ) * M_res := by
      norm_num [piLo]; ring
    linarith
  have hdiv_tot : ((31 / 967680 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 5 * autocorr F t) / (2 * apertureLogTwo) =
      apertureLogTwo ^ 6 * (((31 / 1935360 : ℝ) * ((5 : ℕ).factorial : ℝ)) *
        (∫ y in (-1 : ℝ)..1, lowProj G 24 y * iterPrim 6 (lowProj G 24) y)) +
      (1 : ℝ) * (2 * (w_true * I_RP)) -
      w_true * (∫ y in (-1 : ℝ)..1, iterPrim (2 + 1) R_res y ^ 2) := by
    rw [hdil, hdec]; dsimp [w_true, I_RP]; field_simp [hA_pos.ne']; norm_num; ring
  rw [hdiv_tot, hPP]
  have hsc_eq : (2 * ((42634771624538384695316969 / 200000000000000000000000000000 : ℝ)) ^ 2 / (1 / 10000 : ℝ)) = (1817723751476543414437681449293926857541879379346961 / 2000000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num
  rw [hsc_eq] at hy
  linarith [hPP_pert, hy.1, hw_wirt]

private theorem hIterP_eq_3 {G : ℝ → ℝ}
    (hLowProj : ∀ y : ℝ, lowProj G 24 y = ∑ k : Fin 12, halfMoment G k * basisFn k y) (y : ℝ) :
    iterPrim 8 (lowProj G 24) y =
      ∑ j : Fin 12, halfMoment G j * polyEval (match j.1 with | 0 => iBasis_8_0 | 1 => iBasis_8_1 | 2 => iBasis_8_2 | 3 => iBasis_8_3 | 4 => iBasis_8_4 | 5 => iBasis_8_5 | 6 => iBasis_8_6 | 7 => iBasis_8_7 | 8 => iBasis_8_8 | 9 => iBasis_8_9 | 10 => iBasis_8_10 | 11 => iBasis_8_11 | _ => []) y := by
  have hlp_eq : lowProj G 24 = fun u => ∑ j : Fin 12, halfMoment G j * basisFn j u := funext hLowProj
  rw [hlp_eq, iterPrim_finset_sum Finset.univ (f := fun j u => halfMoment G j * basisFn j u)
    (fun j _ => continuous_const.mul (continuous_const.mul (continuous_legP _))) 8 y]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iterPrim_const_mul (f := basisFn j) (continuous_const.mul (continuous_legP _)) (halfMoment G j) 8 y]
  congr 1; rcases j with ⟨jv, hjv⟩; interval_cases jv
  · exact iterPrim_basis_8_0 y
  · exact iterPrim_basis_8_1 y
  · exact iterPrim_basis_8_2 y
  · exact iterPrim_basis_8_3 y
  · exact iterPrim_basis_8_4 y
  · exact iterPrim_basis_8_5 y
  · exact iterPrim_basis_8_6 y
  · exact iterPrim_basis_8_7 y
  · exact iterPrim_basis_8_8 y
  · exact iterPrim_basis_8_9 y
  · exact iterPrim_basis_8_10 y
  · exact iterPrim_basis_8_11 y

private theorem hPP_eq_3 {G : ℝ → ℝ}
    (hLowProj : ∀ y : ℝ, lowProj G 24 y = ∑ k : Fin 12, halfMoment G k * basisFn k y) :
    ((-127 / 309657600 : ℝ) * ((7 : ℕ).factorial : ℝ)) *
      (∫ y in (-1 : ℝ)..1, lowProj G 24 y * iterPrim 8 (lowProj G 24) y) =
      ∑ i : Fin 12, ∑ j : Fin 12, qOddMat_3 i j * halfMoment G i * halfMoment G j := by
  set m := halfMoment G
  have hfn : ∀ y : ℝ, lowProj G 24 y * iterPrim 8 (lowProj G 24) y =
      ∑ i : Fin 12, ∑ j : Fin 12, (m i * m j) *
        (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y *
         polyEval (match j.1 with | 0 => iBasis_8_0 | 1 => iBasis_8_1 | 2 => iBasis_8_2 | 3 => iBasis_8_3 | 4 => iBasis_8_4 | 5 => iBasis_8_5 | 6 => iBasis_8_6 | 7 => iBasis_8_7 | 8 => iBasis_8_8 | 9 => iBasis_8_9 | 10 => iBasis_8_10 | 11 => iBasis_8_11 | _ => []) y) := fun y => by
    rw [hLowProj y, hIterP_eq_3 hLowProj y, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    have hb : basisFn i y = polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y := by
      rcases i with ⟨iv, hiv⟩; interval_cases iv
      · exact iterPrim_basis_0_0 y
      · exact iterPrim_basis_0_1 y
      · exact iterPrim_basis_0_2 y
      · exact iterPrim_basis_0_3 y
      · exact iterPrim_basis_0_4 y
      · exact iterPrim_basis_0_5 y
      · exact iterPrim_basis_0_6 y
      · exact iterPrim_basis_0_7 y
      · exact iterPrim_basis_0_8 y
      · exact iterPrim_basis_0_9 y
      · exact iterPrim_basis_0_10 y
      · exact iterPrim_basis_0_11 y
    rw [hb]; dsimp only [m]; ring
  simp_rw [hfn]
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (show Continuous fun y : ℝ => ∑ j : Fin 12, (m i * m j) *
      (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y *
       polyEval (match j.1 with | 0 => iBasis_8_0 | 1 => iBasis_8_1 | 2 => iBasis_8_2 | 3 => iBasis_8_3 | 4 => iBasis_8_4 | 5 => iBasis_8_5 | 6 => iBasis_8_6 | 7 => iBasis_8_7 | 8 => iBasis_8_8 | 9 => iBasis_8_9 | 10 => iBasis_8_10 | 11 => iBasis_8_11 | _ => []) y) from
      continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_polyEval _).mul (continuous_polyEval _))).intervalIntegrable (-1) 1]
  have hEach : ∀ (i j : Fin 12), (∫ y in (-1 : ℝ)..1,
      (m i * m j) * (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y *
        polyEval (match j.1 with | 0 => iBasis_8_0 | 1 => iBasis_8_1 | 2 => iBasis_8_2 | 3 => iBasis_8_3 | 4 => iBasis_8_4 | 5 => iBasis_8_5 | 6 => iBasis_8_6 | 7 => iBasis_8_7 | 8 => iBasis_8_8 | 9 => iBasis_8_9 | 10 => iBasis_8_10 | 11 => iBasis_8_11 | _ => []) y)) =
      (m i * m j) * (ApertureLogTwo.matQ mPPRawQ_3 i.1 j.1 : ℝ) := fun i j => by
    rw [intervalIntegral.integral_const_mul, int_pp_3 i j]
  have hSumI : ∀ i : Fin 12, (∫ y in (-1 : ℝ)..1, ∑ j : Fin 12,
      (m i * m j) * (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y *
        polyEval (match j.1 with | 0 => iBasis_8_0 | 1 => iBasis_8_1 | 2 => iBasis_8_2 | 3 => iBasis_8_3 | 4 => iBasis_8_4 | 5 => iBasis_8_5 | 6 => iBasis_8_6 | 7 => iBasis_8_7 | 8 => iBasis_8_8 | 9 => iBasis_8_9 | 10 => iBasis_8_10 | 11 => iBasis_8_11 | _ => []) y)) =
      ∑ j : Fin 12, (m i * m j) * (ApertureLogTwo.matQ mPPRawQ_3 i.1 j.1 : ℝ) := fun i => by
    rw [intervalIntegral.integral_finsetSum fun j _ =>
      (show Continuous fun y : ℝ => (m i * m j) *
        (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | 11 => iBasis_0_11 | _ => []) y *
         polyEval (match j.1 with | 0 => iBasis_8_0 | 1 => iBasis_8_1 | 2 => iBasis_8_2 | 3 => iBasis_8_3 | 4 => iBasis_8_4 | 5 => iBasis_8_5 | 6 => iBasis_8_6 | 7 => iBasis_8_7 | 8 => iBasis_8_8 | 9 => iBasis_8_9 | 10 => iBasis_8_10 | 11 => iBasis_8_11 | _ => []) y) from
        continuous_const.mul ((continuous_polyEval _).mul (continuous_polyEval _))).intervalIntegrable (-1) 1]
    exact Finset.sum_congr rfl fun j _ => hEach i j
  rw [show ((7 : ℕ).factorial : ℝ) = 5040 by norm_num [Nat.factorial]]
  simp_rw [hSumI, sum_finK, matQ_eq_qcoeffAt]
  dsimp only [mPPRawQ_3, qcoeffAt, qlistAt, qOddMat_3, matAt, listAt, coeffAt, m]
  simp only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_zero]
  ring

private theorem hOdd_bound_3 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hLowProj : ∀ y : ℝ, lowProj (dilateLogTwo F) 24 y =
      ∑ k : Fin 12, halfMoment (dilateLogTwo F) k * basisFn k y)
    (hHopp : ∀ r : ℕ, regionalLegendreMoment (dilateLogTwo F) (24 + (2 * r + 1)) = 0) :
    let G := dilateLogTwo F
    let m := halfMoment G
    let M_res := (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 24 x) ^ 2) / 2
    apow0_8 * (∑ i : Fin 12, ∑ j : Fin 12, qOddMat_3 i j * m i * m j) -
      (∑ i : Fin 12, (errApow_8 * qOddRowAbs_3 i) * m i ^ 2) -
      ((758215087248897189698082177505805158304254384420441 / 3125000000000000000000000000000000000000000000000000000 : ℝ) * ∑ r ∈ Finset.range 4,
        ((2 * ↑(24 + 2 * r) + 1) / 2) * (∑ i : Fin 12, m i * gHi_3 i r) ^ 2) -
      ((1 / 10000 : ℝ) + (22557250092361518979566609068529228089780654586780885254538200430789283596098329818441434603407994823459309232798751189533174099872231837246879315921935155407331594126769932678225759225724499012476352239023989 / 3795412406428229602825882065186703220341047511512819244508569433840429098759629451289235019100310039491848137147870930625982176425560167199889414890861467136611133440000000000000000000000000000000000000000000000000 : ℝ)) * M_res ≤
      ((-127 / 154828800 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 7 * autocorr F t) /
        (2 * apertureLogTwo) := by
  intro G m M_res
  have hA_pos : 0 < apertureLogTwo := apertureLogTwo_pos
  set R_res : ℝ → ℝ := fun x => G x - lowProj G 24 x
  have hRc : Continuous R_res := hGc.sub (contDiff_lowProj G _ (k := 0)).continuous
  have hMres_nn : 0 ≤ M_res := div_nonneg (setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _) (by norm_num)
  have hIntR2 : (∫ x in Icc (-1 : ℝ) 1, R_res x ^ 2) = 2 * M_res := by dsimp [R_res, M_res]; ring
  have hpi_lo : piLo ≤ Real.pi := (pi_bounds_d20).1
  have hpi_pos : 0 < piLo := by norm_num [piLo]
  have h4pi : 4 / Real.pi ^ 2 ≤ 4 / piLo ^ 2 := by
    have hp2 : piLo ^ 2 ≤ Real.pi ^ 2 := pow_le_pow_left₀ hpi_pos.le hpi_lo 2
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hp2
  have hdil := dilated_correlation_moment_log_two F 7
  have hdec := odd_lag_moment_lowProj_decomp hGc hsG (m := 24) (q := 3) (by omega)
  change (∫ t in Ioc (0 : ℝ) 2, t ^ 7 * autocorr G t) =
    ((7 : ℕ).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, lowProj G 24 y * iterPrim 8 (lowProj G 24) y) +
    2 * ((7 : ℕ).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, R_res y * iterPrim 8 (lowProj G 24) y) +
    (-1 : ℝ) ^ (3 + 1) * ((7 : ℕ).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, iterPrim (3 + 1) R_res y ^ 2) at hdec
  have hPP := hPP_eq_3 hLowProj
  have hPP_pert := symm_quad_scale_pert qOddMat_3 qOddMat_3_sym abs_aperture_pow_8_sub m
  simp_rw [qOddRowAbs_3_eq] at hPP_pert
  have hWirt := iterPrim_sq_le_wirtinger hRc (m := 24) (fun n hn => sub_lowProj_moment_lt hGc hn) (3 + 1) (by omega)
  have hWirt' : (∫ y in (-1 : ℝ)..1, iterPrim (3 + 1) R_res y ^ 2) ≤ (4 / piLo ^ 2) ^ (3 + 1) * (2 * M_res) := by
    rw [hIntR2] at hWirt
    exact hWirt.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h4pi (3 + 1)) (by positivity))
  have hCross := high_mode_cross_sq_le hGc (m := 24) (q := 3) (by omega) hHopp
  change (∫ y in (-1 : ℝ)..1, R_res y * iterPrim 8 (lowProj G 24) y) ^ 2 ≤
    (∑ r ∈ Finset.range (3 + 1), ((2 * ↑(24 + 2 * r) + 1) / 2) *
      regionalLegendreMoment (iterPrim 8 (lowProj G 24)) (24 + 2 * r) ^ 2) *
    (∫ y in Icc (-1 : ℝ) 1, R_res y ^ 2) at hCross
  rw [hIntR2] at hCross
  have hMomLin : ∀ r ∈ Finset.range (3 + 1), regionalLegendreMoment (iterPrim 8 (lowProj G 24)) (24 + 2 * r) =
      ∑ i : Fin 12, m i * gHi_3 i r := fun r hr => by
    have hlin : regionalLegendreMoment (iterPrim 8 (lowProj G 24)) (24 + 2 * r) =
        ∑ i : Fin 12, m i * regionalLegendreMoment (polyEval (match i.1 with | 0 => iBasis_8_0 | 1 => iBasis_8_1 | 2 => iBasis_8_2 | 3 => iBasis_8_3 | 4 => iBasis_8_4 | 5 => iBasis_8_5 | 6 => iBasis_8_6 | 7 => iBasis_8_7 | 8 => iBasis_8_8 | 9 => iBasis_8_9 | 10 => iBasis_8_10 | 11 => iBasis_8_11 | _ => [])) (24 + 2 * r) := by
      unfold regionalLegendreMoment
      have hfn : ∀ x : ℝ, iterPrim 8 (lowProj G 24) x * legP (24 + 2 * r) x =
          ∑ i : Fin 12, m i * (polyEval (match i.1 with | 0 => iBasis_8_0 | 1 => iBasis_8_1 | 2 => iBasis_8_2 | 3 => iBasis_8_3 | 4 => iBasis_8_4 | 5 => iBasis_8_5 | 6 => iBasis_8_6 | 7 => iBasis_8_7 | 8 => iBasis_8_8 | 9 => iBasis_8_9 | 10 => iBasis_8_10 | 11 => iBasis_8_11 | _ => []) x * legP (24 + 2 * r) x) := fun x => by
        rw [hIterP_eq_3 hLowProj x, Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by dsimp only [m]; ring
      simp_rw [hfn]
      rw [integral_finsetSum _ fun i _ =>
        (show Continuous fun x : ℝ => m i * (polyEval (match i.1 with | 0 => iBasis_8_0 | 1 => iBasis_8_1 | 2 => iBasis_8_2 | 3 => iBasis_8_3 | 4 => iBasis_8_4 | 5 => iBasis_8_5 | 6 => iBasis_8_6 | 7 => iBasis_8_7 | 8 => iBasis_8_8 | 9 => iBasis_8_9 | 10 => iBasis_8_10 | 11 => iBasis_8_11 | _ => []) x * legP (24 + 2 * r) x) from
          continuous_const.mul ((continuous_polyEval _).mul (continuous_legP _))).integrableOn_Icc]
      exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    rw [hlin]; exact Finset.sum_congr rfl fun i _ => by rw [gHi_eq_3 i r hr]
  set A_sp : ℝ := ∑ r ∈ Finset.range (3 + 1), ((2 * ↑(24 + 2 * r) + 1) / 2) *
    (∑ i : Fin 12, m i * gHi_3 i r) ^ 2
  have hAsp_eq : (∑ r ∈ Finset.range (3 + 1), ((2 * ↑(24 + 2 * r) + 1) / 2) *
      regionalLegendreMoment (iterPrim 8 (lowProj G 24)) (24 + 2 * r) ^ 2) = A_sp :=
    Finset.sum_congr rfl fun r hr => by rw [hMomLin r hr]
  rw [hAsp_eq] at hCross
  set w_true : ℝ := ((127 / 309657600 : ℝ) * ((7 : ℕ).factorial : ℝ)) * apertureLogTwo ^ 8
  have hw_nn : 0 ≤ w_true := by dsimp [w_true]; positivity
  have hw_le : w_true ≤ (27535705679152244848103771 / 250000000000000000000000000000 : ℝ) := by
    obtain ⟨_, h2u⟩ := log_two_bounds_d26; dsimp only [w_true]; unfold apertureLogTwo
    have hp : (Real.log 2) ^ 8 ≤ logTwoHi ^ 8 := pow_le_pow_left₀ (apertureLogTwo_pos.le) h2u 8
    have hc : ((127 / 309657600 : ℝ) * ((7 : ℕ).factorial : ℝ)) * logTwoHi ^ 8 ≤ (27535705679152244848103771 / 250000000000000000000000000000 : ℝ) := by
      norm_num [Nat.factorial, logTwoHi]
    nlinarith [hp, hc, (show (0 : ℝ) ≤ (127 / 309657600 : ℝ) * ((7 : ℕ).factorial : ℝ) by positivity)]
  have hAsp_nn : 0 ≤ A_sp := Finset.sum_nonneg fun r _ => mul_nonneg (by positivity) (sq_nonneg _)
  set I_RP : ℝ := ∫ y in (-1 : ℝ)..1, R_res y * iterPrim 8 (lowProj G 24) y
  have hY2 : (w_true * I_RP) ^ 2 ≤ ((27535705679152244848103771 / 250000000000000000000000000000 : ℝ)) ^ 2 * (A_sp * (2 * M_res)) := by
    rw [mul_pow]
    have hw2 : w_true ^ 2 ≤ ((27535705679152244848103771 / 250000000000000000000000000000 : ℝ)) ^ 2 := pow_le_pow_left₀ hw_nn hw_le 2
    exact (mul_le_mul_of_nonneg_right hw2 (sq_nonneg I_RP)).trans (mul_le_mul_of_nonneg_left hCross (sq_nonneg _))
  have hy := cross_spillover_young (by norm_num : (0 : ℝ) ≤ (27535705679152244848103771 / 250000000000000000000000000000 : ℝ)) hAsp_nn hMres_nn
    (by norm_num : (0 : ℝ) < (1 / 10000 : ℝ)) hY2
  have hw_wirt : w_true * (∫ y in (-1 : ℝ)..1, iterPrim (3 + 1) R_res y ^ 2) ≤ (22557250092361518979566609068529228089780654586780885254538200430789283596098329818441434603407994823459309232798751189533174099872231837246879315921935155407331594126769932678225759225724499012476352239023989 / 3795412406428229602825882065186703220341047511512819244508569433840429098759629451289235019100310039491848137147870930625982176425560167199889414890861467136611133440000000000000000000000000000000000000000000000000 : ℝ) * M_res := by
    have hw_ex : w_true ≤ (22557250092361518979566609068529228089780654586780885254538200430789283596098329818441434603407994823459309232798751189533174099872231837246879315921935155407331594126769932678225759225724499012476352239023989 / 204800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
      obtain ⟨_, h2u⟩ := log_two_bounds_d26; dsimp only [w_true]; unfold apertureLogTwo
      have hp : (Real.log 2) ^ 8 ≤ logTwoHi ^ 8 := pow_le_pow_left₀ (apertureLogTwo_pos.le) h2u 8
      have hc : ((127 / 309657600 : ℝ) * ((7 : ℕ).factorial : ℝ)) * logTwoHi ^ 8 = (22557250092361518979566609068529228089780654586780885254538200430789283596098329818441434603407994823459309232798751189533174099872231837246879315921935155407331594126769932678225759225724499012476352239023989 / 204800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
        norm_num [Nat.factorial, logTwoHi]
      nlinarith [hp, hc, (show (0 : ℝ) ≤ (127 / 309657600 : ℝ) * ((7 : ℕ).factorial : ℝ) by positivity)]
    have h1 := mul_le_mul hw_ex hWirt' (by rw [intervalIntegral.integral_of_le (by norm_num)]; exact setIntegral_nonneg measurableSet_Ioc fun _ _ => sq_nonneg _) (by norm_num)
    have h2 : (22557250092361518979566609068529228089780654586780885254538200430789283596098329818441434603407994823459309232798751189533174099872231837246879315921935155407331594126769932678225759225724499012476352239023989 / 204800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * ((4 / piLo ^ 2) ^ (3 + 1) * (2 * M_res)) = (22557250092361518979566609068529228089780654586780885254538200430789283596098329818441434603407994823459309232798751189533174099872231837246879315921935155407331594126769932678225759225724499012476352239023989 / 3795412406428229602825882065186703220341047511512819244508569433840429098759629451289235019100310039491848137147870930625982176425560167199889414890861467136611133440000000000000000000000000000000000000000000000000 : ℝ) * M_res := by
      norm_num [piLo]; ring
    linarith
  have hdiv_tot : ((-127 / 154828800 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 7 * autocorr F t) / (2 * apertureLogTwo) =
      apertureLogTwo ^ 8 * (((-127 / 309657600 : ℝ) * ((7 : ℕ).factorial : ℝ)) *
        (∫ y in (-1 : ℝ)..1, lowProj G 24 y * iterPrim 8 (lowProj G 24) y)) +
      (-1 : ℝ) * (2 * (w_true * I_RP)) -
      w_true * (∫ y in (-1 : ℝ)..1, iterPrim (3 + 1) R_res y ^ 2) := by
    rw [hdil, hdec]; dsimp [w_true, I_RP]; field_simp [hA_pos.ne']; norm_num; ring
  rw [hdiv_tot, hPP]
  have hsc_eq : (2 * ((27535705679152244848103771 / 250000000000000000000000000000 : ℝ)) ^ 2 / (1 / 10000 : ℝ)) = (758215087248897189698082177505805158304254384420441 / 3125000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num
  rw [hsc_eq] at hy
  linarith [hPP_pert, hy.2, hw_wirt]

private theorem bFast_quad_decomp (m : Fin 12 → ℝ) :
    (∑ i : Fin 12, ∑ j : Fin 12, bFastMat i j * m i * m j) =
      (∑ k : Fin 12, ((83986301180386383586712497 / 22309287000000000000000000 : ℝ) * (2 * (degAt k : ℝ) + 1)) * m k ^ 2 -
        ((0 : ℝ) * m ⟨0, by omega⟩ ^ 2 + (15 / 2 : ℝ) * m ⟨1, by omega⟩ ^ 2 + (75 / 4 : ℝ) * m ⟨2, by omega⟩ ^ 2 + (637 / 20 : ℝ) * m ⟨3, by omega⟩ ^ 2 + (12937 / 280 : ℝ) * m ⟨4, by omega⟩ ^ 2 + (7381 / 120 : ℝ) * m ⟨5, by omega⟩ ^ 2 + (430105 / 5544 : ℝ) * m ⟨6, by omega⟩ ^ 2 + (33980257 / 360360 : ℝ) * m ⟨7, by omega⟩ ^ 2 + (2436559 / 21840 : ℝ) * m ⟨8, by omega⟩ ^ 2 + (528149137 / 4084080 : ℝ) * m ⟨9, by omega⟩ ^ 2 + (2289240535 / 15519504 : ℝ) * m ⟨10, by omega⟩ ^ 2 + (859193865 / 5173168 : ℝ) * m ⟨11, by omega⟩ ^ 2)) +
      (-(apow0_1 * (-((1 / 2 : ℝ) * m ⟨0, by omega⟩ ^ 2)) - errApow_1 * (1 / 2 : ℝ) * m ⟨0, by omega⟩ ^ 2)) +
      ((-(apow0_1 * (∑ i : Fin 12, ∑ j : Fin 12, qEvMat_0 i j * m i * m j) - (∑ i : Fin 12, (errApow_1 * qEvRowAbs_0 i) * m i ^ 2))) +
       (-(apow0_3 * (∑ i : Fin 12, ∑ j : Fin 12, qEvMat_1 i j * m i * m j) - (∑ i : Fin 12, (errApow_3 * qEvRowAbs_1 i) * m i ^ 2))) +
       (-(apow0_5 * (∑ i : Fin 12, ∑ j : Fin 12, qEvMat_2 i j * m i * m j) - (∑ i : Fin 12, (errApow_5 * qEvRowAbs_2 i) * m i ^ 2))) +
       (-(apow0_7 * (∑ i : Fin 12, ∑ j : Fin 12, qEvMat_3 i j * m i * m j) - (∑ i : Fin 12, (errApow_7 * qEvRowAbs_3 i) * m i ^ 2))) +
       (-(apow0_9 * (∑ i : Fin 12, ∑ j : Fin 12, qEvMat_4 i j * m i * m j) - (∑ i : Fin 12, (errApow_9 * qEvRowAbs_4 i) * m i ^ 2))) +
       (-(apow0_11 * (∑ i : Fin 12, ∑ j : Fin 12, qEvMat_5 i j * m i * m j) - (∑ i : Fin 12, (errApow_11 * qEvRowAbs_5 i) * m i ^ 2))) +
       (-(apow0_13 * (∑ i : Fin 12, ∑ j : Fin 12, qEvMat_6 i j * m i * m j) - (∑ i : Fin 12, (errApow_13 * qEvRowAbs_6 i) * m i ^ 2))) +
       (-(apow0_15 * (∑ i : Fin 12, ∑ j : Fin 12, qEvMat_7 i j * m i * m j) - (∑ i : Fin 12, (errApow_15 * qEvRowAbs_7 i) * m i ^ 2))) +
       (-(apow0_17 * (∑ i : Fin 12, ∑ j : Fin 12, qEvMat_8 i j * m i * m j) - (∑ i : Fin 12, (errApow_17 * qEvRowAbs_8 i) * m i ^ 2))) +
       (-(apow0_19 * (∑ i : Fin 12, ∑ j : Fin 12, qEvMat_9 i j * m i * m j) - (∑ i : Fin 12, (errApow_19 * qEvRowAbs_9 i) * m i ^ 2))) +
       (-(apow0_21 * (∑ i : Fin 12, ∑ j : Fin 12, qEvMat_10 i j * m i * m j) - (∑ i : Fin 12, (errApow_21 * qEvRowAbs_10 i) * m i ^ 2))) +
       (-(apow0_23 * (∑ i : Fin 12, ∑ j : Fin 12, qEvMat_11 i j * m i * m j) - (∑ i : Fin 12, (errApow_23 * qEvRowAbs_11 i) * m i ^ 2)))) +
      ((-(apow0_2 * (∑ i : Fin 12, ∑ j : Fin 12, qOddMat_0 i j * m i * m j) - (∑ i : Fin 12, (errApow_2 * qOddRowAbs_0 i) * m i ^ 2) - ((6261802804445623152330125031301818197576522398243856809 / 62500000000000000000000000000000000000000000000000000000 : ℝ) * ∑ r ∈ Finset.range 1, ((2 * ↑(24 + 2 * r) + 1) / 2) * (∑ i : Fin 12, m i * gHi_0 i r) ^ 2))) +
       (-(apow0_4 * (∑ i : Fin 12, ∑ j : Fin 12, qOddMat_1 i j * m i * m j) - (∑ i : Fin 12, (errApow_4 * qOddRowAbs_1 i) * m i ^ 2) - ((28330699806371863465765559550147688507568454001005121 / 10000000000000000000000000000000000000000000000000000000 : ℝ) * ∑ r ∈ Finset.range 2, ((2 * ↑(24 + 2 * r) + 1) / 2) * (∑ i : Fin 12, m i * gHi_1 i r) ^ 2))) +
       (-(apow0_6 * (∑ i : Fin 12, ∑ j : Fin 12, qOddMat_2 i j * m i * m j) - (∑ i : Fin 12, (errApow_6 * qOddRowAbs_2 i) * m i ^ 2) - ((1817723751476543414437681449293926857541879379346961 / 2000000000000000000000000000000000000000000000000000000 : ℝ) * ∑ r ∈ Finset.range 3, ((2 * ↑(24 + 2 * r) + 1) / 2) * (∑ i : Fin 12, m i * gHi_2 i r) ^ 2))) +
       (-(apow0_8 * (∑ i : Fin 12, ∑ j : Fin 12, qOddMat_3 i j * m i * m j) - (∑ i : Fin 12, (errApow_8 * qOddRowAbs_3 i) * m i ^ 2) - ((758215087248897189698082177505805158304254384420441 / 3125000000000000000000000000000000000000000000000000000 : ℝ) * ∑ r ∈ Finset.range 4, ((2 * ↑(24 + 2 * r) + 1) / 2) * (∑ i : Fin 12, m i * gHi_3 i r) ^ 2)))) +
      ((-17328679513998632735257514471992062272782418444248379513998632735430803 / 6250000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * (∑ k : Fin 12, vPoleClean k * m k) ^ 2 + (51986038541995898206292409 / 156250000000000000000000000000000000000000000000000000000000 : ℝ) * ∑ k : Fin 12, m k ^ 2) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat]
  simp_rw [sum_finK]
  dsimp only [bFastMat, degAt, vPoleClean, gHi_0, gHi_1, gHi_2, gHi_3, qEvMat_0, qEvRowAbs_0, qEvMat_1, qEvRowAbs_1, qEvMat_2, qEvRowAbs_2, qEvMat_3, qEvRowAbs_3, qEvMat_4, qEvRowAbs_4, qEvMat_5, qEvRowAbs_5, qEvMat_6, qEvRowAbs_6, qEvMat_7, qEvRowAbs_7, qEvMat_8, qEvRowAbs_8, qEvMat_9, qEvRowAbs_9, qEvMat_10, qEvRowAbs_10, qEvMat_11, qEvRowAbs_11, qOddMat_0, qOddRowAbs_0, qOddMat_1, qOddRowAbs_1, qOddMat_2, qOddRowAbs_2, qOddMat_3, qOddRowAbs_3, apow0_1, errApow_1, apow0_2, errApow_2, apow0_3, errApow_3, apow0_4, errApow_4, apow0_5, errApow_5, apow0_6, errApow_6, apow0_7, errApow_7, apow0_8, errApow_8, apow0_9, errApow_9, apow0_10, errApow_10, apow0_11, errApow_11, apow0_12, errApow_12, apow0_13, errApow_13, apow0_14, errApow_14, apow0_15, errApow_15, apow0_16, errApow_16, apow0_17, errApow_17, apow0_18, errApow_18, apow0_19, errApow_19, apow0_20, errApow_20, apow0_21, errApow_21, apow0_22, errApow_22, apow0_23, errApow_23, matAt, listAt, coeffAt]
  ring

private theorem hMomSame_lem {G : ℝ → ℝ} (hGc : Continuous G)
    (hGpar : ∀ u, G (-u) = G u) (k : Fin 12) :
    regionalLegendreMoment G (degAt k) = 2 * halfMoment G k := by
  unfold regionalLegendreMoment
  refine even_integral_Icc_unit (hGc.mul (continuous_legP _)) fun x => ?_
  rw [hGpar x, legP_neg, show degAt k = 2 * k.1 from rfl, pow_mul, neg_one_sq, one_pow]; ring

private theorem hMomOpp_lem {G : ℝ → ℝ}
    (hGpar : ∀ u, G (-u) = G u) (r : ℕ) :
    regionalLegendreMoment G (2 * r + 1) = 0 := by
  unfold regionalLegendreMoment
  refine odd_integral_Icc_unit_zero fun x => ?_
  rw [hGpar x, legP_neg, pow_succ, pow_mul, neg_one_sq, one_pow]; ring

private theorem hHopp_lem {G : ℝ → ℝ}
    (hGpar : ∀ u, G (-u) = G u) (r : ℕ) :
    regionalLegendreMoment G (24 + (2 * r + 1)) = 0 := by
  rw [show 24 + (2 * r + 1) = 2 * (12 + r) + 1 by omega]; exact hMomOpp_lem hGpar _

private theorem hLowProj_eq {G : ℝ → ℝ} (hGc : Continuous G)
    (hGpar : ∀ u, G (-u) = G u) (y : ℝ) :
    lowProj G 24 y = ∑ k : Fin 12, halfMoment G k * basisFn k y := by
  set m := halfMoment G
  unfold lowProj regionalLegendreSum projCoeff
  rw [sum_range_24, sum_finK]
  have hz0 : regionalLegendreMoment G 1 = 0 := hMomOpp_lem hGpar 0
  have hs0 : regionalLegendreMoment G 0 = 2 * m ⟨0, by omega⟩ := hMomSame_lem hGc hGpar ⟨0, by omega⟩
  have hz1 : regionalLegendreMoment G 3 = 0 := hMomOpp_lem hGpar 1
  have hs1 : regionalLegendreMoment G 2 = 2 * m ⟨1, by omega⟩ := hMomSame_lem hGc hGpar ⟨1, by omega⟩
  have hz2 : regionalLegendreMoment G 5 = 0 := hMomOpp_lem hGpar 2
  have hs2 : regionalLegendreMoment G 4 = 2 * m ⟨2, by omega⟩ := hMomSame_lem hGc hGpar ⟨2, by omega⟩
  have hz3 : regionalLegendreMoment G 7 = 0 := hMomOpp_lem hGpar 3
  have hs3 : regionalLegendreMoment G 6 = 2 * m ⟨3, by omega⟩ := hMomSame_lem hGc hGpar ⟨3, by omega⟩
  have hz4 : regionalLegendreMoment G 9 = 0 := hMomOpp_lem hGpar 4
  have hs4 : regionalLegendreMoment G 8 = 2 * m ⟨4, by omega⟩ := hMomSame_lem hGc hGpar ⟨4, by omega⟩
  have hz5 : regionalLegendreMoment G 11 = 0 := hMomOpp_lem hGpar 5
  have hs5 : regionalLegendreMoment G 10 = 2 * m ⟨5, by omega⟩ := hMomSame_lem hGc hGpar ⟨5, by omega⟩
  have hz6 : regionalLegendreMoment G 13 = 0 := hMomOpp_lem hGpar 6
  have hs6 : regionalLegendreMoment G 12 = 2 * m ⟨6, by omega⟩ := hMomSame_lem hGc hGpar ⟨6, by omega⟩
  have hz7 : regionalLegendreMoment G 15 = 0 := hMomOpp_lem hGpar 7
  have hs7 : regionalLegendreMoment G 14 = 2 * m ⟨7, by omega⟩ := hMomSame_lem hGc hGpar ⟨7, by omega⟩
  have hz8 : regionalLegendreMoment G 17 = 0 := hMomOpp_lem hGpar 8
  have hs8 : regionalLegendreMoment G 16 = 2 * m ⟨8, by omega⟩ := hMomSame_lem hGc hGpar ⟨8, by omega⟩
  have hz9 : regionalLegendreMoment G 19 = 0 := hMomOpp_lem hGpar 9
  have hs9 : regionalLegendreMoment G 18 = 2 * m ⟨9, by omega⟩ := hMomSame_lem hGc hGpar ⟨9, by omega⟩
  have hz10 : regionalLegendreMoment G 21 = 0 := hMomOpp_lem hGpar 10
  have hs10 : regionalLegendreMoment G 20 = 2 * m ⟨10, by omega⟩ := hMomSame_lem hGc hGpar ⟨10, by omega⟩
  have hz11 : regionalLegendreMoment G 23 = 0 := hMomOpp_lem hGpar 11
  have hs11 : regionalLegendreMoment G 22 = 2 * m ⟨11, by omega⟩ := hMomSame_lem hGc hGpar ⟨11, by omega⟩
  dsimp only [basisFn, degAt]
  rw [hs0, hz0, hs1, hz1, hs2, hz2, hs3, hz3, hs4, hz4, hs5, hz5,
    hs6, hz6, hs7, hz7, hs8, hz8, hs9, hz9, hs10, hz10, hs11, hz11]
  norm_num; ring

private theorem hMres_eq_lem {G : ℝ → ℝ} (hGc : Continuous G)
    (hGpar : ∀ u, G (-u) = G u) :
    (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 24 x) ^ 2) / 2 =
      (∫ u in (0 : ℝ)..1, G u ^ 2) - ∑ k : Fin 12, (2 * (degAt k : ℝ) + 1) * halfMoment G k ^ 2 := by
  set m := halfMoment G
  set M : ℝ := ∫ u in (0 : ℝ)..1, G u ^ 2
  set M_res : ℝ := (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 24 x) ^ 2) / 2
  have hGsq : ∀ u, G (-u) ^ 2 = G u ^ 2 := fun u => by rw [hGpar u]
  have hM_Icc : (∫ x in Icc (-1 : ℝ) 1, G x ^ 2) = 2 * M := even_integral_Icc_unit (hGc.pow 2) hGsq
  have hIntR2 : (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 24 x) ^ 2) = 2 * M_res := by dsimp [M_res]; ring
  have hp := projection_residual_mass_pub hGc 24
  change (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 24 x) ^ 2) = (∫ x in Icc (-1 : ℝ) 1, G x ^ 2) - _ at hp
  rw [hIntR2, hM_Icc, sum_range_24] at hp
  have hz0 : regionalLegendreMoment G 1 = 0 := hMomOpp_lem hGpar 0
  have hs0 : regionalLegendreMoment G 0 = 2 * m ⟨0, by omega⟩ := hMomSame_lem hGc hGpar ⟨0, by omega⟩
  have hz1 : regionalLegendreMoment G 3 = 0 := hMomOpp_lem hGpar 1
  have hs1 : regionalLegendreMoment G 2 = 2 * m ⟨1, by omega⟩ := hMomSame_lem hGc hGpar ⟨1, by omega⟩
  have hz2 : regionalLegendreMoment G 5 = 0 := hMomOpp_lem hGpar 2
  have hs2 : regionalLegendreMoment G 4 = 2 * m ⟨2, by omega⟩ := hMomSame_lem hGc hGpar ⟨2, by omega⟩
  have hz3 : regionalLegendreMoment G 7 = 0 := hMomOpp_lem hGpar 3
  have hs3 : regionalLegendreMoment G 6 = 2 * m ⟨3, by omega⟩ := hMomSame_lem hGc hGpar ⟨3, by omega⟩
  have hz4 : regionalLegendreMoment G 9 = 0 := hMomOpp_lem hGpar 4
  have hs4 : regionalLegendreMoment G 8 = 2 * m ⟨4, by omega⟩ := hMomSame_lem hGc hGpar ⟨4, by omega⟩
  have hz5 : regionalLegendreMoment G 11 = 0 := hMomOpp_lem hGpar 5
  have hs5 : regionalLegendreMoment G 10 = 2 * m ⟨5, by omega⟩ := hMomSame_lem hGc hGpar ⟨5, by omega⟩
  have hz6 : regionalLegendreMoment G 13 = 0 := hMomOpp_lem hGpar 6
  have hs6 : regionalLegendreMoment G 12 = 2 * m ⟨6, by omega⟩ := hMomSame_lem hGc hGpar ⟨6, by omega⟩
  have hz7 : regionalLegendreMoment G 15 = 0 := hMomOpp_lem hGpar 7
  have hs7 : regionalLegendreMoment G 14 = 2 * m ⟨7, by omega⟩ := hMomSame_lem hGc hGpar ⟨7, by omega⟩
  have hz8 : regionalLegendreMoment G 17 = 0 := hMomOpp_lem hGpar 8
  have hs8 : regionalLegendreMoment G 16 = 2 * m ⟨8, by omega⟩ := hMomSame_lem hGc hGpar ⟨8, by omega⟩
  have hz9 : regionalLegendreMoment G 19 = 0 := hMomOpp_lem hGpar 9
  have hs9 : regionalLegendreMoment G 18 = 2 * m ⟨9, by omega⟩ := hMomSame_lem hGc hGpar ⟨9, by omega⟩
  have hz10 : regionalLegendreMoment G 21 = 0 := hMomOpp_lem hGpar 10
  have hs10 : regionalLegendreMoment G 20 = 2 * m ⟨10, by omega⟩ := hMomSame_lem hGc hGpar ⟨10, by omega⟩
  have hz11 : regionalLegendreMoment G 23 = 0 := hMomOpp_lem hGpar 11
  have hs11 : regionalLegendreMoment G 22 = 2 * m ⟨11, by omega⟩ := hMomSame_lem hGc hGpar ⟨11, by omega⟩
  rw [hs0, hz0, hs1, hz1, hs2, hz2, hs3, hz3, hs4, hz4, hs5, hz5,
    hs6, hz6, hs7, hz7, hs8, hz8, hs9, hz9, hs10, hz10, hs11, hz11] at hp
  have hp' : 2 * M_res = 2 * (M - ∑ k : Fin 12, (2 * (degAt k : ℝ) + 1) * m k ^ 2) := by
    rw [hp, sum_finK]; dsimp only [degAt]; ring
  linarith

private theorem hRegLog_lem {G : ℝ → ℝ} (hG1 : ContDiff ℝ 1 G)
    (hGpar : ∀ u, G (-u) = G u) :
    ((1347822955 / 356948592 : ℝ) : ℝ) * ((∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 24 x) ^ 2) / 2) +
      ((0 : ℝ) * halfMoment G ⟨0, by omega⟩ ^ 2 + (15 / 2 : ℝ) * halfMoment G ⟨1, by omega⟩ ^ 2 + (75 / 4 : ℝ) * halfMoment G ⟨2, by omega⟩ ^ 2 + (637 / 20 : ℝ) * halfMoment G ⟨3, by omega⟩ ^ 2 + (12937 / 280 : ℝ) * halfMoment G ⟨4, by omega⟩ ^ 2 + (7381 / 120 : ℝ) * halfMoment G ⟨5, by omega⟩ ^ 2 + (430105 / 5544 : ℝ) * halfMoment G ⟨6, by omega⟩ ^ 2 + (33980257 / 360360 : ℝ) * halfMoment G ⟨7, by omega⟩ ^ 2 + (2436559 / 21840 : ℝ) * halfMoment G ⟨8, by omega⟩ ^ 2 + (528149137 / 4084080 : ℝ) * halfMoment G ⟨9, by omega⟩ ^ 2 + (2289240535 / 15519504 : ℝ) * halfMoment G ⟨10, by omega⟩ ^ 2 + (859193865 / 5173168 : ℝ) * halfMoment G ⟨11, by omega⟩ ^ 2) ≤
      regionalLogEnergy G / 4 := by
  have hGc : Continuous G := hG1.continuous
  set m := halfMoment G
  set M_res : ℝ := (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 24 x) ^ 2) / 2
  have hIntR2 : (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 24 x) ^ 2) = 2 * M_res := by dsimp [M_res]; ring
  have hg := regionalLogEnergy_ge_low_add_gap_residual hG1 24
  change _ + regionalLogEigenvalue 24 * (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 24 x) ^ 2) ≤ _ at hg
  rw [hIntR2, sum_range_24] at hg
  have hz0 : regionalLegendreMoment G 1 = 0 := hMomOpp_lem hGpar 0
  have hs0 : regionalLegendreMoment G 0 = 2 * m ⟨0, by omega⟩ := hMomSame_lem hGc hGpar ⟨0, by omega⟩
  have hz1 : regionalLegendreMoment G 3 = 0 := hMomOpp_lem hGpar 1
  have hs1 : regionalLegendreMoment G 2 = 2 * m ⟨1, by omega⟩ := hMomSame_lem hGc hGpar ⟨1, by omega⟩
  have hz2 : regionalLegendreMoment G 5 = 0 := hMomOpp_lem hGpar 2
  have hs2 : regionalLegendreMoment G 4 = 2 * m ⟨2, by omega⟩ := hMomSame_lem hGc hGpar ⟨2, by omega⟩
  have hz3 : regionalLegendreMoment G 7 = 0 := hMomOpp_lem hGpar 3
  have hs3 : regionalLegendreMoment G 6 = 2 * m ⟨3, by omega⟩ := hMomSame_lem hGc hGpar ⟨3, by omega⟩
  have hz4 : regionalLegendreMoment G 9 = 0 := hMomOpp_lem hGpar 4
  have hs4 : regionalLegendreMoment G 8 = 2 * m ⟨4, by omega⟩ := hMomSame_lem hGc hGpar ⟨4, by omega⟩
  have hz5 : regionalLegendreMoment G 11 = 0 := hMomOpp_lem hGpar 5
  have hs5 : regionalLegendreMoment G 10 = 2 * m ⟨5, by omega⟩ := hMomSame_lem hGc hGpar ⟨5, by omega⟩
  have hz6 : regionalLegendreMoment G 13 = 0 := hMomOpp_lem hGpar 6
  have hs6 : regionalLegendreMoment G 12 = 2 * m ⟨6, by omega⟩ := hMomSame_lem hGc hGpar ⟨6, by omega⟩
  have hz7 : regionalLegendreMoment G 15 = 0 := hMomOpp_lem hGpar 7
  have hs7 : regionalLegendreMoment G 14 = 2 * m ⟨7, by omega⟩ := hMomSame_lem hGc hGpar ⟨7, by omega⟩
  have hz8 : regionalLegendreMoment G 17 = 0 := hMomOpp_lem hGpar 8
  have hs8 : regionalLegendreMoment G 16 = 2 * m ⟨8, by omega⟩ := hMomSame_lem hGc hGpar ⟨8, by omega⟩
  have hz9 : regionalLegendreMoment G 19 = 0 := hMomOpp_lem hGpar 9
  have hs9 : regionalLegendreMoment G 18 = 2 * m ⟨9, by omega⟩ := hMomSame_lem hGc hGpar ⟨9, by omega⟩
  have hz10 : regionalLegendreMoment G 21 = 0 := hMomOpp_lem hGpar 10
  have hs10 : regionalLegendreMoment G 20 = 2 * m ⟨10, by omega⟩ := hMomSame_lem hGc hGpar ⟨10, by omega⟩
  have hz11 : regionalLegendreMoment G 23 = 0 := hMomOpp_lem hGpar 11
  have hs11 : regionalLegendreMoment G 22 = 2 * m ⟨11, by omega⟩ := hMomSame_lem hGc hGpar ⟨11, by omega⟩
  rw [hs0, hz0, hs1, hz1, hs2, hz2, hs3, hz3, hs4, hz4, hs5, hz5,
    hs6, hz6, hs7, hz7, hs8, hz8, hs9, hz9, hs10, hz10, hs11, hz11] at hg
  rw [regLogEig_0, regLogEig_1, regLogEig_2, regLogEig_3, regLogEig_4, regLogEig_5, regLogEig_6, regLogEig_7, regLogEig_8, regLogEig_9, regLogEig_10, regLogEig_11, regLogEig_12, regLogEig_13, regLogEig_14, regLogEig_15, regLogEig_16, regLogEig_17, regLogEig_18, regLogEig_19, regLogEig_20, regLogEig_21, regLogEig_22, regLogEig_23, regLogEig_24] at hg
  suffices h4 : 4 * (((1347822955 / 356948592 : ℝ) : ℝ) * M_res +
      ((0 : ℝ) * m ⟨0, by omega⟩ ^ 2 + (15 / 2 : ℝ) * m ⟨1, by omega⟩ ^ 2 + (75 / 4 : ℝ) * m ⟨2, by omega⟩ ^ 2 + (637 / 20 : ℝ) * m ⟨3, by omega⟩ ^ 2 + (12937 / 280 : ℝ) * m ⟨4, by omega⟩ ^ 2 + (7381 / 120 : ℝ) * m ⟨5, by omega⟩ ^ 2 + (430105 / 5544 : ℝ) * m ⟨6, by omega⟩ ^ 2 + (33980257 / 360360 : ℝ) * m ⟨7, by omega⟩ ^ 2 + (2436559 / 21840 : ℝ) * m ⟨8, by omega⟩ ^ 2 + (528149137 / 4084080 : ℝ) * m ⟨9, by omega⟩ ^ 2 + (2289240535 / 15519504 : ℝ) * m ⟨10, by omega⟩ ^ 2 + (859193865 / 5173168 : ℝ) * m ⟨11, by omega⟩ ^ 2)) ≤
      regionalLogEnergy G by linarith
  refine le_trans (le_of_eq ?_) hg
  ring

private theorem hPole_bound {F : ℝ → ℝ} (hFc : Continuous F)
    (hs : tsupport F ⊆ Icc (-apertureLogTwo) apertureLogTwo)
    (hpar : ∀ x, F (-x) = F x) :
    let G := dilateLogTwo F;
    let m := halfMoment G;
    let M := ∫ u in (0 : ℝ)..1, G u ^ 2;
    -((-17328679513998632735257514471992062272782418444248379513998632735430803 / 6250000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * (∑ k : Fin 12, vPoleClean k * m k) ^ 2) -
      ((51986038541995898206292409 / 156250000000000000000000000000000000000000000000000000000000 : ℝ) * ∑ k : Fin 12, m k ^ 2) - (1 / 10 ^ 24) * M ≤
      (coshPairing F ^ 2 / 2 - sinhPairing F ^ 2 / 2) / (2 * apertureLogTwo) := by
  intro G m M
  have hGc : Continuous G := hFc.comp (continuous_const.mul continuous_id)
  have hS0 : sinhPairing F = 0 := by
    unfold sinhPairing; exact odd_whole_integral_zero fun x => by rw [hpar x, neg_div, Real.sinh_neg]; ring
  rw [hS0, zero_pow two_ne_zero, zero_div, sub_zero]
  have hdA : |apertureLogTwo - poleA0| ≤ 2 / 10 ^ 25 := by
    obtain ⟨h2l, h2u⟩ := log_two_bounds_d26; unfold apertureLogTwo
    have c1 : poleA0 - 2 / 10 ^ 25 ≤ logTwoLo := by norm_num [poleA0, logTwoLo]
    have c2 : logTwoHi ≤ poleA0 + 2 / 10 ^ 25 := by norm_num [poleA0, logTwoHi]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hpole := even_cosh_pole_ge hFc hs hpar (A0 := poleA0) (by norm_num [poleA0]) (by norm_num [poleA0]) hdA
  change 4 * logTwoLo * (1 - 1 / 10 ^ 20) * (∫ u in (0 : ℝ)..1, G u * evenPolePoly poleA0 u) ^ 2 -
    (1 / 10 ^ 24) * M ≤ _ at hpole
  set P0 := ∫ u in (0 : ℝ)..1, G u * evenPolePoly poleA0 u
  set P_clean := ∑ k : Fin 12, vPoleClean k * m k
  have hP0_eq : P0 = ∑ k : Fin 12, vPoleTrue k * m k := by
    dsimp [P0]; unfold evenPolePoly
    have hfn : ∀ u : ℝ, G u * (∑ j ∈ Finset.range 12, (poleA0 * u / 2) ^ (2 * j) / ((2 * j).factorial : ℝ)) =
        ∑ j ∈ Finset.range 12, ((poleA0 / 2) ^ (2 * j) / ((2 * j).factorial : ℝ)) * (u ^ (2 * j) * G u) := fun u => by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
      rw [show poleA0 * u / 2 = (poleA0 / 2) * u by ring, mul_pow]; ring
    simp_rw [hfn]
    rw [intervalIntegral.integral_finsetSum fun j _ =>
      (show Continuous fun u : ℝ => ((poleA0 / 2) ^ (2 * j) / ((2 * j).factorial : ℝ)) * (u ^ (2 * j) * G u) from
        continuous_const.mul ((continuous_pow _).mul hGc)).intervalIntegrable 0 1]
    simp_rw [intervalIntegral.integral_const_mul]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceMul, Nat.reduceAdd]
    rw [show (poleA0 / 2) ^ 0 / ((0 : ℕ).factorial : ℝ) = (1 : ℝ) by norm_num [poleA0, Nat.factorial], show (poleA0 / 2) ^ 2 / ((2 : ℕ).factorial : ℝ) = (48045301391820142466710249657931579549252042527041 / 800000000000000000000000000000000000000000000000000 : ℝ) by norm_num [poleA0, Nat.factorial], show (poleA0 / 2) ^ 4 / ((4 : ℕ).factorial : ℝ) = (769450328610278172958325630611352119723126800822085875938635783641852401892758958534818404405405227 / 1280000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) by norm_num [poleA0, Nat.factorial], show (poleA0 / 2) ^ 6 / ((6 : ℕ).factorial : ℝ) = (12322824314705287963549675577283118475120592810097113277623642064649684147377745125690660320537779471223687334769419487594750372987758814484236747769 / 5120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) by norm_num [poleA0, Nat.factorial], show (poleA0 / 2) ^ 8 / ((8 : ℕ).factorial : ℝ) = (592053808198465065080488221998775471067784814588844944974875802606599886202865387956494049563214359476551070283540729674929866114250486875701396996177447332245733814215139739290501119148814078921529 / 114688000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) by norm_num [poleA0, Nat.factorial], show (poleA0 / 2) ^ 10 / ((10 : ℕ).factorial : ℝ) = (3160600406118903251784174718888543873270903770480627719648283158447353056565586673853575068609254594498077004110270580790892319101714234260906639662976347722230812223790133669201300542499861278997113936652116865172629800463291903066675775677729521 / 458752000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) by norm_num [poleA0, Nat.factorial], show (poleA0 / 2) ^ 12 / ((12 : ℕ).factorial : ℝ) = (50617333030363949975900135670880281773215050990729684037873358309468804485369862856645133004518848597652172813181494246041093914242658878395150194617604234401647809397442695607560905649819829617880101518286254863547125279484363532158865023411200491337853833056604113556889237844799940632708825787 / 8074035200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) by norm_num [poleA0, Nat.factorial], show (poleA0 / 2) ^ 14 / ((14 : ℕ).factorial : ℝ) = (2431925021093968755383186091106193336256286556571252863888359333197816531936350191421046803101141629587687468453894315527882006803936865269901347188786289031232620704113828285107748507417657118515700995893090966980403940005624130944680046333775214786627960691955339452484775834020658812177953209999498067435122928349275037232127738935499305606267 / 587789762560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) by norm_num [poleA0, Nat.factorial], show (poleA0 / 2) ^ 16 / ((16 : ℕ).factorial : ℝ) = (38947523533589428790125570969383467043696979184007826326838429884458365505735209811268670363953309280217147224284266984229943494559208125203954811061159270856187832039873275254046896540133276544656795398587336239416600500615430483948952490726209433794450854731906769886241066008191113224520785543372543984442612922182224783914409908417017174721260243553675798592419444813845051907229091082188649 / 18809272401920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) by norm_num [poleA0, Nat.factorial], show (poleA0 / 2) ^ 18 / ((18 : ℕ).factorial : ℝ) = (207916167404034659588467675020718636220704718819728654549374330783983795572622929463300376594467378415253560946973170228006751203006341848180018490458110135239324702371668760364481986457282598559742603973588029936972108807144921787054350185049599510937198871251436170100194439675469115123599519812940974760071766558684726785748370572912624516685139822722296842808189603345306502337545994704157473299960170455371166219786717042311520613227306401 / 255806104666112000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) by norm_num [poleA0, Nat.factorial], show (poleA0 / 2) ^ 20 / ((20 : ℕ).factorial : ℝ) = (525757627745209271986405456056472953562542628739790384370643811090944922189737111016588476248665254148324763765228665871618003373297569613787139581504920633156599182766113428486720619450413908997547941297981782381473726149510065073219701103553350679236181013304949092394195562664553359541933193531429063636060433462000622265980531282070949256415538048276788270120231266575430117534199768017093843693676089820039187961802224310854425156238916784021168014108227819479372050728082390781770257339 / 2046448837328896000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) by norm_num [poleA0, Nat.factorial], show (poleA0 / 2) ^ 22 / ((22 : ℕ).factorial : ℝ) = (8420061228022319795555076172744666094083529178309490354863576886132484786856645828238803378325911251328055367243807681261026255966124963957814338156552729892801203462604416784945609109045531201197496802533657543527540428406293295038476860843589419625762694477160155315625074938690550405444565787164465062546052456550638318447716897217816537265986343599530114246682798528082636415936619525649020464331354242319559534472088204905392570780200819899293808236163445951545523992777547463499351044191984204360381518992827368731056606442071478734633 / 126061248379459993600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) by norm_num [poleA0, Nat.factorial]]
    have hm_0 := mon_moment_eq_leg_sum hGc ⟨0, by omega⟩; dsimp only [degAt] at hm_0; simp only [Nat.reduceMul, Nat.reduceAdd] at hm_0; rw [sum_finK] at hm_0; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_0
    have hm_1 := mon_moment_eq_leg_sum hGc ⟨1, by omega⟩; dsimp only [degAt] at hm_1; simp only [Nat.reduceMul, Nat.reduceAdd] at hm_1; rw [sum_finK] at hm_1; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_1
    have hm_2 := mon_moment_eq_leg_sum hGc ⟨2, by omega⟩; dsimp only [degAt] at hm_2; simp only [Nat.reduceMul, Nat.reduceAdd] at hm_2; rw [sum_finK] at hm_2; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_2
    have hm_3 := mon_moment_eq_leg_sum hGc ⟨3, by omega⟩; dsimp only [degAt] at hm_3; simp only [Nat.reduceMul, Nat.reduceAdd] at hm_3; rw [sum_finK] at hm_3; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_3
    have hm_4 := mon_moment_eq_leg_sum hGc ⟨4, by omega⟩; dsimp only [degAt] at hm_4; simp only [Nat.reduceMul, Nat.reduceAdd] at hm_4; rw [sum_finK] at hm_4; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_4
    have hm_5 := mon_moment_eq_leg_sum hGc ⟨5, by omega⟩; dsimp only [degAt] at hm_5; simp only [Nat.reduceMul, Nat.reduceAdd] at hm_5; rw [sum_finK] at hm_5; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_5
    have hm_6 := mon_moment_eq_leg_sum hGc ⟨6, by omega⟩; dsimp only [degAt] at hm_6; simp only [Nat.reduceMul, Nat.reduceAdd] at hm_6; rw [sum_finK] at hm_6; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_6
    have hm_7 := mon_moment_eq_leg_sum hGc ⟨7, by omega⟩; dsimp only [degAt] at hm_7; simp only [Nat.reduceMul, Nat.reduceAdd] at hm_7; rw [sum_finK] at hm_7; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_7
    have hm_8 := mon_moment_eq_leg_sum hGc ⟨8, by omega⟩; dsimp only [degAt] at hm_8; simp only [Nat.reduceMul, Nat.reduceAdd] at hm_8; rw [sum_finK] at hm_8; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_8
    have hm_9 := mon_moment_eq_leg_sum hGc ⟨9, by omega⟩; dsimp only [degAt] at hm_9; simp only [Nat.reduceMul, Nat.reduceAdd] at hm_9; rw [sum_finK] at hm_9; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_9
    have hm_10 := mon_moment_eq_leg_sum hGc ⟨10, by omega⟩; dsimp only [degAt] at hm_10; simp only [Nat.reduceMul, Nat.reduceAdd] at hm_10; rw [sum_finK] at hm_10; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_10
    have hm_11 := mon_moment_eq_leg_sum hGc ⟨11, by omega⟩; dsimp only [degAt] at hm_11; simp only [Nat.reduceMul, Nat.reduceAdd] at hm_11; rw [sum_finK] at hm_11; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_11
    rw [hm_0, hm_1, hm_2, hm_3, hm_4, hm_5, hm_6, hm_7, hm_8, hm_9, hm_10, hm_11, sum_finK]
    dsimp only [vPoleTrue, coeffAt, m]; ring
  have hdiff_v : |P0 - P_clean| ≤ (1 / 10 ^ 30 : ℝ) * ∑ k : Fin 12, |m k| := by
    have heq : P0 - P_clean = ∑ k : Fin 12, (vPoleTrue k - vPoleClean k) * m k := by
      rw [hP0_eq]; dsimp only [P_clean]; rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [heq]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]; refine Finset.sum_le_sum fun k _ => ?_
    rw [abs_mul]; refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rcases k with ⟨kv, hkv⟩; interval_cases kv <;> (dsimp only [vPoleTrue, vPoleClean, coeffAt]; norm_num)
  have hdv_sq : (P0 - P_clean) ^ 2 ≤ (12 : ℝ) * (1 / 10 ^ 30 : ℝ) ^ 2 * ∑ k : Fin 12, m k ^ 2 := by
    have h1 := pow_le_pow_left₀ (abs_nonneg _) hdiff_v 2
    rw [sq_abs, mul_pow] at h1
    have hcs := fin_sum_mul_sq_le 12 (fun _ => (1 : ℝ)) (fun k => |m k|)
    simp only [one_mul, one_pow, sq_abs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hcs
    have hcs' := mul_le_mul_of_nonneg_left hcs (by positivity : (0 : ℝ) ≤ (1 / 10 ^ 30 : ℝ) ^ 2)
    linarith
  have hyoung : (1 - 1 / 10 ^ 25 : ℝ) * P_clean ^ 2 - 10 ^ 25 * (P0 - P_clean) ^ 2 ≤ P0 ^ 2 := by
    have h0 : 0 ≤ ((1 / 10 ^ 25 : ℝ) * P_clean + (P0 - P_clean)) ^ 2 := sq_nonneg _
    have hid : P0 ^ 2 - ((1 - 1 / 10 ^ 25 : ℝ) * P_clean ^ 2 - (10 ^ 25 - 1 : ℝ) * (P0 - P_clean) ^ 2) =
        10 ^ 25 * ((1 / 10 ^ 25 : ℝ) * P_clean + (P0 - P_clean)) ^ 2 := by ring
    nlinarith [sq_nonneg (P0 - P_clean)]
  have hsc1 : -(4 * logTwoLo * (1 - 1 / 10 ^ 20) * (1 - 1 / 10 ^ 25)) = (-17328679513998632735257514471992062272782418444248379513998632735430803 / 6250000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num [logTwoLo]
  have hsc2 : 4 * logTwoLo * (10 ^ 25 : ℝ) * ((12 : ℝ) * (1 / 10 ^ 30 : ℝ) ^ 2) = (51986038541995898206292409 / 156250000000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num [logTwoLo]
  have hpos_c : 0 ≤ 4 * logTwoLo * (1 - 1 / 10 ^ 20 : ℝ) := by norm_num [logTwoLo]
  have hm1 := mul_le_mul_of_nonneg_left hyoung hpos_c
  have hm2 := mul_le_mul_of_nonneg_left hdv_sq (show 0 ≤ 4 * logTwoLo * (1 - 1 / 10 ^ 20 : ℝ) * 10 ^ 25 by norm_num [logTwoLo])
  have h1m : 4 * logTwoLo * (1 - 1 / 10 ^ 20 : ℝ) * 10 ^ 25 ≤ 4 * logTwoLo * 10 ^ 25 := by norm_num [logTwoLo]
  nlinarith [mul_le_mul_of_nonneg_right h1m (sq_nonneg (P0 - P_clean))]

private theorem hP2_bound {F : ℝ → ℝ} (hFc : Continuous F)
    (hs : tsupport F ⊆ Icc (-apertureLogTwo) apertureLogTwo)
    (hpar : ∀ x, F (-x) = F x) :
    let G := dilateLogTwo F
    let M := ∫ u in (0 : ℝ)..1, G u ^ 2
    2 * e2Mid * (∫ u in (0 : ℝ)..(1 / 2), G u * G (1 - u)) - (1 / 10000000000000000000000000 : ℝ) * M ≤
      (-2 * (Real.log 2 / Real.sqrt 2) * autocorr F (Real.log 2)) / (2 * apertureLogTwo) := by
  intro G M
  have hGc : Continuous G := hFc.comp (continuous_const.mul continuous_id)
  have hsG : tsupport G ⊆ Icc (-1 : ℝ) 1 := tsupport_dilateLogTwo hs
  have hGpar : ∀ u, G (-u) = G u := fun u => by unfold G dilateLogTwo; rw [mul_neg, hpar]
  have hGsgn : ∀ u, G (-u) = (1 : ℝ) * G u := fun u => by rw [hGpar u]; ring
  have hdil1 := dilated_autocorr_log_two F 1
  unfold apertureLogTwo at hdil1; rw [mul_one] at hdil1
  have hac1 := autocorr_one_of_parity hGc hsG hGsgn
  have hrew : (-2 * (Real.log 2 / Real.sqrt 2) * autocorr F (Real.log 2)) / (2 * apertureLogTwo) =
      2 * (-(Real.log 2 / Real.sqrt 2)) * (∫ u in (0 : ℝ)..(1 / 2), G u * G (1 - u)) := by
    unfold apertureLogTwo; rw [show autocorr F (Real.log 2) = Real.log 2 * autocorr G 1 by
      have := apertureLogTwo_pos; unfold apertureLogTwo at this; field_simp [this.ne'] at hdil1 ⊢; linarith]
    rw [hac1]; field_simp [(Real.log_pos one_lt_two).ne']; try ring
  rw [hrew]
  obtain ⟨hw2l, hw2u⟩ := primeTwoWeight_bounds
  have hde2 : |(-(Real.log 2 / Real.sqrt 2)) - e2Mid| ≤ (1 / 10000000000000000000000000 : ℝ) := by
    have c1 : e2Mid - (1 / 10000000000000000000000000 : ℝ) ≤ -primeTwoWeightHi := by norm_num [e2Mid, primeTwoWeightLo, primeTwoWeightHi]
    have c2 : -primeTwoWeightLo ≤ e2Mid + (1 / 10000000000000000000000000 : ℝ) := by norm_num [e2Mid, primeTwoWeightLo, primeTwoWeightHi]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hIntAbs : 2 * |∫ u in (0 : ℝ)..(1 / 2), G u * G (1 - u)| ≤ M := by
    have h1 : |∫ u in (0 : ℝ)..(1 / 2), G u * G (1 - u)| ≤ ∫ u in (0 : ℝ)..(1 / 2), |G u * G (1 - u)| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    have h2 : 2 * (∫ u in (0 : ℝ)..(1 / 2), |G u * G (1 - u)|) ≤ ∫ u in (0 : ℝ)..(1 / 2), (G u ^ 2 + G (1 - u) ^ 2) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on (by norm_num) ((by fun_prop : Continuous _).intervalIntegrable _ _)
        ((by fun_prop : Continuous _).intervalIntegrable _ _) fun u _ => ?_
      rw [abs_mul]; nlinarith [sq_nonneg (|G u| - |G (1 - u)|), sq_abs (G u), sq_abs (G (1 - u))]
    have h3 : (∫ u in (0 : ℝ)..(1 / 2), (G u ^ 2 + G (1 - u) ^ 2)) = M := by
      have hc1 : Continuous (fun u : ℝ => G u ^ 2) := hGc.pow 2
      have hc2 : Continuous (fun u : ℝ => G (1 - u) ^ 2) := (hGc.comp (continuous_const.sub continuous_id)).pow 2
      rw [intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
      have hsub := intervalIntegral.integral_comp_sub_left (fun u => G u ^ 2) 1 (a := (0 : ℝ)) (b := 1 / 2)
      norm_num at hsub; rw [hsub]
      exact intervalIntegral.integral_add_adjacent_intervals (hc1.intervalIntegrable 0 (1 / 2)) (hc1.intervalIntegrable (1 / 2) 1)
    linarith
  have hprod := mul_le_mul hde2 hIntAbs (by positivity) (by norm_num)
  have habs_m : |2 * ((-(Real.log 2 / Real.sqrt 2)) - e2Mid) * (∫ u in (0 : ℝ)..(1 / 2), G u * G (1 - u))| ≤ (1 / 10000000000000000000000000 : ℝ) * M := by
    have he : 2 * ((-(Real.log 2 / Real.sqrt 2)) - e2Mid) * (∫ u in (0 : ℝ)..(1 / 2), G u * G (1 - u)) =
        ((-(Real.log 2 / Real.sqrt 2)) - e2Mid) * (2 * ∫ u in (0 : ℝ)..(1 / 2), G u * G (1 - u)) := by ring
    rw [he, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
  linarith [(abs_le.mp habs_m).1]

private theorem hP3_bound {F : ℝ → ℝ} (hFc : Continuous F)
    (hs : tsupport F ⊆ Icc (-apertureLogTwo) apertureLogTwo)
    (hpar : ∀ x, F (-x) = F x) :
    let G := dilateLogTwo F
    let M := ∫ u in (0 : ℝ)..1, G u ^ 2
    let a := primeThreeOffset
    let L4 := (1 - a) / 2
    2 * e3Mid * (∫ s in (0 : ℝ)..L4, G (1 - s) * G (a + s)) - (1 / 10000000000000000000000000 : ℝ) * M ≤
      (-2 * (Real.log 3 / Real.sqrt 3) * autocorr F (Real.log 3)) / (2 * apertureLogTwo) := by
  intro G M a L4
  have hA_pos : 0 < apertureLogTwo := apertureLogTwo_pos
  have hGc : Continuous G := hFc.comp (continuous_const.mul continuous_id)
  have hsG : tsupport G ⊆ Icc (-1 : ℝ) 1 := tsupport_dilateLogTwo hs
  have hGpar : ∀ u, G (-u) = G u := fun u => by unfold G dilateLogTwo; rw [mul_neg, hpar]
  have hGsgn : ∀ u, G (-u) = (1 : ℝ) * G u := fun u => by rw [hGpar u]; ring
  have hM_Ioo : (∫ u in Ioo (0 : ℝ) 1, G u ^ 2) = M := by
    dsimp [M]; rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
  have ha_eq : Real.log 3 = apertureLogTwo * (1 + a) := by
    dsimp [a]; unfold primeThreeOffset apertureLogTwo; field_simp [(Real.log_pos one_lt_two).ne']; ring
  have hdil3 := dilated_autocorr_log_two F (1 + a)
  rw [← ha_eq] at hdil3
  have hac3 := autocorr_primeThree_of_parity hGc hsG hGsgn
  have hrew : (-2 * (Real.log 3 / Real.sqrt 3) * autocorr F (Real.log 3)) / (2 * apertureLogTwo) =
      2 * (-(Real.log 3 / Real.sqrt 3)) * (∫ s in (0 : ℝ)..L4, G (1 - s) * G (a + s)) := by
    have hacF : autocorr F (Real.log 3) = apertureLogTwo * autocorr G (1 + a) := by
      field_simp [hA_pos.ne'] at hdil3 ⊢; linarith
    rw [hacF, hac3]; dsimp [a, L4]; field_simp [hA_pos.ne']; try ring
  rw [hrew]
  obtain ⟨hw3l, hw3u⟩ := primeThreeWeight_bounds
  have hde3 : |(-(Real.log 3 / Real.sqrt 3)) - e3Mid| ≤ (1 / 10000000000000000000000000 : ℝ) := by
    have c1 : e3Mid - (1 / 10000000000000000000000000 : ℝ) ≤ -primeThreeWeightHi := by norm_num [e3Mid, primeThreeWeightLo, primeThreeWeightHi]
    have c2 : -primeThreeWeightLo ≤ e3Mid + (1 / 10000000000000000000000000 : ℝ) := by norm_num [e3Mid, primeThreeWeightLo, primeThreeWeightHi]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨ha_lo, ha_hi⟩ := primeThreeOffset_bounds
  have hL4_pos : 0 ≤ L4 := by dsimp [L4, a]; linarith
  have hIntAbs : 2 * |∫ s in (0 : ℝ)..L4, G (1 - s) * G (a + s)| ≤ M := by
    have h1 : |∫ s in (0 : ℝ)..L4, G (1 - s) * G (a + s)| ≤ ∫ s in (0 : ℝ)..L4, |G (1 - s) * G (a + s)| :=
      intervalIntegral.abs_integral_le_integral_abs hL4_pos
    have h2 : 2 * (∫ s in (0 : ℝ)..L4, |G (1 - s) * G (a + s)|) ≤
        ∫ s in (0 : ℝ)..L4, (G s ^ 2 + G (1 - s) ^ 2 + G (a + s) ^ 2 + G (1 - a - s) ^ 2) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on hL4_pos ((by fun_prop : Continuous _).intervalIntegrable _ _)
        ((by fun_prop : Continuous _).intervalIntegrable _ _) fun s _ => ?_
      rw [abs_mul]; nlinarith [sq_nonneg (|G (1 - s)| - |G (a + s)|), sq_abs (G (1 - s)), sq_abs (G (a + s)), sq_nonneg (G s), sq_nonneg (G (1 - a - s))]
    have hfold := six_interval_folding_diag (H := fun u => G u ^ 2) ((hGc.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    dsimp only at hfold; rw [hM_Ioo] at hfold
    have hp2_nn : 0 ≤ ∫ u in (1 - a)..(1 / 2), (G u ^ 2 + G (1 - u) ^ 2) := by
      rw [intervalIntegral.integral_of_le (by dsimp [a]; linarith)]
      exact setIntegral_nonneg measurableSet_Ioc fun u _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
    dsimp [L4, a]; linarith
  have hprod := mul_le_mul hde3 hIntAbs (by positivity) (by norm_num)
  have habs_m : |2 * ((-(Real.log 3 / Real.sqrt 3)) - e3Mid) * (∫ s in (0 : ℝ)..L4, G (1 - s) * G (a + s))| ≤ (1 / 10000000000000000000000000 : ℝ) * M := by
    have he : 2 * ((-(Real.log 3 / Real.sqrt 3)) - e3Mid) * (∫ s in (0 : ℝ)..L4, G (1 - s) * G (a + s)) =
        ((-(Real.log 3 / Real.sqrt 3)) - e3Mid) * (2 * ∫ s in (0 : ℝ)..L4, G (1 - s) * G (a + s)) := by ring
    rw [he, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
  linarith [(abs_le.mp habs_m).1]

private theorem arch_and_moments_ge {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hs : tsupport F ⊆ Icc (-apertureLogTwo) apertureLogTwo)
    (hpar : ∀ x, F (-x) = F x) :
    let G := dilateLogTwo F
    let m := halfMoment G
    let a := primeThreeOffset
    let L4 := (1 - a) / 2
    (∫ u in Ioo (0 : ℝ) 1, G u ^ 2 * (c0Rat + (Real.log 2 - Real.log (1 - u ^ 2) / 2))) +
      2 * e2Mid * (∫ u in (0 : ℝ)..(1 / 2), G u * G (1 - u)) +
      2 * e3Mid * (∫ s in (0 : ℝ)..L4, G (1 - s) * G (a + s)) -
      (∑ i : Fin 12, ∑ j : Fin 12, bCleanMat i j * m i * m j) ≤
      (weilQuad F - (1 / 10 ^ 13 : ℝ) * (∫ x, F x ^ 2)) / (2 * apertureLogTwo) := by
  intro G m a L4
  have hA_pos : 0 < apertureLogTwo := apertureLogTwo_pos
  have h2A_pos : 0 < 2 * apertureLogTwo := by positivity
  have hG2 : ContDiff ℝ 2 G := contDiff_dilateLogTwo hF
  have hG1 : ContDiff ℝ 1 G := hG2.of_le (by norm_num)
  have hGc : Continuous G := hG2.continuous
  have hsG : tsupport G ⊆ Icc (-1 : ℝ) 1 := tsupport_dilateLogTwo hs
  have hGpar : ∀ u, G (-u) = G u := fun u => by unfold G dilateLogTwo; rw [mul_neg, hpar]
  have hGsq : ∀ u, G (-u) ^ 2 = G u ^ 2 := fun u => by rw [hGpar u]
  set M : ℝ := ∫ u in (0 : ℝ)..1, G u ^ 2
  have hM_nn : 0 ≤ M := by
    dsimp [M]; rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact setIntegral_nonneg measurableSet_Ioc fun u _ => sq_nonneg _
  have hM_Ioo : (∫ u in Ioo (0 : ℝ) 1, G u ^ 2) = M := by
    dsimp [M]; rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
  have hF_mass : (∫ x, F x ^ 2) = 2 * apertureLogTwo * M :=
    dilated_mass_of_sq_even hF.continuous hs hGsq
  obtain ⟨hIntLog, hLagHalf⟩ := logarithmic_lag_half_of_sq_even hG2 hsG hGsq
  have hPotSplit : (∫ u in Ioo (0 : ℝ) 1, G u ^ 2 * (c0Rat + (Real.log 2 - Real.log (1 - u ^ 2) / 2))) =
      c0Rat * M + ∫ u in Ioo (0 : ℝ) 1, G u ^ 2 * (Real.log 2 - Real.log (1 - u ^ 2) / 2) := by
    have hfn : (fun u => G u ^ 2 * (c0Rat + (Real.log 2 - Real.log (1 - u ^ 2) / 2))) =
        fun u => c0Rat * G u ^ 2 + G u ^ 2 * (Real.log 2 - Real.log (1 - u ^ 2) / 2) := funext fun u => by ring
    have hiG2 : IntegrableOn (fun u => G u ^ 2) (Ioo (0 : ℝ) 1) :=
      (hGc.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
    rw [hfn, integral_add (hiG2.const_mul _) hIntLog, integral_const_mul, hM_Ioo]
  have hLowProj : ∀ y : ℝ, lowProj G 24 y = ∑ k : Fin 12, m k * basisFn k y := hLowProj_eq hGc hGpar
  have hHopp : ∀ r : ℕ, regionalLegendreMoment G (24 + (2 * r + 1)) = 0 := hHopp_lem hGpar
  set M_res : ℝ := (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 24 x) ^ 2) / 2
  have hMres_nn : 0 ≤ M_res := div_nonneg (setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _) (by norm_num)
  have hMres_eq : M_res = M - ∑ k : Fin 12, (2 * (degAt k : ℝ) + 1) * m k ^ 2 := hMres_eq_lem hGc hGpar
  have hRegLog := hRegLog_lem hG1 hGpar
  have hMean : apow0_1 * (-((1 / 2 : ℝ) * m ⟨0, by omega⟩ ^ 2)) -
      errApow_1 * (1 / 2 : ℝ) * m ⟨0, by omega⟩ ^ 2 ≤
      -((∫ x, F x) ^ 2 / 4) / (2 * apertureLogTwo) := by
    have hIntF : (∫ x, F x) = 2 * apertureLogTwo * m ⟨0, by omega⟩ := by
      have hsc := Measure.integral_comp_mul_left F apertureLogTwo
      rw [abs_of_pos (inv_pos.mpr hA_pos), smul_eq_mul] at hsc
      have hcut : (∫ u in Icc (-1 : ℝ) 1, G u) = ∫ u, G u :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => dilateLogTwo_outside hs hu
      have hev := even_integral_Icc_unit hGc hGpar
      have hm0 : m ⟨0, by omega⟩ = ∫ u in (0 : ℝ)..1, G u := by
        dsimp [m, halfMoment, degAt]; simp_rw [legP_zero, mul_one]
      change (∫ u, G u) = apertureLogTwo⁻¹ * ∫ x, F x at hsc
      rw [← hcut, hev, ← hm0] at hsc
      field_simp [hA_pos.ne'] at hsc; linarith
    have hq : -((∫ x, F x) ^ 2 / 4) / (2 * apertureLogTwo) =
        apertureLogTwo * (-((1 / 2 : ℝ) * m ⟨0, by omega⟩ ^ 2)) := by
      rw [hIntF]; field_simp [hA_pos.ne']; ring
    rw [hq]
    have hd := abs_aperture_pow_1_sub
    rw [pow_one] at hd
    nlinarith [(abs_le.mp hd).2, sq_nonneg (m ⟨0, by omega⟩)]
  have hEv_0 := hEv_bound_0 hGc hsG hGpar
  dsimp only at hEv_0
  have hEv_1 := hEv_bound_1 hGc hsG hGpar
  dsimp only at hEv_1
  have hEv_2 := hEv_bound_2 hGc hsG hGpar
  dsimp only at hEv_2
  have hEv_3 := hEv_bound_3 hGc hsG hGpar
  dsimp only at hEv_3
  have hEv_4 := hEv_bound_4 hGc hsG hGpar
  dsimp only at hEv_4
  have hEv_5 := hEv_bound_5 hGc hsG hGpar
  dsimp only at hEv_5
  have hEv_6 := hEv_bound_6 hGc hsG hGpar
  dsimp only at hEv_6
  have hEv_7 := hEv_bound_7 hGc hsG hGpar
  dsimp only at hEv_7
  have hEv_8 := hEv_bound_8 hGc hsG hGpar
  dsimp only at hEv_8
  have hEv_9 := hEv_bound_9 hGc hsG hGpar
  dsimp only at hEv_9
  have hEv_10 := hEv_bound_10 hGc hsG hGpar
  dsimp only at hEv_10
  have hEv_11 := hEv_bound_11 hGc hsG hGpar
  dsimp only at hEv_11
  have hOdd_0 := hOdd_bound_0 hGc hsG hLowProj hHopp
  dsimp only at hOdd_0
  have hOdd_1 := hOdd_bound_1 hGc hsG hLowProj hHopp
  dsimp only at hOdd_1
  have hOdd_2 := hOdd_bound_2 hGc hsG hLowProj hHopp
  dsimp only at hOdd_2
  have hOdd_3 := hOdd_bound_3 hGc hsG hLowProj hHopp
  dsimp only at hOdd_3
  have hPole := hPole_bound hF.continuous hs hpar
  dsimp only at hPole
  have hP2_pert := hP2_bound hF.continuous hs hpar
  dsimp only at hP2_pert
  have hP3_pert := hP3_bound hF.continuous hs hpar
  dsimp only at hP3_pert
  have hRet := weilQuad_ge_retained_gamma_moments hF hs
  have hRetDiv := div_le_div_of_nonneg_right hRet h2A_pos.le
  have hLagDil : (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), (autocorr F 0 - autocorr F t) / t) / (2 * apertureLogTwo) =
      regionalLogEnergy G / 4 + ∫ u in Ioo (0 : ℝ) 1, G u ^ 2 * (Real.log 2 - Real.log (1 - u ^ 2) / 2) := by
    rw [dilated_lag_log_two F, ← hLagHalf]; field_simp [hA_pos.ne']; ring
  have hGamM : cGammaLo * M ≤ (twoPrimeGammaMassExact * ∫ x, F x ^ 2) / (2 * apertureLogTwo) := by
    rw [hF_mass, show (twoPrimeGammaMassExact * (2 * apertureLogTwo * M)) / (2 * apertureLogTwo) = twoPrimeGammaMassExact * M by field_simp [hA_pos.ne']]
    exact mul_le_mul_of_nonneg_right cGammaLo_le_twoPrimeGammaMassExact hM_nn
  have hBfast_le := bFast_to_bClean_le m
  have hBfast_id := bFast_quad_decomp m
  have hResMargin : ((295544913996029692272693600319454529326073163181172506579021515867042161533034314545881458517723169851269526925081743047355064581897336273710652194060324209010335306689491605651996673080442008569263254465673167923 / 26567886844997607219781174456306922542387332580589734711559986036883003691317406159024645133702170276442936960035096514381875234978921170399225904236030269956277934080000000000000000000000000000000000000000000000000 : ℝ) : ℝ) * M_res ≤ deltaResRat * M_res :=
    mul_le_mul_of_nonneg_right (by norm_num [deltaResRat]) hMres_nn
  have hMassMargin : c0Rat + (1 / 10 ^ 13 : ℝ) + (1 / 10 ^ 24 : ℝ) + (1 / 10000000000000000000000000 : ℝ) + (1 / 10000000000000000000000000 : ℝ) ≤
      cGammaLo + (83986301180386383586712497 / 22309287000000000000000000 : ℝ) := by norm_num [c0Rat, cGammaLo]
  have hMassMarginM := mul_le_mul_of_nonneg_right hMassMargin hM_nn
  have hEvenSum : (∑ q ∈ Finset.range 12, gammaAlphaEven q * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ (2 * q) * autocorr F t) =
      gammaAlphaEven 0 * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 0 * autocorr F t + gammaAlphaEven 1 * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 2 * autocorr F t + gammaAlphaEven 2 * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 4 * autocorr F t + gammaAlphaEven 3 * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 6 * autocorr F t + gammaAlphaEven 4 * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 8 * autocorr F t + gammaAlphaEven 5 * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 10 * autocorr F t + gammaAlphaEven 6 * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 12 * autocorr F t + gammaAlphaEven 7 * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 14 * autocorr F t + gammaAlphaEven 8 * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 16 * autocorr F t + gammaAlphaEven 9 * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 18 * autocorr F t + gammaAlphaEven 10 * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 20 * autocorr F t + gammaAlphaEven 11 * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 22 * autocorr F t := by
    rw [sum_range_12]; norm_num only [Nat.reduceMul]
  have hRetSplit : ((∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), (autocorr F 0 - autocorr F t) / t) +
      twoPrimeGammaMassExact * (∫ x, F x ^ 2) - (∫ x, F x) ^ 2 / 4 +
      (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t * autocorr F t) / 24 -
      7 * (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 3 * autocorr F t) / 5760 +
      31 * (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 5 * autocorr F t) / 967680 -
      127 * (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 7 * autocorr F t) / 154828800 +
      (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 2 * autocorr F t) / 16 -
      (∑ q ∈ Finset.range 12, gammaAlphaEven q * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ (2 * q) * autocorr F t) -
      2 * (Real.log 2 / Real.sqrt 2) * autocorr F (Real.log 2) -
      2 * (Real.log 3 / Real.sqrt 3) * autocorr F (Real.log 3) +
      coshPairing F ^ 2 / 2 - sinhPairing F ^ 2 / 2) / (2 * apertureLogTwo) -
      ((1 / 10 ^ 13 : ℝ) * (∫ x, F x ^ 2)) / (2 * apertureLogTwo) =
      (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), (autocorr F 0 - autocorr F t) / t) / (2 * apertureLogTwo) +
      (twoPrimeGammaMassExact * ∫ x, F x ^ 2) / (2 * apertureLogTwo) - (1 / 10 ^ 13 : ℝ) * M +
      (-((∫ x, F x) ^ 2 / 4) / (2 * apertureLogTwo)) +
      (((105091 / 5000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 0 * autocorr F t) / (2 * apertureLogTwo) + ((24999999999449249 / 400000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 2 * autocorr F t) / (2 * apertureLogTwo) + ((-65104166242035063 / 10000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 4 * autocorr F t) / (2 * apertureLogTwo) + ((3309458785969429 / 5000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 6 * autocorr F t) / (2 * apertureLogTwo) + ((-5366589076364431 / 80000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 8 * autocorr F t) / (2 * apertureLogTwo) + ((8726421052567571 / 1280000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 10 * autocorr F t) / (2 * apertureLogTwo) + ((-7163072980652803 / 10240000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 12 * autocorr F t) / (2 * apertureLogTwo) + ((6237272726078909 / 81920000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 14 * autocorr F t) / (2 * apertureLogTwo) + ((-3260029542583927 / 327680000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 16 * autocorr F t) / (2 * apertureLogTwo) + ((519878183231709 / 327680000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 18 * autocorr F t) / (2 * apertureLogTwo) + ((-4669432996809649 / 20971520000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 20 * autocorr F t) / (2 * apertureLogTwo) + ((1377431922843341 / 83886080000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 22 * autocorr F t) / (2 * apertureLogTwo)) +
      (((1 / 24 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 1 * autocorr F t) / (2 * apertureLogTwo) + ((-7 / 5760 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 3 * autocorr F t) / (2 * apertureLogTwo) + ((31 / 967680 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 5 * autocorr F t) / (2 * apertureLogTwo) + ((-127 / 154828800 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 7 * autocorr F t) / (2 * apertureLogTwo)) +
      (-2 * (Real.log 2 / Real.sqrt 2) * autocorr F (Real.log 2)) / (2 * apertureLogTwo) +
      (-2 * (Real.log 3 / Real.sqrt 3) * autocorr F (Real.log 3)) / (2 * apertureLogTwo) +
      (coshPairing F ^ 2 / 2 - sinhPairing F ^ 2 / 2) / (2 * apertureLogTwo) := by
    have ht1 : (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t * autocorr F t) =
        ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 1 * autocorr F t := by simp only [pow_one]
    rw [ht1, hEvenSum, hF_mass]; dsimp only [gammaAlphaEven]; field_simp [hA_pos.ne']; ring
  have hSubFloor : (weilQuad F - (1 / 10 ^ 13 : ℝ) * ∫ x, F x ^ 2) / (2 * apertureLogTwo) =
      weilQuad F / (2 * apertureLogTwo) - ((1 / 10 ^ 13 : ℝ) * ∫ x, F x ^ 2) / (2 * apertureLogTwo) := sub_div _ _ _
  rw [hSubFloor, hPotSplit]
  have hRegId : ((1347822955 / 356948592 : ℝ) : ℝ) * M_res - deltaResRat * M_res +
      ((0 : ℝ) * m ⟨0, by omega⟩ ^ 2 + (15 / 2 : ℝ) * m ⟨1, by omega⟩ ^ 2 + (75 / 4 : ℝ) * m ⟨2, by omega⟩ ^ 2 + (637 / 20 : ℝ) * m ⟨3, by omega⟩ ^ 2 + (12937 / 280 : ℝ) * m ⟨4, by omega⟩ ^ 2 + (7381 / 120 : ℝ) * m ⟨5, by omega⟩ ^ 2 + (430105 / 5544 : ℝ) * m ⟨6, by omega⟩ ^ 2 + (33980257 / 360360 : ℝ) * m ⟨7, by omega⟩ ^ 2 + (2436559 / 21840 : ℝ) * m ⟨8, by omega⟩ ^ 2 + (528149137 / 4084080 : ℝ) * m ⟨9, by omega⟩ ^ 2 + (2289240535 / 15519504 : ℝ) * m ⟨10, by omega⟩ ^ 2 + (859193865 / 5173168 : ℝ) * m ⟨11, by omega⟩ ^ 2) =
      (83986301180386383586712497 / 22309287000000000000000000 : ℝ) * M - (∑ k : Fin 12, ((83986301180386383586712497 / 22309287000000000000000000 : ℝ) * (2 * (degAt k : ℝ) + 1)) * m k ^ 2 -
        ((0 : ℝ) * m ⟨0, by omega⟩ ^ 2 + (15 / 2 : ℝ) * m ⟨1, by omega⟩ ^ 2 + (75 / 4 : ℝ) * m ⟨2, by omega⟩ ^ 2 + (637 / 20 : ℝ) * m ⟨3, by omega⟩ ^ 2 + (12937 / 280 : ℝ) * m ⟨4, by omega⟩ ^ 2 + (7381 / 120 : ℝ) * m ⟨5, by omega⟩ ^ 2 + (430105 / 5544 : ℝ) * m ⟨6, by omega⟩ ^ 2 + (33980257 / 360360 : ℝ) * m ⟨7, by omega⟩ ^ 2 + (2436559 / 21840 : ℝ) * m ⟨8, by omega⟩ ^ 2 + (528149137 / 4084080 : ℝ) * m ⟨9, by omega⟩ ^ 2 + (2289240535 / 15519504 : ℝ) * m ⟨10, by omega⟩ ^ 2 + (859193865 / 5173168 : ℝ) * m ⟨11, by omega⟩ ^ 2)) := by
    rw [hMres_eq]; norm_num [deltaResRat]; ring
  linarith [hRetDiv, hRetSplit, hLagDil, hGamM, hRegLog, hRegId, hResMargin, hMassMarginM,
    hMean, hEv_0, hEv_1, hEv_2, hEv_3, hEv_4, hEv_5, hEv_6, hEv_7, hEv_8, hEv_9, hEv_10, hEv_11, hOdd_0, hOdd_1, hOdd_2, hOdd_3,
    hPole, hP2_pert, hP3_pert, hBfast_id, hBfast_le]

/-! ### 3. Fiberwise certificate assembly and `LDLᵀ` synthesis -/

open ApertureLogTwo

private def evenFiberCert : FiberCert where
  p4 := [evenP4_0, evenP4_1, evenP4_2, evenP4_3, evenP4_4, evenP4_5, evenP4_6, evenP4_7, evenP4_8, evenP4_9]
  p2 := [evenP2_0, evenP2_1]
  s4 := ⟨evenSliver4Lo, evenSliver4Tay⟩
  s2 := ⟨evenSliver2Hi, evenSliver2Tay⟩

private theorem evenSector_valid : evenSector.valid = true := by decide +kernel
private theorem evenP4_0_ok : evenP4_0.check evenSector = true := by decide +kernel
private theorem evenP4_1_ok : evenP4_1.check evenSector = true := by decide +kernel
private theorem evenP4_2_ok : evenP4_2.check evenSector = true := by decide +kernel
private theorem evenP4_3_ok : evenP4_3.check evenSector = true := by decide +kernel
private theorem evenP4_4_ok : evenP4_4.check evenSector = true := by decide +kernel
private theorem evenP4_5_ok : evenP4_5.check evenSector = true := by decide +kernel
private theorem evenP4_6_ok : evenP4_6.check evenSector = true := by decide +kernel
private theorem evenP4_7_ok : evenP4_7.check evenSector = true := by decide +kernel
private theorem evenP4_8_ok : evenP4_8.check evenSector = true := by decide +kernel
private theorem evenP4_9_ok : evenP4_9.check evenSector = true := by decide +kernel
private theorem evenP2_0_ok : evenP2_0.check evenSector = true := by decide +kernel
private theorem evenP2_1_ok : evenP2_1.check evenSector = true := by decide +kernel
private theorem evenFiberCert_ok : evenFiberCert.check evenSector = true := by decide +kernel
private theorem evenCertMat_ldl :
    ldlCheck evenSector.K (certMat evenSector evenBClean evenFiberCert) evenCertL evenCertD = true := by
  decide +kernel

/-- Unconditional `1 / 10 ^ 13` `L²` floor on the Weil quadratic form for even
`C²` tests supported in `[-log 2, log 2]`. -/
theorem weilQuad_ge_even_at_aperture_log_two {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hs : tsupport F ⊆ Icc (-apertureLogTwo) apertureLogTwo)
    (hpar : ∀ x, F (-x) = F x) :
    (1 / 10 ^ 13 : ℝ) * (∫ x, F x ^ 2) ≤ weilQuad F := by
  have h2A_pos : 0 < 2 * apertureLogTwo := by linarith [apertureLogTwo_pos]
  have hArch := arch_and_moments_ge hF hs hpar
  dsimp only at hArch
  set G := dilateLogTwo F
  have hG2 : ContDiff ℝ 2 G := contDiff_dilateLogTwo hF
  have hGc : Continuous G := hG2.continuous
  have hsG : tsupport G ⊆ Icc (-1 : ℝ) 1 := tsupport_dilateLogTwo hs
  have hGsq : ∀ u, G (-u) ^ 2 = G u ^ 2 := fun u => by
    unfold G dilateLogTwo; rw [mul_neg, hpar]
  obtain ⟨hIntLog, _⟩ := logarithmic_lag_half_of_sq_even hG2 hsG hGsq
  have hiG2 : IntegrableOn (fun u => G u ^ 2) (Ioo (0 : ℝ) 1) :=
    (hGc.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hiPot : IntegrableOn (fun u => G u ^ 2 * ((evenSector.c0 : ℝ) + vTrue u)) (Ioo (0 : ℝ) 1) := by
    refine ((hiG2.const_mul (evenSector.c0 : ℝ)).add hIntLog).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u _
    simp only [Pi.add_apply, vTrue]; ring
  have h4 : ∀ D ∈ evenFiberCert.p4, D.check evenSector = true := by
    intro D hD
    simp only [evenFiberCert, List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact evenP4_0_ok
    · exact evenP4_1_ok
    · exact evenP4_2_ok
    · exact evenP4_3_ok
    · exact evenP4_4_ok
    · exact evenP4_5_ok
    · exact evenP4_6_ok
    · exact evenP4_7_ok
    · exact evenP4_8_ok
    · exact evenP4_9_ok
  have h2 : ∀ D ∈ evenFiberCert.p2, D.check evenSector = true := by
    intro D hD
    simp only [evenFiberCert, List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl
    · exact evenP2_0_ok
    · exact evenP2_1_ok
  have hFib := evenFiberCert.bound evenSector evenSector_valid evenFiberCert_ok h4 h2 hGc hiPot
  have hCert := quadR_certMat evenSector evenBClean evenFiberCert (evenSector.moments G)
  have hPsd := quad_nonneg_of_ldlCheck evenCertMat_ldl (evenSector.moments G)
  have hMom_eq : evenSector.moments G = halfMoment G := rfl
  have hc0_eq : (evenSector.c0 : ℝ) = c0Rat := by norm_num [evenSector, c0Rat]
  have he2_eq : (evenSector.e2 : ℝ) = e2Mid := by norm_num [evenSector, e2Mid]
  have he3_eq : (evenSector.e3 : ℝ) = e3Mid := by norm_num [evenSector, e3Mid]
  have hBClean_eq : quadR evenSector.K evenBClean (halfMoment G) =
      ∑ i : Fin 12, ∑ j : Fin 12, bCleanMat i j * halfMoment G i * halfMoment G j := rfl
  rw [hMom_eq, hc0_eq, he2_eq, he3_eq] at hFib
  rw [hMom_eq, hBClean_eq] at hCert
  rw [hMom_eq] at hPsd
  have hPot_eq : (∫ u in Ioo (0 : ℝ) 1, G u ^ 2 * (c0Rat + vTrue u)) =
      ∫ u in Ioo (0 : ℝ) 1, G u ^ 2 * (c0Rat + (Real.log 2 - Real.log (1 - u ^ 2) / 2)) := rfl
  rw [hPot_eq] at hFib
  have hDiv_nn : 0 ≤ (weilQuad F - (1 / 10 ^ 13 : ℝ) * ∫ x, F x ^ 2) / (2 * apertureLogTwo) := by
    linarith [hArch, hFib, hCert, hPsd]
  have hSub_nn : 0 ≤ weilQuad F - (1 / 10 ^ 13 : ℝ) * ∫ x, F x ^ 2 :=
    ((div_nonneg_iff.mp hDiv_nn).resolve_right fun h => by linarith [h.2, h2A_pos]).1
  linarith

/-! ### 5. Smooth degree-18 upper-bound witness and degree-14 Gamma insufficiency -/

private def upperUnitPolyList : List ℝ := ([1938762811 / 1024000000, 0, -10133087199 / 1024000000, 0, 5058036369 / 256000000, 0, -3326115637 / 256000000, 0, -9650701551 / 512000000, 0, 26993962803 / 512000000, 0, -15065579023 / 256000000, 0, 1924814463 / 51200000, 0, -13832727909 / 1024000000, 0, 2178873697 / 1024000000] : List ℝ)
private def upperUnitD1List : List ℝ := ([0, -10133087199 / 512000000, 0, 5058036369 / 64000000, 0, -9978346911 / 128000000, 0, -9650701551 / 64000000, 0, 26993962803 / 51200000, 0, -45196737069 / 64000000, 0, 13473701241 / 25600000, 0, -13832727909 / 64000000, 0, 19609863273 / 512000000] : List ℝ)
private def upperUnitD2List : List ℝ := ([-10133087199 / 512000000, 0, 15174109107 / 64000000, 0, -9978346911 / 25600000, 0, -67554910857 / 64000000, 0, 242945665227 / 51200000, 0, -497164107759 / 64000000, 0, 175158116133 / 25600000, 0, -41498183727 / 12800000, 0, 333367675641 / 512000000] : List ℝ)

private def upperUnitD2 (u : ℝ) : ℝ :=
  polyEval upperUnitD2List (max (-1) (min 1 u))

private def upperUnitD1 (u : ℝ) : ℝ :=
  ∫ t in (-1 : ℝ)..u, upperUnitD2 t

/-- Smooth `C²` degree-18 even polynomial witness supported on `[-1, 1]`. -/
def upperUnitTest (u : ℝ) : ℝ :=
  ∫ t in (-1 : ℝ)..u, upperUnitD1 t

/-- Rescaled two-prime test family `F_s(x) = upperUnitTest(x / (s * log 2))`. -/
def twoPrimeScaleTest (s x : ℝ) : ℝ :=
  upperUnitTest (x / (s * Real.log 2))

/-- Smooth `C²` test on `[-log 2, log 2]` achieving Rayleigh quotient `< 1 / 10⁹` and
driving `twoPrimeDegree14GammaForm` strictly negative (`≈ -9.12 × 10⁻⁸`). -/
def twoPrimeUpperTest (x : ℝ) : ℝ :=
  twoPrimeScaleTest 1 x

private theorem continuous_upperUnitD2 : Continuous upperUnitD2 :=
  (continuous_polyEval upperUnitD2List).comp (continuous_const.max (continuous_const.min continuous_id))

private theorem upperUnitD2_eq_of_mem {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    upperUnitD2 u = polyEval upperUnitD2List u := by
  unfold upperUnitD2
  rw [min_eq_right hu.2, max_eq_right hu.1]

private theorem upperUnitD2_of_le_neg_one {u : ℝ} (hu : u ≤ -1) : upperUnitD2 u = 0 := by
  unfold upperUnitD2
  rw [min_eq_right (by linarith : u ≤ 1), max_eq_left hu]
  norm_num [upperUnitD2List, polyEval]

private theorem upperUnitD2_of_one_le {u : ℝ} (hu : 1 ≤ u) : upperUnitD2 u = 0 := by
  unfold upperUnitD2
  rw [min_eq_left hu, max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)]
  norm_num [upperUnitD2List, polyEval]

private theorem hasDerivAt_upperUnitD1 (u : ℝ) : HasDerivAt upperUnitD1 (upperUnitD2 u) u :=
  intervalIntegral.integral_hasDerivAt_right
    (continuous_upperUnitD2.intervalIntegrable (-1) u)
    continuous_upperUnitD2.aestronglyMeasurable.stronglyMeasurableAtFilter
    continuous_upperUnitD2.continuousAt

private theorem contDiff_upperUnitD1 : ContDiff ℝ 1 upperUnitD1 :=
  contDiff_one_iff_deriv.mpr ⟨fun u => (hasDerivAt_upperUnitD1 u).differentiableAt, by
    rw [show deriv upperUnitD1 = upperUnitD2 from funext fun u => (hasDerivAt_upperUnitD1 u).deriv]
    exact continuous_upperUnitD2⟩

private theorem hasDerivAt_upperUnitTest (u : ℝ) : HasDerivAt upperUnitTest (upperUnitD1 u) u := by
  have hc : Continuous upperUnitD1 := contDiff_upperUnitD1.continuous
  exact intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable (-1) u) hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem contDiff_upperUnitTest : ContDiff ℝ 2 upperUnitTest :=
  show ContDiff ℝ (1 + 1) upperUnitTest from contDiff_succ_iff_deriv.mpr
    ⟨fun u => (hasDerivAt_upperUnitTest u).differentiableAt, by simp, by
      rw [show deriv upperUnitTest = upperUnitD1 from funext fun u => (hasDerivAt_upperUnitTest u).deriv]
      exact contDiff_upperUnitD1⟩

private theorem upperUnitD1_eq_of_mem {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    upperUnitD1 u = polyEval upperUnitD1List u := by
  unfold upperUnitD1
  have hcongr : ∫ t in (-1 : ℝ)..u, upperUnitD2 t = ∫ t in (-1 : ℝ)..u, polyEval upperUnitD2List t :=
    intervalIntegral.integral_congr fun t ht => by
      rw [uIcc_of_le hu.1] at ht
      exact upperUnitD2_eq_of_mem ⟨ht.1, ht.2.trans hu.2⟩
  have hd : ∀ t ∈ uIcc (-1 : ℝ) u, HasDerivAt (polyEval upperUnitD1List) (polyEval upperUnitD2List t) t :=
    fun t _ => (hasDerivAt_polyEval upperUnitD1List t).congr_deriv
      (by dsimp [upperUnitD1List, upperUnitD2List, polyDeriv, polyAdd, polyEval]; ring)
  rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_polyEval _).intervalIntegrable _ _)]
  have h0 : polyEval upperUnitD1List (-1) = 0 := by norm_num [upperUnitD1List, polyEval]
  linarith

private theorem upperUnitD1_of_le_neg_one {u : ℝ} (hu : u ≤ -1) : upperUnitD1 u = 0 := by
  unfold upperUnitD1
  have hcongr : ∫ t in (-1 : ℝ)..u, upperUnitD2 t = ∫ _ in (-1 : ℝ)..u, (0 : ℝ) :=
    intervalIntegral.integral_congr fun t ht => by
      rw [uIcc_of_ge hu] at ht; exact upperUnitD2_of_le_neg_one ht.2
  simp [hcongr]

private theorem upperUnitD1_of_one_le {u : ℝ} (hu : 1 ≤ u) : upperUnitD1 u = 0 := by
  unfold upperUnitD1
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_upperUnitD2.intervalIntegrable (-1) 1)
    (continuous_upperUnitD2.intervalIntegrable 1 u)]
  have h1 : (∫ t in (-1 : ℝ)..1, upperUnitD2 t) = 0 := by
    change upperUnitD1 1 = 0
    rw [upperUnitD1_eq_of_mem ⟨by norm_num, le_rfl⟩]
    norm_num [upperUnitD1List, polyEval]
  have h2 : (∫ t in (1 : ℝ)..u, upperUnitD2 t) = ∫ _ in (1 : ℝ)..u, (0 : ℝ) :=
    intervalIntegral.integral_congr fun t ht => by
      rw [uIcc_of_le hu] at ht; exact upperUnitD2_of_one_le ht.1
  simp [h1, h2]

private theorem upperUnitTest_eq_of_mem {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    upperUnitTest u = polyEval upperUnitPolyList u := by
  unfold upperUnitTest
  have hcongr : ∫ t in (-1 : ℝ)..u, upperUnitD1 t = ∫ t in (-1 : ℝ)..u, polyEval upperUnitD1List t :=
    intervalIntegral.integral_congr fun t ht => by
      rw [uIcc_of_le hu.1] at ht
      exact upperUnitD1_eq_of_mem ⟨ht.1, ht.2.trans hu.2⟩
  have hd : ∀ t ∈ uIcc (-1 : ℝ) u, HasDerivAt (polyEval upperUnitPolyList) (polyEval upperUnitD1List t) t :=
    fun t _ => (hasDerivAt_polyEval upperUnitPolyList t).congr_deriv
      (by dsimp [upperUnitPolyList, upperUnitD1List, polyDeriv, polyAdd, polyEval]; ring)
  rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_polyEval _).intervalIntegrable _ _)]
  have h0 : polyEval upperUnitPolyList (-1) = 0 := by norm_num [upperUnitPolyList, polyEval]
  linarith

private theorem upperUnitTest_outside {u : ℝ} (hu : u ∉ Icc (-1 : ℝ) 1) : upperUnitTest u = 0 := by
  have hc : Continuous upperUnitD1 := contDiff_upperUnitD1.continuous
  rcases lt_or_ge u (-1) with hlt | hge
  · unfold upperUnitTest
    have hcongr : ∫ t in (-1 : ℝ)..u, upperUnitD1 t = ∫ _ in (-1 : ℝ)..u, (0 : ℝ) :=
      intervalIntegral.integral_congr fun t ht => by
        rw [uIcc_of_ge hlt.le] at ht; exact upperUnitD1_of_le_neg_one ht.2
    simp [hcongr]
  · have hgt : 1 < u := lt_of_not_ge fun hle => hu ⟨hge, hle⟩
    unfold upperUnitTest
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (-1) 1) (hc.intervalIntegrable 1 u)]
    have h1 : (∫ t in (-1 : ℝ)..1, upperUnitD1 t) = 0 := by
      change upperUnitTest 1 = 0
      rw [upperUnitTest_eq_of_mem ⟨by norm_num, le_rfl⟩]
      norm_num [upperUnitPolyList, polyEval]
    have h2 : (∫ t in (1 : ℝ)..u, upperUnitD1 t) = ∫ _ in (1 : ℝ)..u, (0 : ℝ) :=
      intervalIntegral.integral_congr fun t ht => by
        rw [uIcc_of_le hgt.le] at ht; exact upperUnitD1_of_one_le ht.1
    simp [h1, h2]

theorem tsupport_upperUnitTest : tsupport upperUnitTest ⊆ Icc (-1 : ℝ) 1 :=
  closure_minimal (fun u hu => by_contra fun hnot => hu (upperUnitTest_outside hnot)) isClosed_Icc

theorem upperUnitTest_even (u : ℝ) : upperUnitTest (-u) = upperUnitTest u := by
  by_cases hu : u ∈ Icc (-1 : ℝ) 1
  · have hnu : -u ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    rw [upperUnitTest_eq_of_mem hnu, upperUnitTest_eq_of_mem hu]
    dsimp [upperUnitPolyList, polyEval]; ring
  · have hnu : -u ∉ Icc (-1 : ℝ) 1 := fun h => hu ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [upperUnitTest_outside hnu, upperUnitTest_outside hu]

theorem contDiff_twoPrimeScaleTest (s : ℝ) : ContDiff ℝ 2 (twoPrimeScaleTest s) :=
  contDiff_upperUnitTest.comp (contDiff_id.div_const _)

theorem contDiff_twoPrimeUpperTest : ContDiff ℝ 2 twoPrimeUpperTest :=
  contDiff_twoPrimeScaleTest 1

theorem twoPrimeScaleTest_even (s x : ℝ) : twoPrimeScaleTest s (-x) = twoPrimeScaleTest s x := by
  unfold twoPrimeScaleTest
  rw [neg_div, upperUnitTest_even]

theorem tsupport_twoPrimeScaleTest {s : ℝ} (hs : 0 < s) :
    tsupport (twoPrimeScaleTest s) ⊆ Icc (-(s * Real.log 2)) (s * Real.log 2) := by
  have hA : 0 < s * Real.log 2 := mul_pos hs apertureLogTwo_pos
  refine closure_minimal (fun x hx => ?_) isClosed_Icc
  by_contra hnot
  apply hx
  unfold twoPrimeScaleTest
  apply upperUnitTest_outside
  intro hmem
  apply hnot
  exact ⟨(le_div_iff₀ hA).mp (by linarith [hmem.1]), (div_le_iff₀ hA).mp (by linarith [hmem.2])⟩

theorem tsupport_twoPrimeUpperTest : tsupport twoPrimeUpperTest ⊆ Icc (-Real.log 2) (Real.log 2) := by
  simpa [twoPrimeUpperTest] using tsupport_twoPrimeScaleTest one_pos

private def upperAcList : List ℝ := ([8573402398840939849351 / 4529259115484619140625, 0, -165426213857465883643 / 28802919653320312500, 0, 3200849337069904792453 / 391719707285156250000, 0, -19089405752363054249371 / 2611464715234375000000, 779917329 / 136718750000, 318039004990404130451 / 67392637812500000000, -149543512701 / 1093750000000, -73511039832564976371 / 46477681250000000000, -153835075690067 / 48125000000000, 1042428869593373167 / 116025000000000000, -52131905463531143 / 3753750000000000, 506025198368967 / 28000000000000, -2288040970943921507 / 120120000000000000, 597667008229663 / 40000000000000, -22351018842066239491 / 2722720000000000000, 1400553559032959 / 480000000000000, -793911803213484089 / 1460659200000000000, 0, 38354024591996450291 / 2483120640000000000000, 0, -653352416728657797 / 6922639360000000000000, 0, -19846133129151735729 / 138452787200000000000000, 0, 175288131730815073 / 6085836800000000000000, 0, -1527653904135711397 / 423574241280000000000000, 0, 16195229654724461 / 50815795200000000000000, 0, -6336345955862923 / 325221089280000000000000, 0, 17562953535127 / 23566745600000000000000, 0, -141088608501841 / 10463635046400000000000000] : List ℝ)
private def upperDiffDivTauList : List ℝ := ([0, 165426213857465883643 / 28802919653320312500, 0, -3200849337069904792453 / 391719707285156250000, 0, 19089405752363054249371 / 2611464715234375000000, -779917329 / 136718750000, -318039004990404130451 / 67392637812500000000, 149543512701 / 1093750000000, 73511039832564976371 / 46477681250000000000, 153835075690067 / 48125000000000, -1042428869593373167 / 116025000000000000, 52131905463531143 / 3753750000000000, -506025198368967 / 28000000000000, 2288040970943921507 / 120120000000000000, -597667008229663 / 40000000000000, 22351018842066239491 / 2722720000000000000, -1400553559032959 / 480000000000000, 793911803213484089 / 1460659200000000000, 0, -38354024591996450291 / 2483120640000000000000, 0, 653352416728657797 / 6922639360000000000000, 0, 19846133129151735729 / 138452787200000000000000, 0, -175288131730815073 / 6085836800000000000000, 0, 1527653904135711397 / 423574241280000000000000, 0, -16195229654724461 / 50815795200000000000000, 0, 6336345955862923 / 325221089280000000000000, 0, -17562953535127 / 23566745600000000000000, 0, 141088608501841 / 10463635046400000000000000] : List ℝ)
private def upperBivAntideriv (τ : ℝ) : List ℝ :=
  [polyEval ([8573402398840939849351 / 9058518230969238281250, 3758801237316621721 / 2097152000000000000, -165426213857465883643 / 57605839306640625000, -6548550874013785463 / 1048576000000000000, 3200849337069904792453 / 783439414570312500000, 191127810336621994011 / 20971520000000000000, -19089405752363054249371 / 5222929430468750000000, -6162635586056804923 / 1146880000000000000, 318039004990404130451 / 134785275625000000000, -23587906143703760079 / 7340032000000000000, -73511039832564976371 / 92955362500000000000, 71033370381266912377 / 9175040000000000000, 1042428869593373167 / 232050000000000000, -84797326819334349363 / 5242880000000000000, 506025198368967 / 56000000000000, -1401604182230183217 / 327680000000000000, 597667008229663 / 80000000000000, -61165224109030985229 / 10485760000000000000, 1400553559032959 / 960000000000000] : List ℝ) τ,
    polyEval ([3758801237316621721 / 1048576000000000000, 0, -19645652622041356389 / 1048576000000000000, 0, 9806332808902673259 / 262144000000000000, 0, -6448549302101175607 / 262144000000000000, 0, -18710421267138819861 / 524288000000000000, 0, 52334891203973719233 / 524288000000000000, 0, -29208584335974113653 / 262144000000000000, 0, 3731758698939335493 / 52428800000000000, 0, -26818378444650992199 / 1048576000000000000, 0, 4224319293609682267 / 1048576000000000000] : List ℝ) τ,
    polyEval ([0, -19645652622041356389 / 1048576000000000000, 0, 9806332808902673259 / 131072000000000000, 0, -19345647906303526821 / 262144000000000000, 0, -18710421267138819861 / 131072000000000000, 0, 52334891203973719233 / 104857600000000000, 0, -87625753007922340959 / 131072000000000000, 0, 26122310892575348451 / 52428800000000000, 0, -26818378444650992199 / 131072000000000000, 0, 38018873642487140403 / 1048576000000000000] : List ℝ) τ,
    polyEval ([-6548550874013785463 / 524288000000000000, 0, 112677147865400607939 / 1048576000000000000, 0, -6165906796429498939 / 32768000000000000, 0, -76080692652088349097 / 262144000000000000, 0, 408810250754437485189 / 262144000000000000, 0, -1376355103759314820331 / 524288000000000000, 0, 154217586163406822991 / 65536000000000000, 0, -60138194487793770777 / 52428800000000000, 0, 131081515004036553957 / 524288000000000000, 0, -7359572389102834901 / 1048576000000000000] : List ℝ) τ,
    polyEval ([0, 181130118653759051673 / 2097152000000000000, 0, -41748135046648109233 / 131072000000000000, 0, -32166887677781637153 / 104857600000000000, 0, 6896990378182916673 / 2048000000000000, 0, -1558709889712222459529 / 209715200000000000, 0, 1077966342923925164523 / 131072000000000000, 0, -102397497558688280949 / 20971520000000000, 0, 88902130519007933127 / 65536000000000000, 0, -198708454505776542327 / 2097152000000000000] : List ℝ) τ,
    polyEval ([181130118653759051673 / 5242880000000000000, 0, -227751452305525008561 / 655360000000000000, 0, -23486259977087708523 / 655360000000000000, 0, 6796948725848763750339 / 1310720000000000000, 0, -41420700942160928995611 / 2621440000000000000, 0, 29026139691663347461161 / 1310720000000000000, 0, -5345408375182749951957 / 327680000000000000, 0, 305254681352726765517 / 52428800000000000, 0, -3657909489983014509243 / 5242880000000000000, 0, 11020822402883486193 / 1310720000000000000] : List ℝ) τ,
    polyEval ([0, -28851036442445758019 / 131072000000000000, 0, 5828378237038634643 / 16384000000000000, 0, 1488098128135434242043 / 262144000000000000, 0, -134420490402514496247 / 5242880000000000, 0, 2455700506532314059267 / 52428800000000000, 0, -2851717766125256521251 / 65536000000000000, 0, 5233010682877331322969 / 262144000000000000, 0, -468626779639182343179 / 131072000000000000, 0, 33062467208650458579 / 262144000000000000] : List ℝ) τ,
    polyEval ([-28851036442445758019 / 458752000000000000, 0, 445662392320976157009 / 917504000000000000, 0, 1960287825396496521447 / 458752000000000000, 0, -11679784020250864438369 / 367001600000000000, 0, 71975972254681531748307 / 917504000000000000, 0, -171606442378364424860673 / 1835008000000000000, 0, 12662647005553065929837 / 229376000000000000, 0, -5082846928841913189387 / 367001600000000000, 0, 123728220017261757183 / 131072000000000000, 0, -1035312267805671427 / 262144000000000000] : List ℝ) τ,
    polyEval ([0, 151032145940724858309 / 524288000000000000, 0, 532898218933782079383 / 262144000000000000, 0, -6279986338996248317487 / 209715200000000000, 0, 3409792030541703879849 / 32768000000000000, 0, -34079241129425546464929 / 209715200000000000, 0, 32494270403484910706829 / 262144000000000000, 0, -44133211290843466925133 / 1048576000000000000, 0, 152017798786887252219 / 32768000000000000, 0, -65224672871757299901 / 1048576000000000000] : List ℝ) τ,
    polyEval ([16781349548969428701 / 262144000000000000, 0, 131369643659909724689 / 262144000000000000, 0, -8241146073216034844513 / 393216000000000000, 0, 85432676483437012342243 / 786432000000000000, 0, -119558523398714878845997 / 524288000000000000, 0, 356471728131589296576653 / 1572864000000000000, 0, -80389128293409841412639 / 786432000000000000, 0, 433989652951642222149 / 26214400000000000, 0, -9262859328683559599 / 20971520000000000, 0, -7009219922357001349 / 1572864000000000000] : List ℝ) τ,
    polyEval ([0, 7768690338108224229 / 262144000000000000, 0, -347630095037238053353 / 32768000000000000, 0, 23105696662429323098703 / 262144000000000000, 0, -168401652228436051629177 / 655360000000000000, 0, 7068320190164835921567 / 20971520000000000, 0, -131097484389115434384381 / 655360000000000000, 0, 29397743603724050626071 / 655360000000000000, 0, -605717430527302112019 / 327680000000000000, 0, -189248937903639036423 / 2621440000000000000] : List ℝ) τ,
    polyEval ([7768690338108224229 / 1441792000000000000, 0, -10874548729037794272981 / 2883584000000000000, 0, 2458122352517145472491 / 45056000000000000, 0, -663472632272537993535219 / 2883584000000000000, 0, 1169168314903323143123601 / 2883584000000000000, 0, -1820143867601575831141623 / 5767168000000000000, 0, 3075114095797365852513 / 32768000000000000, 0, -124064303227924186881 / 26214400000000000, 0, -163210549409155890369 / 262144000000000000, 0, 5346948684477553881 / 524288000000000000] : List ℝ) τ,
    polyEval ([0, -482951564403816856303 / 524288000000000000, 0, 659311017898997434253 / 26214400000000000, 0, -84507670154628395891919 / 524288000000000000, 0, 6396648721596539985453 / 16384000000000000, 0, -83591023781828214272949 / 209715200000000000, 0, 395265672560708313573 / 2621440000000000, 0, -1453414061623494201231 / 262144000000000000, 0, -120484232563348931277 / 32768000000000000, 0, 176449306587759278073 / 1048576000000000000] : List ℝ) τ,
    polyEval ([-482951564403816856303 / 3407872000000000000, 0, 2861348704049848118217 / 340787200000000000, 0, -147445225498661367721659 / 1703936000000000000, 0, 201671570363494002600527 / 681574400000000000, 0, -539796435061299252792231 / 1363148800000000000, 0, 305126153554711865716791 / 1703936000000000000, 0, 1097942997749101031 / 106496000000000, 0, -424279206845626080927 / 26214400000000000, 0, 724285442062239791349 / 524288000000000000, 0, -2525076451022281387 / 262144000000000000] : List ℝ) τ,
    polyEval ([0, 50859120931379777463 / 26214400000000000, 0, -568990306587603974799 / 16384000000000000, 0, 45117591363834583407231 / 262144000000000000, 0, -273861993794464297700817 / 917504000000000000, 0, 25160893381197996471159 / 183500800000000000, 0, 16308931153712604783717 / 229376000000000000, 0, -7241217814726921404951 / 131072000000000000, 0, 97612409223580052373 / 13107200000000000, 0, -42204849252800988897 / 262144000000000000] : List ℝ) τ,
    polyEval ([16953040310459925821 / 65536000000000000, 0, -6648196357908033811623 / 655360000000000000, 0, 4856572253833905064579 / 65536000000000000, 0, -205849831220023922567063 / 1310720000000000000, 0, 6429736953349872992247 / 327680000000000000, 0, 26597904204937037542207 / 131072000000000000, 0, -3064218778387121567927 / 20480000000000000, 0, 3845580136048609200099 / 131072000000000000, 0, -859250705798875403013 / 655360000000000000, 0, 1397975868345293237 / 262144000000000000] : List ℝ) τ,
    polyEval ([0, -2168148833664487567617 / 1048576000000000000, 0, 2359906273335748441359 / 104857600000000000, 0, -89901758499430736598219 / 2097152000000000000, 0, -3935305432317820996743 / 32768000000000000, 0, 3312747444682198383817 / 8388608000000000, 0, -85510395975214578818307 / 262144000000000000, 0, 93464848961108542108191 / 1048576000000000000, 0, -451813215184426824729 / 65536000000000000, 0, 37745348445322917399 / 419430400000000000] : List ℝ) τ,
    polyEval ([-2168148833664487567617 / 8912896000000000000, 0, 2412635302880137526553 / 524288000000000000, 0, 5365648591358557778253 / 557056000000000000, 0, -912303661294363090248573 / 4456448000000000000, 0, 1030033257056617489599429 / 1782579200000000000, 0, -5148343685349167916044289 / 8912896000000000000, 0, 959141701020795742859409 / 4456448000000000000, 0, -1371246226359628906287 / 52428800000000000, 0, 766162519577307025173 / 1048576000000000000, 0, -1772927470510465269 / 1048576000000000000] : List ℝ) τ,
    polyEval ([0, 341485047364801049761 / 524288000000000000, 0, 207123219057718664449 / 13107200000000000, 0, -51987025684757765638047 / 262144000000000000, 0, 86058375572137236517337 / 131072000000000000, 0, -87501979878867031584249 / 104857600000000000, 0, 55098037637901697646207 / 131072000000000000, 0, -19870450729453796132661 / 262144000000000000, 0, 496572279837891646389 / 131072000000000000, 0, -30139766998677909573 / 1048576000000000000] : List ℝ) τ,
    polyEval ([341485047364801049761 / 4980736000000000000, 0, 14754367982033058738039 / 1992294400000000000, 0, -81775444604274380581149 / 622592000000000000, 0, 2910150754258756613343431 / 4980736000000000000, 0, -4900037272978536360436479 / 4980736000000000000, 0, 1336136665346320112576301 / 1992294400000000000, 0, -454642423700872520113 / 2621440000000000, 0, 736088345654810151003 / 52428800000000000, 0, -122145371520957844059 / 524288000000000000, 0, 249867925656760411 / 1048576000000000000] : List ℝ) τ,
    polyEval ([0, 361275678224512424427 / 209715200000000000, 0, -7970953575790030200903 / 131072000000000000, 0, 1061671326308962589529177 / 2621440000000000000, 0, -38614981562209910312169 / 40960000000000000, 0, 920353216318133411030217 / 1048576000000000000, 0, -209375765828387592451017 / 655360000000000000, 0, 4134992882574189002367 / 104857600000000000, 0, -391816970982812824449 / 327680000000000000, 0, 42727415287306030281 / 10485760000000000000] : List ℝ) τ,
    polyEval ([120425226074837474809 / 734003200000000000, 0, -17404090475142238872741 / 917504000000000000, 0, 39416264937296436287593 / 183500800000000000, 0, -38164877468917345426423 / 52428800000000000, 0, 493904082066226516750923 / 524288000000000000, 0, -125614717286552763819979 / 262144000000000000, 0, 1138691147139848090789 / 13107200000000000, 0, -228201092989989886767 / 52428800000000000, 0, 34588859994485834037 / 1048576000000000000] : List ℝ) τ,
    polyEval ([0, -471043691868138392421 / 131072000000000000, 0, 1381453287125931946949 / 16384000000000000, 0, -116984485059727460039007 / 262144000000000000, 0, 108183329095357684633179 / 131072000000000000, 0, -30842881902654633312501 / 52428800000000000, 0, 10044531266001242319309 / 65536000000000000, 0, -3126315831408317711163 / 262144000000000000, 0, 22011092723763712569 / 131072000000000000] : List ℝ) τ,
    polyEval ([-471043691868138392421 / 1507328000000000000, 0, 13924504634154249605811 / 602931200000000000, 0, -63977144433553234224627 / 301465600000000000, 0, 3526105999602322561866441 / 6029312000000000000, 0, -1782888167364975677155149 / 3014656000000000000, 0, 1321651439900668579509807 / 6029312000000000000, 0, -834740503398166452087 / 32768000000000000, 0, 31581133038443587599 / 52428800000000000] : List ℝ) τ,
    polyEval ([0, 2066055242467666820777 / 524288000000000000, 0, -19784414113006348495833 / 262144000000000000, 0, 69214585739078446708041 / 209715200000000000, 0, -15888124704475025675673 / 32768000000000000, 0, 53625662990909806625829 / 209715200000000000, 0, -11362692158501571909021 / 262144000000000000, 0, 1694854139729805867813 / 1048576000000000000] : List ℝ) τ,
    polyEval ([2066055242467666820777 / 6553600000000000000, 0, -123763630383075120600591 / 6553600000000000000, 0, 94946793314907771876639 / 655360000000000000, 0, -2105576278127880270525813 / 6553600000000000000, 0, 638484690605663750637789 / 2621440000000000000, 0, -780107589226780333477959 / 13107200000000000000, 0, 22033103816487476281569 / 6553600000000000000] : List ℝ) τ,
    polyEval ([0, -777182789142114679467 / 262144000000000000, 0, 1562189063223879621531 / 32768000000000000, 0, -8886703069943657605647 / 52428800000000000, 0, 4948270891663029079149 / 26214400000000000, 0, -6962286176694597111363 / 104857600000000000, 0, 726366059884202514777 / 131072000000000000] : List ℝ) τ,
    polyEval ([-86353643238012742163 / 393216000000000000, 0, 8699950327707212352779 / 786432000000000000, 0, -683678007249611991617 / 9830400000000000, 0, 92813732757856440913583 / 786432000000000000, 0, -15803284496306783919443 / 262144000000000000, 0, 11541149618160106623679 / 1572864000000000000] : List ℝ) τ,
    polyEval ([0, 169220723612009007081 / 104857600000000000, 0, -2803879252684781872601 / 131072000000000000, 0, 30756936898555791866943 / 524288000000000000, 0, -727660088968080959691 / 16384000000000000, 0, 1648735659737158089097 / 209715200000000000] : List ℝ) τ,
    polyEval ([169220723612009007081 / 1520435200000000000, 0, -17639363154428332554237 / 3801088000000000000, 0, 17221938445926805561971 / 760217600000000000, 0, -200218472172217353293439 / 7602176000000000000, 0, 103870346563440959613111 / 15204352000000000000] : List ℝ) τ,
    polyEval ([0, -82976583786612198683 / 131072000000000000, 0, 107359132221524045863 / 16384000000000000, 0, -16245334412287393259847 / 1310720000000000000, 0, 3147586259498210897367 / 655360000000000000] : List ℝ) τ,
    polyEval ([-82976583786612198683 / 2031616000000000000, 0, 217138450405531972317 / 162529280000000000, 0, -1838525786919352483953 / 406323200000000000, 0, 22033103816487476281569 / 8126464000000000000] : List ℝ) τ,
    polyEval ([0, 359101465605862700721 / 2097152000000000000, 0, -1296009980943150111639 / 1048576000000000000, 0, 5084562419189417603439 / 4194304000000000000] : List ℝ) τ,
    polyEval ([10881862594117051537 / 1048576000000000000, 0, -249338072443608161013 / 1048576000000000000, 0, 22011092723763712569 / 52428800000000000] : List ℝ) τ,
    polyEval ([0, -30139766998677909573 / 1048576000000000000, 0, 14242471762435343427 / 131072000000000000] : List ℝ) τ,
    polyEval ([-4305680999811129939 / 2621440000000000000, 0, 103766579983457502111 / 5242880000000000000] : List ℝ) τ,
    polyEval ([0, 4747490587478447809 / 2097152000000000000] : List ℝ) τ,
    polyEval ([4747490587478447809 / 38797312000000000000] : List ℝ) τ]

private theorem autocorr_upperUnitTest {τ : ℝ} (h0 : 0 ≤ τ) (h2 : τ ≤ 2) :
    autocorr upperUnitTest τ = polyEval upperAcList τ := by
  rw [autocorr_shift_unit_support contDiff_upperUnitTest.continuous tsupport_upperUnitTest h0 h2]
  have hcongr : (∫ u in (-1 : ℝ)..(1 - τ), upperUnitTest u * upperUnitTest (u + τ)) =
      ∫ u in (-1 : ℝ)..(1 - τ), polyEval upperUnitPolyList u * polyEval upperUnitPolyList (u + τ) :=
    intervalIntegral.integral_congr fun u hu => by
      rw [uIcc_of_le (by linarith : (-1 : ℝ) ≤ 1 - τ)] at hu
      rw [upperUnitTest_eq_of_mem ⟨hu.1, by linarith [hu.2]⟩,
        upperUnitTest_eq_of_mem ⟨by linarith [hu.1], by linarith [hu.2]⟩]
  have hd : ∀ u ∈ uIcc (-1 : ℝ) (1 - τ),
      HasDerivAt (polyEval (upperBivAntideriv τ))
        (polyEval upperUnitPolyList u * polyEval upperUnitPolyList (u + τ)) u :=
    fun u _ => (hasDerivAt_polyEval (upperBivAntideriv τ) u).congr_deriv
      (by dsimp [upperBivAntideriv, upperUnitPolyList, polyDeriv, polyAdd, polyEval]; ring)
  rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_polyEval _).mul ((continuous_polyEval _).comp (continuous_id.add continuous_const))).intervalIntegrable _ _)]
  dsimp [upperBivAntideriv, upperAcList, polyEval]; ring

private def upperMassRat : ℝ := (8573402398840939849351 / 9058518230969238281250 : ℝ)

private theorem integral_sq_upperUnitTest : (∫ u, upperUnitTest u ^ 2) = 2 * upperMassRat := by
  have h0 := autocorr_upperUnitTest le_rfl (by norm_num : (0 : ℝ) ≤ 2)
  rw [autocorr_zero_eq] at h0
  rw [h0]; norm_num [upperAcList, upperMassRat, polyEval]

theorem integral_sq_twoPrimeScaleTest {s : ℝ} (hs : 0 < s) :
    (∫ x, twoPrimeScaleTest s x ^ 2) = 2 * (s * Real.log 2) * upperMassRat := by
  have hA : 0 < s * Real.log 2 := mul_pos hs apertureLogTwo_pos
  have hsc := Measure.integral_comp_div (fun u => upperUnitTest u ^ 2) (s * Real.log 2)
  rw [abs_of_pos hA, smul_eq_mul] at hsc
  change (∫ x, twoPrimeScaleTest s x ^ 2) = (s * Real.log 2) * ∫ u, upperUnitTest u ^ 2 at hsc
  rw [hsc, integral_sq_upperUnitTest]; ring

theorem integral_sq_twoPrimeScaleTest_pos {s : ℝ} (hs : 0 < s) :
    0 < ∫ x, twoPrimeScaleTest s x ^ 2 := by
  rw [integral_sq_twoPrimeScaleTest hs]
  have hA : 0 < s * Real.log 2 := mul_pos hs apertureLogTwo_pos
  have hM : 0 < upperMassRat := by norm_num [upperMassRat]
  positivity

theorem integral_sq_twoPrimeUpperTest_pos : 0 < ∫ x, twoPrimeUpperTest x ^ 2 :=
  integral_sq_twoPrimeScaleTest_pos one_pos

private theorem autocorr_twoPrimeScaleTest {s : ℝ} (hs : 0 < s) (τ : ℝ) :
    autocorr (twoPrimeScaleTest s) ((s * Real.log 2) * τ) = (s * Real.log 2) * autocorr upperUnitTest τ := by
  have hA : 0 < s * Real.log 2 := mul_pos hs apertureLogTwo_pos
  unfold autocorr twoPrimeScaleTest
  have h := Measure.integral_comp_div (fun u => upperUnitTest u * upperUnitTest (u + τ)) (s * Real.log 2)
  rw [abs_of_pos hA, smul_eq_mul] at h
  refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans h
  dsimp only; rw [add_div, mul_div_cancel_left₀ _ hA.ne']

private def tauPrim_0 : List ℝ := ([0, 0, 165426213857465883643 / 57605839306640625000, 0, -3200849337069904792453 / 1566878829140625000000, 0, 19089405752363054249371 / 15668788291406250000000, -779917329 / 957031250000, -318039004990404130451 / 539141102500000000000, 49847837567 / 3281250000000, 73511039832564976371 / 464776812500000000000, 153835075690067 / 529375000000000, -1042428869593373167 / 1392300000000000000, 52131905463531143 / 48798750000000000, -506025198368967 / 392000000000000, 2288040970943921507 / 1801800000000000000, -597667008229663 / 640000000000000, 22351018842066239491 / 46286240000000000000, -1400553559032959 / 8640000000000000, 793911803213484089 / 27752524800000000000, 0, -38354024591996450291 / 52145533440000000000000, 0, 653352416728657797 / 159220705280000000000000, 0, 19846133129151735729 / 3461319680000000000000000, 0, -175288131730815073 / 164317593600000000000000, 0, 1527653904135711397 / 12283652997120000000000000, 0, -16195229654724461 / 1575289651200000000000000, 0, 576031450532993 / 975663267840000000000000, 0, -2508993362161 / 117833728000000000000000, 0, 141088608501841 / 387154496716800000000000000] : List ℝ)
private theorem tau_moment_eq_0 :
    (∫ τ in (0 : ℝ)..2, τ ^ 0 * polyEval upperDiffDivTauList τ) = (2963742098784573942031661892392419327 / 1008313375221375690925343627929687500 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_0) (τ ^ 0 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_0 τ).congr_deriv
      (by dsimp [tauPrim_0, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_0, polyEval]
private def tauPrim_1 : List ℝ := ([0, 0, 0, 165426213857465883643 / 86408758959960937500, 0, -3200849337069904792453 / 1958598536425781250000, 0, 19089405752363054249371 / 18280253006640625000000, -779917329 / 1093750000000, -318039004990404130451 / 606533740312500000000, 149543512701 / 10937500000000, 73511039832564976371 / 511254493750000000000, 153835075690067 / 577500000000000, -1042428869593373167 / 1508325000000000000, 52131905463531143 / 52552500000000000, -168675066122989 / 140000000000000, 2288040970943921507 / 1921920000000000000, -35156882837039 / 40000000000000, 22351018842066239491 / 49008960000000000000, -73713345212261 / 480000000000000, 793911803213484089 / 29213184000000000000, 0, -38354024591996450291 / 54628654080000000000000, 0, 217784138909552599 / 55381114880000000000000, 0, 19846133129151735729 / 3599772467200000000000000, 0, -175288131730815073 / 170403430400000000000000, 0, 1527653904135711397 / 12707227238400000000000000, 0, -16195229654724461 / 1626105446400000000000000, 0, 372726232697819 / 650442178560000000000000, 0, -17562953535127 / 848402841600000000000000, 0, 7425716236939 / 20927270092800000000000000] : List ℝ)
private theorem tau_moment_eq_1 :
    (∫ τ in (0 : ℝ)..2, τ ^ 1 * polyEval upperDiffDivTauList τ) = (61926043073418507534419441 / 21762184198080498046875000 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_1) (τ ^ 1 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_1 τ).congr_deriv
      (by dsimp [tauPrim_1, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_1, polyEval]
private def tauPrim_2 : List ℝ := ([0, 0, 0, 0, 165426213857465883643 / 115211678613281250000, 0, -3200849337069904792453 / 2350318243710937500000, 0, 19089405752363054249371 / 20891717721875000000000, -86657481 / 136718750000, -318039004990404130451 / 673926378125000000000, 13594864791 / 1093750000000, 24503679944188325457 / 185910725000000000000, 153835075690067 / 625625000000000, -1042428869593373167 / 1624350000000000000, 52131905463531143 / 56306250000000000, -506025198368967 / 448000000000000, 2288040970943921507 / 2042040000000000000, -597667008229663 / 720000000000000, 22351018842066239491 / 51731680000000000000, -1400553559032959 / 9600000000000000, 793911803213484089 / 30673843200000000000, 0, -1667566286608541317 / 2483120640000000000000, 0, 653352416728657797 / 173065984000000000000000, 0, 6615377709717245243 / 1246075084800000000000000, 0, -175288131730815073 / 176489267200000000000000, 0, 1527653904135711397 / 13130801479680000000000000, 0, -1472293604974951 / 152447385600000000000000, 0, 905192279408989 / 1626105446400000000000000, 0, -17562953535127 / 871969587200000000000000, 0, 10852969884757 / 31390905139200000000000000] : List ℝ)
private theorem tau_moment_eq_2 :
    (∫ τ in (0 : ℝ)..2, τ ^ 2 * polyEval upperDiffDivTauList τ) = (2214956280682876247830331 / 634096276167846679687500 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_2) (τ ^ 2 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_2 τ).congr_deriv
      (by dsimp [tauPrim_2, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_2, polyEval]
private def tauPrim_3 : List ℝ := ([0, 0, 0, 0, 0, 165426213857465883643 / 144014598266601562500, 0, -3200849337069904792453 / 2742037950996093750000, 0, 19089405752363054249371 / 23503182437109375000000, -779917329 / 1367187500000, -318039004990404130451 / 741319015937500000000, 49847837567 / 4375000000000, 73511039832564976371 / 604209856250000000000, 153835075690067 / 673750000000000, -1042428869593373167 / 1740375000000000000, 52131905463531143 / 60060000000000000, -29766188139351 / 28000000000000, 2288040970943921507 / 2162160000000000000, -31456158327877 / 40000000000000, 22351018842066239491 / 54454400000000000000, -1400553559032959 / 10080000000000000, 793911803213484089 / 32134502400000000000, 0, -38354024591996450291 / 59594895360000000000000, 0, 653352416728657797 / 179988623360000000000000, 0, 19846133129151735729 / 3876678041600000000000000, 0, -175288131730815073 / 182575104000000000000000, 0, 1527653904135711397 / 13554375720960000000000000, 0, -16195229654724461 / 1727737036800000000000000, 0, 6336345955862923 / 11707959214080000000000000, 0, -924365975533 / 47133491200000000000000, 0, 141088608501841 / 418545401856000000000000000] : List ℝ)
private theorem tau_moment_eq_3 :
    (∫ τ in (0 : ℝ)..2, τ ^ 3 * polyEval upperDiffDivTauList τ) = (800862363486925844515213463 / 163216381485603735351562500 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_3) (τ ^ 3 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_3 τ).congr_deriv
      (by dsimp [tauPrim_3, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_3, polyEval]
private def tauPrim_4 : List ℝ := ([0, 0, 0, 0, 0, 0, 165426213857465883643 / 172817517919921875000, 0, -3200849337069904792453 / 3133757658281250000000, 0, 19089405752363054249371 / 26114647152343750000000, -779917329 / 1503906250000, -318039004990404130451 / 808711653750000000000, 149543512701 / 14218750000000, 73511039832564976371 / 650687537500000000000, 153835075690067 / 721875000000000, -1042428869593373167 / 1856400000000000000, 52131905463531143 / 63813750000000000, -168675066122989 / 168000000000000, 2288040970943921507 / 2282280000000000000, -597667008229663 / 800000000000000, 22351018842066239491 / 57177120000000000000, -1400553559032959 / 10560000000000000, 793911803213484089 / 33595161600000000000, 0, -38354024591996450291 / 62078016000000000000000, 0, 217784138909552599 / 62303754240000000000000, 0, 19846133129151735729 / 4015130828800000000000000, 0, -175288131730815073 / 188660940800000000000000, 0, 1527653904135711397 / 13977949962240000000000000, 0, -16195229654724461 / 1778552832000000000000000, 0, 6336345955862923 / 12033180303360000000000000, 0, -1350996425779 / 70700236800000000000000, 0, 141088608501841 / 429009036902400000000000000] : List ℝ)
private theorem tau_moment_eq_4 :
    (∫ τ in (0 : ℝ)..2, τ ^ 4 * polyEval upperDiffDivTauList τ) = (145973452084616473861364291 / 19498460492161285400390625 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_4) (τ ^ 4 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_4 τ).congr_deriv
      (by dsimp [tauPrim_4, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_4, polyEval]
private def tauPrim_5 : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 165426213857465883643 / 201620437573242187500, 0, -3200849337069904792453 / 3525477365566406250000, 0, 19089405752363054249371 / 28726111867578125000000, -259972443 / 546875000000, -318039004990404130451 / 876104291562500000000, 149543512701 / 15312500000000, 24503679944188325457 / 232388406250000000000, 153835075690067 / 770000000000000, -1042428869593373167 / 1972425000000000000, 52131905463531143 / 67567500000000000, -506025198368967 / 532000000000000, 2288040970943921507 / 2402400000000000000, -597667008229663 / 840000000000000, 22351018842066239491 / 59899840000000000000, -60893633001433 / 480000000000000, 793911803213484089 / 35055820800000000000, 0, -38354024591996450291 / 64561136640000000000000, 0, 653352416728657797 / 193833902080000000000000, 0, 6615377709717245243 / 1384527872000000000000000, 0, -175288131730815073 / 194746777600000000000000, 0, 1527653904135711397 / 14401524203520000000000000, 0, -16195229654724461 / 1829368627200000000000000, 0, 6336345955862923 / 12358401392640000000000000, 0, -17562953535127 / 942669824000000000000000, 0, 20155515500263 / 62781810278400000000000000] : List ℝ)
private theorem tau_moment_eq_5 :
    (∫ τ in (0 : ℝ)..2, τ ^ 5 * polyEval upperDiffDivTauList τ) = (41810139369292148831766899371 / 3468348106569079376220703125 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_5) (τ ^ 5 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_5 τ).congr_deriv
      (by dsimp [tauPrim_5, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_5, polyEval]
private def tauPrim_6 : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 165426213857465883643 / 230423357226562500000, 0, -3200849337069904792453 / 3917197072851562500000, 0, 19089405752363054249371 / 31337576582812500000000, -779917329 / 1777343750000, -318039004990404130451 / 943496929375000000000, 49847837567 / 5468750000000, 73511039832564976371 / 743642900000000000000, 153835075690067 / 818125000000000, -1042428869593373167 / 2088450000000000000, 52131905463531143 / 71321250000000000, -506025198368967 / 560000000000000, 2288040970943921507 / 2522520000000000000, -597667008229663 / 880000000000000, 22351018842066239491 / 62622560000000000000, -1400553559032959 / 11520000000000000, 793911803213484089 / 36516480000000000000, 0, -38354024591996450291 / 67044257280000000000000, 0, 653352416728657797 / 200756541440000000000000, 0, 19846133129151735729 / 4292036403200000000000000, 0, -175288131730815073 / 200832614400000000000000, 0, 1527653904135711397 / 14825098444800000000000000, 0, -16195229654724461 / 1880184422400000000000000, 0, 487411227374071 / 975663267840000000000000, 0, -17562953535127 / 966236569600000000000000, 0, 141088608501841 / 449936306995200000000000000] : List ℝ)
private theorem tau_moment_eq_6 :
    (∫ τ in (0 : ℝ)..2, τ ^ 6 * polyEval upperDiffDivTauList τ) = (1048312648977840176263786988 / 52040718692871844482421875 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_6) (τ ^ 6 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_6 τ).congr_deriv
      (by dsimp [tauPrim_6, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_6, polyEval]
private def tauPrim_7 : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 165426213857465883643 / 259226276879882812500, 0, -3200849337069904792453 / 4308916780136718750000, 0, 19089405752363054249371 / 33949041298046875000000, -779917329 / 1914062500000, -318039004990404130451 / 1010889567187500000000, 149543512701 / 17500000000000, 73511039832564976371 / 790120581250000000000, 153835075690067 / 866250000000000, -1042428869593373167 / 2204475000000000000, 52131905463531143 / 75075000000000000, -168675066122989 / 196000000000000, 2288040970943921507 / 2642640000000000000, -597667008229663 / 920000000000000, 22351018842066239491 / 65345280000000000000, -1400553559032959 / 12000000000000000, 793911803213484089 / 37977139200000000000, 0, -38354024591996450291 / 69527377920000000000000, 0, 217784138909552599 / 69226393600000000000000, 0, 19846133129151735729 / 4430489190400000000000000, 0, -175288131730815073 / 206918451200000000000000, 0, 1527653904135711397 / 15248672686080000000000000, 0, -16195229654724461 / 1931000217600000000000000, 0, 6336345955862923 / 13008843571200000000000000, 0, -2508993362161 / 141400473600000000000000, 0, 12826237136531 / 41854540185600000000000000] : List ℝ)
private theorem tau_moment_eq_7 :
    (∫ τ in (0 : ℝ)..2, τ ^ 7 * polyEval upperDiffDivTauList τ) = (39970406428063200721912040212 / 1156116035523026458740234375 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_7) (τ ^ 7 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_7 τ).congr_deriv
      (by dsimp [tauPrim_7, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_7, polyEval]
private def tauPrim_8 : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 165426213857465883643 / 288029196533203125000, 0, -3200849337069904792453 / 4700636487421875000000, 0, 19089405752363054249371 / 36560506013281250000000, -259972443 / 683593750000, -318039004990404130451 / 1078282205000000000000, 149543512701 / 18593750000000, 8167893314729441819 / 92955362500000000000, 153835075690067 / 914375000000000, -1042428869593373167 / 2320500000000000000, 52131905463531143 / 78828750000000000, -506025198368967 / 616000000000000, 99480042214953109 / 120120000000000000, -597667008229663 / 960000000000000, 22351018842066239491 / 68068000000000000000, -1400553559032959 / 12480000000000000, 793911803213484089 / 39437798400000000000, 0, -38354024591996450291 / 72010498560000000000000, 0, 653352416728657797 / 214601820160000000000000, 0, 6615377709717245243 / 1522980659200000000000000, 0, -175288131730815073 / 213004288000000000000000, 0, 1527653904135711397 / 15672246927360000000000000, 0, -16195229654724461 / 1981816012800000000000000, 0, 6336345955862923 / 13334064660480000000000000, 0, -17562953535127 / 1013370060800000000000000, 0, 141088608501841 / 470863577088000000000000000] : List ℝ)
private theorem tau_moment_eq_8 :
    (∫ τ in (0 : ℝ)..2, τ ^ 8 * polyEval upperDiffDivTauList τ) = (456799570271561115058033761776 / 7545904210466417449951171875 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_8) (τ ^ 8 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_8 τ).congr_deriv
      (by dsimp [tauPrim_8, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_8, polyEval]
private def tauPrim_9 : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 165426213857465883643 / 316832116186523437500, 0, -3200849337069904792453 / 5092356194707031250000, 0, 19089405752363054249371 / 39171970728515625000000, -779917329 / 2187500000000, -318039004990404130451 / 1145674842812500000000, 49847837567 / 6562500000000, 73511039832564976371 / 883075943750000000000, 153835075690067 / 962500000000000, -1042428869593373167 / 2436525000000000000, 52131905463531143 / 82582500000000000, -506025198368967 / 644000000000000, 2288040970943921507 / 2882880000000000000, -597667008229663 / 1000000000000000, 22351018842066239491 / 70790720000000000000, -1400553559032959 / 12960000000000000, 793911803213484089 / 40898457600000000000, 0, -38354024591996450291 / 74493619200000000000000, 0, 653352416728657797 / 221524459520000000000000, 0, 19846133129151735729 / 4707394764800000000000000, 0, -175288131730815073 / 219090124800000000000000, 0, 1527653904135711397 / 16095821168640000000000000, 0, -16195229654724461 / 2032631808000000000000000, 0, 905192279408989 / 1951326535680000000000000, 0, -1596632139557 / 94266982400000000000000, 0, 6134287326167 / 20927270092800000000000000] : List ℝ)
private theorem tau_moment_eq_9 :
    (∫ τ in (0 : ℝ)..2, τ ^ 9 * polyEval upperDiffDivTauList τ) = (21281803051746064416732351837808 / 197695842074437524444580078125 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_9) (τ ^ 9 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_9 τ).congr_deriv
      (by dsimp [tauPrim_9, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_9, polyEval]
private def tauPrim_10 : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 165426213857465883643 / 345635035839843750000, 0, -3200849337069904792453 / 5484075901992187500000, 0, 19089405752363054249371 / 41783435443750000000000, -779917329 / 2324218750000, -318039004990404130451 / 1213067480625000000000, 149543512701 / 20781250000000, 73511039832564976371 / 929553625000000000000, 153835075690067 / 1010625000000000, -1042428869593373167 / 2552550000000000000, 52131905463531143 / 86336250000000000, -168675066122989 / 224000000000000, 2288040970943921507 / 3003000000000000000, -597667008229663 / 1040000000000000, 22351018842066239491 / 73513440000000000000, -1400553559032959 / 13440000000000000, 793911803213484089 / 42359116800000000000, 0, -38354024591996450291 / 76976739840000000000000, 0, 217784138909552599 / 76149032960000000000000, 0, 19846133129151735729 / 4845847552000000000000000, 0, -175288131730815073 / 225175961600000000000000, 0, 1527653904135711397 / 16519395409920000000000000, 0, -16195229654724461 / 2083447603200000000000000, 0, 6336345955862923 / 13984506839040000000000000, 0, -17562953535127 / 1060503552000000000000000, 0, 141088608501841 / 491790847180800000000000000] : List ℝ)
private theorem tau_moment_eq_10 :
    (∫ τ in (0 : ℝ)..2, τ ^ 10 * polyEval upperDiffDivTauList τ) = (251762943320918310734116713664 / 1299111713889822784423828125 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_10) (τ ^ 10 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_10 τ).congr_deriv
      (by dsimp [tauPrim_10, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_10, polyEval]
private def tauPrim_11 : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 165426213857465883643 / 374437955493164062500, 0, -3200849337069904792453 / 5875795609277343750000, 0, 19089405752363054249371 / 44394900158984375000000, -86657481 / 273437500000, -318039004990404130451 / 1280460118437500000000, 149543512701 / 21875000000000, 24503679944188325457 / 325343768750000000000, 153835075690067 / 1058750000000000, -1042428869593373167 / 2668575000000000000, 52131905463531143 / 90090000000000000, -506025198368967 / 700000000000000, 2288040970943921507 / 3123120000000000000, -597667008229663 / 1080000000000000, 22351018842066239491 / 76236160000000000000, -1400553559032959 / 13920000000000000, 793911803213484089 / 43819776000000000000, 0, -38354024591996450291 / 79459860480000000000000, 0, 653352416728657797 / 235369738240000000000000, 0, 6615377709717245243 / 1661433446400000000000000, 0, -175288131730815073 / 231261798400000000000000, 0, 1527653904135711397 / 16942969651200000000000000, 0, -16195229654724461 / 2134263398400000000000000, 0, 576031450532993 / 1300884357120000000000000, 0, -17562953535127 / 1084070297600000000000000, 0, 141088608501841 / 502254482227200000000000000] : List ℝ)
private theorem tau_moment_eq_11 :
    (∫ τ in (0 : ℝ)..2, τ ^ 11 * polyEval upperDiffDivTauList τ) = (4644322785590215664792224099264 / 13179722804962501629638671875 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_11) (τ ^ 11 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_11 τ).congr_deriv
      (by dsimp [tauPrim_11, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_11, polyEval]
private def tauPrim_12 : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 165426213857465883643 / 403240875146484375000, 0, -3200849337069904792453 / 6267515316562500000000, 0, 19089405752363054249371 / 47006364874218750000000, -779917329 / 2597656250000, -318039004990404130451 / 1347852756250000000000, 49847837567 / 7656250000000, 73511039832564976371 / 1022508987500000000000, 153835075690067 / 1106875000000000, -1042428869593373167 / 2784600000000000000, 52131905463531143 / 93843750000000000, -506025198368967 / 728000000000000, 2288040970943921507 / 3243240000000000000, -597667008229663 / 1120000000000000, 22351018842066239491 / 78958880000000000000, -1400553559032959 / 14400000000000000, 793911803213484089 / 45280435200000000000, 0, -38354024591996450291 / 81942981120000000000000, 0, 653352416728657797 / 242292377600000000000000, 0, 19846133129151735729 / 5122753126400000000000000, 0, -175288131730815073 / 237347635200000000000000, 0, 1527653904135711397 / 17366543892480000000000000, 0, -16195229654724461 / 2185079193600000000000000, 0, 6336345955862923 / 14634949017600000000000000, 0, -17562953535127 / 1107637043200000000000000, 0, 20155515500263 / 73245445324800000000000000] : List ℝ)
private theorem tau_moment_eq_12 :
    (∫ τ in (0 : ℝ)..2, τ ^ 12 * polyEval upperDiffDivTauList τ) = (2520450370298897126692542290930432 / 3901232476811137821624755859375 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_12) (τ ^ 12 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_12 τ).congr_deriv
      (by dsimp [tauPrim_12, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_12, polyEval]
private def tauPrim_13 : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 165426213857465883643 / 432043794799804687500, 0, -3200849337069904792453 / 6659235023847656250000, 0, 19089405752363054249371 / 49617829589453125000000, -779917329 / 2734375000000, -318039004990404130451 / 1415245394062500000000, 13594864791 / 2187500000000, 73511039832564976371 / 1068986668750000000000, 153835075690067 / 1155000000000000, -1042428869593373167 / 2900625000000000000, 52131905463531143 / 97597500000000000, -168675066122989 / 252000000000000, 2288040970943921507 / 3363360000000000000, -597667008229663 / 1160000000000000, 22351018842066239491 / 81681600000000000000, -1400553559032959 / 14880000000000000, 793911803213484089 / 46741094400000000000, 0, -38354024591996450291 / 84426101760000000000000, 0, 217784138909552599 / 83071672320000000000000, 0, 19846133129151735729 / 5261205913600000000000000, 0, -175288131730815073 / 243433472000000000000000, 0, 1527653904135711397 / 17790118133760000000000000, 0, -1472293604974951 / 203263180800000000000000, 0, 6336345955862923 / 14960170106880000000000000, 0, -17562953535127 / 1131203788800000000000000, 0, 141088608501841 / 523181752320000000000000000] : List ℝ)
private theorem tau_moment_eq_13 :
    (∫ τ in (0 : ℝ)..2, τ ^ 13 * polyEval upperDiffDivTauList τ) = (273914631508837010654323527890176 / 229646685237982982940673828125 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_13) (τ ^ 13 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_13 τ).congr_deriv
      (by dsimp [tauPrim_13, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_13, polyEval]
private def tauPrim_14 : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 165426213857465883643 / 460846714453125000000, 0, -3200849337069904792453 / 7050954731132812500000, 0, 19089405752363054249371 / 52229294304687500000000, -259972443 / 957031250000, -318039004990404130451 / 1482638031875000000000, 149543512701 / 25156250000000, 24503679944188325457 / 371821450000000000000, 153835075690067 / 1203125000000000, -1042428869593373167 / 3016650000000000000, 52131905463531143 / 101351250000000000, -506025198368967 / 784000000000000, 2288040970943921507 / 3483480000000000000, -597667008229663 / 1200000000000000, 22351018842066239491 / 84404320000000000000, -1400553559032959 / 15360000000000000, 793911803213484089 / 48201753600000000000, 0, -38354024591996450291 / 86909222400000000000000, 0, 653352416728657797 / 256137656320000000000000, 0, 6615377709717245243 / 1799886233600000000000000, 0, -175288131730815073 / 249519308800000000000000, 0, 1527653904135711397 / 18213692375040000000000000, 0, -16195229654724461 / 2286710784000000000000000, 0, 6336345955862923 / 15285391196160000000000000, 0, -2508993362161 / 164967219200000000000000, 0, 8299329911873 / 31390905139200000000000000] : List ℝ)
private theorem tau_moment_eq_14 :
    (∫ τ in (0 : ℝ)..2, τ ^ 14 * polyEval upperDiffDivTauList τ) = (112344544242480780911895264459538432 / 50716022198544791681121826171875 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_14) (τ ^ 14 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_14 τ).congr_deriv
      (by dsimp [tauPrim_14, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_14, polyEval]
private def tauPrim_15 : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 165426213857465883643 / 489649634106445312500, 0, -3200849337069904792453 / 7442674438417968750000, 0, 19089405752363054249371 / 54840759019921875000000, -779917329 / 3007812500000, -318039004990404130451 / 1550030669687500000000, 49847837567 / 8750000000000, 73511039832564976371 / 1161942031250000000000, 153835075690067 / 1251250000000000, -1042428869593373167 / 3132675000000000000, 52131905463531143 / 105105000000000000, -506025198368967 / 812000000000000, 2288040970943921507 / 3603600000000000000, -597667008229663 / 1240000000000000, 22351018842066239491 / 87127040000000000000, -1400553559032959 / 15840000000000000, 793911803213484089 / 49662412800000000000, 0, -38354024591996450291 / 89392343040000000000000, 0, 653352416728657797 / 263060295680000000000000, 0, 19846133129151735729 / 5538111488000000000000000, 0, -175288131730815073 / 255605145600000000000000, 0, 1527653904135711397 / 18637266616320000000000000, 0, -16195229654724461 / 2337526579200000000000000, 0, 6336345955862923 / 15610612285440000000000000, 0, -17562953535127 / 1178337280000000000000000, 0, 10852969884757 / 41854540185600000000000000] : List ℝ)
private theorem tau_moment_eq_15 :
    (∫ τ in (0 : ℝ)..2, τ ^ 15 * polyEval upperDiffDivTauList τ) = (38671223913531381393019755854848 / 9352127453130528717041015625 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_15) (τ ^ 15 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_15 τ).congr_deriv
      (by dsimp [tauPrim_15, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_15, polyEval]
private def tauPrim_16 : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 165426213857465883643 / 518452553759765625000, 0, -3200849337069904792453 / 7834394145703125000000, 0, 19089405752363054249371 / 57452223735156250000000, -779917329 / 3144531250000, -318039004990404130451 / 1617423307500000000000, 149543512701 / 27343750000000, 73511039832564976371 / 1208419712500000000000, 153835075690067 / 1299375000000000, -1042428869593373167 / 3248700000000000000, 52131905463531143 / 108858750000000000, -168675066122989 / 280000000000000, 2288040970943921507 / 3723720000000000000, -597667008229663 / 1280000000000000, 22351018842066239491 / 89849760000000000000, -82385503472527 / 960000000000000, 793911803213484089 / 51123072000000000000, 0, -38354024591996450291 / 91875463680000000000000, 0, 217784138909552599 / 89994311680000000000000, 0, 19846133129151735729 / 5676564275200000000000000, 0, -175288131730815073 / 261690982400000000000000, 0, 1527653904135711397 / 19060840857600000000000000, 0, -16195229654724461 / 2388342374400000000000000, 0, 905192279408989 / 2276547624960000000000000, 0, -1033114913831 / 70700236800000000000000, 0, 141088608501841 / 554572657459200000000000000] : List ℝ)
private theorem tau_moment_eq_16 :
    (∫ τ in (0 : ℝ)..2, τ ^ 16 * polyEval upperDiffDivTauList τ) = (6946739574695588967484128988789633024 / 895983058840957986366485595703125 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_16) (τ ^ 16 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_16 τ).congr_deriv
      (by dsimp [tauPrim_16, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_16, polyEval]
private def tauPrim_17 : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 165426213857465883643 / 547255473413085937500, 0, -3200849337069904792453 / 8226113852988281250000, 0, 19089405752363054249371 / 60063688450390625000000, -259972443 / 1093750000000, -318039004990404130451 / 1684815945312500000000, 149543512701 / 28437500000000, 8167893314729441819 / 139433043750000000000, 153835075690067 / 1347500000000000, -1042428869593373167 / 3364725000000000000, 52131905463531143 / 112612500000000000, -506025198368967 / 868000000000000, 2288040970943921507 / 3843840000000000000, -597667008229663 / 1320000000000000, 22351018842066239491 / 92572480000000000000, -1400553559032959 / 16800000000000000, 793911803213484089 / 52583731200000000000, 0, -38354024591996450291 / 94358584320000000000000, 0, 653352416728657797 / 276905574400000000000000, 0, 6615377709717245243 / 1938339020800000000000000, 0, -175288131730815073 / 267776819200000000000000, 0, 1527653904135711397 / 19484415098880000000000000, 0, -16195229654724461 / 2439158169600000000000000, 0, 6336345955862923 / 16261054464000000000000000, 0, -1350996425779 / 94266982400000000000000, 0, 141088608501841 / 565036292505600000000000000] : List ℝ)
private theorem tau_moment_eq_17 :
    (∫ τ in (0 : ℝ)..2, τ ^ 17 * polyEval upperDiffDivTauList τ) = (42187178849367448553822140493824 / 2890657576422163421630859375 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_17) (τ ^ 17 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_17 τ).congr_deriv
      (by dsimp [tauPrim_17, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_17, polyEval]
private def tauPrim_18 : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 165426213857465883643 / 576058393066406250000, 0, -3200849337069904792453 / 8617833560273437500000, 0, 19089405752363054249371 / 62675153165625000000000, -779917329 / 3417968750000, -318039004990404130451 / 1752208583125000000000, 49847837567 / 9843750000000, 73511039832564976371 / 1301375075000000000000, 153835075690067 / 1395625000000000, -1042428869593373167 / 3480750000000000000, 52131905463531143 / 116366250000000000, -506025198368967 / 896000000000000, 2288040970943921507 / 3963960000000000000, -35156882837039 / 80000000000000, 22351018842066239491 / 95295200000000000000, -1400553559032959 / 17280000000000000, 21457075762526597 / 1460659200000000000, 0, -38354024591996450291 / 96841704960000000000000, 0, 653352416728657797 / 283828213760000000000000, 0, 19846133129151735729 / 5953469849600000000000000, 0, -175288131730815073 / 273862656000000000000000, 0, 1527653904135711397 / 19907989340160000000000000, 0, -16195229654724461 / 2489973964800000000000000, 0, 372726232697819 / 975663267840000000000000, 0, -17562953535127 / 1249037516800000000000000, 0, 12826237136531 / 52318175232000000000000000] : List ℝ)
private theorem tau_moment_eq_18 :
    (∫ τ in (0 : ℝ)..2, τ ^ 18 * polyEval upperDiffDivTauList τ) = (24699664689626876177754261003038154752 / 895983058840957986366485595703125 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_18) (τ ^ 18 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_18 τ).congr_deriv
      (by dsimp [tauPrim_18, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_18, polyEval]
private def tauPrim_19 : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 165426213857465883643 / 604861312719726562500, 0, -3200849337069904792453 / 9009553267558593750000, 0, 19089405752363054249371 / 65286617880859375000000, -779917329 / 3554687500000, -318039004990404130451 / 1819601220937500000000, 149543512701 / 30625000000000, 73511039832564976371 / 1347852756250000000000, 153835075690067 / 1443750000000000, -1042428869593373167 / 3596775000000000000, 52131905463531143 / 120120000000000000, -168675066122989 / 308000000000000, 2288040970943921507 / 4084080000000000000, -597667008229663 / 1400000000000000, 22351018842066239491 / 98017920000000000000, -1400553559032959 / 17760000000000000, 793911803213484089 / 55505049600000000000, 0, -38354024591996450291 / 99324825600000000000000, 0, 217784138909552599 / 96916951040000000000000, 0, 19846133129151735729 / 6091922636800000000000000, 0, -175288131730815073 / 279948492800000000000000, 0, 1527653904135711397 / 20331563581440000000000000, 0, -16195229654724461 / 2540789760000000000000000, 0, 487411227374071 / 1300884357120000000000000, 0, -17562953535127 / 1272604262400000000000000, 0, 20155515500263 / 83709080371200000000000000] : List ℝ)
private theorem tau_moment_eq_19 :
    (∫ τ in (0 : ℝ)..2, τ ^ 19 * polyEval upperDiffDivTauList τ) = (54276112722225328110106180026368 / 1039125272570058746337890625 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_19) (τ ^ 19 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_19 τ).congr_deriv
      (by dsimp [tauPrim_19, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_19, polyEval]
private def tauPrim_20 : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 165426213857465883643 / 633664232373046875000, 0, -3200849337069904792453 / 9401272974843750000000, 0, 19089405752363054249371 / 67898082596093750000000, -28885827 / 136718750000, -318039004990404130451 / 1886993858750000000000, 149543512701 / 31718750000000, 24503679944188325457 / 464776812500000000000, 153835075690067 / 1491875000000000, -1042428869593373167 / 3712800000000000000, 52131905463531143 / 123873750000000000, -29766188139351 / 56000000000000, 2288040970943921507 / 4204200000000000000, -597667008229663 / 1440000000000000, 22351018842066239491 / 100740640000000000000, -73713345212261 / 960000000000000, 793911803213484089 / 56965708800000000000, 0, -38354024591996450291 / 101807946240000000000000, 0, 653352416728657797 / 297673492480000000000000, 0, 6615377709717245243 / 2076791808000000000000000, 0, -175288131730815073 / 286034329600000000000000, 0, 1527653904135711397 / 20755137822720000000000000, 0, -16195229654724461 / 2591605555200000000000000, 0, 6336345955862923 / 17236717731840000000000000, 0, -1596632139557 / 117833728000000000000000, 0, 7425716236939 / 31390905139200000000000000] : List ℝ)
private theorem tau_moment_eq_20 :
    (∫ τ in (0 : ℝ)..2, τ ^ 20 * polyEval upperDiffDivTauList τ) = (4234239141421419847197891217410654208 / 42665859944807523160308837890625 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_20) (τ ^ 20 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_20 τ).congr_deriv
      (by dsimp [tauPrim_20, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_20, polyEval]
private def tauPrim_21 : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 165426213857465883643 / 662467152026367187500, 0, -3200849337069904792453 / 9792992682128906250000, 0, 19089405752363054249371 / 70509547311328125000000, -779917329 / 3828125000000, -318039004990404130451 / 1954386496562500000000, 49847837567 / 10937500000000, 2371323865566612141 / 46477681250000000000, 153835075690067 / 1540000000000000, -1042428869593373167 / 3828825000000000000, 52131905463531143 / 127627500000000000, -506025198368967 / 980000000000000, 2288040970943921507 / 4324320000000000000, -597667008229663 / 1480000000000000, 22351018842066239491 / 103463360000000000000, -1400553559032959 / 18720000000000000, 793911803213484089 / 58426368000000000000, 0, -38354024591996450291 / 104291066880000000000000, 0, 653352416728657797 / 304596131840000000000000, 0, 19846133129151735729 / 6368828211200000000000000, 0, -175288131730815073 / 292120166400000000000000, 0, 1527653904135711397 / 21178712064000000000000000, 0, -16195229654724461 / 2642421350400000000000000, 0, 6336345955862923 / 17561938821120000000000000, 0, -2508993362161 / 188533964800000000000000, 0, 141088608501841 / 606890832691200000000000000] : List ℝ)
private theorem tau_moment_eq_21 :
    (∫ τ in (0 : ℝ)..2, τ ^ 21 * polyEval upperDiffDivTauList τ) = (539660575521740964077540244586496 / 2854859959376687713623046875 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_21) (τ ^ 21 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_21 τ).congr_deriv
      (by dsimp [tauPrim_21, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_21, polyEval]
private def tauPrim_22 : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 165426213857465883643 / 691270071679687500000, 0, -3200849337069904792453 / 10184712389414062500000, 0, 19089405752363054249371 / 73121012026562500000000, -26893701 / 136718750000, -318039004990404130451 / 2021779134375000000000, 149543512701 / 33906250000000, 73511039832564976371 / 1487285800000000000000, 153835075690067 / 1588125000000000, -1042428869593373167 / 3944850000000000000, 52131905463531143 / 131381250000000000, -168675066122989 / 336000000000000, 2288040970943921507 / 4444440000000000000, -31456158327877 / 80000000000000, 22351018842066239491 / 106186080000000000000, -1400553559032959 / 19200000000000000, 793911803213484089 / 59887027200000000000, 0, -38354024591996450291 / 106774187520000000000000, 0, 217784138909552599 / 103839590400000000000000, 0, 19846133129151735729 / 6507280998400000000000000, 0, -175288131730815073 / 298206003200000000000000, 0, 1527653904135711397 / 21602286305280000000000000, 0, -16195229654724461 / 2693237145600000000000000, 0, 576031450532993 / 1626105446400000000000000, 0, -924365975533 / 70700236800000000000000, 0, 141088608501841 / 617354467737600000000000000] : List ℝ)
private theorem tau_moment_eq_22 :
    (∫ τ in (0 : ℝ)..2, τ ^ 22 * polyEval upperDiffDivTauList τ) = (7206940263583047818280800950018035023872 / 19970466844832908007235223388671875 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_22) (τ ^ 22 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_22 τ).congr_deriv
      (by dsimp [tauPrim_22, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_22, polyEval]
private def tauPrim_23 : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 165426213857465883643 / 720072991333007812500, 0, -3200849337069904792453 / 10576432096699218750000, 0, 19089405752363054249371 / 75732476741796875000000, -259972443 / 1367187500000, -318039004990404130451 / 2089171772187500000000, 149543512701 / 35000000000000, 24503679944188325457 / 511254493750000000000, 153835075690067 / 1636250000000000, -1042428869593373167 / 4060875000000000000, 52131905463531143 / 135135000000000000, -506025198368967 / 1036000000000000, 2288040970943921507 / 4564560000000000000, -597667008229663 / 1560000000000000, 22351018842066239491 / 108908800000000000000, -1400553559032959 / 19680000000000000, 793911803213484089 / 61347686400000000000, 0, -38354024591996450291 / 109257308160000000000000, 0, 653352416728657797 / 318441410560000000000000, 0, 6615377709717245243 / 2215244595200000000000000, 0, -175288131730815073 / 304291840000000000000000, 0, 1527653904135711397 / 22025860546560000000000000, 0, -16195229654724461 / 2744052940800000000000000, 0, 905192279408989 / 2601768714240000000000000, 0, -17562953535127 / 1366871244800000000000000, 0, 141088608501841 / 627818102784000000000000000] : List ℝ)
private theorem tau_moment_eq_23 :
    (∫ τ in (0 : ℝ)..2, τ ^ 23 * polyEval upperDiffDivTauList τ) = (493828943979138013008625710167228416 / 715301023154936754913330078125 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_23) (τ ^ 23 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_23 τ).congr_deriv
      (by dsimp [tauPrim_23, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_23, polyEval]
private def tauPrim_24 : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 165426213857465883643 / 748875910986328125000, 0, -3200849337069904792453 / 10968151803984375000000, 0, 19089405752363054249371 / 78343941457031250000000, -779917329 / 4238281250000, -318039004990404130451 / 2156564410000000000000, 4531621597 / 1093750000000, 73511039832564976371 / 1580241162500000000000, 153835075690067 / 1684375000000000, -1042428869593373167 / 4176900000000000000, 52131905463531143 / 138888750000000000, -506025198368967 / 1064000000000000, 2288040970943921507 / 4684680000000000000, -597667008229663 / 1600000000000000, 22351018842066239491 / 111631520000000000000, -1400553559032959 / 20160000000000000, 793911803213484089 / 62808345600000000000, 0, -38354024591996450291 / 111740428800000000000000, 0, 653352416728657797 / 325364049920000000000000, 0, 19846133129151735729 / 6784186572800000000000000, 0, -175288131730815073 / 310377676800000000000000, 0, 1527653904135711397 / 22449434787840000000000000, 0, -1472293604974951 / 254078976000000000000000, 0, 6336345955862923 / 18537602088960000000000000, 0, -17562953535127 / 1390437990400000000000000, 0, 141088608501841 / 638281737830400000000000000] : List ℝ)
private theorem tau_moment_eq_24 :
    (∫ τ in (0 : ℝ)..2, τ ^ 24 * polyEval upperDiffDivTauList τ) = (1846419181266037157493549727878219241619456 / 1395390983358052099487362972412109375 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_24) (τ ^ 24 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_24 τ).congr_deriv
      (by dsimp [tauPrim_24, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_24, polyEval]
private def tauPrim_25 : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 165426213857465883643 / 777678830639648437500, 0, -3200849337069904792453 / 11359871511269531250000, 0, 19089405752363054249371 / 80955406172265625000000, -779917329 / 4375000000000, -318039004990404130451 / 2223957047812500000000, 149543512701 / 37187500000000, 73511039832564976371 / 1626718843750000000000, 153835075690067 / 1732500000000000, -1042428869593373167 / 4292925000000000000, 52131905463531143 / 142642500000000000, -168675066122989 / 364000000000000, 2288040970943921507 / 4804800000000000000, -597667008229663 / 1640000000000000, 22351018842066239491 / 114354240000000000000, -1400553559032959 / 20640000000000000, 793911803213484089 / 64269004800000000000, 0, -1667566286608541317 / 4966241280000000000000, 0, 217784138909552599 / 110762229760000000000000, 0, 19846133129151735729 / 6922639360000000000000000, 0, -175288131730815073 / 316463513600000000000000, 0, 1527653904135711397 / 22873009029120000000000000, 0, -16195229654724461 / 2845684531200000000000000, 0, 6336345955862923 / 18862823178240000000000000, 0, -17562953535127 / 1414004736000000000000000, 0, 141088608501841 / 648745372876800000000000000] : List ℝ)
private theorem tau_moment_eq_25 :
    (∫ τ in (0 : ℝ)..2, τ ^ 25 * polyEval upperDiffDivTauList τ) = (947914932712325030803627573378168127488 / 373107233686512010812835693359375 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_25) (τ ^ 25 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_25 τ).congr_deriv
      (by dsimp [tauPrim_25, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_25, polyEval]
private def tauPrim_26 : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 165426213857465883643 / 806481750292968750000, 0, -3200849337069904792453 / 11751591218554687500000, 0, 19089405752363054249371 / 83566870887500000000000, -259972443 / 1503906250000, -318039004990404130451 / 2291349685625000000000, 149543512701 / 38281250000000, 8167893314729441819 / 185910725000000000000, 153835075690067 / 1780625000000000, -1042428869593373167 / 4408950000000000000, 52131905463531143 / 146396250000000000, -506025198368967 / 1120000000000000, 2288040970943921507 / 4924920000000000000, -597667008229663 / 1680000000000000, 22351018842066239491 / 117076960000000000000, -1400553559032959 / 21120000000000000, 793911803213484089 / 65729664000000000000, 0, -38354024591996450291 / 116706670080000000000000, 0, 653352416728657797 / 339209328640000000000000, 0, 6615377709717245243 / 2353697382400000000000000, 0, -175288131730815073 / 322549350400000000000000, 0, 1527653904135711397 / 23296583270400000000000000, 0, -16195229654724461 / 2896500326400000000000000, 0, 6336345955862923 / 19188044267520000000000000, 0, -17562953535127 / 1437571481600000000000000, 0, 20155515500263 / 94172715417600000000000000] : List ℝ)
private theorem tau_moment_eq_26 :
    (∫ τ in (0 : ℝ)..2, τ ^ 26 * polyEval upperDiffDivTauList τ) = (6817549815561675048909195762750112208519168 / 1395390983358052099487362972412109375 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_26) (τ ^ 26 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_26 τ).congr_deriv
      (by dsimp [tauPrim_26, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_26, polyEval]
private def tauPrim_27 : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 165426213857465883643 / 835284669946289062500, 0, -3200849337069904792453 / 12143310925839843750000, 0, 19089405752363054249371 / 86178335602734375000000, -779917329 / 4648437500000, -318039004990404130451 / 2358742323437500000000, 49847837567 / 13125000000000, 73511039832564976371 / 1719674206250000000000, 153835075690067 / 1828750000000000, -1042428869593373167 / 4524975000000000000, 52131905463531143 / 150150000000000000, -506025198368967 / 1148000000000000, 2288040970943921507 / 5045040000000000000, -597667008229663 / 1720000000000000, 22351018842066239491 / 119799680000000000000, -1400553559032959 / 21600000000000000, 793911803213484089 / 67190323200000000000, 0, -38354024591996450291 / 119189790720000000000000, 0, 653352416728657797 / 346131968000000000000000, 0, 19846133129151735729 / 7199544934400000000000000, 0, -175288131730815073 / 328635187200000000000000, 0, 1527653904135711397 / 23720157511680000000000000, 0, -16195229654724461 / 2947316121600000000000000, 0, 6336345955862923 / 19513265356800000000000000, 0, -17562953535127 / 1461138227200000000000000, 0, 141088608501841 / 669672642969600000000000000] : List ℝ)
private theorem tau_moment_eq_27 :
    (∫ τ in (0 : ℝ)..2, τ ^ 27 * polyEval upperDiffDivTauList τ) = (1014230194044023097459055266951543652352 / 107786534176103469790374755859375 : ℝ) := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 2, HasDerivAt (polyEval tauPrim_27) (τ ^ 27 * polyEval upperDiffDivTauList τ) τ :=
    fun τ _ => (hasDerivAt_polyEval tauPrim_27 τ).congr_deriv
      (by dsimp [tauPrim_27, upperDiffDivTauList, polyDeriv, polyAdd, polyEval]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_pow _).mul (continuous_polyEval _)).intervalIntegrable _ _)]
  norm_num [tauPrim_27, polyEval]

private def upperKupList : List ℝ := ([1250000001 / 2500000000, -1 / 24, -1 / 16, 7 / 5760, 5 / 768, -31 / 967680, -61 / 92160, 127 / 154828800, 277 / 4128768, -73 / 3503554560, -50521 / 7431782400, 1414477 / 2678117105664000, 540553 / 784796221440, -8191 / 612141052723200, -199360981 / 2856658246041600, 0, 3878302429 / 548478383239987200, 0, -2404879675441 / 3356687705428721664000, 0, 14814847529501 / 204086612490066277171200, 0, -69348874393137901 / 9428801497041062005309440000, 0, 238685140977801337 / 320289133930256383195742208000, 0, -4087072509293123892361 / 54128863634213328760080433152000000] : List ℝ)
private def upperKupMomList : List ℝ := ([8600839322633241943493645420491049 / 12090102332266943359375000000000000, -2214956280682876247830331 / 30436621256056640625000000, -800862363486925844515213463 / 5222924207539319531250000000, 145973452084616473861364291 / 32088894981385429687500000000, 41810139369292148831766899371 / 1065476538338021184375000000000, -262078162244460044065946747 / 812238107495455265625000000000, -609548698027963811009158613233 / 53273826916901059218750000000000, 3625846589030516350773142984097 / 146040411727682856759375000000000000, 368441215333353740214678841192051 / 102030033311248908615750000000000000, -287167107225422448181101876523 / 142234649035878248561250000000000000, -192957098232568491448164435624109 / 161100052596708803077500000000000000, 605488973918015134353377571679416553 / 3548898583328750821741947375000000000000000, 44490798018628717734443072707818001 / 108308804591941149145950000000000000000, -56165415154428715603597052684819293 / 3789716701483201770360150946875000000000000, -7528840953000268914841372148049795787 / 52179359388705765382666500000000000000000, 0, 2349704707665429699560847666463362803 / 45538350011961395243054400000000000000000, 0, -3983383799671154115377865116389776387391 / 212891786305919522761279320000000000000000000, 0, 60996926452921691557148872985177257956743 / 8890360996135199270511024403200000000000000000, 0, -2107096112633069880193307415812673811154649947 / 829934318045126518997409528091200000000000000000000, 0, 107885937380506691108343415907851008487820401186253 / 113966171970907889834130308442023600640000000000000000000, 0, -494150202771706275893946755455052402653213357129433209 / 1391020443444914633142134931372921392256000000000000000000000] : List ℝ)
private def upperK14List : List ℝ := ([1 / 2, -1 / 24, -1 / 16, 7 / 5760, 5 / 768, -31 / 967680, -61 / 92160, 127 / 154828800, 277 / 4128768, -73 / 3503554560, -50521 / 7431782400, 1414477 / 2678117105664000, 540553 / 784796221440, -8191 / 612141052723200, -199360981 / 2856658246041600] : List ℝ)
private def upperK14MomList : List ℝ := ([61926043073418507534419441 / 87048736792321992187500000, -2214956280682876247830331 / 30436621256056640625000000, -800862363486925844515213463 / 5222924207539319531250000000, 145973452084616473861364291 / 32088894981385429687500000000, 41810139369292148831766899371 / 1065476538338021184375000000000, -262078162244460044065946747 / 812238107495455265625000000000, -609548698027963811009158613233 / 53273826916901059218750000000000, 3625846589030516350773142984097 / 146040411727682856759375000000000000, 368441215333353740214678841192051 / 102030033311248908615750000000000000, -287167107225422448181101876523 / 142234649035878248561250000000000000, -192957098232568491448164435624109 / 161100052596708803077500000000000000, 605488973918015134353377571679416553 / 3548898583328750821741947375000000000000000, 44490798018628717734443072707818001 / 108308804591941149145950000000000000000, -56165415154428715603597052684819293 / 3789716701483201770360150946875000000000000, -7528840953000268914841372148049795787 / 52179359388705765382666500000000000000000] : List ℝ)
private def upperCoshPolyList : List ℝ := ([643430647 / 938437500, 2459921869 / 382882500000, 344380717 / 12932920000000, 8173040147 / 123559128000000000, 362648839607 / 3238237626624000000000, 18419096797 / 132577258125312000000000, 2219663709173 / 16768371607689461760000000000, 282123195331 / 2817086430091829575680000000000, 55610762041 / 901467657629385464217600000000000] : List ℝ)

private theorem scaled_lag_poly_integral {s : ℝ} (hs : 0 < s) {K_list : List ℝ} {D : ℕ} (hD : K_list.length ≤ D) :
    let A := s * Real.log 2
    (∫ t in Ioc (0 : ℝ) (2 * A),
      (autocorr (twoPrimeScaleTest s) 0 - autocorr (twoPrimeScaleTest s) t) * (1 / t + polyEval K_list t)) / (2 * A) =
      (1 / 2 : ℝ) * (∫ τ in (0 : ℝ)..2, τ ^ 0 * polyEval upperDiffDivTauList τ) +
        A * ∑ j ∈ Finset.range D, coeffAt K_list j * (1 / 2 : ℝ) *
          (∫ τ in (0 : ℝ)..2, τ ^ (j + 1) * polyEval upperDiffDivTauList τ) * A ^ j := by
  intro A
  have hA : 0 < A := mul_pos hs apertureLogTwo_pos
  have h2A : 0 < 2 * A := by positivity
  have h0 : autocorr (twoPrimeScaleTest s) 0 = A * autocorr upperUnitTest 0 := by
    simpa using autocorr_twoPrimeScaleTest hs 0
  have hsub : ∀ τ ∈ Ioc (0 : ℝ) 2,
      (autocorr (twoPrimeScaleTest s) 0 - autocorr (twoPrimeScaleTest s) (A * τ)) *
        (1 / (A * τ) + polyEval K_list (A * τ)) =
      τ ^ 0 * polyEval upperDiffDivTauList τ +
        ∑ j ∈ Finset.range D, (coeffAt K_list j * A ^ (j + 1)) * (τ ^ (j + 1) * polyEval upperDiffDivTauList τ) := by
    intro τ hτ
    have hτ0 : τ ≠ 0 := hτ.1.ne'
    rw [h0, autocorr_twoPrimeScaleTest hs τ, autocorr_upperUnitTest le_rfl (by norm_num),
      autocorr_upperUnitTest hτ.1.le hτ.2]
    have hdiff : polyEval upperAcList 0 - polyEval upperAcList τ = τ * polyEval upperDiffDivTauList τ := by
      dsimp [upperAcList, upperDiffDivTauList, polyEval]; ring
    rw [← mul_sub, hdiff, polyEval_eq_sum_of_le K_list hD (A * τ)]
    have h1 : (A * (τ * polyEval upperDiffDivTauList τ)) *
        (1 / (A * τ) + ∑ p ∈ Finset.range D, coeffAt K_list p * (A * τ) ^ p) =
        τ ^ 0 * polyEval upperDiffDivTauList τ +
          (A * τ * polyEval upperDiffDivTauList τ) * ∑ p ∈ Finset.range D, coeffAt K_list p * (A * τ) ^ p := by
      field_simp [hA.ne', hτ0]; ring
    rw [h1, Finset.mul_sum]; congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow]; ring
  have hcomp := intervalIntegral.mul_integral_comp_mul_left
    (f := fun t => (autocorr (twoPrimeScaleTest s) 0 - autocorr (twoPrimeScaleTest s) t) * (1 / t + polyEval K_list t))
    (a := (0 : ℝ)) (b := 2) (c := A)
  rw [mul_zero, show A * 2 = 2 * A by ring,
    intervalIntegral.integral_of_le h2A.le, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)] at hcomp
  rw [← hcomp, setIntegral_congr_fun measurableSet_Ioc hsub, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
  have hi0 : IntervalIntegrable (fun τ => τ ^ 0 * polyEval upperDiffDivTauList τ) volume 0 2 :=
    ((continuous_pow 0).mul (continuous_polyEval _)).intervalIntegrable 0 2
  have his : ∀ j ∈ Finset.range D, IntervalIntegrable
      (fun τ => (coeffAt K_list j * A ^ (j + 1)) * (τ ^ (j + 1) * polyEval upperDiffDivTauList τ)) volume 0 2 :=
    fun j _ => (continuous_const.mul ((continuous_pow _).mul (continuous_polyEval _))).intervalIntegrable 0 2
  rw [intervalIntegral.integral_add hi0 (IntervalIntegrable.sum _ his),
    intervalIntegral.integral_finsetSum his]
  simp_rw [intervalIntegral.integral_const_mul]
  have hdiv : ∀ X Y : ℝ, (A * (X + Y)) / (2 * A) = (1 / 2 : ℝ) * X + (1 / 2 : ℝ) * Y := fun X Y => by
    field_simp [hA.ne']; ring
  rw [hdiv, Finset.mul_sum]; congr 1
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring

private theorem scaled_lag_kup_eq {s : ℝ} (hs : 0 < s) :
    let A := s * Real.log 2
    (∫ t in Ioc (0 : ℝ) (2 * A),
      (autocorr (twoPrimeScaleTest s) 0 - autocorr (twoPrimeScaleTest s) t) * (1 / t + polyEval upperKupList t)) / (2 * A) =
      (2963742098784573942031661892392419327 / 2016626750442751381850687255859375000 : ℝ) + A * polyEval upperKupMomList A := by
  intro A
  rw [scaled_lag_poly_integral hs (K_list := upperKupList) (D := 27) (by decide)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [tau_moment_eq_0, tau_moment_eq_1, tau_moment_eq_2, tau_moment_eq_3, tau_moment_eq_4, tau_moment_eq_5, tau_moment_eq_6, tau_moment_eq_7, tau_moment_eq_8, tau_moment_eq_9, tau_moment_eq_10, tau_moment_eq_11, tau_moment_eq_12, tau_moment_eq_13, tau_moment_eq_14, tau_moment_eq_15, tau_moment_eq_16, tau_moment_eq_17, tau_moment_eq_18, tau_moment_eq_19, tau_moment_eq_20, tau_moment_eq_21, tau_moment_eq_22, tau_moment_eq_23, tau_moment_eq_24, tau_moment_eq_25, tau_moment_eq_26, tau_moment_eq_27]
  dsimp [upperKupList, upperKupMomList, coeffAt, polyEval]; ring

private theorem scaled_lag_k14_eq :
    let A := Real.log 2
    (∫ t in Ioc (0 : ℝ) (2 * A),
      (autocorr twoPrimeUpperTest 0 - autocorr twoPrimeUpperTest t) * (1 / t + polyEval upperK14List t)) / (2 * A) =
      (2963742098784573942031661892392419327 / 2016626750442751381850687255859375000 : ℝ) + A * polyEval upperK14MomList A := by
  intro A
  have h1 := scaled_lag_poly_integral one_pos (K_list := upperK14List) (D := 15) (by decide)
  dsimp only [one_mul] at h1
  unfold twoPrimeUpperTest; rw [h1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [tau_moment_eq_0, tau_moment_eq_1, tau_moment_eq_2, tau_moment_eq_3, tau_moment_eq_4, tau_moment_eq_5, tau_moment_eq_6, tau_moment_eq_7, tau_moment_eq_8, tau_moment_eq_9, tau_moment_eq_10, tau_moment_eq_11, tau_moment_eq_12, tau_moment_eq_13, tau_moment_eq_14, tau_moment_eq_15]
  dsimp [upperK14List, upperK14MomList, coeffAt, polyEval]; ring

private theorem kup_kernel_eq {t : ℝ} (ht : t ≠ 0) :
    gammaSinhPolynomial14 (t / 2) / t + gammaCoshPolynomial26 (t / 2) / 2 + 4 / 10 ^ 10 =
      1 / t + polyEval upperKupList t := by
  unfold gammaSinhPolynomial14 gammaCoshPolynomial26
  dsimp [upperKupList, polyEval]; field_simp [ht]; ring

private theorem k14_kernel_eq {t : ℝ} (ht : t ≠ 0) :
    gammaSinhPolynomial14 (t / 2) / t + gammaCoshPolynomial14 (t / 2) / 2 =
      1 / t + polyEval upperK14List t := by
  unfold gammaSinhPolynomial14 gammaCoshPolynomial14
  dsimp [upperK14List, polyEval]; field_simp [ht]; ring

private theorem abs_upperUnitTest_le {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    |upperUnitTest u| ≤ (2336679937 / 10240000 : ℝ) := by
  rw [upperUnitTest_eq_of_mem ⟨by linarith [hu.1], hu.2⟩]
  have hpow : ∀ k : ℕ, 0 ≤ u ^ k ∧ u ^ k ≤ 1 := fun k =>
    ⟨pow_nonneg hu.1 k, by simpa using pow_le_pow_left₀ hu.1 hu.2 k⟩
  have hexp : polyEval upperUnitPolyList u = (1938762811 / 1024000000 : ℝ) + (-10133087199 / 1024000000 : ℝ) * u ^ 2 + (5058036369 / 256000000 : ℝ) * u ^ 4 + (-3326115637 / 256000000 : ℝ) * u ^ 6 + (-9650701551 / 512000000 : ℝ) * u ^ 8 + (26993962803 / 512000000 : ℝ) * u ^ 10 + (-15065579023 / 256000000 : ℝ) * u ^ 12 + (1924814463 / 51200000 : ℝ) * u ^ 14 + (-13832727909 / 1024000000 : ℝ) * u ^ 16 + (2178873697 / 1024000000 : ℝ) * u ^ 18 := by
    dsimp [upperUnitPolyList, polyEval]; ring
  rw [hexp, abs_le]; constructor <;>
    linarith [(hpow 2).1, (hpow 2).2, (hpow 4).1, (hpow 4).2, (hpow 6).1, (hpow 6).2, (hpow 8).1, (hpow 8).2, (hpow 10).1, (hpow 10).2, (hpow 12).1, (hpow 12).2, (hpow 14).1, (hpow 14).2, (hpow 16).1, (hpow 16).2, (hpow 18).1, (hpow 18).2]

private theorem coshPairing_twoPrimeScaleTest_le {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    let A := s * Real.log 2
    coshPairing (twoPrimeScaleTest s) ^ 2 / 2 / (2 * A) ≤
      4 * A * (|polyEval upperCoshPolyList (A ^ 2)| + (1 / 10 ^ 18 : ℝ)) ^ 2 := by
  intro A
  obtain ⟨_, h2u⟩ := log_two_bounds_d26
  have hA_pos : 0 < A := mul_pos hs0 apertureLogTwo_pos
  have hA_le : A ≤ logTwoHi := by
    have h1 : A ≤ Real.log 2 := by dsimp [A]; nlinarith [apertureLogTwo_pos]
    linarith
  have hA_lt1 : A ≤ 1 := hA_le.trans (by norm_num [logTwoHi])
  have hcp : coshPairing (twoPrimeScaleTest s) = 4 * A * ∫ u in (0 : ℝ)..1, upperUnitTest u * Real.cosh (A * u / 2) := by
    unfold coshPairing twoPrimeScaleTest
    have hsc := Measure.integral_comp_div (fun u => 2 * Real.cosh ((A * u) / 2) * upperUnitTest u) A
    rw [abs_of_pos hA_pos, smul_eq_mul] at hsc
    have hcongr : (∫ x, 2 * Real.cosh (x / 2) * upperUnitTest (x / A)) =
        ∫ x, 2 * Real.cosh ((A * (x / A)) / 2) * upperUnitTest (x / A) :=
      integral_congr_ae (Eventually.of_forall fun x => by rw [mul_div_cancel₀ _ hA_pos.ne'])
    rw [hcongr, hsc]
    have hcut : (∫ u, 2 * Real.cosh (A * u / 2) * upperUnitTest u) =
        ∫ u in Icc (-1 : ℝ) 1, 2 * Real.cosh (A * u / 2) * upperUnitTest u := by
      symm; apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro u hu; rw [upperUnitTest_outside hu, mul_zero]
    have hev := even_integral_Icc_unit (H := fun u => 2 * Real.cosh (A * u / 2) * upperUnitTest u)
      ((continuous_const.mul (Real.continuous_cosh.comp ((continuous_const.mul continuous_id).div_const 2))).mul contDiff_upperUnitTest.continuous)
      (fun u => by dsimp only; rw [mul_neg, neg_div, Real.cosh_neg, upperUnitTest_even])
    rw [hcut, hev, show (∫ u in (0 : ℝ)..1, 2 * Real.cosh (A * u / 2) * upperUnitTest u) =
        2 * ∫ u in (0 : ℝ)..1, upperUnitTest u * Real.cosh (A * u / 2) by
      rw [← intervalIntegral.integral_const_mul]; exact intervalIntegral.integral_congr fun u _ => by ring]
    ring
  set P_true := ∫ u in (0 : ℝ)..1, upperUnitTest u * Real.cosh (A * u / 2)
  let coshTay16 : ℝ → ℝ := fun z => ∑ j ∈ Finset.range 9, z ^ (2 * j) / ((2 * j).factorial : ℝ)
  have htay_int : (∫ u in (0 : ℝ)..1, upperUnitTest u * coshTay16 (A * u / 2)) = polyEval upperCoshPolyList (A ^ 2) := by
    have hcongr : (∫ u in (0 : ℝ)..1, upperUnitTest u * coshTay16 (A * u / 2)) =
        ∑ j ∈ Finset.range 9, ((A / 2) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
          ∫ u in (0 : ℝ)..1, polyEval upperUnitPolyList u * u ^ (2 * j) := by
      have hfn : ∀ u ∈ uIcc (0 : ℝ) 1, upperUnitTest u * coshTay16 (A * u / 2) =
          ∑ j ∈ Finset.range 9, ((A / 2) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
            (polyEval upperUnitPolyList u * u ^ (2 * j)) := fun u hu => by
        rw [uIcc_of_le zero_le_one] at hu
        rw [upperUnitTest_eq_of_mem ⟨by linarith [hu.1], hu.2⟩]; dsimp [coshTay16]
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
        rw [show A * u / 2 = (A / 2) * u by ring, mul_pow]; ring
      rw [intervalIntegral.integral_congr hfn, intervalIntegral.integral_finsetSum fun j _ =>
        (continuous_const.mul ((continuous_polyEval _).mul (continuous_pow _))).intervalIntegrable 0 1]
      exact Finset.sum_congr rfl fun j _ => intervalIntegral.integral_const_mul _ _
    rw [hcongr]
    have hij_0 : (∫ u in (0 : ℝ)..1, polyEval upperUnitPolyList u * u ^ 0) = (643430647 / 938437500 : ℝ) := by
      let pr : List ℝ := ([0, 1938762811 / 1024000000, 0, -3377695733 / 1024000000, 0, 5058036369 / 1280000000, 0, -3326115637 / 1792000000, 0, -3216900517 / 1536000000, 0, 26993962803 / 5632000000, 0, -15065579023 / 3328000000, 0, 641604821 / 256000000, 0, -813689877 / 1024000000, 0, 114677563 / 1024000000] : List ℝ)
      have hd : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt (polyEval pr) (polyEval upperUnitPolyList u * u ^ 0) u :=
        fun u _ => (hasDerivAt_polyEval pr u).congr_deriv
          (by dsimp [pr, upperUnitPolyList, polyDeriv, polyAdd, polyEval]; ring)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        (((continuous_polyEval _).mul (continuous_pow _)).intervalIntegrable 0 1)]
      norm_num [pr, polyEval]
    have hij_1 : (∫ u in (0 : ℝ)..1, polyEval upperUnitPolyList u * u ^ 2) = (2459921869 / 47860312500 : ℝ) := by
      let pr : List ℝ := ([0, 0, 0, 1938762811 / 3072000000, 0, -10133087199 / 5120000000, 0, 5058036369 / 1792000000, 0, -3326115637 / 2304000000, 0, -9650701551 / 5632000000, 0, 26993962803 / 6656000000, 0, -15065579023 / 3840000000, 0, 1924814463 / 870400000, 0, -728038311 / 1024000000, 0, 311267671 / 3072000000] : List ℝ)
      have hd : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt (polyEval pr) (polyEval upperUnitPolyList u * u ^ 2) u :=
        fun u _ => (hasDerivAt_polyEval pr u).congr_deriv
          (by dsimp [pr, upperUnitPolyList, polyDeriv, polyAdd, polyEval]; ring)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        (((continuous_polyEval _).mul (continuous_pow _)).intervalIntegrable 0 1)]
      norm_num [pr, polyEval]
    have hij_2 : (∫ u in (0 : ℝ)..1, polyEval upperUnitPolyList u * u ^ 4) = (1033142151 / 101038437500 : ℝ) := by
      let pr : List ℝ := ([0, 0, 0, 0, 0, 1938762811 / 5120000000, 0, -10133087199 / 7168000000, 0, 562004041 / 256000000, 0, -3326115637 / 2816000000, 0, -9650701551 / 6656000000, 0, 8997987601 / 2560000000, 0, -15065579023 / 4352000000, 0, 1924814463 / 972800000, 0, -658701329 / 1024000000, 0, 94733639 / 1024000000] : List ℝ)
      have hd : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt (polyEval pr) (polyEval upperUnitPolyList u * u ^ 4) u :=
        fun u _ => (hasDerivAt_polyEval pr u).congr_deriv
          (by dsimp [pr, upperUnitPolyList, polyDeriv, polyAdd, polyEval]; ring)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        (((continuous_polyEval _).mul (continuous_pow _)).intervalIntegrable 0 1)]
      norm_num [pr, polyEval]
    have hij_3 : (∫ u in (0 : ℝ)..1, polyEval upperUnitPolyList u * u ^ 6) = (8173040147 / 2681404687500 : ℝ) := by
      let pr : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 1938762811 / 7168000000, 0, -3377695733 / 3072000000, 0, 5058036369 / 2816000000, 0, -255855049 / 256000000, 0, -3216900517 / 2560000000, 0, 26993962803 / 8704000000, 0, -15065579023 / 4864000000, 0, 641604821 / 358400000, 0, -13832727909 / 23552000000, 0, 2178873697 / 25600000000] : List ℝ)
      have hd : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt (polyEval pr) (polyEval upperUnitPolyList u * u ^ 6) u :=
        fun u _ => (hasDerivAt_polyEval pr u).congr_deriv
          (by dsimp [pr, upperUnitPolyList, polyDeriv, polyAdd, polyEval]; ring)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        (((continuous_polyEval _).mul (continuous_pow _)).intervalIntegrable 0 1)]
      norm_num [pr, polyEval]
    have hij_4 : (∫ u in (0 : ℝ)..1, polyEval upperUnitPolyList u * u ^ 8) = (362648839607 / 313724348437500 : ℝ) := by
      let pr : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1938762811 / 9216000000, 0, -10133087199 / 11264000000, 0, 5058036369 / 3328000000, 0, -3326115637 / 3840000000, 0, -9650701551 / 8704000000, 0, 26993962803 / 9728000000, 0, -15065579023 / 5376000000, 0, 1924814463 / 1177600000, 0, -13832727909 / 25600000000, 0, 2178873697 / 27648000000] : List ℝ)
      have hd : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt (polyEval pr) (polyEval upperUnitPolyList u * u ^ 8) u :=
        fun u _ => (hasDerivAt_polyEval pr u).congr_deriv
          (by dsimp [pr, upperUnitPolyList, polyDeriv, polyAdd, polyEval]; ring)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        (((continuous_polyEval _).mul (continuous_pow _)).intervalIntegrable 0 1)]
      norm_num [pr, polyEval]
    have hij_5 : (∫ u in (0 : ℝ)..1, polyEval upperUnitPolyList u * u ^ 10) = (18419096797 / 35678455312500 : ℝ) := by
      let pr : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1938762811 / 11264000000, 0, -10133087199 / 13312000000, 0, 1686012123 / 1280000000, 0, -195653861 / 256000000, 0, -9650701551 / 9728000000, 0, 8997987601 / 3584000000, 0, -15065579023 / 5888000000, 0, 1924814463 / 1280000000, 0, -4610909303 / 9216000000, 0, 2178873697 / 29696000000] : List ℝ)
      have hd : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt (polyEval pr) (polyEval upperUnitPolyList u * u ^ 10) u :=
        fun u _ => (hasDerivAt_polyEval pr u).congr_deriv
          (by dsimp [pr, upperUnitPolyList, polyDeriv, polyAdd, polyEval]; ring)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        (((continuous_polyEval _).mul (continuous_pow _)).intervalIntegrable 0 1)]
      norm_num [pr, polyEval]
    have hij_6 : (∫ u in (0 : ℝ)..1, polyEval upperUnitPolyList u * u ^ 12) = (2219663709173 / 8546611795312500 : ℝ) := by
      let pr : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1938762811 / 13312000000, 0, -3377695733 / 5120000000, 0, 5058036369 / 4352000000, 0, -3326115637 / 4864000000, 0, -3216900517 / 3584000000, 0, 26993962803 / 11776000000, 0, -15065579023 / 6400000000, 0, 641604821 / 460800000, 0, -13832727909 / 29696000000, 0, 2178873697 / 31744000000] : List ℝ)
      have hd : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt (polyEval pr) (polyEval upperUnitPolyList u * u ^ 12) u :=
        fun u _ => (hasDerivAt_polyEval pr u).congr_deriv
          (by dsimp [pr, upperUnitPolyList, polyDeriv, polyAdd, polyEval]; ring)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        (((continuous_polyEval _).mul (continuous_pow _)).intervalIntegrable 0 1)]
      norm_num [pr, polyEval]
    have hij_7 : (∫ u in (0 : ℝ)..1, polyEval upperUnitPolyList u * u ^ 14) = (282123195331 / 1972295029687500 : ℝ) := by
      let pr : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1938762811 / 15360000000, 0, -10133087199 / 17408000000, 0, 5058036369 / 4864000000, 0, -3326115637 / 5376000000, 0, -9650701551 / 11776000000, 0, 26993962803 / 12800000000, 0, -15065579023 / 6912000000, 0, 1924814463 / 1484800000, 0, -13832727909 / 31744000000, 0, 198079427 / 3072000000] : List ℝ)
      have hd : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt (polyEval pr) (polyEval upperUnitPolyList u * u ^ 14) u :=
        fun u _ => (hasDerivAt_polyEval pr u).congr_deriv
          (by dsimp [pr, upperUnitPolyList, polyDeriv, polyAdd, polyEval]; ring)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        (((continuous_polyEval _).mul (continuous_pow _)).intervalIntegrable 0 1)]
      norm_num [pr, polyEval]
    have hij_8 : (∫ u in (0 : ℝ)..1, polyEval upperUnitPolyList u * u ^ 16) = (55610762041 / 657431676562500 : ℝ) := by
      let pr : List ℝ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1938762811 / 17408000000, 0, -10133087199 / 19456000000, 0, 1686012123 / 1792000000, 0, -3326115637 / 5888000000, 0, -9650701551 / 12800000000, 0, 8997987601 / 4608000000, 0, -15065579023 / 7424000000, 0, 1924814463 / 1587200000, 0, -419173573 / 1024000000, 0, 311267671 / 5120000000] : List ℝ)
      have hd : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt (polyEval pr) (polyEval upperUnitPolyList u * u ^ 16) u :=
        fun u _ => (hasDerivAt_polyEval pr u).congr_deriv
          (by dsimp [pr, upperUnitPolyList, polyDeriv, polyAdd, polyEval]; ring)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        (((continuous_polyEval _).mul (continuous_pow _)).intervalIntegrable 0 1)]
      norm_num [pr, polyEval]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num only [Nat.reduceMul] at *
    rw [hij_0, hij_1, hij_2, hij_3, hij_4, hij_5, hij_6, hij_7, hij_8]
    norm_num [Nat.factorial]; dsimp [upperCoshPolyList, polyEval]; ring
  have herr : |P_true - polyEval upperCoshPolyList (A ^ 2)| ≤ 1 / 10 ^ 18 := by
    rw [← htay_int, ← intervalIntegral.integral_sub
      ((contDiff_upperUnitTest.continuous.mul (Real.continuous_cosh.comp ((continuous_const.mul continuous_id).div_const 2))).intervalIntegrable 0 1)
      ((contDiff_upperUnitTest.continuous.mul (continuous_finset_sum _ fun j _ => ((continuous_pow _).div_const _).comp ((continuous_const.mul continuous_id).div_const 2))).intervalIntegrable 0 1)]
    refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans ?_
    have hpt : ∀ u ∈ Ioc (0 : ℝ) 1,
        |upperUnitTest u * Real.cosh (A * u / 2) - upperUnitTest u * coshTay16 (A * u / 2)| ≤ 1 / 10 ^ 18 := by
      intro u hu
      rw [← mul_sub, abs_mul]
      have hGu := abs_upperUnitTest_le ⟨hu.1.le, hu.2⟩
      set z := A * u / 2
      have hz0 : 0 ≤ z := by dsimp [z]; positivity [hu.1]
      have hz_half : z ≤ 1 / 2 := by dsimp [z]; nlinarith [hu.2, hA_lt1]
      have hz1 : |z| ≤ 1 := by rw [abs_of_nonneg hz0]; linarith
      have hnz1 : |-z| ≤ 1 := by simpa only [abs_neg] using hz1
      have hp := Real.exp_bound hz1 (n := 18) (by norm_num)
      have hm := Real.exp_bound hnz1 (n := 18) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg, abs_of_nonneg hz0] at hp hm
      obtain ⟨hpl, hpu⟩ := abs_le.mp hp
      obtain ⟨hml, hmu⟩ := abs_le.mp hm
      have hc_err : |Real.cosh z - coshTay16 z| ≤ 4 * (1 / 2 : ℝ) ^ 18 / (18 * (18).factorial : ℝ) := by
        have hz18 : z ^ 18 ≤ (1 / 2 : ℝ) ^ 18 := pow_le_pow_left₀ hz0 hz_half 18
        dsimp [coshTay16]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
        rw [Real.cosh_eq, abs_le]; norm_num [Nat.factorial] at hz18 ⊢
        exact ⟨by linarith, by linarith⟩
      have hprod := mul_le_mul hGu hc_err (abs_nonneg _) (by norm_num)
      refine hprod.trans ?_; norm_num [Nat.factorial]
    have hint := intervalIntegral.integral_mono_on zero_le_one
      (((by fun_prop : Continuous _).abs).intervalIntegrable 0 1)
      (continuous_const.intervalIntegrable 0 1) fun u hu => hpt u (by
        by_cases h0 : u = 0; · subst h0; simp [coshTay16, Finset.sum_range_succ]; norm_num
        · exact ⟨lt_of_le_of_ne hu.1 (Ne.symm h0), hu.2⟩)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hint; linarith
  have habs_P : |P_true| ≤ |polyEval upperCoshPolyList (A ^ 2)| + 1 / 10 ^ 18 := by
    have htr := abs_add_le (polyEval upperCoshPolyList (A ^ 2)) (P_true - polyEval upperCoshPolyList (A ^ 2))
    rw [add_sub_cancel] at htr; linarith
  have hsq_P : P_true ^ 2 ≤ (|polyEval upperCoshPolyList (A ^ 2)| + 1 / 10 ^ 18) ^ 2 := by
    rw [← sq_abs P_true]; exact pow_le_pow_left₀ (abs_nonneg _) habs_P 2
  rw [hcp, show (4 * A * P_true) ^ 2 / 2 / (2 * A) = 4 * A * P_true ^ 2 by field_simp [hA_pos.ne']; ring]
  exact mul_le_mul_of_nonneg_left hsq_P (by positivity)

private theorem archLevyAntideriv_twoPrimeScale_le {s : ℝ} (hs0 : 1 - 1 / 10 ^ 20 ≤ s) (hs1 : s ≤ 1) :
    archLevyAntideriv (2 * (s * Real.log 2)) ≤ archLevyTwoLogTwoHi + (4 / 10 ^ 20 : ℝ) * logTwoHi := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  obtain ⟨_, hlev_u⟩ := archLevyAntideriv_two_mul_log_two_bounds
  set a := 2 * (s * Real.log 2)
  set b := 2 * Real.log 2
  have ha1 : 1 ≤ a := by
    have hc : (1 : ℝ) ≤ 2 * ((1 - 1 / 10 ^ 20 : ℝ) * logTwoLo) := by norm_num [logTwoLo]
    dsimp [a]; nlinarith [apertureLogTwo_pos]
  have ha_pos : 0 < a := by linarith
  have hab : a ≤ b := by dsimp [a, b]; nlinarith [apertureLogTwo_pos]
  have hb_pos : 0 < b := lt_of_lt_of_le ha_pos hab
  have hunion : archLevyAntideriv a = (∫ y in Ioc a b, archLevyDensity y) + archLevyAntideriv b := by
    rw [← WeilLevyCoshCrossover.integral_archLevyDensity_Ioi ha_pos,
      ← WeilLevyCoshCrossover.integral_archLevyDensity_Ioi hb_pos]
    have hi := WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi ha_pos
    rw [← setIntegral_union (Set.disjoint_left.mpr fun y hy hy' => not_lt_of_ge hy.2 hy')
      measurableSet_Ioi (hi.mono_set fun _ hy => hy.1) (hi.mono_set fun y (hy : b < y) => lt_of_le_of_lt hab hy),
      Ioc_union_Ioi_eq_Ioi hab]
  have hdens_le : ∀ y ∈ Ioc a b, archLevyDensity y ≤ 2 := fun y hy => by
    have h1y : 1 ≤ y := ha1.trans hy.1.le
    have hd := WeilLevyCoshCrossover.archLevyDensity_le_of_le one_pos h1y
    have hexp_y : Real.exp (-(1 / 2 : ℝ) * y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hexp2 : Real.exp (-2 * (1 : ℝ)) ≤ 1 / 2 := by
      rw [show (-2 * (1 : ℝ)) = -(2 : ℝ) by ring, Real.exp_neg]
      have he2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
      exact inv_anti₀ two_pos he2
    have hinv : (1 - Real.exp (-2 * (1 : ℝ)))⁻¹ ≤ 2 := by
      have hpos : (0 : ℝ) < 1 / 2 := by norm_num
      simpa using inv_anti₀ hpos (by linarith : (1 / 2 : ℝ) ≤ 1 - Real.exp (-2 * (1 : ℝ)))
    nlinarith [Real.exp_pos (-(1 / 2 : ℝ) * y)]
  have hint_le : (∫ y in Ioc a b, archLevyDensity y) ≤ 2 * (b - a) := by
    have hi1 := (WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi ha_pos).mono_set fun _ hy => hy.1
    have hi2 : IntegrableOn (fun _ : ℝ => (2 : ℝ)) (Ioc a b) := integrableOn_const (by simp)
    have hm := setIntegral_mono_on hi1 hi2 measurableSet_Ioc hdens_le
    rw [setIntegral_const, Real.volume_real_Ioc_of_le hab, smul_eq_mul] at hm
    linarith
  have hba : 2 * (b - a) ≤ (4 / 10 ^ 20 : ℝ) * logTwoHi := by
    have he : 2 * (b - a) = 4 * (1 - s) * Real.log 2 := by dsimp [a, b]; ring
    rw [he]; nlinarith [apertureLogTwo_pos]
  linarith

private theorem horner_step_pp {c x x_lo x_hi acc acc_lo acc_hi lo_next hi_next : ℝ}
    (hx0 : 0 ≤ x_lo) (hx : x_lo ≤ x ∧ x ≤ x_hi) (hacc : acc_lo ≤ acc ∧ acc ≤ acc_hi)
    (ha0 : 0 ≤ acc_lo) (ha1 : 0 ≤ acc_hi)
    (hlo : lo_next ≤ c + x_lo * acc_lo) (hhi : c + x_hi * acc_hi ≤ hi_next) :
    lo_next ≤ c + x * acc ∧ c + x * acc ≤ hi_next :=
  ⟨by nlinarith [hx0, hx.1, hacc.1, ha0], by nlinarith [hx0, hx.1, hx.2, hacc.2, ha1]⟩

private theorem horner_step_np {c x x_lo x_hi acc acc_lo acc_hi lo_next hi_next : ℝ}
    (hx0 : 0 ≤ x_lo) (hx : x_lo ≤ x ∧ x ≤ x_hi) (hacc : acc_lo ≤ acc ∧ acc ≤ acc_hi)
    (ha0 : acc_lo ≤ 0) (ha1 : 0 ≤ acc_hi)
    (hlo : lo_next ≤ c + x_hi * acc_lo) (hhi : c + x_hi * acc_hi ≤ hi_next) :
    lo_next ≤ c + x * acc ∧ c + x * acc ≤ hi_next :=
  ⟨by nlinarith [hx0, hx.1, hx.2, hacc.1, ha0], by nlinarith [hx0, hx.1, hx.2, hacc.2, ha1]⟩

private theorem horner_step_nn {c x x_lo x_hi acc acc_lo acc_hi lo_next hi_next : ℝ}
    (hx0 : 0 ≤ x_lo) (hx : x_lo ≤ x ∧ x ≤ x_hi) (hacc : acc_lo ≤ acc ∧ acc ≤ acc_hi)
    (ha0 : acc_lo ≤ 0) (ha1 : acc_hi ≤ 0)
    (hlo : lo_next ≤ c + x_hi * acc_lo) (hhi : c + x_lo * acc_hi ≤ hi_next) :
    lo_next ≤ c + x * acc ∧ c + x * acc ≤ hi_next :=
  ⟨by nlinarith [hx0, hx.1, hx.2, hacc.1, ha0], by nlinarith [hx0, hx.1, hacc.2, ha1]⟩

private theorem horner_ac_p2 {x : ℝ} (hx : (1 : ℝ) ≤ x ∧ x ≤ (1000000000000000000010001 / 1000000000000000000000000 : ℝ)) :
    (63953227262567843 / 1000000000000000000 : ℝ) ≤ polyEval upperAcList x ∧ polyEval upperAcList x ≤ (63953227262567883 / 1000000000000000000 : ℝ) := by
  have hx0 : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
  dsimp only [upperAcList, polyEval]
  have hs_0 : (0 : ℝ) ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ (0 : ℝ) := ⟨le_rfl, le_rfl⟩
  have hs_1 := horner_step_pp hx0 hx hs_0 (c := (-141088608501841 / 10463635046400000000000000 : ℝ))
    (lo_next := (-13483709 / 1000000000000000000 : ℝ)) (hi_next := (-3370927 / 250000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_2 := horner_step_nn hx0 hx hs_1 (c := (0 : ℝ))
    (lo_next := (-1348371 / 100000000000000000 : ℝ)) (hi_next := (-3370927 / 250000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_3 := horner_step_nn hx0 hx hs_2 (c := (17562953535127 / 23566745600000000000000 : ℝ))
    (lo_next := (731759347 / 1000000000000000000 : ℝ)) (hi_next := (14635187 / 20000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_4 := horner_step_pp hx0 hx hs_3 (c := (0 : ℝ))
    (lo_next := (731759347 / 1000000000000000000 : ℝ)) (hi_next := (731759351 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_5 := horner_step_pp hx0 hx hs_4 (c := (-6336345955862923 / 325221089280000000000000 : ℝ))
    (lo_next := (-1171964739 / 62500000000000000 : ℝ)) (hi_next := (-18751435819 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_6 := horner_step_nn hx0 hx hs_5 (c := (0 : ℝ))
    (lo_next := (-750057433 / 40000000000000000 : ℝ)) (hi_next := (-18751435819 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_7 := horner_step_nn hx0 hx hs_6 (c := (16195229654724461 / 50815795200000000000000 : ℝ))
    (lo_next := (149976601489 / 500000000000000000 : ℝ)) (hi_next := (59990640597 / 200000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_8 := horner_step_pp hx0 hx hs_7 (c := (0 : ℝ))
    (lo_next := (149976601489 / 500000000000000000 : ℝ)) (hi_next := (149976601493 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_9 := horner_step_pp hx0 hx hs_8 (c := (-1527653904135711397 / 423574241280000000000000 : ℝ))
    (lo_next := (-1653312828387 / 500000000000000000 : ℝ)) (hi_next := (-661325131353 / 200000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_10 := horner_step_nn hx0 hx hs_9 (c := (0 : ℝ))
    (lo_next := (-132265026271 / 40000000000000000 : ℝ)) (hi_next := (-661325131353 / 200000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_11 := horner_step_nn hx0 hx hs_10 (c := (175288131730815073 / 6085836800000000000000 : ℝ))
    (lo_next := (1593500539903 / 62500000000000000 : ℝ)) (hi_next := (25496008638459 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_12 := horner_step_pp hx0 hx hs_11 (c := (0 : ℝ))
    (lo_next := (1593500539903 / 62500000000000000 : ℝ)) (hi_next := (1274800431923 / 50000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_13 := horner_step_pp hx0 hx hs_12 (c := (-19846133129151735729 / 138452787200000000000000 : ℝ))
    (lo_next := (-5892311740577 / 50000000000000000 : ℝ)) (hi_next := (-117846234811527 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_14 := horner_step_nn hx0 hx hs_13 (c := (0 : ℝ))
    (lo_next := (-117846234811541 / 1000000000000000000 : ℝ)) (hi_next := (-117846234811527 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_15 := horner_step_nn hx0 hx hs_14 (c := (-653352416728657797 / 6922639360000000000000 : ℝ))
    (lo_next := (-212225326766529 / 1000000000000000000 : ℝ)) (hi_next := (-106112663383257 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_16 := horner_step_nn hx0 hx hs_15 (c := (0 : ℝ))
    (lo_next := (-21222532676653 / 100000000000000000 : ℝ)) (hi_next := (-106112663383257 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_17 := horner_step_nn hx0 hx hs_16 (c := (38354024591996450291 / 2483120640000000000000 : ℝ))
    (lo_next := (15233671249565923 / 1000000000000000000 : ℝ)) (hi_next := (761683562478297 / 50000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_18 := horner_step_pp hx0 hx hs_17 (c := (0 : ℝ))
    (lo_next := (15233671249565923 / 1000000000000000000 : ℝ)) (hi_next := (15233671249565941 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_19 := horner_step_pp hx0 hx hs_18 (c := (-793911803213484089 / 1460659200000000000 : ℝ))
    (lo_next := (-26414806450164081 / 50000000000000000 : ℝ)) (hi_next := (-528296129003281601 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_20 := horner_step_nn hx0 hx hs_19 (c := (1400553559032959 / 480000000000000 : ℝ))
    (lo_next := (298690473206089537 / 125000000000000000 : ℝ)) (hi_next := (597380946412179079 / 250000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_21 := horner_step_pp hx0 hx hs_20 (c := (-22351018842066239491 / 2722720000000000000 : ℝ))
    (lo_next := (-2909776738042245743 / 500000000000000000 : ℝ)) (hi_next := (-1163910695216898293 / 200000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_22 := horner_step_nn hx0 hx hs_21 (c := (597667008229663 / 40000000000000 : ℝ))
    (lo_next := (9122121729657083513 / 1000000000000000000 : ℝ)) (hi_next := (1824424345931416707 / 200000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_23 := horner_step_pp hx0 hx hs_22 (c := (-2288040970943921507 / 120120000000000000 : ℝ))
    (lo_next := (-4962919200705597051 / 500000000000000000 : ℝ)) (hi_next := (-4962919200705597039 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_24 := horner_step_nn hx0 hx hs_23 (c := (506025198368967 / 28000000000000 : ℝ))
    (lo_next := (1629298022353239751 / 200000000000000000 : ℝ)) (hi_next := (407324505588309939 / 50000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_25 := horner_step_pp hx0 hx hs_24 (c := (-52131905463531143 / 3753750000000000 : ℝ))
    (lo_next := (-5741463391672001179 / 1000000000000000000 : ℝ)) (hi_next := (-5741463391672001153 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_26 := horner_step_nn hx0 hx hs_25 (c := (1042428869593373167 / 116025000000000000 : ℝ))
    (lo_next := (162152803091846253 / 50000000000000000 : ℝ)) (hi_next := (101345501932403909 / 31250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_27 := horner_step_pp hx0 hx hs_26 (c := (-153835075690067 / 48125000000000 : ℝ))
    (lo_next := (46483060484883501 / 1000000000000000000 : ℝ)) (hi_next := (4648306048488353 / 100000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_28 := horner_step_pp hx0 hx hs_27 (c := (-73511039832564976371 / 46477681250000000000 : ℝ))
    (lo_next := (-1535158662069099899 / 1000000000000000000 : ℝ)) (hi_next := (-1535158662069099869 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_29 := horner_step_nn hx0 hx hs_28 (c := (-149543512701 / 1093750000000 : ℝ))
    (lo_next := (-1671884159395728471 / 1000000000000000000 : ℝ)) (hi_next := (-41797103984893211 / 25000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_30 := horner_step_nn hx0 hx hs_29 (c := (318039004990404130451 / 67392637812500000000 : ℝ))
    (lo_next := (1523655461766926091 / 500000000000000000 : ℝ)) (hi_next := (1523655461766926107 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_31 := horner_step_pp hx0 hx hs_30 (c := (779917329 / 136718750000 : ℝ))
    (lo_next := (3053015461711680753 / 1000000000000000000 : ℝ)) (hi_next := (1526507730855840393 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_32 := horner_step_pp hx0 hx hs_31 (c := (-19089405752363054249371 / 2611464715234375000000 : ℝ))
    (lo_next := (-4256830863609934407 / 1000000000000000000 : ℝ)) (hi_next := (-4256830863609934373 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_33 := horner_step_nn hx0 hx hs_32 (c := (0 : ℝ))
    (lo_next := (-532103857951241801 / 125000000000000000 : ℝ)) (hi_next := (-4256830863609934373 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_34 := horner_step_nn hx0 hx hs_33 (c := (3200849337069904792453 / 391719707285156250000 : ℝ))
    (lo_next := (61163185080782387 / 15625000000000000 : ℝ)) (hi_next := (978610961292518201 / 250000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_35 := horner_step_pp hx0 hx hs_34 (c := (0 : ℝ))
    (lo_next := (61163185080782387 / 15625000000000000 : ℝ)) (hi_next := (782888769034014561 / 200000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_36 := horner_step_pp hx0 hx hs_35 (c := (-165426213857465883643 / 28802919653320312500 : ℝ))
    (lo_next := (-1828939667632805727 / 1000000000000000000 : ℝ)) (hi_next := (-1828939667632805689 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_37 := horner_step_nn hx0 hx hs_36 (c := (0 : ℝ))
    (lo_next := (-57154364613525179 / 31250000000000000 : ℝ)) (hi_next := (-1828939667632805689 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_38 := horner_step_nn hx0 hx hs_37 (c := (8573402398840939849351 / 4529259115484619140625 : ℝ))
    (lo_next := (63953227262567843 / 1000000000000000000 : ℝ)) (hi_next := (63953227262567883 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact hs_38

private theorem horner_ac_p3 {x : ℝ} (hx : (792481250360578090726869 / 500000000000000000000000 : ℝ) ≤ x ∧ x ≤ (1584962500721156181469591 / 1000000000000000000000000 : ℝ)) :
    (5337678228563 / 125000000000000000 : ℝ) ≤ polyEval upperAcList x ∧ polyEval upperAcList x ≤ (5337687103009 / 125000000000000000 : ℝ) := by
  have hx0 : (0 : ℝ) ≤ (792481250360578090726869 / 500000000000000000000000 : ℝ) := by norm_num
  dsimp only [upperAcList, polyEval]
  have hs_0 : (0 : ℝ) ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ (0 : ℝ) := ⟨le_rfl, le_rfl⟩
  have hs_1 := horner_step_pp hx0 hx hs_0 (c := (-141088608501841 / 10463635046400000000000000 : ℝ))
    (lo_next := (-13483709 / 1000000000000000000 : ℝ)) (hi_next := (-3370927 / 250000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_2 := horner_step_nn hx0 hx hs_1 (c := (0 : ℝ))
    (lo_next := (-10685587 / 500000000000000000 : ℝ)) (hi_next := (-21371171 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_3 := horner_step_nn hx0 hx hs_2 (c := (17562953535127 / 23566745600000000000000 : ℝ))
    (lo_next := (711370547 / 1000000000000000000 : ℝ)) (hi_next := (711370553 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_4 := horner_step_pp hx0 hx hs_3 (c := (0 : ℝ))
    (lo_next := (1127495641 / 1000000000000000000 : ℝ)) (hi_next := (1127495651 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_5 := horner_step_pp hx0 hx hs_4 (c := (-6336345955862923 / 325221089280000000000000 : ℝ))
    (lo_next := (-884807843 / 50000000000000000 : ℝ)) (hi_next := (-17696156843 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_6 := horner_step_nn hx0 hx hs_5 (c := (0 : ℝ))
    (lo_next := (-2804774503 / 100000000000000000 : ℝ)) (hi_next := (-28047745003 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_7 := horner_step_nn hx0 hx hs_6 (c := (16195229654724461 / 50815795200000000000000 : ℝ))
    (lo_next := (274250014701 / 1000000000000000000 : ℝ)) (hi_next := (34281251843 / 125000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_8 := horner_step_pp hx0 hx hs_7 (c := (0 : ℝ))
    (lo_next := (434675989123 / 1000000000000000000 : ℝ)) (hi_next := (54334498649 / 125000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_9 := horner_step_pp hx0 hx hs_8 (c := (-1527653904135711397 / 423574241280000000000000 : ℝ))
    (lo_next := (-729408429257 / 250000000000000000 : ℝ)) (hi_next := (-1458816858459 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_10 := horner_step_nn hx0 hx hs_9 (c := (0 : ℝ))
    (lo_next := (-462434003233 / 100000000000000000 : ℝ)) (hi_next := (-2312170016077 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_11 := horner_step_nn hx0 hx hs_10 (c := (175288131730815073 / 6085836800000000000000 : ℝ))
    (lo_next := (21473228753397 / 1000000000000000000 : ℝ)) (hi_next := (21473228753677 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_12 := horner_step_pp hx0 hx hs_11 (c := (0 : ℝ))
    (lo_next := (34034262343541 / 1000000000000000000 : ℝ)) (hi_next := (17017131171993 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_13 := horner_step_pp hx0 hx hs_12 (c := (-19846133129151735729 / 138452787200000000000000 : ℝ))
    (lo_next := (-8939921389577 / 100000000000000000 : ℝ)) (hi_next := (-89399213895063 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_14 := horner_step_nn hx0 hx hs_13 (c := (0 : ℝ))
    (lo_next := (-70847200809373 / 500000000000000000 : ℝ)) (hi_next := (-17711800202203 / 125000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_15 := horner_step_nn hx0 hx hs_14 (c := (-653352416728657797 / 6922639360000000000000 : ℝ))
    (lo_next := (-39869925635353 / 125000000000000000 : ℝ)) (hi_next := (-79739851270261 / 250000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_16 := horner_step_nn hx0 hx hs_15 (c := (0 : ℝ))
    (lo_next := (-101107739261721 / 200000000000000000 : ℝ)) (hi_next := (-505538696305783 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_17 := horner_step_nn hx0 hx hs_16 (c := (38354024591996450291 / 2483120640000000000000 : ℝ))
    (lo_next := (14644636700019853 / 1000000000000000000 : ℝ)) (hi_next := (14644636700024327 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_18 := horner_step_pp hx0 hx hs_17 (c := (0 : ℝ))
    (lo_next := (11605600003108143 / 500000000000000000 : ℝ)) (hi_next := (11605600003111689 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_19 := horner_step_pp hx0 hx hs_18 (c := (-793911803213484089 / 1460659200000000000 : ℝ))
    (lo_next := (-253370459323128031 / 500000000000000000 : ℝ)) (hi_next := (-506740918646244821 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_20 := horner_step_nn hx0 hx hs_19 (c := (1400553559032959 / 480000000000000 : ℝ))
    (lo_next := (2114654561016691947 / 1000000000000000000 : ℝ)) (hi_next := (528663640254177441 / 250000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_21 := horner_step_pp hx0 hx hs_20 (c := (-22351018842066239491 / 2722720000000000000 : ℝ))
    (lo_next := (-1214357270135698241 / 250000000000000000 : ℝ)) (hi_next := (-4857429080542764723 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_22 := horner_step_nn hx0 hx hs_21 (c := (597667008229663 / 40000000000000 : ℝ))
    (lo_next := (7242832263168803499 / 1000000000000000000 : ℝ)) (hi_next := (7242832263168848261 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_23 := horner_step_pp hx0 hx hs_22 (c := (-2288040970943921507 / 120120000000000000 : ℝ))
    (lo_next := (-7568342594932379641 / 1000000000000000000 : ℝ)) (hi_next := (-3784171297466154347 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_24 := horner_step_nn hx0 hx hs_23 (c := (506025198368967 / 28000000000000 : ℝ))
    (lo_next := (1519197326899731011 / 250000000000000000 : ℝ)) (hi_next := (3038394653799518247 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_25 := horner_step_pp hx0 hx hs_24 (c := (-52131905463531143 / 3753750000000000 : ℝ))
    (lo_next := (-4256470326110626111 / 1000000000000000000 : ℝ)) (hi_next := (-4256470326110447881 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_26 := horner_step_nn hx0 hx hs_25 (c := (1042428869593373167 / 116025000000000000 : ℝ))
    (lo_next := (447634720238246623 / 200000000000000000 : ℝ)) (hi_next := (559543400297878901 / 250000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_27 := horner_step_pp hx0 hx hs_26 (c := (-153835075690067 / 48125000000000 : ℝ))
    (lo_next := (70169645328018197 / 200000000000000000 : ℝ)) (hi_next := (2192801416503367 / 6250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_28 := horner_step_pp hx0 hx hs_27 (c := (-73511039832564976371 / 46477681250000000000 : ℝ))
    (lo_next := (-41022417595396873 / 40000000000000000 : ℝ)) (hi_next := (-1025560439884212181 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_29 := horner_step_nn hx0 hx hs_28 (c := (-149543512701 / 1093750000000 : ℝ))
    (lo_next := (-1762200336767323231 / 1000000000000000000 : ℝ)) (hi_next := (-1762200336766198471 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_30 := horner_step_nn hx0 hx hs_29 (c := (318039004990404130451 / 67392637812500000000 : ℝ))
    (lo_next := (1926173630395180441 / 1000000000000000000 : ℝ)) (hi_next := (240771703799620393 / 125000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_31 := horner_step_pp hx0 hx hs_30 (c := (779917329 / 136718750000 : ℝ))
    (lo_next := (3058617512232121771 / 1000000000000000000 : ℝ)) (hi_next := (3058617512234947289 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_32 := horner_step_pp hx0 hx hs_31 (c := (-19089405752363054249371 / 2611464715234375000000 : ℝ))
    (lo_next := (-615513066096167483 / 250000000000000000 : ℝ)) (hi_next := (-2462052264380191591 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_33 := horner_step_nn hx0 hx hs_32 (c := (0 : ℝ))
    (lo_next := (-3902260513865311627 / 1000000000000000000 : ℝ)) (hi_next := (-487782564232276703 / 125000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_34 := horner_step_nn hx0 hx hs_33 (c := (3200849337069904792453 / 391719707285156250000 : ℝ))
    (lo_next := (397267625251723781 / 200000000000000000 : ℝ)) (hi_next := (79453525050794759 / 40000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_35 := horner_step_pp hx0 hx hs_34 (c := (0 : ℝ))
    (lo_next := (787067860968159071 / 250000000000000000 : ℝ)) (hi_next := (393533930486308403 / 125000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_36 := horner_step_pp hx0 hx hs_35 (c := (-165426213857465883643 / 28802919653320312500 : ℝ))
    (lo_next := (-188372833043374949 / 250000000000000000 : ℝ)) (hi_next := (-94186416518154803 / 125000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_37 := horner_step_nn hx0 hx hs_36 (c := (0 : ℝ))
    (lo_next := (-1194255506113425603 / 1000000000000000000 : ℝ)) (hi_next := (-1194255506068632387 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_38 := horner_step_nn hx0 hx hs_37 (c := (8573402398840939849351 / 4529259115484619140625 : ℝ))
    (lo_next := (5337678228563 / 125000000000000000 : ℝ)) (hi_next := (5337687103009 / 125000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact hs_38

private theorem horner_ac_p3_one {x : ℝ} (hx : (792481250360578090726869 / 500000000000000000000000 : ℝ) ≤ x ∧ x ≤ (1584962500721156181453739 / 1000000000000000000000000 : ℝ)) :
    (42701425828511 / 1000000000000000000 : ℝ) ≤ polyEval upperAcList x ∧ polyEval upperAcList x ≤ (5337687103009 / 125000000000000000 : ℝ) := by
  have hx0 : (0 : ℝ) ≤ (792481250360578090726869 / 500000000000000000000000 : ℝ) := by norm_num
  dsimp only [upperAcList, polyEval]
  have hs_0 : (0 : ℝ) ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ (0 : ℝ) := ⟨le_rfl, le_rfl⟩
  have hs_1 := horner_step_pp hx0 hx hs_0 (c := (-141088608501841 / 10463635046400000000000000 : ℝ))
    (lo_next := (-13483709 / 1000000000000000000 : ℝ)) (hi_next := (-3370927 / 250000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_2 := horner_step_nn hx0 hx hs_1 (c := (0 : ℝ))
    (lo_next := (-10685587 / 500000000000000000 : ℝ)) (hi_next := (-21371171 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_3 := horner_step_nn hx0 hx hs_2 (c := (17562953535127 / 23566745600000000000000 : ℝ))
    (lo_next := (711370547 / 1000000000000000000 : ℝ)) (hi_next := (711370553 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_4 := horner_step_pp hx0 hx hs_3 (c := (0 : ℝ))
    (lo_next := (1127495641 / 1000000000000000000 : ℝ)) (hi_next := (1127495651 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_5 := horner_step_pp hx0 hx hs_4 (c := (-6336345955862923 / 325221089280000000000000 : ℝ))
    (lo_next := (-884807843 / 50000000000000000 : ℝ)) (hi_next := (-17696156843 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_6 := horner_step_nn hx0 hx hs_5 (c := (0 : ℝ))
    (lo_next := (-2804774503 / 100000000000000000 : ℝ)) (hi_next := (-28047745003 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_7 := horner_step_nn hx0 hx hs_6 (c := (16195229654724461 / 50815795200000000000000 : ℝ))
    (lo_next := (274250014701 / 1000000000000000000 : ℝ)) (hi_next := (34281251843 / 125000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_8 := horner_step_pp hx0 hx hs_7 (c := (0 : ℝ))
    (lo_next := (434675989123 / 1000000000000000000 : ℝ)) (hi_next := (54334498649 / 125000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_9 := horner_step_pp hx0 hx hs_8 (c := (-1527653904135711397 / 423574241280000000000000 : ℝ))
    (lo_next := (-729408429257 / 250000000000000000 : ℝ)) (hi_next := (-1458816858459 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_10 := horner_step_nn hx0 hx hs_9 (c := (0 : ℝ))
    (lo_next := (-462434003233 / 100000000000000000 : ℝ)) (hi_next := (-2312170016077 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_11 := horner_step_nn hx0 hx hs_10 (c := (175288131730815073 / 6085836800000000000000 : ℝ))
    (lo_next := (21473228753397 / 1000000000000000000 : ℝ)) (hi_next := (21473228753677 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_12 := horner_step_pp hx0 hx hs_11 (c := (0 : ℝ))
    (lo_next := (34034262343541 / 1000000000000000000 : ℝ)) (hi_next := (17017131171993 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_13 := horner_step_pp hx0 hx hs_12 (c := (-19846133129151735729 / 138452787200000000000000 : ℝ))
    (lo_next := (-8939921389577 / 100000000000000000 : ℝ)) (hi_next := (-89399213895063 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_14 := horner_step_nn hx0 hx hs_13 (c := (0 : ℝ))
    (lo_next := (-70847200809373 / 500000000000000000 : ℝ)) (hi_next := (-17711800202203 / 125000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_15 := horner_step_nn hx0 hx hs_14 (c := (-653352416728657797 / 6922639360000000000000 : ℝ))
    (lo_next := (-39869925635353 / 125000000000000000 : ℝ)) (hi_next := (-79739851270261 / 250000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_16 := horner_step_nn hx0 hx hs_15 (c := (0 : ℝ))
    (lo_next := (-101107739261721 / 200000000000000000 : ℝ)) (hi_next := (-505538696305783 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_17 := horner_step_nn hx0 hx hs_16 (c := (38354024591996450291 / 2483120640000000000000 : ℝ))
    (lo_next := (14644636700019853 / 1000000000000000000 : ℝ)) (hi_next := (14644636700024327 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_18 := horner_step_pp hx0 hx hs_17 (c := (0 : ℝ))
    (lo_next := (11605600003108143 / 500000000000000000 : ℝ)) (hi_next := (11605600003111689 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_19 := horner_step_pp hx0 hx hs_18 (c := (-793911803213484089 / 1460659200000000000 : ℝ))
    (lo_next := (-253370459323128031 / 500000000000000000 : ℝ)) (hi_next := (-506740918646244821 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_20 := horner_step_nn hx0 hx hs_19 (c := (1400553559032959 / 480000000000000 : ℝ))
    (lo_next := (2114654561016691947 / 1000000000000000000 : ℝ)) (hi_next := (528663640254177441 / 250000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_21 := horner_step_pp hx0 hx hs_20 (c := (-22351018842066239491 / 2722720000000000000 : ℝ))
    (lo_next := (-1214357270135698241 / 250000000000000000 : ℝ)) (hi_next := (-4857429080542764723 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_22 := horner_step_nn hx0 hx hs_21 (c := (597667008229663 / 40000000000000 : ℝ))
    (lo_next := (7242832263168803499 / 1000000000000000000 : ℝ)) (hi_next := (7242832263168848261 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_23 := horner_step_pp hx0 hx hs_22 (c := (-2288040970943921507 / 120120000000000000 : ℝ))
    (lo_next := (-7568342594932379641 / 1000000000000000000 : ℝ)) (hi_next := (-3784171297466154347 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_24 := horner_step_nn hx0 hx hs_23 (c := (506025198368967 / 28000000000000 : ℝ))
    (lo_next := (1519197326899731011 / 250000000000000000 : ℝ)) (hi_next := (3038394653799518247 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_25 := horner_step_pp hx0 hx hs_24 (c := (-52131905463531143 / 3753750000000000 : ℝ))
    (lo_next := (-4256470326110626111 / 1000000000000000000 : ℝ)) (hi_next := (-4256470326110447881 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_26 := horner_step_nn hx0 hx hs_25 (c := (1042428869593373167 / 116025000000000000 : ℝ))
    (lo_next := (447634720238246623 / 200000000000000000 : ℝ)) (hi_next := (559543400297878901 / 250000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_27 := horner_step_pp hx0 hx hs_26 (c := (-153835075690067 / 48125000000000 : ℝ))
    (lo_next := (70169645328018197 / 200000000000000000 : ℝ)) (hi_next := (2192801416503367 / 6250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_28 := horner_step_pp hx0 hx hs_27 (c := (-73511039832564976371 / 46477681250000000000 : ℝ))
    (lo_next := (-41022417595396873 / 40000000000000000 : ℝ)) (hi_next := (-1025560439884212181 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_29 := horner_step_nn hx0 hx hs_28 (c := (-149543512701 / 1093750000000 : ℝ))
    (lo_next := (-1762200336767323231 / 1000000000000000000 : ℝ)) (hi_next := (-1762200336766198471 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_30 := horner_step_nn hx0 hx hs_29 (c := (318039004990404130451 / 67392637812500000000 : ℝ))
    (lo_next := (1926173630395180441 / 1000000000000000000 : ℝ)) (hi_next := (240771703799620393 / 125000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_31 := horner_step_pp hx0 hx hs_30 (c := (779917329 / 136718750000 : ℝ))
    (lo_next := (3058617512232121771 / 1000000000000000000 : ℝ)) (hi_next := (3058617512234947289 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_32 := horner_step_pp hx0 hx hs_31 (c := (-19089405752363054249371 / 2611464715234375000000 : ℝ))
    (lo_next := (-615513066096167483 / 250000000000000000 : ℝ)) (hi_next := (-2462052264380191591 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_33 := horner_step_nn hx0 hx hs_32 (c := (0 : ℝ))
    (lo_next := (-3902260513865311627 / 1000000000000000000 : ℝ)) (hi_next := (-487782564232276703 / 125000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_34 := horner_step_nn hx0 hx hs_33 (c := (3200849337069904792453 / 391719707285156250000 : ℝ))
    (lo_next := (993169063129309453 / 500000000000000000 : ℝ)) (hi_next := (79453525050794759 / 40000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_35 := horner_step_pp hx0 hx hs_34 (c := (0 : ℝ))
    (lo_next := (1574135721936318143 / 500000000000000000 : ℝ)) (hi_next := (393533930486308403 / 125000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_36 := horner_step_pp hx0 hx hs_35 (c := (-165426213857465883643 / 28802919653320312500 : ℝ))
    (lo_next := (-753491332173499793 / 1000000000000000000 : ℝ)) (hi_next := (-94186416518154803 / 125000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_37 := horner_step_nn hx0 hx hs_36 (c := (0 : ℝ))
    (lo_next := (-597127753056712799 / 500000000000000000 : ℝ)) (hi_next := (-1194255506068632387 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_38 := horner_step_nn hx0 hx hs_37 (c := (8573402398840939849351 / 4529259115484619140625 : ℝ))
    (lo_next := (42701425828511 / 1000000000000000000 : ℝ)) (hi_next := (5337687103009 / 125000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact hs_38

private theorem horner_kup_mom {x : ℝ} (hx : (6931471805599453094103 / 10000000000000000000000 : ℝ) ≤ x ∧ x ≤ (69314718055994530941723213 / 100000000000000000000000000 : ℝ)) :
    (596702535507933593 / 1000000000000000000 : ℝ) ≤ polyEval upperKupMomList x ∧ polyEval upperKupMomList x ≤ (149175633876983399 / 250000000000000000 : ℝ) := by
  have hx0 : (0 : ℝ) ≤ (6931471805599453094103 / 10000000000000000000000 : ℝ) := by norm_num
  dsimp only [upperKupMomList, polyEval]
  have hs_0 : (0 : ℝ) ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ (0 : ℝ) := ⟨le_rfl, le_rfl⟩
  have hs_1 := horner_step_pp hx0 hx hs_0 (c := (-494150202771706275893946755455052402653213357129433209 / 1391020443444914633142134931372921392256000000000000000000000 : ℝ))
    (lo_next := (-71048589559 / 200000000000000000 : ℝ)) (hi_next := (-177621473897 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_2 := horner_step_nn hx0 hx hs_1 (c := (0 : ℝ))
    (lo_next := (-123117823839 / 500000000000000000 : ℝ)) (hi_next := (-246235647677 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_3 := horner_step_nn hx0 hx hs_2 (c := (107885937380506691108343415907851008487820401186253 / 113966171970907889834130308442023600640000000000000000000 : ℝ))
    (lo_next := (775971232627 / 1000000000000000000 : ℝ)) (hi_next := (775971232629 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_4 := horner_step_pp hx0 hx hs_3 (c := (0 : ℝ))
    (lo_next := (537862272091 / 1000000000000000000 : ℝ)) (hi_next := (537862272093 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_5 := horner_step_pp hx0 hx hs_4 (c := (-2107096112633069880193307415812673811154649947 / 829934318045126518997409528091200000000000000000000 : ℝ))
    (lo_next := (-541513302763 / 250000000000000000 : ℝ)) (hi_next := (-2166053211049 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_6 := horner_step_nn hx0 hx hs_5 (c := (0 : ℝ))
    (lo_next := (-187674209523 / 125000000000000000 : ℝ)) (hi_next := (-1501393676181 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_7 := horner_step_nn hx0 hx hs_6 (c := (60996926452921691557148872985177257956743 / 8890360996135199270511024403200000000000000000 : ℝ))
    (lo_next := (2910165582521 / 500000000000000000 : ℝ)) (hi_next := (1164066233009 / 200000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_8 := horner_step_pp hx0 hx hs_7 (c := (0 : ℝ))
    (lo_next := (2017173068487 / 500000000000000000 : ℝ)) (hi_next := (4034346136977 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_9 := horner_step_pp hx0 hx hs_8 (c := (-3983383799671154115377865116389776387391 / 212891786305919522761279320000000000000000000 : ℝ))
    (lo_next := (-3978610675007 / 250000000000000000 : ℝ)) (hi_next := (-636577708001 / 40000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_10 := horner_step_nn hx0 hx hs_9 (c := (0 : ℝ))
    (lo_next := (-2757762771927 / 250000000000000000 : ℝ)) (hi_next := (-2206210217541 / 200000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_11 := horner_step_nn hx0 hx hs_10 (c := (2349704707665429699560847666463362803 / 45538350011961395243054400000000000000000 : ℝ))
    (lo_next := (1373507177413 / 31250000000000000 : ℝ)) (hi_next := (43952229677219 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_12 := horner_step_pp hx0 hx hs_11 (c := (0 : ℝ))
    (lo_next := (6093072816017 / 200000000000000000 : ℝ)) (hi_next := (3808170510011 / 125000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_13 := horner_step_pp hx0 hx hs_12 (c := (-7528840953000268914841372148049795787 / 52179359388705765382666500000000000000000 : ℝ))
    (lo_next := (-61585370883963 / 500000000000000000 : ℝ)) (hi_next := (-123170741767923 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_14 := horner_step_nn hx0 hx hs_13 (c := (-56165415154428715603597052684819293 / 3789716701483201770360150946875000000000000 : ℝ))
    (lo_next := (-21347568215621 / 250000000000000000 : ℝ)) (hi_next := (-85390272862481 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_15 := horner_step_nn hx0 hx hs_14 (c := (44490798018628717734443072707818001 / 108308804591941149145950000000000000000 : ℝ))
    (lo_next := (351589270367873 / 1000000000000000000 : ℝ)) (hi_next := (87897317591969 / 250000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_16 := horner_step_pp hx0 hx hs_15 (c := (605488973918015134353377571679416553 / 3548898583328750821741947375000000000000000 : ℝ))
    (lo_next := (30484215584889 / 125000000000000000 : ℝ)) (hi_next := (48774744935823 / 200000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_17 := horner_step_pp hx0 hx hs_16 (c := (-192957098232568491448164435624109 / 161100052596708803077500000000000000 : ℝ))
    (lo_next := (-205741315039159 / 200000000000000000 : ℝ)) (hi_next := (-64294160949737 / 62500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_18 := horner_step_nn hx0 hx hs_17 (c := (-287167107225422448181101876523 / 142234649035878248561250000000000000 : ℝ))
    (lo_next := (-357532014766883 / 500000000000000000 : ℝ)) (hi_next := (-715064029533763 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_19 := horner_step_nn hx0 hx hs_18 (c := (368441215333353740214678841192051 / 102030033311248908615750000000000000 : ℝ))
    (lo_next := (3115460892613357 / 1000000000000000000 : ℝ)) (hi_next := (3115460892613361 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_20 := horner_step_pp hx0 hx hs_19 (c := (3625846589030516350773142984097 / 146040411727682856759375000000000000 : ℝ))
    (lo_next := (8532424325839 / 3906250000000000 : ℝ)) (hi_next := (546075156853697 / 250000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_21 := horner_step_pp hx0 hx hs_20 (c := (-609548698027963811009158613233 / 53273826916901059218750000000000 : ℝ))
    (lo_next := (-1240970300752429 / 125000000000000000 : ℝ)) (hi_next := (-2481940601504857 / 250000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_22 := horner_step_nn hx0 hx hs_21 (c := (-262078162244460044065946747 / 812238107495455265625000000000 : ℝ))
    (lo_next := (-1440812452492229 / 200000000000000000 : ℝ)) (hi_next := (-7204062262461141 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_23 := horner_step_nn hx0 hx hs_22 (c := (41810139369292148831766899371 / 1065476538338021184375000000000 : ℝ))
    (lo_next := (6849462587686841 / 200000000000000000 : ℝ)) (hi_next := (34247312938434209 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_24 := horner_step_pp hx0 hx hs_23 (c := (145973452084616473861364291 / 32088894981385429687500000000 : ℝ))
    (lo_next := (88398317852963 / 3125000000000000 : ℝ)) (hi_next := (7071865428237041 / 250000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_25 := horner_step_pp hx0 hx hs_24 (c := (-800862363486925844515213463 / 5222924207539319531250000000 : ℝ))
    (lo_next := (-6686431831006501 / 50000000000000000 : ℝ)) (hi_next := (-4179019894379063 / 31250000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_26 := horner_step_nn hx0 hx hs_25 (c := (-2214956280682876247830331 / 30436621256056640625000000 : ℝ))
    (lo_next := (-82733182986271299 / 500000000000000000 : ℝ)) (hi_next := (-82733182986271297 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_27 := horner_step_nn hx0 hx hs_26 (c := (8600839322633241943493645420491049 / 12090102332266943359375000000000000 : ℝ))
    (lo_next := (596702535507933593 / 1000000000000000000 : ℝ)) (hi_next := (149175633876983399 / 250000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact hs_27

private theorem horner_k14_mom {x : ℝ} (hx : (17328679513998632735430803 / 25000000000000000000000000 : ℝ) ≤ x ∧ x ≤ (69314718055994530941723213 / 100000000000000000000000000 : ℝ)) :
    (596702410146374101 / 1000000000000000000 : ℝ) ≤ polyEval upperK14MomList x ∧ polyEval upperK14MomList x ≤ (74587801268296763 / 125000000000000000 : ℝ) := by
  have hx0 : (0 : ℝ) ≤ (17328679513998632735430803 / 25000000000000000000000000 : ℝ) := by norm_num
  dsimp only [upperK14MomList, polyEval]
  have hs_0 : (0 : ℝ) ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ (0 : ℝ) := ⟨le_rfl, le_rfl⟩
  have hs_1 := horner_step_pp hx0 hx hs_0 (c := (-7528840953000268914841372148049795787 / 52179359388705765382666500000000000000000 : ℝ))
    (lo_next := (-144287722984769 / 1000000000000000000 : ℝ)) (hi_next := (-2254495671637 / 15625000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_2 := horner_step_nn hx0 hx hs_1 (c := (-56165415154428715603597052684819293 / 3789716701483201770360150946875000000000000 : ℝ))
    (lo_next := (-25006862213719 / 250000000000000000 : ℝ)) (hi_next := (-50013724427437 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_3 := horner_step_nn hx0 hx hs_2 (c := (44490798018628717734443072707818001 / 108308804591941149145950000000000000000 : ℝ))
    (lo_next := (170721776548693 / 500000000000000000 : ℝ)) (hi_next := (341443553097389 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_4 := horner_step_pp hx0 hx hs_3 (c := (605488973918015134353377571679416553 / 3548898583328750821741947375000000000000000 : ℝ))
    (lo_next := (59210312339579 / 250000000000000000 : ℝ)) (hi_next := (236841249358319 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_5 := horner_step_pp hx0 hx hs_4 (c := (-192957098232568491448164435624109 / 161100052596708803077500000000000000 : ℝ))
    (lo_next := (-516790557818381 / 500000000000000000 : ℝ)) (hi_next := (-1033581115636759 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_6 := horner_step_nn hx0 hx hs_5 (c := (-287167107225422448181101876523 / 142234649035878248561250000000000000 : ℝ))
    (lo_next := (-179610700874237 / 250000000000000000 : ℝ)) (hi_next := (-143688560699389 / 200000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_7 := horner_step_nn hx0 hx hs_6 (c := (368441215333353740214678841192051 / 102030033311248908615750000000000000 : ℝ))
    (lo_next := (778279726241757 / 250000000000000000 : ℝ)) (hi_next := (389139863120879 / 125000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_8 := horner_step_pp hx0 hx hs_7 (c := (3625846589030516350773142984097 / 146040411727682856759375000000000000 : ℝ))
    (lo_next := (87307091411233 / 40000000000000000 : ℝ)) (hi_next := (2182677285280829 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_9 := horner_step_pp hx0 hx hs_8 (c := (-609548698027963811009158613233 / 53273826916901059218750000000000 : ℝ))
    (lo_next := (-992888762104267 / 100000000000000000 : ℝ)) (hi_next := (-4964443810521333 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_10 := horner_step_nn hx0 hx hs_9 (c := (-262078162244460044065946747 / 812238107495455265625000000000 : ℝ))
    (lo_next := (-3602421101041013 / 500000000000000000 : ℝ)) (hi_next := (-3602421101041011 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_11 := horner_step_nn hx0 hx hs_10 (c := (41810139369292148831766899371 / 1065476538338021184375000000000 : ℝ))
    (lo_next := (6849354465096997 / 200000000000000000 : ℝ)) (hi_next := (8561693081371247 / 250000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_12 := horner_step_pp hx0 hx hs_11 (c := (145973452084616473861364291 / 32088894981385429687500000000 : ℝ))
    (lo_next := (14143543494303317 / 500000000000000000 : ℝ)) (hi_next := (28287086988606637 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_13 := horner_step_pp hx0 hx hs_12 (c := (-800862363486925844515213463 / 5222924207539319531250000000 : ℝ))
    (lo_next := (-33432224089812709 / 250000000000000000 : ℝ)) (hi_next := (-133728896359250833 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_14 := horner_step_nn hx0 hx hs_13 (c := (-2214956280682876247830331 / 30436621256056640625000000 : ℝ))
    (lo_next := (-10341659125623867 / 62500000000000000 : ℝ)) (hi_next := (-165466546009981869 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_15 := horner_step_nn hx0 hx hs_14 (c := (61926043073418507534419441 / 87048736792321992187500000 : ℝ))
    (lo_next := (596702410146374101 / 1000000000000000000 : ℝ)) (hi_next := (74587801268296763 / 125000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact hs_15

private theorem horner_pcosh {x : ℝ} (hx : (0 : ℝ) ≤ x ∧ x ≤ (480453013918201424667103 / 1000000000000000000000000 : ℝ)) :
    (685640383083583083 / 1000000000000000000 : ℝ) ≤ polyEval upperCoshPolyList x ∧ polyEval upperCoshPolyList x ≤ (688733324552902361 / 1000000000000000000 : ℝ) := by
  have hx0 : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
  dsimp only [upperCoshPolyList, polyEval]
  have hs_0 : (0 : ℝ) ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ (0 : ℝ) := ⟨le_rfl, le_rfl⟩
  have hs_1 := horner_step_pp hx0 hx hs_0 (c := (55610762041 / 901467657629385464217600000000000 : ℝ))
    (lo_next := (0 : ℝ)) (hi_next := (1 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_2 := horner_step_pp hx0 hx hs_1 (c := (282123195331 / 2817086430091829575680000000000 : ℝ))
    (lo_next := (0 : ℝ)) (hi_next := (1 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_3 := horner_step_pp hx0 hx hs_2 (c := (2219663709173 / 16768371607689461760000000000 : ℝ))
    (lo_next := (33 / 250000000000000000 : ℝ)) (hi_next := (133 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_4 := horner_step_pp hx0 hx hs_3 (c := (18419096797 / 132577258125312000000000 : ℝ))
    (lo_next := (138931 / 1000000000000000000 : ℝ)) (hi_next := (27799 / 200000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_5 := horner_step_pp hx0 hx hs_4 (c := (362648839607 / 3238237626624000000000 : ℝ))
    (lo_next := (11198957 / 100000000000000000 : ℝ)) (hi_next := (112056351 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_6 := horner_step_pp hx0 hx hs_5 (c := (8173040147 / 123559128000000000 : ℝ))
    (lo_next := (66146793679 / 1000000000000000000 : ℝ)) (hi_next := (66200631491 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_7 := horner_step_pp hx0 hx hs_6 (c := (344380717 / 12932920000000 : ℝ))
    (lo_next := (5325645206187 / 200000000000000000 : ℝ)) (hi_next := (26660032323859 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_8 := horner_step_pp hx0 hx hs_7 (c := (2459921869 / 382882500000 : ℝ))
    (lo_next := (3212371770712947 / 500000000000000000 : ℝ)) (hi_next := (128751048686141 / 20000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs_9 := horner_step_pp hx0 hx hs_8 (c := (643430647 / 938437500 : ℝ))
    (lo_next := (685640383083583083 / 1000000000000000000 : ℝ)) (hi_next := (688733324552902361 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact hs_9

/-- Uniform upper bound `< 1 / 10⁹` on the Rayleigh quotient of `twoPrimeScaleTest s` across
`s ∈ [1 - 1 / 10²⁰, 1]`, covering both `s = 1` and strictly interior compact supports `s < 1`. -/
theorem weilQuad_twoPrimeScaleTest_lt {s : ℝ} (hs0 : 1 - 1 / 10 ^ 20 ≤ s) (hs1 : s ≤ 1) :
    weilQuad (twoPrimeScaleTest s) < (1 / 10 ^ 9 : ℝ) * ∫ x, twoPrimeScaleTest s x ^ 2 := by
  have hs_pos : 0 < s := by linarith
  set F := twoPrimeScaleTest s
  set A := s * Real.log 2
  have hA_pos : 0 < A := mul_pos hs_pos apertureLogTwo_pos
  have h2A_pos : 0 < 2 * A := by positivity
  have hF2 : ContDiff ℝ 2 F := contDiff_twoPrimeScaleTest s
  have hsA : tsupport F ⊆ Icc (-A) A := tsupport_twoPrimeScaleTest hs_pos
  have hs_log2 : tsupport F ⊆ Icc (-Real.log 2) (Real.log 2) := by
    have hAle : A ≤ Real.log 2 := by dsimp [A]; nlinarith [apertureLogTwo_pos]
    exact hsA.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hcs : HasCompactSupport F := isCompact_Icc.of_isClosed_subset (isClosed_tsupport F) hs_log2
  have hdecomp := weilQuad_two_prime_decomposition hF2 hs_log2
  have hsinh0 : sinhPairing F = 0 :=
    odd_whole_integral_zero ((continuous_const.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))).mul hF2.continuous)
      (fun x => by dsimp only; rw [neg_div, Real.sinh_neg, twoPrimeScaleTest_even]; ring)
  set D : ℝ → ℝ := fun t => autocorr F 0 - autocorr F t
  have hd_nn : ∀ t, 0 ≤ D t := fun t =>
    sub_nonneg.mpr ((le_abs_self _).trans (abs_autocorr_le_zero hcs hF2.continuous t))
  have hiW : IntegrableOn (fun t => D t * archLevySinhWeight t) (Ioi (0 : ℝ)) :=
    integrableOn_biScaleLevyIntegrand hF2 hcs
  have hsplit : (∫ t in Ioc (0 : ℝ) (2 * A), D t * archLevySinhWeight t) +
      (∫ t in Ioi (2 * A), D t * archLevySinhWeight t) = biScaleLevyEnergy F := by
    rw [← setIntegral_union (Set.disjoint_left.mpr fun t ht ht' => not_lt_of_ge ht.2 ht')
      measurableSet_Ioi (hiW.mono_set fun _ ht => ht.1) (hiW.mono_set fun t (ht : 2 * A < t) => lt_trans h2A_pos ht),
      Ioc_union_Ioi_eq_Ioi h2A_pos.le]; rfl
  have htail : (∫ t in Ioi (2 * A), D t * archLevySinhWeight t) =
      2 * archLevyAntideriv (2 * A) * (∫ x, F x ^ 2) := by
    have hs_r : tsupport F ⊆ Icc (-(2 * A / 2)) (2 * A / 2) := by simpa using hsA
    have he : ∀ t ∈ Ioi (2 * A), D t * archLevySinhWeight t = 2 * archLevyDensity t * autocorr F 0 := fun t ht => by
      dsimp [D]
      rw [autocorr_eq_zero_of_support (x := t) hs_r (by have ht' : 2 * A < t := ht; linarith),
        sub_zero, archLevySinhWeight, exp_half_div_sinh_eq (lt_trans h2A_pos ht)]; ring
    rw [setIntegral_congr_fun measurableSet_Ioi he, integral_mul_const, integral_const_mul,
      WeilLevyCoshCrossover.integral_archLevyDensity_Ioi h2A_pos, autocorr_zero_eq]
  have h2A_lt75 : 2 * A < 7 / 5 := by
    have h1 : 2 * A ≤ 2 * Real.log 2 := by dsimp [A]; nlinarith [apertureLogTwo_pos]
    exact lt_of_le_of_lt h1 two_mul_log_two_lt_seven_fifths
  have hilog : IntegrableOn (fun t => D t / t) (Ioc (0 : ℝ) (2 * A)) :=
    (local_gamma_terms_integrable_to_two hF2 hcs).1.mono_set fun _ ht => ⟨ht.1, ht.2.trans (by linarith)⟩
  have hikup : IntegrableOn (fun t => D t * (1 / t + polyEval upperKupList t)) (Ioc (0 : ℝ) (2 * A)) := by
    have hc : Continuous (fun t => D t * polyEval upperKupList t) :=
      (continuous_const.sub (_root_.RHTower.ArchimedeanExactForm.continuous_autocorr hF2 hcs)).mul (continuous_polyEval _)
    refine (hilog.add (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [Pi.add_apply]; field_simp [ht.1.ne']; ring
  have hloc_le : (∫ t in Ioc (0 : ℝ) (2 * A), D t * archLevySinhWeight t) ≤
      ∫ t in Ioc (0 : ℝ) (2 * A), D t * (1 / t + polyEval upperKupList t) :=
    setIntegral_mono_on (hiW.mono_set fun _ ht => ht.1) hikup measurableSet_Ioc fun t ht => by
      have hk := archLevySinhWeight_le_poly14_cosh26 ⟨ht.1, ht.2.trans h2A_lt75.le⟩
      rw [kup_kernel_eq ht.1.ne'] at hk
      exact mul_le_mul_of_nonneg_left hk (hd_nn t)
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  obtain ⟨h3l, h3u⟩ := log_three_bounds_d26
  obtain ⟨_, hgb_u⟩ := gammaBracket_zero_bounds
  obtain ⟨hw2l, _⟩ := primeTwoWeight_bounds
  obtain ⟨hw3l, _⟩ := primeThreeWeight_bounds
  have hlev_s := archLevyAntideriv_twoPrimeScale_le hs0 hs1
  have hmass := integral_sq_twoPrimeScaleTest hs_pos
  have hlag := scaled_lag_kup_eq hs_pos
  have hcosh := coshPairing_twoPrimeScaleTest_le hs_pos hs1
  dsimp only at hlag hcosh
  have hinv_s : (1 : ℝ) ≤ 1 / s ∧ 1 / s ≤ (1000000000000000000010001 / 1000000000000000000000000 : ℝ) := by
    refine ⟨(le_div_iff₀ hs_pos).mpr (by linarith), (div_le_iff₀ hs_pos).mpr ?_⟩
    have hc : (1 : ℝ) ≤ (1000000000000000000010001 / 1000000000000000000000000 : ℝ) * (1 - 1 / 10 ^ 20) := by norm_num
    nlinarith
  have htau3 : (792481250360578090726869 / 500000000000000000000000 : ℝ) ≤ Real.log 3 / A ∧ Real.log 3 / A ≤ (1584962500721156181469591 / 1000000000000000000000000 : ℝ) := by
    have hlog2_pos : 0 < Real.log 2 := apertureLogTwo_pos
    constructor
    · rw [le_div_iff₀ hA_pos]
      have hAle : A ≤ logTwoHi := by dsimp [A]; nlinarith
      have hc : (792481250360578090726869 / 500000000000000000000000 : ℝ) * logTwoHi ≤ logThreeLo := by norm_num [logTwoHi, logThreeLo]
      nlinarith
    · rw [div_le_iff₀ hA_pos]
      have hAlo : (1 - 1 / 10 ^ 20 : ℝ) * logTwoLo ≤ A := by dsimp [A]; nlinarith
      have hc : logThreeHi ≤ (1584962500721156181469591 / 1000000000000000000000000 : ℝ) * ((1 - 1 / 10 ^ 20 : ℝ) * logTwoLo) := by norm_num [logTwoLo, logThreeHi]
      nlinarith
  have hA_iv : (6931471805599453094103 / 10000000000000000000000 : ℝ) ≤ A ∧ A ≤ (69314718055994530941723213 / 100000000000000000000000000 : ℝ) := by
    constructor
    · have hc : (6931471805599453094103 / 10000000000000000000000 : ℝ) ≤ (1 - 1 / 10 ^ 20 : ℝ) * logTwoLo := by norm_num [logTwoLo]
      dsimp [A]; nlinarith
    · have hc : logTwoHi ≤ (69314718055994530941723213 / 100000000000000000000000000 : ℝ) := by norm_num [logTwoHi]
      dsimp [A]; nlinarith
  have hAsq_iv : (0 : ℝ) ≤ A ^ 2 ∧ A ^ 2 ≤ (480453013918201424667103 / 1000000000000000000000000 : ℝ) := by
    refine ⟨sq_nonneg A, (pow_le_pow_left₀ hA_pos.le hA_iv.2 2).trans ?_⟩; norm_num
  have hc2 := horner_ac_p2 hinv_s
  have hc3 := horner_ac_p3 htau3
  have hkup_m := horner_kup_mom hA_iv
  have hpcosh := horner_pcosh hAsq_iv
  have hac_p2 : (-2 * (Real.log 2 / Real.sqrt 2) * autocorr F (Real.log 2)) / (2 * A) ≤ -primeTwoWeightLo * (63953227262567843 / 1000000000000000000 : ℝ) := by
    have he1 : Real.log 2 = A * (1 / s) := by dsimp [A]; field_simp [hs_pos.ne']; ring
    have hac_eq : autocorr F (Real.log 2) = A * polyEval upperAcList (1 / s) := by
      dsimp [F]; rw [he1, autocorr_twoPrimeScaleTest hs_pos (1 / s),
        autocorr_upperUnitTest (by linarith [hinv_s.1]) (by linarith [hinv_s.2])]
    rw [hac_eq, show (-2 * (Real.log 2 / Real.sqrt 2) * (A * polyEval upperAcList (1 / s))) / (2 * A) =
        -(Real.log 2 / Real.sqrt 2) * polyEval upperAcList (1 / s) by field_simp [hA_pos.ne']; ring]
    have hw2_nn : 0 ≤ primeTwoWeightLo := by norm_num [primeTwoWeightLo]
    nlinarith [hc2.1]
  have hac_p3 : (-2 * (Real.log 3 / Real.sqrt 3) * autocorr F (Real.log 3)) / (2 * A) ≤ -primeThreeWeightLo * (5337678228563 / 125000000000000000 : ℝ) := by
    have he3 : Real.log 3 = A * (Real.log 3 / A) := by field_simp [hA_pos.ne']
    have hac_eq : autocorr F (Real.log 3) = A * polyEval upperAcList (Real.log 3 / A) := by
      dsimp [F]; rw [he3, autocorr_twoPrimeScaleTest hs_pos (Real.log 3 / A),
        autocorr_upperUnitTest (by linarith [htau3.1]) (by linarith [htau3.2])]
    rw [hac_eq, show (-2 * (Real.log 3 / Real.sqrt 3) * (A * polyEval upperAcList (Real.log 3 / A))) / (2 * A) =
        -(Real.log 3 / Real.sqrt 3) * polyEval upperAcList (Real.log 3 / A) by field_simp [hA_pos.ne']; ring]
    have hw3_nn : 0 ≤ primeThreeWeightLo := by norm_num [primeThreeWeightLo]
    nlinarith [hc3.1]
  have hcosh_num : coshPairing F ^ 2 / 2 / (2 * A) ≤ 4 * (69314718055994530941723213 / 100000000000000000000000000 : ℝ) * (344366662276451181 / 500000000000000000 : ℝ) ^ 2 := by
    have habs_pc : |polyEval upperCoshPolyList (A ^ 2)| = polyEval upperCoshPolyList (A ^ 2) :=
      abs_of_nonneg (by linarith [hpcosh.1])
    rw [habs_pc] at hcosh
    have hpt : polyEval upperCoshPolyList (A ^ 2) + 1 / 10 ^ 18 ≤ (344366662276451181 / 500000000000000000 : ℝ) := by linarith [hpcosh.2]
    have hsq := pow_le_pow_left₀ (by linarith [hpcosh.1]) hpt 2
    nlinarith [hcosh, hA_iv.2, hA_pos]
  have hdiv_lt : weilQuad F / (2 * A) < (1 / 10 ^ 9 : ℝ) * upperMassRat := by
    have hloc_div := div_le_div_of_nonneg_right hloc_le h2A_pos.le
    rw [hlag] at hloc_div
    have hw_div : weilQuad F / (2 * A) =
        (Zeta23.EF.gammaBracket 0 + 2 * archLevyAntideriv (2 * A)) * upperMassRat +
        (∫ t in Ioc (0 : ℝ) (2 * A), D t * archLevySinhWeight t) / (2 * A) +
        (-2 * (Real.log 2 / Real.sqrt 2) * autocorr F (Real.log 2)) / (2 * A) +
        (-2 * (Real.log 3 / Real.sqrt 3) * autocorr F (Real.log 3)) / (2 * A) +
        coshPairing F ^ 2 / 2 / (2 * A) := by
      rw [hdecomp, ← hsplit, htail, hsinh0, hmass]; field_simp [hA_pos.ne']; ring
    rw [hw_div]
    have hM_pos : 0 < upperMassRat := by norm_num [upperMassRat]
    have hAk : A * polyEval upperKupMomList A ≤ (69314718055994530941723213 / 100000000000000000000000000 : ℝ) * (149175633876983399 / 250000000000000000 : ℝ) := by
      nlinarith [hA_pos, hA_iv.2, hkup_m.2]
    have hnum : (gammaBracketZeroHi + 2 * (archLevyTwoLogTwoHi + (4 / 10 ^ 20 : ℝ) * logTwoHi)) * upperMassRat +
        (2963742098784573942031661892392419327 / 2016626750442751381850687255859375000 : ℝ) + (69314718055994530941723213 / 100000000000000000000000000 : ℝ) * (149175633876983399 / 250000000000000000 : ℝ) -
        primeTwoWeightLo * (63953227262567843 / 1000000000000000000 : ℝ) - primeThreeWeightLo * (5337678228563 / 125000000000000000 : ℝ) +
        4 * (69314718055994530941723213 / 100000000000000000000000000 : ℝ) * (344366662276451181 / 500000000000000000 : ℝ) ^ 2 < (1 / 10 ^ 9 : ℝ) * upperMassRat := by
      norm_num [gammaBracketZeroHi, archLevyTwoLogTwoHi, logTwoHi, upperMassRat, primeTwoWeightLo, primeThreeWeightLo]
    nlinarith [hgb_u, hlev_s, hM_pos, hloc_div, hAk, hac_p2, hac_p3, hcosh_num, hnum]
  have hm := (div_lt_iff₀ h2A_pos).mp hdiv_lt
  rw [hmass]; linarith

/-- At the exact boundary `s = 1`, `twoPrimeUpperTest` has Rayleigh quotient `< 1 / 10⁹`. -/
theorem weilQuad_twoPrimeUpperTest_lt :
    weilQuad twoPrimeUpperTest < (1 / 10 ^ 9 : ℝ) * ∫ x, twoPrimeUpperTest x ^ 2 :=
  weilQuad_twoPrimeScaleTest_lt (by norm_num) le_rfl

/-- The degree-14 local Gamma lower kernel fails to certify positivity at aperture `A = log 2`:
its quadratic form evaluates strictly negatively (`≈ -9.12 × 10⁻⁸` per unit mass) on `twoPrimeUpperTest`. -/
theorem twoPrimeDegree14GammaForm_twoPrimeUpperTest_lt_zero :
    twoPrimeDegree14GammaForm twoPrimeUpperTest < 0 := by
  set F := twoPrimeUpperTest
  set A := Real.log 2
  have hA_pos : 0 < A := apertureLogTwo_pos
  have h2A_pos : 0 < 2 * A := by positivity
  have hsinh0 : sinhPairing F = 0 :=
    odd_whole_integral_zero ((continuous_const.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))).mul contDiff_twoPrimeUpperTest.continuous)
      (fun x => by dsimp only [F]; unfold twoPrimeUpperTest; rw [neg_div, Real.sinh_neg, twoPrimeScaleTest_even]; ring)
  have hmass : (∫ x, F x ^ 2) = 2 * A * upperMassRat := by
    simpa [F, twoPrimeUpperTest, A] using integral_sq_twoPrimeScaleTest one_pos
  have hlag14 : (∫ t in Ioc (0 : ℝ) (2 * A),
      (autocorr F 0 - autocorr F t) * (gammaSinhPolynomial14 (t / 2) / t + gammaCoshPolynomial14 (t / 2) / 2)) / (2 * A) =
      (2963742098784573942031661892392419327 / 2016626750442751381850687255859375000 : ℝ) + A * polyEval upperK14MomList A := by
    have hcongr : (∫ t in Ioc (0 : ℝ) (2 * A),
        (autocorr F 0 - autocorr F t) * (gammaSinhPolynomial14 (t / 2) / t + gammaCoshPolynomial14 (t / 2) / 2)) =
        ∫ t in Ioc (0 : ℝ) (2 * A), (autocorr F 0 - autocorr F t) * (1 / t + polyEval upperK14List t) :=
      setIntegral_congr_fun measurableSet_Ioc fun t ht => by rw [k14_kernel_eq ht.1.ne']
    rw [hcongr]; exact scaled_lag_k14_eq
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  obtain ⟨h3l, h3u⟩ := log_three_bounds_d26
  obtain ⟨_, hgb_u⟩ := gammaBracket_zero_bounds
  obtain ⟨_, hlev_u⟩ := archLevyAntideriv_two_mul_log_two_bounds
  obtain ⟨hw2l, _⟩ := primeTwoWeight_bounds
  obtain ⟨hw3l, _⟩ := primeThreeWeight_bounds
  have htau3 : (792481250360578090726869 / 500000000000000000000000 : ℝ) ≤ Real.log 3 / A ∧ Real.log 3 / A ≤ (1584962500721156181453739 / 1000000000000000000000000 : ℝ) := by
    constructor
    · rw [le_div_iff₀ hA_pos]
      have hc : (792481250360578090726869 / 500000000000000000000000 : ℝ) * logTwoHi ≤ logThreeLo := by norm_num [logTwoHi, logThreeLo]
      dsimp [A] at *; nlinarith
    · rw [div_le_iff₀ hA_pos]
      have hc : logThreeHi ≤ (1584962500721156181453739 / 1000000000000000000000000 : ℝ) * logTwoLo := by norm_num [logTwoLo, logThreeHi]
      dsimp [A] at *; nlinarith
  have hk14_m := horner_k14_mom ⟨h2l, h2u⟩
  have hc3_1 := horner_ac_p3_one htau3
  have hAsq_iv : (0 : ℝ) ≤ A ^ 2 ∧ A ^ 2 ≤ (480453013918201424667103 / 1000000000000000000000000 : ℝ) := by
    refine ⟨sq_nonneg A, (pow_le_pow_left₀ hA_pos.le h2u 2).trans ?_⟩; norm_num [logTwoHi]
  have hpcosh := horner_pcosh hAsq_iv
  have hac_p2 : (-2 * (Real.log 2 / Real.sqrt 2) * autocorr F (Real.log 2)) / (2 * A) ≤ -primeTwoWeightLo * (995266715748155559345806835383 / 15562415820893061120000000000000 : ℝ) := by
    have hac_eq : autocorr F (Real.log 2) = A * (995266715748155559345806835383 / 15562415820893061120000000000000 : ℝ) := by
      dsimp [F, twoPrimeUpperTest]
      have h1 := autocorr_twoPrimeScaleTest one_pos 1
      simp only [one_mul, mul_one] at h1
      rw [h1, autocorr_upperUnitTest zero_le_one (by norm_num)]
      dsimp [A]; norm_num [upperAcList, polyEval]
    rw [hac_eq, show (-2 * (Real.log 2 / Real.sqrt 2) * (A * (995266715748155559345806835383 / 15562415820893061120000000000000 : ℝ))) / (2 * A) =
        -(Real.log 2 / Real.sqrt 2) * (995266715748155559345806835383 / 15562415820893061120000000000000 : ℝ) by field_simp [hA_pos.ne']; ring]
    linarith
  have hac_p3 : (-2 * (Real.log 3 / Real.sqrt 3) * autocorr F (Real.log 3)) / (2 * A) ≤ -primeThreeWeightLo * (42701425828511 / 1000000000000000000 : ℝ) := by
    have he3 : Real.log 3 = A * (Real.log 3 / A) := by field_simp [hA_pos.ne']
    have hac_eq : autocorr F (Real.log 3) = A * polyEval upperAcList (Real.log 3 / A) := by
      dsimp [F, twoPrimeUpperTest]
      have h1 := autocorr_twoPrimeScaleTest one_pos (Real.log 3 / A)
      simp only [one_mul] at h1
      rw [he3, show Real.log 2 * (Real.log 3 / A) = A * (Real.log 3 / A) from rfl] at *
      rw [show A * (Real.log 3 / A) = Real.log 2 * (Real.log 3 / A) from rfl, h1,
        autocorr_upperUnitTest (by linarith [htau3.1]) (by linarith [htau3.2])]
    rw [hac_eq, show (-2 * (Real.log 3 / Real.sqrt 3) * (A * polyEval upperAcList (Real.log 3 / A))) / (2 * A) =
        -(Real.log 3 / Real.sqrt 3) * polyEval upperAcList (Real.log 3 / A) by field_simp [hA_pos.ne']; ring]
    have hw3_nn : 0 ≤ primeThreeWeightLo := by norm_num [primeThreeWeightLo]
    nlinarith [hc3_1.1]
  have hcosh_num : coshPairing F ^ 2 / 2 / (2 * A) ≤ 4 * logTwoHi * (344366662276451181 / 500000000000000000 : ℝ) ^ 2 := by
    have hcosh := coshPairing_twoPrimeScaleTest_le one_pos le_rfl
    dsimp only [one_mul] at hcosh
    change coshPairing F ^ 2 / 2 / (2 * A) ≤ 4 * A * (|polyEval upperCoshPolyList (A ^ 2)| + 1 / 10 ^ 18) ^ 2 at hcosh
    have habs_pc : |polyEval upperCoshPolyList (A ^ 2)| = polyEval upperCoshPolyList (A ^ 2) :=
      abs_of_nonneg (by linarith [hpcosh.1])
    rw [habs_pc] at hcosh
    have hpt : polyEval upperCoshPolyList (A ^ 2) + 1 / 10 ^ 18 ≤ (344366662276451181 / 500000000000000000 : ℝ) := by linarith [hpcosh.2]
    have hsq := pow_le_pow_left₀ (by linarith [hpcosh.1]) hpt 2
    nlinarith [hcosh, h2u, hA_pos]
  suffices hdiv : twoPrimeDegree14GammaForm F / (2 * A) < 0 by
    exact (div_lt_iff₀ h2A_pos).mp (by simpa using hdiv)
  have hw_div : twoPrimeDegree14GammaForm F / (2 * A) =
      (Zeta23.EF.gammaBracket 0 + 2 * archLevyAntideriv (2 * A)) * upperMassRat +
      (∫ t in Ioc (0 : ℝ) (2 * A),
        (autocorr F 0 - autocorr F t) * (gammaSinhPolynomial14 (t / 2) / t + gammaCoshPolynomial14 (t / 2) / 2)) / (2 * A) +
      (-2 * (Real.log 2 / Real.sqrt 2) * autocorr F (Real.log 2)) / (2 * A) +
      (-2 * (Real.log 3 / Real.sqrt 3) * autocorr F (Real.log 3)) / (2 * A) +
      coshPairing F ^ 2 / 2 / (2 * A) := by
    unfold twoPrimeDegree14GammaForm; rw [hsinh0, hmass]; dsimp [A]; field_simp [hA_pos.ne']; ring
  rw [hw_div, hlag14]
  have hM_pos : 0 < upperMassRat := by norm_num [upperMassRat]
  have hAk : A * polyEval upperK14MomList A ≤ logTwoHi * (74587801268296763 / 125000000000000000 : ℝ) := by
    nlinarith [hA_pos, h2u, hk14_m.2]
  have hnum : (gammaBracketZeroHi + 2 * archLevyTwoLogTwoHi) * upperMassRat +
      (2963742098784573942031661892392419327 / 2016626750442751381850687255859375000 : ℝ) + logTwoHi * (74587801268296763 / 125000000000000000 : ℝ) -
      primeTwoWeightLo * (995266715748155559345806835383 / 15562415820893061120000000000000 : ℝ) - primeThreeWeightLo * (42701425828511 / 1000000000000000000 : ℝ) +
      4 * logTwoHi * (344366662276451181 / 500000000000000000 : ℝ) ^ 2 < 0 := by
    norm_num [gammaBracketZeroHi, archLevyTwoLogTwoHi, logTwoHi, upperMassRat, primeTwoWeightLo, primeThreeWeightLo]
  nlinarith [hgb_u, hlev_u, hM_pos, hAk, hac_p2, hac_p3, hcosh_num, hnum]

end GaloisForLFunctions.WindowTowerOfSpecZ
