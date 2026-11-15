import GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo.Data.OddDataA
import GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo.Data.OddDataB

/-!
# The odd Weil quadratic form has a positive floor at aperture `log 2`

This module proves the unconditional `L²` floor `(1 / 10 ^ 10) * ∫ x, F x ^ 2 ≤ weilQuad F`
for every real odd `C²` test `F` supported in `[-log 2, log 2]` (retaining both the
prime-two and prime-three shifts):

1. Retains 11 low odd Legendre moment charges (`P_1, P_3, ..., P_21` on `[0, 1]`),
   the regional logarithmic gap above degree 23, all even correlation moments up to
   `t ^ 22`, the four odd correlation moments `t, t ^ 3, t ^ 5, t ^ 7` via repeated
   integration by parts and Dirichlet–Wirtinger damping, and the exact `sinh` pole
   Taylor charge.
2. Folds `(0, 1)` into four coupled branches on `(0, (1 - a) / 2)` (`a = log 3 / log 2 - 1`)
   and two coupled branches on `(1 - a, 1 / 2)`, dominating the tridiagonal fiberwise
   energy across 10 + 2 dyadic subintervals and two boundary slivers via shifted rational
   Taylor potentials and Bernstein–Jensen `L²` residual bounds (`FiberCert.bound`).
3. Certifies positive semidefiniteness of the assembled `11 × 11` rational certificate
   matrix by an exact `LDLᵀ` factorization plus strict diagonal dominance (`quad_nonneg_of_ldlCheck`).
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

private theorem sum_finK (f : Fin 11 → ℝ) :
    (∑ i : Fin 11, f i) = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ + f ⟨2, by omega⟩ + f ⟨3, by omega⟩ + f ⟨4, by omega⟩ + f ⟨5, by omega⟩ + f ⟨6, by omega⟩ + f ⟨7, by omega⟩ + f ⟨8, by omega⟩ + f ⟨9, by omega⟩ + f ⟨10, by omega⟩ := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f ⟨0, by omega⟩ + (f ⟨1, by omega⟩ + (f ⟨2, by omega⟩ + (f ⟨3, by omega⟩ + (f ⟨4, by omega⟩ + (f ⟨5, by omega⟩ + (f ⟨6, by omega⟩ + (f ⟨7, by omega⟩ + (f ⟨8, by omega⟩ + (f ⟨9, by omega⟩ + (f ⟨10, by omega⟩)))))))))) = _
  ring

private theorem sum_range_12 (f : ℕ → ℝ) :
    (∑ p ∈ Finset.range 12, f p) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

private theorem sum_range_23 (f : ℕ → ℝ) :
    (∑ p ∈ Finset.range 23, f p) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 := by
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

/-! ### 2. Retained archimedean moments, Wirtinger damping, and `B_clean` bound -/

private def degAt (k : Fin 11) : ℕ := 2 * k.1 + 1
private def halfMoment (G : ℝ → ℝ) (k : Fin 11) : ℝ := ∫ u in (0 : ℝ)..1, G u * legP (degAt k) u

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

private def monToLegMat (j k : Fin 11) : ℝ :=
  matAt ([([1] : List ℝ),
    ([3 / 5, 2 / 5] : List ℝ),
    ([3 / 7, 4 / 9, 8 / 63] : List ℝ),
    ([1 / 3, 14 / 33, 8 / 39, 16 / 429] : List ℝ),
    ([3 / 11, 56 / 143, 16 / 65, 192 / 2431, 128 / 12155] : List ℝ),
    ([3 / 13, 14 / 39, 176 / 663, 480 / 4199, 128 / 4641, 256 / 88179] : List ℝ),
    ([1 / 5, 28 / 85, 88 / 323, 320 / 2261, 128 / 2737, 512 / 56525, 1024 / 1300075] : List ℝ),
    ([3 / 17, 98 / 323, 88 / 323, 1200 / 7429, 128 / 1955, 256 / 14535, 3072 / 1077205, 2048 / 9694845] : List ℝ),
    ([3 / 19, 16 / 57, 352 / 1311, 384 / 2185, 256 / 3105, 2048 / 74385, 12288 / 1964315, 16384 / 18819405, 32768 / 583401555] : List ℝ),
    ([1 / 7, 6 / 23, 1056 / 4025, 64 / 345, 4864 / 50025, 512 / 13485, 12288 / 1137235, 8192 / 3851925, 32768 / 126233085, 65536 / 4418157975] : List ℝ),
    ([3 / 23, 28 / 115, 88 / 345, 128 / 667, 34048 / 310155, 7168 / 148335, 18432 / 1137235, 16384 / 4072035, 229376 / 328206021, 131072 / 1725185495, 262144 / 67282234305] : List ℝ)] : List (List ℝ)) j.1 k.1

private theorem pow_eq_leg_sum_0 (u : ℝ) :
    u ^ 1 = ∑ k : Fin 11, monToLegMat ⟨0, by omega⟩ k * legP (degAt k) u := by
  rw [sum_finK]; dsimp only [monToLegMat, matAt, listAt, coeffAt, degAt]
  rw [legP_eq_1 u]
  dsimp only [legList_1, polyEval]; ring
private theorem pow_eq_leg_sum_1 (u : ℝ) :
    u ^ 3 = ∑ k : Fin 11, monToLegMat ⟨1, by omega⟩ k * legP (degAt k) u := by
  rw [sum_finK]; dsimp only [monToLegMat, matAt, listAt, coeffAt, degAt]
  rw [legP_eq_1 u, legP_eq_3 u]
  dsimp only [legList_1, legList_3, polyEval]; ring
private theorem pow_eq_leg_sum_2 (u : ℝ) :
    u ^ 5 = ∑ k : Fin 11, monToLegMat ⟨2, by omega⟩ k * legP (degAt k) u := by
  rw [sum_finK]; dsimp only [monToLegMat, matAt, listAt, coeffAt, degAt]
  rw [legP_eq_1 u, legP_eq_3 u, legP_eq_5 u]
  dsimp only [legList_1, legList_3, legList_5, polyEval]; ring
private theorem pow_eq_leg_sum_3 (u : ℝ) :
    u ^ 7 = ∑ k : Fin 11, monToLegMat ⟨3, by omega⟩ k * legP (degAt k) u := by
  rw [sum_finK]; dsimp only [monToLegMat, matAt, listAt, coeffAt, degAt]
  rw [legP_eq_1 u, legP_eq_3 u, legP_eq_5 u, legP_eq_7 u]
  dsimp only [legList_1, legList_3, legList_5, legList_7, polyEval]; ring
private theorem pow_eq_leg_sum_4 (u : ℝ) :
    u ^ 9 = ∑ k : Fin 11, monToLegMat ⟨4, by omega⟩ k * legP (degAt k) u := by
  rw [sum_finK]; dsimp only [monToLegMat, matAt, listAt, coeffAt, degAt]
  rw [legP_eq_1 u, legP_eq_3 u, legP_eq_5 u, legP_eq_7 u, legP_eq_9 u]
  dsimp only [legList_1, legList_3, legList_5, legList_7, legList_9, polyEval]; ring
private theorem pow_eq_leg_sum_5 (u : ℝ) :
    u ^ 11 = ∑ k : Fin 11, monToLegMat ⟨5, by omega⟩ k * legP (degAt k) u := by
  rw [sum_finK]; dsimp only [monToLegMat, matAt, listAt, coeffAt, degAt]
  rw [legP_eq_1 u, legP_eq_3 u, legP_eq_5 u, legP_eq_7 u, legP_eq_9 u, legP_eq_11 u]
  dsimp only [legList_1, legList_3, legList_5, legList_7, legList_9, legList_11, polyEval]; ring
private theorem pow_eq_leg_sum_6 (u : ℝ) :
    u ^ 13 = ∑ k : Fin 11, monToLegMat ⟨6, by omega⟩ k * legP (degAt k) u := by
  rw [sum_finK]; dsimp only [monToLegMat, matAt, listAt, coeffAt, degAt]
  rw [legP_eq_1 u, legP_eq_3 u, legP_eq_5 u, legP_eq_7 u, legP_eq_9 u, legP_eq_11 u, legP_eq_13 u]
  dsimp only [legList_1, legList_3, legList_5, legList_7, legList_9, legList_11, legList_13, polyEval]; ring
private theorem pow_eq_leg_sum_7 (u : ℝ) :
    u ^ 15 = ∑ k : Fin 11, monToLegMat ⟨7, by omega⟩ k * legP (degAt k) u := by
  rw [sum_finK]; dsimp only [monToLegMat, matAt, listAt, coeffAt, degAt]
  rw [legP_eq_1 u, legP_eq_3 u, legP_eq_5 u, legP_eq_7 u, legP_eq_9 u, legP_eq_11 u, legP_eq_13 u, legP_eq_15 u]
  dsimp only [legList_1, legList_3, legList_5, legList_7, legList_9, legList_11, legList_13, legList_15, polyEval]; ring
private theorem pow_eq_leg_sum_8 (u : ℝ) :
    u ^ 17 = ∑ k : Fin 11, monToLegMat ⟨8, by omega⟩ k * legP (degAt k) u := by
  rw [sum_finK]; dsimp only [monToLegMat, matAt, listAt, coeffAt, degAt]
  rw [legP_eq_1 u, legP_eq_3 u, legP_eq_5 u, legP_eq_7 u, legP_eq_9 u, legP_eq_11 u, legP_eq_13 u, legP_eq_15 u, legP_eq_17 u]
  dsimp only [legList_1, legList_3, legList_5, legList_7, legList_9, legList_11, legList_13, legList_15, legList_17, polyEval]; ring
private theorem pow_eq_leg_sum_9 (u : ℝ) :
    u ^ 19 = ∑ k : Fin 11, monToLegMat ⟨9, by omega⟩ k * legP (degAt k) u := by
  rw [sum_finK]; dsimp only [monToLegMat, matAt, listAt, coeffAt, degAt]
  rw [legP_eq_1 u, legP_eq_3 u, legP_eq_5 u, legP_eq_7 u, legP_eq_9 u, legP_eq_11 u, legP_eq_13 u, legP_eq_15 u, legP_eq_17 u, legP_eq_19 u]
  dsimp only [legList_1, legList_3, legList_5, legList_7, legList_9, legList_11, legList_13, legList_15, legList_17, legList_19, polyEval]; ring
private theorem pow_eq_leg_sum_10 (u : ℝ) :
    u ^ 21 = ∑ k : Fin 11, monToLegMat ⟨10, by omega⟩ k * legP (degAt k) u := by
  rw [sum_finK]; dsimp only [monToLegMat, matAt, listAt, coeffAt, degAt]
  rw [legP_eq_1 u, legP_eq_3 u, legP_eq_5 u, legP_eq_7 u, legP_eq_9 u, legP_eq_11 u, legP_eq_13 u, legP_eq_15 u, legP_eq_17 u, legP_eq_19 u, legP_eq_21 u]
  dsimp only [legList_1, legList_3, legList_5, legList_7, legList_9, legList_11, legList_13, legList_15, legList_17, legList_19, legList_21, polyEval]; ring

private theorem mon_moment_eq_leg_sum {G : ℝ → ℝ} (hGc : Continuous G) (j : Fin 11) :
    (∫ u in (0 : ℝ)..1, u ^ (degAt j) * G u) = ∑ k : Fin 11, monToLegMat j k * halfMoment G k := by
  have hpow : ∀ u : ℝ, u ^ (degAt j) = ∑ k : Fin 11, monToLegMat j k * legP (degAt k) u := by
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
  have hfn : ∀ u : ℝ, u ^ (degAt j) * G u =
      ∑ k : Fin 11, monToLegMat j k * (G u * legP (degAt k) u) := fun u => by
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

private def qEvMat_0 (i j : Fin 11) : ℝ :=
  matAt ([] : List (List ℝ)) i.1 j.1
private theorem qEvMat_0_sym (i j : Fin 11) : qEvMat_0 i j = qEvMat_0 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qEvRowAbs_0 (i : Fin 11) : ℝ := coeffAt ([] : List ℝ) i.1
private theorem qEvRowAbs_0_eq (i : Fin 11) :
    (∑ j : Fin 11, |qEvMat_0 i j|) = qEvRowAbs_0 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qEvMat_0, qEvRowAbs_0, matAt, listAt, coeffAt]; norm_num)

private def qEvMat_1 (i j : Fin 11) : ℝ :=
  matAt ([([-24999999999449249 / 200000000000000000] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qEvMat_1_sym (i j : Fin 11) : qEvMat_1 i j = qEvMat_1 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qEvRowAbs_1 (i : Fin 11) : ℝ := coeffAt ([24999999999449249 / 200000000000000000] : List ℝ) i.1
private theorem qEvRowAbs_1_eq (i : Fin 11) :
    (∑ j : Fin 11, |qEvMat_1 i j|) = qEvRowAbs_1 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qEvMat_1, qEvRowAbs_1, matAt, listAt, coeffAt]; norm_num)

private def qEvMat_2 (i j : Fin 11) : ℝ :=
  matAt ([([195312498726105189 / 6250000000000000000, 65104166242035063 / 6250000000000000000] : List ℝ),
    ([65104166242035063 / 6250000000000000000] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qEvMat_2_sym (i j : Fin 11) : qEvMat_2 i j = qEvMat_2 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qEvRowAbs_2 (i : Fin 11) : ℝ := coeffAt ([65104166242035063 / 1562500000000000000, 65104166242035063 / 6250000000000000000] : List ℝ) i.1
private theorem qEvRowAbs_2_eq (i : Fin 11) :
    (∑ j : Fin 11, |qEvMat_2 i j|) = qEvRowAbs_2 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qEvMat_2, qEvRowAbs_2, matAt, listAt, coeffAt]; norm_num)

private def qEvMat_3 (i j : Fin 11) : ℝ :=
  matAt ([([-89355387221174583 / 10937500000000000000, -23166211501786003 / 4687500000000000000, -3309458785969429 / 6562500000000000000] : List ℝ),
    ([-23166211501786003 / 4687500000000000000, -3309458785969429 / 1562500000000000000] : List ℝ),
    ([-3309458785969429 / 6562500000000000000] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qEvMat_3_sym (i j : Fin 11) : qEvMat_3 i j = qEvMat_3 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qEvRowAbs_3 (i : Fin 11) : ℝ := coeffAt ([29785129073724861 / 2187500000000000000, 3309458785969429 / 468750000000000000, 3309458785969429 / 6562500000000000000] : List ℝ) i.1
private theorem qEvRowAbs_3_eq (i : Fin 11) :
    (∑ j : Fin 11, |qEvMat_3 i j|) = qEvRowAbs_3 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qEvMat_3, qEvRowAbs_3, matAt, listAt, coeffAt]; norm_num)

private def qEvMat_4 (i j : Fin 11) : ℝ :=
  matAt ([([5366589076364431 / 2343750000000000000, 16099767229093293 / 8593750000000000000, 16099767229093293 / 40625000000000000000, 5366589076364431 / 268125000000000000000] : List ℝ),
    ([16099767229093293 / 8593750000000000000, 37566123534551017 / 28125000000000000000, 5366589076364431 / 28125000000000000000] : List ℝ),
    ([16099767229093293 / 40625000000000000000, 5366589076364431 / 28125000000000000000] : List ℝ),
    ([5366589076364431 / 268125000000000000000] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qEvMat_4_sym (i j : Fin 11) : qEvMat_4 i j = qEvMat_4 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qEvRowAbs_4 (i : Fin 11) : ℝ := coeffAt ([5366589076364431 / 1171875000000000000, 262962864741857119 / 77343750000000000000, 5366589076364431 / 9140625000000000000, 5366589076364431 / 268125000000000000000] : List ℝ) i.1
private theorem qEvRowAbs_4_eq (i : Fin 11) :
    (∑ j : Fin 11, |qEvMat_4 i j|) = qEvRowAbs_4 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qEvMat_4, qEvRowAbs_4, matAt, listAt, coeffAt]; norm_num)

private def qEvMat_5 (i j : Fin 11) : ℝ :=
  matAt ([([-26179263157702713 / 38500000000000000000, -8726421052567571 / 13000000000000000000, -95990631578243281 / 455000000000000000000, -26179263157702713 / 1105000000000000000000, -8726421052567571 / 12155000000000000000000] : List ℝ),
    ([-8726421052567571 / 13000000000000000000, -61084947367972997 / 99000000000000000000, -95990631578243281 / 585000000000000000000, -8726421052567571 / 715000000000000000000] : List ℝ),
    ([-95990631578243281 / 455000000000000000000, -95990631578243281 / 585000000000000000000, -8726421052567571 / 315000000000000000000] : List ℝ),
    ([-26179263157702713 / 1105000000000000000000, -8726421052567571 / 715000000000000000000] : List ℝ),
    ([-8726421052567571 / 12155000000000000000000] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qEvMat_5_sym (i j : Fin 11) : qEvMat_5 i j = qEvMat_5 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qEvRowAbs_5 (i : Fin 11) : ℝ := coeffAt ([8726421052567571 / 5500000000000000000, 26179263157702713 / 17875000000000000000, 26179263157702713 / 65000000000000000000, 8726421052567571 / 243100000000000000000, 8726421052567571 / 12155000000000000000000] : List ℝ) i.1
private theorem qEvRowAbs_5_eq (i : Fin 11) :
    (∑ j : Fin 11, |qEvMat_5 i j|) = qEvRowAbs_5 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qEvMat_5, qEvRowAbs_5, matAt, listAt, coeffAt]; norm_num)

private def qEvMat_6 (i j : Fin 11) : ℝ :=
  matAt ([([193402970477625681 / 910000000000000000000, 7163072980652803 / 30000000000000000000, 866731830658989163 / 8925000000000000000000, 193402970477625681 / 11305000000000000000000, 7163072980652803 / 5950000000000000000000, 7163072980652803 / 293930000000000000000000] : List ℝ),
    ([7163072980652803 / 30000000000000000000, 50141510864569621 / 195000000000000000000, 7163072980652803 / 75000000000000000000, 7163072980652803 / 510000000000000000000, 7163072980652803 / 11050000000000000000000] : List ℝ),
    ([866731830658989163 / 8925000000000000000000, 7163072980652803 / 75000000000000000000, 78793802787180833 / 2730000000000000000000, 7163072980652803 / 2730000000000000000000] : List ℝ),
    ([193402970477625681 / 11305000000000000000000, 7163072980652803 / 510000000000000000000, 7163072980652803 / 2730000000000000000000] : List ℝ),
    ([7163072980652803 / 5950000000000000000000, 7163072980652803 / 11050000000000000000000] : List ℝ),
    ([7163072980652803 / 293930000000000000000000] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qEvMat_6_sym (i j : Fin 11) : qEvMat_6 i j = qEvMat_6 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qEvRowAbs_6 (i : Fin 11) : ℝ := coeffAt ([64467656825875227 / 113750000000000000000, 78793802787180833 / 130000000000000000000, 866731830658989163 / 3867500000000000000000, 709144225084627497 / 20995000000000000000000, 7163072980652803 / 3867500000000000000000, 7163072980652803 / 293930000000000000000000] : List ℝ) i.1
private theorem qEvRowAbs_6_eq (i : Fin 11) :
    (∑ j : Fin 11, |qEvMat_6 i j|) = qEvRowAbs_6 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qEvMat_6, qEvRowAbs_6, matAt, listAt, coeffAt]; norm_num)

private def qEvMat_7 (i j : Fin 11) : ℝ :=
  matAt ([([-43660909082552363 / 600000000000000000000, -305626363577866541 / 3400000000000000000000, -567591818073180719 / 12920000000000000000000, -81084545439025817 / 7752000000000000000000, -813557312097249 / 680000000000000000000, -18711818178236727 / 323000000000000000000000, -271185770699083 / 323000000000000000000000] : List ℝ),
    ([-305626363577866541 / 3400000000000000000000, -2139384545045065787 / 19800000000000000000000, -305626363577866541 / 6120000000000000000000, -305626363577866541 / 28424000000000000000000, -6237272726078909 / 6120000000000000000000, -6237272726078909 / 193800000000000000000000] : List ℝ),
    ([-567591818073180719 / 12920000000000000000000, -305626363577866541 / 6120000000000000000000, -480269999908075993 / 23400000000000000000000, -6237272726078909 / 1768000000000000000000, -6237272726078909 / 30600000000000000000000] : List ℝ),
    ([-81084545439025817 / 7752000000000000000000, -305626363577866541 / 28424000000000000000000, -6237272726078909 / 1768000000000000000000, -6237272726078909 / 17160000000000000000000] : List ℝ),
    ([-813557312097249 / 680000000000000000000, -6237272726078909 / 6120000000000000000000, -6237272726078909 / 30600000000000000000000] : List ℝ),
    ([-18711818178236727 / 323000000000000000000000, -6237272726078909 / 193800000000000000000000] : List ℝ),
    ([-271185770699083 / 323000000000000000000000] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qEvMat_7_sym (i j : Fin 11) : qEvMat_7 i j = qEvMat_7 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qEvRowAbs_7 (i : Fin 11) : ℝ := coeffAt ([43660909082552363 / 200000000000000000000, 3973142726512265033 / 15300000000000000000000, 68678609986854866999 / 581400000000000000000000, 81084545439025817 / 3230000000000000000000, 24677905133616553 / 10200000000000000000000, 43660909082552363 / 484500000000000000000000, 271185770699083 / 323000000000000000000000] : List ℝ) i.1
private theorem qEvRowAbs_7_eq (i : Fin 11) :
    (∑ j : Fin 11, |qEvMat_7 i j|) = qEvRowAbs_7 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qEvMat_7, qEvRowAbs_7, matAt, listAt, coeffAt]; norm_num)

private def qEvMat_8 (i j : Fin 11) : ℝ :=
  matAt ([([3260029542583927 / 106250000000000000000, 159741447586612423 / 3918750000000000000000, 3260029542583927 / 142500000000000000000, 3260029542583927 / 480700000000000000000, 3260029542583927 / 3018750000000000000000, 3260029542583927 / 37406250000000000000000, 9780088627751781 / 3168250000000000000000000, 3260029542583927 / 96948450000000000000000000] : List ℝ),
    ([159741447586612423 / 3918750000000000000000, 1118190133106286961 / 21037500000000000000000, 159741447586612423 / 5557500000000000000000, 3260029542583927 / 407550000000000000000, 3260029542583927 / 2846250000000000000000, 3260029542583927 / 42750000000000000000000, 3260029542583927 / 1857250000000000000000000] : List ℝ),
    ([3260029542583927 / 142500000000000000000, 159741447586612423 / 5557500000000000000000, 35860324968423197 / 2486250000000000000000, 3260029542583927 / 926250000000000000000, 3260029542583927 / 8190000000000000000000, 3260029542583927 / 203490000000000000000000] : List ℝ),
    ([3260029542583927 / 480700000000000000000, 3260029542583927 / 407550000000000000000, 3260029542583927 / 926250000000000000000, 3260029542583927 / 4862000000000000000000, 3260029542583927 / 72930000000000000000000] : List ℝ),
    ([3260029542583927 / 3018750000000000000000, 3260029542583927 / 2846250000000000000000, 3260029542583927 / 8190000000000000000000, 3260029542583927 / 72930000000000000000000] : List ℝ),
    ([3260029542583927 / 37406250000000000000000, 3260029542583927 / 42750000000000000000000, 3260029542583927 / 203490000000000000000000] : List ℝ),
    ([9780088627751781 / 3168250000000000000000000, 3260029542583927 / 1857250000000000000000000] : List ℝ),
    ([3260029542583927 / 96948450000000000000000000] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qEvMat_8_sym (i j : Fin 11) : qEvMat_8 i j = qEvMat_8 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qEvRowAbs_8 (i : Fin 11) : ℝ := coeffAt ([3260029542583927 / 31875000000000000000, 159741447586612423 / 1211250000000000000000, 42380384053591051 / 605625000000000000000, 42380384053591051 / 2228700000000000000000, 3260029542583927 / 1221875000000000000000, 3260029542583927 / 18168750000000000000000, 3260029542583927 / 673253125000000000000000, 3260029542583927 / 96948450000000000000000000] : List ℝ) i.1
private theorem qEvRowAbs_8_eq (i : Fin 11) :
    (∑ j : Fin 11, |qEvMat_8 i j|) = qEvRowAbs_8 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qEvMat_8, qEvRowAbs_8, matAt, listAt, coeffAt]; norm_num)

private def qEvMat_9 (i j : Fin 11) : ℝ :=
  matAt ([([-42110132841768429 / 2612500000000000000000, -1559634549695127 / 68750000000000000000, -26513787344817159 / 1868750000000000000000, -715872258310063293 / 143893750000000000000000, -55973551061280669 / 55343750000000000000000, -2945976371646351 / 25375000000000000000000, -126330398525305287 / 18092375000000000000000000, -173292727743903 / 917125000000000000000000, -173292727743903 / 108037325000000000000000000] : List ℝ),
    ([-1559634549695127 / 68750000000000000000, -534954650545428561 / 16981250000000000000000, -1559634549695127 / 81250000000000000000, -26513787344817159 / 4111250000000000000000, -503761959551526021 / 411125000000000000000000, -173292727743903 / 1375000000000000000000, -519878183231709 / 83375000000000000000000, -173292727743903 / 1584125000000000000000000] : List ℝ),
    ([-26513787344817159 / 1868750000000000000000, -1559634549695127 / 81250000000000000000, -17155980046646397 / 1543750000000000000000, -1559634549695127 / 455000000000000000000, -29633056444207413 / 52325000000000000000000, -519878183231709 / 11375000000000000000000, -519878183231709 / 382375000000000000000000] : List ℝ),
    ([-715872258310063293 / 143893750000000000000000, -26513787344817159 / 4111250000000000000000, -1559634549695127 / 455000000000000000000, -42110132841768429 / 46189000000000000000000, -9877685481402471 / 85085000000000000000000, -519878183231709 / 95095000000000000000000] : List ℝ),
    ([-55973551061280669 / 55343750000000000000000, -503761959551526021 / 411125000000000000000000, -29633056444207413 / 52325000000000000000000, -9877685481402471 / 85085000000000000000000, -519878183231709 / 60775000000000000000000] : List ℝ),
    ([-2945976371646351 / 25375000000000000000000, -173292727743903 / 1375000000000000000000, -519878183231709 / 11375000000000000000000, -519878183231709 / 95095000000000000000000] : List ℝ),
    ([-126330398525305287 / 18092375000000000000000000, -519878183231709 / 83375000000000000000000, -519878183231709 / 382375000000000000000000] : List ℝ),
    ([-173292727743903 / 917125000000000000000000, -173292727743903 / 1584125000000000000000000] : List ℝ),
    ([-173292727743903 / 108037325000000000000000000] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qEvMat_9_sym (i j : Fin 11) : qEvMat_9 i j = qEvMat_9 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qEvRowAbs_9 (i : Fin 11) : ℝ := coeffAt ([14036710947256143 / 237500000000000000000, 26513787344817159 / 326562500000000000000, 26513787344817159 / 546250000000000000000, 238624086103354431 / 15021875000000000000000, 2945976371646351 / 1006250000000000000000, 8837929114939053 / 30132812500000000000000, 715872258310063293 / 49107875000000000000000000, 519878183231709 / 1742537500000000000000000, 173292727743903 / 108037325000000000000000000] : List ℝ) i.1
private theorem qEvRowAbs_9_eq (i : Fin 11) :
    (∑ j : Fin 11, |qEvMat_9 i j|) = qEvRowAbs_9 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qEvMat_9, qEvRowAbs_9, matAt, listAt, coeffAt]; norm_num)

private def qEvMat_10 (i j : Fin 11) : ℝ :=
  matAt ([([4669432996809649 / 616000000000000000000, 294174278799007887 / 26312000000000000000000, 798473042454449979 / 104650000000000000000000, 1508226857969516627 / 493350000000000000000000, 28656310301420815913 / 38152400000000000000000000, 88719226939383331 / 791120000000000000000000, 88719226939383331 / 9097880000000000000000000, 4669432996809649 / 10271800000000000000000000, 32686030977667543 / 3366215600000000000000000000, 4669432996809649 / 70690527600000000000000000000] : List ℝ),
    ([294174278799007887 / 26312000000000000000000, 4669432996809649 / 286000000000000000000, 32686030977667543 / 2990000000000000000000, 5589311297181149853 / 1315600000000000000000000, 11799657182937983023 / 11840400000000000000000000, 621034588575683317 / 4478760000000000000000000, 98058092933002629 / 9097880000000000000000000, 32686030977667543 / 79239600000000000000000000, 4669432996809649 / 818809200000000000000000000] : List ℝ),
    ([798473042454449979 / 104650000000000000000000, 32686030977667543 / 2990000000000000000000, 51363762964906139 / 7280000000000000000000, 2472052763016873 / 956800000000000000000, 99156783049899017 / 179400000000000000000000, 4669432996809649 / 70200000000000000000000, 14008298990428947 / 3468400000000000000000000, 4669432996809649 / 50425200000000000000000000] : List ℝ),
    ([1508226857969516627 / 493350000000000000000000, 5589311297181149853 / 1315600000000000000000000, 2472052763016873 / 956800000000000000000, 274672529224097 / 320320000000000000000, 824017587672291 / 5262400000000000000000, 824017587672291 / 57200000000000000000000, 4669432996809649 / 9209200000000000000000000] : List ℝ),
    ([28656310301420815913 / 38152400000000000000000000, 11799657182937983023 / 11840400000000000000000000, 99156783049899017 / 179400000000000000000000, 824017587672291 / 5262400000000000000000, 5218778055257843 / 240240000000000000000000, 274672529224097 / 240240000000000000000000] : List ℝ),
    ([88719226939383331 / 791120000000000000000000, 621034588575683317 / 4478760000000000000000000, 4669432996809649 / 70200000000000000000000, 824017587672291 / 57200000000000000000000, 274672529224097 / 240240000000000000000000] : List ℝ),
    ([88719226939383331 / 9097880000000000000000000, 98058092933002629 / 9097880000000000000000000, 14008298990428947 / 3468400000000000000000000, 4669432996809649 / 9209200000000000000000000] : List ℝ),
    ([4669432996809649 / 10271800000000000000000000, 32686030977667543 / 79239600000000000000000000, 4669432996809649 / 50425200000000000000000000] : List ℝ),
    ([32686030977667543 / 3366215600000000000000000000, 4669432996809649 / 818809200000000000000000000] : List ℝ),
    ([4669432996809649 / 70690527600000000000000000000] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qEvMat_10_sym (i j : Fin 11) : qEvMat_10 i j = qEvMat_10 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qEvRowAbs_10 (i : Fin 11) : ℝ := coeffAt ([4669432996809649 / 154000000000000000000, 88719226939383331 / 2024000000000000000000, 1508226857969516627 / 52325000000000000000000, 1508226857969516627 / 138138000000000000000000, 28656310301420815913 / 11555775000000000000000000, 1508226857969516627 / 4530960000000000000000000, 798473042454449979 / 31842580000000000000000000, 88719226939383331 / 92446200000000000000000000, 4669432996809649 / 302959404000000000000000000, 4669432996809649 / 70690527600000000000000000000] : List ℝ) i.1
private theorem qEvRowAbs_10_eq (i : Fin 11) :
    (∑ j : Fin 11, |qEvMat_10 i j|) = qEvRowAbs_10 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qEvMat_10, qEvRowAbs_10, matAt, listAt, coeffAt]; norm_num)

private def qEvMat_11 (i j : Fin 11) : ℝ :=
  matAt ([([-45455253453830253 / 23920000000000000000000, -15151751151276751 / 5200000000000000000000, -166669262664044261 / 78000000000000000000000, -287883271874258269 / 301600000000000000000000, -38288475159276349777 / 140244000000000000000000000, -4213564251977780119 / 84146400000000000000000000, -4132295768530023 / 719200000000000000000000, -15151751151276751 / 38628000000000000000000000, -15151751151276751 / 1037805600000000000000000000, -1377431922843341 / 5455132000000000000000000000, -1377431922843341 / 978650680800000000000000000000] : List ℝ),
    ([-15151751151276751 / 5200000000000000000000, -106062258058937257 / 23920000000000000000000, -166669262664044261 / 52000000000000000000000, -742435806412560799 / 530400000000000000000000, -268019326114934448439 / 692172000000000000000000000, -17076023547488898377 / 252439200000000000000000000, -67494164219323709 / 9349600000000000000000000, -1377431922843341 / 3132000000000000000000000, -9642023459903387 / 718480800000000000000000000, -1377431922843341 / 9180588000000000000000000000] : List ℝ),
    ([-166669262664044261 / 78000000000000000000000, -166669262664044261 / 52000000000000000000000, -1833361889304486871 / 813280000000000000000000, -166669262664044261 / 176800000000000000000000, -1166684838648309827 / 4773600000000000000000000, -26833751288911126021 / 692172000000000000000000000, -166669262664044261 / 46748000000000000000000000, -1377431922843341 / 8143200000000000000000000, -1377431922843341 / 446623200000000000000000000] : List ℝ),
    ([-287883271874258269 / 301600000000000000000000, -742435806412560799 / 530400000000000000000000, -166669262664044261 / 176800000000000000000000, -45455253453830253 / 123618560000000000000000, -15151751151276751 / 176800000000000000000000, -348490276479365273 / 30232800000000000000000000, -4132295768530023 / 5127200000000000000000000, -1377431922843341 / 62431200000000000000000000] : List ℝ),
    ([-38288475159276349777 / 140244000000000000000000000, -268019326114934448439 / 692172000000000000000000000, -1166684838648309827 / 4773600000000000000000000, -15151751151276751 / 176800000000000000000000, -287883271874258269 / 17078880000000000000000000, -31680934225396843 / 18564000000000000000000000, -1377431922843341 / 20332000000000000000000000] : List ℝ),
    ([-4213564251977780119 / 84146400000000000000000000, -17076023547488898377 / 252439200000000000000000000, -26833751288911126021 / 692172000000000000000000000, -348490276479365273 / 30232800000000000000000000, -31680934225396843 / 18564000000000000000000000, -1377431922843341 / 14108640000000000000000000] : List ℝ),
    ([-4132295768530023 / 719200000000000000000000, -67494164219323709 / 9349600000000000000000000, -166669262664044261 / 46748000000000000000000000, -4132295768530023 / 5127200000000000000000000, -1377431922843341 / 20332000000000000000000000] : List ℝ),
    ([-15151751151276751 / 38628000000000000000000000, -1377431922843341 / 3132000000000000000000000, -1377431922843341 / 8143200000000000000000000, -1377431922843341 / 62431200000000000000000000] : List ℝ),
    ([-15151751151276751 / 1037805600000000000000000000, -9642023459903387 / 718480800000000000000000000, -1377431922843341 / 446623200000000000000000000] : List ℝ),
    ([-1377431922843341 / 5455132000000000000000000000, -1377431922843341 / 9180588000000000000000000000] : List ℝ),
    ([-1377431922843341 / 978650680800000000000000000000] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qEvMat_11_sym (i j : Fin 11) : qEvMat_11 i j = qEvMat_11 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qEvRowAbs_11 (i : Fin 11) : ℝ := coeffAt ([15151751151276751 / 1840000000000000000000, 742435806412560799 / 59800000000000000000000, 3166715990616840959 / 358800000000000000000000, 4894015621862390573 / 1300650000000000000000000, 650904077707697946209 / 645122400000000000000000000, 183198445738164353 / 1078800000000000000000000, 287883271874258269 / 16541600000000000000000000, 15151751151276751 / 14807400000000000000000000, 742435806412560799 / 23869528800000000000000000000, 15151751151276751 / 37640410800000000000000000000, 1377431922843341 / 978650680800000000000000000000] : List ℝ) i.1
private theorem qEvRowAbs_11_eq (i : Fin 11) :
    (∑ j : Fin 11, |qEvMat_11 i j|) = qEvRowAbs_11 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qEvMat_11, qEvRowAbs_11, matAt, listAt, coeffAt]; norm_num)

private def basisFn (k : Fin 11) (y : ℝ) : ℝ := (2 * (degAt k : ℝ) + 1) * legP (degAt k) y

private def iBasis_0_0 : List ℝ := ([0, 3] : List ℝ)
private def iBasis_1_0 : List ℝ := ([-3 / 2, 0, 3 / 2] : List ℝ)
private def iBasis_2_0 : List ℝ := ([-1, -3 / 2, 0, 1 / 2] : List ℝ)
private def iBasis_3_0 : List ℝ := ([-3 / 8, -1, -3 / 4, 0, 1 / 8] : List ℝ)
private def iBasis_4_0 : List ℝ := ([-1 / 10, -3 / 8, -1 / 2, -1 / 4, 0, 1 / 40] : List ℝ)
private def iBasis_5_0 : List ℝ := ([-1 / 48, -1 / 10, -3 / 16, -1 / 6, -1 / 16, 0, 1 / 240] : List ℝ)
private def iBasis_6_0 : List ℝ := ([-1 / 280, -1 / 48, -1 / 20, -1 / 16, -1 / 24, -1 / 80, 0, 1 / 1680] : List ℝ)
private def iBasis_7_0 : List ℝ := ([-1 / 1920, -1 / 280, -1 / 96, -1 / 60, -1 / 64, -1 / 120, -1 / 480, 0, 1 / 13440] : List ℝ)
private def iBasis_8_0 : List ℝ := ([-1 / 15120, -1 / 1920, -1 / 560, -1 / 288, -1 / 240, -1 / 320, -1 / 720, -1 / 3360, 0, 1 / 120960] : List ℝ)
private theorem iterPrim_basis_0_0 (y : ℝ) : iterPrim 0 (basisFn ⟨0, by omega⟩) y = polyEval iBasis_0_0 y := by
  dsimp only [iterPrim, basisFn, degAt]; rw [legP_eq_1 y]
  dsimp only [legList_1, iBasis_0_0, polyEval]; ring
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
private def iBasis_0_1 : List ℝ := ([0, -21 / 2, 0, 35 / 2] : List ℝ)
private def iBasis_1_1 : List ℝ := ([7 / 8, 0, -21 / 4, 0, 35 / 8] : List ℝ)
private def iBasis_2_1 : List ℝ := ([0, 7 / 8, 0, -7 / 4, 0, 7 / 8] : List ℝ)
private def iBasis_3_1 : List ℝ := ([-7 / 48, 0, 7 / 16, 0, -7 / 16, 0, 7 / 48] : List ℝ)
private def iBasis_4_1 : List ℝ := ([-1 / 15, -7 / 48, 0, 7 / 48, 0, -7 / 80, 0, 1 / 48] : List ℝ)
private def iBasis_5_1 : List ℝ := ([-7 / 384, -1 / 15, -7 / 96, 0, 7 / 192, 0, -7 / 480, 0, 1 / 384] : List ℝ)
private def iBasis_6_1 : List ℝ := ([-1 / 270, -7 / 384, -1 / 30, -7 / 288, 0, 7 / 960, 0, -1 / 480, 0, 1 / 3456] : List ℝ)
private def iBasis_7_1 : List ℝ := ([-7 / 11520, -1 / 270, -7 / 768, -1 / 90, -7 / 1152, 0, 7 / 5760, 0, -1 / 3840, 0, 1 / 34560] : List ℝ)
private def iBasis_8_1 : List ℝ := ([-1 / 11880, -7 / 11520, -1 / 540, -7 / 2304, -1 / 360, -7 / 5760, 0, 1 / 5760, 0, -1 / 34560, 0, 1 / 380160] : List ℝ)
private theorem iterPrim_basis_0_1 (y : ℝ) : iterPrim 0 (basisFn ⟨1, by omega⟩) y = polyEval iBasis_0_1 y := by
  dsimp only [iterPrim, basisFn, degAt]; rw [legP_eq_3 y]
  dsimp only [legList_3, iBasis_0_1, polyEval]; ring
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
private def iBasis_0_2 : List ℝ := ([0, 165 / 8, 0, -385 / 4, 0, 693 / 8] : List ℝ)
private def iBasis_1_2 : List ℝ := ([-11 / 16, 0, 165 / 16, 0, -385 / 16, 0, 231 / 16] : List ℝ)
private def iBasis_2_2 : List ℝ := ([0, -11 / 16, 0, 55 / 16, 0, -77 / 16, 0, 33 / 16] : List ℝ)
private def iBasis_3_2 : List ℝ := ([11 / 384, 0, -11 / 32, 0, 55 / 64, 0, -77 / 96, 0, 33 / 128] : List ℝ)
private def iBasis_4_2 : List ℝ := ([0, 11 / 384, 0, -11 / 96, 0, 11 / 64, 0, -11 / 96, 0, 11 / 384] : List ℝ)
private def iBasis_5_2 : List ℝ := ([-11 / 3840, 0, 11 / 768, 0, -11 / 384, 0, 11 / 384, 0, -11 / 768, 0, 11 / 3840] : List ℝ)
private def iBasis_6_2 : List ℝ := ([-1 / 945, -11 / 3840, 0, 11 / 2304, 0, -11 / 1920, 0, 11 / 2688, 0, -11 / 6912, 0, 1 / 3840] : List ℝ)
private def iBasis_7_2 : List ℝ := ([-11 / 46080, -1 / 945, -11 / 7680, 0, 11 / 9216, 0, -11 / 11520, 0, 11 / 21504, 0, -11 / 69120, 0, 1 / 46080] : List ℝ)
private def iBasis_8_2 : List ℝ := ([-1 / 24570, -11 / 46080, -1 / 1890, -11 / 23040, 0, 11 / 46080, 0, -11 / 80640, 0, 11 / 193536, 0, -1 / 69120, 0, 1 / 599040] : List ℝ)
private theorem iterPrim_basis_0_2 (y : ℝ) : iterPrim 0 (basisFn ⟨2, by omega⟩) y = polyEval iBasis_0_2 y := by
  dsimp only [iterPrim, basisFn, degAt]; rw [legP_eq_5 y]
  dsimp only [legList_5, iBasis_0_2, polyEval]; ring
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
private def iBasis_0_3 : List ℝ := ([0, -525 / 16, 0, 4725 / 16, 0, -10395 / 16, 0, 6435 / 16] : List ℝ)
private def iBasis_1_3 : List ℝ := ([75 / 128, 0, -525 / 32, 0, 4725 / 64, 0, -3465 / 32, 0, 6435 / 128] : List ℝ)
private def iBasis_2_3 : List ℝ := ([0, 75 / 128, 0, -175 / 32, 0, 945 / 64, 0, -495 / 32, 0, 715 / 128] : List ℝ)
private def iBasis_3_3 : List ℝ := ([-3 / 256, 0, 75 / 256, 0, -175 / 128, 0, 315 / 128, 0, -495 / 256, 0, 143 / 256] : List ℝ)
private def iBasis_4_3 : List ℝ := ([0, -3 / 256, 0, 25 / 256, 0, -35 / 128, 0, 45 / 128, 0, -55 / 256, 0, 13 / 256] : List ℝ)
private def iBasis_5_3 : List ℝ := ([1 / 3072, 0, -3 / 512, 0, 25 / 1024, 0, -35 / 768, 0, 45 / 1024, 0, -11 / 512, 0, 13 / 3072] : List ℝ)
private def iBasis_6_3 : List ℝ := ([0, 1 / 3072, 0, -1 / 512, 0, 5 / 1024, 0, -5 / 768, 0, 5 / 1024, 0, -1 / 512, 0, 1 / 3072] : List ℝ)
private def iBasis_7_3 : List ℝ := ([-1 / 43008, 0, 1 / 6144, 0, -1 / 2048, 0, 5 / 6144, 0, -5 / 6144, 0, 1 / 2048, 0, -1 / 6144, 0, 1 / 43008] : List ℝ)
private def iBasis_8_3 : List ℝ := ([-1 / 135135, -1 / 43008, 0, 1 / 18432, 0, -1 / 10240, 0, 5 / 43008, 0, -5 / 55296, 0, 1 / 22528, 0, -1 / 79872, 0, 1 / 645120] : List ℝ)
private theorem iterPrim_basis_0_3 (y : ℝ) : iterPrim 0 (basisFn ⟨3, by omega⟩) y = polyEval iBasis_0_3 y := by
  dsimp only [iterPrim, basisFn, degAt]; rw [legP_eq_7 y]
  dsimp only [legList_7, iBasis_0_3, polyEval]; ring
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
private def iBasis_0_4 : List ℝ := ([0, 5985 / 128, 0, -21945 / 32, 0, 171171 / 64, 0, -122265 / 32, 0, 230945 / 128] : List ℝ)
private def iBasis_1_4 : List ℝ := ([-133 / 256, 0, 5985 / 256, 0, -21945 / 128, 0, 57057 / 128, 0, -122265 / 256, 0, 46189 / 256] : List ℝ)
private def iBasis_2_4 : List ℝ := ([0, -133 / 256, 0, 1995 / 256, 0, -4389 / 128, 0, 8151 / 128, 0, -13585 / 256, 0, 4199 / 256] : List ℝ)
private def iBasis_3_4 : List ℝ := ([19 / 3072, 0, -133 / 512, 0, 1995 / 1024, 0, -1463 / 256, 0, 8151 / 1024, 0, -2717 / 512, 0, 4199 / 3072] : List ℝ)
private def iBasis_4_4 : List ℝ := ([0, 19 / 3072, 0, -133 / 1536, 0, 399 / 1024, 0, -209 / 256, 0, 2717 / 3072, 0, -247 / 512, 0, 323 / 3072] : List ℝ)
private def iBasis_5_4 : List ℝ := ([-19 / 215040, 0, 19 / 6144, 0, -133 / 6144, 0, 133 / 2048, 0, -209 / 2048, 0, 2717 / 30720, 0, -247 / 6144, 0, 323 / 43008] : List ℝ)
private def iBasis_6_4 : List ℝ := ([0, -19 / 215040, 0, 19 / 18432, 0, -133 / 30720, 0, 19 / 2048, 0, -209 / 18432, 0, 247 / 30720, 0, -19 / 6144, 0, 323 / 645120] : List ℝ)
private def iBasis_7_4 : List ℝ := ([19 / 10321920, 0, -19 / 430080, 0, 19 / 73728, 0, -133 / 184320, 0, 19 / 16384, 0, -209 / 184320, 0, 247 / 368640, 0, -19 / 86016, 0, 323 / 10321920] : List ℝ)
private def iBasis_8_4 : List ℝ := ([0, 19 / 10321920, 0, -19 / 1290240, 0, 19 / 368640, 0, -19 / 184320, 0, 19 / 147456, 0, -19 / 184320, 0, 19 / 368640, 0, -19 / 1290240, 0, 19 / 10321920] : List ℝ)
private theorem iterPrim_basis_0_4 (y : ℝ) : iterPrim 0 (basisFn ⟨4, by omega⟩) y = polyEval iBasis_0_4 y := by
  dsimp only [iterPrim, basisFn, degAt]; rw [legP_eq_9 y]
  dsimp only [legList_9, iBasis_0_4, polyEval]; ring
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
private def iBasis_0_5 : List ℝ := ([0, -15939 / 256, 0, 345345 / 256, 0, -1036035 / 128, 0, 2516085 / 128, 0, -5311735 / 256, 0, 2028117 / 256] : List ℝ)
private def iBasis_1_5 : List ℝ := ([483 / 1024, 0, -15939 / 512, 0, 345345 / 1024, 0, -345345 / 256, 0, 2516085 / 1024, 0, -1062347 / 512, 0, 676039 / 1024] : List ℝ)
private def iBasis_2_5 : List ℝ := ([0, 483 / 1024, 0, -5313 / 512, 0, 69069 / 1024, 0, -49335 / 256, 0, 279565 / 1024, 0, -96577 / 512, 0, 52003 / 1024] : List ℝ)
private def iBasis_3_5 : List ℝ := ([-23 / 6144, 0, 483 / 2048, 0, -5313 / 2048, 0, 23023 / 2048, 0, -49335 / 2048, 0, 55913 / 2048, 0, -96577 / 6144, 0, 7429 / 2048] : List ℝ)
private def iBasis_4_5 : List ℝ := ([0, -23 / 6144, 0, 161 / 2048, 0, -5313 / 10240, 0, 3289 / 2048, 0, -16445 / 6144, 0, 5083 / 2048, 0, -7429 / 6144, 0, 7429 / 30720] : List ℝ)
private def iBasis_5_5 : List ℝ := ([23 / 688128, 0, -23 / 12288, 0, 161 / 8192, 0, -1771 / 20480, 0, 3289 / 16384, 0, -3289 / 12288, 0, 5083 / 24576, 0, -7429 / 86016, 0, 7429 / 491520] : List ℝ)
private def iBasis_6_5 : List ℝ := ([0, 23 / 688128, 0, -23 / 36864, 0, 161 / 40960, 0, -253 / 20480, 0, 3289 / 147456, 0, -299 / 12288, 0, 391 / 24576, 0, -7429 / 1290240, 0, 437 / 491520] : List ℝ)
private def iBasis_7_5 : List ℝ := ([-23 / 61931520, 0, 23 / 1376256, 0, -23 / 147456, 0, 161 / 245760, 0, -253 / 163840, 0, 3289 / 1474560, 0, -299 / 147456, 0, 391 / 344064, 0, -7429 / 20643840, 0, 437 / 8847360] : List ℝ)
private def iBasis_8_5 : List ℝ := ([0, -23 / 61931520, 0, 23 / 4128768, 0, -23 / 737280, 0, 23 / 245760, 0, -253 / 1474560, 0, 299 / 1474560, 0, -23 / 147456, 0, 391 / 5160960, 0, -437 / 20643840, 0, 23 / 8847360] : List ℝ)
private theorem iterPrim_basis_0_5 (y : ℝ) : iterPrim 0 (basisFn ⟨5, by omega⟩) y = polyEval iBasis_0_5 y := by
  dsimp only [iterPrim, basisFn, degAt]; rw [legP_eq_11 y]
  dsimp only [legList_11, iBasis_0_5, polyEval]; ring
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
private def iBasis_0_6 : List ℝ := ([0, 81081 / 1024, 0, -1216215 / 512, 0, 20675655 / 1024, 0, -18706545 / 256, 0, 130945815 / 1024, 0, -54759159 / 512, 0, 35102025 / 1024] : List ℝ)
private def iBasis_1_6 : List ℝ := ([-891 / 2048, 0, 81081 / 2048, 0, -1216215 / 2048, 0, 6891885 / 2048, 0, -18706545 / 2048, 0, 26189163 / 2048, 0, -18253053 / 2048, 0, 5014575 / 2048] : List ℝ)
private def iBasis_2_6 : List ℝ := ([0, -891 / 2048, 0, 27027 / 2048, 0, -243243 / 2048, 0, 984555 / 2048, 0, -2078505 / 2048, 0, 2380833 / 2048, 0, -1404081 / 2048, 0, 334305 / 2048] : List ℝ)
private def iBasis_3_6 : List ℝ := ([81 / 32768, 0, -891 / 4096, 0, 27027 / 8192, 0, -81081 / 4096, 0, 984555 / 16384, 0, -415701 / 4096, 0, 793611 / 8192, 0, -200583 / 4096, 0, 334305 / 32768] : List ℝ)
private def iBasis_4_6 : List ℝ := ([0, 81 / 32768, 0, -297 / 4096, 0, 27027 / 40960, 0, -11583 / 4096, 0, 109395 / 16384, 0, -37791 / 4096, 0, 61047 / 8192, 0, -66861 / 20480, 0, 19665 / 32768] : List ℝ)
private def iBasis_5_6 : List ℝ := ([-1 / 65536, 0, 81 / 65536, 0, -297 / 16384, 0, 9009 / 81920, 0, -11583 / 32768, 0, 21879 / 32768, 0, -12597 / 16384, 0, 8721 / 16384, 0, -66861 / 327680, 0, 2185 / 65536] : List ℝ)
private def iBasis_6_6 : List ℝ := ([0, -1 / 65536, 0, 27 / 65536, 0, -297 / 81920, 0, 1287 / 81920, 0, -1287 / 32768, 0, 1989 / 32768, 0, -969 / 16384, 0, 2907 / 81920, 0, -3933 / 327680, 0, 115 / 65536] : List ℝ)
private def iBasis_7_6 : List ℝ := ([1 / 9175040, 0, -1 / 131072, 0, 27 / 262144, 0, -99 / 163840, 0, 1287 / 655360, 0, -1287 / 327680, 0, 663 / 131072, 0, -969 / 229376, 0, 2907 / 1310720, 0, -437 / 655360, 0, 23 / 262144] : List ℝ)
private def iBasis_8_6 : List ℝ := ([0, 1 / 9175040, 0, -1 / 393216, 0, 27 / 1310720, 0, -99 / 1146880, 0, 143 / 655360, 0, -117 / 327680, 0, 51 / 131072, 0, -323 / 1146880, 0, 171 / 1310720, 0, -23 / 655360, 0, 23 / 5505024] : List ℝ)
private theorem iterPrim_basis_0_6 (y : ℝ) : iterPrim 0 (basisFn ⟨6, by omega⟩) y = polyEval iBasis_0_6 y := by
  dsimp only [iterPrim, basisFn, degAt]; rw [legP_eq_13 y]
  dsimp only [legList_13, iBasis_0_6, polyEval]; ring
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
private def iBasis_0_7 : List ℝ := ([0, -199485 / 2048, 0, 7912905 / 2048, 0, -90207117 / 2048, 0, 451035585 / 2048, 0, -1152646495 / 2048, 0, 1571790675 / 2048, 0, -1088162775 / 2048, 0, 300540195 / 2048] : List ℝ)
private def iBasis_1_7 : List ℝ := ([13299 / 32768, 0, -199485 / 4096, 0, 7912905 / 8192, 0, -30069039 / 4096, 0, 451035585 / 16384, 0, -230529299 / 4096, 0, 523930225 / 8192, 0, -155451825 / 4096, 0, 300540195 / 32768] : List ℝ)
private def iBasis_2_7 : List ℝ := ([0, 13299 / 32768, 0, -66495 / 4096, 0, 1582581 / 8192, 0, -4295577 / 4096, 0, 50115065 / 16384, 0, -20957209 / 4096, 0, 40302325 / 8192, 0, -10363455 / 4096, 0, 17678835 / 32768] : List ℝ)
private def iBasis_3_7 : List ℝ := ([-341 / 196608, 0, 13299 / 65536, 0, -66495 / 16384, 0, 527527 / 16384, 0, -4295577 / 32768, 0, 10023013 / 32768, 0, -20957209 / 49152, 0, 5757475 / 16384, 0, -10363455 / 65536, 0, 1964315 / 65536] : List ℝ)
private def iBasis_4_7 : List ℝ := ([0, -341 / 196608, 0, 4433 / 65536, 0, -13299 / 16384, 0, 75361 / 16384, 0, -1431859 / 98304, 0, 911183 / 32768, 0, -1612093 / 49152, 0, 1151495 / 49152, 0, -609615 / 65536, 0, 103385 / 65536] : List ℝ)
private def iBasis_5_7 : List ℝ := ([31 / 3932160, 0, -341 / 393216, 0, 4433 / 262144, 0, -4433 / 32768, 0, 75361 / 131072, 0, -1431859 / 983040, 0, 911183 / 393216, 0, -230299 / 98304, 0, 1151495 / 786432, 0, -67735 / 131072, 0, 20677 / 262144] : List ℝ)
private def iBasis_6_7 : List ℝ := ([0, 31 / 3932160, 0, -341 / 1179648, 0, 4433 / 1310720, 0, -4433 / 229376, 0, 75361 / 1179648, 0, -130169 / 983040, 0, 70091 / 393216, 0, -230299 / 1474560, 0, 67735 / 786432, 0, -3565 / 131072, 0, 20677 / 5505024] : List ℝ)
private def iBasis_7_7 : List ℝ := ([-31 / 778567680, 0, 31 / 7864320, 0, -341 / 4718592, 0, 4433 / 7864320, 0, -4433 / 1835008, 0, 75361 / 11796480, 0, -130169 / 11796480, 0, 10013 / 786432, 0, -230299 / 23592960, 0, 67735 / 14155776, 0, -713 / 524288, 0, 20677 / 121110528] : List ℝ)
private def iBasis_8_7 : List ℝ := ([0, -31 / 778567680, 0, 31 / 23592960, 0, -341 / 23592960, 0, 4433 / 55050240, 0, -4433 / 16515072, 0, 6851 / 11796480, 0, -10013 / 11796480, 0, 10013 / 11796480, 0, -13547 / 23592960, 0, 3565 / 14155776, 0, -713 / 11010048, 0, 899 / 121110528] : List ℝ)
private theorem iterPrim_basis_0_7 (y : ℝ) : iterPrim 0 (basisFn ⟨7, by omega⟩) y = polyEval iBasis_0_7 y := by
  dsimp only [iterPrim, basisFn, degAt]; rw [legP_eq_15 y]
  dsimp only [legList_15, iBasis_0_7, polyEval]; ring
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
private def iBasis_0_8 : List ℝ := ([0, 3828825 / 32768, 0, -24249225 / 4096, 0, 712927215 / 8192, 0, -2342475135 / 4096, 0, 32534376875 / 16384, 0, -15971421375 / 4096, 0, 35628555375 / 8192, 0, -10518906825 / 4096, 0, 20419054425 / 32768] : List ℝ)
private def iBasis_1_8 : List ℝ := ([-25025 / 65536, 0, 3828825 / 65536, 0, -24249225 / 16384, 0, 237642405 / 16384, 0, -2342475135 / 32768, 0, 6506875375 / 32768, 0, -5323807125 / 16384, 0, 5089793625 / 16384, 0, -10518906825 / 65536, 0, 2268783825 / 65536] : List ℝ)
private def iBasis_2_8 : List ℝ := ([0, -25025 / 65536, 0, 1276275 / 65536, 0, -4849845 / 16384, 0, 33948915 / 16384, 0, -260275015 / 32768, 0, 591534125 / 32768, 0, -409523625 / 16384, 0, 339319575 / 16384, 0, -618759225 / 65536, 0, 119409675 / 65536] : List ℝ)
private def iBasis_3_8 : List ℝ := ([1001 / 786432, 0, -25025 / 131072, 0, 1276275 / 262144, 0, -1616615 / 32768, 0, 33948915 / 131072, 0, -52055003 / 65536, 0, 591534125 / 393216, 0, -58503375 / 32768, 0, 339319575 / 262144, 0, -68751025 / 131072, 0, 23881935 / 262144] : List ℝ)
private def iBasis_4_8 : List ℝ := ([0, 1001 / 786432, 0, -25025 / 393216, 0, 255255 / 262144, 0, -230945 / 32768, 0, 11316305 / 393216, 0, -4732273 / 65536, 0, 45502625 / 393216, 0, -3900225 / 32768, 0, 19959975 / 262144, 0, -3618475 / 131072, 0, 1137235 / 262144] : List ℝ)
private def iBasis_5_8 : List ℝ := ([-7 / 1572864, 0, 1001 / 1572864, 0, -25025 / 1572864, 0, 85085 / 524288, 0, -230945 / 262144, 0, 2263261 / 786432, 0, -4732273 / 786432, 0, 6500375 / 786432, 0, -3900225 / 524288, 0, 2217775 / 524288, 0, -723695 / 524288, 0, 103385 / 524288] : List ℝ)
private def iBasis_6_8 : List ℝ := ([0, -7 / 1572864, 0, 1001 / 4718592, 0, -5005 / 1572864, 0, 12155 / 524288, 0, -230945 / 2359296, 0, 205751 / 786432, 0, -364021 / 786432, 0, 1300075 / 2359296, 0, -229425 / 524288, 0, 116725 / 524288, 0, -103385 / 1572864, 0, 4495 / 524288] : List ℝ)
private def iBasis_7_8 : List ℝ := ([7 / 415236096, 0, -7 / 3145728, 0, 1001 / 18874368, 0, -5005 / 9437184, 0, 12155 / 4194304, 0, -46189 / 4718592, 0, 205751 / 9437184, 0, -52003 / 1572864, 0, 1300075 / 37748736, 0, -76475 / 3145728, 0, 23345 / 2097152, 0, -103385 / 34603008, 0, 4495 / 12582912] : List ℝ)
private def iBasis_8_8 : List ℝ := ([0, 7 / 415236096, 0, -7 / 9437184, 0, 1001 / 94371840, 0, -715 / 9437184, 0, 12155 / 37748736, 0, -4199 / 4718592, 0, 15827 / 9437184, 0, -52003 / 23592960, 0, 76475 / 37748736, 0, -4025 / 3145728, 0, 3335 / 6291456, 0, -4495 / 34603008, 0, 899 / 62914560] : List ℝ)
private theorem iterPrim_basis_0_8 (y : ℝ) : iterPrim 0 (basisFn ⟨8, by omega⟩) y = polyEval iBasis_0_8 y := by
  dsimp only [iterPrim, basisFn, degAt]; rw [legP_eq_17 y]
  dsimp only [legList_17, iBasis_0_8, polyEval]; ring
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
private def iBasis_0_9 : List ℝ := ([0, -9006855 / 65536, 0, 567431865 / 65536, 0, -2610186579 / 16384, 0, 21751554825 / 16384, 0, -195763993425 / 32768, 0, 516105073575 / 32768, 0, -410237366175 / 16384, 0, 386795230965 / 16384, 0, -796343122575 / 65536, 0, 172308161025 / 65536] : List ℝ)
private def iBasis_1_9 : List ℝ := ([94809 / 262144, 0, -9006855 / 131072, 0, 567431865 / 262144, 0, -870062193 / 32768, 0, 21751554825 / 131072, 0, -39152798685 / 65536, 0, 172035024525 / 131072, 0, -58605338025 / 32768, 0, 386795230965 / 262144, 0, -88482569175 / 131072, 0, 34461632205 / 262144] : List ℝ)
private def iBasis_2_9 : List ℝ := ([0, 94809 / 262144, 0, -3002285 / 131072, 0, 113486373 / 262144, 0, -124294599 / 32768, 0, 2416839425 / 131072, 0, -3559345335 / 65536, 0, 13233463425 / 131072, 0, -3907022535 / 32768, 0, 22752660645 / 262144, 0, -4656977325 / 131072, 0, 1641030105 / 262144] : List ℝ)
private def iBasis_3_9 : List ℝ := ([-507 / 524288, 0, 94809 / 524288, 0, -3002285 / 524288, 0, 37828791 / 524288, 0, -124294599 / 262144, 0, 483367885 / 262144, 0, -1186448445 / 262144, 0, 1890494775 / 262144, 0, -3907022535 / 524288, 0, 2528073405 / 524288, 0, -931395465 / 524288, 0, 149184555 / 524288] : List ℝ)
private def iBasis_4_9 : List ℝ := ([0, -507 / 524288, 0, 31603 / 524288, 0, -600457 / 524288, 0, 5404113 / 524288, 0, -13810511 / 262144, 0, 43942535 / 262144, 0, -91265265 / 262144, 0, 126032985 / 262144, 0, -229824855 / 524288, 0, 133056495 / 524288, 0, -44352165 / 524288, 0, 6486285 / 524288] : List ℝ)
private def iBasis_5_9 : List ℝ := ([169 / 62914560, 0, -507 / 1048576, 0, 31603 / 2097152, 0, -600457 / 3145728, 0, 5404113 / 4194304, 0, -13810511 / 2621440, 0, 43942535 / 3145728, 0, -13037895 / 524288, 0, 126032985 / 4194304, 0, -25536095 / 1048576, 0, 26611299 / 2097152, 0, -4032015 / 1048576, 0, 2162095 / 4194304] : List ℝ)
private def iBasis_6_9 : List ℝ := ([0, 169 / 62914560, 0, -169 / 1048576, 0, 31603 / 10485760, 0, -600457 / 22020096, 0, 600457 / 4194304, 0, -1255501 / 2621440, 0, 3380195 / 3145728, 0, -869193 / 524288, 0, 7413705 / 4194304, 0, -1344005 / 1048576, 0, 8870433 / 14680064, 0, -175305 / 1048576, 0, 432419 / 20971520] : List ℝ)
private def iBasis_7_9 : List ℝ := ([-1 / 125829120, 0, 169 / 125829120, 0, -169 / 4194304, 0, 31603 / 62914560, 0, -600457 / 176160768, 0, 600457 / 41943040, 0, -1255501 / 31457280, 0, 482885 / 6291456, 0, -869193 / 8388608, 0, 823745 / 8388608, 0, -268801 / 4194304, 0, 806403 / 29360128, 0, -58435 / 8388608, 0, 33263 / 41943040] : List ℝ)
private def iBasis_8_9 : List ℝ := ([0, -1 / 125829120, 0, 169 / 377487360, 0, -169 / 20971520, 0, 31603 / 440401920, 0, -600457 / 1585446912, 0, 54587 / 41943040, 0, -96577 / 31457280, 0, 96577 / 18874368, 0, -51129 / 8388608, 0, 43355 / 8388608, 0, -268801 / 88080384, 0, 35061 / 29360128, 0, -11687 / 41943040, 0, 33263 / 1132462080] : List ℝ)
private theorem iterPrim_basis_0_9 (y : ℝ) : iterPrim 0 (basisFn ⟨9, by omega⟩) y = polyEval iBasis_0_9 y := by
  dsimp only [iterPrim, basisFn, degAt]; rw [legP_eq_19 y]
  dsimp only [legList_19, iBasis_0_9, polyEval]; ring
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
private def iBasis_0_10 : List ℝ := ([0, 41708667 / 262144, 0, -1598832235 / 131072, 0, 71947450575 / 262144, 0, -92503865025 / 32768, 0, 2086476066675 / 131072, 0, -3528041349105 / 65536, 0, 14926328784675 / 131072, 0, -4975442928225 / 32768, 0, 32486715590175 / 262144, 0, -7409250924075 / 131072, 0, 2893136075115 / 262144] : List ℝ)
private def iBasis_1_10 : List ℝ := ([-180557 / 524288, 0, 41708667 / 524288, 0, -1598832235 / 524288, 0, 23982483525 / 524288, 0, -92503865025 / 262144, 0, 417295213335 / 262144, 0, -1176013783035 / 262144, 0, 2132332683525 / 262144, 0, -4975442928225 / 524288, 0, 3609635065575 / 524288, 0, -1481850184815 / 524288, 0, 263012370465 / 524288] : List ℝ)
private def iBasis_2_10 : List ℝ := ([0, -180557 / 524288, 0, 13902889 / 524288, 0, -319766447 / 524288, 0, 3426069075 / 524288, 0, -10278207225 / 262144, 0, 37935928485 / 262144, 0, -90462598695 / 262144, 0, 142155512235 / 262144, 0, -292673113425 / 524288, 0, 189980792925 / 524288, 0, -70564294515 / 524288, 0, 11435320455 / 524288] : List ℝ)
private def iBasis_3_10 : List ℝ := ([9503 / 12582912, 0, -180557 / 1048576, 0, 13902889 / 2097152, 0, -319766447 / 3145728, 0, 3426069075 / 4194304, 0, -2055641445 / 524288, 0, 12645309495 / 1048576, 0, -12923228385 / 524288, 0, 142155512235 / 4194304, 0, -32519234825 / 1048576, 0, 37996158585 / 2097152, 0, -6414935865 / 1048576, 0, 3811773485 / 4194304] : List ℝ)
private def iBasis_4_10 : List ℝ := ([0, 9503 / 12582912, 0, -180557 / 3145728, 0, 13902889 / 10485760, 0, -45680921 / 3145728, 0, 1142023025 / 12582912, 0, -186876495 / 524288, 0, 972716115 / 1048576, 0, -861548559 / 524288, 0, 8362088955 / 4194304, 0, -1711538675 / 1048576, 0, 1809340885 / 2097152, 0, -278910255 / 1048576, 0, 762354697 / 20971520] : List ℝ)
private def iBasis_5_10 : List ℝ := ([-43 / 25165824, 0, 9503 / 25165824, 0, -180557 / 12582912, 0, 13902889 / 62914560, 0, -45680921 / 25165824, 0, 228404605 / 25165824, 0, -62292165 / 2097152, 0, 138959445 / 2097152, 0, -861548559 / 8388608, 0, 929120995 / 8388608, 0, -342307735 / 4194304, 0, 164485535 / 4194304, 0, -92970085 / 8388608, 0, 58642669 / 41943040] : List ℝ)
private def iBasis_6_10 : List ℝ := ([0, -43 / 25165824, 0, 9503 / 75497472, 0, -180557 / 62914560, 0, 1986127 / 62914560, 0, -45680921 / 226492416, 0, 20764055 / 25165824, 0, -4791705 / 2097152, 0, 9263963 / 2097152, 0, -50679327 / 8388608, 0, 48901105 / 8388608, 0, -48901105 / 12582912, 0, 7151545 / 4194304, 0, -18594017 / 41943040, 0, 58642669 / 1132462080] : List ℝ)
private def iBasis_7_10 : List ℝ := ([43 / 10569646080, 0, -43 / 50331648, 0, 9503 / 301989888, 0, -180557 / 377487360, 0, 1986127 / 503316480, 0, -45680921 / 2264924160, 0, 20764055 / 301989888, 0, -4791705 / 29360128, 0, 9263963 / 33554432, 0, -16893109 / 50331648, 0, 9780221 / 33554432, 0, -4445555 / 25165824, 0, 7151545 / 100663296, 0, -1430309 / 83886080, 0, 58642669 / 31708938240] : List ℝ)
private def iBasis_8_10 : List ℝ := ([0, 43 / 10569646080, 0, -43 / 150994944, 0, 9503 / 1509949440, 0, -180557 / 2642411520, 0, 1986127 / 4529848320, 0, -4152811 / 2264924160, 0, 1597235 / 301989888, 0, -319447 / 29360128, 0, 544939 / 33554432, 0, -889111 / 50331648, 0, 9780221 / 704643072, 0, -193285 / 25165824, 0, 1430309 / 503316480, 0, -1430309 / 2264924160, 0, 2022161 / 31708938240] : List ℝ)
private theorem iterPrim_basis_0_10 (y : ℝ) : iterPrim 0 (basisFn ⟨10, by omega⟩) y = polyEval iBasis_0_10 y := by
  dsimp only [iterPrim, basisFn, degAt]; rw [legP_eq_21 y]
  dsimp only [legList_21, iBasis_0_10, polyEval]; ring
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
private def iBasis0Q : List (List ℚ) := ([[0, 3],
    [0, -21 / 2, 0, 35 / 2],
    [0, 165 / 8, 0, -385 / 4, 0, 693 / 8],
    [0, -525 / 16, 0, 4725 / 16, 0, -10395 / 16, 0, 6435 / 16],
    [0, 5985 / 128, 0, -21945 / 32, 0, 171171 / 64, 0, -122265 / 32, 0, 230945 / 128],
    [0, -15939 / 256, 0, 345345 / 256, 0, -1036035 / 128, 0, 2516085 / 128, 0, -5311735 / 256, 0, 2028117 / 256],
    [0, 81081 / 1024, 0, -1216215 / 512, 0, 20675655 / 1024, 0, -18706545 / 256, 0, 130945815 / 1024, 0, -54759159 / 512, 0, 35102025 / 1024],
    [0, -199485 / 2048, 0, 7912905 / 2048, 0, -90207117 / 2048, 0, 451035585 / 2048, 0, -1152646495 / 2048, 0, 1571790675 / 2048, 0, -1088162775 / 2048, 0, 300540195 / 2048],
    [0, 3828825 / 32768, 0, -24249225 / 4096, 0, 712927215 / 8192, 0, -2342475135 / 4096, 0, 32534376875 / 16384, 0, -15971421375 / 4096, 0, 35628555375 / 8192, 0, -10518906825 / 4096, 0, 20419054425 / 32768],
    [0, -9006855 / 65536, 0, 567431865 / 65536, 0, -2610186579 / 16384, 0, 21751554825 / 16384, 0, -195763993425 / 32768, 0, 516105073575 / 32768, 0, -410237366175 / 16384, 0, 386795230965 / 16384, 0, -796343122575 / 65536, 0, 172308161025 / 65536],
    [0, 41708667 / 262144, 0, -1598832235 / 131072, 0, 71947450575 / 262144, 0, -92503865025 / 32768, 0, 2086476066675 / 131072, 0, -3528041349105 / 65536, 0, 14926328784675 / 131072, 0, -4975442928225 / 32768, 0, 32486715590175 / 262144, 0, -7409250924075 / 131072, 0, 2893136075115 / 262144]] : List (List ℚ))
private theorem polyEval_iBasis_0 (i : Fin 11) (y : ℝ) :
    polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y =
      ApertureLogTwo.qeval (iBasis0Q.getD i.1 []) y := by
  rcases i with ⟨iv, hiv⟩; dsimp only; interval_cases iv <;>
    (dsimp [iBasis_0_0, iBasis_0_1, iBasis_0_2, iBasis_0_3, iBasis_0_4, iBasis_0_5, iBasis_0_6, iBasis_0_7, iBasis_0_8, iBasis_0_9, iBasis_0_10, iBasis0Q, List.getD, polyEval, ApertureLogTwo.qeval]; norm_num; dsimp [polyEval]; ring)

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

private def iBasisStepQ_0 : List (List ℚ) := ([[-1, -3 / 2, 0, 1 / 2],
    [0, 7 / 8, 0, -7 / 4, 0, 7 / 8],
    [0, -11 / 16, 0, 55 / 16, 0, -77 / 16, 0, 33 / 16],
    [0, 75 / 128, 0, -175 / 32, 0, 945 / 64, 0, -495 / 32, 0, 715 / 128],
    [0, -133 / 256, 0, 1995 / 256, 0, -4389 / 128, 0, 8151 / 128, 0, -13585 / 256, 0, 4199 / 256],
    [0, 483 / 1024, 0, -5313 / 512, 0, 69069 / 1024, 0, -49335 / 256, 0, 279565 / 1024, 0, -96577 / 512, 0, 52003 / 1024],
    [0, -891 / 2048, 0, 27027 / 2048, 0, -243243 / 2048, 0, 984555 / 2048, 0, -2078505 / 2048, 0, 2380833 / 2048, 0, -1404081 / 2048, 0, 334305 / 2048],
    [0, 13299 / 32768, 0, -66495 / 4096, 0, 1582581 / 8192, 0, -4295577 / 4096, 0, 50115065 / 16384, 0, -20957209 / 4096, 0, 40302325 / 8192, 0, -10363455 / 4096, 0, 17678835 / 32768],
    [0, -25025 / 65536, 0, 1276275 / 65536, 0, -4849845 / 16384, 0, 33948915 / 16384, 0, -260275015 / 32768, 0, 591534125 / 32768, 0, -409523625 / 16384, 0, 339319575 / 16384, 0, -618759225 / 65536, 0, 119409675 / 65536],
    [0, 94809 / 262144, 0, -3002285 / 131072, 0, 113486373 / 262144, 0, -124294599 / 32768, 0, 2416839425 / 131072, 0, -3559345335 / 65536, 0, 13233463425 / 131072, 0, -3907022535 / 32768, 0, 22752660645 / 262144, 0, -4656977325 / 131072, 0, 1641030105 / 262144],
    [0, -180557 / 524288, 0, 13902889 / 524288, 0, -319766447 / 524288, 0, 3426069075 / 524288, 0, -10278207225 / 262144, 0, 37935928485 / 262144, 0, -90462598695 / 262144, 0, 142155512235 / 262144, 0, -292673113425 / 524288, 0, 189980792925 / 524288, 0, -70564294515 / 524288, 0, 11435320455 / 524288]] : List (List ℚ))
private theorem polyEval_iBasisStep_0 (j : Fin 11) (y : ℝ) :
    polyEval (match j.1 with | 0 => iBasis_2_0 | 1 => iBasis_2_1 | 2 => iBasis_2_2 | 3 => iBasis_2_3 | 4 => iBasis_2_4 | 5 => iBasis_2_5 | 6 => iBasis_2_6 | 7 => iBasis_2_7 | 8 => iBasis_2_8 | 9 => iBasis_2_9 | 10 => iBasis_2_10 | _ => []) y =
      ApertureLogTwo.qeval (iBasisStepQ_0.getD j.1 []) y := by
  rcases j with ⟨jv, hjv⟩; interval_cases jv <;>
    (dsimp [iBasis_2_0, iBasis_2_1, iBasis_2_2, iBasis_2_3, iBasis_2_4, iBasis_2_5, iBasis_2_6, iBasis_2_7, iBasis_2_8, iBasis_2_9, iBasis_2_10, iBasisStepQ_0, List.getD, polyEval, ApertureLogTwo.qeval]; norm_num; dsimp [polyEval]; ring)
private def mPPRawQ_0 : List (List ℚ) := ([[-12 / 5, 2 / 5, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [2 / 5, -28 / 45, 2 / 9, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 2 / 9, -44 / 117, 2 / 13, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 2 / 13, -60 / 221, 2 / 17, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 2 / 17, -76 / 357, 2 / 21, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 2 / 21, -92 / 525, 2 / 25, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 2 / 25, -108 / 725, 2 / 29, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 2 / 29, -124 / 957, 2 / 33, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 2 / 33, -140 / 1221, 2 / 37, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 2 / 37, -156 / 1517, 2 / 41],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 2 / 41, -172 / 1845]] : List (List ℚ))
private theorem mPPRawQ_0_ok :
    (List.range 11).all (fun i => (List.range 11).all (fun j =>
      decide (qintSymm (ApertureLogTwo.qmul (iBasis0Q.getD i []) (iBasisStepQ_0.getD j [])) =
        ApertureLogTwo.matQ mPPRawQ_0 i j))) = true := by
  decide +kernel
private theorem int_pp_0 (i j : Fin 11) :
    (∫ y in (-1 : ℝ)..1,
      polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y *
        polyEval (match j.1 with | 0 => iBasis_2_0 | 1 => iBasis_2_1 | 2 => iBasis_2_2 | 3 => iBasis_2_3 | 4 => iBasis_2_4 | 5 => iBasis_2_5 | 6 => iBasis_2_6 | 7 => iBasis_2_7 | 8 => iBasis_2_8 | 9 => iBasis_2_9 | 10 => iBasis_2_10 | _ => []) y) =
      (ApertureLogTwo.matQ mPPRawQ_0 i.1 j.1 : ℝ) := by
  simp_rw [polyEval_iBasis_0 i, polyEval_iBasisStep_0 j, integral_qeval_mul_symm]
  have h1 := List.all_eq_true.mp mPPRawQ_0_ok i.1 (List.mem_range.mpr i.2)
  have h2 := List.all_eq_true.mp h1 j.1 (List.mem_range.mpr j.2)
  exact_mod_cast of_decide_eq_true h2
private def qOddMat_0 (i j : Fin 11) : ℝ := matAt ([([-1 / 20, 1 / 120] : List ℝ),
    ([1 / 120, -7 / 540, 1 / 216] : List ℝ),
    ([0, 1 / 216, -11 / 1404, 1 / 312] : List ℝ),
    ([0, 0, 1 / 312, -5 / 884, 1 / 408] : List ℝ),
    ([0, 0, 0, 1 / 408, -19 / 4284, 1 / 504] : List ℝ),
    ([0, 0, 0, 0, 1 / 504, -23 / 6300, 1 / 600] : List ℝ),
    ([0, 0, 0, 0, 0, 1 / 600, -9 / 2900, 1 / 696] : List ℝ),
    ([0, 0, 0, 0, 0, 0, 1 / 696, -31 / 11484, 1 / 792] : List ℝ),
    ([0, 0, 0, 0, 0, 0, 0, 1 / 792, -35 / 14652, 1 / 888] : List ℝ),
    ([0, 0, 0, 0, 0, 0, 0, 0, 1 / 888, -13 / 6068, 1 / 984] : List ℝ),
    ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1 / 984, -43 / 22140] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qOddMat_0_sym (i j : Fin 11) : qOddMat_0 i j = qOddMat_0 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qOddRowAbs_0 (i : Fin 11) : ℝ := coeffAt ([7 / 120, 7 / 270, 11 / 702, 5 / 442, 19 / 2142, 23 / 3150, 9 / 1450, 31 / 5742, 35 / 7326, 13 / 3034, 131 / 44280] : List ℝ) i.1
private theorem qOddRowAbs_0_eq (i : Fin 11) :
    (∑ j : Fin 11, |qOddMat_0 i j|) = qOddRowAbs_0 i := by
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
    [2 / 2115]] : List (List ℚ))
private def gHi_0 (i : Fin 11) (r : ℕ) : ℝ := matAt ([([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([2 / 2115] : List ℝ)] : List (List ℝ)) i.1 r
private theorem gHiQ_0_ok :
    (List.range 11).all (fun i => (List.range 1).all (fun r =>
      decide (qintSymm (ApertureLogTwo.qmul (iBasisStepQ_0.getD i [])
        (ApertureLogTwo.qleg (23 + 2 * r))) =
        ApertureLogTwo.matQ gHiQ_0 i r))) = true := by
  decide +kernel
private theorem gHi_eq_0 (i : Fin 11) (r : ℕ) (hr : r ∈ Finset.range 1) :
    regionalLegendreMoment
      (polyEval (match i.1 with | 0 => iBasis_2_0 | 1 => iBasis_2_1 | 2 => iBasis_2_2 | 3 => iBasis_2_3 | 4 => iBasis_2_4 | 5 => iBasis_2_5 | 6 => iBasis_2_6 | 7 => iBasis_2_7 | 8 => iBasis_2_8 | 9 => iBasis_2_9 | 10 => iBasis_2_10 | _ => [])) (23 + 2 * r) =
      gHi_0 i r := by
  unfold regionalLegendreMoment
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  simp_rw [polyEval_iBasisStep_0 i, ApertureLogTwo.legP_eq_qeval_qleg, integral_qeval_mul_symm]
  rw [Finset.mem_range] at hr
  have h1 := List.all_eq_true.mp gHiQ_0_ok i.1 (List.mem_range.mpr i.2)
  have h2 := List.all_eq_true.mp h1 r (List.mem_range.mpr hr)
  have h3 : (qintSymm (ApertureLogTwo.qmul (iBasisStepQ_0.getD i.1 [])
      (ApertureLogTwo.qleg (23 + 2 * r))) : ℝ) =
      (ApertureLogTwo.matQ gHiQ_0 i.1 r : ℝ) := by
    exact_mod_cast of_decide_eq_true h2
  have h4 : (ApertureLogTwo.matQ gHiQ_0 i.1 r : ℝ) = gHi_0 i r := by
    rcases i with ⟨iv, hiv⟩; interval_cases iv <;> interval_cases r <;>
      norm_num [gHiQ_0, gHi_0, ApertureLogTwo.matQ, matAt, listAt, coeffAt]
  exact h3.trans h4

private def iBasisStepQ_1 : List (List ℚ) := ([[-1 / 10, -3 / 8, -1 / 2, -1 / 4, 0, 1 / 40],
    [-1 / 15, -7 / 48, 0, 7 / 48, 0, -7 / 80, 0, 1 / 48],
    [0, 11 / 384, 0, -11 / 96, 0, 11 / 64, 0, -11 / 96, 0, 11 / 384],
    [0, -3 / 256, 0, 25 / 256, 0, -35 / 128, 0, 45 / 128, 0, -55 / 256, 0, 13 / 256],
    [0, 19 / 3072, 0, -133 / 1536, 0, 399 / 1024, 0, -209 / 256, 0, 2717 / 3072, 0, -247 / 512, 0, 323 / 3072],
    [0, -23 / 6144, 0, 161 / 2048, 0, -5313 / 10240, 0, 3289 / 2048, 0, -16445 / 6144, 0, 5083 / 2048, 0, -7429 / 6144, 0, 7429 / 30720],
    [0, 81 / 32768, 0, -297 / 4096, 0, 27027 / 40960, 0, -11583 / 4096, 0, 109395 / 16384, 0, -37791 / 4096, 0, 61047 / 8192, 0, -66861 / 20480, 0, 19665 / 32768],
    [0, -341 / 196608, 0, 4433 / 65536, 0, -13299 / 16384, 0, 75361 / 16384, 0, -1431859 / 98304, 0, 911183 / 32768, 0, -1612093 / 49152, 0, 1151495 / 49152, 0, -609615 / 65536, 0, 103385 / 65536],
    [0, 1001 / 786432, 0, -25025 / 393216, 0, 255255 / 262144, 0, -230945 / 32768, 0, 11316305 / 393216, 0, -4732273 / 65536, 0, 45502625 / 393216, 0, -3900225 / 32768, 0, 19959975 / 262144, 0, -3618475 / 131072, 0, 1137235 / 262144],
    [0, -507 / 524288, 0, 31603 / 524288, 0, -600457 / 524288, 0, 5404113 / 524288, 0, -13810511 / 262144, 0, 43942535 / 262144, 0, -91265265 / 262144, 0, 126032985 / 262144, 0, -229824855 / 524288, 0, 133056495 / 524288, 0, -44352165 / 524288, 0, 6486285 / 524288],
    [0, 9503 / 12582912, 0, -180557 / 3145728, 0, 13902889 / 10485760, 0, -45680921 / 3145728, 0, 1142023025 / 12582912, 0, -186876495 / 524288, 0, 972716115 / 1048576, 0, -861548559 / 524288, 0, 8362088955 / 4194304, 0, -1711538675 / 1048576, 0, 1809340885 / 2097152, 0, -278910255 / 1048576, 0, 762354697 / 20971520]] : List (List ℚ))
private theorem polyEval_iBasisStep_1 (j : Fin 11) (y : ℝ) :
    polyEval (match j.1 with | 0 => iBasis_4_0 | 1 => iBasis_4_1 | 2 => iBasis_4_2 | 3 => iBasis_4_3 | 4 => iBasis_4_4 | 5 => iBasis_4_5 | 6 => iBasis_4_6 | 7 => iBasis_4_7 | 8 => iBasis_4_8 | 9 => iBasis_4_9 | 10 => iBasis_4_10 | _ => []) y =
      ApertureLogTwo.qeval (iBasisStepQ_1.getD j.1 []) y := by
  rcases j with ⟨jv, hjv⟩; interval_cases jv <;>
    (dsimp [iBasis_4_0, iBasis_4_1, iBasis_4_2, iBasis_4_3, iBasis_4_4, iBasis_4_5, iBasis_4_6, iBasis_4_7, iBasis_4_8, iBasis_4_9, iBasis_4_10, iBasisStepQ_1, List.getD, polyEval, ApertureLogTwo.qeval]; norm_num; dsimp [polyEval]; ring)
private def mPPRawQ_1 : List (List ℚ) := ([[-36 / 35, -8 / 45, 2 / 315, 0, 0, 0, 0, 0, 0, 0, 0],
    [-8 / 45, 28 / 495, -8 / 585, 2 / 1287, 0, 0, 0, 0, 0, 0, 0],
    [2 / 315, -8 / 585, 44 / 4095, -8 / 1989, 2 / 3315, 0, 0, 0, 0, 0, 0],
    [0, 2 / 1287, -8 / 1989, 180 / 46189, -8 / 4641, 2 / 6783, 0, 0, 0, 0, 0],
    [0, 0, 2 / 3315, -8 / 4641, 76 / 41055, -8 / 8925, 2 / 12075, 0, 0, 0, 0],
    [0, 0, 0, 2 / 6783, -8 / 8925, 92 / 89775, -8 / 15225, 2 / 19575, 0, 0, 0],
    [0, 0, 0, 0, 2 / 12075, -8 / 15225, 324 / 516925, -8 / 23925, 2 / 29667, 0, 0],
    [0, 0, 0, 0, 0, 2 / 19575, -8 / 23925, 124 / 301455, -8 / 35409, 2 / 42735, 0],
    [0, 0, 0, 0, 0, 0, 2 / 29667, -8 / 35409, 140 / 492063, -8 / 50061, 2 / 59163],
    [0, 0, 0, 0, 0, 0, 0, 2 / 42735, -8 / 50061, 468 / 2283085, -8 / 68265],
    [0, 0, 0, 0, 0, 0, 0, 0, 2 / 59163, -8 / 68265, 172 / 1127295]] : List (List ℚ))
private theorem mPPRawQ_1_ok :
    (List.range 11).all (fun i => (List.range 11).all (fun j =>
      decide (qintSymm (ApertureLogTwo.qmul (iBasis0Q.getD i []) (iBasisStepQ_1.getD j [])) =
        ApertureLogTwo.matQ mPPRawQ_1 i j))) = true := by
  decide +kernel
private theorem int_pp_1 (i j : Fin 11) :
    (∫ y in (-1 : ℝ)..1,
      polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y *
        polyEval (match j.1 with | 0 => iBasis_4_0 | 1 => iBasis_4_1 | 2 => iBasis_4_2 | 3 => iBasis_4_3 | 4 => iBasis_4_4 | 5 => iBasis_4_5 | 6 => iBasis_4_6 | 7 => iBasis_4_7 | 8 => iBasis_4_8 | 9 => iBasis_4_9 | 10 => iBasis_4_10 | _ => []) y) =
      (ApertureLogTwo.matQ mPPRawQ_1 i.1 j.1 : ℝ) := by
  simp_rw [polyEval_iBasis_0 i, polyEval_iBasisStep_1 j, integral_qeval_mul_symm]
  have h1 := List.all_eq_true.mp mPPRawQ_1_ok i.1 (List.mem_range.mpr i.2)
  have h2 := List.all_eq_true.mp h1 j.1 (List.mem_range.mpr j.2)
  exact_mod_cast of_decide_eq_true h2
private def qOddMat_1 (i j : Fin 11) : ℝ := matAt ([([3 / 800, 7 / 10800, -1 / 43200] : List ℝ),
    ([7 / 10800, -49 / 237600, 7 / 140400, -7 / 1235520] : List ℝ),
    ([-1 / 43200, 7 / 140400, -11 / 280800, 7 / 477360, -7 / 3182400] : List ℝ),
    ([0, -7 / 1235520, 7 / 477360, -21 / 1478048, 1 / 159120, -1 / 930240] : List ℝ),
    ([0, 0, -7 / 3182400, 1 / 159120, -19 / 2815200, 1 / 306000, -1 / 1656000] : List ℝ),
    ([0, 0, 0, -1 / 930240, 1 / 306000, -23 / 6156000, 1 / 522000, -7 / 18792000] : List ℝ),
    ([0, 0, 0, 0, -1 / 1656000, 1 / 522000, -189 / 82708000, 7 / 5742000, -7 / 28480320] : List ℝ),
    ([0, 0, 0, 0, 0, -7 / 18792000, 7 / 5742000, -31 / 20671200, 7 / 8498160, -1 / 5860800] : List ℝ),
    ([0, 0, 0, 0, 0, 0, -7 / 28480320, 7 / 8498160, -49 / 47238048, 7 / 12014640, -7 / 56796480] : List ℝ),
    ([0, 0, 0, 0, 0, 0, 0, -1 / 5860800, 7 / 12014640, -39 / 52184800, 7 / 16383600] : List ℝ),
    ([0, 0, 0, 0, 0, 0, 0, 0, -7 / 56796480, 7 / 16383600, -301 / 541101600] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qOddMat_1_sym (i j : Fin 11) : qOddMat_1 i j = qOddMat_1 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qOddRowAbs_1 (i : Fin 11) : ℝ := coeffAt ([191 / 43200, 511 / 561600, 77 / 596700, 1 / 23868, 19 / 994500, 23 / 2218500, 1 / 159500, 217 / 53113500, 49 / 17421228, 59759 / 30997771200, 3409 / 3080116800] : List ℝ) i.1
private theorem qOddRowAbs_1_eq (i : Fin 11) :
    (∑ j : Fin 11, |qOddMat_1 i j|) = qOddRowAbs_1 i := by
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
    [2 / 3728745, 0],
    [-8 / 4249035, 2 / 5285385]] : List (List ℚ))
private def gHi_1 (i : Fin 11) (r : ℕ) : ℝ := matAt ([([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([2 / 3728745] : List ℝ),
    ([-8 / 4249035, 2 / 5285385] : List ℝ)] : List (List ℝ)) i.1 r
private theorem gHiQ_1_ok :
    (List.range 11).all (fun i => (List.range 2).all (fun r =>
      decide (qintSymm (ApertureLogTwo.qmul (iBasisStepQ_1.getD i [])
        (ApertureLogTwo.qleg (23 + 2 * r))) =
        ApertureLogTwo.matQ gHiQ_1 i r))) = true := by
  decide +kernel
private theorem gHi_eq_1 (i : Fin 11) (r : ℕ) (hr : r ∈ Finset.range 2) :
    regionalLegendreMoment
      (polyEval (match i.1 with | 0 => iBasis_4_0 | 1 => iBasis_4_1 | 2 => iBasis_4_2 | 3 => iBasis_4_3 | 4 => iBasis_4_4 | 5 => iBasis_4_5 | 6 => iBasis_4_6 | 7 => iBasis_4_7 | 8 => iBasis_4_8 | 9 => iBasis_4_9 | 10 => iBasis_4_10 | _ => [])) (23 + 2 * r) =
      gHi_1 i r := by
  unfold regionalLegendreMoment
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  simp_rw [polyEval_iBasisStep_1 i, ApertureLogTwo.legP_eq_qeval_qleg, integral_qeval_mul_symm]
  rw [Finset.mem_range] at hr
  have h1 := List.all_eq_true.mp gHiQ_1_ok i.1 (List.mem_range.mpr i.2)
  have h2 := List.all_eq_true.mp h1 r (List.mem_range.mpr hr)
  have h3 : (qintSymm (ApertureLogTwo.qmul (iBasisStepQ_1.getD i.1 [])
      (ApertureLogTwo.qleg (23 + 2 * r))) : ℝ) =
      (ApertureLogTwo.matQ gHiQ_1 i.1 r : ℝ) := by
    exact_mod_cast of_decide_eq_true h2
  have h4 : (ApertureLogTwo.matQ gHiQ_1 i.1 r : ℝ) = gHi_1 i r := by
    rcases i with ⟨iv, hiv⟩; interval_cases iv <;> interval_cases r <;>
      norm_num [gHiQ_1, gHi_1, ApertureLogTwo.matQ, matAt, listAt, coeffAt]
  exact h3.trans h4

private def iBasisStepQ_2 : List (List ℚ) := ([[-1 / 280, -1 / 48, -1 / 20, -1 / 16, -1 / 24, -1 / 80, 0, 1 / 1680],
    [-1 / 270, -7 / 384, -1 / 30, -7 / 288, 0, 7 / 960, 0, -1 / 480, 0, 1 / 3456],
    [-1 / 945, -11 / 3840, 0, 11 / 2304, 0, -11 / 1920, 0, 11 / 2688, 0, -11 / 6912, 0, 1 / 3840],
    [0, 1 / 3072, 0, -1 / 512, 0, 5 / 1024, 0, -5 / 768, 0, 5 / 1024, 0, -1 / 512, 0, 1 / 3072],
    [0, -19 / 215040, 0, 19 / 18432, 0, -133 / 30720, 0, 19 / 2048, 0, -209 / 18432, 0, 247 / 30720, 0, -19 / 6144, 0, 323 / 645120],
    [0, 23 / 688128, 0, -23 / 36864, 0, 161 / 40960, 0, -253 / 20480, 0, 3289 / 147456, 0, -299 / 12288, 0, 391 / 24576, 0, -7429 / 1290240, 0, 437 / 491520],
    [0, -1 / 65536, 0, 27 / 65536, 0, -297 / 81920, 0, 1287 / 81920, 0, -1287 / 32768, 0, 1989 / 32768, 0, -969 / 16384, 0, 2907 / 81920, 0, -3933 / 327680, 0, 115 / 65536],
    [0, 31 / 3932160, 0, -341 / 1179648, 0, 4433 / 1310720, 0, -4433 / 229376, 0, 75361 / 1179648, 0, -130169 / 983040, 0, 70091 / 393216, 0, -230299 / 1474560, 0, 67735 / 786432, 0, -3565 / 131072, 0, 20677 / 5505024],
    [0, -7 / 1572864, 0, 1001 / 4718592, 0, -5005 / 1572864, 0, 12155 / 524288, 0, -230945 / 2359296, 0, 205751 / 786432, 0, -364021 / 786432, 0, 1300075 / 2359296, 0, -229425 / 524288, 0, 116725 / 524288, 0, -103385 / 1572864, 0, 4495 / 524288],
    [0, 169 / 62914560, 0, -169 / 1048576, 0, 31603 / 10485760, 0, -600457 / 22020096, 0, 600457 / 4194304, 0, -1255501 / 2621440, 0, 3380195 / 3145728, 0, -869193 / 524288, 0, 7413705 / 4194304, 0, -1344005 / 1048576, 0, 8870433 / 14680064, 0, -175305 / 1048576, 0, 432419 / 20971520],
    [0, -43 / 25165824, 0, 9503 / 75497472, 0, -180557 / 62914560, 0, 1986127 / 62914560, 0, -45680921 / 226492416, 0, 20764055 / 25165824, 0, -4791705 / 2097152, 0, 9263963 / 2097152, 0, -50679327 / 8388608, 0, 48901105 / 8388608, 0, -48901105 / 12582912, 0, 7151545 / 4194304, 0, -18594017 / 41943040, 0, 58642669 / 1132462080]] : List (List ℚ))
private theorem polyEval_iBasisStep_2 (j : Fin 11) (y : ℝ) :
    polyEval (match j.1 with | 0 => iBasis_6_0 | 1 => iBasis_6_1 | 2 => iBasis_6_2 | 3 => iBasis_6_3 | 4 => iBasis_6_4 | 5 => iBasis_6_5 | 6 => iBasis_6_6 | 7 => iBasis_6_7 | 8 => iBasis_6_8 | 9 => iBasis_6_9 | 10 => iBasis_6_10 | _ => []) y =
      ApertureLogTwo.qeval (iBasisStepQ_2.getD j.1 []) y := by
  rcases j with ⟨jv, hjv⟩; interval_cases jv <;>
    (dsimp [iBasis_6_0, iBasis_6_1, iBasis_6_2, iBasis_6_3, iBasis_6_4, iBasis_6_5, iBasis_6_6, iBasis_6_7, iBasis_6_8, iBasis_6_9, iBasis_6_10, iBasisStepQ_2, List.getD, polyEval, ApertureLogTwo.qeval]; norm_num; dsimp [polyEval]; ring)
private def mPPRawQ_2 : List (List ℚ) := ([[-8 / 63, -2 / 33, -4 / 1365, 2 / 45045, 0, 0, 0, 0, 0, 0, 0],
    [-2 / 33, -56 / 3861, 2 / 1755, -4 / 36465, 2 / 328185, 0, 0, 0, 0, 0, 0],
    [-4 / 1365, 2 / 1755, -88 / 208845, 10 / 88179, -4 / 208845, 2 / 1322685, 0, 0, 0, 0, 0],
    [2 / 45045, -4 / 36465, 10 / 88179, -200 / 2909907, 10 / 391391, -4 / 734825, 2 / 3900225, 0, 0, 0, 0],
    [0, 2 / 328185, -4 / 208845, 10 / 391391, -152 / 8005725, 2 / 240975, -4 / 1984325, 2 / 9454725, 0, 0, 0],
    [0, 0, 2 / 1322685, -4 / 734825, 2 / 240975, -184 / 26555445, 2 / 597835, -4 / 4521825, 2 / 20025225, 0, 0],
    [0, 0, 0, 2 / 3900225, -4 / 1984325, 2 / 597835, -24 / 7960645, 2 / 1283975, -4 / 9147325, 2 / 38418765, 0],
    [0, 0, 0, 0, 2 / 9454725, -4 / 4521825, 2 / 1283975, -248 / 167307525, 10 / 12428559, -4 / 16937305, 2 / 68333265],
    [0, 0, 0, 0, 0, 2 / 20025225, -4 / 9147325, 10 / 12428559, -1400 / 1755188721, 10 / 22243771, -4 / 29285685],
    [0, 0, 0, 0, 0, 0, 2 / 38418765, -4 / 16937305, 10 / 22243771, -104 / 226025415, 2 / 7486395],
    [0, 0, 0, 0, 0, 0, 0, 2 / 68333265, -4 / 29285685, 2 / 7486395, -344 / 1226271501]] : List (List ℚ))
private theorem mPPRawQ_2_ok :
    (List.range 11).all (fun i => (List.range 11).all (fun j =>
      decide (qintSymm (ApertureLogTwo.qmul (iBasis0Q.getD i []) (iBasisStepQ_2.getD j [])) =
        ApertureLogTwo.matQ mPPRawQ_2 i j))) = true := by
  decide +kernel
private theorem int_pp_2 (i j : Fin 11) :
    (∫ y in (-1 : ℝ)..1,
      polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y *
        polyEval (match j.1 with | 0 => iBasis_6_0 | 1 => iBasis_6_1 | 2 => iBasis_6_2 | 3 => iBasis_6_3 | 4 => iBasis_6_4 | 5 => iBasis_6_5 | 6 => iBasis_6_6 | 7 => iBasis_6_7 | 8 => iBasis_6_8 | 9 => iBasis_6_9 | 10 => iBasis_6_10 | _ => []) y) =
      (ApertureLogTwo.matQ mPPRawQ_2 i.1 j.1 : ℝ) := by
  simp_rw [polyEval_iBasis_0 i, polyEval_iBasisStep_2 j, integral_qeval_mul_symm]
  have h1 := List.all_eq_true.mp mPPRawQ_2_ok i.1 (List.mem_range.mpr i.2)
  have h2 := List.all_eq_true.mp h1 j.1 (List.mem_range.mpr j.2)
  exact_mod_cast of_decide_eq_true h2
private def qOddMat_2 (i j : Fin 11) : ℝ := matAt ([([-31 / 127008, -31 / 266112, -31 / 5503680, 31 / 363242880] : List ℝ),
    ([-31 / 266112, -31 / 1111968, 31 / 14152320, -31 / 147026880, 31 / 2646483840] : List ℝ),
    ([-31 / 5503680, 31 / 14152320, -341 / 421031520, 155 / 711075456, -31 / 842063040, 31 / 10666131840] : List ℝ),
    ([31 / 363242880, -31 / 147026880, 155 / 711075456, -775 / 5866372512, 155 / 3156177024, -31 / 2962814400, 31 / 31451414400] : List ℝ),
    ([0, 31 / 2646483840, -31 / 842063040, 155 / 3156177024, -589 / 16139541600, 31 / 1943222400, -31 / 8000798400, 31 / 76242902400] : List ℝ),
    ([0, 0, 31 / 10666131840, -31 / 2962814400, 31 / 1943222400, -713 / 53535777120, 1 / 155514240, -31 / 18231998400, 1 / 5209142400] : List ℝ),
    ([0, 0, 0, 31 / 31451414400, -31 / 8000798400, 1 / 155514240, -1 / 172566240, 31 / 10353974400, -1 / 1189742400, 1 / 9993836160] : List ℝ),
    ([0, 0, 0, 0, 31 / 76242902400, -31 / 18231998400, 31 / 10353974400, -961 / 337291970400, 155 / 100223899776, -31 / 68291213760, 31 / 551039448960] : List ℝ),
    ([0, 0, 0, 0, 0, 1 / 5209142400, -1 / 1189742400, 155 / 100223899776, -25 / 16306269408, 5 / 5786250624, -31 / 118079881920] : List ℝ),
    ([0, 0, 0, 0, 0, 0, 1 / 9993836160, -31 / 68291213760, 5 / 5786250624, -403 / 455667236640, 31 / 60370289280] : List ℝ),
    ([0, 0, 0, 0, 0, 0, 0, 31 / 551039448960, -31 / 118079881920, 31 / 60370289280, -1333 / 2472163346016] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qOddMat_2_sym (i j : Fin 11) : qOddMat_2 i j = qOddMat_2 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qOddRowAbs_2 (i : Fin 11) : ℝ := coeffAt ([33263 / 90810720, 129487 / 882161280, 713 / 80196480, 31 / 43857450, 589 / 3815598150, 713 / 13990526550, 31 / 1474784850, 961 / 96034519350, 7713947 / 1472456127542400, 999409 / 354899682023040, 372961 / 271937968061760] : List ℝ) i.1
private theorem qOddRowAbs_2_eq (i : Fin 11) :
    (∑ j : Fin 11, |qOddMat_2 i j|) = qOddRowAbs_2 i := by
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
    [2 / 5380579035, 0, 0],
    [-4 / 2253404895, 2 / 9318133755, 0],
    [2 / 563422041, -4 / 3828380535, 2 / 15406897275]] : List (List ℚ))
private def gHi_2 (i : Fin 11) (r : ℕ) : ℝ := matAt ([([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([2 / 5380579035] : List ℝ),
    ([-4 / 2253404895, 2 / 9318133755] : List ℝ),
    ([2 / 563422041, -4 / 3828380535, 2 / 15406897275] : List ℝ)] : List (List ℝ)) i.1 r
private theorem gHiQ_2_ok :
    (List.range 11).all (fun i => (List.range 3).all (fun r =>
      decide (qintSymm (ApertureLogTwo.qmul (iBasisStepQ_2.getD i [])
        (ApertureLogTwo.qleg (23 + 2 * r))) =
        ApertureLogTwo.matQ gHiQ_2 i r))) = true := by
  decide +kernel
private theorem gHi_eq_2 (i : Fin 11) (r : ℕ) (hr : r ∈ Finset.range 3) :
    regionalLegendreMoment
      (polyEval (match i.1 with | 0 => iBasis_6_0 | 1 => iBasis_6_1 | 2 => iBasis_6_2 | 3 => iBasis_6_3 | 4 => iBasis_6_4 | 5 => iBasis_6_5 | 6 => iBasis_6_6 | 7 => iBasis_6_7 | 8 => iBasis_6_8 | 9 => iBasis_6_9 | 10 => iBasis_6_10 | _ => [])) (23 + 2 * r) =
      gHi_2 i r := by
  unfold regionalLegendreMoment
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  simp_rw [polyEval_iBasisStep_2 i, ApertureLogTwo.legP_eq_qeval_qleg, integral_qeval_mul_symm]
  rw [Finset.mem_range] at hr
  have h1 := List.all_eq_true.mp gHiQ_2_ok i.1 (List.mem_range.mpr i.2)
  have h2 := List.all_eq_true.mp h1 r (List.mem_range.mpr hr)
  have h3 : (qintSymm (ApertureLogTwo.qmul (iBasisStepQ_2.getD i.1 [])
      (ApertureLogTwo.qleg (23 + 2 * r))) : ℝ) =
      (ApertureLogTwo.matQ gHiQ_2 i.1 r : ℝ) := by
    exact_mod_cast of_decide_eq_true h2
  have h4 : (ApertureLogTwo.matQ gHiQ_2 i.1 r : ℝ) = gHi_2 i r := by
    rcases i with ⟨iv, hiv⟩; interval_cases iv <;> interval_cases r <;>
      norm_num [gHiQ_2, gHi_2, ApertureLogTwo.matQ, matAt, listAt, coeffAt]
  exact h3.trans h4

private def iBasisStepQ_3 : List (List ℚ) := ([[-1 / 15120, -1 / 1920, -1 / 560, -1 / 288, -1 / 240, -1 / 320, -1 / 720, -1 / 3360, 0, 1 / 120960],
    [-1 / 11880, -7 / 11520, -1 / 540, -7 / 2304, -1 / 360, -7 / 5760, 0, 1 / 5760, 0, -1 / 34560, 0, 1 / 380160],
    [-1 / 24570, -11 / 46080, -1 / 1890, -11 / 23040, 0, 11 / 46080, 0, -11 / 80640, 0, 11 / 193536, 0, -1 / 69120, 0, 1 / 599040],
    [-1 / 135135, -1 / 43008, 0, 1 / 18432, 0, -1 / 10240, 0, 5 / 43008, 0, -5 / 55296, 0, 1 / 22528, 0, -1 / 79872, 0, 1 / 645120],
    [0, 19 / 10321920, 0, -19 / 1290240, 0, 19 / 368640, 0, -19 / 184320, 0, 19 / 147456, 0, -19 / 184320, 0, 19 / 368640, 0, -19 / 1290240, 0, 19 / 10321920],
    [0, -23 / 61931520, 0, 23 / 4128768, 0, -23 / 737280, 0, 23 / 245760, 0, -253 / 1474560, 0, 299 / 1474560, 0, -23 / 147456, 0, 391 / 5160960, 0, -437 / 20643840, 0, 23 / 8847360],
    [0, 1 / 9175040, 0, -1 / 393216, 0, 27 / 1310720, 0, -99 / 1146880, 0, 143 / 655360, 0, -117 / 327680, 0, 51 / 131072, 0, -323 / 1146880, 0, 171 / 1310720, 0, -23 / 655360, 0, 23 / 5505024],
    [0, -31 / 778567680, 0, 31 / 23592960, 0, -341 / 23592960, 0, 4433 / 55050240, 0, -4433 / 16515072, 0, 6851 / 11796480, 0, -10013 / 11796480, 0, 10013 / 11796480, 0, -13547 / 23592960, 0, 3565 / 14155776, 0, -713 / 11010048, 0, 899 / 121110528],
    [0, 7 / 415236096, 0, -7 / 9437184, 0, 1001 / 94371840, 0, -715 / 9437184, 0, 12155 / 37748736, 0, -4199 / 4718592, 0, 15827 / 9437184, 0, -52003 / 23592960, 0, 76475 / 37748736, 0, -4025 / 3145728, 0, 3335 / 6291456, 0, -4495 / 34603008, 0, 899 / 62914560],
    [0, -1 / 125829120, 0, 169 / 377487360, 0, -169 / 20971520, 0, 31603 / 440401920, 0, -600457 / 1585446912, 0, 54587 / 41943040, 0, -96577 / 31457280, 0, 96577 / 18874368, 0, -51129 / 8388608, 0, 43355 / 8388608, 0, -268801 / 88080384, 0, 35061 / 29360128, 0, -11687 / 41943040, 0, 33263 / 1132462080],
    [0, 43 / 10569646080, 0, -43 / 150994944, 0, 9503 / 1509949440, 0, -180557 / 2642411520, 0, 1986127 / 4529848320, 0, -4152811 / 2264924160, 0, 1597235 / 301989888, 0, -319447 / 29360128, 0, 544939 / 33554432, 0, -889111 / 50331648, 0, 9780221 / 704643072, 0, -193285 / 25165824, 0, 1430309 / 503316480, 0, -1430309 / 2264924160, 0, 2022161 / 31708938240]] : List (List ℚ))
private theorem polyEval_iBasisStep_3 (j : Fin 11) (y : ℝ) :
    polyEval (match j.1 with | 0 => iBasis_8_0 | 1 => iBasis_8_1 | 2 => iBasis_8_2 | 3 => iBasis_8_3 | 4 => iBasis_8_4 | 5 => iBasis_8_5 | 6 => iBasis_8_6 | 7 => iBasis_8_7 | 8 => iBasis_8_8 | 9 => iBasis_8_9 | 10 => iBasis_8_10 | _ => []) y =
      ApertureLogTwo.qeval (iBasisStepQ_3.getD j.1 []) y := by
  rcases j with ⟨jv, hjv⟩; interval_cases jv <;>
    (dsimp [iBasis_8_0, iBasis_8_1, iBasis_8_2, iBasis_8_3, iBasis_8_4, iBasis_8_5, iBasis_8_6, iBasis_8_7, iBasis_8_8, iBasis_8_9, iBasis_8_10, iBasisStepQ_3, List.getD, polyEval, ApertureLogTwo.qeval]; norm_num; dsimp [polyEval]; ring)
private def mPPRawQ_3 : List (List ℚ) := ([[-4 / 495, -112 / 19305, -8 / 8775, -16 / 765765, 2 / 11486475, 0, 0, 0, 0, 0, 0],
    [-112 / 19305, -196 / 57915, -112 / 447525, 56 / 6235515, -16 / 34459425, 2 / 130945815, 0, 0, 0, 0, 0],
    [-8 / 8775, -112 / 447525, 44 / 1700595, -16 / 3968055, 8 / 14410305, -16 / 297604125, 2 / 760543875, 0, 0, 0, 0],
    [-16 / 765765, 56 / 6235515, -16 / 3968055, 100 / 66927861, -16 / 37741275, 8 / 93532725, -16 / 1470384825, 2 / 3053876175, 0, 0, 0],
    [2 / 11486475, -16 / 34459425, 8 / 14410305, -16 / 37741275, 76 / 339671475, -16 / 194673375, 8 / 395447625, -16 / 5304100725, 2 / 9672183675, 0, 0],
    [0, 2 / 130945815, -16 / 297604125, 8 / 93532725, -16 / 194673375, 92 / 1764040275, -16 / 718683075, 8 / 1288720125, -16 / 15559599825, 2 / 25932666375, 0],
    [0, 0, 2 / 760543875, -16 / 1470384825, 8 / 395447625, -16 / 718683075, 12 / 756261275, -16 / 2137818375, 56 / 24615451575, -16 / 39379234125, 2 / 61431605235],
    [0, 0, 0, 2 / 3053876175, -16 / 5304100725, 8 / 1288720125, -16 / 2137818375, 124 / 21439264275, -112 / 38217818925, 8 / 8427519045, -16 / 89174910825],
    [0, 0, 0, 0, 2 / 9672183675, -16 / 15559599825, 56 / 24615451575, -112 / 38217818925, 4900 / 2037774105081, -112 / 87084363465, 56 / 128007729135],
    [0, 0, 0, 0, 0, 2 / 25932666375, -16 / 39379234125, 8 / 8427519045, -112 / 87084363465, 52 / 47045575665, -16 / 25940358675],
    [0, 0, 0, 0, 0, 0, 2 / 61431605235, -16 / 89174910825, 56 / 128007729135, -16 / 25940358675, 172 / 312699232755]] : List (List ℚ))
private theorem mPPRawQ_3_ok :
    (List.range 11).all (fun i => (List.range 11).all (fun j =>
      decide (qintSymm (ApertureLogTwo.qmul (iBasis0Q.getD i []) (iBasisStepQ_3.getD j [])) =
        ApertureLogTwo.matQ mPPRawQ_3 i j))) = true := by
  decide +kernel
private theorem int_pp_3 (i j : Fin 11) :
    (∫ y in (-1 : ℝ)..1,
      polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y *
        polyEval (match j.1 with | 0 => iBasis_8_0 | 1 => iBasis_8_1 | 2 => iBasis_8_2 | 3 => iBasis_8_3 | 4 => iBasis_8_4 | 5 => iBasis_8_5 | 6 => iBasis_8_6 | 7 => iBasis_8_7 | 8 => iBasis_8_8 | 9 => iBasis_8_9 | 10 => iBasis_8_10 | _ => []) y) =
      (ApertureLogTwo.matQ mPPRawQ_3 i.1 j.1 : ℝ) := by
  simp_rw [polyEval_iBasis_0 i, polyEval_iBasisStep_3 j, integral_qeval_mul_symm]
  have h1 := List.all_eq_true.mp mPPRawQ_3_ok i.1 (List.mem_range.mpr i.2)
  have h2 := List.all_eq_true.mp h1 j.1 (List.mem_range.mpr j.2)
  exact_mod_cast of_decide_eq_true h2
private def qOddMat_3 (i j : Fin 11) : ℝ := matAt ([([127 / 7603200, 889 / 74131200, 127 / 67392000, 127 / 2940537600, -127 / 352864512000] : List ℝ),
    ([889 / 74131200, 6223 / 889574400, 889 / 1718496000, -889 / 47888755200, 127 / 132324192000, -127 / 4022655436800] : List ℝ),
    ([127 / 67392000, 889 / 1718496000, -1397 / 26121139200, 127 / 15237331200, -127 / 110671142400, 127 / 1142799840000, -127 / 23363907840000] : List ℝ),
    ([127 / 2940537600, -889 / 47888755200, 127 / 15237331200, -635 / 205602388992, 127 / 144926496000, -127 / 718331328000, 127 / 5646277728000, -127 / 93815076096000] : List ℝ),
    ([-127 / 352864512000, 127 / 132324192000, -127 / 110671142400, 127 / 144926496000, -2413 / 5217353856000, 127 / 747545760000, -127 / 3037037760000, 127 / 20367746784000, -127 / 297129482496000] : List ℝ),
    ([0, -127 / 4022655436800, 127 / 1142799840000, -127 / 718331328000, 127 / 747545760000, -2921 / 27095658624000, 127 / 2759743008000, -127 / 9897370560000, 127 / 59748863328000, -127 / 796651511040000] : List ℝ),
    ([0, 0, -127 / 23363907840000, 127 / 5646277728000, -127 / 3037037760000, 127 / 2759743008000, -127 / 3872057728000, 127 / 8209222560000, -889 / 189046668096000, 127 / 151216259040000, -127 / 1887178912819200] : List ℝ),
    ([0, 0, 0, -127 / 93815076096000, 127 / 20367746784000, -127 / 9897370560000, 127 / 8209222560000, -3937 / 329307099264000, 889 / 146756424672000, -127 / 64723346265600, 127 / 342431657568000] : List ℝ),
    ([0, 0, 0, 0, -127 / 297129482496000, 127 / 59748863328000, -889 / 189046668096000, 889 / 146756424672000, -31115 / 6260042050808832, 889 / 334403955705600, -889 / 983099359756800] : List ℝ),
    ([0, 0, 0, 0, 0, -127 / 796651511040000, 127 / 151216259040000, -127 / 64723346265600, 889 / 334403955705600, -1651 / 722620042214400, 127 / 99610977312000] : List ℝ),
    ([0, 0, 0, 0, 0, 0, -127 / 1887178912819200, 127 / 342431657568000, -889 / 983099359756800, 127 / 99610977312000, -5461 / 4803060215116800] : List ℝ)] : List (List ℝ)) i.1 j.1
private theorem qOddMat_3_sym (i j : Fin 11) : qOddMat_3 i j = qOddMat_3 j i := by
  rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
  interval_cases iv <;> interval_cases jv <;> rfl
private def qOddRowAbs_3 (i : Fin 11) : ℝ := coeffAt ([10806049 / 352864512000, 375793 / 19247155200, 395351 / 160392960000, 759841 / 10233070848000, 2413 / 599593995000, 2921 / 4436995563000, 127 / 748628881000, 51189763 / 910245606117120000, 10995533 / 503312276323584000, 15203297 / 1656198516107520000, 11504803 / 3064352417244518400] : List ℝ) i.1
private theorem qOddRowAbs_3_eq (i : Fin 11) :
    (∑ j : Fin 11, |qOddMat_3 i j|) = qOddRowAbs_3 i := by
  rcases i with ⟨iv, hiv⟩; interval_cases iv <;>
    (rw [sum_finK]; dsimp only [qOddMat_3, qOddRowAbs_3, matAt, listAt, coeffAt]; norm_num)
private def gHiQ_3 : List (List ℚ) := ([[0, 0, 0, 0],
    [0, 0, 0, 0],
    [0, 0, 0, 0],
    [0, 0, 0, 0],
    [0, 0, 0, 0],
    [0, 0, 0, 0],
    [0, 0, 0, 0],
    [2 / 6214568785425, 0, 0, 0],
    [-16 / 8700396299595, 2 / 13446067008465, 0, 0],
    [8 / 1723854744675, -16 / 18272860293555, 2 / 27162359895825, 0],
    [-16 / 2367579905145, 8 / 3519375534675, -16 / 36005918931675, 2 / 51813395535825]] : List (List ℚ))
private def gHi_3 (i : Fin 11) (r : ℕ) : ℝ := matAt ([([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([] : List ℝ),
    ([2 / 6214568785425] : List ℝ),
    ([-16 / 8700396299595, 2 / 13446067008465] : List ℝ),
    ([8 / 1723854744675, -16 / 18272860293555, 2 / 27162359895825] : List ℝ),
    ([-16 / 2367579905145, 8 / 3519375534675, -16 / 36005918931675, 2 / 51813395535825] : List ℝ)] : List (List ℝ)) i.1 r
private theorem gHiQ_3_ok :
    (List.range 11).all (fun i => (List.range 4).all (fun r =>
      decide (qintSymm (ApertureLogTwo.qmul (iBasisStepQ_3.getD i [])
        (ApertureLogTwo.qleg (23 + 2 * r))) =
        ApertureLogTwo.matQ gHiQ_3 i r))) = true := by
  decide +kernel
private theorem gHi_eq_3 (i : Fin 11) (r : ℕ) (hr : r ∈ Finset.range 4) :
    regionalLegendreMoment
      (polyEval (match i.1 with | 0 => iBasis_8_0 | 1 => iBasis_8_1 | 2 => iBasis_8_2 | 3 => iBasis_8_3 | 4 => iBasis_8_4 | 5 => iBasis_8_5 | 6 => iBasis_8_6 | 7 => iBasis_8_7 | 8 => iBasis_8_8 | 9 => iBasis_8_9 | 10 => iBasis_8_10 | _ => [])) (23 + 2 * r) =
      gHi_3 i r := by
  unfold regionalLegendreMoment
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  simp_rw [polyEval_iBasisStep_3 i, ApertureLogTwo.legP_eq_qeval_qleg, integral_qeval_mul_symm]
  rw [Finset.mem_range] at hr
  have h1 := List.all_eq_true.mp gHiQ_3_ok i.1 (List.mem_range.mpr i.2)
  have h2 := List.all_eq_true.mp h1 r (List.mem_range.mpr hr)
  have h3 : (qintSymm (ApertureLogTwo.qmul (iBasisStepQ_3.getD i.1 [])
      (ApertureLogTwo.qleg (23 + 2 * r))) : ℝ) =
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

private def poleA0 : ℝ := (6931471805599453094172321 / 10000000000000000000000000 : ℝ)
private def vPoleTrue (k : Fin 11) : ℝ := coeffAt ([177793716928406792974401851898804139668246697060236358922688262398500413031449933112875000261934031962311709998691978076194065016971730485947875701173999716374125058031009530956461344012760192607189248065290184998790229534555581890522417213091321192132059781432977622022134506706404021987952783311108961168834362048176261591570509123755127140190424837833207454188416749545326392053305379992354049805207718714334777441334021784827161756873778667254262434556166109407799189681997739350912399937568017050717666137268262404594418151701226553029301063 / 506889635092234240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 3287457497320043609310744164548096295322628700533056051514155858760837302767750049743086670952322845883905292410150646087232897073211070505818262751250464514917329036371462071058944505773962323485057553243055427667754928992089780766085590718100560242246602344098365674844035896366690617717034389836909112369178402318355712110069596070343950564794186175688436637886465929534225102386951636160201215625584158567236393705261756559748417199043208460952421029369390413626580866230660277996023566182740553109886594829137086575811990705315063126971273 / 1176708081464115200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1990193594309490022182488968517185803539429186979405168225759642124740673098487874759081748208301458907135023605666477699095495651311741544715855877292812209973345571280432958374059710323316667408778805800555694631157388314121744239174362861971619770721303207833631235669642293255716150136794558522930239799297456181589063485248024019702504110629641224513283027003260167116423852382465594856858246677066033750716215226968758090389761739837409139929781379546592440248968621160613757382157427046851036628864943045695525270663568438354375657091 / 374407116829491200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 6658542385524564821534341509444276396822054801332365443256319133718839375164600196972484646225453583324053630670177816596029836847511052580218542015096262092185455231537920617725864027256338892521434361580119685112702320367333507847656304029938396440567145768606699248319720753617448477675824924492351079615238702425205806791353132494813030203410051082463217613916646212260250079032002370159810581972780042576904277790257371248938302983321205988021027555524878986740888668543782101781089940553109886594829137086575811990705315063126971273 / 1492948378357596160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 4957279820691869704400578739861077579965302066339803642070990483504641835115214044462390875512131267517748750094755457436178862807785107805972214784676756290352880933663769392746915858598964014401875016758231633307375828955306863211520853639133971735187398769712008494229925624172126807373034229454703579331332679844646023792166967762978875022538531088282750357898596016570186409972411964066566131909303176703269854057237348965103906117329015435270791212844033669277056539285328588551127167099421204845409744997163229685761247591069247 / 2361295904545177600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 13719058693898052433274961264003806560078549643497991002658990462338892973822486795056899718764990044285555747193670266120598122216314191974917974336845446831742850021913417887946908331884134968630069301641746174469829365502843958967578413487438865970998322710617344253303872455188202192283581075979485993003556079401222896903033080754692022449094229161290449105574963243060645467175671471590979599486688364087166020395512360784544947746800224045370591896292297128708302210657900508207154248668845527974676101875423828992905227001 / 21717604473241600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 20986538071431555876565196935621755461878293330630224635364084199262436244827169265312334301938335218808241245014901242426164518954103854112783114426034242696684104704513708772769600911340077906534789637285629940820802023759060100236622996390397159765412480762250700909923486881869478724789792093015511076497403367068097178604541670556009335663665522477461017564789605023469658171421898674178259517059641104659778526013700944693098298096019710709636643341164865775380434659114008664977988979353462233779182307916347835568142741457 / 159092311568731340800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 36937514214002301672657337821166575441381298349318974180566183650522147245124657461623360155202420726666992050509331314018895646234173221362869421562540432203466933994216934445483479597315076638495083946037950843741948468306628143574806335995764375287084889474530469189518972729648310051793672148131871533084344268147532310330387596316364070530126658142779428841769108148539829074163887747066496936771941735895228057546043655629207342302048265480838052177258121696416590857157450079740681918695822732713127966802950336589007 / 1825811268003430400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 324524796866946304703556267134021309927065294561017444384744272341538484324506413563779040050894123790220505502003335468809031838694111570333159718322186873659195477263949165324664683358381613745764260913863207138616958649878491170728905049904540480679637345122945490071180180131351641441906235263054009178057975113632409329755060152301853147928791904056875801305873337211774493243826031478067095319324734364254985389867433306478945755710006877097615633359714946454788596646851036628864943045695525270663568438354375657091 / 136648931900999598080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 830516753059362864920942556336923608968798178255229945665120184095581987634790694617042159741126272224274755010533991064518994011362313685689579569509608798868681517608778294426322542111791313685702579969835069127184636441303826764658807818961268151514541716899377340562899692854780032709180220125186105258350337059374958345674487910919127357722572692254942997848968063524163558036349876711990630149092858116489303882797618617686874044071373975454279456682752314090861140553109886594829137086575811990705315063126971273 / 3770984947652585062400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 404919352588307869926101198210447694321482406728214634223449091269348012569070422948318644065300946014641092311902666298096091678158731276986560925306217023383124323847114326004531587940825605683305194492920572779733655705582095862280896425100005093129527800244459078717452370623041868312637246135125967891582787122069395179300693073607557381191918415096480934424681223696735286852856728408025681181925873456138811540878876299533541501993577285683733119966365406214246851036628864943045695525270663568438354375657091 / 24511402159741802905600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000] : List ℝ) k.1
private def vPoleClean (k : Fin 11) : ℝ := coeffAt ([350754295648707113706335787047 / 1000000000000000000000000000000, 1396887447747293160185790861 / 500000000000000000000000000000, 5315586976985387750852757 / 1000000000000000000000000000000, 4459995055455084004307 / 1000000000000000000000000000000, 1049694748368845173 / 500000000000000000000000000000, 631702207801113 / 1000000000000000000000000000000, 515289919 / 3906250000000000000000000000, 20230741 / 1000000000000000000000000000000, 19 / 8000000000000000000000000000] : List ℝ) k.1
private def bFastQ : List (List ℚ) := ([[903415056013080536256233959291620219981105599177176350917245699267988660633437386930924409711981500783098511445839449503452620568287940873631 / 105411381075000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -6952027539210458301990695946165517168624049084328737259349980230306128089973932150017778157748470197051660444744595161189022068498429407 / 2509794787500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 122112201574806371707566022763659164220474719581029487393335067852603242831359920024649725631100336621871294914714734446424017384052317 / 3194284275000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -149143640387401307480547981803916253454185595096262353187613453054163337627781473112888436357605725850992019161135324564108655735086809 / 339658894575000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 100891396522319225454373718630582618285068159222186897506616656391603978337564821374678309561875197395050667985803275441699620750847 / 16964703112500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -4723933408255230225658069702675431029334061439570315187319370617505961666896335006500171434945239807644868080249495758355873932501 / 65400159825000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 39688474103731147045594637590259263267362541278045575231317591437656350221428894805167811844285118129504448262158607822354703 / 50220475292968750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -166032069942831231011869675151372168197759694517730648602079464656411622513415577015295953955611716126039376392181663147262167 / 19729009575000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 121442866081305770495381600010867867414417249908034032928911836758795744770577218935106261353388148519173573263497059163797 / 415727626600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 51971921392123252872677385717300261302859749 / 2070222594000000000000000000000000000000000000000000000000000, 25053851665633920884899324716161608191011 / 81554223400000000000000000000000000000000000000000000000000],
    [-6952027539210458301990695946165517168624049084328737259349980230306128089973932150017778157748470197051660444744595161189022068498429407 / 2509794787500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 8792014015962070145425333570247817791173998216174949320505997505359241490032168112445512604158129743016543796150543620369693340935417336243 / 664357443750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -1533835430989617082752743143317014224125229677850959303214497831782954307628233013913224051951323796362163871734769908686467946921486341 / 684489487500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 333537856844660656805652798916503641049733130087504484400403000364371029646944611082168821542828279394390977277314685848271773489503 / 228163162500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -2176214103403277718355860060573395318471607494190549445942630504868584971599819855345900813438590735330729754692168625902693348459 / 522373556250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 16002978870006382345113508483264943187230805323836126678001074589190455271161101630350074915494363844288339523706568949450808037633 / 294300719212500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -41007635359942589921034301492256113240475205501667772201298158492798511475420560059169217554231656184941305863491473205251849 / 46633298486328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 566225831840676416424273564694152795986607013767221343150678112446009744082255600374929248188563384621963610378761165543653 / 47048512500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 854436011301460258068359892436812085582970240123340585061965450361877903074239276497473950644781853968129174535285677139 / 2524661700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 25053851665633920884899324716161608191011 / 765049000000000000000000000000000000000000000000000000000, 0],
    [122112201574806371707566022763659164220474719581029487393335067852603242831359920024649725631100336621871294914714734446424017384052317 / 3194284275000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -1533835430989617082752743143317014224125229677850959303214497831782954307628233013913224051951323796362163871734769908686467946921486341 / 684489487500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 151789974673617196030780072759209421740308554281681317389229467810509486637621397326415511682904531117871301360676625325968994224839073217381 / 9582852825000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -4929852831607812145296706147181385633615908026531614557608653753375829434634968480987610136937169983878751958293184847502032427424573823 / 3194284275000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 129186371933596327597800532269041257240702098854854859268701854010560631166623747572117213991629098475147165527123312926664821507911 / 252180337500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -4087911245129799073283726864611890057990143919534280408160377681836690367932457231126006796179137018215137563683608796245419971933 / 12082727475000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 277006323340083068640507414544255061079563659125826415959234513594495673044012069121612488727720697065396061067283226249329971 / 534163237207031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -30131001399532850947118438576093385645811915168189249050708013965086843094587959250784823562163390056314107653664498086023 / 5852925000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 25053851665633922187647063231554494427491751874792459668957197087007042641535153386825306252958263967434041996796235847 / 37218600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0, 0],
    [-149143640387401307480547981803916253454185595096262353187613453054163337627781473112888436357605725850992019161135324564108655735086809 / 339658894575000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 333537856844660656805652798916503641049733130087504484400403000364371029646944611082168821542828279394390977277314685848271773489503 / 228163162500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -4929852831607812145296706147181385633615908026531614557608653753375829434634968480987610136937169983878751958293184847502032427424573823 / 3194284275000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 17276111998079350365158300806562997803364947700231028766601077115343307128622641783584429197567155784910041315727148178053250885309092097761913 / 1018976683725000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -99109994509789889442145138041853634821511002446066084060391699666484626431908338043711966121509472628275048325098730078128340522943813 / 84060112500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1142644307675169394959282555307351122841311590949620888431276971007951095732420483514649926105758584336263960895063280844521663626803 / 4583103525000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -48899634867626527213290166466385136806850106803980071038506282848055577515339869181511153996344743585721443817911983757433009131 / 442264185644531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 3054896200960827720167112242303398242352370573784932875875922148532022249270039827449137375984431078191370370003950066736598641 / 39700390275000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 5873722696199977970650529664288572601890698672981450723652168026184450792854303202186983689429 / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0, 0],
    [100891396522319225454373718630582618285068159222186897506616656391603978337564821374678309561875197395050667985803275441699620750847 / 16964703112500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -2176214103403277718355860060573395318471607494190549445942630504868584971599819855345900813438590735330729754692168625902693348459 / 522373556250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 129186371933596327597800532269041257240702098854854859268701854010560631166623747572117213991629098475147165527123312926664821507911 / 252180337500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -99109994509789889442145138041853634821511002446066084060391699666484626431908338043711966121509472628275048325098730078128340522943813 / 84060112500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 63547733562263959905985816101684173610908329166058559474684418889692815153516916040309410127379636278567288829827458807050124768393405940993493 / 3740717036306250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -10010598767237209732820028792123443494550871549854980125312460157011437139966461605688774835610670167400694522494018668171376463410305359 / 10492894912500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 13758582207116501207925016585200814865832427701351626937183393487721140383924054820025616565179121273761454538318367590391268430407 / 98398491064453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -843301738919941286338521707982155926321039430537095155218875933672443456682850567744431579274191555636134356844517242415126048873 / 18564352537500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 881142581732871835139321150739849887248855881543290955575134032293788312579365066344743262020960395561794248646252120094457 / 38688734700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0, 0],
    [-4723933408255230225658069702675431029334061439570315187319370617505961666896335006500171434945239807644868080249495758355873932501 / 65400159825000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 16002978870006382345113508483264943187230805323836126678001074589190455271161101630350074915494363844288339523706568949450808037633 / 294300719212500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -4087911245129799073283726864611890057990143919534280408160377681836690367932457231126006796179137018215137563683608796245419971933 / 12082727475000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1142644307675169394959282555307351122841311590949620888431276971007951095732420483514649926105758584336263960895063280844521663626803 / 4583103525000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -10010598767237209732820028792123443494550871549854980125312460157011437139966461605688774835610670167400694522494018668171376463410305359 / 10492894912500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 7396533662353108938199319389394926799769279778833552910227097395821119445554080523121242320558698193708332074878195633879454664227880255242636453 / 457343317656225000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -110213136604114893370035123770919718946006711096656877319776643782099581417773577392026857395492280716844370684118586519393363325986103 / 137560432324218750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 155477793878354836850366410995324265088553078412440044030993038129178811701833101306221674401201633183201714620546576410458740033183 / 1804208175000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -2664275685489031942023131807204075964515516574228237748938967861305948090002503988514761057808169449642908944012008237910273177 / 124476798600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 451145001847230379591332155339 / 53110100736000000000000000000000000000000000, 0],
    [39688474103731147045594637590259263267362541278045575231317591437656350221428894805167811844285118129504448262158607822354703 / 50220475292968750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -41007635359942589921034301492256113240475205501667772201298158492798511475420560059169217554231656184941305863491473205251849 / 46633298486328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 277006323340083068640507414544255061079563659125826415959234513594495673044012069121612488727720697065396061067283226249329971 / 534163237207031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -48899634867626527213290166466385136806850106803980071038506282848055577515339869181511153996344743585721443817911983757433009131 / 442264185644531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 13758582207116501207925016585200814865832427701351626937183393487721140383924054820025616565179121273761454538318367590391268430407 / 98398491064453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -110213136604114893370035123770919718946006711096656877319776643782099581417773577392026857395492280716844370684118586519393363325986103 / 137560432324218750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1190868409431806791902143096755799353688005666500872934350950156202573581670643030599405336688761224517048900982696460393681744087999918460171 / 81243585384005355834960937500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -8073796056053378695542544579293162315163127490473679638406329903636134953412852932541834758835589400910470360884353015910817142156117 / 11691194238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 306003064462076728530259845734660930363564032972623577150116900441321414642610224393003634925086756106380938131363756608751808113 / 5384630032031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -786273500212451662740721377493573 / 70567587552000000000000000000000000000000000, 451145001847230379591332155339 / 125811927521280000000000000000000000000000000],
    [-166032069942831231011869675151372168197759694517730648602079464656411622513415577015295953955611716126039376392181663147262167 / 19729009575000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 566225831840676416424273564694152795986607013767221343150678112446009744082255600374929248188563384621963610378761165543653 / 47048512500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -30131001399532850947118438576093385645811915168189249050708013965086843094587959250784823562163390056314107653664498086023 / 5852925000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 3054896200960827720167112242303398242352370573784932875875922148532022249270039827449137375984431078191370370003950066736598641 / 39700390275000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -843301738919941286338521707982155926321039430537095155218875933672443456682850567744431579274191555636134356844517242415126048873 / 18564352537500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 155477793878354836850366410995324265088553078412440044030993038129178811701833101306221674401201633183201714620546576410458740033183 / 1804208175000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -8073796056053378695542544579293162315163127490473679638406329903636134953412852932541834758835589400910470360884353015910817142156117 / 11691194238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 88857373012447154217175751762445011058260570886120600315263305313586564494109492305636086894850346591718446207405351760065465956201548818391933171997381915051 / 7081291759264412567571869175000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -32391579266669340568927034541933872277165754916799237373344244848612448291320844978742242040988537983474185931052811986963257408366780079684295661953 / 53378966014107834672772200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 101829287501912159792028995888214995205679501113042342510745252148192789 / 2582092775258120918006103515625000000000000000000000000000000000000000000000000, -11098160448465472818685675140854699376892606488692608401502148192789 / 1773151417428085029075952148437500000000000000000000000000000000000000000000000],
    [121442866081305770495381600010867867414417249908034032928911836758795744770577218935106261353388148519173573263497059163797 / 415727626600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 854436011301460258068359892436812085582970240123340585061965450361877903074239276497473950644781853968129174535285677139 / 2524661700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 25053851665633922187647063231554494427491751874792459668957197087007042641535153386825306252958263967434041996796235847 / 37218600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 5873722696199977970650529664288572601890698672981450723652168026184450792854303202186983689429 / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 881142581732871835139321150739849887248855881543290955575134032293788312579365066344743262020960395561794248646252120094457 / 38688734700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -2664275685489031942023131807204075964515516574228237748938967861305948090002503988514761057808169449642908944012008237910273177 / 124476798600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 306003064462076728530259845734660930363564032972623577150116900441321414642610224393003634925086756106380938131363756608751808113 / 5384630032031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -32391579266669340568927034541933872277165754916799237373344244848612448291320844978742242040988537983474185931052811986963257408366780079684295661953 / 53378966014107834672772200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 6550778457077647400738360929069043301163540563719914660055206846647711072383223967256187348388586115660006917169395174603975146475340736701774260587646219467 / 660316293967887943100941656830400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -690610553961164509984331218343510080159221932473886065738091937183786888313140947 / 1276107431668527074619835645312500000000000000000000000000000000000000000000000000000, 4217451187038214919854777325697707583940980793435172960964057524253000791 / 148090303065234279257746875000000000000000000000000000000000000000000000000000000],
    [51971921392123252872677385717300261302859749 / 2070222594000000000000000000000000000000000000000000000000000, 25053851665633920884899324716161608191011 / 765049000000000000000000000000000000000000000000000000000, 0, 0, 0, 451145001847230379591332155339 / 53110100736000000000000000000000000000000000, -786273500212451662740721377493573 / 70567587552000000000000000000000000000000000, 101829287501912159792028995888214995205679501113042342510745252148192789 / 2582092775258120918006103515625000000000000000000000000000000000000000000000000, -690610553961164509984331218343510080159221932473886065738091937183786888313140947 / 1276107431668527074619835645312500000000000000000000000000000000000000000000000000000, 19203485164449978824573262991616677446792965635945462264451438515770617670322103346493252138314899149193450620026678156332086073713447 / 2809617729895833969419398822500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -6742596972693772272025265603785781143456931439688382450732438659607419240559 / 13806500454970126796861718750000000000000000000000000000000000000000000000000000],
    [25053851665633920884899324716161608191011 / 81554223400000000000000000000000000000000000000000000000000, 0, 0, 0, 0, 0, 451145001847230379591332155339 / 125811927521280000000000000000000000000000000, -11098160448465472818685675140854699376892606488692608401502148192789 / 1773151417428085029075952148437500000000000000000000000000000000000000000000000, 4217451187038214919854777325697707583940980793435172960964057524253000791 / 148090303065234279257746875000000000000000000000000000000000000000000000000000000, -6742596972693772272025265603785781143456931439688382450732438659607419240559 / 13806500454970126796861718750000000000000000000000000000000000000000000000000000, 441078315652167906655505406656969079074697585731931770232808682087706313444730653614320850822430109233227399767261370939903426139390437373 / 132134226400089483504431520050527500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]] : List (List ℚ))
private def bFastMat (i j : Fin 11) : ℝ := matAt ([([903415056013080536256233959291620219981105599177176350917245699267988660633437386930924409711981500783098511445839449503452620568287940873631 / 105411381075000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -6952027539210458301990695946165517168624049084328737259349980230306128089973932150017778157748470197051660444744595161189022068498429407 / 2509794787500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 122112201574806371707566022763659164220474719581029487393335067852603242831359920024649725631100336621871294914714734446424017384052317 / 3194284275000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -149143640387401307480547981803916253454185595096262353187613453054163337627781473112888436357605725850992019161135324564108655735086809 / 339658894575000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 100891396522319225454373718630582618285068159222186897506616656391603978337564821374678309561875197395050667985803275441699620750847 / 16964703112500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -4723933408255230225658069702675431029334061439570315187319370617505961666896335006500171434945239807644868080249495758355873932501 / 65400159825000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 39688474103731147045594637590259263267362541278045575231317591437656350221428894805167811844285118129504448262158607822354703 / 50220475292968750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -166032069942831231011869675151372168197759694517730648602079464656411622513415577015295953955611716126039376392181663147262167 / 19729009575000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 121442866081305770495381600010867867414417249908034032928911836758795744770577218935106261353388148519173573263497059163797 / 415727626600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 51971921392123252872677385717300261302859749 / 2070222594000000000000000000000000000000000000000000000000000, 25053851665633920884899324716161608191011 / 81554223400000000000000000000000000000000000000000000000000] : List ℝ),
    ([-6952027539210458301990695946165517168624049084328737259349980230306128089973932150017778157748470197051660444744595161189022068498429407 / 2509794787500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 8792014015962070145425333570247817791173998216174949320505997505359241490032168112445512604158129743016543796150543620369693340935417336243 / 664357443750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -1533835430989617082752743143317014224125229677850959303214497831782954307628233013913224051951323796362163871734769908686467946921486341 / 684489487500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 333537856844660656805652798916503641049733130087504484400403000364371029646944611082168821542828279394390977277314685848271773489503 / 228163162500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -2176214103403277718355860060573395318471607494190549445942630504868584971599819855345900813438590735330729754692168625902693348459 / 522373556250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 16002978870006382345113508483264943187230805323836126678001074589190455271161101630350074915494363844288339523706568949450808037633 / 294300719212500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -41007635359942589921034301492256113240475205501667772201298158492798511475420560059169217554231656184941305863491473205251849 / 46633298486328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 566225831840676416424273564694152795986607013767221343150678112446009744082255600374929248188563384621963610378761165543653 / 47048512500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 854436011301460258068359892436812085582970240123340585061965450361877903074239276497473950644781853968129174535285677139 / 2524661700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 25053851665633920884899324716161608191011 / 765049000000000000000000000000000000000000000000000000000] : List ℝ),
    ([122112201574806371707566022763659164220474719581029487393335067852603242831359920024649725631100336621871294914714734446424017384052317 / 3194284275000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -1533835430989617082752743143317014224125229677850959303214497831782954307628233013913224051951323796362163871734769908686467946921486341 / 684489487500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 151789974673617196030780072759209421740308554281681317389229467810509486637621397326415511682904531117871301360676625325968994224839073217381 / 9582852825000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -4929852831607812145296706147181385633615908026531614557608653753375829434634968480987610136937169983878751958293184847502032427424573823 / 3194284275000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 129186371933596327597800532269041257240702098854854859268701854010560631166623747572117213991629098475147165527123312926664821507911 / 252180337500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -4087911245129799073283726864611890057990143919534280408160377681836690367932457231126006796179137018215137563683608796245419971933 / 12082727475000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 277006323340083068640507414544255061079563659125826415959234513594495673044012069121612488727720697065396061067283226249329971 / 534163237207031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -30131001399532850947118438576093385645811915168189249050708013965086843094587959250784823562163390056314107653664498086023 / 5852925000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 25053851665633922187647063231554494427491751874792459668957197087007042641535153386825306252958263967434041996796235847 / 37218600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000] : List ℝ),
    ([-149143640387401307480547981803916253454185595096262353187613453054163337627781473112888436357605725850992019161135324564108655735086809 / 339658894575000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 333537856844660656805652798916503641049733130087504484400403000364371029646944611082168821542828279394390977277314685848271773489503 / 228163162500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -4929852831607812145296706147181385633615908026531614557608653753375829434634968480987610136937169983878751958293184847502032427424573823 / 3194284275000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 17276111998079350365158300806562997803364947700231028766601077115343307128622641783584429197567155784910041315727148178053250885309092097761913 / 1018976683725000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -99109994509789889442145138041853634821511002446066084060391699666484626431908338043711966121509472628275048325098730078128340522943813 / 84060112500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1142644307675169394959282555307351122841311590949620888431276971007951095732420483514649926105758584336263960895063280844521663626803 / 4583103525000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -48899634867626527213290166466385136806850106803980071038506282848055577515339869181511153996344743585721443817911983757433009131 / 442264185644531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 3054896200960827720167112242303398242352370573784932875875922148532022249270039827449137375984431078191370370003950066736598641 / 39700390275000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 5873722696199977970650529664288572601890698672981450723652168026184450792854303202186983689429 / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000] : List ℝ),
    ([100891396522319225454373718630582618285068159222186897506616656391603978337564821374678309561875197395050667985803275441699620750847 / 16964703112500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -2176214103403277718355860060573395318471607494190549445942630504868584971599819855345900813438590735330729754692168625902693348459 / 522373556250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 129186371933596327597800532269041257240702098854854859268701854010560631166623747572117213991629098475147165527123312926664821507911 / 252180337500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -99109994509789889442145138041853634821511002446066084060391699666484626431908338043711966121509472628275048325098730078128340522943813 / 84060112500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 63547733562263959905985816101684173610908329166058559474684418889692815153516916040309410127379636278567288829827458807050124768393405940993493 / 3740717036306250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -10010598767237209732820028792123443494550871549854980125312460157011437139966461605688774835610670167400694522494018668171376463410305359 / 10492894912500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 13758582207116501207925016585200814865832427701351626937183393487721140383924054820025616565179121273761454538318367590391268430407 / 98398491064453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -843301738919941286338521707982155926321039430537095155218875933672443456682850567744431579274191555636134356844517242415126048873 / 18564352537500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 881142581732871835139321150739849887248855881543290955575134032293788312579365066344743262020960395561794248646252120094457 / 38688734700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000] : List ℝ),
    ([-4723933408255230225658069702675431029334061439570315187319370617505961666896335006500171434945239807644868080249495758355873932501 / 65400159825000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 16002978870006382345113508483264943187230805323836126678001074589190455271161101630350074915494363844288339523706568949450808037633 / 294300719212500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -4087911245129799073283726864611890057990143919534280408160377681836690367932457231126006796179137018215137563683608796245419971933 / 12082727475000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1142644307675169394959282555307351122841311590949620888431276971007951095732420483514649926105758584336263960895063280844521663626803 / 4583103525000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -10010598767237209732820028792123443494550871549854980125312460157011437139966461605688774835610670167400694522494018668171376463410305359 / 10492894912500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 7396533662353108938199319389394926799769279778833552910227097395821119445554080523121242320558698193708332074878195633879454664227880255242636453 / 457343317656225000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -110213136604114893370035123770919718946006711096656877319776643782099581417773577392026857395492280716844370684118586519393363325986103 / 137560432324218750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 155477793878354836850366410995324265088553078412440044030993038129178811701833101306221674401201633183201714620546576410458740033183 / 1804208175000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -2664275685489031942023131807204075964515516574228237748938967861305948090002503988514761057808169449642908944012008237910273177 / 124476798600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 451145001847230379591332155339 / 53110100736000000000000000000000000000000000] : List ℝ),
    ([39688474103731147045594637590259263267362541278045575231317591437656350221428894805167811844285118129504448262158607822354703 / 50220475292968750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -41007635359942589921034301492256113240475205501667772201298158492798511475420560059169217554231656184941305863491473205251849 / 46633298486328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 277006323340083068640507414544255061079563659125826415959234513594495673044012069121612488727720697065396061067283226249329971 / 534163237207031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -48899634867626527213290166466385136806850106803980071038506282848055577515339869181511153996344743585721443817911983757433009131 / 442264185644531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 13758582207116501207925016585200814865832427701351626937183393487721140383924054820025616565179121273761454538318367590391268430407 / 98398491064453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -110213136604114893370035123770919718946006711096656877319776643782099581417773577392026857395492280716844370684118586519393363325986103 / 137560432324218750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1190868409431806791902143096755799353688005666500872934350950156202573581670643030599405336688761224517048900982696460393681744087999918460171 / 81243585384005355834960937500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -8073796056053378695542544579293162315163127490473679638406329903636134953412852932541834758835589400910470360884353015910817142156117 / 11691194238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 306003064462076728530259845734660930363564032972623577150116900441321414642610224393003634925086756106380938131363756608751808113 / 5384630032031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -786273500212451662740721377493573 / 70567587552000000000000000000000000000000000, 451145001847230379591332155339 / 125811927521280000000000000000000000000000000] : List ℝ),
    ([-166032069942831231011869675151372168197759694517730648602079464656411622513415577015295953955611716126039376392181663147262167 / 19729009575000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 566225831840676416424273564694152795986607013767221343150678112446009744082255600374929248188563384621963610378761165543653 / 47048512500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -30131001399532850947118438576093385645811915168189249050708013965086843094587959250784823562163390056314107653664498086023 / 5852925000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 3054896200960827720167112242303398242352370573784932875875922148532022249270039827449137375984431078191370370003950066736598641 / 39700390275000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -843301738919941286338521707982155926321039430537095155218875933672443456682850567744431579274191555636134356844517242415126048873 / 18564352537500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 155477793878354836850366410995324265088553078412440044030993038129178811701833101306221674401201633183201714620546576410458740033183 / 1804208175000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -8073796056053378695542544579293162315163127490473679638406329903636134953412852932541834758835589400910470360884353015910817142156117 / 11691194238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 88857373012447154217175751762445011058260570886120600315263305313586564494109492305636086894850346591718446207405351760065465956201548818391933171997381915051 / 7081291759264412567571869175000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -32391579266669340568927034541933872277165754916799237373344244848612448291320844978742242040988537983474185931052811986963257408366780079684295661953 / 53378966014107834672772200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 101829287501912159792028995888214995205679501113042342510745252148192789 / 2582092775258120918006103515625000000000000000000000000000000000000000000000000, -11098160448465472818685675140854699376892606488692608401502148192789 / 1773151417428085029075952148437500000000000000000000000000000000000000000000000] : List ℝ),
    ([121442866081305770495381600010867867414417249908034032928911836758795744770577218935106261353388148519173573263497059163797 / 415727626600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 854436011301460258068359892436812085582970240123340585061965450361877903074239276497473950644781853968129174535285677139 / 2524661700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 25053851665633922187647063231554494427491751874792459668957197087007042641535153386825306252958263967434041996796235847 / 37218600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 5873722696199977970650529664288572601890698672981450723652168026184450792854303202186983689429 / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 881142581732871835139321150739849887248855881543290955575134032293788312579365066344743262020960395561794248646252120094457 / 38688734700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -2664275685489031942023131807204075964515516574228237748938967861305948090002503988514761057808169449642908944012008237910273177 / 124476798600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 306003064462076728530259845734660930363564032972623577150116900441321414642610224393003634925086756106380938131363756608751808113 / 5384630032031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -32391579266669340568927034541933872277165754916799237373344244848612448291320844978742242040988537983474185931052811986963257408366780079684295661953 / 53378966014107834672772200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 6550778457077647400738360929069043301163540563719914660055206846647711072383223967256187348388586115660006917169395174603975146475340736701774260587646219467 / 660316293967887943100941656830400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -690610553961164509984331218343510080159221932473886065738091937183786888313140947 / 1276107431668527074619835645312500000000000000000000000000000000000000000000000000000, 4217451187038214919854777325697707583940980793435172960964057524253000791 / 148090303065234279257746875000000000000000000000000000000000000000000000000000000] : List ℝ),
    ([51971921392123252872677385717300261302859749 / 2070222594000000000000000000000000000000000000000000000000000, 25053851665633920884899324716161608191011 / 765049000000000000000000000000000000000000000000000000000, 0, 0, 0, 451145001847230379591332155339 / 53110100736000000000000000000000000000000000, -786273500212451662740721377493573 / 70567587552000000000000000000000000000000000, 101829287501912159792028995888214995205679501113042342510745252148192789 / 2582092775258120918006103515625000000000000000000000000000000000000000000000000, -690610553961164509984331218343510080159221932473886065738091937183786888313140947 / 1276107431668527074619835645312500000000000000000000000000000000000000000000000000000, 19203485164449978824573262991616677446792965635945462264451438515770617670322103346493252138314899149193450620026678156332086073713447 / 2809617729895833969419398822500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, -6742596972693772272025265603785781143456931439688382450732438659607419240559 / 13806500454970126796861718750000000000000000000000000000000000000000000000000000] : List ℝ),
    ([25053851665633920884899324716161608191011 / 81554223400000000000000000000000000000000000000000000000000, 0, 0, 0, 0, 0, 451145001847230379591332155339 / 125811927521280000000000000000000000000000000, -11098160448465472818685675140854699376892606488692608401502148192789 / 1773151417428085029075952148437500000000000000000000000000000000000000000000000, 4217451187038214919854777325697707583940980793435172960964057524253000791 / 148090303065234279257746875000000000000000000000000000000000000000000000000000000, -6742596972693772272025265603785781143456931439688382450732438659607419240559 / 13806500454970126796861718750000000000000000000000000000000000000000000000000000, 441078315652167906655505406656969079074697585731931770232808682087706313444730653614320850822430109233227399767261370939903426139390437373 / 132134226400089483504431520050527500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000] : List ℝ)] : List (List ℝ)) i.1 j.1
private def bCleanMat (i j : Fin 11) : ℝ := (ApertureLogTwo.matQ ApertureLogTwo.oddBClean i.1 j.1 : ℝ)

private theorem bFast_to_bClean_le (m : Fin 11 → ℝ) :
    (∑ i : Fin 11, ∑ j : Fin 11, bFastMat i j * m i * m j) ≤
      ∑ i : Fin 11, ∑ j : Fin 11, bCleanMat i j * m i * m j := by
  have h := ApertureLogTwo.quad_le_of_domCheck_sub (Q := bFastQ) (Q' := ApertureLogTwo.oddBClean) (by decide +kernel) m
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

private def c0Rat : ℝ := (490620189449324317 / 500000000000000000 : ℝ)
private def e2Mid : ℝ := (1225322679335683989642377 / 2500000000000000000000000 : ℝ)
private def e3Mid : ℝ := (3171420502987819885931939 / 5000000000000000000000000 : ℝ)
private def deltaResRat : ℝ := (11324140799014169 / 1000000000000000000 : ℝ)

set_option linter.unusedSimpArgs false in
private theorem hEv_bound_0 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hGpar : ∀ u, dilateLogTwo F (-u) = -dilateLogTwo F u) :
    let m := halfMoment (dilateLogTwo F)
    apow0_1 * (∑ i : Fin 11, ∑ j : Fin 11, qEvMat_0 i j * m i * m j) -
      (∑ i : Fin 11, (errApow_1 * qEvRowAbs_0 i) * m i ^ 2) ≤
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
      ∑ i : Fin 11, ∑ j : Fin 11, qEvMat_0 i j * m i * m j := by
    have hevm := even_lag_moment_of_odd hGc hsG hGpar 0
    rw [hevm]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    simp_rw [sum_finK]; dsimp only [qEvMat_0, matAt, listAt, coeffAt, m]; ring
  rw [hexp]
  have hpert := symm_quad_scale_pert qEvMat_0 qEvMat_0_sym abs_aperture_pow_1_sub m
  simp_rw [qEvRowAbs_0_eq] at hpert
  exact hpert

set_option linter.unusedSimpArgs false in
private theorem hEv_bound_1 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hGpar : ∀ u, dilateLogTwo F (-u) = -dilateLogTwo F u) :
    let m := halfMoment (dilateLogTwo F)
    apow0_3 * (∑ i : Fin 11, ∑ j : Fin 11, qEvMat_1 i j * m i * m j) -
      (∑ i : Fin 11, (errApow_3 * qEvRowAbs_1 i) * m i ^ 2) ≤
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
      ∑ i : Fin 11, ∑ j : Fin 11, qEvMat_1 i j * m i * m j := by
    have hevm := even_lag_moment_of_odd hGc hsG hGpar 1
    rw [hevm]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [show ((2 : ℕ).choose 1 : ℝ) = 2 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]]
    have hm_0 := mon_moment_eq_leg_sum hGc ⟨0, by omega⟩
    dsimp only [degAt] at hm_0
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_0
    rw [sum_finK] at hm_0; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_0
    rw [hm_0]
    simp_rw [sum_finK]; dsimp only [qEvMat_1, matAt, listAt, coeffAt, m]; ring
  rw [hexp]
  have hpert := symm_quad_scale_pert qEvMat_1 qEvMat_1_sym abs_aperture_pow_3_sub m
  simp_rw [qEvRowAbs_1_eq] at hpert
  exact hpert

set_option linter.unusedSimpArgs false in
private theorem hEv_bound_2 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hGpar : ∀ u, dilateLogTwo F (-u) = -dilateLogTwo F u) :
    let m := halfMoment (dilateLogTwo F)
    apow0_5 * (∑ i : Fin 11, ∑ j : Fin 11, qEvMat_2 i j * m i * m j) -
      (∑ i : Fin 11, (errApow_5 * qEvRowAbs_2 i) * m i ^ 2) ≤
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
      ∑ i : Fin 11, ∑ j : Fin 11, qEvMat_2 i j * m i * m j := by
    have hevm := even_lag_moment_of_odd hGc hsG hGpar 2
    rw [hevm]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [show ((4 : ℕ).choose 1 : ℝ) = 4 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((4 : ℕ).choose 3 : ℝ) = 4 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]]
    have hm_0 := mon_moment_eq_leg_sum hGc ⟨0, by omega⟩
    dsimp only [degAt] at hm_0
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_0
    rw [sum_finK] at hm_0; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_0
    have hm_1 := mon_moment_eq_leg_sum hGc ⟨1, by omega⟩
    dsimp only [degAt] at hm_1
    simp only [Nat.reduceMul, Nat.reduceAdd] at hm_1
    rw [sum_finK] at hm_1; dsimp only [monToLegMat, matAt, listAt, coeffAt] at hm_1
    rw [hm_0, hm_1]
    simp_rw [sum_finK]; dsimp only [qEvMat_2, matAt, listAt, coeffAt, m]; ring
  rw [hexp]
  have hpert := symm_quad_scale_pert qEvMat_2 qEvMat_2_sym abs_aperture_pow_5_sub m
  simp_rw [qEvRowAbs_2_eq] at hpert
  exact hpert

set_option linter.unusedSimpArgs false in
private theorem hEv_bound_3 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hGpar : ∀ u, dilateLogTwo F (-u) = -dilateLogTwo F u) :
    let m := halfMoment (dilateLogTwo F)
    apow0_7 * (∑ i : Fin 11, ∑ j : Fin 11, qEvMat_3 i j * m i * m j) -
      (∑ i : Fin 11, (errApow_7 * qEvRowAbs_3 i) * m i ^ 2) ≤
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
      ∑ i : Fin 11, ∑ j : Fin 11, qEvMat_3 i j * m i * m j := by
    have hevm := even_lag_moment_of_odd hGc hsG hGpar 3
    rw [hevm]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [show ((6 : ℕ).choose 1 : ℝ) = 6 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((6 : ℕ).choose 3 : ℝ) = 20 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((6 : ℕ).choose 5 : ℝ) = 6 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]]
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
    simp_rw [sum_finK]; dsimp only [qEvMat_3, matAt, listAt, coeffAt, m]; ring
  rw [hexp]
  have hpert := symm_quad_scale_pert qEvMat_3 qEvMat_3_sym abs_aperture_pow_7_sub m
  simp_rw [qEvRowAbs_3_eq] at hpert
  exact hpert

set_option linter.unusedSimpArgs false in
private theorem hEv_bound_4 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hGpar : ∀ u, dilateLogTwo F (-u) = -dilateLogTwo F u) :
    let m := halfMoment (dilateLogTwo F)
    apow0_9 * (∑ i : Fin 11, ∑ j : Fin 11, qEvMat_4 i j * m i * m j) -
      (∑ i : Fin 11, (errApow_9 * qEvRowAbs_4 i) * m i ^ 2) ≤
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
      ∑ i : Fin 11, ∑ j : Fin 11, qEvMat_4 i j * m i * m j := by
    have hevm := even_lag_moment_of_odd hGc hsG hGpar 4
    rw [hevm]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [show ((8 : ℕ).choose 1 : ℝ) = 8 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((8 : ℕ).choose 3 : ℝ) = 56 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((8 : ℕ).choose 5 : ℝ) = 56 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((8 : ℕ).choose 7 : ℝ) = 8 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]]
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
    simp_rw [sum_finK]; dsimp only [qEvMat_4, matAt, listAt, coeffAt, m]; ring
  rw [hexp]
  have hpert := symm_quad_scale_pert qEvMat_4 qEvMat_4_sym abs_aperture_pow_9_sub m
  simp_rw [qEvRowAbs_4_eq] at hpert
  exact hpert

set_option linter.unusedSimpArgs false in
private theorem hEv_bound_5 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hGpar : ∀ u, dilateLogTwo F (-u) = -dilateLogTwo F u) :
    let m := halfMoment (dilateLogTwo F)
    apow0_11 * (∑ i : Fin 11, ∑ j : Fin 11, qEvMat_5 i j * m i * m j) -
      (∑ i : Fin 11, (errApow_11 * qEvRowAbs_5 i) * m i ^ 2) ≤
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
      ∑ i : Fin 11, ∑ j : Fin 11, qEvMat_5 i j * m i * m j := by
    have hevm := even_lag_moment_of_odd hGc hsG hGpar 5
    rw [hevm]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [show ((10 : ℕ).choose 1 : ℝ) = 10 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((10 : ℕ).choose 3 : ℝ) = 120 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((10 : ℕ).choose 5 : ℝ) = 252 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((10 : ℕ).choose 7 : ℝ) = 120 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((10 : ℕ).choose 9 : ℝ) = 10 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]]
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
    simp_rw [sum_finK]; dsimp only [qEvMat_5, matAt, listAt, coeffAt, m]; ring
  rw [hexp]
  have hpert := symm_quad_scale_pert qEvMat_5 qEvMat_5_sym abs_aperture_pow_11_sub m
  simp_rw [qEvRowAbs_5_eq] at hpert
  exact hpert

set_option linter.unusedSimpArgs false in
private theorem hEv_bound_6 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hGpar : ∀ u, dilateLogTwo F (-u) = -dilateLogTwo F u) :
    let m := halfMoment (dilateLogTwo F)
    apow0_13 * (∑ i : Fin 11, ∑ j : Fin 11, qEvMat_6 i j * m i * m j) -
      (∑ i : Fin 11, (errApow_13 * qEvRowAbs_6 i) * m i ^ 2) ≤
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
      ∑ i : Fin 11, ∑ j : Fin 11, qEvMat_6 i j * m i * m j := by
    have hevm := even_lag_moment_of_odd hGc hsG hGpar 6
    rw [hevm]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [show ((12 : ℕ).choose 1 : ℝ) = 12 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((12 : ℕ).choose 3 : ℝ) = 220 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((12 : ℕ).choose 5 : ℝ) = 792 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((12 : ℕ).choose 7 : ℝ) = 792 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((12 : ℕ).choose 9 : ℝ) = 220 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((12 : ℕ).choose 11 : ℝ) = 12 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]]
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
    simp_rw [sum_finK]; dsimp only [qEvMat_6, matAt, listAt, coeffAt, m]; ring
  rw [hexp]
  have hpert := symm_quad_scale_pert qEvMat_6 qEvMat_6_sym abs_aperture_pow_13_sub m
  simp_rw [qEvRowAbs_6_eq] at hpert
  exact hpert

set_option linter.unusedSimpArgs false in
private theorem hEv_bound_7 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hGpar : ∀ u, dilateLogTwo F (-u) = -dilateLogTwo F u) :
    let m := halfMoment (dilateLogTwo F)
    apow0_15 * (∑ i : Fin 11, ∑ j : Fin 11, qEvMat_7 i j * m i * m j) -
      (∑ i : Fin 11, (errApow_15 * qEvRowAbs_7 i) * m i ^ 2) ≤
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
      ∑ i : Fin 11, ∑ j : Fin 11, qEvMat_7 i j * m i * m j := by
    have hevm := even_lag_moment_of_odd hGc hsG hGpar 7
    rw [hevm]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [show ((14 : ℕ).choose 1 : ℝ) = 14 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((14 : ℕ).choose 3 : ℝ) = 364 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((14 : ℕ).choose 5 : ℝ) = 2002 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((14 : ℕ).choose 7 : ℝ) = 3432 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((14 : ℕ).choose 9 : ℝ) = 2002 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((14 : ℕ).choose 11 : ℝ) = 364 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((14 : ℕ).choose 13 : ℝ) = 14 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]]
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
    simp_rw [sum_finK]; dsimp only [qEvMat_7, matAt, listAt, coeffAt, m]; ring
  rw [hexp]
  have hpert := symm_quad_scale_pert qEvMat_7 qEvMat_7_sym abs_aperture_pow_15_sub m
  simp_rw [qEvRowAbs_7_eq] at hpert
  exact hpert

set_option linter.unusedSimpArgs false in
private theorem hEv_bound_8 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hGpar : ∀ u, dilateLogTwo F (-u) = -dilateLogTwo F u) :
    let m := halfMoment (dilateLogTwo F)
    apow0_17 * (∑ i : Fin 11, ∑ j : Fin 11, qEvMat_8 i j * m i * m j) -
      (∑ i : Fin 11, (errApow_17 * qEvRowAbs_8 i) * m i ^ 2) ≤
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
      ∑ i : Fin 11, ∑ j : Fin 11, qEvMat_8 i j * m i * m j := by
    have hevm := even_lag_moment_of_odd hGc hsG hGpar 8
    rw [hevm]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [show ((16 : ℕ).choose 1 : ℝ) = 16 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((16 : ℕ).choose 3 : ℝ) = 560 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((16 : ℕ).choose 5 : ℝ) = 4368 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((16 : ℕ).choose 7 : ℝ) = 11440 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((16 : ℕ).choose 9 : ℝ) = 11440 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((16 : ℕ).choose 11 : ℝ) = 4368 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((16 : ℕ).choose 13 : ℝ) = 560 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((16 : ℕ).choose 15 : ℝ) = 16 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]]
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
    simp_rw [sum_finK]; dsimp only [qEvMat_8, matAt, listAt, coeffAt, m]; ring
  rw [hexp]
  have hpert := symm_quad_scale_pert qEvMat_8 qEvMat_8_sym abs_aperture_pow_17_sub m
  simp_rw [qEvRowAbs_8_eq] at hpert
  exact hpert

set_option linter.unusedSimpArgs false in
private theorem hEv_bound_9 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hGpar : ∀ u, dilateLogTwo F (-u) = -dilateLogTwo F u) :
    let m := halfMoment (dilateLogTwo F)
    apow0_19 * (∑ i : Fin 11, ∑ j : Fin 11, qEvMat_9 i j * m i * m j) -
      (∑ i : Fin 11, (errApow_19 * qEvRowAbs_9 i) * m i ^ 2) ≤
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
      ∑ i : Fin 11, ∑ j : Fin 11, qEvMat_9 i j * m i * m j := by
    have hevm := even_lag_moment_of_odd hGc hsG hGpar 9
    rw [hevm]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [show ((18 : ℕ).choose 1 : ℝ) = 18 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((18 : ℕ).choose 3 : ℝ) = 816 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((18 : ℕ).choose 5 : ℝ) = 8568 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((18 : ℕ).choose 7 : ℝ) = 31824 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((18 : ℕ).choose 9 : ℝ) = 48620 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((18 : ℕ).choose 11 : ℝ) = 31824 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((18 : ℕ).choose 13 : ℝ) = 8568 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((18 : ℕ).choose 15 : ℝ) = 816 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((18 : ℕ).choose 17 : ℝ) = 18 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]]
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
    simp_rw [sum_finK]; dsimp only [qEvMat_9, matAt, listAt, coeffAt, m]; ring
  rw [hexp]
  have hpert := symm_quad_scale_pert qEvMat_9 qEvMat_9_sym abs_aperture_pow_19_sub m
  simp_rw [qEvRowAbs_9_eq] at hpert
  exact hpert

set_option linter.unusedSimpArgs false in
private theorem hEv_bound_10 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hGpar : ∀ u, dilateLogTwo F (-u) = -dilateLogTwo F u) :
    let m := halfMoment (dilateLogTwo F)
    apow0_21 * (∑ i : Fin 11, ∑ j : Fin 11, qEvMat_10 i j * m i * m j) -
      (∑ i : Fin 11, (errApow_21 * qEvRowAbs_10 i) * m i ^ 2) ≤
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
      ∑ i : Fin 11, ∑ j : Fin 11, qEvMat_10 i j * m i * m j := by
    have hevm := even_lag_moment_of_odd hGc hsG hGpar 10
    rw [hevm]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [show ((20 : ℕ).choose 1 : ℝ) = 20 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((20 : ℕ).choose 3 : ℝ) = 1140 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((20 : ℕ).choose 5 : ℝ) = 15504 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((20 : ℕ).choose 7 : ℝ) = 77520 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((20 : ℕ).choose 9 : ℝ) = 167960 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((20 : ℕ).choose 11 : ℝ) = 167960 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((20 : ℕ).choose 13 : ℝ) = 77520 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((20 : ℕ).choose 15 : ℝ) = 15504 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((20 : ℕ).choose 17 : ℝ) = 1140 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((20 : ℕ).choose 19 : ℝ) = 20 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]]
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
    simp_rw [sum_finK]; dsimp only [qEvMat_10, matAt, listAt, coeffAt, m]; ring
  rw [hexp]
  have hpert := symm_quad_scale_pert qEvMat_10 qEvMat_10_sym abs_aperture_pow_21_sub m
  simp_rw [qEvRowAbs_10_eq] at hpert
  exact hpert

set_option linter.unusedSimpArgs false in
private theorem hEv_bound_11 {F : ℝ → ℝ}
    (hGc : Continuous (dilateLogTwo F))
    (hsG : tsupport (dilateLogTwo F) ⊆ Icc (-1 : ℝ) 1)
    (hGpar : ∀ u, dilateLogTwo F (-u) = -dilateLogTwo F u) :
    let m := halfMoment (dilateLogTwo F)
    apow0_23 * (∑ i : Fin 11, ∑ j : Fin 11, qEvMat_11 i j * m i * m j) -
      (∑ i : Fin 11, (errApow_23 * qEvRowAbs_11 i) * m i ^ 2) ≤
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
      ∑ i : Fin 11, ∑ j : Fin 11, qEvMat_11 i j * m i * m j := by
    have hevm := even_lag_moment_of_odd hGc hsG hGpar 11
    rw [hevm]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [show ((22 : ℕ).choose 1 : ℝ) = 22 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((22 : ℕ).choose 3 : ℝ) = 1540 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((22 : ℕ).choose 5 : ℝ) = 26334 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((22 : ℕ).choose 7 : ℝ) = 170544 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((22 : ℕ).choose 9 : ℝ) = 497420 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((22 : ℕ).choose 11 : ℝ) = 705432 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((22 : ℕ).choose 13 : ℝ) = 497420 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((22 : ℕ).choose 15 : ℝ) = 170544 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((22 : ℕ).choose 17 : ℝ) = 26334 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((22 : ℕ).choose 19 : ℝ) = 1540 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial], show ((22 : ℕ).choose 21 : ℝ) = 22 by norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]]
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
    simp_rw [sum_finK]; dsimp only [qEvMat_11, matAt, listAt, coeffAt, m]; ring
  rw [hexp]
  have hpert := symm_quad_scale_pert qEvMat_11 qEvMat_11_sym abs_aperture_pow_23_sub m
  simp_rw [qEvRowAbs_11_eq] at hpert
  exact hpert

private theorem hIterP_eq_0 {G : ℝ → ℝ}
    (hLowProj : ∀ y : ℝ, lowProj G 23 y = ∑ k : Fin 11, halfMoment G k * basisFn k y) (y : ℝ) :
    iterPrim 2 (lowProj G 23) y =
      ∑ j : Fin 11, halfMoment G j * polyEval (match j.1 with | 0 => iBasis_2_0 | 1 => iBasis_2_1 | 2 => iBasis_2_2 | 3 => iBasis_2_3 | 4 => iBasis_2_4 | 5 => iBasis_2_5 | 6 => iBasis_2_6 | 7 => iBasis_2_7 | 8 => iBasis_2_8 | 9 => iBasis_2_9 | 10 => iBasis_2_10 | _ => []) y := by
  have hlp_eq : lowProj G 23 = fun u => ∑ j : Fin 11, halfMoment G j * basisFn j u := funext hLowProj
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

private theorem hPP_eq_0 {G : ℝ → ℝ}
    (hLowProj : ∀ y : ℝ, lowProj G 23 y = ∑ k : Fin 11, halfMoment G k * basisFn k y) :
    ((1 / 48 : ℝ) * ((1 : ℕ).factorial : ℝ)) *
      (∫ y in (-1 : ℝ)..1, lowProj G 23 y * iterPrim 2 (lowProj G 23) y) =
      ∑ i : Fin 11, ∑ j : Fin 11, qOddMat_0 i j * halfMoment G i * halfMoment G j := by
  set m := halfMoment G
  have hfn : ∀ y : ℝ, lowProj G 23 y * iterPrim 2 (lowProj G 23) y =
      ∑ i : Fin 11, ∑ j : Fin 11, (m i * m j) *
        (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y *
         polyEval (match j.1 with | 0 => iBasis_2_0 | 1 => iBasis_2_1 | 2 => iBasis_2_2 | 3 => iBasis_2_3 | 4 => iBasis_2_4 | 5 => iBasis_2_5 | 6 => iBasis_2_6 | 7 => iBasis_2_7 | 8 => iBasis_2_8 | 9 => iBasis_2_9 | 10 => iBasis_2_10 | _ => []) y) := fun y => by
    rw [hLowProj y, hIterP_eq_0 hLowProj y, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    have hb : basisFn i y = polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y := by
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
    rw [hb]; dsimp only [m]; ring
  simp_rw [hfn]
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (show Continuous fun y : ℝ => ∑ j : Fin 11, (m i * m j) *
      (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y *
       polyEval (match j.1 with | 0 => iBasis_2_0 | 1 => iBasis_2_1 | 2 => iBasis_2_2 | 3 => iBasis_2_3 | 4 => iBasis_2_4 | 5 => iBasis_2_5 | 6 => iBasis_2_6 | 7 => iBasis_2_7 | 8 => iBasis_2_8 | 9 => iBasis_2_9 | 10 => iBasis_2_10 | _ => []) y) from
      continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_polyEval _).mul (continuous_polyEval _))).intervalIntegrable (-1) 1]
  have hEach : ∀ (i j : Fin 11), (∫ y in (-1 : ℝ)..1,
      (m i * m j) * (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y *
        polyEval (match j.1 with | 0 => iBasis_2_0 | 1 => iBasis_2_1 | 2 => iBasis_2_2 | 3 => iBasis_2_3 | 4 => iBasis_2_4 | 5 => iBasis_2_5 | 6 => iBasis_2_6 | 7 => iBasis_2_7 | 8 => iBasis_2_8 | 9 => iBasis_2_9 | 10 => iBasis_2_10 | _ => []) y)) =
      (m i * m j) * (ApertureLogTwo.matQ mPPRawQ_0 i.1 j.1 : ℝ) := fun i j => by
    rw [intervalIntegral.integral_const_mul, int_pp_0 i j]
  have hSumI : ∀ i : Fin 11, (∫ y in (-1 : ℝ)..1, ∑ j : Fin 11,
      (m i * m j) * (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y *
        polyEval (match j.1 with | 0 => iBasis_2_0 | 1 => iBasis_2_1 | 2 => iBasis_2_2 | 3 => iBasis_2_3 | 4 => iBasis_2_4 | 5 => iBasis_2_5 | 6 => iBasis_2_6 | 7 => iBasis_2_7 | 8 => iBasis_2_8 | 9 => iBasis_2_9 | 10 => iBasis_2_10 | _ => []) y)) =
      ∑ j : Fin 11, (m i * m j) * (ApertureLogTwo.matQ mPPRawQ_0 i.1 j.1 : ℝ) := fun i => by
    rw [intervalIntegral.integral_finsetSum fun j _ =>
      (show Continuous fun y : ℝ => (m i * m j) *
        (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y *
         polyEval (match j.1 with | 0 => iBasis_2_0 | 1 => iBasis_2_1 | 2 => iBasis_2_2 | 3 => iBasis_2_3 | 4 => iBasis_2_4 | 5 => iBasis_2_5 | 6 => iBasis_2_6 | 7 => iBasis_2_7 | 8 => iBasis_2_8 | 9 => iBasis_2_9 | 10 => iBasis_2_10 | _ => []) y) from
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
    (hLowProj : ∀ y : ℝ, lowProj (dilateLogTwo F) 23 y =
      ∑ k : Fin 11, halfMoment (dilateLogTwo F) k * basisFn k y)
    (hHopp : ∀ r : ℕ, regionalLegendreMoment (dilateLogTwo F) (23 + (2 * r + 1)) = 0) :
    let G := dilateLogTwo F
    let m := halfMoment G
    let M_res := (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 23 x) ^ 2) / 2
    apow0_2 * (∑ i : Fin 11, ∑ j : Fin 11, qOddMat_0 i j * m i * m j) -
      (∑ i : Fin 11, (errApow_2 * qOddRowAbs_0 i) * m i ^ 2) -
      ((6261802804445623152330125031301818197576522398243856809 / 62500000000000000000000000000000000000000000000000000000 : ℝ) * ∑ r ∈ Finset.range 1,
        ((2 * ↑(23 + 2 * r) + 1) / 2) * (∑ i : Fin 11, m i * gHi_0 i r) ^ 2) -
      ((1 / 500 : ℝ) + (1601510046394004748890341793893822096964129967681123 / 197392088021787172376357642657862688463432000000000000 : ℝ)) * M_res ≤
      ((1 / 24 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 1 * autocorr F t) /
        (2 * apertureLogTwo) := by
  intro G m M_res
  have hA_pos : 0 < apertureLogTwo := apertureLogTwo_pos
  set R_res : ℝ → ℝ := fun x => G x - lowProj G 23 x
  have hRc : Continuous R_res := hGc.sub (contDiff_lowProj G _ (k := 0)).continuous
  have hMres_nn : 0 ≤ M_res := div_nonneg (setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _) (by norm_num)
  have hIntR2 : (∫ x in Icc (-1 : ℝ) 1, R_res x ^ 2) = 2 * M_res := by dsimp [R_res, M_res]; ring
  have hpi_lo : piLo ≤ Real.pi := (pi_bounds_d20).1
  have hpi_pos : 0 < piLo := by norm_num [piLo]
  have h4pi : 4 / Real.pi ^ 2 ≤ 4 / piLo ^ 2 := by
    have hp2 : piLo ^ 2 ≤ Real.pi ^ 2 := pow_le_pow_left₀ hpi_pos.le hpi_lo 2
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hp2
  have hdil := dilated_correlation_moment_log_two F 1
  have hdec := odd_lag_moment_lowProj_decomp hGc hsG (m := 23) (q := 0) (by omega)
  change (∫ t in Ioc (0 : ℝ) 2, t ^ 1 * autocorr G t) =
    ((1 : ℕ).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, lowProj G 23 y * iterPrim 2 (lowProj G 23) y) +
    2 * ((1 : ℕ).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, R_res y * iterPrim 2 (lowProj G 23) y) +
    (-1 : ℝ) ^ (0 + 1) * ((1 : ℕ).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, iterPrim (0 + 1) R_res y ^ 2) at hdec
  have hPP := hPP_eq_0 hLowProj
  have hPP_pert := symm_quad_scale_pert qOddMat_0 qOddMat_0_sym abs_aperture_pow_2_sub m
  simp_rw [qOddRowAbs_0_eq] at hPP_pert
  have hWirt := iterPrim_sq_le_wirtinger hRc (m := 23) (fun n hn => sub_lowProj_moment_lt hGc hn) (0 + 1) (by omega)
  have hWirt' : (∫ y in (-1 : ℝ)..1, iterPrim (0 + 1) R_res y ^ 2) ≤ (4 / piLo ^ 2) ^ (0 + 1) * (2 * M_res) := by
    rw [hIntR2] at hWirt
    exact hWirt.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h4pi (0 + 1)) (by positivity))
  have hCross := high_mode_cross_sq_le hGc (m := 23) (q := 0) (by omega) hHopp
  change (∫ y in (-1 : ℝ)..1, R_res y * iterPrim 2 (lowProj G 23) y) ^ 2 ≤
    (∑ r ∈ Finset.range (0 + 1), ((2 * ↑(23 + 2 * r) + 1) / 2) *
      regionalLegendreMoment (iterPrim 2 (lowProj G 23)) (23 + 2 * r) ^ 2) *
    (∫ y in Icc (-1 : ℝ) 1, R_res y ^ 2) at hCross
  rw [hIntR2] at hCross
  have hMomLin : ∀ r ∈ Finset.range (0 + 1), regionalLegendreMoment (iterPrim 2 (lowProj G 23)) (23 + 2 * r) =
      ∑ i : Fin 11, m i * gHi_0 i r := fun r hr => by
    have hlin : regionalLegendreMoment (iterPrim 2 (lowProj G 23)) (23 + 2 * r) =
        ∑ i : Fin 11, m i * regionalLegendreMoment (polyEval (match i.1 with | 0 => iBasis_2_0 | 1 => iBasis_2_1 | 2 => iBasis_2_2 | 3 => iBasis_2_3 | 4 => iBasis_2_4 | 5 => iBasis_2_5 | 6 => iBasis_2_6 | 7 => iBasis_2_7 | 8 => iBasis_2_8 | 9 => iBasis_2_9 | 10 => iBasis_2_10 | _ => [])) (23 + 2 * r) := by
      unfold regionalLegendreMoment
      have hfn : ∀ x : ℝ, iterPrim 2 (lowProj G 23) x * legP (23 + 2 * r) x =
          ∑ i : Fin 11, m i * (polyEval (match i.1 with | 0 => iBasis_2_0 | 1 => iBasis_2_1 | 2 => iBasis_2_2 | 3 => iBasis_2_3 | 4 => iBasis_2_4 | 5 => iBasis_2_5 | 6 => iBasis_2_6 | 7 => iBasis_2_7 | 8 => iBasis_2_8 | 9 => iBasis_2_9 | 10 => iBasis_2_10 | _ => []) x * legP (23 + 2 * r) x) := fun x => by
        rw [hIterP_eq_0 hLowProj x, Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by dsimp only [m]; ring
      simp_rw [hfn]
      rw [integral_finsetSum _ fun i _ =>
        (show Continuous fun x : ℝ => m i * (polyEval (match i.1 with | 0 => iBasis_2_0 | 1 => iBasis_2_1 | 2 => iBasis_2_2 | 3 => iBasis_2_3 | 4 => iBasis_2_4 | 5 => iBasis_2_5 | 6 => iBasis_2_6 | 7 => iBasis_2_7 | 8 => iBasis_2_8 | 9 => iBasis_2_9 | 10 => iBasis_2_10 | _ => []) x * legP (23 + 2 * r) x) from
          continuous_const.mul ((continuous_polyEval _).mul (continuous_legP _))).integrableOn_Icc]
      exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    rw [hlin]; exact Finset.sum_congr rfl fun i _ => by rw [gHi_eq_0 i r hr]
  set A_sp : ℝ := ∑ r ∈ Finset.range (0 + 1), ((2 * ↑(23 + 2 * r) + 1) / 2) *
    (∑ i : Fin 11, m i * gHi_0 i r) ^ 2
  have hAsp_eq : (∑ r ∈ Finset.range (0 + 1), ((2 * ↑(23 + 2 * r) + 1) / 2) *
      regionalLegendreMoment (iterPrim 2 (lowProj G 23)) (23 + 2 * r) ^ 2) = A_sp :=
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
  set I_RP : ℝ := ∫ y in (-1 : ℝ)..1, R_res y * iterPrim 2 (lowProj G 23) y
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
        (∫ y in (-1 : ℝ)..1, lowProj G 23 y * iterPrim 2 (lowProj G 23) y)) +
      (1 : ℝ) * (2 * (w_true * I_RP)) -
      w_true * (∫ y in (-1 : ℝ)..1, iterPrim (0 + 1) R_res y ^ 2) := by
    rw [hdil, hdec]; dsimp [w_true, I_RP]; field_simp [hA_pos.ne']; norm_num; ring
  rw [hdiv_tot, hPP]
  have hsc_eq : (2 * ((2502359447490632420141159053 / 250000000000000000000000000000 : ℝ)) ^ 2 / (1 / 500 : ℝ)) = (6261802804445623152330125031301818197576522398243856809 / 62500000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num
  rw [hsc_eq] at hy
  linarith [hPP_pert, hy.1, hw_wirt]

private theorem hIterP_eq_1 {G : ℝ → ℝ}
    (hLowProj : ∀ y : ℝ, lowProj G 23 y = ∑ k : Fin 11, halfMoment G k * basisFn k y) (y : ℝ) :
    iterPrim 4 (lowProj G 23) y =
      ∑ j : Fin 11, halfMoment G j * polyEval (match j.1 with | 0 => iBasis_4_0 | 1 => iBasis_4_1 | 2 => iBasis_4_2 | 3 => iBasis_4_3 | 4 => iBasis_4_4 | 5 => iBasis_4_5 | 6 => iBasis_4_6 | 7 => iBasis_4_7 | 8 => iBasis_4_8 | 9 => iBasis_4_9 | 10 => iBasis_4_10 | _ => []) y := by
  have hlp_eq : lowProj G 23 = fun u => ∑ j : Fin 11, halfMoment G j * basisFn j u := funext hLowProj
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

private theorem hPP_eq_1 {G : ℝ → ℝ}
    (hLowProj : ∀ y : ℝ, lowProj G 23 y = ∑ k : Fin 11, halfMoment G k * basisFn k y) :
    ((-7 / 11520 : ℝ) * ((3 : ℕ).factorial : ℝ)) *
      (∫ y in (-1 : ℝ)..1, lowProj G 23 y * iterPrim 4 (lowProj G 23) y) =
      ∑ i : Fin 11, ∑ j : Fin 11, qOddMat_1 i j * halfMoment G i * halfMoment G j := by
  set m := halfMoment G
  have hfn : ∀ y : ℝ, lowProj G 23 y * iterPrim 4 (lowProj G 23) y =
      ∑ i : Fin 11, ∑ j : Fin 11, (m i * m j) *
        (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y *
         polyEval (match j.1 with | 0 => iBasis_4_0 | 1 => iBasis_4_1 | 2 => iBasis_4_2 | 3 => iBasis_4_3 | 4 => iBasis_4_4 | 5 => iBasis_4_5 | 6 => iBasis_4_6 | 7 => iBasis_4_7 | 8 => iBasis_4_8 | 9 => iBasis_4_9 | 10 => iBasis_4_10 | _ => []) y) := fun y => by
    rw [hLowProj y, hIterP_eq_1 hLowProj y, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    have hb : basisFn i y = polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y := by
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
    rw [hb]; dsimp only [m]; ring
  simp_rw [hfn]
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (show Continuous fun y : ℝ => ∑ j : Fin 11, (m i * m j) *
      (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y *
       polyEval (match j.1 with | 0 => iBasis_4_0 | 1 => iBasis_4_1 | 2 => iBasis_4_2 | 3 => iBasis_4_3 | 4 => iBasis_4_4 | 5 => iBasis_4_5 | 6 => iBasis_4_6 | 7 => iBasis_4_7 | 8 => iBasis_4_8 | 9 => iBasis_4_9 | 10 => iBasis_4_10 | _ => []) y) from
      continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_polyEval _).mul (continuous_polyEval _))).intervalIntegrable (-1) 1]
  have hEach : ∀ (i j : Fin 11), (∫ y in (-1 : ℝ)..1,
      (m i * m j) * (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y *
        polyEval (match j.1 with | 0 => iBasis_4_0 | 1 => iBasis_4_1 | 2 => iBasis_4_2 | 3 => iBasis_4_3 | 4 => iBasis_4_4 | 5 => iBasis_4_5 | 6 => iBasis_4_6 | 7 => iBasis_4_7 | 8 => iBasis_4_8 | 9 => iBasis_4_9 | 10 => iBasis_4_10 | _ => []) y)) =
      (m i * m j) * (ApertureLogTwo.matQ mPPRawQ_1 i.1 j.1 : ℝ) := fun i j => by
    rw [intervalIntegral.integral_const_mul, int_pp_1 i j]
  have hSumI : ∀ i : Fin 11, (∫ y in (-1 : ℝ)..1, ∑ j : Fin 11,
      (m i * m j) * (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y *
        polyEval (match j.1 with | 0 => iBasis_4_0 | 1 => iBasis_4_1 | 2 => iBasis_4_2 | 3 => iBasis_4_3 | 4 => iBasis_4_4 | 5 => iBasis_4_5 | 6 => iBasis_4_6 | 7 => iBasis_4_7 | 8 => iBasis_4_8 | 9 => iBasis_4_9 | 10 => iBasis_4_10 | _ => []) y)) =
      ∑ j : Fin 11, (m i * m j) * (ApertureLogTwo.matQ mPPRawQ_1 i.1 j.1 : ℝ) := fun i => by
    rw [intervalIntegral.integral_finsetSum fun j _ =>
      (show Continuous fun y : ℝ => (m i * m j) *
        (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y *
         polyEval (match j.1 with | 0 => iBasis_4_0 | 1 => iBasis_4_1 | 2 => iBasis_4_2 | 3 => iBasis_4_3 | 4 => iBasis_4_4 | 5 => iBasis_4_5 | 6 => iBasis_4_6 | 7 => iBasis_4_7 | 8 => iBasis_4_8 | 9 => iBasis_4_9 | 10 => iBasis_4_10 | _ => []) y) from
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
    (hLowProj : ∀ y : ℝ, lowProj (dilateLogTwo F) 23 y =
      ∑ k : Fin 11, halfMoment (dilateLogTwo F) k * basisFn k y)
    (hHopp : ∀ r : ℕ, regionalLegendreMoment (dilateLogTwo F) (23 + (2 * r + 1)) = 0) :
    let G := dilateLogTwo F
    let m := halfMoment G
    let M_res := (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 23 x) ^ 2) / 2
    apow0_4 * (∑ i : Fin 11, ∑ j : Fin 11, qOddMat_1 i j * m i * m j) -
      (∑ i : Fin 11, (errApow_4 * qOddRowAbs_1 i) * m i ^ 2) -
      ((28330699806371863465765559550147688507568454001005121 / 10000000000000000000000000000000000000000000000000000000 : ℝ) * ∑ r ∈ Finset.range 2,
        ((2 * ↑(23 + 2 * r) + 1) / 2) * (∑ i : Fin 11, m i * gHi_1 i r) ^ 2) -
      ((1 / 2000 : ℝ) + (53861523002719472107082803467484904070644308185446063804726431212902824004833568504936804890286021363709 / 194818182068004874472224973590719464580142832654429411005735291835112933326006093120000000000000000000000000 : ℝ)) * M_res ≤
      ((-7 / 5760 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 3 * autocorr F t) /
        (2 * apertureLogTwo) := by
  intro G m M_res
  have hA_pos : 0 < apertureLogTwo := apertureLogTwo_pos
  set R_res : ℝ → ℝ := fun x => G x - lowProj G 23 x
  have hRc : Continuous R_res := hGc.sub (contDiff_lowProj G _ (k := 0)).continuous
  have hMres_nn : 0 ≤ M_res := div_nonneg (setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _) (by norm_num)
  have hIntR2 : (∫ x in Icc (-1 : ℝ) 1, R_res x ^ 2) = 2 * M_res := by dsimp [R_res, M_res]; ring
  have hpi_lo : piLo ≤ Real.pi := (pi_bounds_d20).1
  have hpi_pos : 0 < piLo := by norm_num [piLo]
  have h4pi : 4 / Real.pi ^ 2 ≤ 4 / piLo ^ 2 := by
    have hp2 : piLo ^ 2 ≤ Real.pi ^ 2 := pow_le_pow_left₀ hpi_pos.le hpi_lo 2
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hp2
  have hdil := dilated_correlation_moment_log_two F 3
  have hdec := odd_lag_moment_lowProj_decomp hGc hsG (m := 23) (q := 1) (by omega)
  change (∫ t in Ioc (0 : ℝ) 2, t ^ 3 * autocorr G t) =
    ((3 : ℕ).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, lowProj G 23 y * iterPrim 4 (lowProj G 23) y) +
    2 * ((3 : ℕ).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, R_res y * iterPrim 4 (lowProj G 23) y) +
    (-1 : ℝ) ^ (1 + 1) * ((3 : ℕ).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, iterPrim (1 + 1) R_res y ^ 2) at hdec
  have hPP := hPP_eq_1 hLowProj
  have hPP_pert := symm_quad_scale_pert qOddMat_1 qOddMat_1_sym abs_aperture_pow_4_sub m
  simp_rw [qOddRowAbs_1_eq] at hPP_pert
  have hWirt := iterPrim_sq_le_wirtinger hRc (m := 23) (fun n hn => sub_lowProj_moment_lt hGc hn) (1 + 1) (by omega)
  have hWirt' : (∫ y in (-1 : ℝ)..1, iterPrim (1 + 1) R_res y ^ 2) ≤ (4 / piLo ^ 2) ^ (1 + 1) * (2 * M_res) := by
    rw [hIntR2] at hWirt
    exact hWirt.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h4pi (1 + 1)) (by positivity))
  have hCross := high_mode_cross_sq_le hGc (m := 23) (q := 1) (by omega) hHopp
  change (∫ y in (-1 : ℝ)..1, R_res y * iterPrim 4 (lowProj G 23) y) ^ 2 ≤
    (∑ r ∈ Finset.range (1 + 1), ((2 * ↑(23 + 2 * r) + 1) / 2) *
      regionalLegendreMoment (iterPrim 4 (lowProj G 23)) (23 + 2 * r) ^ 2) *
    (∫ y in Icc (-1 : ℝ) 1, R_res y ^ 2) at hCross
  rw [hIntR2] at hCross
  have hMomLin : ∀ r ∈ Finset.range (1 + 1), regionalLegendreMoment (iterPrim 4 (lowProj G 23)) (23 + 2 * r) =
      ∑ i : Fin 11, m i * gHi_1 i r := fun r hr => by
    have hlin : regionalLegendreMoment (iterPrim 4 (lowProj G 23)) (23 + 2 * r) =
        ∑ i : Fin 11, m i * regionalLegendreMoment (polyEval (match i.1 with | 0 => iBasis_4_0 | 1 => iBasis_4_1 | 2 => iBasis_4_2 | 3 => iBasis_4_3 | 4 => iBasis_4_4 | 5 => iBasis_4_5 | 6 => iBasis_4_6 | 7 => iBasis_4_7 | 8 => iBasis_4_8 | 9 => iBasis_4_9 | 10 => iBasis_4_10 | _ => [])) (23 + 2 * r) := by
      unfold regionalLegendreMoment
      have hfn : ∀ x : ℝ, iterPrim 4 (lowProj G 23) x * legP (23 + 2 * r) x =
          ∑ i : Fin 11, m i * (polyEval (match i.1 with | 0 => iBasis_4_0 | 1 => iBasis_4_1 | 2 => iBasis_4_2 | 3 => iBasis_4_3 | 4 => iBasis_4_4 | 5 => iBasis_4_5 | 6 => iBasis_4_6 | 7 => iBasis_4_7 | 8 => iBasis_4_8 | 9 => iBasis_4_9 | 10 => iBasis_4_10 | _ => []) x * legP (23 + 2 * r) x) := fun x => by
        rw [hIterP_eq_1 hLowProj x, Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by dsimp only [m]; ring
      simp_rw [hfn]
      rw [integral_finsetSum _ fun i _ =>
        (show Continuous fun x : ℝ => m i * (polyEval (match i.1 with | 0 => iBasis_4_0 | 1 => iBasis_4_1 | 2 => iBasis_4_2 | 3 => iBasis_4_3 | 4 => iBasis_4_4 | 5 => iBasis_4_5 | 6 => iBasis_4_6 | 7 => iBasis_4_7 | 8 => iBasis_4_8 | 9 => iBasis_4_9 | 10 => iBasis_4_10 | _ => []) x * legP (23 + 2 * r) x) from
          continuous_const.mul ((continuous_polyEval _).mul (continuous_legP _))).integrableOn_Icc]
      exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    rw [hlin]; exact Finset.sum_congr rfl fun i _ => by rw [gHi_eq_1 i r hr]
  set A_sp : ℝ := ∑ r ∈ Finset.range (1 + 1), ((2 * ↑(23 + 2 * r) + 1) / 2) *
    (∑ i : Fin 11, m i * gHi_1 i r) ^ 2
  have hAsp_eq : (∑ r ∈ Finset.range (1 + 1), ((2 * ↑(23 + 2 * r) + 1) / 2) *
      regionalLegendreMoment (iterPrim 4 (lowProj G 23)) (23 + 2 * r) ^ 2) = A_sp :=
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
  set I_RP : ℝ := ∫ y in (-1 : ℝ)..1, R_res y * iterPrim 4 (lowProj G 23) y
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
        (∫ y in (-1 : ℝ)..1, lowProj G 23 y * iterPrim 4 (lowProj G 23) y)) +
      (-1 : ℝ) * (2 * (w_true * I_RP)) -
      w_true * (∫ y in (-1 : ℝ)..1, iterPrim (1 + 1) R_res y ^ 2) := by
    rw [hdil, hdec]; dsimp [w_true, I_RP]; field_simp [hA_pos.ne']; norm_num; ring
  rw [hdiv_tot, hPP]
  have hsc_eq : (2 * ((168317259383498350334633761 / 200000000000000000000000000000 : ℝ)) ^ 2 / (1 / 2000 : ℝ)) = (28330699806371863465765559550147688507568454001005121 / 10000000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num
  rw [hsc_eq] at hy
  linarith [hPP_pert, hy.2, hw_wirt]

private theorem hIterP_eq_2 {G : ℝ → ℝ}
    (hLowProj : ∀ y : ℝ, lowProj G 23 y = ∑ k : Fin 11, halfMoment G k * basisFn k y) (y : ℝ) :
    iterPrim 6 (lowProj G 23) y =
      ∑ j : Fin 11, halfMoment G j * polyEval (match j.1 with | 0 => iBasis_6_0 | 1 => iBasis_6_1 | 2 => iBasis_6_2 | 3 => iBasis_6_3 | 4 => iBasis_6_4 | 5 => iBasis_6_5 | 6 => iBasis_6_6 | 7 => iBasis_6_7 | 8 => iBasis_6_8 | 9 => iBasis_6_9 | 10 => iBasis_6_10 | _ => []) y := by
  have hlp_eq : lowProj G 23 = fun u => ∑ j : Fin 11, halfMoment G j * basisFn j u := funext hLowProj
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

private theorem hPP_eq_2 {G : ℝ → ℝ}
    (hLowProj : ∀ y : ℝ, lowProj G 23 y = ∑ k : Fin 11, halfMoment G k * basisFn k y) :
    ((31 / 1935360 : ℝ) * ((5 : ℕ).factorial : ℝ)) *
      (∫ y in (-1 : ℝ)..1, lowProj G 23 y * iterPrim 6 (lowProj G 23) y) =
      ∑ i : Fin 11, ∑ j : Fin 11, qOddMat_2 i j * halfMoment G i * halfMoment G j := by
  set m := halfMoment G
  have hfn : ∀ y : ℝ, lowProj G 23 y * iterPrim 6 (lowProj G 23) y =
      ∑ i : Fin 11, ∑ j : Fin 11, (m i * m j) *
        (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y *
         polyEval (match j.1 with | 0 => iBasis_6_0 | 1 => iBasis_6_1 | 2 => iBasis_6_2 | 3 => iBasis_6_3 | 4 => iBasis_6_4 | 5 => iBasis_6_5 | 6 => iBasis_6_6 | 7 => iBasis_6_7 | 8 => iBasis_6_8 | 9 => iBasis_6_9 | 10 => iBasis_6_10 | _ => []) y) := fun y => by
    rw [hLowProj y, hIterP_eq_2 hLowProj y, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    have hb : basisFn i y = polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y := by
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
    rw [hb]; dsimp only [m]; ring
  simp_rw [hfn]
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (show Continuous fun y : ℝ => ∑ j : Fin 11, (m i * m j) *
      (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y *
       polyEval (match j.1 with | 0 => iBasis_6_0 | 1 => iBasis_6_1 | 2 => iBasis_6_2 | 3 => iBasis_6_3 | 4 => iBasis_6_4 | 5 => iBasis_6_5 | 6 => iBasis_6_6 | 7 => iBasis_6_7 | 8 => iBasis_6_8 | 9 => iBasis_6_9 | 10 => iBasis_6_10 | _ => []) y) from
      continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_polyEval _).mul (continuous_polyEval _))).intervalIntegrable (-1) 1]
  have hEach : ∀ (i j : Fin 11), (∫ y in (-1 : ℝ)..1,
      (m i * m j) * (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y *
        polyEval (match j.1 with | 0 => iBasis_6_0 | 1 => iBasis_6_1 | 2 => iBasis_6_2 | 3 => iBasis_6_3 | 4 => iBasis_6_4 | 5 => iBasis_6_5 | 6 => iBasis_6_6 | 7 => iBasis_6_7 | 8 => iBasis_6_8 | 9 => iBasis_6_9 | 10 => iBasis_6_10 | _ => []) y)) =
      (m i * m j) * (ApertureLogTwo.matQ mPPRawQ_2 i.1 j.1 : ℝ) := fun i j => by
    rw [intervalIntegral.integral_const_mul, int_pp_2 i j]
  have hSumI : ∀ i : Fin 11, (∫ y in (-1 : ℝ)..1, ∑ j : Fin 11,
      (m i * m j) * (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y *
        polyEval (match j.1 with | 0 => iBasis_6_0 | 1 => iBasis_6_1 | 2 => iBasis_6_2 | 3 => iBasis_6_3 | 4 => iBasis_6_4 | 5 => iBasis_6_5 | 6 => iBasis_6_6 | 7 => iBasis_6_7 | 8 => iBasis_6_8 | 9 => iBasis_6_9 | 10 => iBasis_6_10 | _ => []) y)) =
      ∑ j : Fin 11, (m i * m j) * (ApertureLogTwo.matQ mPPRawQ_2 i.1 j.1 : ℝ) := fun i => by
    rw [intervalIntegral.integral_finsetSum fun j _ =>
      (show Continuous fun y : ℝ => (m i * m j) *
        (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y *
         polyEval (match j.1 with | 0 => iBasis_6_0 | 1 => iBasis_6_1 | 2 => iBasis_6_2 | 3 => iBasis_6_3 | 4 => iBasis_6_4 | 5 => iBasis_6_5 | 6 => iBasis_6_6 | 7 => iBasis_6_7 | 8 => iBasis_6_8 | 9 => iBasis_6_9 | 10 => iBasis_6_10 | _ => []) y) from
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
    (hLowProj : ∀ y : ℝ, lowProj (dilateLogTwo F) 23 y =
      ∑ k : Fin 11, halfMoment (dilateLogTwo F) k * basisFn k y)
    (hHopp : ∀ r : ℕ, regionalLegendreMoment (dilateLogTwo F) (23 + (2 * r + 1)) = 0) :
    let G := dilateLogTwo F
    let m := halfMoment G
    let M_res := (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 23 x) ^ 2) / 2
    apow0_6 * (∑ i : Fin 11, ∑ j : Fin 11, qOddMat_2 i j * m i * m j) -
      (∑ i : Fin 11, (errApow_6 * qOddRowAbs_2 i) * m i ^ 2) -
      ((1817723751476543414437681449293926857541879379346961 / 2000000000000000000000000000000000000000000000000000000 : ℝ) * ∑ r ∈ Finset.range 3,
        ((2 * ↑(23 + 2 * r) + 1) / 2) * (∑ i : Fin 11, m i * gHi_2 i r) ^ 2) -
      ((1 / 10000 : ℝ) + (382007553755863926870040042097449282156357447299937480899016149154433081824883286535181352428961783385936212243165829737413357202226711792633500829201931631 / 13459448710054262118355122316425225466502542667336215127570474536177358766844660236371912877458932196995890038503706807375744000000000000000000000000000000000000 : ℝ)) * M_res ≤
      ((31 / 967680 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 5 * autocorr F t) /
        (2 * apertureLogTwo) := by
  intro G m M_res
  have hA_pos : 0 < apertureLogTwo := apertureLogTwo_pos
  set R_res : ℝ → ℝ := fun x => G x - lowProj G 23 x
  have hRc : Continuous R_res := hGc.sub (contDiff_lowProj G _ (k := 0)).continuous
  have hMres_nn : 0 ≤ M_res := div_nonneg (setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _) (by norm_num)
  have hIntR2 : (∫ x in Icc (-1 : ℝ) 1, R_res x ^ 2) = 2 * M_res := by dsimp [R_res, M_res]; ring
  have hpi_lo : piLo ≤ Real.pi := (pi_bounds_d20).1
  have hpi_pos : 0 < piLo := by norm_num [piLo]
  have h4pi : 4 / Real.pi ^ 2 ≤ 4 / piLo ^ 2 := by
    have hp2 : piLo ^ 2 ≤ Real.pi ^ 2 := pow_le_pow_left₀ hpi_pos.le hpi_lo 2
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hp2
  have hdil := dilated_correlation_moment_log_two F 5
  have hdec := odd_lag_moment_lowProj_decomp hGc hsG (m := 23) (q := 2) (by omega)
  change (∫ t in Ioc (0 : ℝ) 2, t ^ 5 * autocorr G t) =
    ((5 : ℕ).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, lowProj G 23 y * iterPrim 6 (lowProj G 23) y) +
    2 * ((5 : ℕ).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, R_res y * iterPrim 6 (lowProj G 23) y) +
    (-1 : ℝ) ^ (2 + 1) * ((5 : ℕ).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, iterPrim (2 + 1) R_res y ^ 2) at hdec
  have hPP := hPP_eq_2 hLowProj
  have hPP_pert := symm_quad_scale_pert qOddMat_2 qOddMat_2_sym abs_aperture_pow_6_sub m
  simp_rw [qOddRowAbs_2_eq] at hPP_pert
  have hWirt := iterPrim_sq_le_wirtinger hRc (m := 23) (fun n hn => sub_lowProj_moment_lt hGc hn) (2 + 1) (by omega)
  have hWirt' : (∫ y in (-1 : ℝ)..1, iterPrim (2 + 1) R_res y ^ 2) ≤ (4 / piLo ^ 2) ^ (2 + 1) * (2 * M_res) := by
    rw [hIntR2] at hWirt
    exact hWirt.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h4pi (2 + 1)) (by positivity))
  have hCross := high_mode_cross_sq_le hGc (m := 23) (q := 2) (by omega) hHopp
  change (∫ y in (-1 : ℝ)..1, R_res y * iterPrim 6 (lowProj G 23) y) ^ 2 ≤
    (∑ r ∈ Finset.range (2 + 1), ((2 * ↑(23 + 2 * r) + 1) / 2) *
      regionalLegendreMoment (iterPrim 6 (lowProj G 23)) (23 + 2 * r) ^ 2) *
    (∫ y in Icc (-1 : ℝ) 1, R_res y ^ 2) at hCross
  rw [hIntR2] at hCross
  have hMomLin : ∀ r ∈ Finset.range (2 + 1), regionalLegendreMoment (iterPrim 6 (lowProj G 23)) (23 + 2 * r) =
      ∑ i : Fin 11, m i * gHi_2 i r := fun r hr => by
    have hlin : regionalLegendreMoment (iterPrim 6 (lowProj G 23)) (23 + 2 * r) =
        ∑ i : Fin 11, m i * regionalLegendreMoment (polyEval (match i.1 with | 0 => iBasis_6_0 | 1 => iBasis_6_1 | 2 => iBasis_6_2 | 3 => iBasis_6_3 | 4 => iBasis_6_4 | 5 => iBasis_6_5 | 6 => iBasis_6_6 | 7 => iBasis_6_7 | 8 => iBasis_6_8 | 9 => iBasis_6_9 | 10 => iBasis_6_10 | _ => [])) (23 + 2 * r) := by
      unfold regionalLegendreMoment
      have hfn : ∀ x : ℝ, iterPrim 6 (lowProj G 23) x * legP (23 + 2 * r) x =
          ∑ i : Fin 11, m i * (polyEval (match i.1 with | 0 => iBasis_6_0 | 1 => iBasis_6_1 | 2 => iBasis_6_2 | 3 => iBasis_6_3 | 4 => iBasis_6_4 | 5 => iBasis_6_5 | 6 => iBasis_6_6 | 7 => iBasis_6_7 | 8 => iBasis_6_8 | 9 => iBasis_6_9 | 10 => iBasis_6_10 | _ => []) x * legP (23 + 2 * r) x) := fun x => by
        rw [hIterP_eq_2 hLowProj x, Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by dsimp only [m]; ring
      simp_rw [hfn]
      rw [integral_finsetSum _ fun i _ =>
        (show Continuous fun x : ℝ => m i * (polyEval (match i.1 with | 0 => iBasis_6_0 | 1 => iBasis_6_1 | 2 => iBasis_6_2 | 3 => iBasis_6_3 | 4 => iBasis_6_4 | 5 => iBasis_6_5 | 6 => iBasis_6_6 | 7 => iBasis_6_7 | 8 => iBasis_6_8 | 9 => iBasis_6_9 | 10 => iBasis_6_10 | _ => []) x * legP (23 + 2 * r) x) from
          continuous_const.mul ((continuous_polyEval _).mul (continuous_legP _))).integrableOn_Icc]
      exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    rw [hlin]; exact Finset.sum_congr rfl fun i _ => by rw [gHi_eq_2 i r hr]
  set A_sp : ℝ := ∑ r ∈ Finset.range (2 + 1), ((2 * ↑(23 + 2 * r) + 1) / 2) *
    (∑ i : Fin 11, m i * gHi_2 i r) ^ 2
  have hAsp_eq : (∑ r ∈ Finset.range (2 + 1), ((2 * ↑(23 + 2 * r) + 1) / 2) *
      regionalLegendreMoment (iterPrim 6 (lowProj G 23)) (23 + 2 * r) ^ 2) = A_sp :=
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
  set I_RP : ℝ := ∫ y in (-1 : ℝ)..1, R_res y * iterPrim 6 (lowProj G 23) y
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
        (∫ y in (-1 : ℝ)..1, lowProj G 23 y * iterPrim 6 (lowProj G 23) y)) +
      (1 : ℝ) * (2 * (w_true * I_RP)) -
      w_true * (∫ y in (-1 : ℝ)..1, iterPrim (2 + 1) R_res y ^ 2) := by
    rw [hdil, hdec]; dsimp [w_true, I_RP]; field_simp [hA_pos.ne']; norm_num; ring
  rw [hdiv_tot, hPP]
  have hsc_eq : (2 * ((42634771624538384695316969 / 200000000000000000000000000000 : ℝ)) ^ 2 / (1 / 10000 : ℝ)) = (1817723751476543414437681449293926857541879379346961 / 2000000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num
  rw [hsc_eq] at hy
  linarith [hPP_pert, hy.1, hw_wirt]

private theorem hIterP_eq_3 {G : ℝ → ℝ}
    (hLowProj : ∀ y : ℝ, lowProj G 23 y = ∑ k : Fin 11, halfMoment G k * basisFn k y) (y : ℝ) :
    iterPrim 8 (lowProj G 23) y =
      ∑ j : Fin 11, halfMoment G j * polyEval (match j.1 with | 0 => iBasis_8_0 | 1 => iBasis_8_1 | 2 => iBasis_8_2 | 3 => iBasis_8_3 | 4 => iBasis_8_4 | 5 => iBasis_8_5 | 6 => iBasis_8_6 | 7 => iBasis_8_7 | 8 => iBasis_8_8 | 9 => iBasis_8_9 | 10 => iBasis_8_10 | _ => []) y := by
  have hlp_eq : lowProj G 23 = fun u => ∑ j : Fin 11, halfMoment G j * basisFn j u := funext hLowProj
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

private theorem hPP_eq_3 {G : ℝ → ℝ}
    (hLowProj : ∀ y : ℝ, lowProj G 23 y = ∑ k : Fin 11, halfMoment G k * basisFn k y) :
    ((-127 / 309657600 : ℝ) * ((7 : ℕ).factorial : ℝ)) *
      (∫ y in (-1 : ℝ)..1, lowProj G 23 y * iterPrim 8 (lowProj G 23) y) =
      ∑ i : Fin 11, ∑ j : Fin 11, qOddMat_3 i j * halfMoment G i * halfMoment G j := by
  set m := halfMoment G
  have hfn : ∀ y : ℝ, lowProj G 23 y * iterPrim 8 (lowProj G 23) y =
      ∑ i : Fin 11, ∑ j : Fin 11, (m i * m j) *
        (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y *
         polyEval (match j.1 with | 0 => iBasis_8_0 | 1 => iBasis_8_1 | 2 => iBasis_8_2 | 3 => iBasis_8_3 | 4 => iBasis_8_4 | 5 => iBasis_8_5 | 6 => iBasis_8_6 | 7 => iBasis_8_7 | 8 => iBasis_8_8 | 9 => iBasis_8_9 | 10 => iBasis_8_10 | _ => []) y) := fun y => by
    rw [hLowProj y, hIterP_eq_3 hLowProj y, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    have hb : basisFn i y = polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y := by
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
    rw [hb]; dsimp only [m]; ring
  simp_rw [hfn]
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (show Continuous fun y : ℝ => ∑ j : Fin 11, (m i * m j) *
      (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y *
       polyEval (match j.1 with | 0 => iBasis_8_0 | 1 => iBasis_8_1 | 2 => iBasis_8_2 | 3 => iBasis_8_3 | 4 => iBasis_8_4 | 5 => iBasis_8_5 | 6 => iBasis_8_6 | 7 => iBasis_8_7 | 8 => iBasis_8_8 | 9 => iBasis_8_9 | 10 => iBasis_8_10 | _ => []) y) from
      continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_polyEval _).mul (continuous_polyEval _))).intervalIntegrable (-1) 1]
  have hEach : ∀ (i j : Fin 11), (∫ y in (-1 : ℝ)..1,
      (m i * m j) * (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y *
        polyEval (match j.1 with | 0 => iBasis_8_0 | 1 => iBasis_8_1 | 2 => iBasis_8_2 | 3 => iBasis_8_3 | 4 => iBasis_8_4 | 5 => iBasis_8_5 | 6 => iBasis_8_6 | 7 => iBasis_8_7 | 8 => iBasis_8_8 | 9 => iBasis_8_9 | 10 => iBasis_8_10 | _ => []) y)) =
      (m i * m j) * (ApertureLogTwo.matQ mPPRawQ_3 i.1 j.1 : ℝ) := fun i j => by
    rw [intervalIntegral.integral_const_mul, int_pp_3 i j]
  have hSumI : ∀ i : Fin 11, (∫ y in (-1 : ℝ)..1, ∑ j : Fin 11,
      (m i * m j) * (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y *
        polyEval (match j.1 with | 0 => iBasis_8_0 | 1 => iBasis_8_1 | 2 => iBasis_8_2 | 3 => iBasis_8_3 | 4 => iBasis_8_4 | 5 => iBasis_8_5 | 6 => iBasis_8_6 | 7 => iBasis_8_7 | 8 => iBasis_8_8 | 9 => iBasis_8_9 | 10 => iBasis_8_10 | _ => []) y)) =
      ∑ j : Fin 11, (m i * m j) * (ApertureLogTwo.matQ mPPRawQ_3 i.1 j.1 : ℝ) := fun i => by
    rw [intervalIntegral.integral_finsetSum fun j _ =>
      (show Continuous fun y : ℝ => (m i * m j) *
        (polyEval (match i.1 with | 0 => iBasis_0_0 | 1 => iBasis_0_1 | 2 => iBasis_0_2 | 3 => iBasis_0_3 | 4 => iBasis_0_4 | 5 => iBasis_0_5 | 6 => iBasis_0_6 | 7 => iBasis_0_7 | 8 => iBasis_0_8 | 9 => iBasis_0_9 | 10 => iBasis_0_10 | _ => []) y *
         polyEval (match j.1 with | 0 => iBasis_8_0 | 1 => iBasis_8_1 | 2 => iBasis_8_2 | 3 => iBasis_8_3 | 4 => iBasis_8_4 | 5 => iBasis_8_5 | 6 => iBasis_8_6 | 7 => iBasis_8_7 | 8 => iBasis_8_8 | 9 => iBasis_8_9 | 10 => iBasis_8_10 | _ => []) y) from
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
    (hLowProj : ∀ y : ℝ, lowProj (dilateLogTwo F) 23 y =
      ∑ k : Fin 11, halfMoment (dilateLogTwo F) k * basisFn k y)
    (hHopp : ∀ r : ℕ, regionalLegendreMoment (dilateLogTwo F) (23 + (2 * r + 1)) = 0) :
    let G := dilateLogTwo F
    let m := halfMoment G
    let M_res := (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 23 x) ^ 2) / 2
    apow0_8 * (∑ i : Fin 11, ∑ j : Fin 11, qOddMat_3 i j * m i * m j) -
      (∑ i : Fin 11, (errApow_8 * qOddRowAbs_3 i) * m i ^ 2) -
      ((758215087248897189698082177505805158304254384420441 / 3125000000000000000000000000000000000000000000000000000 : ℝ) * ∑ r ∈ Finset.range 4,
        ((2 * ↑(23 + 2 * r) + 1) / 2) * (∑ i : Fin 11, m i * gHi_3 i r) ^ 2) -
      ((1 / 10000 : ℝ) + (22557250092361518979566609068529228089780654586780885254538200430789283596098329818441434603407994823459309232798751189533174099872231837246879315921935155407331594126769932678225759225724499012476352239023989 / 3795412406428229602825882065186703220341047511512819244508569433840429098759629451289235019100310039491848137147870930625982176425560167199889414890861467136611133440000000000000000000000000000000000000000000000000 : ℝ)) * M_res ≤
      ((-127 / 154828800 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 7 * autocorr F t) /
        (2 * apertureLogTwo) := by
  intro G m M_res
  have hA_pos : 0 < apertureLogTwo := apertureLogTwo_pos
  set R_res : ℝ → ℝ := fun x => G x - lowProj G 23 x
  have hRc : Continuous R_res := hGc.sub (contDiff_lowProj G _ (k := 0)).continuous
  have hMres_nn : 0 ≤ M_res := div_nonneg (setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _) (by norm_num)
  have hIntR2 : (∫ x in Icc (-1 : ℝ) 1, R_res x ^ 2) = 2 * M_res := by dsimp [R_res, M_res]; ring
  have hpi_lo : piLo ≤ Real.pi := (pi_bounds_d20).1
  have hpi_pos : 0 < piLo := by norm_num [piLo]
  have h4pi : 4 / Real.pi ^ 2 ≤ 4 / piLo ^ 2 := by
    have hp2 : piLo ^ 2 ≤ Real.pi ^ 2 := pow_le_pow_left₀ hpi_pos.le hpi_lo 2
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hp2
  have hdil := dilated_correlation_moment_log_two F 7
  have hdec := odd_lag_moment_lowProj_decomp hGc hsG (m := 23) (q := 3) (by omega)
  change (∫ t in Ioc (0 : ℝ) 2, t ^ 7 * autocorr G t) =
    ((7 : ℕ).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, lowProj G 23 y * iterPrim 8 (lowProj G 23) y) +
    2 * ((7 : ℕ).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, R_res y * iterPrim 8 (lowProj G 23) y) +
    (-1 : ℝ) ^ (3 + 1) * ((7 : ℕ).factorial : ℝ) * (∫ y in (-1 : ℝ)..1, iterPrim (3 + 1) R_res y ^ 2) at hdec
  have hPP := hPP_eq_3 hLowProj
  have hPP_pert := symm_quad_scale_pert qOddMat_3 qOddMat_3_sym abs_aperture_pow_8_sub m
  simp_rw [qOddRowAbs_3_eq] at hPP_pert
  have hWirt := iterPrim_sq_le_wirtinger hRc (m := 23) (fun n hn => sub_lowProj_moment_lt hGc hn) (3 + 1) (by omega)
  have hWirt' : (∫ y in (-1 : ℝ)..1, iterPrim (3 + 1) R_res y ^ 2) ≤ (4 / piLo ^ 2) ^ (3 + 1) * (2 * M_res) := by
    rw [hIntR2] at hWirt
    exact hWirt.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h4pi (3 + 1)) (by positivity))
  have hCross := high_mode_cross_sq_le hGc (m := 23) (q := 3) (by omega) hHopp
  change (∫ y in (-1 : ℝ)..1, R_res y * iterPrim 8 (lowProj G 23) y) ^ 2 ≤
    (∑ r ∈ Finset.range (3 + 1), ((2 * ↑(23 + 2 * r) + 1) / 2) *
      regionalLegendreMoment (iterPrim 8 (lowProj G 23)) (23 + 2 * r) ^ 2) *
    (∫ y in Icc (-1 : ℝ) 1, R_res y ^ 2) at hCross
  rw [hIntR2] at hCross
  have hMomLin : ∀ r ∈ Finset.range (3 + 1), regionalLegendreMoment (iterPrim 8 (lowProj G 23)) (23 + 2 * r) =
      ∑ i : Fin 11, m i * gHi_3 i r := fun r hr => by
    have hlin : regionalLegendreMoment (iterPrim 8 (lowProj G 23)) (23 + 2 * r) =
        ∑ i : Fin 11, m i * regionalLegendreMoment (polyEval (match i.1 with | 0 => iBasis_8_0 | 1 => iBasis_8_1 | 2 => iBasis_8_2 | 3 => iBasis_8_3 | 4 => iBasis_8_4 | 5 => iBasis_8_5 | 6 => iBasis_8_6 | 7 => iBasis_8_7 | 8 => iBasis_8_8 | 9 => iBasis_8_9 | 10 => iBasis_8_10 | _ => [])) (23 + 2 * r) := by
      unfold regionalLegendreMoment
      have hfn : ∀ x : ℝ, iterPrim 8 (lowProj G 23) x * legP (23 + 2 * r) x =
          ∑ i : Fin 11, m i * (polyEval (match i.1 with | 0 => iBasis_8_0 | 1 => iBasis_8_1 | 2 => iBasis_8_2 | 3 => iBasis_8_3 | 4 => iBasis_8_4 | 5 => iBasis_8_5 | 6 => iBasis_8_6 | 7 => iBasis_8_7 | 8 => iBasis_8_8 | 9 => iBasis_8_9 | 10 => iBasis_8_10 | _ => []) x * legP (23 + 2 * r) x) := fun x => by
        rw [hIterP_eq_3 hLowProj x, Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by dsimp only [m]; ring
      simp_rw [hfn]
      rw [integral_finsetSum _ fun i _ =>
        (show Continuous fun x : ℝ => m i * (polyEval (match i.1 with | 0 => iBasis_8_0 | 1 => iBasis_8_1 | 2 => iBasis_8_2 | 3 => iBasis_8_3 | 4 => iBasis_8_4 | 5 => iBasis_8_5 | 6 => iBasis_8_6 | 7 => iBasis_8_7 | 8 => iBasis_8_8 | 9 => iBasis_8_9 | 10 => iBasis_8_10 | _ => []) x * legP (23 + 2 * r) x) from
          continuous_const.mul ((continuous_polyEval _).mul (continuous_legP _))).integrableOn_Icc]
      exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    rw [hlin]; exact Finset.sum_congr rfl fun i _ => by rw [gHi_eq_3 i r hr]
  set A_sp : ℝ := ∑ r ∈ Finset.range (3 + 1), ((2 * ↑(23 + 2 * r) + 1) / 2) *
    (∑ i : Fin 11, m i * gHi_3 i r) ^ 2
  have hAsp_eq : (∑ r ∈ Finset.range (3 + 1), ((2 * ↑(23 + 2 * r) + 1) / 2) *
      regionalLegendreMoment (iterPrim 8 (lowProj G 23)) (23 + 2 * r) ^ 2) = A_sp :=
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
  set I_RP : ℝ := ∫ y in (-1 : ℝ)..1, R_res y * iterPrim 8 (lowProj G 23) y
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
        (∫ y in (-1 : ℝ)..1, lowProj G 23 y * iterPrim 8 (lowProj G 23) y)) +
      (-1 : ℝ) * (2 * (w_true * I_RP)) -
      w_true * (∫ y in (-1 : ℝ)..1, iterPrim (3 + 1) R_res y ^ 2) := by
    rw [hdil, hdec]; dsimp [w_true, I_RP]; field_simp [hA_pos.ne']; norm_num; ring
  rw [hdiv_tot, hPP]
  have hsc_eq : (2 * ((27535705679152244848103771 / 250000000000000000000000000000 : ℝ)) ^ 2 / (1 / 10000 : ℝ)) = (758215087248897189698082177505805158304254384420441 / 3125000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num
  rw [hsc_eq] at hy
  linarith [hPP_pert, hy.2, hw_wirt]

private theorem bFast_quad_decomp (m : Fin 11 → ℝ) :
    (∑ i : Fin 11, ∑ j : Fin 11, bFastMat i j * m i * m j) =
      ((27685582518462127862237499 / 7436429000000000000000000 : ℝ) * (∑ k : Fin 11, (2 * (degAt k : ℝ) + 1) * m k ^ 2) -
        ((3 : ℝ) * m ⟨0, by omega⟩ ^ 2 + (77 / 6 : ℝ) * m ⟨1, by omega⟩ ^ 2 + (1507 / 60 : ℝ) * m ⟨2, by omega⟩ ^ 2 + (1089 / 28 : ℝ) * m ⟨3, by omega⟩ ^ 2 + (135451 / 2520 : ℝ) * m ⟨4, by omega⟩ ^ 2 + (1925353 / 27720 : ℝ) * m ⟨5, by omega⟩ ^ 2 + (3437979 / 40040 : ℝ) * m ⟨6, by omega⟩ ^ 2 + (37068467 / 360360 : ℝ) * m ⟨7, by omega⟩ ^ 2 + (42142223 / 350064 : ℝ) * m ⟨8, by omega⟩ ^ 2 + (275295799 / 1989680 : ℝ) * m ⟨9, by omega⟩ ^ 2 + (810896279 / 5173168 : ℝ) * m ⟨10, by omega⟩ ^ 2)) +
      ((-(apow0_1 * (∑ i : Fin 11, ∑ j : Fin 11, qEvMat_0 i j * m i * m j) - (∑ i : Fin 11, (errApow_1 * qEvRowAbs_0 i) * m i ^ 2))) +
       (-(apow0_3 * (∑ i : Fin 11, ∑ j : Fin 11, qEvMat_1 i j * m i * m j) - (∑ i : Fin 11, (errApow_3 * qEvRowAbs_1 i) * m i ^ 2))) +
       (-(apow0_5 * (∑ i : Fin 11, ∑ j : Fin 11, qEvMat_2 i j * m i * m j) - (∑ i : Fin 11, (errApow_5 * qEvRowAbs_2 i) * m i ^ 2))) +
       (-(apow0_7 * (∑ i : Fin 11, ∑ j : Fin 11, qEvMat_3 i j * m i * m j) - (∑ i : Fin 11, (errApow_7 * qEvRowAbs_3 i) * m i ^ 2))) +
       (-(apow0_9 * (∑ i : Fin 11, ∑ j : Fin 11, qEvMat_4 i j * m i * m j) - (∑ i : Fin 11, (errApow_9 * qEvRowAbs_4 i) * m i ^ 2))) +
       (-(apow0_11 * (∑ i : Fin 11, ∑ j : Fin 11, qEvMat_5 i j * m i * m j) - (∑ i : Fin 11, (errApow_11 * qEvRowAbs_5 i) * m i ^ 2))) +
       (-(apow0_13 * (∑ i : Fin 11, ∑ j : Fin 11, qEvMat_6 i j * m i * m j) - (∑ i : Fin 11, (errApow_13 * qEvRowAbs_6 i) * m i ^ 2))) +
       (-(apow0_15 * (∑ i : Fin 11, ∑ j : Fin 11, qEvMat_7 i j * m i * m j) - (∑ i : Fin 11, (errApow_15 * qEvRowAbs_7 i) * m i ^ 2))) +
       (-(apow0_17 * (∑ i : Fin 11, ∑ j : Fin 11, qEvMat_8 i j * m i * m j) - (∑ i : Fin 11, (errApow_17 * qEvRowAbs_8 i) * m i ^ 2))) +
       (-(apow0_19 * (∑ i : Fin 11, ∑ j : Fin 11, qEvMat_9 i j * m i * m j) - (∑ i : Fin 11, (errApow_19 * qEvRowAbs_9 i) * m i ^ 2))) +
       (-(apow0_21 * (∑ i : Fin 11, ∑ j : Fin 11, qEvMat_10 i j * m i * m j) - (∑ i : Fin 11, (errApow_21 * qEvRowAbs_10 i) * m i ^ 2))) +
       (-(apow0_23 * (∑ i : Fin 11, ∑ j : Fin 11, qEvMat_11 i j * m i * m j) - (∑ i : Fin 11, (errApow_23 * qEvRowAbs_11 i) * m i ^ 2)))) +
      ((-(apow0_2 * (∑ i : Fin 11, ∑ j : Fin 11, qOddMat_0 i j * m i * m j) - (∑ i : Fin 11, (errApow_2 * qOddRowAbs_0 i) * m i ^ 2) - ((6261802804445623152330125031301818197576522398243856809 / 62500000000000000000000000000000000000000000000000000000 : ℝ) * ∑ r ∈ Finset.range 1, ((2 * ↑(23 + 2 * r) + 1) / 2) * (∑ i : Fin 11, m i * gHi_0 i r) ^ 2))) +
       (-(apow0_4 * (∑ i : Fin 11, ∑ j : Fin 11, qOddMat_1 i j * m i * m j) - (∑ i : Fin 11, (errApow_4 * qOddRowAbs_1 i) * m i ^ 2) - ((28330699806371863465765559550147688507568454001005121 / 10000000000000000000000000000000000000000000000000000000 : ℝ) * ∑ r ∈ Finset.range 2, ((2 * ↑(23 + 2 * r) + 1) / 2) * (∑ i : Fin 11, m i * gHi_1 i r) ^ 2))) +
       (-(apow0_6 * (∑ i : Fin 11, ∑ j : Fin 11, qOddMat_2 i j * m i * m j) - (∑ i : Fin 11, (errApow_6 * qOddRowAbs_2 i) * m i ^ 2) - ((1817723751476543414437681449293926857541879379346961 / 2000000000000000000000000000000000000000000000000000000 : ℝ) * ∑ r ∈ Finset.range 3, ((2 * ↑(23 + 2 * r) + 1) / 2) * (∑ i : Fin 11, m i * gHi_2 i r) ^ 2))) +
       (-(apow0_8 * (∑ i : Fin 11, ∑ j : Fin 11, qOddMat_3 i j * m i * m j) - (∑ i : Fin 11, (errApow_8 * qOddRowAbs_3 i) * m i ^ 2) - ((758215087248897189698082177505805158304254384420441 / 3125000000000000000000000000000000000000000000000000000 : ℝ) * ∑ r ∈ Finset.range 4, ((2 * ↑(23 + 2 * r) + 1) / 2) * (∑ i : Fin 11, m i * gHi_3 i r) ^ 2)))) +
      ((69314718055994530942416367112031750908870326371636018055994530941723213 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * (∑ k : Fin 11, vPoleClean k * m k) ^ 2 + (762461898615939840366580038232349259997573590087996198615939840358955343 / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * ∑ k : Fin 11, m k ^ 2) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat]
  simp_rw [sum_finK]
  dsimp only [bFastMat, degAt, vPoleClean, gHi_0, gHi_1, gHi_2, gHi_3, qEvMat_0, qEvRowAbs_0, qEvMat_1, qEvRowAbs_1, qEvMat_2, qEvRowAbs_2, qEvMat_3, qEvRowAbs_3, qEvMat_4, qEvRowAbs_4, qEvMat_5, qEvRowAbs_5, qEvMat_6, qEvRowAbs_6, qEvMat_7, qEvRowAbs_7, qEvMat_8, qEvRowAbs_8, qEvMat_9, qEvRowAbs_9, qEvMat_10, qEvRowAbs_10, qEvMat_11, qEvRowAbs_11, qOddMat_0, qOddRowAbs_0, qOddMat_1, qOddRowAbs_1, qOddMat_2, qOddRowAbs_2, qOddMat_3, qOddRowAbs_3, apow0_1, errApow_1, apow0_2, errApow_2, apow0_3, errApow_3, apow0_4, errApow_4, apow0_5, errApow_5, apow0_6, errApow_6, apow0_7, errApow_7, apow0_8, errApow_8, apow0_9, errApow_9, apow0_10, errApow_10, apow0_11, errApow_11, apow0_12, errApow_12, apow0_13, errApow_13, apow0_14, errApow_14, apow0_15, errApow_15, apow0_16, errApow_16, apow0_17, errApow_17, apow0_18, errApow_18, apow0_19, errApow_19, apow0_20, errApow_20, apow0_21, errApow_21, apow0_22, errApow_22, apow0_23, errApow_23, matAt, listAt, coeffAt]
  ring

private theorem hMomSame_lem {G : ℝ → ℝ} (hGc : Continuous G)
    (hGpar : ∀ u, G (-u) = -G u) (k : Fin 11) :
    regionalLegendreMoment G (degAt k) = 2 * halfMoment G k := by
  unfold regionalLegendreMoment
  refine even_integral_Icc_unit (hGc.mul (continuous_legP _)) fun x => ?_
  rw [hGpar x, legP_neg, show degAt k = 2 * k.1 + 1 from rfl, pow_succ, pow_mul, neg_one_sq, one_pow]; ring

private theorem hMomOpp_lem {G : ℝ → ℝ}
    (hGpar : ∀ u, G (-u) = -G u) (r : ℕ) :
    regionalLegendreMoment G (2 * r) = 0 := by
  unfold regionalLegendreMoment
  refine odd_integral_Icc_unit_zero fun x => ?_
  rw [hGpar x, legP_neg, pow_mul, neg_one_sq, one_pow]; ring

private theorem hHopp_lem {G : ℝ → ℝ}
    (hGpar : ∀ u, G (-u) = -G u) (r : ℕ) :
    regionalLegendreMoment G (23 + (2 * r + 1)) = 0 := by
  rw [show 23 + (2 * r + 1) = 2 * (12 + r) by omega]; exact hMomOpp_lem hGpar _

private theorem hLowProj_eq {G : ℝ → ℝ} (hGc : Continuous G)
    (hGpar : ∀ u, G (-u) = -G u) (y : ℝ) :
    lowProj G 23 y = ∑ k : Fin 11, halfMoment G k * basisFn k y := by
  set m := halfMoment G
  unfold lowProj regionalLegendreSum projCoeff
  rw [sum_range_23, sum_finK]
  have hz0 : regionalLegendreMoment G 0 = 0 := hMomOpp_lem hGpar 0
  have hz1 : regionalLegendreMoment G 2 = 0 := hMomOpp_lem hGpar 1
  have hz2 : regionalLegendreMoment G 4 = 0 := hMomOpp_lem hGpar 2
  have hz3 : regionalLegendreMoment G 6 = 0 := hMomOpp_lem hGpar 3
  have hz4 : regionalLegendreMoment G 8 = 0 := hMomOpp_lem hGpar 4
  have hz5 : regionalLegendreMoment G 10 = 0 := hMomOpp_lem hGpar 5
  have hz6 : regionalLegendreMoment G 12 = 0 := hMomOpp_lem hGpar 6
  have hz7 : regionalLegendreMoment G 14 = 0 := hMomOpp_lem hGpar 7
  have hz8 : regionalLegendreMoment G 16 = 0 := hMomOpp_lem hGpar 8
  have hz9 : regionalLegendreMoment G 18 = 0 := hMomOpp_lem hGpar 9
  have hz10 : regionalLegendreMoment G 20 = 0 := hMomOpp_lem hGpar 10
  have hz11 : regionalLegendreMoment G 22 = 0 := hMomOpp_lem hGpar 11
  have hs0 : regionalLegendreMoment G 1 = 2 * m ⟨0, by omega⟩ := hMomSame_lem hGc hGpar ⟨0, by omega⟩
  have hs1 : regionalLegendreMoment G 3 = 2 * m ⟨1, by omega⟩ := hMomSame_lem hGc hGpar ⟨1, by omega⟩
  have hs2 : regionalLegendreMoment G 5 = 2 * m ⟨2, by omega⟩ := hMomSame_lem hGc hGpar ⟨2, by omega⟩
  have hs3 : regionalLegendreMoment G 7 = 2 * m ⟨3, by omega⟩ := hMomSame_lem hGc hGpar ⟨3, by omega⟩
  have hs4 : regionalLegendreMoment G 9 = 2 * m ⟨4, by omega⟩ := hMomSame_lem hGc hGpar ⟨4, by omega⟩
  have hs5 : regionalLegendreMoment G 11 = 2 * m ⟨5, by omega⟩ := hMomSame_lem hGc hGpar ⟨5, by omega⟩
  have hs6 : regionalLegendreMoment G 13 = 2 * m ⟨6, by omega⟩ := hMomSame_lem hGc hGpar ⟨6, by omega⟩
  have hs7 : regionalLegendreMoment G 15 = 2 * m ⟨7, by omega⟩ := hMomSame_lem hGc hGpar ⟨7, by omega⟩
  have hs8 : regionalLegendreMoment G 17 = 2 * m ⟨8, by omega⟩ := hMomSame_lem hGc hGpar ⟨8, by omega⟩
  have hs9 : regionalLegendreMoment G 19 = 2 * m ⟨9, by omega⟩ := hMomSame_lem hGc hGpar ⟨9, by omega⟩
  have hs10 : regionalLegendreMoment G 21 = 2 * m ⟨10, by omega⟩ := hMomSame_lem hGc hGpar ⟨10, by omega⟩
  dsimp only [basisFn, degAt]
  rw [hz0, hs0, hz1, hs1, hz2, hs2, hz3, hs3, hz4, hs4, hz5, hs5,
    hz6, hs6, hz7, hs7, hz8, hs8, hz9, hs9, hz10, hs10, hz11]
  norm_num; ring

private theorem hMres_eq_lem {G : ℝ → ℝ} (hGc : Continuous G)
    (hGpar : ∀ u, G (-u) = -G u) :
    (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 23 x) ^ 2) / 2 =
      (∫ u in (0 : ℝ)..1, G u ^ 2) - ∑ k : Fin 11, (2 * (degAt k : ℝ) + 1) * halfMoment G k ^ 2 := by
  set m := halfMoment G
  set M : ℝ := ∫ u in (0 : ℝ)..1, G u ^ 2
  set M_res : ℝ := (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 23 x) ^ 2) / 2
  have hGsq : ∀ u, G (-u) ^ 2 = G u ^ 2 := fun u => by rw [hGpar u, neg_sq]
  have hM_Icc : (∫ x in Icc (-1 : ℝ) 1, G x ^ 2) = 2 * M := even_integral_Icc_unit (hGc.pow 2) hGsq
  have hIntR2 : (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 23 x) ^ 2) = 2 * M_res := by dsimp [M_res]; ring
  have hp := projection_residual_mass_pub hGc 23
  change (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 23 x) ^ 2) = (∫ x in Icc (-1 : ℝ) 1, G x ^ 2) - _ at hp
  rw [hIntR2, hM_Icc, sum_range_23] at hp
  have hz0 : regionalLegendreMoment G 0 = 0 := hMomOpp_lem hGpar 0
  have hz1 : regionalLegendreMoment G 2 = 0 := hMomOpp_lem hGpar 1
  have hz2 : regionalLegendreMoment G 4 = 0 := hMomOpp_lem hGpar 2
  have hz3 : regionalLegendreMoment G 6 = 0 := hMomOpp_lem hGpar 3
  have hz4 : regionalLegendreMoment G 8 = 0 := hMomOpp_lem hGpar 4
  have hz5 : regionalLegendreMoment G 10 = 0 := hMomOpp_lem hGpar 5
  have hz6 : regionalLegendreMoment G 12 = 0 := hMomOpp_lem hGpar 6
  have hz7 : regionalLegendreMoment G 14 = 0 := hMomOpp_lem hGpar 7
  have hz8 : regionalLegendreMoment G 16 = 0 := hMomOpp_lem hGpar 8
  have hz9 : regionalLegendreMoment G 18 = 0 := hMomOpp_lem hGpar 9
  have hz10 : regionalLegendreMoment G 20 = 0 := hMomOpp_lem hGpar 10
  have hz11 : regionalLegendreMoment G 22 = 0 := hMomOpp_lem hGpar 11
  have hs0 : regionalLegendreMoment G 1 = 2 * m ⟨0, by omega⟩ := hMomSame_lem hGc hGpar ⟨0, by omega⟩
  have hs1 : regionalLegendreMoment G 3 = 2 * m ⟨1, by omega⟩ := hMomSame_lem hGc hGpar ⟨1, by omega⟩
  have hs2 : regionalLegendreMoment G 5 = 2 * m ⟨2, by omega⟩ := hMomSame_lem hGc hGpar ⟨2, by omega⟩
  have hs3 : regionalLegendreMoment G 7 = 2 * m ⟨3, by omega⟩ := hMomSame_lem hGc hGpar ⟨3, by omega⟩
  have hs4 : regionalLegendreMoment G 9 = 2 * m ⟨4, by omega⟩ := hMomSame_lem hGc hGpar ⟨4, by omega⟩
  have hs5 : regionalLegendreMoment G 11 = 2 * m ⟨5, by omega⟩ := hMomSame_lem hGc hGpar ⟨5, by omega⟩
  have hs6 : regionalLegendreMoment G 13 = 2 * m ⟨6, by omega⟩ := hMomSame_lem hGc hGpar ⟨6, by omega⟩
  have hs7 : regionalLegendreMoment G 15 = 2 * m ⟨7, by omega⟩ := hMomSame_lem hGc hGpar ⟨7, by omega⟩
  have hs8 : regionalLegendreMoment G 17 = 2 * m ⟨8, by omega⟩ := hMomSame_lem hGc hGpar ⟨8, by omega⟩
  have hs9 : regionalLegendreMoment G 19 = 2 * m ⟨9, by omega⟩ := hMomSame_lem hGc hGpar ⟨9, by omega⟩
  have hs10 : regionalLegendreMoment G 21 = 2 * m ⟨10, by omega⟩ := hMomSame_lem hGc hGpar ⟨10, by omega⟩
  rw [hz0, hs0, hz1, hs1, hz2, hs2, hz3, hs3, hz4, hs4, hz5, hs5,
    hz6, hs6, hz7, hs7, hz8, hs8, hz9, hs9, hz10, hs10, hz11] at hp
  have hp' : 2 * M_res = 2 * (M - ∑ k : Fin 11, (2 * (degAt k : ℝ) + 1) * m k ^ 2) := by
    rw [hp, sum_finK]; dsimp only [degAt]; ring
  linarith

private theorem hRegLog_lem {G : ℝ → ℝ} (hG1 : ContDiff ℝ 1 G)
    (hGpar : ∀ u, G (-u) = -G u) :
    ((444316699 / 118982864 : ℝ) : ℝ) * ((∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 23 x) ^ 2) / 2) +
      ((3 : ℝ) * halfMoment G ⟨0, by omega⟩ ^ 2 + (77 / 6 : ℝ) * halfMoment G ⟨1, by omega⟩ ^ 2 + (1507 / 60 : ℝ) * halfMoment G ⟨2, by omega⟩ ^ 2 + (1089 / 28 : ℝ) * halfMoment G ⟨3, by omega⟩ ^ 2 + (135451 / 2520 : ℝ) * halfMoment G ⟨4, by omega⟩ ^ 2 + (1925353 / 27720 : ℝ) * halfMoment G ⟨5, by omega⟩ ^ 2 + (3437979 / 40040 : ℝ) * halfMoment G ⟨6, by omega⟩ ^ 2 + (37068467 / 360360 : ℝ) * halfMoment G ⟨7, by omega⟩ ^ 2 + (42142223 / 350064 : ℝ) * halfMoment G ⟨8, by omega⟩ ^ 2 + (275295799 / 1989680 : ℝ) * halfMoment G ⟨9, by omega⟩ ^ 2 + (810896279 / 5173168 : ℝ) * halfMoment G ⟨10, by omega⟩ ^ 2) ≤
      regionalLogEnergy G / 4 := by
  have hGc : Continuous G := hG1.continuous
  set m := halfMoment G
  set M_res : ℝ := (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 23 x) ^ 2) / 2
  have hIntR2 : (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 23 x) ^ 2) = 2 * M_res := by dsimp [M_res]; ring
  have hg := regionalLogEnergy_ge_low_add_gap_residual hG1 23
  change _ + regionalLogEigenvalue 23 * (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 23 x) ^ 2) ≤ _ at hg
  rw [hIntR2, sum_range_23] at hg
  have hz0 : regionalLegendreMoment G 0 = 0 := hMomOpp_lem hGpar 0
  have hz1 : regionalLegendreMoment G 2 = 0 := hMomOpp_lem hGpar 1
  have hz2 : regionalLegendreMoment G 4 = 0 := hMomOpp_lem hGpar 2
  have hz3 : regionalLegendreMoment G 6 = 0 := hMomOpp_lem hGpar 3
  have hz4 : regionalLegendreMoment G 8 = 0 := hMomOpp_lem hGpar 4
  have hz5 : regionalLegendreMoment G 10 = 0 := hMomOpp_lem hGpar 5
  have hz6 : regionalLegendreMoment G 12 = 0 := hMomOpp_lem hGpar 6
  have hz7 : regionalLegendreMoment G 14 = 0 := hMomOpp_lem hGpar 7
  have hz8 : regionalLegendreMoment G 16 = 0 := hMomOpp_lem hGpar 8
  have hz9 : regionalLegendreMoment G 18 = 0 := hMomOpp_lem hGpar 9
  have hz10 : regionalLegendreMoment G 20 = 0 := hMomOpp_lem hGpar 10
  have hz11 : regionalLegendreMoment G 22 = 0 := hMomOpp_lem hGpar 11
  have hs0 : regionalLegendreMoment G 1 = 2 * m ⟨0, by omega⟩ := hMomSame_lem hGc hGpar ⟨0, by omega⟩
  have hs1 : regionalLegendreMoment G 3 = 2 * m ⟨1, by omega⟩ := hMomSame_lem hGc hGpar ⟨1, by omega⟩
  have hs2 : regionalLegendreMoment G 5 = 2 * m ⟨2, by omega⟩ := hMomSame_lem hGc hGpar ⟨2, by omega⟩
  have hs3 : regionalLegendreMoment G 7 = 2 * m ⟨3, by omega⟩ := hMomSame_lem hGc hGpar ⟨3, by omega⟩
  have hs4 : regionalLegendreMoment G 9 = 2 * m ⟨4, by omega⟩ := hMomSame_lem hGc hGpar ⟨4, by omega⟩
  have hs5 : regionalLegendreMoment G 11 = 2 * m ⟨5, by omega⟩ := hMomSame_lem hGc hGpar ⟨5, by omega⟩
  have hs6 : regionalLegendreMoment G 13 = 2 * m ⟨6, by omega⟩ := hMomSame_lem hGc hGpar ⟨6, by omega⟩
  have hs7 : regionalLegendreMoment G 15 = 2 * m ⟨7, by omega⟩ := hMomSame_lem hGc hGpar ⟨7, by omega⟩
  have hs8 : regionalLegendreMoment G 17 = 2 * m ⟨8, by omega⟩ := hMomSame_lem hGc hGpar ⟨8, by omega⟩
  have hs9 : regionalLegendreMoment G 19 = 2 * m ⟨9, by omega⟩ := hMomSame_lem hGc hGpar ⟨9, by omega⟩
  have hs10 : regionalLegendreMoment G 21 = 2 * m ⟨10, by omega⟩ := hMomSame_lem hGc hGpar ⟨10, by omega⟩
  rw [hz0, hs0, hz1, hs1, hz2, hs2, hz3, hs3, hz4, hs4, hz5, hs5,
    hz6, hs6, hz7, hs7, hz8, hs8, hz9, hs9, hz10, hs10, hz11] at hg
  rw [regLogEig_0, regLogEig_1, regLogEig_2, regLogEig_3, regLogEig_4, regLogEig_5, regLogEig_6, regLogEig_7, regLogEig_8, regLogEig_9, regLogEig_10, regLogEig_11, regLogEig_12, regLogEig_13, regLogEig_14, regLogEig_15, regLogEig_16, regLogEig_17, regLogEig_18, regLogEig_19, regLogEig_20, regLogEig_21, regLogEig_22, regLogEig_23] at hg
  suffices h4 : 4 * (((444316699 / 118982864 : ℝ) : ℝ) * M_res +
      ((3 : ℝ) * m ⟨0, by omega⟩ ^ 2 + (77 / 6 : ℝ) * m ⟨1, by omega⟩ ^ 2 + (1507 / 60 : ℝ) * m ⟨2, by omega⟩ ^ 2 + (1089 / 28 : ℝ) * m ⟨3, by omega⟩ ^ 2 + (135451 / 2520 : ℝ) * m ⟨4, by omega⟩ ^ 2 + (1925353 / 27720 : ℝ) * m ⟨5, by omega⟩ ^ 2 + (3437979 / 40040 : ℝ) * m ⟨6, by omega⟩ ^ 2 + (37068467 / 360360 : ℝ) * m ⟨7, by omega⟩ ^ 2 + (42142223 / 350064 : ℝ) * m ⟨8, by omega⟩ ^ 2 + (275295799 / 1989680 : ℝ) * m ⟨9, by omega⟩ ^ 2 + (810896279 / 5173168 : ℝ) * m ⟨10, by omega⟩ ^ 2)) ≤
      regionalLogEnergy G by linarith
  refine le_trans (le_of_eq ?_) hg
  ring

set_option linter.unusedSimpArgs false in
private theorem hPole_bound {F : ℝ → ℝ} (hFc : Continuous F)
    (hs : tsupport F ⊆ Icc (-apertureLogTwo) apertureLogTwo)
    (hpar : ∀ x, F (-x) = -F x) :
    let G := dilateLogTwo F;
    let m := halfMoment G;
    let M := ∫ u in (0 : ℝ)..1, G u ^ 2;
    -((69314718055994530942416367112031750908870326371636018055994530941723213 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * (∑ k : Fin 11, vPoleClean k * m k) ^ 2) -
      ((762461898615939840366580038232349259997573590087996198615939840358955343 / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * ∑ k : Fin 11, m k ^ 2) - (1 / 10 ^ 24) * M ≤
      (coshPairing F ^ 2 / 2 - sinhPairing F ^ 2 / 2) / (2 * apertureLogTwo) := by
  intro G m M
  have hGc : Continuous G := hFc.comp (continuous_const.mul continuous_id)
  have hC0 : coshPairing F = 0 := by
    unfold coshPairing; exact odd_whole_integral_zero fun x => by rw [hpar x, neg_div, Real.cosh_neg]; ring
  rw [hC0, zero_pow two_ne_zero, zero_div, zero_sub]
  have hdA : |apertureLogTwo - poleA0| ≤ 2 / 10 ^ 25 := by
    obtain ⟨h2l, h2u⟩ := log_two_bounds_d26; unfold apertureLogTwo
    have c1 : poleA0 - 2 / 10 ^ 25 ≤ logTwoLo := by norm_num [poleA0, logTwoLo]
    have c2 : logTwoHi ≤ poleA0 + 2 / 10 ^ 25 := by norm_num [poleA0, logTwoHi]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hpole := odd_sinh_pole_ge hFc hs hpar (A0 := poleA0) (by norm_num [poleA0]) (by norm_num [poleA0]) hdA
  change -4 * logTwoHi * (1 + 1 / 10 ^ 20) * (∫ u in (0 : ℝ)..1, G u * oddPolePoly poleA0 u) ^ 2 -
    (1 / 10 ^ 24) * M ≤ _ at hpole
  set S0 := ∫ u in (0 : ℝ)..1, G u * oddPolePoly poleA0 u
  set S_clean := ∑ k : Fin 11, vPoleClean k * m k
  have hS0_eq : S0 = ∑ k : Fin 11, vPoleTrue k * m k := by
    dsimp [S0]; unfold oddPolePoly
    have hfn : ∀ u : ℝ, G u * (∑ j ∈ Finset.range 11, (poleA0 * u / 2) ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) =
        ∑ j ∈ Finset.range 11, ((poleA0 / 2) ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) * (u ^ (2 * j + 1) * G u) := fun u => by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
      rw [show poleA0 * u / 2 = (poleA0 / 2) * u by ring, mul_pow]; ring
    simp_rw [hfn]
    rw [intervalIntegral.integral_finsetSum fun j _ =>
      (show Continuous fun u : ℝ => ((poleA0 / 2) ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) * (u ^ (2 * j + 1) * G u) from
        continuous_const.mul ((continuous_pow _).mul hGc)).intervalIntegrable 0 1]
    simp_rw [intervalIntegral.integral_const_mul]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceMul, Nat.reduceAdd]
    rw [show (poleA0 / 2) ^ 1 / ((1 : ℕ).factorial : ℝ) = (6931471805599453094172321 / 20000000000000000000000000 : ℝ) by norm_num [poleA0, Nat.factorial], show (poleA0 / 2) ^ 3 / ((3 : ℕ).factorial : ℝ) = (111008217329643159906284517227597909397906881849085443859055322445052077387 / 16000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) by norm_num [poleA0, Nat.factorial], show (poleA0 / 2) ^ 5 / ((5 : ℕ).factorial : ℝ) = (5333423258571377369364887969648419308159665597022204663087311899787158176562032021824151342567630836292766570914466172121867 / 128000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) by norm_num [poleA0, Nat.factorial], show (poleA0 / 2) ^ 7 / ((7 : ℕ).factorial : ℝ) = (85415309302735105568142439957480176387438428167106465637617537040899990730020489835691832687938846475948341534099941389657438790015252697504693658597691472394362807898301849 / 716800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) by norm_num [poleA0, Nat.factorial], show (poleA0 / 2) ^ 9 / ((9 : ℕ).factorial : ℝ) = (455978253213938547791552213335007849379933701930630386932388805147845113336960565179572504296009728867128612200129482720082431887148500337772619353937224773191376519209154923555418111851151304770013417820328725906062533201 / 2293760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) by norm_num [poleA0, Nat.factorial], show (poleA0 / 2) ^ 11 / ((11 : ℕ).factorial : ℝ) = (21907612603779359060155093917921242877807781249675242271620312791672495468861803991115190558143121722894330733812612639815700254902158446405464640312683043571706828575725521950776563407561024414815591577326439906363763046769226971919191878750788747280872949599150002788241 / 100925440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) by norm_num [poleA0, Nat.factorial], show (poleA0 / 2) ^ 13 / ((13 : ℕ).factorial : ℝ) = (350852616774605645050184715102621340628221568035367450964280600498664610519270798710034512192792360222610110789206908352083926118602857211838287098568938266745788518244657281024951414064820669761256927774012534941474531192907088549463204309834826272947854921529066541579967139000121430454899013295194829323893152546441627 / 2099249152000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) by norm_num [poleA0, Nat.factorial], show (poleA0 / 2) ^ 15 / ((15 : ℕ).factorial : ℝ) = (5618939905681566554059787649428151406309031336420233464917309500732806172102335803070304891731864110990821271228576138184394019190650393070011354577250962265943495973431249165265463164080825548737524581105153524603864894117681170932623235316738424328231306676525961795017295614756752418509338919697825932024430391544454567637539904817217914468634983694522491593825178569 / 58778976256000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) by norm_num [poleA0, Nat.factorial], show (poleA0 / 2) ^ 17 / ((17 : ℕ).factorial : ℝ) = (269963661270996309597370129800573134171189041284428470878561285496397932872195927395283756175999409217095546128012288010209247775334900029226300217133915012424092212706853094871093785139580908128689803762706309490830841596781315840598045971364913169920650259166865470095982625935030741909363798531679195622534119082379462495464601193289524336554926729725863659196800867429480099362385902064113231040272863139103836184329 / 6395152616652800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) by norm_num [poleA0, Nat.factorial], show (poleA0 / 2) ^ 19 / ((19 : ℕ).factorial : ℝ) = (75850792225755909266265023116673073099314060765400484917297241172723226548513733233066817421548509395082088268316916134051040158810472941328532306713447269615719403472918013851979476891582515567254816864605759823979765439712232970463899249666399524655654250015119874694519573391119900040022162352449456770244718478476410075622248704118747379778566793019175630034667135962171343186810180475009135954775647606352520193430638596535512812765127430816819657681968282122459 / 5116122093322240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) by norm_num [poleA0, Nat.factorial], show (poleA0 / 2) ^ 21 / ((21 : ℕ).factorial : ℝ) = (1214758057764923609778303594631343082964447220184643902670347273808044037707211268844955932195902838043923276935707998894288275034476193830959682775918651070149372971541342978013594763822476817049915583478761718339200967116746287586842689275300015279388583400733377236152357111869125604937911738405377903674748361366208185537902079220822672143575755245289442803274043671090205860558570185224077043545777620368416434622636628898600624505980731857051199359899096218642740553109886594829137086575811990705315063126971273 / 286502837226045440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) by norm_num [poleA0, Nat.factorial]]
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
    rw [hm_0, hm_1, hm_2, hm_3, hm_4, hm_5, hm_6, hm_7, hm_8, hm_9, hm_10, sum_finK]
    dsimp only [vPoleTrue, coeffAt, m]; ring
  have hdiff_v : |S0 - S_clean| ≤ (1 / 10 ^ 30 : ℝ) * ∑ k : Fin 11, |m k| := by
    have heq : S0 - S_clean = ∑ k : Fin 11, (vPoleTrue k - vPoleClean k) * m k := by
      rw [hS0_eq]; dsimp only [S_clean]; rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [heq]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]; refine Finset.sum_le_sum fun k _ => ?_
    rw [abs_mul]; refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rcases k with ⟨kv, hkv⟩; interval_cases kv <;> (dsimp only [vPoleTrue, vPoleClean, coeffAt]; norm_num)
  have hdv_sq : (S0 - S_clean) ^ 2 ≤ (11 : ℝ) * (1 / 10 ^ 30 : ℝ) ^ 2 * ∑ k : Fin 11, m k ^ 2 := by
    have h1 := pow_le_pow_left₀ (abs_nonneg _) hdiff_v 2
    rw [sq_abs, mul_pow] at h1
    have hcs := fin_sum_mul_sq_le 11 (fun _ => (1 : ℝ)) (fun k => |m k|)
    simp only [one_mul, one_pow, sq_abs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hcs
    have hcs' := mul_le_mul_of_nonneg_left hcs (by positivity : (0 : ℝ) ≤ (1 / 10 ^ 30 : ℝ) ^ 2)
    linarith
  have hyoung : S0 ^ 2 ≤ (1 + 1 / 10 ^ 25 : ℝ) * S_clean ^ 2 + (1 + 10 ^ 25 : ℝ) * (S0 - S_clean) ^ 2 := by
    have h0 : 0 ≤ (S_clean - 10 ^ 25 * (S0 - S_clean)) ^ 2 := sq_nonneg _
    have hid : (1 + 1 / 10 ^ 25 : ℝ) * S_clean ^ 2 + (1 + 10 ^ 25 : ℝ) * (S0 - S_clean) ^ 2 - S0 ^ 2 =
        (1 / 10 ^ 25 : ℝ) * (S_clean - 10 ^ 25 * (S0 - S_clean)) ^ 2 := by ring
    linarith
  have hsc1 : 4 * logTwoHi * (1 + 1 / 10 ^ 20) * (1 + 1 / 10 ^ 25) = (69314718055994530942416367112031750908870326371636018055994530941723213 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num [logTwoHi]
  have hsc2 : 4 * logTwoHi * (1 + 1 / 10 ^ 20) * (1 + 10 ^ 25) * ((11 : ℝ) * (1 / 10 ^ 30 : ℝ) ^ 2) = (762461898615939840366580038232349259997573590087996198615939840358955343 / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by norm_num [logTwoHi]
  have hm1 : 4 * logTwoHi * (1 + 1 / 10 ^ 20) * S0 ^ 2 ≤
      (69314718055994530942416367112031750908870326371636018055994530941723213 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * S_clean ^ 2 +
        4 * logTwoHi * (1 + 1 / 10 ^ 20) * (1 + 10 ^ 25) * (S0 - S_clean) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hyoung (by norm_num [logTwoHi] : (0 : ℝ) ≤ 4 * logTwoHi * (1 + 1 / 10 ^ 20))
    have he : 4 * logTwoHi * (1 + 1 / 10 ^ 20) * ((1 + 1 / 10 ^ 25) * S_clean ^ 2 + (1 + 10 ^ 25) * (S0 - S_clean) ^ 2) =
        (69314718055994530942416367112031750908870326371636018055994530941723213 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * S_clean ^ 2 + 4 * logTwoHi * (1 + 1 / 10 ^ 20) * (1 + 10 ^ 25) * (S0 - S_clean) ^ 2 := by
      rw [← hsc1]; ring
    linarith
  have hm2 : 4 * logTwoHi * (1 + 1 / 10 ^ 20) * (1 + 10 ^ 25) * (S0 - S_clean) ^ 2 ≤
      (762461898615939840366580038232349259997573590087996198615939840358955343 / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * ∑ k : Fin 11, m k ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hdv_sq (by norm_num [logTwoHi] : (0 : ℝ) ≤ 4 * logTwoHi * (1 + 1 / 10 ^ 20) * (1 + 10 ^ 25))
    have he : 4 * logTwoHi * (1 + 1 / 10 ^ 20) * (1 + 10 ^ 25) * ((11 : ℝ) * (1 / 10 ^ 30 : ℝ) ^ 2 * ∑ k : Fin 11, m k ^ 2) =
        (762461898615939840366580038232349259997573590087996198615939840358955343 / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * ∑ k : Fin 11, m k ^ 2 := by
      rw [← hsc2]; ring
    linarith
  linarith [hpole, hm1, hm2]

private theorem hP2_bound {F : ℝ → ℝ} (hFc : Continuous F)
    (hs : tsupport F ⊆ Icc (-apertureLogTwo) apertureLogTwo)
    (hpar : ∀ x, F (-x) = -F x) :
    let G := dilateLogTwo F
    let M := ∫ u in (0 : ℝ)..1, G u ^ 2
    2 * e2Mid * (∫ u in (0 : ℝ)..(1 / 2), G u * G (1 - u)) - (1 / 10000000000000000000000000 : ℝ) * M ≤
      (-2 * (Real.log 2 / Real.sqrt 2) * autocorr F (Real.log 2)) / (2 * apertureLogTwo) := by
  intro G M
  have hGc : Continuous G := hFc.comp (continuous_const.mul continuous_id)
  have hsG : tsupport G ⊆ Icc (-1 : ℝ) 1 := tsupport_dilateLogTwo hs
  have hGpar : ∀ u, G (-u) = -G u := fun u => by unfold G dilateLogTwo; rw [mul_neg, hpar]
  have hGsgn : ∀ u, G (-u) = (-1 : ℝ) * G u := fun u => by rw [hGpar u]; ring
  have hdil1 := dilated_autocorr_log_two F 1
  unfold apertureLogTwo at hdil1; rw [mul_one] at hdil1
  have hac1 := autocorr_one_of_parity hGc hsG hGsgn
  have hrew : (-2 * (Real.log 2 / Real.sqrt 2) * autocorr F (Real.log 2)) / (2 * apertureLogTwo) =
      2 * (Real.log 2 / Real.sqrt 2) * (∫ u in (0 : ℝ)..(1 / 2), G u * G (1 - u)) := by
    unfold apertureLogTwo; rw [show autocorr F (Real.log 2) = Real.log 2 * autocorr G 1 by
      have := apertureLogTwo_pos; unfold apertureLogTwo at this; field_simp [this.ne'] at hdil1 ⊢; linarith]
    rw [hac1]; field_simp [(Real.log_pos one_lt_two).ne']; try ring
  rw [hrew]
  obtain ⟨hw2l, hw2u⟩ := primeTwoWeight_bounds
  have hde2 : |(Real.log 2 / Real.sqrt 2) - e2Mid| ≤ (1 / 10000000000000000000000000 : ℝ) := by
    have c1 : e2Mid - (1 / 10000000000000000000000000 : ℝ) ≤ primeTwoWeightLo := by norm_num [e2Mid, primeTwoWeightLo, primeTwoWeightHi]
    have c2 : primeTwoWeightHi ≤ e2Mid + (1 / 10000000000000000000000000 : ℝ) := by norm_num [e2Mid, primeTwoWeightLo, primeTwoWeightHi]
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
  have habs_m : |2 * ((Real.log 2 / Real.sqrt 2) - e2Mid) * (∫ u in (0 : ℝ)..(1 / 2), G u * G (1 - u))| ≤ (1 / 10000000000000000000000000 : ℝ) * M := by
    have he : 2 * ((Real.log 2 / Real.sqrt 2) - e2Mid) * (∫ u in (0 : ℝ)..(1 / 2), G u * G (1 - u)) =
        ((Real.log 2 / Real.sqrt 2) - e2Mid) * (2 * ∫ u in (0 : ℝ)..(1 / 2), G u * G (1 - u)) := by ring
    rw [he, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
  linarith [(abs_le.mp habs_m).1]

private theorem hP3_bound {F : ℝ → ℝ} (hFc : Continuous F)
    (hs : tsupport F ⊆ Icc (-apertureLogTwo) apertureLogTwo)
    (hpar : ∀ x, F (-x) = -F x) :
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
  have hGpar : ∀ u, G (-u) = -G u := fun u => by unfold G dilateLogTwo; rw [mul_neg, hpar]
  have hGsgn : ∀ u, G (-u) = (-1 : ℝ) * G u := fun u => by rw [hGpar u]; ring
  have hM_Ioo : (∫ u in Ioo (0 : ℝ) 1, G u ^ 2) = M := by
    dsimp [M]; rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
  have ha_eq : Real.log 3 = apertureLogTwo * (1 + a) := by
    dsimp [a]; unfold primeThreeOffset apertureLogTwo; field_simp [(Real.log_pos one_lt_two).ne']; ring
  have hdil3 := dilated_autocorr_log_two F (1 + a)
  rw [← ha_eq] at hdil3
  have hac3 := autocorr_primeThree_of_parity hGc hsG hGsgn
  have hrew : (-2 * (Real.log 3 / Real.sqrt 3) * autocorr F (Real.log 3)) / (2 * apertureLogTwo) =
      2 * (Real.log 3 / Real.sqrt 3) * (∫ s in (0 : ℝ)..L4, G (1 - s) * G (a + s)) := by
    have hacF : autocorr F (Real.log 3) = apertureLogTwo * autocorr G (1 + a) := by
      field_simp [hA_pos.ne'] at hdil3 ⊢; linarith
    rw [hacF, hac3]; dsimp [a, L4]; field_simp [hA_pos.ne']; try ring
  rw [hrew]
  obtain ⟨hw3l, hw3u⟩ := primeThreeWeight_bounds
  have hde3 : |(Real.log 3 / Real.sqrt 3) - e3Mid| ≤ (1 / 10000000000000000000000000 : ℝ) := by
    have c1 : e3Mid - (1 / 10000000000000000000000000 : ℝ) ≤ primeThreeWeightLo := by norm_num [e3Mid, primeThreeWeightLo, primeThreeWeightHi]
    have c2 : primeThreeWeightHi ≤ e3Mid + (1 / 10000000000000000000000000 : ℝ) := by norm_num [e3Mid, primeThreeWeightLo, primeThreeWeightHi]
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
  have habs_m : |2 * ((Real.log 3 / Real.sqrt 3) - e3Mid) * (∫ s in (0 : ℝ)..L4, G (1 - s) * G (a + s))| ≤ (1 / 10000000000000000000000000 : ℝ) * M := by
    have he : 2 * ((Real.log 3 / Real.sqrt 3) - e3Mid) * (∫ s in (0 : ℝ)..L4, G (1 - s) * G (a + s)) =
        ((Real.log 3 / Real.sqrt 3) - e3Mid) * (2 * ∫ s in (0 : ℝ)..L4, G (1 - s) * G (a + s)) := by ring
    rw [he, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
  linarith [(abs_le.mp habs_m).1]

private theorem hRetSplit_lem (F : ℝ → ℝ) (M : ℝ)
    (hF_mass : (∫ x, F x ^ 2) = 2 * apertureLogTwo * M) :
    ((∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), (autocorr F 0 - autocorr F t) / t) +
      twoPrimeGammaMassExact * (∫ x, F x ^ 2) - (∫ x, F x) ^ 2 / 4 +
      (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t * autocorr F t) / 24 -
      7 * (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 3 * autocorr F t) / 5760 +
      31 * (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 5 * autocorr F t) / 967680 -
      127 * (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 7 * autocorr F t) / 154828800 +
      (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 2 * autocorr F t) / 16 -
      (∑ q ∈ Finset.range 12, gammaAlphaEven q * (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ (2 * q) * autocorr F t)) -
      2 * (Real.log 2 / Real.sqrt 2) * autocorr F (Real.log 2) -
      2 * (Real.log 3 / Real.sqrt 3) * autocorr F (Real.log 3) +
      coshPairing F ^ 2 / 2 - sinhPairing F ^ 2 / 2) / (2 * apertureLogTwo) -
      ((1 / 10 ^ 10 : ℝ) * (∫ x, F x ^ 2)) / (2 * apertureLogTwo) =
      (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), (autocorr F 0 - autocorr F t) / t) / (2 * apertureLogTwo) +
      (twoPrimeGammaMassExact * ∫ x, F x ^ 2) / (2 * apertureLogTwo) - (1 / 10 ^ 10 : ℝ) * M +
      (-((∫ x, F x) ^ 2 / 4) / (2 * apertureLogTwo)) +
      (((105091 / 5000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 0 * autocorr F t) / (2 * apertureLogTwo) + ((24999999999449249 / 400000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 2 * autocorr F t) / (2 * apertureLogTwo) + ((-65104166242035063 / 10000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 4 * autocorr F t) / (2 * apertureLogTwo) + ((3309458785969429 / 5000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 6 * autocorr F t) / (2 * apertureLogTwo) + ((-5366589076364431 / 80000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 8 * autocorr F t) / (2 * apertureLogTwo) + ((8726421052567571 / 1280000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 10 * autocorr F t) / (2 * apertureLogTwo) + ((-7163072980652803 / 10240000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 12 * autocorr F t) / (2 * apertureLogTwo) + ((6237272726078909 / 81920000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 14 * autocorr F t) / (2 * apertureLogTwo) + ((-3260029542583927 / 327680000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 16 * autocorr F t) / (2 * apertureLogTwo) + ((519878183231709 / 327680000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 18 * autocorr F t) / (2 * apertureLogTwo) + ((-4669432996809649 / 20971520000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 20 * autocorr F t) / (2 * apertureLogTwo) + ((1377431922843341 / 83886080000000000000000000 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 22 * autocorr F t) / (2 * apertureLogTwo)) +
      (((1 / 24 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 1 * autocorr F t) / (2 * apertureLogTwo) + ((-7 / 5760 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 3 * autocorr F t) / (2 * apertureLogTwo) + ((31 / 967680 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 5 * autocorr F t) / (2 * apertureLogTwo) + ((-127 / 154828800 : ℝ) * ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 7 * autocorr F t) / (2 * apertureLogTwo)) +
      (-2 * (Real.log 2 / Real.sqrt 2) * autocorr F (Real.log 2)) / (2 * apertureLogTwo) +
      (-2 * (Real.log 3 / Real.sqrt 3) * autocorr F (Real.log 3)) / (2 * apertureLogTwo) +
      (coshPairing F ^ 2 / 2 - sinhPairing F ^ 2 / 2) / (2 * apertureLogTwo) := by
  have hA_pos : 0 < apertureLogTwo := apertureLogTwo_pos
  have hEvenSum : (∑ q ∈ Finset.range 12, gammaAlphaEven q * (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ (2 * q) * autocorr F t)) =
      gammaAlphaEven 0 * (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 0 * autocorr F t) + gammaAlphaEven 1 * (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 2 * autocorr F t) + gammaAlphaEven 2 * (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 4 * autocorr F t) + gammaAlphaEven 3 * (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 6 * autocorr F t) + gammaAlphaEven 4 * (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 8 * autocorr F t) + gammaAlphaEven 5 * (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 10 * autocorr F t) + gammaAlphaEven 6 * (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 12 * autocorr F t) + gammaAlphaEven 7 * (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 14 * autocorr F t) + gammaAlphaEven 8 * (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 16 * autocorr F t) + gammaAlphaEven 9 * (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 18 * autocorr F t) + gammaAlphaEven 10 * (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 20 * autocorr F t) + gammaAlphaEven 11 * (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 22 * autocorr F t) := by
    rw [sum_range_12]
  have hMassDiv : ((1 / 10 ^ 10 : ℝ) * (∫ x, F x ^ 2)) / (2 * apertureLogTwo) = (1 / 10 ^ 10 : ℝ) * M := by
    rw [hF_mass]; field_simp [hA_pos.ne']
  have ht1 : (∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t * autocorr F t) =
      ∫ t in Ioc (0 : ℝ) (2 * apertureLogTwo), t ^ 1 * autocorr F t := by simp only [pow_one]
  rw [ht1, hEvenSum, hMassDiv, gammaAlphaEven_eq_0, gammaAlphaEven_eq_1, gammaAlphaEven_eq_2, gammaAlphaEven_eq_3, gammaAlphaEven_eq_4, gammaAlphaEven_eq_5, gammaAlphaEven_eq_6, gammaAlphaEven_eq_7, gammaAlphaEven_eq_8, gammaAlphaEven_eq_9, gammaAlphaEven_eq_10, gammaAlphaEven_eq_11]; ring

private theorem hRegId_lem (M M_res : ℝ) (m : Fin 11 → ℝ)
    (hMres_eq : M_res = M - ∑ k : Fin 11, (2 * (degAt k : ℝ) + 1) * m k ^ 2) :
    ((444316699 / 118982864 : ℝ) : ℝ) * M_res - deltaResRat * M_res +
      ((3 : ℝ) * m ⟨0, by omega⟩ ^ 2 + (77 / 6 : ℝ) * m ⟨1, by omega⟩ ^ 2 + (1507 / 60 : ℝ) * m ⟨2, by omega⟩ ^ 2 + (1089 / 28 : ℝ) * m ⟨3, by omega⟩ ^ 2 + (135451 / 2520 : ℝ) * m ⟨4, by omega⟩ ^ 2 + (1925353 / 27720 : ℝ) * m ⟨5, by omega⟩ ^ 2 + (3437979 / 40040 : ℝ) * m ⟨6, by omega⟩ ^ 2 + (37068467 / 360360 : ℝ) * m ⟨7, by omega⟩ ^ 2 + (42142223 / 350064 : ℝ) * m ⟨8, by omega⟩ ^ 2 + (275295799 / 1989680 : ℝ) * m ⟨9, by omega⟩ ^ 2 + (810896279 / 5173168 : ℝ) * m ⟨10, by omega⟩ ^ 2) =
      (27685582518462127862237499 / 7436429000000000000000000 : ℝ) * M - ((27685582518462127862237499 / 7436429000000000000000000 : ℝ) * (∑ k : Fin 11, (2 * (degAt k : ℝ) + 1) * m k ^ 2) -
        ((3 : ℝ) * m ⟨0, by omega⟩ ^ 2 + (77 / 6 : ℝ) * m ⟨1, by omega⟩ ^ 2 + (1507 / 60 : ℝ) * m ⟨2, by omega⟩ ^ 2 + (1089 / 28 : ℝ) * m ⟨3, by omega⟩ ^ 2 + (135451 / 2520 : ℝ) * m ⟨4, by omega⟩ ^ 2 + (1925353 / 27720 : ℝ) * m ⟨5, by omega⟩ ^ 2 + (3437979 / 40040 : ℝ) * m ⟨6, by omega⟩ ^ 2 + (37068467 / 360360 : ℝ) * m ⟨7, by omega⟩ ^ 2 + (42142223 / 350064 : ℝ) * m ⟨8, by omega⟩ ^ 2 + (275295799 / 1989680 : ℝ) * m ⟨9, by omega⟩ ^ 2 + (810896279 / 5173168 : ℝ) * m ⟨10, by omega⟩ ^ 2)) := by
  rw [hMres_eq]; dsimp only [deltaResRat]; ring

private theorem arch_and_moments_ge {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hs : tsupport F ⊆ Icc (-apertureLogTwo) apertureLogTwo)
    (hpar : ∀ x, F (-x) = -F x) :
    let G := dilateLogTwo F
    let m := halfMoment G
    let a := primeThreeOffset
    let L4 := (1 - a) / 2
    (∫ u in Ioo (0 : ℝ) 1, G u ^ 2 * (c0Rat + (Real.log 2 - Real.log (1 - u ^ 2) / 2))) +
      2 * e2Mid * (∫ u in (0 : ℝ)..(1 / 2), G u * G (1 - u)) +
      2 * e3Mid * (∫ s in (0 : ℝ)..L4, G (1 - s) * G (a + s)) -
      (∑ i : Fin 11, ∑ j : Fin 11, bCleanMat i j * m i * m j) ≤
      (weilQuad F - (1 / 10 ^ 10 : ℝ) * (∫ x, F x ^ 2)) / (2 * apertureLogTwo) := by
  intro G m a L4
  have hA_pos : 0 < apertureLogTwo := apertureLogTwo_pos
  have h2A_pos : 0 < 2 * apertureLogTwo := by positivity
  have hG2 : ContDiff ℝ 2 G := contDiff_dilateLogTwo hF
  have hG1 : ContDiff ℝ 1 G := hG2.of_le (by norm_num)
  have hGc : Continuous G := hG2.continuous
  have hsG : tsupport G ⊆ Icc (-1 : ℝ) 1 := tsupport_dilateLogTwo hs
  have hGpar : ∀ u, G (-u) = -G u := fun u => by unfold G dilateLogTwo; rw [mul_neg, hpar]
  have hGsq : ∀ u, G (-u) ^ 2 = G u ^ 2 := fun u => by rw [hGpar u, neg_sq]
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
  have hLowProj : ∀ y : ℝ, lowProj G 23 y = ∑ k : Fin 11, m k * basisFn k y := hLowProj_eq hGc hGpar
  have hHopp : ∀ r : ℕ, regionalLegendreMoment G (23 + (2 * r + 1)) = 0 := hHopp_lem hGpar
  set M_res : ℝ := (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 23 x) ^ 2) / 2
  have hMres_nn : 0 ≤ M_res := div_nonneg (setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _) (by norm_num)
  have hMres_eq : M_res = M - ∑ k : Fin 11, (2 * (degAt k : ℝ) + 1) * m k ^ 2 := hMres_eq_lem hGc hGpar
  have hRegLog : ((444316699 / 118982864 : ℝ) : ℝ) * M_res +
      ((3 : ℝ) * m ⟨0, by omega⟩ ^ 2 + (77 / 6 : ℝ) * m ⟨1, by omega⟩ ^ 2 + (1507 / 60 : ℝ) * m ⟨2, by omega⟩ ^ 2 + (1089 / 28 : ℝ) * m ⟨3, by omega⟩ ^ 2 + (135451 / 2520 : ℝ) * m ⟨4, by omega⟩ ^ 2 + (1925353 / 27720 : ℝ) * m ⟨5, by omega⟩ ^ 2 + (3437979 / 40040 : ℝ) * m ⟨6, by omega⟩ ^ 2 + (37068467 / 360360 : ℝ) * m ⟨7, by omega⟩ ^ 2 + (42142223 / 350064 : ℝ) * m ⟨8, by omega⟩ ^ 2 + (275295799 / 1989680 : ℝ) * m ⟨9, by omega⟩ ^ 2 + (810896279 / 5173168 : ℝ) * m ⟨10, by omega⟩ ^ 2) ≤
      regionalLogEnergy G / 4 := hRegLog_lem hG1 hGpar
  have hMean : -((∫ x, F x) ^ 2 / 4) / (2 * apertureLogTwo) = 0 := by
    rw [odd_whole_integral_zero hpar]; norm_num
  have hG_def : dilateLogTwo F = G := rfl
  have hm_def : halfMoment G = m := rfl
  have hMres_def : (∫ x in Icc (-1 : ℝ) 1, (G x - lowProj G 23 x) ^ 2) / 2 = M_res := rfl
  have hEv_0 := hEv_bound_0 hGc hsG hGpar
  dsimp only at hEv_0; rw [hG_def, hm_def] at hEv_0
  have hEv_1 := hEv_bound_1 hGc hsG hGpar
  dsimp only at hEv_1; rw [hG_def, hm_def] at hEv_1
  have hEv_2 := hEv_bound_2 hGc hsG hGpar
  dsimp only at hEv_2; rw [hG_def, hm_def] at hEv_2
  have hEv_3 := hEv_bound_3 hGc hsG hGpar
  dsimp only at hEv_3; rw [hG_def, hm_def] at hEv_3
  have hEv_4 := hEv_bound_4 hGc hsG hGpar
  dsimp only at hEv_4; rw [hG_def, hm_def] at hEv_4
  have hEv_5 := hEv_bound_5 hGc hsG hGpar
  dsimp only at hEv_5; rw [hG_def, hm_def] at hEv_5
  have hEv_6 := hEv_bound_6 hGc hsG hGpar
  dsimp only at hEv_6; rw [hG_def, hm_def] at hEv_6
  have hEv_7 := hEv_bound_7 hGc hsG hGpar
  dsimp only at hEv_7; rw [hG_def, hm_def] at hEv_7
  have hEv_8 := hEv_bound_8 hGc hsG hGpar
  dsimp only at hEv_8; rw [hG_def, hm_def] at hEv_8
  have hEv_9 := hEv_bound_9 hGc hsG hGpar
  dsimp only at hEv_9; rw [hG_def, hm_def] at hEv_9
  have hEv_10 := hEv_bound_10 hGc hsG hGpar
  dsimp only at hEv_10; rw [hG_def, hm_def] at hEv_10
  have hEv_11 := hEv_bound_11 hGc hsG hGpar
  dsimp only at hEv_11; rw [hG_def, hm_def] at hEv_11
  have hOdd_0 := hOdd_bound_0 hGc hsG hLowProj hHopp
  dsimp only at hOdd_0; rw [hG_def, hm_def, hMres_def] at hOdd_0
  have hOdd_1 := hOdd_bound_1 hGc hsG hLowProj hHopp
  dsimp only at hOdd_1; rw [hG_def, hm_def, hMres_def] at hOdd_1
  have hOdd_2 := hOdd_bound_2 hGc hsG hLowProj hHopp
  dsimp only at hOdd_2; rw [hG_def, hm_def, hMres_def] at hOdd_2
  have hOdd_3 := hOdd_bound_3 hGc hsG hLowProj hHopp
  dsimp only at hOdd_3; rw [hG_def, hm_def, hMres_def] at hOdd_3
  have hPole : -((69314718055994530942416367112031750908870326371636018055994530941723213 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * (∑ k : Fin 11, vPoleClean k * m k) ^ 2) -
      ((762461898615939840366580038232349259997573590087996198615939840358955343 / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) * ∑ k : Fin 11, m k ^ 2) - (1 / 10 ^ 24) * M ≤
      (coshPairing F ^ 2 / 2 - sinhPairing F ^ 2 / 2) / (2 * apertureLogTwo) :=
    hPole_bound hF.continuous hs hpar
  have hP2_pert : 2 * e2Mid * (∫ u in (0 : ℝ)..(1 / 2), G u * G (1 - u)) - (1 / 10000000000000000000000000 : ℝ) * M ≤
      (-2 * (Real.log 2 / Real.sqrt 2) * autocorr F (Real.log 2)) / (2 * apertureLogTwo) :=
    hP2_bound hF.continuous hs hpar
  have hP3_pert : 2 * e3Mid * (∫ s in (0 : ℝ)..L4, G (1 - s) * G (a + s)) - (1 / 10000000000000000000000000 : ℝ) * M ≤
      (-2 * (Real.log 3 / Real.sqrt 3) * autocorr F (Real.log 3)) / (2 * apertureLogTwo) :=
    hP3_bound hF.continuous hs hpar
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
  have hMassMargin : c0Rat + (1 / 10 ^ 10 : ℝ) + (1 / 10 ^ 24 : ℝ) + (1 / 10000000000000000000000000 : ℝ) + (1 / 10000000000000000000000000 : ℝ) ≤
      cGammaLo + (27685582518462127862237499 / 7436429000000000000000000 : ℝ) := by norm_num [c0Rat, cGammaLo]
  have hMassMarginM := mul_le_mul_of_nonneg_right hMassMargin hM_nn
  have hRetSplit := hRetSplit_lem F M hF_mass
  have hSubFloor : (weilQuad F - (1 / 10 ^ 10 : ℝ) * ∫ x, F x ^ 2) / (2 * apertureLogTwo) =
      weilQuad F / (2 * apertureLogTwo) - ((1 / 10 ^ 10 : ℝ) * ∫ x, F x ^ 2) / (2 * apertureLogTwo) := sub_div _ _ _
  rw [hSubFloor, hPotSplit]
  have hRegId := hRegId_lem M M_res m hMres_eq
  linarith [hRetDiv, hRetSplit, hLagDil, hGamM, hRegLog, hRegId, hResMargin, hMassMarginM,
    hMean, hEv_0, hEv_1, hEv_2, hEv_3, hEv_4, hEv_5, hEv_6, hEv_7, hEv_8, hEv_9, hEv_10, hEv_11, hOdd_0, hOdd_1, hOdd_2, hOdd_3,
    hPole, hP2_pert, hP3_pert, hBfast_id, hBfast_le]

/-! ### 3. Fiberwise certificate assembly and `LDLᵀ` synthesis -/

open ApertureLogTwo

private def oddFiberCert : FiberCert where
  p4 := [oddP4_0, oddP4_1, oddP4_2, oddP4_3, oddP4_4, oddP4_5, oddP4_6, oddP4_7, oddP4_8, oddP4_9]
  p2 := [oddP2_0, oddP2_1]
  s4 := ⟨oddSliver4Lo, oddSliver4Tay⟩
  s2 := ⟨oddSliver2Hi, oddSliver2Tay⟩

private theorem oddSector_valid : oddSector.valid = true := by decide +kernel
private theorem oddP4_0_ok : oddP4_0.check oddSector = true := by decide +kernel
private theorem oddP4_1_ok : oddP4_1.check oddSector = true := by decide +kernel
private theorem oddP4_2_ok : oddP4_2.check oddSector = true := by decide +kernel
private theorem oddP4_3_ok : oddP4_3.check oddSector = true := by decide +kernel
private theorem oddP4_4_ok : oddP4_4.check oddSector = true := by decide +kernel
private theorem oddP4_5_ok : oddP4_5.check oddSector = true := by decide +kernel
private theorem oddP4_6_ok : oddP4_6.check oddSector = true := by decide +kernel
private theorem oddP4_7_ok : oddP4_7.check oddSector = true := by decide +kernel
private theorem oddP4_8_ok : oddP4_8.check oddSector = true := by decide +kernel
private theorem oddP4_9_ok : oddP4_9.check oddSector = true := by decide +kernel
private theorem oddP2_0_ok : oddP2_0.check oddSector = true := by decide +kernel
private theorem oddP2_1_ok : oddP2_1.check oddSector = true := by decide +kernel
private theorem oddFiberCert_ok : oddFiberCert.check oddSector = true := by decide +kernel
private theorem oddCertMat_ldl :
    ldlCheck oddSector.K (certMat oddSector oddBClean oddFiberCert) oddCertL oddCertD = true := by
  decide +kernel

/-- Unconditional `1 / 10 ^ 10` `L²` floor on the Weil quadratic form for odd
`C²` tests supported in `[-log 2, log 2]`. -/
theorem weilQuad_ge_odd_at_aperture_log_two {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hs : tsupport F ⊆ Icc (-apertureLogTwo) apertureLogTwo)
    (hpar : ∀ x, F (-x) = -F x) :
    (1 / 10 ^ 10 : ℝ) * (∫ x, F x ^ 2) ≤ weilQuad F := by
  have h2A_pos : 0 < 2 * apertureLogTwo := by linarith [apertureLogTwo_pos]
  have hArch := arch_and_moments_ge hF hs hpar
  dsimp only at hArch
  set G := dilateLogTwo F
  have hG2 : ContDiff ℝ 2 G := contDiff_dilateLogTwo hF
  have hGc : Continuous G := hG2.continuous
  have hsG : tsupport G ⊆ Icc (-1 : ℝ) 1 := tsupport_dilateLogTwo hs
  have hGsq : ∀ u, G (-u) ^ 2 = G u ^ 2 := fun u => by
    unfold G dilateLogTwo; rw [mul_neg, hpar, neg_sq]
  obtain ⟨hIntLog, _⟩ := logarithmic_lag_half_of_sq_even hG2 hsG hGsq
  have hiG2 : IntegrableOn (fun u => G u ^ 2) (Ioo (0 : ℝ) 1) :=
    (hGc.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hiPot : IntegrableOn (fun u => G u ^ 2 * ((oddSector.c0 : ℝ) + vTrue u)) (Ioo (0 : ℝ) 1) := by
    refine ((hiG2.const_mul (oddSector.c0 : ℝ)).add hIntLog).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u _
    simp only [Pi.add_apply, vTrue]; ring
  have h4 : ∀ D ∈ oddFiberCert.p4, D.check oddSector = true := by
    intro D hD
    simp only [oddFiberCert, List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact oddP4_0_ok
    · exact oddP4_1_ok
    · exact oddP4_2_ok
    · exact oddP4_3_ok
    · exact oddP4_4_ok
    · exact oddP4_5_ok
    · exact oddP4_6_ok
    · exact oddP4_7_ok
    · exact oddP4_8_ok
    · exact oddP4_9_ok
  have h2 : ∀ D ∈ oddFiberCert.p2, D.check oddSector = true := by
    intro D hD
    simp only [oddFiberCert, List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl
    · exact oddP2_0_ok
    · exact oddP2_1_ok
  have hFib := oddFiberCert.bound oddSector oddSector_valid oddFiberCert_ok h4 h2 hGc hiPot
  have hCert := quadR_certMat oddSector oddBClean oddFiberCert (oddSector.moments G)
  have hPsd := quad_nonneg_of_ldlCheck oddCertMat_ldl (oddSector.moments G)
  have hMom_eq : oddSector.moments G = halfMoment G := rfl
  have hc0_eq : (oddSector.c0 : ℝ) = c0Rat := by norm_num [oddSector, c0Rat]
  have he2_eq : (oddSector.e2 : ℝ) = e2Mid := by norm_num [oddSector, e2Mid]
  have he3_eq : (oddSector.e3 : ℝ) = e3Mid := by norm_num [oddSector, e3Mid]
  have hBClean_eq : quadR oddSector.K oddBClean (halfMoment G) =
      ∑ i : Fin 11, ∑ j : Fin 11, bCleanMat i j * halfMoment G i * halfMoment G j := rfl
  rw [hMom_eq, hc0_eq, he2_eq, he3_eq] at hFib
  rw [hMom_eq, hBClean_eq] at hCert
  rw [hMom_eq] at hPsd
  have hPot_eq : (∫ u in Ioo (0 : ℝ) 1, G u ^ 2 * (c0Rat + vTrue u)) =
      ∫ u in Ioo (0 : ℝ) 1, G u ^ 2 * (c0Rat + (Real.log 2 - Real.log (1 - u ^ 2) / 2)) := rfl
  rw [hPot_eq] at hFib
  have hDiv_nn : 0 ≤ (weilQuad F - (1 / 10 ^ 10 : ℝ) * ∫ x, F x ^ 2) / (2 * apertureLogTwo) := by
    linarith [hArch, hFib, hCert, hPsd]
  have hSub_nn : 0 ≤ weilQuad F - (1 / 10 ^ 10 : ℝ) * ∫ x, F x ^ 2 :=
    ((div_nonneg_iff.mp hDiv_nn).resolve_right fun h => by linarith [h.2, h2A_pos]).1
  linarith

end GaloisForLFunctions.WindowTowerOfSpecZ
