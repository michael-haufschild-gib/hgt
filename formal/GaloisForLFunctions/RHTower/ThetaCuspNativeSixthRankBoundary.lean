import GaloisForLFunctions.RHTower.ThetaCuspModularSeamSourceJets
import GaloisForLFunctions.HTGeometry.RankThreeHankelSchurBoundary
import GaloisForLFunctions.RHTower.HedenmalmCenterMixedEighthHankelClosure
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthHankelSeam
import GaloisForLFunctions.HilbertMetric.FivePointFiniteDifferenceCusp

/-!
# Native rank-six theta boundary and its positive survivor

The literal reflected complete theta source has a negative signed odd rank-three
Hankel block at the self-dual seam, although its leading five-dimensional block
is strictly positive. The exact Schur split isolates the sole remaining scalar
channel. The negative chamber is open; integration over the center remains essential.
-/

open scoped BigOperators ContDiff
open Filter Topology Matrix
open GaloisForLFunctions.HTGeometry
namespace RHTower
noncomputable section
set_option maxHeartbeats 1000000

/-- Literal center derivative of the complete-source reflection product. -/
def thetaCuspNativeReflectionJet (n : ℕ) (x : ℝ) : ℝ :=
  iteratedDeriv n (fun t => thetaCuspFullSource (x+t)*thetaCuspFullSource (x-t)) 0

/-- All reflected source jets are exact finite Leibniz sums. -/
theorem thetaCuspNativeReflectionJet_eq (n : ℕ) (x : ℝ) :
    thetaCuspNativeReflectionJet n x =
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*iteratedDeriv i thetaCuspFullSource x *
        ((-1 : ℝ)^(n-i)*iteratedDeriv (n-i) thetaCuspFullSource x) := by
  have hf : ContDiff ℝ n thetaCuspFullSource := contDiff_thetaCuspFullSource.of_le
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  unfold thetaCuspNativeReflectionJet
  change iteratedDeriv n
    ((fun t => thetaCuspFullSource (x+t))*(fun t => thetaCuspFullSource (x-t))) 0 = _
  have hl : ContDiffAt ℝ n (fun t : ℝ => thetaCuspFullSource (x+t)) 0 :=
    (hf.comp (contDiff_const.add contDiff_id)).contDiffAt
  have hr : ContDiffAt ℝ n (fun t : ℝ => thetaCuspFullSource (x-t)) 0 :=
    (hf.comp (contDiff_const.sub contDiff_id)).contDiffAt
  rw [iteratedDeriv_mul hl hr]
  simp only [iteratedDeriv_comp_const_add, iteratedDeriv_comp_const_sub,
    add_zero, sub_zero, smul_eq_mul]

/-- Reflected derivatives depend continuously on the center, at every order. -/
theorem continuous_thetaCuspNativeReflectionJet (n : ℕ) :
    Continuous (thetaCuspNativeReflectionJet n) := by
  have hj (k : ℕ) : Continuous (iteratedDeriv k thetaCuspFullSource) := by
    rw [iteratedDeriv_thetaCuspFullSource]
    exact continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_thetaCuspFullDerivative k x).continuousAt
  change Continuous (fun x => thetaCuspNativeReflectionJet n x)
  simp_rw [thetaCuspNativeReflectionJet_eq]
  fun_prop

/-- Compatibility with the existing order-0 reflected-source jet. -/
theorem thetaCuspNativeReflectionJet_zero (x : ℝ) :
    thetaCuspNativeReflectionJet 0 x = thetaCuspSourceReflectionJetZero x := by
  rw [thetaCuspNativeReflectionJet_eq]
  norm_num [Finset.sum_range_succ, Nat.choose, thetaCuspSourceReflectionJetZero]
  ring

/-- Compatibility with the existing order-2 reflected-source jet. -/
theorem thetaCuspNativeReflectionJet_two (x : ℝ) :
    thetaCuspNativeReflectionJet 2 x = thetaCuspSourceReflectionJetTwo x := by
  rw [thetaCuspNativeReflectionJet_eq]
  norm_num [Finset.sum_range_succ, Nat.choose, thetaCuspSourceReflectionJetTwo]
  ring

/-- Compatibility with the existing order-4 reflected-source jet. -/
theorem thetaCuspNativeReflectionJet_four (x : ℝ) :
    thetaCuspNativeReflectionJet 4 x = thetaCuspSourceReflectionJetFour x := by
  rw [thetaCuspNativeReflectionJet_eq]
  norm_num [Finset.sum_range_succ, Nat.choose, thetaCuspSourceReflectionJetFour]
  ring

/-- Compatibility with the existing order-6 reflected-source jet. -/
theorem thetaCuspNativeReflectionJet_six (x : ℝ) :
    thetaCuspNativeReflectionJet 6 x = thetaCuspSourceReflectionJetSix x := by
  rw [thetaCuspNativeReflectionJet_eq]
  norm_num [Finset.sum_range_succ, Nat.choose, thetaCuspSourceReflectionJetSix, HilbertMetric.reflectedProductSixthJet]
  ring

/-- Compatibility with the existing order-8 reflected-source jet. -/
theorem thetaCuspNativeReflectionJet_eight (x : ℝ) :
    thetaCuspNativeReflectionJet 8 x = thetaCuspSourceReflectionJetEight x := by
  rw [thetaCuspNativeReflectionJet_eq]
  norm_num [Finset.sum_range_succ, Nat.choose, thetaCuspSourceReflectionJetEight, HilbertMetric.reflectedProductEighthJet]
  ring

/-- Odd rank-three block of the signed native reflection-jet Hankel matrix. -/
def thetaCuspNativeOddHankelThree (x : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-thetaCuspNativeReflectionJet 2 x, thetaCuspNativeReflectionJet 4 x,
       -thetaCuspNativeReflectionJet 6 x;
     thetaCuspNativeReflectionJet 4 x, -thetaCuspNativeReflectionJet 6 x,
       thetaCuspNativeReflectionJet 8 x;
     -thetaCuspNativeReflectionJet 6 x, thetaCuspNativeReflectionJet 8 x,
       -thetaCuspNativeReflectionJet 10 x]

/-- Determinant of the native signed odd rank-three block. -/
def thetaCuspNativeOddHankelThreeDet (x : ℝ) : ℝ :=
  HilbertMetric.signedEvenHankelThreeDet
    (-thetaCuspNativeReflectionJet 2 x) (thetaCuspNativeReflectionJet 4 x)
    (-thetaCuspNativeReflectionJet 6 x) (thetaCuspNativeReflectionJet 8 x)
    (-thetaCuspNativeReflectionJet 10 x)

/-- The leading odd plane remains strictly positive at every center. -/
theorem thetaCuspNativeOddHankelThree_head_pos (x : ℝ) :
    0 < -thetaCuspNativeReflectionJet 2 x ∧
      0 < (-thetaCuspNativeReflectionJet 2 x)*(-thetaCuspNativeReflectionJet 6 x)-
        (thetaCuspNativeReflectionJet 4 x)^2 := by
  rw [thetaCuspNativeReflectionJet_two, thetaCuspNativeReflectionJet_four,
    thetaCuspNativeReflectionJet_six]
  refine ⟨neg_pos.mpr (thetaCuspSourceReflectionJetTwo_neg x), ?_⟩
  have h := thetaCuspFullSourceReflectionSecondSixthCurvature_pos x
  unfold thetaCuspFullSourceReflectionSecondSixthCurvature at h
  unfold thetaCuspSourceReflectionJetTwo thetaCuspSourceReflectionJetFour
    thetaCuspSourceReflectionJetSix HilbertMetric.reflectedProductSecondJet
    HilbertMetric.reflectedProductFourthJet at *
  simp only [iteratedDeriv_zero, neg_mul_neg] at *
  exact h

/-- Exact source realization of the twelfth-jet modular elimination. -/
theorem thetaCuspNativeOddHankelThreeDet_zero_eq_modularClosure :
    thetaCuspNativeOddHankelThreeDet 0 = thetaCuspSelfDualThetaMass^6 *
      HTGeometry.modularThetaReflectedTenthSeamPolynomial (thetaCuspSelfDualModularScale^2) := by
  have h := thetaCuspFullSource_oddHankelThreeSeam_eq_modularPolynomial
  dsimp only at h
  apply Complex.ofReal_injective
  have ho1 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 1) (by norm_num : Odd 1)
  have ho3 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 3) (by norm_num : Odd 3)
  have ho5 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 5) (by norm_num : Odd 5)
  have ho7 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 7) (by norm_num : Odd 7)
  have ho9 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 9) (by norm_num : Odd 9)
  unfold thetaCuspNativeOddHankelThreeDet
  simp_rw [thetaCuspNativeReflectionJet_eq]
  norm_num [Finset.sum_range_succ, Nat.choose, ho1, ho3, ho5, ho7, ho9] at ⊢
  simp only [HTGeometry.signedEvenHankelThreeDetC, HilbertMetric.signedEvenHankelThreeDet,
    HTGeometry.modularThetaReflectedTenthSeamPolynomial, iteratedDeriv_zero] at h ⊢
  push_cast
  convert h using 1; ring

/-- Unconditional strict failure of the native odd rank-three seam determinant. -/
theorem thetaCuspNativeOddHankelThreeDet_zero_neg : thetaCuspNativeOddHankelThreeDet 0 < 0 := by
  rw [thetaCuspNativeOddHankelThreeDet_zero_eq_modularClosure]
  have hm : 0 < thetaCuspSelfDualThetaMass := by
    linarith [thetaCuspSelfDualThetaMass_gt_five_thousand_four_hundred_thirty_one_div_five_thousand]
  exact mul_neg_of_pos_of_neg (pow_pos hm 6)
    (HTGeometry.modularThetaReflectedTenthSeamPolynomial_neg
      thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one.le
      thetaCuspSelfDualModularScale_sq_lt_twenty.le)

/-- The negative native block persists on a nontrivial open center chamber. -/
theorem exists_thetaCuspNativeOddHankelThreeDet_neg_near_zero :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| < δ → thetaCuspNativeOddHankelThreeDet x < 0 := by
  have hc : Continuous thetaCuspNativeOddHankelThreeDet := by
    unfold thetaCuspNativeOddHankelThreeDet HilbertMetric.signedEvenHankelThreeDet
    have := continuous_thetaCuspNativeReflectionJet
    fun_prop
  have he := hc.continuousAt.eventually (eventually_lt_nhds thetaCuspNativeOddHankelThreeDet_zero_neg)
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp he
  exact ⟨δ, hδ, fun x hx => hb (by simpa [Real.dist_eq] using hx)⟩

/-- The existing five-dimensional native jet block is strictly positive on the physical ray. -/
theorem thetaCuspNativeFivePointJet_posDef {x : ℝ} (hx : 0 < x) :
    (HilbertMetric.fivePointJetMatrix
      (thetaCuspNativeReflectionJet 0 x) (thetaCuspNativeReflectionJet 2 x)
      (thetaCuspNativeReflectionJet 4 x) (thetaCuspNativeReflectionJet 6 x)
      (thetaCuspNativeReflectionJet 8 x)).PosDef := by
  have hhead := (thetaCuspNativeOddHankelThree_head_pos x).2
  rw [thetaCuspNativeReflectionJet_zero, thetaCuspNativeReflectionJet_two,
    thetaCuspNativeReflectionJet_four, thetaCuspNativeReflectionJet_six,
    thetaCuspNativeReflectionJet_eight]
  apply HilbertMetric.fivePointJetMatrix_posDef
  · exact sq_pos_of_pos (thetaCuspFullSource_pos_of_pos hx)
  · exact thetaCuspSourceReflectionJetTwo_neg x
  · exact thetaCuspSourceReflectionFourthHankel_pos hx
  · simpa only [thetaCuspNativeReflectionJet_two, thetaCuspNativeReflectionJet_four,
      thetaCuspNativeReflectionJet_six, neg_mul_neg] using hhead
  · have hs := thetaCuspFullSource_pos_of_pos hx
    have hraw : 0 < thetaCuspFullSourceReflectionEighthHankelCurvature x := by
      rw [thetaCuspFullSourceReflectionEighthHankelCurvature_eq_fullReflection hx]
      exact mul_pos (by positivity)
        (thetaCuspFullReflectionEighthHankelCurvature_pos_on_nonnegative x hx.le)
    simpa only [thetaCuspFullSourceReflectionEighthHankelCurvature,
      thetaCuspSourceReflectionJetZero, thetaCuspSourceReflectionJetTwo,
      thetaCuspSourceReflectionJetFour, thetaCuspSourceReflectionJetSix,
      thetaCuspSourceReflectionJetEight, HilbertMetric.reflectedProductSecondJet,
      HilbertMetric.reflectedProductFourthJet, iteratedDeriv_zero] using hraw

/-- A negative native determinant gives an explicit nonzero polynomial witness. -/
theorem thetaCuspNativeOddHankelThree_not_posSemidef {x : ℝ}
    (hneg : thetaCuspNativeOddHankelThreeDet x < 0) :
    ¬ (thetaCuspNativeOddHankelThree x).PosSemidef := by
  let a := -thetaCuspNativeReflectionJet 2 x
  let b := thetaCuspNativeReflectionJet 4 x
  let c := -thetaCuspNativeReflectionJet 6 x
  let d := thetaCuspNativeReflectionJet 8 x
  let e := -thetaCuspNativeReflectionJet 10 x
  have hhead : 0 < a*c-b^2 := (thetaCuspNativeOddHankelThree_head_pos x).2
  have hD : HilbertMetric.signedEvenHankelThreeDet a b c d e < 0 := hneg
  have hQ : hankelThreeQuadratic a b c d e (b*d-c^2) (b*c-a*d) (a*c-b^2) < 0 := by
    rw [hankelThreeQuadratic_cofactor]
    exact mul_neg_of_pos_of_neg hhead hD
  intro hps
  have hp := hps.dotProduct_mulVec_nonneg ![b*d-c^2,b*c-a*d,a*c-b^2]
  have heq : star ![b*d-c^2,b*c-a*d,a*c-b^2] ⬝ᵥ
      (thetaCuspNativeOddHankelThree x *ᵥ ![b*d-c^2,b*c-a*d,a*c-b^2]) =
      hankelThreeQuadratic a b c d e (b*d-c^2) (b*c-a*d) (a*c-b^2) := by
    simp [thetaCuspNativeOddHankelThree, dotProduct, mulVec, Fin.sum_univ_succ,
      hankelThreeQuadratic, a,b,c,d,e]
    ring
  rw [heq] at hp
  exact (not_lt_of_ge hp) hQ

/-- The positive survivor and exact negative scalar channel coexist on an open physical interval. -/
theorem exists_thetaCuspNativeSixthRankBoundary :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 < x → x < δ →
      (HilbertMetric.fivePointJetMatrix
        (thetaCuspNativeReflectionJet 0 x) (thetaCuspNativeReflectionJet 2 x)
        (thetaCuspNativeReflectionJet 4 x) (thetaCuspNativeReflectionJet 6 x)
        (thetaCuspNativeReflectionJet 8 x)).PosDef ∧
      ¬ (thetaCuspNativeOddHankelThree x).PosSemidef := by
  obtain ⟨δ,hδ,hn⟩ := exists_thetaCuspNativeOddHankelThreeDet_neg_near_zero
  exact ⟨δ,hδ,fun x hx hxδ => ⟨thetaCuspNativeFivePointJet_posDef hx,
    thetaCuspNativeOddHankelThree_not_posSemidef (hn x (by simpa [abs_of_pos hx] using hxδ))⟩⟩

/-- The native odd block is exactly its strict positive plane plus one Schur scalar. -/
theorem thetaCuspNativeOddHankelThree_schur_split (r x y z : ℝ) :
    let a := -thetaCuspNativeReflectionJet 2 r
    let b := thetaCuspNativeReflectionJet 4 r
    let c := -thetaCuspNativeReflectionJet 6 r
    let d := thetaCuspNativeReflectionJet 8 r
    let e := -thetaCuspNativeReflectionJet 10 r
    hankelThreeQuadratic a b c d e
      (x+(b*d-c^2)/(a*c-b^2)*z) (y+(b*c-a*d)/(a*c-b^2)*z) z =
      hankelThreeQuadratic a b c d e x y 0 +
      thetaCuspNativeOddHankelThreeDet r/(a*c-b^2)*z^2 := by
  exact hankelThreeQuadratic_schur_split
    (thetaCuspNativeOddHankelThree_head_pos r).2.ne' x y z

/-- Literal unnormalized mixed translation-derivative matrix of a native reflection fibre. -/
def thetaCuspNativeTranslationJetMatrix (N : ℕ) (x : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => (-1 : ℝ)^j.val * thetaCuspNativeReflectionJet (i.val+j.val) x

/-- Reflection-product symmetry kills every odd jet. -/
theorem thetaCuspNativeReflectionJet_odd (x : ℝ) {n : ℕ} (hn : Odd n) :
    thetaCuspNativeReflectionJet n x = 0 := by
  apply iteratedDeriv_zero_of_even_real_of_odd (n:=n) ?_ hn
  intro t
  simp only [sub_eq_add_neg, neg_neg, mul_comm]

/-- Strict rank five holds throughout the positive center ray. -/
theorem thetaCuspNativeTranslationJetMatrix_five_posDef {x : ℝ} (hx : 0 < x) :
    (thetaCuspNativeTranslationJetMatrix 5 x).PosDef := by
  have heq : thetaCuspNativeTranslationJetMatrix 5 x =
      HilbertMetric.fivePointJetMatrix
        (thetaCuspNativeReflectionJet 0 x) (thetaCuspNativeReflectionJet 2 x)
        (thetaCuspNativeReflectionJet 4 x) (thetaCuspNativeReflectionJet 6 x)
        (thetaCuspNativeReflectionJet 8 x) := by
    ext i j
    have h1 := thetaCuspNativeReflectionJet_odd x (by norm_num : Odd 1)
    have h3 := thetaCuspNativeReflectionJet_odd x (by norm_num : Odd 3)
    have h5 := thetaCuspNativeReflectionJet_odd x (by norm_num : Odd 5)
    have h7 := thetaCuspNativeReflectionJet_odd x (by norm_num : Odd 7)
    fin_cases i <;> fin_cases j <;>
      norm_num [thetaCuspNativeTranslationJetMatrix,HilbertMetric.fivePointJetMatrix,h1,h3,h5,h7]
  rw [heq]
  exact thetaCuspNativeFivePointJet_posDef hx

/-- The signed odd block is a diagonal congruence of the literal rank-six principal block. -/
theorem thetaCuspNativeTranslationJetMatrix_six_not_posSemidef {x : ℝ}
    (hn : thetaCuspNativeOddHankelThreeDet x < 0) :
    ¬ (thetaCuspNativeTranslationJetMatrix 6 x).PosSemidef := by
  intro h
  let e : Fin 3 → Fin 6 := fun i => ⟨2*i.val+1, by omega⟩
  let D : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![1,-1,1]
  have hp := (h.submatrix e).conjTranspose_mul_mul_same D
  apply thetaCuspNativeOddHankelThree_not_posSemidef hn
  convert hp using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e,D,thetaCuspNativeOddHankelThree,thetaCuspNativeTranslationJetMatrix,
      Matrix.mul_apply, Matrix.diagonal, Fin.sum_univ_succ]

/-- Sharp uniform leading rank for the literal native translation-jet hierarchy. -/
theorem exists_thetaCuspNativeTranslationJet_rankFiveBoundary :
    (∀ x : ℝ, 0 < x → (thetaCuspNativeTranslationJetMatrix 5 x).PosDef) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 < x → x < δ →
      ¬ (thetaCuspNativeTranslationJetMatrix 6 x).PosSemidef := by
  refine ⟨fun _ hx => thetaCuspNativeTranslationJetMatrix_five_posDef hx, ?_⟩
  obtain ⟨δ,hδ,hn⟩ := exists_thetaCuspNativeOddHankelThreeDet_neg_near_zero
  exact ⟨δ,hδ,fun x hx hxδ => thetaCuspNativeTranslationJetMatrix_six_not_posSemidef
    (hn x (by simpa [abs_of_pos hx] using hxδ))⟩

end
end RHTower
