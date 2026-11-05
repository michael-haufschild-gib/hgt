import GaloisForLFunctions.RHTower.Jensen.HermiteErrorBounds
import GaloisForLFunctions.RHTower.Jensen.HermiteSignMargins

/-!
# Explicit real-rootedness horizons for Xi Jensen polynomials

A finite expression in Hermite roots and their sign margins specifies a
saddle height. A score ceiling then forces all degree-many real sign
changes of the actual normalized Jensen polynomial, at every later shift.
-/

open Polynomial Finset
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.SignAlternation
noncomputable section
namespace RHTower

/-- An explicit saddle height sufficient to preserve all degree-`d` Hermite signs. -/
def xiJensenRealRootedSaddle (d : ℕ) : ℝ :=
  2 + xiJensenFluctuationBound d +
    4 * xiJensenFluctuationBound d *
      (xiJensenHermiteErrorConstant (hermiteSignSampleBound d) d + 1) ^ 2 /
        hermiteSignMargin d ^ 2

/-- A fixed-degree Jensen horizon using only finite algebraic data and a score ceiling. -/
def xiJensenRealRootednessHorizon (d : ℕ) : ℕ :=
  max ⌈thetaJensenScore (xiJensenRealRootedSaddle d)⌉₊ (4 * (d + 1))

theorem xiJensenRealRootedSaddle_ge_two (d : ℕ) : 2 ≤ xiJensenRealRootedSaddle d := by
  have hF := one_le_xiJensenFluctuationBound d
  have hterm : 0 ≤ 4 * xiJensenFluctuationBound d *
      (xiJensenHermiteErrorConstant (hermiteSignSampleBound d) d + 1) ^ 2 /
        hermiteSignMargin d ^ 2 := by positivity
  unfold xiJensenRealRootedSaddle
  linarith only [hF, hterm]

theorem xiJensenHermitePolynomial_error_lt_margin (n d : ℕ)
    (hn : xiJensenRealRootednessHorizon d ≤ n) {x : ℝ}
    (hx : |x| ≤ hermiteSignSampleBound d) :
    |(xiJensenHermitePolynomial n d).eval x - (hermiteReal d).eval x| < hermiteSignMargin d / 2 := by
  have hR : 0 ≤ hermiteSignSampleBound d := (by norm_num : (0 : ℝ) ≤ 1).trans
    (one_le_hermiteSignSampleBound d)
  have hC := xiJensenHermiteErrorConstant_nonneg hR d
  have hm := hermiteSignMargin_pos d
  have hF := one_le_xiJensenFluctuationBound d
  have hN := (le_max_left ⌈thetaJensenScore (xiJensenRealRootedSaddle d)⌉₊ (4 * (d + 1))).trans hn
  have hS := le_thetaJensenSaddle_of_score_ceil_le
    ((by norm_num : (0 : ℝ) ≤ 2).trans (xiJensenRealRootedSaddle_ge_two d)) hN
  have hs := (xiJensenRealRootedSaddle_ge_two d).trans hS
  have hs0 := thetaJensenSaddle_pos n
  have hterm : 0 ≤ 4 * xiJensenFluctuationBound d *
      (xiJensenHermiteErrorConstant (hermiteSignSampleBound d) d + 1) ^ 2 /
        hermiteSignMargin d ^ 2 := by positivity
  have hFs : xiJensenFluctuationBound d ≤ thetaJensenSaddle n := by
    unfold xiJensenRealRootedSaddle at hS
    linarith only [hS, hterm]
  have hcap : 4 * xiJensenFluctuationBound d *
      (xiJensenHermiteErrorConstant (hermiteSignSampleBound d) d + 1) ^ 2 /
        hermiteSignMargin d ^ 2 ≤ thetaJensenSaddle n := by
    unfold xiJensenRealRootedSaddle at hS
    linarith only [hS, hF]
  have hη : Real.sqrt (xiJensenFluctuationBound d / thetaJensenSaddle n) ≤
      hermiteSignMargin d / (2 * (xiJensenHermiteErrorConstant (hermiteSignSampleBound d) d + 1)) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [div_pow, mul_pow]
    norm_num only
    apply (div_le_div_iff₀ hs0 (by positivity)).mpr
    have h := (div_le_iff₀ (sq_pos_of_pos hm)).mp hcap
    nlinarith only [h]
  have herr := xiJensenHermitePolynomial_eval_error_le n d hR hx hs
    ((le_max_right ⌈thetaJensenScore (xiJensenRealRootedSaddle d)⌉₊ (4 * (d + 1))).trans hn) hFs
  refine (herr.trans (mul_le_mul_of_nonneg_left hη hC)).trans_lt ?_
  calc
    _ < (xiJensenHermiteErrorConstant (hermiteSignSampleBound d) d + 1) *
        (hermiteSignMargin d /
          (2 * (xiJensenHermiteErrorConstant (hermiteSignSampleBound d) d + 1))) :=
      mul_lt_mul_of_pos_right (by linarith only []) (by positivity)
    _ = _ := by field_simp

private theorem sign_change_of_close_values {a b u v : ℝ}
    (h : a * b < 0) (hu : |u - a| < |a|) (hv : |v - b| < |b|) : u * v < 0 := by
  rcases mul_neg_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [abs_of_pos ha] at hu
    rw [abs_of_neg hb] at hv
    have hu0 : 0 < u := by linarith only [(abs_lt.mp hu).1]
    have hv0 : v < 0 := by linarith only [(abs_lt.mp hv).2]
    exact mul_neg_of_pos_of_neg hu0 hv0
  · rw [abs_of_neg ha] at hu
    rw [abs_of_pos hb] at hv
    have hu0 : u < 0 := by linarith only [(abs_lt.mp hu).2]
    have hv0 : 0 < v := by linarith only [(abs_lt.mp hv).1]
    exact mul_neg_of_neg_of_pos hu0 hv0

private theorem splits_of_explicit_sign_intervals (P : ℝ[X]) (Z : Finset ℝ)
    {ε : ℝ} (hε : 0 < ε) (hdeg : P.natDegree ≤ Z.card)
    (hsign : ∀ z ∈ Z, P.eval (z - ε) * P.eval (z + ε) < 0)
    (hsep : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → 2 * ε < |z - w|) : P.Splits := by
  classical
  by_cases hP : P = 0
  · subst P
    exact Polynomial.Splits.zero
  have hroot : ∀ z ∈ Z, ∃ r ∈ Set.Ioo (z - ε) (z + ε), P.IsRoot r :=
    fun z hz => exists_root_of_sign_change (by linarith only [hε]) (hsign z hz)
  choose r hr hPr using hroot
  let f : ℝ → ℝ := fun z => if hz : z ∈ Z then r z hz else 0
  have hf (z : ℝ) (hz : z ∈ Z) : f z = r z hz := dif_pos hz
  have hinj : Set.InjOn f Z := by
    intro z hz w hw heq
    by_contra hne
    have hzr := hr z hz
    have hwr := hr w hw
    have he : r z hz = r w hw := by simpa only [hf z hz, hf w hw] using heq
    have hab : |z - w| < 2 * ε := by
      rw [abs_lt]
      constructor <;> linarith only [hzr.1, hzr.2, hwr.1, hwr.2, he]
    exact (not_lt_of_ge hab.le) (hsep z hz w hw hne)
  have hcard : Z.card ≤ P.roots.toFinset.card :=
    Finset.card_le_card_of_injOn (f := f)
      (fun z hz => by
        change f z ∈ P.roots.toFinset
        rw [Multiset.mem_toFinset, mem_roots hP, hf z hz]
        exact hPr z hz) hinj
  have h1 := Multiset.toFinset_card_le P.roots
  have h2 := Polynomial.card_roots' P
  rw [splits_iff_card_roots]
  omega

/-- Beyond the explicit horizon, the actual normalized degree-`d` Xi Jensen polynomial splits. -/
theorem xiJensenHermitePolynomial_splits_of_horizon_le (d n : ℕ)
    (hn : xiJensenRealRootednessHorizon d ≤ n) : (xiJensenHermitePolynomial n d).Splits := by
  apply splits_of_explicit_sign_intervals _ (hermiteSignRoots d)
    (finiteRootSignRadius_pos _) (by
      rw [hermiteSignRoots_card]
      exact natDegree_xiJensenHermitePolynomial_le n d)
  · intro z hz
    have hm := hermiteSignMargin_pos d
    have hmargin := hermiteSignMargin_le_values d hz
    have hbound := abs_hermiteSignSamples_le d hz
    apply sign_change_of_close_values (hermiteSignRoots_sign_change d hz)
    · exact (xiJensenHermitePolynomial_error_lt_margin n d hn hbound.1).trans_le
        ((by linarith only [hm] : hermiteSignMargin d / 2 ≤ hermiteSignMargin d).trans hmargin.1)
    · exact (xiJensenHermitePolynomial_error_lt_margin n d hn hbound.2).trans_le
        ((by linarith only [hm] : hermiteSignMargin d / 2 ≤ hermiteSignMargin d).trans hmargin.2)
  · intro z hz w hw hzw
    exact finiteRootSignRadius_separated _ hz hw hzw

/-- Every actual Xi Jensen polynomial of fixed degree splits at every shift above a finite expression. -/
theorem xiJensenPoly_splits_of_horizon_le (d n : ℕ)
    (hn : xiJensenRealRootednessHorizon d ≤ n) : (jensenPoly xiJensenCoeff d n).Splits := by
  have h := xiJensenHermitePolynomial_splits_of_horizon_le d n hn
  have hγ := (xiJensenCoeff_pos n).ne'
  have hδ := (xiJensenDelta_pos n).ne'
  have hA := (xiJensenScale_pos n).ne'
  have hcomp := (splits_mul_iff_right
    (C_ne_zero.mpr (inv_ne_zero (mul_ne_zero hγ (pow_ne_zero d hδ))))
    (Polynomial.Splits.C _)).mp h
  apply (splits_iff_comp_splits_of_natDegree_eq_one ?_).mpr hcomp
  rw [natDegree_C_mul (inv_ne_zero hA),
    natDegree_sub_eq_left_of_natDegree_lt (by
      simpa only [natDegree_one, natDegree_C_mul hδ, natDegree_X] using Nat.zero_lt_one),
    natDegree_C_mul hδ, natDegree_X]

end RHTower

#print axioms RHTower.xiJensenHermitePolynomial_error_lt_margin
#print axioms RHTower.xiJensenHermitePolynomial_splits_of_horizon_le
#print axioms RHTower.xiJensenPoly_splits_of_horizon_le
