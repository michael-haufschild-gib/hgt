import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerBoundaryResolvent
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivThreeFourOne

/-! The logarithmic derivative of the actual shifted Mayer boundary inverse
has nonnegative von Mangoldt weights. Its three-four-one positivity is
therefore a property of the source observable itself. -/

open Complex Set Filter Topology ArithmeticFunction
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerParameter MayerBoundaryResolvent
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerBoundaryPositivity

/-- Shifted actual constant-input, boundary-output inverse entry. -/
def shiftedBoundary (s : ℂ) : ℂ := positiveBoundary (s+1)

/-- Negative logarithmic derivative of the actual boundary response. -/
def boundarySlope (s : ℂ) : ℂ := -logDeriv shiftedBoundary s

/-- Exact absolute-chamber value of the actual inverse entry. -/
theorem shiftedBoundary_eq {s : ℂ} (hs : 1 < s.re) :
    shiftedBoundary s=2*riemannZeta s/riemannZeta (s+1) := by
  have hw : 2 < (s+1).re := by simp only [Complex.add_re,Complex.one_re]; linarith only [hs]
  have h0 : 0 < (s+1).re := by linarith only [hw]
  have hD : sourceDeterminant (s+1) 1 ≠ 0 := by
    rw [sourceDeterminant_eq h0]
    exact MayerUnitOrbitDeterminant.determinant_ne_zero_on_closed_unit hw (by simp)
  rw [shiftedBoundary,positiveBoundary_eq_cofactor h0,
    MayerCoprimeCofactor.polePart_eq_response hw,MayerCoprimeHeight.green_zero hw,add_sub_cancel_right]
  field_simp [hD]

/-- Logarithmic differentiation retains the shifted denominator correction. -/
theorem boundarySlope_eq {s : ℂ} (hs : 1 < s.re) :
    boundarySlope s=-logDeriv riemannZeta s+logDeriv riemannZeta (s+1) := by
  have he : shiftedBoundary =ᶠ[𝓝 s] fun v => 2*(riemannZeta v/riemannZeta (v+1)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with v hv
    rw [shiftedBoundary_eq hv]
    ring
  have hs1 : 1 < (s+1).re := by simp only [Complex.add_re,Complex.one_re]; linarith only [hs]
  have hsne : s ≠ 1 := by intro h; norm_num [h] at hs
  have hs1ne : s+1 ≠ 1 := by intro h; norm_num [h] at hs1
  have hds := differentiableAt_riemannZeta hsne
  have hdt : DifferentiableAt ℂ (fun v => riemannZeta (v+1)) s :=
    (differentiableAt_riemannZeta hs1ne).comp s (differentiableAt_id.add_const 1)
  have hl : logDeriv shiftedBoundary s=
      logDeriv (fun v => 2*(riemannZeta v/riemannZeta (v+1))) s := by
    rw [logDeriv_apply,logDeriv_apply,he.deriv_eq,he.eq_of_nhds]
  rw [boundarySlope,hl,logDeriv_const_mul s 2 (by norm_num),
    logDeriv_div (f := riemannZeta) (g := fun v => riemannZeta (v+1)) s
      (riemannZeta_ne_zero_of_one_lt_re hs)
      (riemannZeta_ne_zero_of_one_lt_re hs1) hds hdt]
  have ht : logDeriv (fun v => riemannZeta (v+1)) s=logDeriv riemannZeta (s+1) := by
    rw [logDeriv_apply,logDeriv_apply,deriv_comp_add_const]
  rw [ht]
  ring

/-- The Dirichlet coefficient factor introduced by the shifted denominator. -/
def boundaryWeight (n : ℕ) : ℝ := 1-1/(n : ℝ)

/-- All boundary coefficient factors are nonnegative, including the zero convention. -/
theorem boundaryWeight_nonneg (n : ℕ) : 0 ≤ boundaryWeight n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num [boundaryWeight]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
    exact sub_nonneg.mpr ((div_le_iff₀ hn0).mpr (by simpa using hn1))

private def zetaTerm (s : ℂ) (n : ℕ) : ℂ :=
  LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ)) s n

private theorem zeta_hasSum {s : ℂ} (hs : 1 < s.re) :
    HasSum (zetaTerm s) (-logDeriv riemannZeta s) := by
  have h := (LSeriesSummable_vonMangoldt hs).LSeriesHasSum
  rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs] at h
  change HasSum (LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ)) s) _
  simpa only [LSeriesHasSum,logDeriv_apply,neg_div] using! h

private theorem weighted_term (s : ℂ) (n : ℕ) :
    ((boundaryWeight n : ℝ) : ℂ)*zetaTerm s n=zetaTerm s n-zetaTerm (s+1) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [zetaTerm,LSeries.term]
  · have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp only [zetaTerm,LSeries.term_of_ne_zero hn]
    rw [Complex.cpow_add _ _ hn0,Complex.cpow_one,boundaryWeight]
    push_cast
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring

/-- The actual source slope is the convergent von Mangoldt series with positive boundary weights. -/
theorem boundarySlope_hasSum {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => ((boundaryWeight n : ℝ) : ℂ)*
      LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ)) s n) (boundarySlope s) := by
  have hs1 : 1 < (s+1).re := by simp only [Complex.add_re,Complex.one_re]; linarith only [hs]
  have h := (zeta_hasSum hs).sub (zeta_hasSum hs1)
  rw [boundarySlope_eq hs]
  change HasSum (fun n : ℕ => ((boundaryWeight n : ℝ) : ℂ)*zetaTerm s n) _
  simp only [weighted_term]
  simpa only [sub_neg_eq_add] using h

/-- Three-four-one positivity follows termwise from nonnegative source coefficients. -/
theorem three_four_one {σ t : ℝ} (hσ : 1 < σ) :
    0 ≤ 3*(boundarySlope (σ : ℂ)).re+
      4*(boundarySlope ((σ : ℂ)+(t : ℂ)*I)).re+
      (boundarySlope ((σ : ℂ)+(2*t : ℂ)*I)).re := by
  have h0 := hasSum_re (boundarySlope_hasSum (s := (σ : ℂ)) (by simpa using hσ))
  have h1 := hasSum_re (boundarySlope_hasSum (s := (σ : ℂ)+(t : ℂ)*I) (by simpa using hσ))
  have h2 := hasSum_re (boundarySlope_hasSum (s := (σ : ℂ)+(2*t : ℂ)*I) (by simpa using hσ))
  apply (((h0.mul_left 3).add (h1.mul_left 4)).add h2).nonneg
  intro n
  simp only [Complex.re_ofReal_mul]
  have h := mul_nonneg (boundaryWeight_nonneg n)
    (_root_.RHTower.Sieve.zero_le_three_four_one_vonMangoldt_term (σ := σ) (t := t) n)
  convert h using 1; ring

#print axioms shiftedBoundary_eq
#print axioms boundarySlope_eq
#print axioms boundaryWeight_nonneg
#print axioms boundarySlope_hasSum
#print axioms three_four_one
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerBoundaryPositivity
