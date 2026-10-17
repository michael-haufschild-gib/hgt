import GaloisForLFunctions.RHTower.PrimeLogHolomorphicUniqueness
import GaloisForLFunctions.HTGeometry.BurnolComplexLaplaceFeature
import GaloisForLFunctions.RHTower.PrimeLogCubicLaplaceGraphFormation

/-! The actual critical-prime Burnol columns form a total Hilbert feature family. -/

noncomputable section
open MeasureTheory Set Complex Filter
open scoped InnerProductSpace ComplexConjugate

namespace RHTower
open GaloisForLFunctions.HTGeometry _root_.HTGeometry PrimeBlindCarlson

/-- The unamplified Burnol feature at an actual prime logarithm. -/
def primeBurnolRawFeature (p : Nat.Primes) : BurnolHalfLineL2 :=
  burnolComplexFeature (Real.log (p : ℝ))
    (Real.log_pos (by exact_mod_cast p.property.one_lt))

def primeBurnolFeatureScale (p : Nat.Primes) : ℝ :=
  2 * Real.log (p : ℝ)^2 / Real.sqrt (p : ℝ)

theorem primeBurnolFeatureScale_pos (p : Nat.Primes) : 0 < primeBurnolFeatureScale p := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  have hl : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.property.one_lt)
  unfold primeBurnolFeatureScale
  positivity

/-- Exact normalization of the existing critical-prime Laplace column. -/
theorem primeLogCriticalLaplaceFeatureL2_eq_burnol (p : Nat.Primes) :
    primeLogCriticalLaplaceFeatureL2 p =
      (primeBurnolFeatureScale p : ℂ) • primeBurnolRawFeature p := by
  rw [primeBurnolRawFeature, burnolComplexFeature_ofReal]
  refine Lp.ext ?_
  let ell : Ioi (0 : ℝ) := ⟨Real.log (p : ℝ), Real.log_pos (by exact_mod_cast p.property.one_lt)⟩
  filter_upwards [primeLogCriticalLaplaceFeatureL2_ae p,
    Lp.coeFn_smul (primeBurnolFeatureScale p : ℂ) (burnolDepthFeatureL2 ell 0),
    burnolDepthFeatureL2_ae ell 0] with t hp hs hd
  rw [hp, hs, Pi.smul_apply, hd, smul_eq_mul]
  simp only [primeLogCriticalLaplaceFeatureC, primeLogCriticalLaplaceFeature,
    primeBurnolFeatureScale, burnolDepthFeature, Nat.cast_zero, zero_add, one_mul]
  dsimp [ell]
  push_cast
  ring

theorem burnolComplexCoordinate_analytic (f : BurnolHalfLineL2) :
    AnalyticOnNhd ℂ (burnolComplexCoordinate f) PrimeBlindCarlson.rightHalf := by
  apply DifferentiableOn.analyticOnNhd _ PrimeBlindCarlson.isOpen_rightHalf
  intro z hz
  exact (burnolComplexCoordinate_differentiableAt f hz).differentiableWithinAt

/-- Actual prime logarithms already give a total feature family in the Burnol output space. -/
theorem primeBurnolRawFeature_span_orthogonal :
    (Submodule.span ℂ (Set.range primeBurnolRawFeature))ᗮ = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun f hf => ?_
  have hz : ∀ p : ℕ, p.Prime → burnolComplexCoordinate f (Real.log p) = 0 := by
    intro p hp
    have hpair := (Submodule.mem_orthogonal _ f).mp hf (primeBurnolRawFeature ⟨p,hp⟩)
      (Submodule.subset_span ⟨⟨p,hp⟩,rfl⟩)
    rw [burnolComplexCoordinate_eq_inner f (Real.log_pos (by exact_mod_cast hp.one_lt))]
    exact inner_eq_zero_symm.mp hpair
  have hzero := eqOn_zero_of_primeLog_zeros (burnolComplexCoordinate_analytic f)
    (fun δ hδ => burnolComplexCoordinate_bounded f hδ) hz
  let ell : Ioi (0 : ℝ) := ⟨1, by norm_num⟩
  have hdepth : ∀ n : ℕ, inner ℂ (burnolDepthFeatureL2 ell n) f = 0 := by
    intro n
    have hn : 0 < (n + 1 : ℝ) := by positivity
    have hpair := hzero (show ((n + 1 : ℝ) : ℂ) ∈ PrimeBlindCarlson.rightHalf from hn)
    rw [burnolComplexCoordinate_eq_inner f hn] at hpair
    have heq : burnolComplexFeature ((n + 1 : ℝ) : ℂ) hn = burnolDepthFeatureL2 ell n := by
      simpa [ell] using burnolComplexFeature_depth ell n
    rw [heq] at hpair
    exact inner_eq_zero_symm.mp hpair
  have hmem : f ∈ (burnolDepthSpan ell)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    change u ∈ Submodule.span ℂ (Set.range (burnolDepthFeatureL2 ell)) at hu
    refine Submodule.span_induction (fun x hx => ?_) (by simp)
      (fun x y hx hy h1 h2 => by simp [inner_add_left, h1, h2])
      (fun c x hx h => by simp [inner_smul_left, h]) hu
    obtain ⟨n,rfl⟩ := hx
    exact hdepth n
  rw [burnolDepthSpan_orthogonal ell] at hmem
  exact hmem

theorem dense_primeBurnolRawFeature_span :
    Dense (Submodule.span ℂ (Set.range primeBurnolRawFeature) : Set BurnolHalfLineL2) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (Submodule.topologicalClosure_eq_top_iff.mpr primeBurnolRawFeature_span_orthogonal)

theorem denseRange_primeBurnolRawSynthesis :
    DenseRange (Finsupp.linearCombination ℂ primeBurnolRawFeature) := by
  have h := congrArg (fun K : Submodule ℂ BurnolHalfLineL2 => (K : Set BurnolHalfLineL2))
    (Finsupp.range_linearCombination ℂ (v := primeBurnolRawFeature))
  change Set.range (Finsupp.linearCombination ℂ primeBurnolRawFeature) = _ at h
  change Dense (Set.range (Finsupp.linearCombination ℂ primeBurnolRawFeature))
  rw [h]
  exact dense_primeBurnolRawFeature_span

/-- Physical critical columns have the same dense span as the raw prime features. -/
theorem dense_primeLogCriticalLaplaceFeature_span :
    Dense (Submodule.span ℂ (Set.range primeLogCriticalLaplaceFeatureL2) :
      Set BurnolHalfLineL2) := by
  apply dense_primeBurnolRawFeature_span.mono
  change Submodule.span ℂ (Set.range primeBurnolRawFeature) ≤
    Submodule.span ℂ (Set.range primeLogCriticalLaplaceFeatureL2)
  apply Submodule.span_le.mpr
  rintro _ ⟨p,rfl⟩
  have hc : (primeBurnolFeatureScale p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (primeBurnolFeatureScale_pos p).ne'
  have heq : primeBurnolRawFeature p = (primeBurnolFeatureScale p : ℂ)⁻¹ •
      primeLogCriticalLaplaceFeatureL2 p := by
    rw [primeLogCriticalLaplaceFeatureL2_eq_burnol, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p,rfl⟩)

/-- An operator is determined by its action on the actual critical-prime columns. -/
theorem primeBurnol_operator_ext {T U : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2}
    (h : ∀ p, T (primeLogCriticalLaplaceFeatureL2 p) = U (primeLogCriticalLaplaceFeatureL2 p)) :
    T = U := by
  apply ContinuousLinearMap.ext_on dense_primeLogCriticalLaplaceFeature_span
  rintro _ ⟨p,rfl⟩
  exact h p

end RHTower
