import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathCoefficientMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.CoordinateLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.UnivariateSublevel

/-! # Lower longitudinal mass on every positive-density set of Gaussian bonds -/
open Filter MeasureTheory ProbabilityTheory Set Polynomial
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.SpanningDensity
noncomputable section

private theorem mass_at_scale (q : ℝ) (hq : 0<q) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ S : Finset (Fin (n+1)),
      q*((S.card:ℝ)-3*q*(n+1:ℕ)) ≤ ∑ e∈S, |pathPauliDisorderShell ω n (.inr (e,2,2))| := by
  classical
  let γ := gaussianReal 0 1
  let D : Set ℝ := {x | |x|<q}
  have hm : MeasurableSet D := measurableSet_lt measurable_abs measurable_const
  let f := D.indicator (fun _ : ℝ => (1:ℝ))
  have hi : Integrable f γ := (integrable_const _).indicator hm
  have hs : γ.real D ≤ 2*q := by
    simpa only [γ,D,Polynomial.eval_X,Polynomial.leadingCoeff_X,norm_one,Polynomial.natDegree_X,
      pow_one,one_mul,Nat.cast_one,mul_one,Complex.norm_real,Real.norm_eq_abs] using
      gaussian_polynomial_sublevel (Polynomial.X:ℂ[X]) q hq.le
  have hμ : (∫ x, f x ∂γ)=γ.real D := by simp [f,integral_indicator hm]
  have hslln := LocalPatches.coordinate_strong_law γ (Sum.inr (2,2) : PathPauliDirections) f
    (measurable_const.indicator hm) hi
  filter_upwards [hslln] with ω hω
  have hq' : (∫ x, f x ∂γ)<3*q := by linarith only [hμ,hs,hq]
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (hω.eventually_lt_const hq')] with n hn
  let v (e : Fin (n+1)) := ω (e.val,Sum.inr (2,2))
  have hN : 0<((n+1:ℕ):ℝ) := by positivity
  have hsum : (∑ e : Fin (n+1), f (v e)) ≤ 3*q*(n+1:ℕ) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => f (ω (i,Sum.inr (2,2))))]
    exact ((div_lt_iff₀ hN).mp hn).le
  intro S
  have hn' (x : ℝ) : 0≤f x := by by_cases h : x∈D <;> simp [f,h]
  have hx (x : ℝ) : q ≤ |x|+q*f x := by
    by_cases h : x∈D
    · simp [f,h,abs_nonneg]
    · simpa only [f,indicator_of_notMem h,mul_zero,add_zero] using le_of_not_gt h
  have ha := Finset.sum_le_sum (s:=S) (fun e _ => hx (v e))
  rw [Finset.sum_const,nsmul_eq_mul,Finset.sum_add_distrib,←Finset.mul_sum] at ha
  have hb := mul_le_mul_of_nonneg_left
    ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun e _ _ => hn' (v e))).trans hsum) hq.le
  change q*((S.card:ℝ)-3*q*(n+1:ℕ)) ≤ ∑ e∈S, |v e|
  linarith only [ha,hb]

/-- One draw simultaneously controls every bond set at every reciprocal
integer cutoff. The set can depend on the draw and on the circuit. -/
theorem gaussian_subset_longitudinal_mass :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, let q : ℝ := 1/(k+1:ℕ)
      ∀ᶠ n : ℕ in atTop, ∀ S : Finset (Fin (n+1)),
        q*((S.card:ℝ)-3*q*(n+1:ℕ)) ≤ ∑ e∈S, |pathPauliDisorderShell ω n (.inr (e,2,2))| :=
  ae_all_iff.mpr fun k => mass_at_scale _ (by positivity)

#print axioms gaussian_subset_longitudinal_mass
end
end GaloisForLFunctions.HTGeometry.SpanningDensity
