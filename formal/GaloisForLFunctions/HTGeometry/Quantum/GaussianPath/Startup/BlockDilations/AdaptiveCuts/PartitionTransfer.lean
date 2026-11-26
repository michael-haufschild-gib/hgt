import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.SelectedCoordinates
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Gaussian pattern counting with a draw-dependent spatial partition -/

open MeasureTheory ProbabilityTheory Finset Set
namespace GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
noncomputable section
variable {ι P J : Type*} [Fintype ι] [DecidableEq ι] [Fintype P] [Fintype J]

omit [Fintype ι] in
private theorem measurable_selected (S : Finset ι) (a : ℝ) : Measurable (expand S a) := by
  apply measurable_pi_lambda
  intro i
  by_cases h : i∈S
  · simpa only [expand,if_pos h] using (measurable_pi_apply (X:=fun _ : ι => ℝ) i).const_mul a
  · simpa only [expand,if_neg h] using (measurable_pi_apply (X:=fun _ : ι => ℝ) i)

/-- A pointwise selector common to all successful patterns removes the
number of spatial partitions from the Gaussian change-of-variables cost. -/
theorem partition_pattern_cap (S : P→J→Finset ι) (E : P→Set (ι→ℝ))
    (hE : ∀ p, MeasurableSet (E p)) (owner : (ι→ℝ)→P) {a : ℝ} (ha : 1≤a)
    (howner : ∀ x p j, expand (S p j) a x∈E p → p=owner x) :
    open Classical in
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    ∀ M : ℝ, (∀ x, ((univ.filter fun j => expand (S (owner x) j) a x∈E (owner x)).card:ℝ)≤M) →
      (∑ p, μ.real (E p))*(Fintype.card J:ℝ) ≤ a^Fintype.card ι*M := by
  classical
  intro μ M hcap
  let d := a^Fintype.card ι
  have hd : 0≤d := pow_nonneg (zero_le_one.trans ha) _
  let F (p : P) (j : J) := expand (S p j) a ⁻¹' E p
  let f (p : P) (j : J) := (F p j).indicator (1 : (ι→ℝ)→ℝ)
  have hF (p : P) (j : J) : MeasurableSet (F p j) := (hE p).preimage (measurable_selected _ _)
  have hf (p : P) (j : J) : Integrable (f p j) μ := (integrable_const _).indicator (hF p j)
  have h (p : P) (j : J) : μ.real (E p) ≤ d*(∫ x, f p j x ∂μ) := by
    have hcomp := selected_gaussian_comparison (S p j) ha (hE p)
    have hpow : a^(S p j).card≤d := pow_le_pow_right₀ ha (card_le_univ _)
    change _ ≤ d*(∫ x, (F p j).indicator (1 : (ι→ℝ)→ℝ) x ∂μ)
    rw [integral_indicator_one (hF p j)]
    exact hcomp.trans (mul_le_mul_of_nonneg_right hpow measureReal_nonneg)
  have hpoint (x : ι→ℝ) : ∑ p, ∑ j, f p j x ≤ M := by
    rw [sum_eq_single (owner x)]
    · have hcnt := sum_boole (R:=ℝ) (fun j => expand (S (owner x) j) a x∈E (owner x)) univ
      simpa only [f,F,Set.indicator_apply,Pi.one_apply,Set.mem_preimage] using hcnt.trans_le (hcap x)
    · intro p _ hp
      apply sum_eq_zero
      intro j _
      have hx : x∉F p j := fun he => hp (howner x p j he)
      exact Set.indicator_of_notMem hx (1 : (ι→ℝ)→ℝ)
    · exact fun h => (h (mem_univ _)).elim
  have hi := integral_mono (integrable_finsetSum _ (fun p _ => integrable_finsetSum _ (fun j _ => hf p j)))
    (integrable_const (μ:=μ) M) hpoint
  have hh := sum_le_sum (s:=univ) (fun p _ => sum_le_sum (s:=univ) (fun j _ => h p j))
  simp only [sum_const,card_univ,nsmul_eq_mul,←mul_sum] at hh
  rw [mul_comm]
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ hd
  simpa only [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun j _ => hf p j)),
    integral_finsetSum _ (fun j _ => hf _ j),integral_const,probReal_univ,one_smul] using hi

#print axioms partition_pattern_cap
end
end GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
