import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.RelativeExcursion
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.RateScaling

/-! # Divergence of the first-excursion moment measured in mean entry spacings -/
open MeasureTheory ProbabilityTheory Filter Set Real
namespace GaloisForLFunctions.HTGeometry.WeakBonds
open PrescribedTimes
noncomputable section

/-- Measuring both passages in mean-spacing units removes the Gaussian radial speed exactly. -/
theorem fluxExcursion_smul (n P : ℕ) (x : PrefixIndex n → ℝ) {q : ℝ} (hq : 0 < q) :
    fluxExcursion n P (q • x)=fluxExcursion n P x := by
  unfold fluxExcursion
  rw [emptyRate_smul _ _ _ hq,mul_comm q, mul_assoc,mul_min_of_nonneg _ _ hq.le,
    smul_crossingOrigin _ _ _ hq,smul_crossingWait _ _ _ hq]

private theorem transfer_moment {X : Type*} [MeasurableSpace X] (μ : Measure X) (Q : Set X)
    (J F : X → ℝ) (hQ : MeasurableSet Q) (hJ : Measurable J) {β : ℝ} (hβ : 0 < β)
    (hfloor : ∀ x ∈ Q, β*|J x| ≤ |F x|)
    (hdiv : ¬Integrable (fun x => |Q.indicator J x|^18) μ) :
    ¬Integrable (fun x => |F x|^18) μ := by
  have hm : Measurable (fun x => |Q.indicator J x|^18) := by
    simpa only [Real.norm_eq_abs] using (hJ.indicator hQ).norm.pow_const (18:ℕ)
  intro hint
  apply hdiv
  apply (hint.const_mul ((1/β)^18)).mono' hm.aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg _) _),←mul_pow]
  apply pow_le_pow_left₀ (abs_nonneg _) _ 18
  by_cases hx : x∈Q
  · rw [indicator_of_mem hx,one_div,←div_eq_inv_mul,le_div_iff₀ hβ,mul_comm]
    exact hfloor x hx
  · rw [indicator_of_notMem hx,abs_zero]
    exact mul_nonneg (one_div_pos.mpr hβ).le (abs_nonneg _)

private theorem retained_flux_moment {n P : ℕ} (a b : Fin (n+1)) (μ : Measure (PrefixIndex n → ℝ))
    (q : (PrefixIndex n → ℝ) → ℝ) (hq : ∀ x, 1≤coefficientNorm x → 0 < q x) :
    let Q := retainedSector (cutSet a b) (Icc 1 2)
    let J := fun x => min (crossingOrigin n P (9/80) x) (crossingWait n P (P/2) x)
    ¬Integrable (fun x => |Q.indicator J x|^18) μ →
      ¬Integrable (fun x => |fluxExcursion n P (q x • x)|^18) μ := by
  intro Q J hdiv
  have hJ : Measurable J := (measurable_crossingOrigin _ _ _).min (measurable_crossingWait _ _ _)
  have hs : (1/10:ℝ) < sqrt 2 := by nlinarith only [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg 2]
  obtain ⟨hβ,hfloor⟩ := coefficient_rate_floor n (1/10) (by norm_num) hs
  refine transfer_moment μ Q J _ (measurable_retainedSector (cutSet a b) measurableSet_Icc) hJ hβ ?_ hdiv
  intro x hx
  have hn := retained_coefficient_norm (n := n) a b x hx
  have hf := (le_mul_of_one_le_right hβ.le hn).trans (hfloor x)
  rw [fluxExcursion_smul n P x (hq x hn),fluxExcursion,abs_mul,abs_of_nonneg (hβ.le.trans hf)]
  exact mul_le_mul_of_nonneg_right hf (abs_nonneg _)

/-- The eighteenth moment of the true first excursion in mean-spacing
units diverges even after an arbitrary positive radial rescaling of each
draw. The selected scale may depend on the entire generator. -/
theorem gaussian_relative_excursion_moment :
    ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let P := nearHilbertContinuousCircuitBudget (k+3)
      let μ := Measure.pi (fun _ : PrefixIndex n => gaussianReal 0 1)
      ∀ q : (PrefixIndex n → ℝ) → ℝ, (∀ x, 1≤coefficientNorm x → 0 < q x) →
        ¬Integrable (fun x => |fluxExcursion n P (q x • x)|^18) μ := by
  filter_upwards [gaussian_two_weak_bonds_moment] with k hk
  intro n P μ q hq
  obtain ⟨a,b,_,hbulk⟩ := hk
  exact retained_flux_moment (n := k+1) (P := P) a b μ q hq (hbulk (P/2) le_rfl)

#print axioms gaussian_relative_excursion_moment
#print axioms fluxExcursion_smul
end
end GaloisForLFunctions.HTGeometry.WeakBonds
