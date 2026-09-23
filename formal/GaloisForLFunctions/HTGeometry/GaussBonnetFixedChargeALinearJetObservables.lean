import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAQuarticHarmonicJets

/-!
# Closed linear jet observables of the actual critical Gibbs potential

Every fixed three-term linear combination of actual Gibbs derivatives
inherits the uniform first-order cancellation. Coefficients and orders
are arbitrary data. This supplies differential spectral projectors
without assuming any unproved convergence or regularity property.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeALinearJetObservable (a b c : ℝ) (j k m : ℕ) (f : ℝ → ℝ) (ψ : ℝ) : ℝ :=
  a * iteratedDeriv j f ψ + b * iteratedDeriv k f ψ + c * iteratedDeriv m f ψ

theorem egbFixedChargeALinearJetObservable_uniform_first_zero_limit
    (w φ l₁ l₂ a b c : ℝ) (j k m : ℕ) :
    TendstoUniformly (fun τ ψ =>
      (egbFixedChargeALinearJetObservable a b c j k m (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ -
       egbFixedChargeALinearJetObservable a b c j k m (fun x : ℝ => cos x ^ (4 : ℕ)) ψ) /
        egbCoexistenceASymmetricRatio τ) (fun _ => (0 : ℝ)) atBot := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  let M := |a| + |b| + |c| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have he : 0 < ε / M := div_pos hε hM
  have hj := (Metric.tendstoUniformly_iff.mp
    (egbFixedChargeAPeakNormalizedGibbs_iteratedDeriv_uniform_first_zero_limit w φ l₁ l₂ j)) (ε / M) he
  have hk := (Metric.tendstoUniformly_iff.mp
    (egbFixedChargeAPeakNormalizedGibbs_iteratedDeriv_uniform_first_zero_limit w φ l₁ l₂ k)) (ε / M) he
  have hm := (Metric.tendstoUniformly_iff.mp
    (egbFixedChargeAPeakNormalizedGibbs_iteratedDeriv_uniform_first_zero_limit w φ l₁ l₂ m)) (ε / M) he
  filter_upwards [hj, hk, hm] with τ hj hk hm
  intro ψ
  have hj := hj ψ
  have hk := hk ψ
  have hm := hm ψ
  simp only [Real.dist_eq, zero_sub, abs_neg] at hj hk hm ⊢
  let e := fun r : ℕ => (iteratedDeriv r (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ -
    iteratedDeriv r (fun x : ℝ => cos x ^ (4 : ℕ)) ψ) / egbCoexistenceASymmetricRatio τ
  have hid : (egbFixedChargeALinearJetObservable a b c j k m (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ -
      egbFixedChargeALinearJetObservable a b c j k m (fun x : ℝ => cos x ^ (4 : ℕ)) ψ) /
        egbCoexistenceASymmetricRatio τ = a * e j + b * e k + c * e m := by
    dsimp [egbFixedChargeALinearJetObservable, e]
    ring
  rw [hid]
  change |e j| < ε / M at hj
  change |e k| < ε / M at hk
  change |e m| < ε / M at hm
  have hsum : |a * e j + b * e k + c * e m| ≤ |a| * |e j| + |b| * |e k| + |c| * |e m| := by
    have h₁ := abs_add_le (a * e j + b * e k) (c * e m)
    have h₂ := abs_add_le (a * e j) (b * e k)
    simp only [abs_mul] at h₁ h₂
    linarith
  have ha := mul_le_mul_of_nonneg_left hj.le (abs_nonneg a)
  have hb := mul_le_mul_of_nonneg_left hk.le (abs_nonneg b)
  have hc := mul_le_mul_of_nonneg_left hm.le (abs_nonneg c)
  have heq : M * (ε / M) = ε := by field_simp
  have hbound : (|a| + |b| + |c|) * (ε / M) < ε := by
    dsimp only [M] at heq
    nlinarith
  nlinarith

theorem egbFixedChargeALinearJetObservable_uniform_limit
    (w φ l₁ l₂ a b c : ℝ) (j k m : ℕ) :
    TendstoUniformly (fun τ ψ =>
      egbFixedChargeALinearJetObservable a b c j k m (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ)
      (egbFixedChargeALinearJetObservable a b c j k m (fun x : ℝ => cos x ^ (4 : ℕ))) atBot := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have he := (Metric.tendstoUniformly_iff.mp
    (egbFixedChargeALinearJetObservable_uniform_first_zero_limit w φ l₁ l₂ a b c j k m)) 1 (by norm_num)
  have hd := egbCoexistenceASymmetricRatio_critical_limit.eventually_lt_const hε
  filter_upwards [he, hd] with τ hτ hδ
  intro ψ
  have hp := (egbCoexistenceASymmetricRatio_bounds τ).1
  have h := hτ ψ
  simp only [Real.dist_eq, zero_sub, abs_neg, abs_div, abs_of_pos hp] at h
  have hx := (div_lt_iff₀ hp).mp h
  simp only [one_mul] at hx
  simpa only [Real.dist_eq, abs_sub_comm] using hx.trans hδ

theorem egbFixedChargeALinearJetObservable_moving_first_zero_limit
    (w φ l₁ l₂ a b c : ℝ) (j k m : ℕ) (ψ : ℝ → ℝ) :
    Tendsto (fun τ =>
      (egbFixedChargeALinearJetObservable a b c j k m (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) (ψ τ) -
       egbFixedChargeALinearJetObservable a b c j k m (fun x : ℝ => cos x ^ (4 : ℕ)) (ψ τ)) /
        egbCoexistenceASymmetricRatio τ) atBot (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have h := (Metric.tendstoUniformly_iff.mp
    (egbFixedChargeALinearJetObservable_uniform_first_zero_limit w φ l₁ l₂ a b c j k m)) ε hε
  filter_upwards [h] with τ hτ
  simpa only [dist_comm] using hτ (ψ τ)

end GaloisForLFunctions.HTGeometry
