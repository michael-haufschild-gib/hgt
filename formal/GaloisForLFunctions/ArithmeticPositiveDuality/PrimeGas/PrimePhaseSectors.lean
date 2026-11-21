import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.PhaseOverlapLogarithm
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Visibility sectors at the partition pole

Two coherent phases have positive limiting overlap magnitude exactly when
their prime coordinates have finite squared distance with weights 1/p.
Removing the damped prime angle also gives a complex limit.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open Filter Topology
open scoped ComplexConjugate Classical

/-- Finite harmonic-prime squared distance of two phase preparations. -/
def samePhaseSector (χ ψ : ℕ+ →* Circle) : Prop :=
  Summable (fun p : Nat.Primes =>
    ‖(ψ (p : ℕ+) : ℂ) - (χ (p : ℕ+) : ℂ)‖^2 / (p : ℕ))

private theorem chord_eq (a b : Circle) :
    ‖(b : ℂ)-(a : ℂ)‖^2 = 2*(1-((b/a : Circle) : ℂ).re) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Circle.normSq_coe, Circle.normSq_coe,
    div_eq_mul_inv, Circle.coe_mul, Circle.coe_inv_eq_conj]
  ring

theorem samePhaseSector_iff_mismatch (χ ψ : ℕ+ →* Circle) :
    samePhaseSector χ ψ ↔ Summable (fun p => primeMismatch (ψ/χ) p * primeWeight 1 p) := by
  have h (p : Nat.Primes) : ‖(ψ (p : ℕ+) : ℂ)-(χ (p : ℕ+) : ℂ)‖^2 / (p : ℕ) =
      2*(primeMismatch (ψ/χ) p * primeWeight 1 p) := by
    rw [chord_eq, primeMismatch, MonoidHom.div_apply, primeWeight_one, div_eq_mul_inv, mul_assoc]
  change Summable _ ↔ _
  constructor
  · intro hs
    exact (hs.mul_left (2:ℝ)⁻¹).congr (fun p => by rw [h, inv_mul_cancel_left₀ (by norm_num : (2:ℝ) ≠ 0)])
  · intro hs
    exact (hs.mul_left 2).congr fun p => (h p).symm

theorem samePhaseSector_refl (χ : ℕ+ →* Circle) : samePhaseSector χ χ := by
  simp [samePhaseSector]

theorem samePhaseSector_symm (χ ψ : ℕ+ →* Circle) :
    samePhaseSector χ ψ ↔ samePhaseSector ψ χ := by
  unfold samePhaseSector
  simp only [norm_sub_rev (χ _ : ℂ) (ψ _ : ℂ)]

theorem samePhaseSector_trans {χ ψ η : ℕ+ →* Circle} (h₁ : samePhaseSector χ ψ)
    (h₂ : samePhaseSector ψ η) : samePhaseSector χ η := by
  unfold samePhaseSector at *
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ ((h₂.add h₁).mul_left 2)
  intro p
  let z := (η (p : ℕ+) : ℂ)
  let w := (ψ (p : ℕ+) : ℂ)
  let v := (χ (p : ℕ+) : ℂ)
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le_norm_sub_add_norm_sub z w v) 2
  have hh : ‖z-v‖^2 ≤ 2*(‖z-w‖^2 + ‖w-v‖^2) := by
    nlinarith only [h, sq_nonneg (‖z-w‖-‖w-v‖)]
  change ‖z-v‖^2 / _ ≤ 2*(‖z-w‖^2 / _ + ‖w-v‖^2 / _)
  rw [← add_div, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hh (Nat.cast_nonneg _)

/-- Thermal damping of a nonnegative bounded prime series is summable at every trace temperature. -/
private theorem prime_mass_summable {a : Nat.Primes → ℝ} {C : ℝ}
    (ha : ∀ p, 0 ≤ a p ∧ a p ≤ C) (β : TraceTemperature) :
    Summable (fun p => a p * primeWeight β.val p) :=
  Summable.of_nonneg_of_le (fun p => mul_nonneg (ha p).1 (Real.exp_pos _).le)
    (fun p => mul_le_mul_of_nonneg_right (ha p).2 (Real.exp_pos _).le)
    ((primeWeight_summable β).mul_left C)

/-- Finite partial sums detect divergence at the boundary without exchanging divergent sums. -/
theorem prime_mass_escape {a : Nat.Primes → ℝ} {C : ℝ} (ha : ∀ p, 0 ≤ a p ∧ a p ≤ C)
    (hdiv : ¬ Summable (fun p => a p * primeWeight 1 p)) :
    Tendsto (fun β : TraceTemperature => ∑' p, a p * primeWeight β.val p) atPartitionPole atTop := by
  apply tendsto_atTop.mpr
  intro M
  have hn (p) : 0 ≤ a p * primeWeight 1 p := mul_nonneg (ha p).1 (Real.exp_pos _).le
  obtain ⟨S,hS⟩ : ∃ S : Finset Nat.Primes, M < ∑ p ∈ S, a p * primeWeight 1 p := by
    by_contra! hb
    exact hdiv (summable_of_sum_le hn hb)
  have ht := tendsto_finsetSum S (fun p _ => (primeWeight_limit p).const_mul (a p))
  filter_upwards [ht.eventually_const_lt hS] with β hβ
  exact hβ.le.trans ((prime_mass_summable ha β).sum_le_tsum S
    (fun p _ => mul_nonneg (ha p).1 (Real.exp_pos _).le))

private theorem mismatch_limit {ρ : ℕ+ →* Circle}
    (h : Summable (fun p => primeMismatch ρ p * primeWeight 1 p)) :
    Tendsto (fun β : TraceTemperature => dampedMismatch ρ β.val) atPartitionPole
      (𝓝 (dampedMismatch ρ 1)) := by
  apply tendsto_tsum_of_dominated_convergence h (fun p => (primeWeight_limit p).const_mul _)
  exact Eventually.of_forall fun β p => by
    have hw : 0 ≤ primeWeight β.val p := (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (primeMismatch_bounds ρ p).1 hw)]
    exact mul_le_mul_of_nonneg_left (primeWeight_le_one_weight β p) (primeMismatch_bounds ρ p).1

/-- The prime angle removed from a complex overlap has unit modulus. -/
def driftPhase (ρ : ℕ+ →* Circle) (β : TraceTemperature) : ℂ :=
  Complex.exp ((primeDrift ρ β : ℂ)*Complex.I)

theorem norm_driftPhase (ρ : ℕ+ →* Circle) (β : TraceTemperature) : ‖driftPhase ρ β‖ = 1 := by
  simp [driftPhase, Complex.norm_exp]

private theorem corrected_eq (χ ψ : ℕ+ →* Circle) (β : TraceTemperature) :
    phaseOverlap χ ψ β / driftPhase (ψ/χ) β =
      (Real.exp (-dampedMismatch (ψ/χ) β.val) : ℝ) * Complex.exp (overlapRemainder (ψ/χ) β.val) := by
  rw [phaseOverlap_logarithm, driftPhase, ← Complex.exp_sub, Complex.ofReal_exp, ← Complex.exp_add,
    Complex.ofReal_neg]
  congr 1
  ring

/-- Complex boundary amplitude in the frame rotating with the measured prime angle. -/
def sectorAmplitude (χ ψ : ℕ+ →* Circle) : ℂ :=
  if samePhaseSector χ ψ then
    (Real.exp (-dampedMismatch (ψ/χ) 1) : ℝ) * Complex.exp (overlapRemainder (ψ/χ) 1) else 0

/-- The complex overlap always converges after its first-order Euler angle is removed. -/
theorem corrected_phaseOverlap_limit (χ ψ : ℕ+ →* Circle) :
    Tendsto (fun β => phaseOverlap χ ψ β / driftPhase (ψ/χ) β) atPartitionPole
      (𝓝 (sectorAmplitude χ ψ)) := by
  let ρ := ψ/χ
  have hr := Complex.continuous_exp.continuousAt.tendsto.comp (overlapRemainder_limit ρ)
  by_cases h : samePhaseSector χ ψ
  · rw [sectorAmplitude, if_pos h]
    have he := Real.continuous_exp.continuousAt.tendsto.comp
      (mismatch_limit ((samePhaseSector_iff_mismatch χ ψ).mp h)).neg
    exact (((Complex.continuous_ofReal.tendsto _).comp he).mul hr).congr
      (fun β => (corrected_eq χ ψ β).symm)
  · rw [sectorAmplitude, if_neg h]
    have hd := prime_mass_escape (primeMismatch_bounds ρ) (fun hs => h ((samePhaseSector_iff_mismatch χ ψ).mpr hs))
    have he := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hd)
    have hz := ((Complex.continuous_ofReal.tendsto _).comp he).mul hr
    rw [Complex.ofReal_zero, zero_mul] at hz
    exact hz.congr (fun β => (corrected_eq χ ψ β).symm)

theorem phaseOverlap_norm_limit (χ ψ : ℕ+ →* Circle) :
    Tendsto (fun β => ‖phaseOverlap χ ψ β‖) atPartitionPole (𝓝 ‖sectorAmplitude χ ψ‖) := by
  simpa only [norm_div, norm_driftPhase, div_one] using (corrected_phaseOverlap_limit χ ψ).norm

theorem sectorAmplitude_ne_zero_iff (χ ψ : ℕ+ →* Circle) :
    sectorAmplitude χ ψ ≠ 0 ↔ samePhaseSector χ ψ := by
  by_cases h : samePhaseSector χ ψ
  · rw [sectorAmplitude, if_pos h]
    exact iff_of_true (mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne') (Complex.exp_ne_zero _)) h
  · simp [sectorAmplitude,h]

/-- Two coherent states become orthogonal exactly when their harmonic-prime squared distance diverges. -/
theorem phaseOverlap_zero_iff (χ ψ : ℕ+ →* Circle) :
    Tendsto (phaseOverlap χ ψ) atPartitionPole (𝓝 0) ↔ ¬samePhaseSector χ ψ := by
  rw [tendsto_zero_iff_norm_tendsto_zero, ← sectorAmplitude_ne_zero_iff, not_not]
  constructor
  · intro h
    exact norm_eq_zero.mp (tendsto_nhds_unique (phaseOverlap_norm_limit χ ψ) h)
  · intro h
    simpa only [h, norm_zero] using phaseOverlap_norm_limit χ ψ

/-- Inside a sector, convergence of the observable complex phase is equivalent to convergence
of the damped first-order prime phase. -/
theorem phaseOverlap_nonzero_limit_iff (χ ψ : ℕ+ →* Circle) :
    (∃ z : ℂ, z ≠ 0 ∧ Tendsto (phaseOverlap χ ψ) atPartitionPole (𝓝 z)) ↔
      samePhaseSector χ ψ ∧ ∃ u : ℂ, Tendsto (driftPhase (ψ/χ)) atPartitionPole (𝓝 u) := by
  let ρ := ψ/χ
  have hc := corrected_phaseOverlap_limit χ ψ
  have hne (β) : driftPhase ρ β ≠ 0 := Complex.exp_ne_zero _
  constructor
  · rintro ⟨z,hz,h⟩
    have hs : samePhaseSector χ ψ := by
      by_contra hn
      exact hz (tendsto_nhds_unique h ((phaseOverlap_zero_iff χ ψ).mpr hn))
    have hb := (sectorAmplitude_ne_zero_iff χ ψ).mpr hs
    refine ⟨hs, z/sectorAmplitude χ ψ, (h.div hc hb).congr (fun β => ?_)⟩
    have hov : phaseOverlap χ ψ β ≠ 0 := by rw [phaseOverlap_logarithm]; exact Complex.exp_ne_zero _
    change phaseOverlap χ ψ β / (phaseOverlap χ ψ β / driftPhase ρ β) = driftPhase ρ β
    field_simp [hov, hne]
  · rintro ⟨hs,u,hu⟩
    have hn : ‖u‖ = 1 := tendsto_nhds_unique hu.norm (tendsto_const_nhds.congr (fun β => (norm_driftPhase ρ β).symm))
    have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (hn.trans_ne one_ne_zero)
    refine ⟨sectorAmplitude χ ψ * u, mul_ne_zero ((sectorAmplitude_ne_zero_iff χ ψ).mpr hs) hu0,
      (hc.mul hu).congr (fun β => ?_)⟩
    exact div_mul_cancel₀ _ (hne β)

#print axioms samePhaseSector_iff_mismatch
#print axioms samePhaseSector_trans
#print axioms corrected_phaseOverlap_limit
#print axioms phaseOverlap_norm_limit
#print axioms phaseOverlap_zero_iff
#print axioms phaseOverlap_nonzero_limit_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
