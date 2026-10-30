import GaloisForLFunctions.CompletedArithmeticForms.WeilGreenModes
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# The exact heat domain of the completed conductor spectrum

Bounded shell completion preserves the logarithmic lower envelope. Prime
conductors supply a matching upper envelope and force divergence at the
critical inverse temperature. Every source correction and the pole remain
in the conductor energies.
-/

noncomputable section

open Finset MeasureTheory Filter Topology

namespace GaloisForLFunctions.CompletedArithmeticForms

open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis ArithmeticIntersectionTheory

/-- A conductor-independent bound for the literal shell correction. -/
def completedShellCorrectionBudget (φ : ℝ → ℝ) (c : ℝ) : ℝ :=
  2 / |∫ u, φ u ^ 2| *
    ∑ h ∈ Finset.Ico 1 ⌈c⌉₊, |∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u|

/-- Shell completion retains a logarithmic lower envelope at every positive conductor. -/
theorem completedConductorEnergy_log_lower (φ : ℝ → ℝ) {c : ℝ} (hc : 0 < c)
    {m : ℕ} (hm : 0 < m) :
    Real.log m + completeWeilSelfFinitePart φ c - completedShellCorrectionBudget φ c ≤
      completedConductorEnergy φ c m := by
  have hs := (abs_le.mp (abs_shellCorrection_le φ c hm)).2
  have ht := SelectiveMultiscaleArithmeticPositivity.tameDifferent_nonneg m
  have hp : 0 ≤ if m = 1 then completeWeilPoleShift φ c else 0 := by
    split_ifs
    · exact completeWeilPoleShift_nonneg φ hc.le
    · exact le_rfl
  rw [completedConductorEnergy_eq_sub_shellCorrection hc hm,
    completeWeilAdjunctionEnergy, ramanujanAdjunctionEnergy]
  change shellCorrection φ c m ≤ completedShellCorrectionBudget φ c at hs
  linarith only [hs, ht, hp]

/-- Prime conductors retain a matching logarithmic ceiling with an explicit constant. -/
theorem completedConductorEnergy_prime_log_upper (φ : ℝ → ℝ) {c : ℝ} (hc : 0 < c)
    {p : ℕ} (hp : p.Prime) :
    completedConductorEnergy φ c p ≤ Real.log p + completeWeilSelfFinitePart φ c +
      completedShellCorrectionBudget φ c + 1 := by
  have hs := (abs_le.mp (abs_shellCorrection_le φ c hp.pos)).1
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have ht : tameDifferent p ≤ 1 := by
    have he := tameDifferent_prime_pow hp (show (1 : ℕ) ≠ 0 by decide)
    simp only [pow_one] at he
    rw [he, div_le_iff₀ (sub_pos.mpr hpR), one_mul]
    exact Real.log_le_sub_one_of_pos (zero_lt_one.trans hpR)
  rw [completedConductorEnergy_eq_sub_shellCorrection hc hp.pos,
    completeWeilAdjunctionEnergy, ramanujanAdjunctionEnergy, if_neg hp.ne_one]
  change -completedShellCorrectionBudget φ c ≤ shellCorrection φ c p at hs
  linarith only [hs, ht]

/-- The heat weights of the completed conductor model, indexed over all positive conductors. -/
def completedConductorHeatWeight (φ : ℝ → ℝ) (c β : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-β * completedConductorEnergy φ c (n + 1))

/-- The complete conductor energies escape to infinity with the conductor itself. -/
theorem tendsto_completedConductorEnergy_atTop (φ : ℝ → ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => completedConductorEnergy φ c (n + 1)) atTop atTop := by
  have hlog : Tendsto (fun n : ℕ => Real.log ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  refine Filter.tendsto_atTop.2 fun T => ?_
  filter_upwards [hlog.eventually (eventually_ge_atTop
    (T - completeWeilSelfFinitePart φ c + completedShellCorrectionBudget φ c))] with n hn
  have h := completedConductorEnergy_log_lower φ hc (Nat.succ_pos n)
  linarith only [h, hn]

/-- Reciprocal completed energies vanish, with no conductor cutoff assumption. -/
theorem tendsto_completedConductorEnergy_inv_zero (φ : ℝ → ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => (completedConductorEnergy φ c (n + 1))⁻¹) atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp (tendsto_completedConductorEnergy_atTop φ hc)

/-- The complete conductor heat series converges above the exact logarithmic threshold. -/
theorem summable_completedConductorHeatWeight (φ : ℝ → ℝ) {c β : ℝ}
    (hc : 0 < c) (hβ : 1 < β) :
    Summable (completedConductorHeatWeight φ c β) := by
  let B := completeWeilSelfFinitePart φ c - completedShellCorrectionBudget φ c
  have hs : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-β)) :=
    (Real.summable_nat_rpow.mpr (by linarith only [hβ])).comp_injective Nat.add_right_cancel
  apply (hs.mul_left (Real.exp (-β * B))).of_nonneg_of_le
    (fun _ => (Real.exp_pos _).le)
  intro n
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hE := completedConductorEnergy_log_lower φ hc (Nat.succ_pos n)
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  have hb : -β * completedConductorEnergy φ c (n + 1) ≤
      -β * B + Real.log ((n + 1 : ℕ) : ℝ) * (-β) := by
    have h := mul_le_mul_of_nonneg_left hE hβ0.le
    dsimp only [B]
    nlinarith only [h]
  unfold completedConductorHeatWeight
  rw [Real.rpow_def_of_pos hn, ← Real.exp_add]
  exact Real.exp_le_exp.mpr hb

/-- Finite shell completion preserves the exact heat threshold at every positive overlap. -/
theorem summable_completedConductorHeatWeight_iff (φ : ℝ → ℝ) {c β : ℝ} (hc : 0 < c) :
    Summable (completedConductorHeatWeight φ c β) ↔ 1 < β := by
  refine ⟨?_, summable_completedConductorHeatWeight φ hc⟩
  intro hsum
  by_contra hβ
  have hβle : β ≤ 1 := le_of_not_gt hβ
  have hβ0 : 0 < β := by
    by_contra h
    have hβneg : 0 ≤ -β := neg_nonneg.mpr (le_of_not_gt h)
    have hsmall := hsum.tendsto_atTop_zero.eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    have hlarge := (tendsto_completedConductorEnergy_atTop φ hc).eventually_ge_atTop 0
    obtain ⟨n, hn, hEn⟩ := (hsmall.and hlarge).exists
    have hweight : 1 ≤ completedConductorHeatWeight φ c β n :=
      Real.one_le_exp_iff.mpr (mul_nonneg hβneg hEn)
    linarith only [hn, hweight]
  let U := completeWeilSelfFinitePart φ c + completedShellCorrectionBudget φ c + 1
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ) - 1) := by
    intro p q he
    apply Subtype.ext
    have hp := p.property.two_le
    have hq := q.property.two_le
    omega
  have hs : Summable (fun p : Nat.Primes =>
      Real.exp (-β * completedConductorEnergy φ c (p : ℕ))) := by
    have h := hsum.comp_injective hinj
    refine h.congr fun p => ?_
    simp only [completedConductorHeatWeight, Nat.sub_add_cancel p.property.one_le]
  apply Nat.Primes.not_summable_one_div
  apply (hs.mul_left (Real.exp (β * U))).of_nonneg_of_le (fun _ => by positivity)
  intro p
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
  have hu := completedConductorEnergy_prime_log_upper φ hc p.property
  have hb : -Real.log (p : ℕ) ≤ β * U + -β * completedConductorEnergy φ c (p : ℕ) := by
    have h := mul_le_mul_of_nonneg_left hu hβ0.le
    have hlog := mul_le_mul_of_nonneg_right hβle (Real.log_natCast_nonneg (p : ℕ))
    dsimp only [U]
    nlinarith only [h, hlog]
  have h := Real.exp_le_exp.mpr hb
  simpa only [Real.exp_neg, Real.exp_log hp, one_div, Real.exp_add] using h

/-- The literal tilted-spline conductor spectrum has the sharp heat threshold `β = 1`. -/
theorem summable_tiltedWeil_conductor_heat_iff {c β : ℝ} (hc : 0 < c) :
    Summable (completedConductorHeatWeight tiltedUnitSpline c β) ↔ 1 < β :=
  summable_completedConductorHeatWeight_iff tiltedUnitSpline hc

/-- No positive integer power of the complete conductor Green weights is summable. -/
theorem not_summable_tiltedWeil_inverse_energy_pow {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ¬ Summable (fun n : ℕ =>
      (completedConductorEnergy tiltedUnitSpline c (n + 1))⁻¹ ^ k) := by
  intro hs
  have hheat : Summable (completedConductorHeatWeight tiltedUnitSpline c 1) := by
    apply (hs.mul_left (k.factorial : ℝ)).of_nonneg_of_le
      (fun _ => (Real.exp_pos _).le)
    intro n
    let E := completedConductorEnergy tiltedUnitSpline c (n + 1)
    have hE : 0 < E := tiltedWeilConductorEnergy_pos hc (Nat.succ_pos n)
    have hf0 : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    have h := (div_le_iff₀ hf0).mp (Real.pow_div_factorial_le_exp E hE.le k)
    have hpay : Real.exp (-E) * E ^ k ≤ (k.factorial : ℝ) := by
      calc
        _ ≤ Real.exp (-E) * (Real.exp E * k.factorial) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
        _ = _ := by
          rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    change Real.exp (-(1 : ℝ) * E) ≤ _
    rw [neg_one_mul, ← inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hE k)]
    exact hpay
  exact (lt_irrefl (1 : ℝ)) ((summable_tiltedWeil_conductor_heat_iff hc).mp hheat)

#print axioms completedConductorEnergy_log_lower
#print axioms completedConductorEnergy_prime_log_upper
#print axioms tendsto_completedConductorEnergy_inv_zero
#print axioms summable_completedConductorHeatWeight_iff
#print axioms summable_tiltedWeil_conductor_heat_iff
#print axioms not_summable_tiltedWeil_inverse_energy_pow

end GaloisForLFunctions.CompletedArithmeticForms
