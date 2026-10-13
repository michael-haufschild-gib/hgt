import GaloisForLFunctions.HTGeometry.TwoBaseCircleQuadrature
import GaloisForLFunctions.RHTower.WeilLagComplexWolffSummable

/-!
# Two incommensurable lag progressions can both vanish at a non-attained top

Let `φ` be the golden ratio and `ℓ > log 100`. There is a countable, injective, locally finite
configuration `ρ_i` in the strip `½ < Re ρ < 1` whose largest real part is not attained, with
weights `c_i` in the sector `|c_i| ≤ 2 Re c_i`, arguments tending to `0`, one weight equal to `1`,
and `Σ_i |c_i|^p < ∞` for every `p > 0`. Both lag progressions vanish:
`Σ_i c_i e^{mℓ(ρ_i − ½)} = 0` and `Σ_i c_i e^{mφℓ(ρ_i − ½)} = 0` for every `m ≥ 1`
(`exists_two_base_lag_configuration_vanishing`).

The mirror terms `Σ_i c_i e^{−mℓ(ρ_i − ½)}` are bounded by `Σ_i |c_i|`
(`norm_tsum_mirror_le`). So after closing the configuration under `ρ ↦ ρ̄` (weight `c̄`) and
`ρ ↦ 1 − ρ̄`, both two-sided sample sequences
`m ↦ 2 Re Σ_i c_i e^{mℓ(ρ_i − ½)} + 2 Re Σ_i c_i e^{−mℓ(ρ_i − ½)}`, `ℓ ∈ {ℓ, φℓ}`, stay bounded
by `2 Σ|c_i|`. Hence two incommensurable spacings with two-sided bounded lag samples do not force
the zeros onto the line on zero-side grounds, even for sector-positive, `p`-summable weights.

**Proof.** Rescale the two-base circle quadrature
(`TwoBaseQuadrature.exists_two_base_sector_configuration`) by `ρ = ½ + z/ℓ`.
-/

open Complex Set

namespace RHTower

noncomputable section

local notation "g" => Real.goldenRatio

/-- **Two incommensurable lag progressions vanishing at a non-attained top.** -/
theorem exists_two_base_lag_configuration_vanishing {ℓ : ℝ} (hℓ : Real.log 100 < ℓ) :
    ∃ (ι : Type) (_ : Countable ι) (ρ : ι → ℂ) (c : ι → ℂ), Function.Injective ρ ∧
      (∀ i, 1 / 2 < (ρ i).re ∧ (ρ i).re < 1) ∧ (∀ i, ∃ j, (ρ i).re < (ρ j).re) ∧
      (∀ T : ℝ, {i | |(ρ i).im| ≤ T}.Finite) ∧ (∃ i, c i = 1) ∧
      (∀ i, ‖c i‖ ≤ 2 * (c i).re) ∧ (∀ ε : ℝ, 0 < ε → {i | ε * (c i).re < |(c i).im|}.Finite) ∧
      (∀ p : ℝ, 0 < p → Summable fun i => ‖c i‖ ^ p) ∧
      ∀ m : ℕ, 1 ≤ m →
        HasSum (fun i => c i * Complex.exp (((m : ℝ) * ℓ : ℝ) * (ρ i - 1 / 2))) 0 ∧
        HasSum (fun i => c i * Complex.exp (((m : ℝ) * (g * ℓ) : ℝ) * (ρ i - 1 / 2))) 0 := by
  obtain ⟨ι, hι, z, c, hinj, hre, htop, hfin, hc1, hsec, harg, hp, hmom⟩ :=
    GaloisForLFunctions.HTGeometry.TwoBaseQuadrature.exists_two_base_sector_configuration
  have hℓ0 : 0 < ℓ := lt_trans (Real.log_pos (by norm_num)) hℓ
  have hℓc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ0.ne'
  have hlog100 : Real.log 100 = 2 * Real.log 10 := by
    rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.log_pow]; norm_num
  set ρ : ι → ℂ := fun i => 1 / 2 + z i / ℓ with hρ
  have hsub : ∀ i, ρ i - 1 / 2 = z i / ℓ := fun i => by rw [hρ]; ring
  have hreρ : ∀ i, (ρ i).re = 1 / 2 + (z i).re / ℓ := fun i => by
    rw [hρ]; simp [Complex.div_ofReal_re]
  have himρ : ∀ i, (ρ i).im = (z i).im / ℓ := fun i => by
    rw [hρ]; simp [Complex.div_ofReal_im]
  refine ⟨ι, hι, ρ, c, ?_, ?_, ?_, ?_, hc1, hsec, harg, hp, fun m hm => ⟨?_, ?_⟩⟩
  · intro a b hab
    apply hinj
    have h1 := hsub a
    have h2 := hsub b
    rw [hab] at h1
    have : z a / ℓ = z b / ℓ := h1.symm.trans h2
    exact (div_left_inj' hℓc).mp this
  · intro i
    rw [hreρ]
    have h1 := (hre i).1
    have h2 := (hre i).2
    have hl : 0 < Real.log (5 / 4) := Real.log_pos (by norm_num)
    constructor
    · have : 0 < (z i).re / ℓ := div_pos (by linarith) hℓ0
      linarith
    · have : (z i).re / ℓ < 1 / 2 := by rw [div_lt_iff₀ hℓ0]; linarith
      linarith
  · intro i
    obtain ⟨j, hj⟩ := htop i
    refine ⟨j, ?_⟩
    rw [hreρ, hreρ]
    have := div_lt_div_of_pos_right hj hℓ0
    linarith
  · intro T
    refine (hfin (T * ℓ)).subset fun i hi => ?_
    simp only [mem_setOf_eq] at hi ⊢
    rw [himρ, abs_div, abs_of_pos hℓ0, div_le_iff₀ hℓ0] at hi
    exact hi
  · refine (hmom m hm).1.congr_fun fun i => ?_
    rw [hsub]
    congr 2
    push_cast
    field_simp
  · refine (hmom m hm).2.congr_fun fun i => ?_
    rw [hsub]
    congr 2
    push_cast
    field_simp

/-- **The mirror samples are bounded.** If `Re x_i ≥ 0` and `ℓ ≥ 0`, then
`|Σ_i c_i e^{−mℓ x_i}| ≤ Σ_i |c_i|`. -/
theorem norm_tsum_mirror_le {ι : Type*} {x c : ι → ℂ} (hx : ∀ i, 0 ≤ (x i).re)
    (hc : Summable fun i => ‖c i‖) {L : ℝ} (hL : 0 ≤ L) :
    ‖∑' i, c i * Complex.exp (-(L : ℂ) * x i)‖ ≤ ∑' i, ‖c i‖ := by
  have hb : ∀ i, ‖c i * Complex.exp (-(L : ℂ) * x i)‖ ≤ ‖c i‖ := by
    intro i
    rw [norm_mul, Complex.norm_exp]
    have : (-(L : ℂ) * x i).re = -(L * (x i).re) := by simp
    rw [this]
    have h1 : Real.exp (-(L * (x i).re)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hx i])
    nlinarith [norm_nonneg (c i)]
  have hs : Summable fun i => ‖c i * Complex.exp (-(L : ℂ) * x i)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hc
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hb hc)

end

end RHTower
