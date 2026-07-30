/-
The dyadic caustic assembly, part III: THE CAPSTONE (doc 87 App B).

`annulus_lintegral_le`: the third-phase integral of the radial-band
measure is at most

  J · (shell constant) + (core constant) + (core constant) + (mid constant),

all explicit.  `J` is free, constrained only by the cover hypothesis
`G/3 < 2^J σ0`; with `σ0` at its minimal admissible scale (`~ r`) the
consumer picks `J ~ log(1/r)` and reads off the `r·log(1/r)` law for the
annulus, hence `r²·log(1/r)` for the three-phase sublevel through
`three_phase_sublevel`: the (L3) base case.
-/
import Mathlib
import GaloisForLFunctions.RHTower.RouteBCausticSum

namespace RHTower
namespace Sublevel

open MeasureTheory

private theorem coreSetM_volume_le {B C c : ℂ} {ρ r σ0 : ℝ}
    (hB : B ≠ 0) (hC : C ≠ 0) (hc : c ≠ 0) (hr0 : 0 < r) :
    volume (coreSetM c C B ρ r σ0)
      ≤ ENNReal.ofReal (2 * Real.pi
          * Real.sqrt (2 * ((σ0 + r * (2 * (ρ + ‖B‖) + r))
            / (2 * (‖c‖ * ‖C‖))))) := by
  have hb0 : (0 : ℝ) < ‖B‖ := norm_pos_iff.mpr hB
  have hsub : coreSetM c C B ρ r σ0
      ⊆ {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
          ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2
            ∈ Set.Icc ((ρ - ‖B‖ - r) ^ 2) ((ρ - ‖B‖) ^ 2 + σ0)} :=
    fun η h => ⟨h.1, h.2.1, h.2.2⟩
  refine le_trans (measure_mono hsub)
    (le_trans (center_shell_measure hc hC)
      (ENNReal.ofReal_le_ofReal ?_))
  have hw : (ρ - ‖B‖) ^ 2 + σ0 - (ρ - ‖B‖ - r) ^ 2
      ≤ σ0 + r * (2 * (ρ + ‖B‖) + r) := by nlinarith [hb0, hr0]
  have hcc : (0 : ℝ) < ‖c‖ * ‖C‖ :=
    mul_pos (norm_pos_iff.mpr hc) (norm_pos_iff.mpr hC)
  gcongr

private theorem coreSetP_volume_le {B C c : ℂ} {ρ r σ0 : ℝ}
    (hC : C ≠ 0) (hc : c ≠ 0) :
    volume (coreSetP c C B ρ r σ0)
      ≤ ENNReal.ofReal (2 * Real.pi
          * Real.sqrt (2 * ((σ0 + r * (2 * (ρ + ‖B‖) + r))
            / (2 * (‖c‖ * ‖C‖))))) := by
  have hsub : coreSetP c C B ρ r σ0
      ⊆ {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
          ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2
            ∈ Set.Icc ((ρ + ‖B‖) ^ 2 - σ0) ((ρ + ‖B‖ + r) ^ 2)} :=
    fun η h => ⟨h.1, h.2.1, h.2.2⟩
  refine le_trans (measure_mono hsub)
    (le_trans (center_shell_measure hc hC)
      (ENNReal.ofReal_le_ofReal ?_))
  have hw : (ρ + ‖B‖ + r) ^ 2 - ((ρ + ‖B‖) ^ 2 - σ0)
      ≤ σ0 + r * (2 * (ρ + ‖B‖) + r) := by nlinarith
  have hcc : (0 : ℝ) < ‖c‖ * ‖C‖ :=
    mul_pos (norm_pos_iff.mpr hc) (norm_pos_iff.mpr hC)
  gcongr

theorem annulus_lintegral_le {B C c : ℂ} {ρ r σ0 : ℝ} {J : ℕ}
    (hB : B ≠ 0) (hC : C ≠ 0) (hc : c ≠ 0) (hρB : ‖B‖ < ρ) (hr0 : 0 < r)
    (hr2 : 2 * r ≤ ρ - ‖B‖) (hσ0 : 0 < σ0)
    (hσ0G : σ0 ≤ ((ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2) / 3)
    (hJ : ((ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2) / 3 < 2 ^ J * σ0)
    (hHσ0 : 2 * (r * (2 * ρ + r) / ((ρ - ‖B‖) * ‖B‖))
        ≤ σ0 * causticKappa ρ ‖B‖) :
    ∫⁻ η in Set.Icc (0 : ℝ) (2 * Real.pi),
        volume {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
          |‖c + C * Complex.exp ((η : ℂ) * Complex.I)
            + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ρ| ≤ r}
      ≤ J • ENNReal.ofReal (8 * Real.pi ^ 2
            * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
            * (Real.sqrt (2 / (causticKappa ρ ‖B‖ * (‖c‖ * ‖C‖)))
              + Real.sqrt 2))
        + ENNReal.ofReal ((2 * Real.pi
            * Real.sqrt (2 * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))))
            * (2 * Real.pi * Real.sqrt (2 * ((σ0 + r * (2 * (ρ + ‖B‖) + r))
              / (2 * (‖c‖ * ‖C‖))))))
        + ENNReal.ofReal ((2 * Real.pi
            * Real.sqrt (2 * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))))
            * (2 * Real.pi * Real.sqrt (2 * ((σ0 + r * (2 * (ρ + ‖B‖) + r))
              / (2 * (‖c‖ * ‖C‖))))))
        + ENNReal.ofReal (2 * Real.pi * (2 * Real.pi
            * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
            / Real.sqrt (min (((ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2) / 3
                * causticKappa ρ ‖B‖ / 2) (1 / 2)))) := by
  classical
  have hb0 : (0 : ℝ) < ‖B‖ := norm_pos_iff.mpr hB
  have hρ0 : (0 : ℝ) < ρ := lt_of_le_of_lt (norm_nonneg B) hρB
  have hxmin : (0 : ℝ) < (ρ - ‖B‖) / 2 := by linarith
  have hκ : (0 : ℝ) < causticKappa ρ ‖B‖ := by
    rw [causticKappa]
    have hGpos : (0 : ℝ) < (ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2 := by nlinarith
    have hpb : (0 : ℝ) < ρ + ‖B‖ := by linarith
    positivity
  have hG3 : (0 : ℝ) < ((ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2) / 3 := by nlinarith
  have hHbar : ∀ η : ℝ, (ρ - ‖B‖) / 2
        ≤ ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ →
      bandHalf (c + C * Complex.exp ((η : ℂ) * Complex.I)) B ρ r
        ≤ r * (2 * ρ + r) / ((ρ - ‖B‖) * ‖B‖) := by
    intro η hx
    rw [bandHalf_def]
    have hnum : (0 : ℝ) ≤ r * (2 * ρ + r) := by positivity
    have heq : (ρ - ‖B‖) * ‖B‖ = 2 * ((ρ - ‖B‖) / 2 * ‖B‖) := by ring
    rw [heq]
    apply div_le_div_of_nonneg_left hnum (by positivity)
    have hmm := mul_le_mul_of_nonneg_right hx (norm_nonneg B)
    nlinarith [hmm]
  have hfloor : ∀ η : ℝ, ∀ a : ℝ, 0 ≤ a →
      a ^ 2 ≤ ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 →
      a ≤ ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ := by
    intro η a ha h
    have h1 := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_sq ha, Real.sqrt_sq (norm_nonneg _)] at h1
  have hpt : ∀ η ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      volume {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
          |‖c + C * Complex.exp ((η : ℂ) * Complex.I)
            + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ρ| ≤ r}
        ≤ (∑ j ∈ Finset.range J,
            ((shellSetP c C B ρ (2 ^ j * σ0)).indicator
              (fun _ => ENNReal.ofReal (2 * Real.pi
                * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
                / Real.sqrt (min (2 ^ j * σ0 * causticKappa ρ ‖B‖ / 2)
                  (1 / 2)))) η
            + (shellSetM c C B ρ (2 ^ j * σ0)).indicator
              (fun _ => ENNReal.ofReal (2 * Real.pi
                * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
                / Real.sqrt (min (2 ^ j * σ0 * causticKappa ρ ‖B‖ / 2)
                  (1 / 2)))) η))
          + (coreSetM c C B ρ r σ0).indicator
              (fun _ => ENNReal.ofReal (2 * Real.pi
                * Real.sqrt (2 * (r * (2 * ρ + r)
                  / ((ρ - ‖B‖) / 2 * ‖B‖))))) η
          + (coreSetP c C B ρ r σ0).indicator
              (fun _ => ENNReal.ofReal (2 * Real.pi
                * Real.sqrt (2 * (r * (2 * ρ + r)
                  / ((ρ - ‖B‖) / 2 * ‖B‖))))) η
          + (midSet c C B ρ).indicator
              (fun _ => ENNReal.ofReal (2 * Real.pi
                * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
                / Real.sqrt (min (((ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2) / 3
                    * causticKappa ρ ‖B‖ / 2) (1 / 2)))) η := by
    intro η hη
    rcases annulus_cover (C := C) (c := c) hρB hr2 hσ0 hJ hη with
      h0 | hcm | hcp | hmid | ⟨j, hjJ, hsh⟩
    · rw [h0]
      exact bot_le
    · have hxm : (ρ - ‖B‖) / 2
          ≤ ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ :=
        le_trans (by linarith)
          (hfloor η (ρ - ‖B‖ - r) (by linarith) hcm.2.1)
      refine le_trans (vol_K_le_sqrt hB hρ0.le hr0.le hxmin hxm) ?_
      refine le_trans (le_of_eq (Set.indicator_of_mem hcm
        (fun _ => ENNReal.ofReal (2 * Real.pi
          * Real.sqrt (2 * (r * (2 * ρ + r)
            / ((ρ - ‖B‖) / 2 * ‖B‖)))))).symm) ?_
      exact le_trans le_add_self (le_trans le_self_add le_self_add)
    · have hy : (ρ - ‖B‖) ^ 2
          ≤ ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 := by
        have h1 := hcp.2.1
        nlinarith [hσ0G, hG3]
      have hxm : (ρ - ‖B‖) / 2
          ≤ ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ :=
        le_trans (by linarith) (hfloor η (ρ - ‖B‖) (by linarith) hy)
      refine le_trans (vol_K_le_sqrt hB hρ0.le hr0.le hxmin hxm) ?_
      refine le_trans (le_of_eq (Set.indicator_of_mem hcp
        (fun _ => ENNReal.ofReal (2 * Real.pi
          * Real.sqrt (2 * (r * (2 * ρ + r)
            / ((ρ - ‖B‖) / 2 * ‖B‖)))))).symm) ?_
      exact le_trans le_add_self le_self_add
    · have hy : (ρ - ‖B‖) ^ 2
          ≤ ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 := by
        have h1 := hmid.2.2
        nlinarith [hG3]
      have hxm : (ρ - ‖B‖) / 2
          ≤ ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ :=
        le_trans (by linarith) (hfloor η (ρ - ‖B‖) (by linarith) hy)
      have hHσmid : 2 * (r * (2 * ρ + r) / ((ρ - ‖B‖) * ‖B‖))
          ≤ (((ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2) / 3) * causticKappa ρ ‖B‖ :=
        le_trans hHσ0 (mul_le_mul_of_nonneg_right hσ0G hκ.le)
      refine le_trans (vol_K_le_shell hB hρ0.le hr0.le hG3 hxmin hxm
        (hHbar η hxm) hHσmid hmid.2.1 hmid.2.2) ?_
      have hconv : ENNReal.ofReal (2 * Real.pi * (r * (2 * ρ + r))
            / (Real.sqrt (min (((ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2) / 3
                * causticKappa ρ ‖B‖ / 2) (1 / 2))
              * ((ρ - ‖B‖) / 2 * ‖B‖)))
          = ENNReal.ofReal (2 * Real.pi
            * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
            / Real.sqrt (min (((ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2) / 3
                * causticKappa ρ ‖B‖ / 2) (1 / 2))) := by
        have hs0 : (0 : ℝ) < Real.sqrt (min (((ρ + ‖B‖) ^ 2
            - (ρ - ‖B‖) ^ 2) / 3 * causticKappa ρ ‖B‖ / 2) (1 / 2)) :=
          Real.sqrt_pos.mpr (lt_min (div_pos (mul_pos hG3 hκ) two_pos)
            (by norm_num))
        congr 1
        field_simp
      refine le_trans (le_of_eq hconv) ?_
      refine le_trans (le_of_eq (Set.indicator_of_mem hmid
        (fun _ => ENNReal.ofReal (2 * Real.pi
          * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
          / Real.sqrt (min (((ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2) / 3
              * causticKappa ρ ‖B‖ / 2) (1 / 2))))).symm) ?_
      exact le_add_self
    · have hσj : (0 : ℝ) < 2 ^ j * σ0 := by positivity
      have hHσj : 2 * (r * (2 * ρ + r) / ((ρ - ‖B‖) * ‖B‖))
          ≤ 2 ^ j * σ0 * causticKappa ρ ‖B‖ := by
        refine le_trans hHσ0 ?_
        have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
        have h2 : σ0 ≤ 2 ^ j * σ0 := by nlinarith
        exact mul_le_mul_of_nonneg_right h2 hκ.le
      have hconv : ENNReal.ofReal (2 * Real.pi * (r * (2 * ρ + r))
            / (Real.sqrt (min (2 ^ j * σ0 * causticKappa ρ ‖B‖ / 2)
                (1 / 2)) * ((ρ - ‖B‖) / 2 * ‖B‖)))
          = ENNReal.ofReal (2 * Real.pi
            * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
            / Real.sqrt (min (2 ^ j * σ0 * causticKappa ρ ‖B‖ / 2)
              (1 / 2))) := by
        have hs0 : (0 : ℝ) < Real.sqrt (min (2 ^ j * σ0
            * causticKappa ρ ‖B‖ / 2) (1 / 2)) :=
          Real.sqrt_pos.mpr (lt_min (div_pos (mul_pos hσj hκ) two_pos)
            (by norm_num))
        congr 1
        field_simp
      have htail : ((shellSetP c C B ρ (2 ^ j * σ0)).indicator
            (fun _ => ENNReal.ofReal (2 * Real.pi
              * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
              / Real.sqrt (min (2 ^ j * σ0 * causticKappa ρ ‖B‖ / 2)
                (1 / 2)))) η
          + (shellSetM c C B ρ (2 ^ j * σ0)).indicator
            (fun _ => ENNReal.ofReal (2 * Real.pi
              * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
              / Real.sqrt (min (2 ^ j * σ0 * causticKappa ρ ‖B‖ / 2)
                (1 / 2)))) η)
          ≤ (∑ j' ∈ Finset.range J,
            ((shellSetP c C B ρ (2 ^ j' * σ0)).indicator
              (fun _ => ENNReal.ofReal (2 * Real.pi
                * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
                / Real.sqrt (min (2 ^ j' * σ0 * causticKappa ρ ‖B‖ / 2)
                  (1 / 2)))) η
            + (shellSetM c C B ρ (2 ^ j' * σ0)).indicator
              (fun _ => ENNReal.ofReal (2 * Real.pi
                * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
                / Real.sqrt (min (2 ^ j' * σ0 * causticKappa ρ ‖B‖ / 2)
                  (1 / 2)))) η)) :=
        Finset.single_le_sum
          (f := fun j' => (shellSetP c C B ρ (2 ^ j' * σ0)).indicator
              (fun _ => ENNReal.ofReal (2 * Real.pi
                * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
                / Real.sqrt (min (2 ^ j' * σ0 * causticKappa ρ ‖B‖ / 2)
                  (1 / 2)))) η
            + (shellSetM c C B ρ (2 ^ j' * σ0)).indicator
              (fun _ => ENNReal.ofReal (2 * Real.pi
                * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
                / Real.sqrt (min (2 ^ j' * σ0 * causticKappa ρ ‖B‖ / 2)
                  (1 / 2)))) η)
          (fun i _ => bot_le) (Finset.mem_range.mpr hjJ)
      rcases hsh with hP | hP
      · have hy : (ρ - ‖B‖) ^ 2
            ≤ ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 := by
          have h1 := hP.2.2.2
          nlinarith [hσj]
        have hxm : (ρ - ‖B‖) / 2
            ≤ ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ :=
          le_trans (by linarith) (hfloor η (ρ - ‖B‖) (by linarith) hy)
        refine le_trans ?_ (le_trans htail
          (le_trans le_self_add (le_trans le_self_add le_self_add)))
        refine le_trans (le_trans (vol_K_le_shell hB hρ0.le hr0.le hσj
          hxmin hxm (hHbar η hxm) hHσj hP.2.1 hP.2.2.2)
          (le_of_eq hconv)) ?_
        refine le_trans (le_of_eq (Set.indicator_of_mem hP
          (fun _ => ENNReal.ofReal (2 * Real.pi
            * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
            / Real.sqrt (min (2 ^ j * σ0 * causticKappa ρ ‖B‖ / 2)
              (1 / 2))))).symm) ?_
        exact le_self_add
      · have hy : (ρ - ‖B‖) ^ 2
            ≤ ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 := by
          have h1 := hP.2.1
          nlinarith [hσj]
        have hxm : (ρ - ‖B‖) / 2
            ≤ ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ :=
          le_trans (by linarith) (hfloor η (ρ - ‖B‖) (by linarith) hy)
        refine le_trans ?_ (le_trans htail
          (le_trans le_self_add (le_trans le_self_add le_self_add)))
        refine le_trans (le_trans (vol_K_le_shell hB hρ0.le hr0.le hσj
          hxmin hxm (hHbar η hxm) hHσj hP.2.2.2 hP.2.1)
          (le_of_eq hconv)) ?_
        refine le_trans (le_of_eq (Set.indicator_of_mem hP
          (fun _ => ENNReal.ofReal (2 * Real.pi
            * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
            / Real.sqrt (min (2 ^ j * σ0 * causticKappa ρ ‖B‖ / 2)
              (1 / 2))))).symm) ?_
        exact le_add_self
  have hmP : ∀ j : ℕ, Measurable
      ((shellSetP c C B ρ (2 ^ j * σ0)).indicator
        (fun _ : ℝ => ENNReal.ofReal (2 * Real.pi
          * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
          / Real.sqrt (min (2 ^ j * σ0 * causticKappa ρ ‖B‖ / 2)
            (1 / 2))))) := fun j =>
    measurable_const.indicator (measurableSet_shellSetP c C B ρ _)
  have hmM : ∀ j : ℕ, Measurable
      ((shellSetM c C B ρ (2 ^ j * σ0)).indicator
        (fun _ : ℝ => ENNReal.ofReal (2 * Real.pi
          * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
          / Real.sqrt (min (2 ^ j * σ0 * causticKappa ρ ‖B‖ / 2)
            (1 / 2))))) := fun j =>
    measurable_const.indicator (measurableSet_shellSetM c C B ρ _)
  have hmS : Measurable (fun η => ∑ j ∈ Finset.range J,
      ((shellSetP c C B ρ (2 ^ j * σ0)).indicator
        (fun _ => ENNReal.ofReal (2 * Real.pi
          * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
          / Real.sqrt (min (2 ^ j * σ0 * causticKappa ρ ‖B‖ / 2)
            (1 / 2)))) η
      + (shellSetM c C B ρ (2 ^ j * σ0)).indicator
        (fun _ => ENNReal.ofReal (2 * Real.pi
          * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
          / Real.sqrt (min (2 ^ j * σ0 * causticKappa ρ ‖B‖ / 2)
            (1 / 2)))) η)) :=
    Finset.measurable_sum _ (fun j _ => ((hmP j).add (hmM j)))
  have hmCM : Measurable ((coreSetM c C B ρ r σ0).indicator
      (fun _ : ℝ => ENNReal.ofReal (2 * Real.pi
        * Real.sqrt (2 * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖)))))) :=
    measurable_const.indicator (measurableSet_coreSetM c C B ρ r σ0)
  have hmCP : Measurable ((coreSetP c C B ρ r σ0).indicator
      (fun _ : ℝ => ENNReal.ofReal (2 * Real.pi
        * Real.sqrt (2 * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖)))))) :=
    measurable_const.indicator (measurableSet_coreSetP c C B ρ r σ0)
  let shellTerm : ℕ → ℝ → ENNReal := fun j η =>
    (shellSetP c C B ρ (2 ^ j * σ0)).indicator
      (fun _ => ENNReal.ofReal (2 * Real.pi
        * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
        / Real.sqrt (min (2 ^ j * σ0 * causticKappa ρ ‖B‖ / 2)
          (1 / 2)))) η
    + (shellSetM c C B ρ (2 ^ j * σ0)).indicator
      (fun _ => ENNReal.ofReal (2 * Real.pi
        * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
        / Real.sqrt (min (2 ^ j * σ0 * causticKappa ρ ‖B‖ / 2)
          (1 / 2)))) η
  let shellBound : ℝ → ENNReal := fun η =>
    ∑ j ∈ Finset.range J, shellTerm j η
  let coreMBound : ℝ → ENNReal := (coreSetM c C B ρ r σ0).indicator
    (fun _ => ENNReal.ofReal (2 * Real.pi
      * Real.sqrt (2 * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖)))))
  let corePBound : ℝ → ENNReal := (coreSetP c C B ρ r σ0).indicator
    (fun _ => ENNReal.ofReal (2 * Real.pi
      * Real.sqrt (2 * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖)))))
  let midBound : ℝ → ENNReal := (midSet c C B ρ).indicator
    (fun _ => ENNReal.ofReal (2 * Real.pi
      * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
      / Real.sqrt (min (((ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2) / 3
          * causticKappa ρ ‖B‖ / 2) (1 / 2))))
  have hmShellBound : Measurable shellBound := by
    simpa only [shellBound, shellTerm] using hmS
  have hmShellTerm : ∀ j : ℕ, Measurable (shellTerm j) := fun j => by
    simpa only [shellTerm] using! (hmP j).add (hmM j)
  have hmCoreMBound : Measurable coreMBound := by
    simpa only [coreMBound] using hmCM
  have hmCorePBound : Measurable corePBound := by
    simpa only [corePBound] using hmCP
  have hmShellCoreM :
      Measurable (fun η => shellBound η + coreMBound η) :=
    hmShellBound.add hmCoreMBound
  have hmShellCores :
      Measurable (fun η => shellBound η + coreMBound η + corePBound η) :=
    hmShellCoreM.add hmCorePBound
  refine le_trans (setLIntegral_mono' measurableSet_Icc hpt) ?_
  refine le_trans (setLIntegral_le_lintegral _ _) ?_
  change (∫⁻ η, shellBound η + coreMBound η + corePBound η + midBound η) ≤ _
  rw [lintegral_add_left hmShellCores, lintegral_add_left hmShellCoreM,
    lintegral_add_left hmShellBound]
  dsimp only [shellBound]
  rw [MeasureTheory.lintegral_finsetSum' _ (fun j _ =>
    (hmShellTerm j).aemeasurable)]
  dsimp only [shellTerm, coreMBound, corePBound, midBound]
  refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
  · -- shells
    have hterm : ∀ j ∈ Finset.range J,
        (∫⁻ η, ((shellSetP c C B ρ (2 ^ j * σ0)).indicator
            (fun _ => ENNReal.ofReal (2 * Real.pi
              * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
              / Real.sqrt (min (2 ^ j * σ0 * causticKappa ρ ‖B‖ / 2)
                (1 / 2)))) η
          + (shellSetM c C B ρ (2 ^ j * σ0)).indicator
            (fun _ => ENNReal.ofReal (2 * Real.pi
              * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
              / Real.sqrt (min (2 ^ j * σ0 * causticKappa ρ ‖B‖ / 2)
                (1 / 2)))) η))
        ≤ ENNReal.ofReal (8 * Real.pi ^ 2
            * (r * (2 * ρ + r) / ((ρ - ‖B‖) / 2 * ‖B‖))
            * (Real.sqrt (2 / (causticKappa ρ ‖B‖ * (‖c‖ * ‖C‖)))
              + Real.sqrt 2)) := by
      intro j _
      rw [lintegral_add_left (hmP j),
        lintegral_indicator (measurableSet_shellSetP c C B ρ _),
        lintegral_indicator (measurableSet_shellSetM c C B ρ _),
        setLIntegral_const, setLIntegral_const]
      refine le_trans (add_le_add
        (shellP_prod_le hB hC hc hρB hr0 hσ0 j)
        (shellM_prod_le hB hC hc hρB hr0 hσ0 j)) (le_of_eq ?_)
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range]
  · -- inner core
    rw [lintegral_indicator (measurableSet_coreSetM c C B ρ r σ0),
      setLIntegral_const]
    have hvol : volume (coreSetM c C B ρ r σ0)
        ≤ ENNReal.ofReal (2 * Real.pi
            * Real.sqrt (2 * ((σ0 + r * (2 * (ρ + ‖B‖) + r))
              / (2 * (‖c‖ * ‖C‖))))) :=
      coreSetM_volume_le hB hC hc hr0
    refine le_trans (mul_le_mul_right hvol _) (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity)]
  · -- outer core
    rw [lintegral_indicator (measurableSet_coreSetP c C B ρ r σ0),
      setLIntegral_const]
    have hvol : volume (coreSetP c C B ρ r σ0)
        ≤ ENNReal.ofReal (2 * Real.pi
            * Real.sqrt (2 * ((σ0 + r * (2 * (ρ + ‖B‖) + r))
              / (2 * (‖c‖ * ‖C‖))))) :=
      coreSetP_volume_le hC hc
    refine le_trans (mul_le_mul_right hvol _) (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity)]
  · -- mid annulus
    rw [lintegral_indicator (measurableSet_midSet c C B ρ),
      setLIntegral_const]
    have hvol : volume (midSet c C B ρ) ≤ ENNReal.ofReal (2 * Real.pi) := by
      refine le_trans (measure_mono (fun η h => h.1)) ?_
      rw [Real.volume_Icc]
      apply ENNReal.ofReal_le_ofReal
      linarith [Real.pi_pos]
    refine le_trans (mul_le_mul_right hvol _) (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring

end Sublevel
end RHTower
