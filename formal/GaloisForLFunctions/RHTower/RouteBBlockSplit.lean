/-
Block-splitting inputs for the hierarchical small-ball step: a prime-index
character is a single bare phase, and the unit-interval phase measure
rescales to the angle interval `[0, 2π]`.
-/
import Mathlib
import GaloisForLFunctions.RHTower.RouteBHierarchy

namespace RHTower
namespace SteinhausModel

open MeasureTheory

/-- At a prime index the character is one bare phase:
`X p ω = exp(2πi·ω p)`. -/
theorem X_prime {p : ℕ} (hp : p.Prime) (ω : Omega) :
    X p ω = Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (ω p : ℂ)) := by
  unfold X
  rw [hp.primeFactors, Finset.sum_singleton, hp.factorization_self]
  norm_num

end SteinhausModel
end RHTower

namespace RHTower
namespace SteinhausModel

open MeasureTheory

/-- The phase rescale: pushing the uniform phase on `[0,1]` through
`θ = 2π·x` gives `(2π)⁻¹` times Lebesgue on `[0, 2π]`. -/
theorem map_two_pi_smul :
    Measure.map (fun x : ℝ => 2 * Real.pi * x)
        (volume.restrict (Set.Icc (0 : ℝ) 1))
      = ENNReal.ofReal (2 * Real.pi)⁻¹
          • volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpre : (fun x : ℝ => 2 * Real.pi * x) ⁻¹'
      Set.Icc (0 : ℝ) (2 * Real.pi) = Set.Icc 0 1 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
  calc Measure.map (fun x : ℝ => 2 * Real.pi * x)
        (volume.restrict (Set.Icc (0 : ℝ) 1))
      = Measure.map (fun x : ℝ => 2 * Real.pi * x)
          (volume.restrict ((fun x : ℝ => 2 * Real.pi * x) ⁻¹'
            Set.Icc (0 : ℝ) (2 * Real.pi))) := by rw [hpre]
    _ = (Measure.map (fun x : ℝ => 2 * Real.pi * x) volume).restrict
          (Set.Icc (0 : ℝ) (2 * Real.pi)) :=
        (Measure.restrict_map (by fun_prop) measurableSet_Icc).symm
    _ = (ENNReal.ofReal |(2 * Real.pi)⁻¹| • volume).restrict
          (Set.Icc (0 : ℝ) (2 * Real.pi)) := by
        rw [Real.map_volume_mul_left (ne_of_gt hπ)]
    _ = ENNReal.ofReal (2 * Real.pi)⁻¹
          • volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)) := by
        rw [Measure.restrict_smul, abs_of_pos (by positivity)]

end SteinhausModel
end RHTower

namespace RHTower
namespace Sublevel

open MeasureTheory

/-- **The center-uniform one-phase small-ball law.**  For `2s ≤ ‖D‖` the
sublevel measure of one circle arm is at most `8πs/‖D‖` UNIFORMLY in the
center: below reach the set is empty, above it the radial √-law applies
with `‖c'‖ ≥ ‖D‖/2`.  This is the distribution bound the fourth-phase
averaging of the three-phase constants consumes. -/
theorem one_phase_smallball_uniform {D c' : ℂ} {s : ℝ} (hD : D ≠ 0)
    (hs : 0 ≤ s) (hs2 : 2 * s ≤ ‖D‖) :
    volume {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
        ‖c' + D * Complex.exp ((η : ℂ) * Complex.I)‖ ≤ s}
      ≤ ENNReal.ofReal (8 * Real.pi * s / ‖D‖) := by
  have hD0 : (0 : ℝ) < ‖D‖ := norm_pos_iff.mpr hD
  rcases lt_or_ge ‖c'‖ (‖D‖ / 2) with hc | hc
  · have hempty : {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
        ‖c' + D * Complex.exp ((η : ℂ) * Complex.I)‖ ≤ s} = ∅ := by
      ext η
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, hle⟩
      have htri := abs_norm_sub_norm_le
        (c' + D * Complex.exp ((η : ℂ) * Complex.I))
        (D * Complex.exp ((η : ℂ) * Complex.I))
      rw [add_sub_cancel_right, norm_mul, Complex.norm_exp_ofReal_mul_I,
        mul_one] at htri
      have h1 := abs_le.mp htri
      linarith [h1.1]
    rw [hempty, measure_empty]
    exact bot_le
  · have hc0 : c' ≠ 0 := by
      intro h
      rw [h, norm_zero] at hc
      linarith
    have hsub : {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
          ‖c' + D * Complex.exp ((η : ℂ) * Complex.I)‖ ≤ s}
        ⊆ {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
            |‖c' + D * Complex.exp ((η : ℂ) * Complex.I)‖ - 0| ≤ s} := by
      rintro η ⟨hηI, hle⟩
      refine ⟨hηI, ?_⟩
      rw [sub_zero, abs_of_nonneg (norm_nonneg _)]
      exact hle
    refine le_trans (measure_mono hsub)
      (le_trans (radial_band_measure hc0 hD le_rfl hs)
        (ENNReal.ofReal_le_ofReal ?_))
    have harg : 2 * (s * (2 * 0 + s) / (‖c'‖ * ‖D‖))
        ≤ (2 * s / ‖D‖) ^ 2 := by
      rw [show 2 * (s * (2 * 0 + s) / (‖c'‖ * ‖D‖))
          = 2 * (s * s) / (‖c'‖ * ‖D‖) from by ring, div_pow,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg
        (by nlinarith [hc, hD0] : (0 : ℝ) ≤ 2 * ‖c'‖ - ‖D‖)
        (by positivity : (0 : ℝ) ≤ 2 * s ^ 2 * ‖D‖)]
    have hsq := Real.sqrt_le_sqrt harg
    rw [Real.sqrt_sq (by positivity)] at hsq
    calc 2 * Real.pi * Real.sqrt (2 * (s * (2 * 0 + s) / (‖c'‖ * ‖D‖)))
        ≤ 2 * Real.pi * (2 * s / ‖D‖) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ 8 * Real.pi * s / ‖D‖ := by
          rw [show 2 * Real.pi * (2 * s / ‖D‖)
              = 4 * Real.pi * s / ‖D‖ from by ring]
          gcongr
          nlinarith [Real.pi_pos, hs]
  
end Sublevel
end RHTower

namespace RHTower
namespace Sublevel

open MeasureTheory

theorem inv_sqrt_average' {D c' : ℂ} {M K sstar : ℝ} {f : ℝ → ENNReal}
    (hD : D ≠ 0) (hK : 0 ≤ K) (hs : 0 < sstar)
    (hs2 : 2 * sstar ≤ ‖D‖)
    (hfM : ∀ η ∈ Set.Icc (0 : ℝ) (2 * Real.pi), f η ≤ ENNReal.ofReal M)
    (hfK : ∀ η ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      sstar ≤ ‖c' + D * Complex.exp ((η : ℂ) * Complex.I)‖ →
      f η ≤ ENNReal.ofReal
        (K / Real.sqrt ‖c' + D * Complex.exp ((η : ℂ) * Complex.I)‖)) :
    ∫⁻ η in Set.Icc (0 : ℝ) (2 * Real.pi), f η
      ≤ ENNReal.ofReal M * ENNReal.ofReal (8 * Real.pi * sstar / ‖D‖)
        + ENNReal.ofReal (K / Real.sqrt sstar)
          * ENNReal.ofReal (2 * Real.pi) := by
  classical
  have hcont : Continuous fun η : ℝ =>
      ‖c' + D * Complex.exp ((η : ℂ) * Complex.I)‖ :=
    (continuous_const.add (continuous_const.mul (Complex.continuous_exp.comp
      (Complex.continuous_ofReal.mul continuous_const)))).norm
  set E1 : Set ℝ := {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
      ‖c' + D * Complex.exp ((η : ℂ) * Complex.I)‖ ≤ sstar} with hE1
  set E2 : Set ℝ := {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
      sstar ≤ ‖c' + D * Complex.exp ((η : ℂ) * Complex.I)‖} with hE2
  have hE1m : MeasurableSet E1 := by
    apply IsClosed.measurableSet
    exact isClosed_Icc.inter (isClosed_le hcont continuous_const)
  have hE2m : MeasurableSet E2 := by
    apply IsClosed.measurableSet
    exact isClosed_Icc.inter (isClosed_le continuous_const hcont)
  have hpt : ∀ η ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      f η ≤ E1.indicator (fun _ => ENNReal.ofReal M) η
        + E2.indicator (fun _ => ENNReal.ofReal (K / Real.sqrt sstar)) η := by
    intro η hη
    rcases le_total ‖c' + D * Complex.exp ((η : ℂ) * Complex.I)‖ sstar
      with hle | hge
    · refine le_trans (hfM η hη) ?_
      refine le_trans (le_of_eq (Set.indicator_of_mem
        (show η ∈ E1 from ⟨hη, hle⟩) (fun _ => ENNReal.ofReal M)).symm) ?_
      exact le_self_add
    · refine le_trans (hfK η hη hge) ?_
      have hmono : K / Real.sqrt ‖c' + D * Complex.exp ((η : ℂ)
            * Complex.I)‖ ≤ K / Real.sqrt sstar := by
        apply div_le_div_of_nonneg_left hK (Real.sqrt_pos.mpr hs)
        exact Real.sqrt_le_sqrt hge
      refine le_trans (ENNReal.ofReal_le_ofReal hmono) ?_
      refine le_trans (le_of_eq (Set.indicator_of_mem
        (show η ∈ E2 from ⟨hη, hge⟩)
        (fun _ => ENNReal.ofReal (K / Real.sqrt sstar))).symm) ?_
      exact le_add_self
  refine le_trans (setLIntegral_mono' measurableSet_Icc hpt) ?_
  refine le_trans (setLIntegral_le_lintegral _ _) ?_
  rw [lintegral_add_left (measurable_const.indicator hE1m),
    lintegral_indicator hE1m, lintegral_indicator hE2m,
    setLIntegral_const, setLIntegral_const]
  have hv1 : volume E1 ≤ ENNReal.ofReal (8 * Real.pi * sstar / ‖D‖) :=
    one_phase_smallball_uniform hD hs.le hs2
  have hv2 : volume E2 ≤ ENNReal.ofReal (2 * Real.pi) := by
    refine le_trans (measure_mono (fun η h => h.1)) ?_
    rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    linarith [Real.pi_pos]
  exact add_le_add (mul_le_mul_right hv1 _) (mul_le_mul_right hv2 _)

/-- **The fourth-phase averaging of an inverse-√ singularity.**  Any
integrand dominated both by a constant `M` and by `K/√‖c' + De^{iη}‖`
integrates over the circle to at most `M·(8πs*/‖D‖) + (K/√s*)·2π` for any
split height `s*` with `2s* ≤ ‖D‖`: the singular region pays the constant
against the center-uniform one-phase law, the bulk pays the capped
singularity against the full circle. -/
theorem inv_sqrt_average {D c' : ℂ} {M K sstar : ℝ} {f : ℝ → ENNReal}
    (hD : D ≠ 0) (hK : 0 ≤ K) (hs : 0 < sstar)
    (hs2 : 2 * sstar ≤ ‖D‖)
    (hfM : ∀ η ∈ Set.Icc (0 : ℝ) (2 * Real.pi), f η ≤ ENNReal.ofReal M)
    (hfK : ∀ η ∈ Set.Icc (0 : ℝ) (2 * Real.pi), f η ≤ ENNReal.ofReal
      (K / Real.sqrt ‖c' + D * Complex.exp ((η : ℂ) * Complex.I)‖)) :
    ∫⁻ η in Set.Icc (0 : ℝ) (2 * Real.pi), f η
      ≤ ENNReal.ofReal M * ENNReal.ofReal (8 * Real.pi * sstar / ‖D‖)
        + ENNReal.ofReal (K / Real.sqrt sstar)
          * ENNReal.ofReal (2 * Real.pi) :=
  inv_sqrt_average' hD hK hs hs2 hfM (fun η hη _ => hfK η hη)

end Sublevel
end RHTower
