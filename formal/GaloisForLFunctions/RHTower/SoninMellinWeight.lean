import GaloisForLFunctions.RHTower.SoninAnnulusBump
import GaloisForLFunctions.RHTower.SoninRapidFourierDecay
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The Mellin weight on the annulus is smooth and compactly supported

The Mellin kernel `x^{-s}` is singular only at the origin, and the annulus profile avoids a
neighbourhood of the origin, so their product is smooth on the whole line and compactly supported.
That is exactly the hypothesis of the rapid-decay lemma.

Only the positive half of the profile is used, since the Mellin transform integrates over the
positive half-line; the reflected half lives on the negatives and never enters.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter
open scoped Topology ContDiff FourierTransform

/-- The one-sided annulus profile, supported strictly inside `(b, c)` on the positive axis. -/
def soninPositiveBump (b c : ℝ) (hbc : b < c) : ℝ → ℝ := fun x =>
  soninAnnulusBumpData b c hbc x

theorem contDiff_soninPositiveBump (b c : ℝ) (hbc : b < c) :
    ContDiff ℝ ∞ (soninPositiveBump b c hbc) :=
  (soninAnnulusBumpData b c hbc).contDiff

theorem soninPositiveBump_support_subset (b c : ℝ) (hbc : b < c) {x : ℝ}
    (hx : soninPositiveBump b c hbc x ≠ 0) : b < x ∧ x < c :=
  soninAnnulusBumpData_support_subset b c hbc hx

theorem soninPositiveBump_eq_zero_of_le (b c : ℝ) (hbc : b < c) {x : ℝ} (hx : x ≤ b) :
    soninPositiveBump b c hbc x = 0 := by
  by_contra hne
  exact absurd hx (not_le.mpr (soninPositiveBump_support_subset b c hbc hne).1)

theorem hasCompactSupport_soninPositiveBump (b c : ℝ) (hbc : b < c) :
    HasCompactSupport (soninPositiveBump b c hbc) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := b) (b := c)) ?_
  intro x hx
  obtain ⟨h1, h2⟩ := soninPositiveBump_support_subset b c hbc hx
  exact ⟨h1.le, h2.le⟩

/-- The Mellin weight: the one-sided profile against the Mellin kernel. -/
def soninMellinWeight (b c : ℝ) (hbc : b < c) (s : ℂ) : ℝ → ℂ := fun x =>
  (soninPositiveBump b c hbc x : ℂ) * Complex.exp (-s * (Real.log x : ℂ))

/-- On the positive axis the Mellin weight is the profile times `x ^ (-s)`. -/
theorem soninMellinWeight_eq_cpow (b c : ℝ) (hbc : b < c) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    soninMellinWeight b c hbc s x = (soninPositiveBump b c hbc x : ℂ) * (x : ℂ) ^ (-s) := by
  unfold soninMellinWeight
  congr 1
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne')]
  congr 1
  rw [← Complex.ofReal_log hx.le]
  ring

/-- The Mellin weight is smooth: away from the origin because the kernel is, and near the origin
because the profile vanishes there. -/
theorem contDiff_soninMellinWeight (b c : ℝ) (hb : 0 < b) (hbc : b < c) (s : ℂ) :
    ContDiff ℝ ∞ (soninMellinWeight b c hbc s) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : 0 < x
  · refine ContDiffAt.mul ?_ ?_
    · exact (Complex.ofRealCLM.contDiff.comp
        (contDiff_soninPositiveBump b c hbc)).contDiffAt
    · refine Complex.contDiff_exp.contDiffAt.comp x ?_
      refine ContDiffAt.mul contDiffAt_const ?_
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp x
        (Real.contDiffAt_log.mpr hx.ne')
  · have hev : soninMellinWeight b c hbc s =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      have hopen : Set.Iio b ∈ 𝓝 x := by
        refine IsOpen.mem_nhds isOpen_Iio ?_
        simp only [Set.mem_Iio]
        push Not at hx
        linarith
      filter_upwards [hopen] with y hy
      simp only [soninMellinWeight,
        soninPositiveBump_eq_zero_of_le b c hbc (le_of_lt hy)]
      simp
    exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const hev

theorem hasCompactSupport_soninMellinWeight (b c : ℝ) (hbc : b < c) (s : ℂ) :
    HasCompactSupport (soninMellinWeight b c hbc s) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (hasCompactSupport_soninPositiveBump b c hbc) ?_
  intro x hx
  refine subset_tsupport _ ?_
  intro h0
  exact hx (by simp [soninMellinWeight, h0])

/-- **Rapid decay of the Mellin-weighted transform.**  Every fixed Mellin exponent sees the
oscillatory integral vanish faster than every polynomial rate. -/
theorem tendsto_pow_mul_norm_fourier_soninMellinWeight
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (s : ℂ) (N : ℕ) :
    Tendsto (fun w : ℝ => w ^ N * ‖𝓕 (soninMellinWeight b c hbc s) w‖) atTop (𝓝 0) :=
  tendsto_pow_mul_norm_fourier_atTop (hasCompactSupport_soninMellinWeight b c hbc s)
    (contDiff_soninMellinWeight b c hb hbc s) N

end RHTower
