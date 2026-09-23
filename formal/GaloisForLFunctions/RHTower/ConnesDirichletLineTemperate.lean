import GaloisForLFunctions.RHTower.ConnesZetaLineTemperate
import GaloisForLFunctions.RHTower.DirichletLPhragmenInputs

/-!
# App I (25) for Dirichlet L-functions

Appendix I (25) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Connes needs the restriction of `L(Χ₀, ·)` to the critical line to be a multiplier of the Schwartz
space.  `ConnesHolomorphicLineTemperate.connes_hasTemperateGrowth_lineRestrict` already reduces
this to two inputs: analyticity on a tube around the line, and a polynomial bound there.  For the
Hecke characters of `ℚ` - the Dirichlet characters - both are available:

* analyticity, because `L(Χ, ·)` is entire for `Χ ≠ 1` (mathlib's
  `DirichletCharacter.differentiableAt_LFunction`);
* the polynomial bound, from the corpus's Phragmén–Lindelöf cubic envelope
  `RHTower.bound_LFunction_strip`, valid on `-2 ≤ Re s ≤ 3` - a strip that contains the whole
  radius-`1/8` tube around the critical line.

So App I (25) holds for every primitive non-principal Dirichlet character, i.e. for every
non-trivial Grössencharakter of `ℚ`.
-/

open Complex

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {N : ℕ} [NeZero N]

/-- A non-principal Dirichlet `L`-function is analytic on the critical strip. -/
theorem connes_dirichletL_analyticOnNhd {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) connesCriticalStrip := by
  refine DifferentiableOn.analyticOnNhd ?_ connesCriticalStrip_isOpen
  intro z _
  exact (DirichletCharacter.differentiableAt_LFunction χ z (Or.inr hχ)).differentiableWithinAt

/-- **App I (25) for a Dirichlet `L`-function.**  The `L`-function of a primitive non-principal
Dirichlet character, restricted to the critical line, has temperate growth. -/
theorem connes_dirichletL_hasTemperateGrowth {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) :
    Function.HasTemperateGrowth
      (fun t : ℝ => DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (t : ℂ) * I)) := by
  obtain ⟨C, hC0, hC⟩ := _root_.RHTower.bound_LFunction_strip hχ hprim
  refine connes_hasTemperateGrowth_lineRestrict connesCriticalStrip_isOpen
    (connes_dirichletL_analyticOnNhd hχ) (1 / 2 : ℂ) (by norm_num : (0 : ℝ) < 1 / 8)
    connes_criticalLine_mem (fun s z hz => connes_criticalTube_subset s hz)
    (C := C * 125) (N := 3) ?_
  intro s z hz
  obtain ⟨hre1, hre2⟩ := connes_criticalTube_re hz
  have him := abs_le.mp (connes_criticalTube_im hz)
  have hb := hC z (by linarith) (by linarith)
  have hnorm : ‖z - 4‖ ≤ 5 * (1 + |s|) := by
    have h1 : ‖z - 4‖ ≤ |(z - 4).re| + |(z - 4).im| := Complex.norm_le_abs_re_add_abs_im _
    have hre : (z - 4).re = z.re - 4 := by simp
    have him2 : (z - 4).im = z.im := by simp
    rw [hre, him2] at h1
    have h2 : |z.re - 4| ≤ 4 := by
      rw [abs_le]
      constructor <;> linarith
    have h3 : |z.im| ≤ |s| + 1 / 8 := by
      rcases abs_cases z.im with ⟨he, _⟩ | ⟨he, _⟩ <;>
        rcases abs_cases s with ⟨hs, _⟩ | ⟨hs, _⟩ <;> rw [he] <;>
          linarith [him.1, him.2]
    have habs : (0 : ℝ) ≤ |s| := abs_nonneg s
    linarith
  have hcube : ‖z - 4‖ ^ (3 : ℕ) ≤ 125 * (1 + |s|) ^ (3 : ℕ) := by
    have h0 : (0 : ℝ) ≤ ‖z - 4‖ := norm_nonneg _
    have hpow := pow_le_pow_left₀ h0 hnorm 3
    calc ‖z - 4‖ ^ (3 : ℕ) ≤ (5 * (1 + |s|)) ^ (3 : ℕ) := hpow
      _ = 125 * (1 + |s|) ^ (3 : ℕ) := by ring
  calc ‖DirichletCharacter.LFunction χ z‖ ≤ C * ‖z - 4‖ ^ (3 : ℕ) := hb
    _ ≤ C * (125 * (1 + |s|) ^ (3 : ℕ)) := mul_le_mul_of_nonneg_left hcube hC0.le
    _ = C * 125 * (1 + |s|) ^ (3 : ℕ) := by ring

/-- **The multiplier of App I (25) for a Dirichlet `L`-function.** -/
def connesDirichletLineMultiplier (χ : DirichletCharacter ℂ N) :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ
    (fun t : ℝ => DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (t : ℂ) * I))

/-- **App I (25) for a Dirichlet `L`-function, the conclusion.**  `L(Χ, 1/2+it) ψ(t)` is again a
Schwartz function. -/
theorem connesDirichletLineMultiplier_apply {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) (ψ : SchwartzMap ℝ ℂ) (t : ℝ) :
    connesDirichletLineMultiplier χ ψ t
      = DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (t : ℂ) * I) * ψ t := by
  rw [connesDirichletLineMultiplier,
    SchwartzMap.smulLeftCLM_apply_apply (connes_dirichletL_hasTemperateGrowth hχ hprim),
    smul_eq_mul]

end

end GaloisForLFunctions.RHTower
