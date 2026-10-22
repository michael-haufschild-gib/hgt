import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerGaussianResidueGrowth
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmInfiniteOrientationSingularities
import GaloisForLFunctions.RHTower.WindingXiCircle

/-!
# Nonadmission of the Gaussian Green residue packet

The residue of the completed singular Meyer lift grows like `exp(γ²/(32π))` along the strip.  The
Xi zero set is infinite and meets every compact disc in a finite set, so its ordinates are
unbounded; evaluating the growth estimate along such zeros makes the residue family unbounded.

An unbounded family of coordinates cannot lie in any carrier whose coordinate evaluations are
bounded by the norm — in particular not in the unweighted `ℓ²` Xi incidence carrier.

The obstruction is exact rather than merely negative: the flattening factor inverts the residue
pointwise, so the diagonal renormalisation forced by the obstruction is uniquely determined.

* `exists_xiZero_im_gt` : the Xi zero ordinates are unbounded.
* `not_exists_bound_gaussianGreenResidue` : the residue family is unbounded along the Xi zeros.
* `gaussianResidueFlattening_mul_self` : the flattening factor inverts the residue.
-/

open Complex Filter Topology Set
open scoped Real

namespace RHTower
namespace DeningerMeyerGaussianGreen

noncomputable section

/-- The Gamma/Green residue of the completed singular lift at a strip point. -/
def gaussianGreenResidue (c ρ : ℂ) : ℂ :=
  -(2 * (Real.pi : ℂ) * archFactor ρ / (gaussianMellinCharacter c ρ * (ρ - c)))

/-- **The Xi zero ordinates are unbounded.**  If they were bounded, the zero set would lie in a
compact disc — the real parts are confined to the open unit strip — and would therefore be finite,
contradicting its infinitude. -/
theorem exists_xiZero_im_gt (T : ℝ) : ∃ ρ ∈ xiZeroSet, T < |ρ.im| := by
  by_contra hcon
  rw [not_exists] at hcon
  simp only [not_and, not_lt] at hcon
  have hsub : xiZeroSet ⊆ {z ∈ Metric.closedBall (0 : ℂ) (1 + |T|) | xi z = 0} := by
    intro z hz
    have hstrip := xiZeroSet_mem_openUnitStrip hz
    have him := hcon z hz
    refine ⟨?_, hz⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 1 + |T| := by
        have h1 : |z.re| ≤ 1 := by
          rw [abs_of_pos hstrip.1]
          linarith [hstrip.2]
        have h2 : |z.im| ≤ |T| := le_trans him (le_abs_self T)
        linarith
  exact xiZeroSet_infinite ((xi_zeros_closedBall_finite 0 (1 + |T|)).subset hsub)

/-- **The Gaussian Green residue family is unbounded along the Xi zeros.**  The growth estimate is
evaluated at zeros of arbitrarily large ordinate, which exist because the zero set is infinite and
locally finite. -/
theorem not_exists_bound_gaussianGreenResidue :
    ¬ ∃ B : ℝ, ∀ ρ ∈ xiZeroSet, ‖gaussianGreenResidue 2 ρ‖ ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨C, hCpos, T₀, hT₀pos, hgrow⟩ := exists_residue_growth
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set T : ℝ := max T₀ (max 1 (32 * Real.pi * (|B| / C) + 1)) with hT
  obtain ⟨ρ, hρ, hρT⟩ := exists_xiZero_im_gt T
  have hstrip := xiZeroSet_mem_openUnitStrip hρ
  have hT0le : T₀ ≤ T := le_max_left _ _
  have hT1 : (1 : ℝ) ≤ T := le_trans (le_max_left _ _) (le_max_right _ _)
  have hTbig : 32 * Real.pi * (|B| / C) + 1 ≤ T :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT1
  have hres := hgrow ρ hstrip.1 hstrip.2 (le_of_lt (lt_of_le_of_lt hT0le hρT))
  -- the exponent is large
  have hsq : T ^ (2 : ℕ) ≤ ρ.im ^ (2 : ℕ) := by
    have h := sq_abs ρ.im
    nlinarith [abs_nonneg ρ.im, hρT, hTpos]
  have hu : |B| / C < ρ.im ^ (2 : ℕ) / (32 * Real.pi) := by
    have hTT : T ≤ T ^ (2 : ℕ) := by nlinarith
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [hsq, hTT, hTbig, hpi]
  have hexp : ρ.im ^ (2 : ℕ) / (32 * Real.pi) < Real.exp (ρ.im ^ (2 : ℕ) / (32 * Real.pi)) :=
    lt_of_lt_of_le (lt_add_one _) (Real.add_one_le_exp _)
  have hfinal : B < C * Real.exp (ρ.im ^ (2 : ℕ) / (32 * Real.pi)) := by
    have h1 : |B| < C * (ρ.im ^ (2 : ℕ) / (32 * Real.pi)) := by
      have h := (div_lt_iff₀ hCpos).1 hu
      linarith [h]
    have h2 : C * (ρ.im ^ (2 : ℕ) / (32 * Real.pi)) ≤ C * Real.exp (ρ.im ^ (2 : ℕ) / (32 * Real.pi)) :=
      mul_le_mul_of_nonneg_left (le_of_lt hexp) (le_of_lt hCpos)
    exact lt_of_le_of_lt (le_abs_self B) (lt_of_lt_of_le h1 h2)
  exact absurd (le_trans hres (hB ρ hρ)) (not_le.2 hfinal)

/-- **No carrier with norm-bounded coordinates admits the residue packet.**  Any family whose
coordinates are bounded by a single constant is bounded; the residue family is not. -/
theorem not_forall_norm_le_of_gaussianGreenResidue (b : ℂ → ℝ)
    (hb : ∀ ρ ∈ xiZeroSet, ‖gaussianGreenResidue 2 ρ‖ ≤ b ρ)
    (hbdd : ∃ B : ℝ, ∀ ρ ∈ xiZeroSet, b ρ ≤ B) : False := by
  obtain ⟨B, hB⟩ := hbdd
  exact not_exists_bound_gaussianGreenResidue ⟨B, fun ρ hρ => le_trans (hb ρ hρ) (hB ρ hρ)⟩

/-- The source-residue flattening factor. -/
def gaussianResidueFlattening (c ρ : ℂ) : ℂ :=
  -(gaussianMellinCharacter c ρ * (ρ - c) / (2 * (Real.pi : ℂ) * archFactor ρ))

/-- **The flattening factor inverts the residue.**  The obstruction therefore determines the
diagonal renormalisation instead of merely rejecting the packet. -/
theorem gaussianResidueFlattening_mul_self {c ρ : ℂ}
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) (hcr : ρ ≠ c) :
    gaussianResidueFlattening c ρ * gaussianGreenResidue c ρ = 1 := by
  have hchar : gaussianMellinCharacter c ρ ≠ 0 := Complex.exp_ne_zero _
  have harch : archFactor ρ ≠ 0 := archFactor_ne_zero_strip hstrip
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsub : ρ - c ≠ 0 := sub_ne_zero.mpr hcr
  rw [gaussianResidueFlattening, gaussianGreenResidue]
  field_simp

end

end DeningerMeyerGaussianGreen
end RHTower
