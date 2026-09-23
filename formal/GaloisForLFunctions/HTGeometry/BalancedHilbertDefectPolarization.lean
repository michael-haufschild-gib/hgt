import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Balanced Hilbert defect polarization

Two square-summable Hilbert-valued channels have a square-summable pointwise defect.  Expanding
that defect gives the exact total-mass/cross-polarization law.  When the channels have the same
total mass, the law collapses to twice the gap between one mass and their real inner-product
overlap.

The equal-mass hypothesis is discharged in two reusable cases:

* pointwise norm preservation, as for conjugation or an isometry;
* reindexing a single channel by an equivalence.

These two cases cover the global and endpoint Xi reflection-defect energies without putting
Xi-specific analytic content in the general hypertranscendence layer.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι 𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- On the scalar complex Hilbert space, the real inner product is the real part of the
Hermitian product in the orientation used by value-reflection formulas. -/
theorem re_inner_complex_eq_mul_conj_re (z w : ℂ) :
    RCLike.re (inner ℂ z w) = (z * (starRingEnd ℂ) w).re := by
  rw [RCLike.inner_apply]
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Square summability of two Hilbert-valued channels implies summability of the product of
their pointwise norms. -/
theorem summable_norm_mul_norm_of_summable_norm_sq
    {f g : ι → E}
    (hf : Summable (fun i => ‖f i‖ ^ (2 : ℕ)))
    (hg : Summable (fun i => ‖g i‖ ^ (2 : ℕ))) :
    Summable (fun i => ‖f i‖ * ‖g i‖) := by
  refine ((hf.mul_left (2 : ℝ)⁻¹).add
    (hg.mul_left (2 : ℝ)⁻¹)).of_norm_bounded (fun i => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  nlinarith [sq_nonneg (‖f i‖ - ‖g i‖)]

/-- The real part of the pointwise Hilbert pairing is summable for two square-summable
channels.  Thus callers do not need to carry an independent cross-term summability interface. -/
theorem summable_re_inner_of_summable_norm_sq
    {f g : ι → E}
    (hf : Summable (fun i => ‖f i‖ ^ (2 : ℕ)))
    (hg : Summable (fun i => ‖g i‖ ^ (2 : ℕ))) :
    Summable (fun i => RCLike.re (inner 𝕜 (f i) (g i))) := by
  exact Summable.of_norm_bounded
    (summable_norm_mul_norm_of_summable_norm_sq hf hg)
    (fun i => (RCLike.norm_re_le_norm _).trans (norm_inner_le_norm (𝕜 := 𝕜) _ _))

/-- The pointwise difference of two square-summable Hilbert-valued channels is square
summable. -/
theorem summable_norm_sub_sq_of_summable_norm_sq
    {f g : ι → E}
    (hf : Summable (fun i => ‖f i‖ ^ (2 : ℕ)))
    (hg : Summable (fun i => ‖g i‖ ^ (2 : ℕ))) :
    Summable (fun i => ‖f i - g i‖ ^ (2 : ℕ)) := by
  refine ((hf.mul_left 2).add (hg.mul_left 2)).of_norm_bounded (fun i => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hnorm : ‖f i - g i‖ ≤ ‖f i‖ + ‖g i‖ := norm_sub_le _ _
  calc
    ‖f i - g i‖ ^ (2 : ℕ) ≤ (‖f i‖ + ‖g i‖) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ 2 * ‖f i‖ ^ (2 : ℕ) + 2 * ‖g i‖ ^ (2 : ℕ) := by
      nlinarith [sq_nonneg (‖f i‖ - ‖g i‖)]

/-- **Square-summable Hilbert defect polarization.**  The total squared defect is the sum of
the two channel masses minus twice their real cross-polarization. -/
theorem tsum_norm_sub_sq_eq_mass_sub_two_re_inner_add_mass
    {f g : ι → E}
    (hf : Summable (fun i => ‖f i‖ ^ (2 : ℕ)))
    (hg : Summable (fun i => ‖g i‖ ^ (2 : ℕ))) :
    (∑' i, ‖f i - g i‖ ^ (2 : ℕ)) =
      (∑' i, ‖f i‖ ^ (2 : ℕ)) -
        2 * ∑' i, RCLike.re (inner 𝕜 (f i) (g i)) +
      ∑' i, ‖g i‖ ^ (2 : ℕ) := by
  have hinner : Summable (fun i => RCLike.re (inner 𝕜 (f i) (g i))) :=
    summable_re_inner_of_summable_norm_sq (𝕜 := 𝕜) hf hg
  calc
    (∑' i, ‖f i - g i‖ ^ (2 : ℕ)) =
        ∑' i, (‖f i‖ ^ (2 : ℕ) -
          2 * RCLike.re (inner 𝕜 (f i) (g i)) + ‖g i‖ ^ (2 : ℕ)) := by
      apply tsum_congr
      intro i
      exact norm_sub_sq (𝕜 := 𝕜) (f i) (g i)
    _ = (∑' i, ‖f i‖ ^ (2 : ℕ)) -
          2 * ∑' i, RCLike.re (inner 𝕜 (f i) (g i)) +
        ∑' i, ‖g i‖ ^ (2 : ℕ) := by
      rw [(hf.sub (hinner.mul_left 2)).tsum_add hg,
        hf.tsum_sub (hinner.mul_left 2), tsum_mul_left]

/-- **Balanced Hilbert defect law.**  If two square-summable channels have the same total
mass, their squared distance is twice the gap between that mass and their real overlap. -/
theorem tsum_norm_sub_sq_eq_two_mul_mass_sub_re_inner_of_balanced
    {f g : ι → E}
    (hf : Summable (fun i => ‖f i‖ ^ (2 : ℕ)))
    (hg : Summable (fun i => ‖g i‖ ^ (2 : ℕ)))
    (hbalance : (∑' i, ‖g i‖ ^ (2 : ℕ)) = ∑' i, ‖f i‖ ^ (2 : ℕ)) :
    (∑' i, ‖f i - g i‖ ^ (2 : ℕ)) =
      2 * ((∑' i, ‖f i‖ ^ (2 : ℕ)) -
        ∑' i, RCLike.re (inner 𝕜 (f i) (g i))) := by
  rw [tsum_norm_sub_sq_eq_mass_sub_two_re_inner_add_mass (𝕜 := 𝕜) hf hg,
    hbalance]
  ring

/-- Pointwise norm preservation discharges the equal-total-mass interface in the balanced
defect law. -/
theorem tsum_norm_sub_sq_eq_two_mul_mass_sub_re_inner_of_norm_eq
    {f g : ι → E}
    (hf : Summable (fun i => ‖f i‖ ^ (2 : ℕ)))
    (hg : Summable (fun i => ‖g i‖ ^ (2 : ℕ)))
    (hnorm : ∀ i, ‖g i‖ = ‖f i‖) :
    (∑' i, ‖f i - g i‖ ^ (2 : ℕ)) =
      2 * ((∑' i, ‖f i‖ ^ (2 : ℕ)) -
        ∑' i, RCLike.re (inner 𝕜 (f i) (g i))) := by
  apply tsum_norm_sub_sq_eq_two_mul_mass_sub_re_inner_of_balanced
    (𝕜 := 𝕜) hf hg
  apply tsum_congr
  intro i
  rw [hnorm i]

/-- Reindexing by an equivalence automatically preserves square summability and total mass, so
the balanced law needs only the original channel's square summability. -/
theorem tsum_norm_sub_equiv_sq_eq_two_mul_mass_sub_re_inner
    (e : ι ≃ ι) (f : ι → E)
    (hf : Summable (fun i => ‖f i‖ ^ (2 : ℕ))) :
    (∑' i, ‖f i - f (e i)‖ ^ (2 : ℕ)) =
      2 * ((∑' i, ‖f i‖ ^ (2 : ℕ)) -
        ∑' i, RCLike.re (inner 𝕜 (f i) (f (e i)))) := by
  have hg : Summable (fun i => ‖f (e i)‖ ^ (2 : ℕ)) :=
    hf.comp_injective e.injective
  apply tsum_norm_sub_sq_eq_two_mul_mass_sub_re_inner_of_balanced
    (𝕜 := 𝕜) hf hg
  exact e.tsum_eq (fun i => ‖f i‖ ^ (2 : ℕ))

/-- A square-summable Hilbert defect has zero total mass exactly when the two channels agree
pointwise. -/
theorem tsum_norm_sub_sq_eq_zero_iff
    {f g : ι → E}
    (hf : Summable (fun i => ‖f i‖ ^ (2 : ℕ)))
    (hg : Summable (fun i => ‖g i‖ ^ (2 : ℕ))) :
    (∑' i, ‖f i - g i‖ ^ (2 : ℕ)) = 0 ↔ ∀ i, f i = g i := by
  have hdefect := summable_norm_sub_sq_of_summable_norm_sq hf hg
  constructor
  · intro hzero i
    have hle := hdefect.le_tsum i (fun j _ => sq_nonneg ‖f j - g j‖)
    rw [hzero] at hle
    have hsquare : ‖f i - g i‖ ^ (2 : ℕ) = 0 := le_antisymm hle (sq_nonneg _)
    have hnorm : ‖f i - g i‖ = 0 := by
      nlinarith [norm_nonneg (f i - g i)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  · intro h
    have hfun : (fun i => ‖f i - g i‖ ^ (2 : ℕ)) = 0 := by
      funext i
      simp [h i]
    rw [hfun]
    exact tsum_zero

/-- Reindexing specialization of the zero-defect criterion. -/
theorem tsum_norm_sub_equiv_sq_eq_zero_iff
    (e : ι ≃ ι) (f : ι → E)
    (hf : Summable (fun i => ‖f i‖ ^ (2 : ℕ))) :
    (∑' i, ‖f i - f (e i)‖ ^ (2 : ℕ)) = 0 ↔ ∀ i, f i = f (e i) := by
  exact tsum_norm_sub_sq_eq_zero_iff hf (hf.comp_injective e.injective)

end

end GaloisForLFunctions.HTGeometry
