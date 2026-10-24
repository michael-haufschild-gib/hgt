import GaloisForLFunctions.RHTower.XiSliceBoundedDetectionOrder
import GaloisForLFunctions.HTGeometry.BanachTriangularExponential

/-!
# A finite Xi zero block with a compensated Gaussian tail

Retain any finite block of zero multiplicity copies exactly. The remaining product differs
from the exponential of its quadratic reciprocal-zero sum by at most its fourth moment times
an explicit exponential envelope. Absolute reciprocal-square summability proves convergence;
the actual Xi product formula identifies the reconstructed slice.
-/

open Filter Topology
namespace RHTower
noncomputable section

private theorem summable_gaussianTail_norm_sq {ι : Type*} (a : ι → ℂ)
    (ha : Summable fun i => ‖a i‖) : Summable fun i => ‖a i‖ ^ 2 := by
  refine (ha.mul_left (∑' i, ‖a i‖)).of_nonneg_of_le (fun i => sq_nonneg _) fun i => ?_
  have hi : ‖a i‖ ≤ ∑' j, ‖a j‖ := ha.le_tsum i (fun j _ => norm_nonneg _)
  nlinarith only [mul_le_mul_of_nonneg_right hi (norm_nonneg (a i))]

private theorem norm_tprod_one_add_sub_exp_tsum_le {ι : Type*} (a : ι → ℂ)
    (ha : Summable fun i => ‖a i‖) :
    ‖tprod (fun i : ι => (1 : ℂ) + a i) - Complex.exp (tsum a)‖ ≤
      Real.exp (2 * tsum (fun i : ι => ‖a i‖)) * tsum (fun i : ι => ‖a i‖ ^ 2) := by
  classical
  have hs := summable_gaussianTail_norm_sq a ha
  have hp := (multipliable_one_add_of_summable ha).hasProd
  have he := Complex.continuous_exp.continuousAt.tendsto.comp ha.of_norm.hasSum
  have hl := (hp.sub he).norm
  have hr := (Real.continuous_exp.continuousAt.tendsto.comp
    (ha.hasSum.const_mul 2)).mul hs.hasSum
  apply le_of_tendsto_of_tendsto' hl hr
  intro F
  simpa only [Function.comp_apply, Complex.exp_eq_exp_ℂ] using
    GaloisForLFunctions.HTGeometry.FormationDust.norm_prod_one_add_sub_exp_le F a

/-- The reciprocal-square contribution of a multiplicity copy to the centered slice. -/
def xiSliceGaussianReciprocal (t : ℝ) (q : XiZeroCopy) : ℂ :=
  ((xiSpectralPoint q - t) ^ 2)⁻¹

/-- The finite zero block retained exactly in the slice product. -/
def xiSliceGaussianHead (t : ℝ) (H : Finset XiZeroCopy) (z : ℂ) : ℂ :=
  ∏ q ∈ H, (1 + z ^ 2 * xiSliceGaussianReciprocal t q)

/-- The complementary product, with every zero multiplicity retained. -/
def xiSliceGaussianTail (t : ℝ) (H : Finset XiZeroCopy) (z : ℂ) : ℂ :=
  ∏' q : {q : XiZeroCopy // q ∉ H}, (1 + z ^ 2 * xiSliceGaussianReciprocal t q)

/-- The signed quadratic coefficient of the complementary zero product. -/
def xiSliceGaussianTailQuadratic (t : ℝ) (H : Finset XiZeroCopy) : ℂ :=
  ∑' q : {q : XiZeroCopy // q ∉ H}, xiSliceGaussianReciprocal t q

/-- The absolute reciprocal-square mass of the complementary zero product. -/
def xiSliceGaussianTailMass (t : ℝ) (H : Finset XiZeroCopy) : ℝ :=
  ∑' q : {q : XiZeroCopy // q ∉ H}, ‖xiSliceGaussianReciprocal t q‖

/-- The fourth reciprocal-distance moment governing the compensated error. -/
def xiSliceGaussianTailFourth (t : ℝ) (H : Finset XiZeroCopy) : ℝ :=
  ∑' q : {q : XiZeroCopy // q ∉ H}, ‖xiSliceGaussianReciprocal t q‖ ^ 2

theorem summable_norm_xiSliceGaussianReciprocal (t : ℝ) :
    Summable fun q : XiZeroCopy => ‖xiSliceGaussianReciprocal t q‖ := by
  simpa only [xiSliceGaussianReciprocal, norm_inv, norm_pow, one_div] using
    summable_inv_sq_norm_xiSpectralPoint_sub (t : ℂ)

theorem summable_norm_xiSliceGaussianTail (t : ℝ) (H : Finset XiZeroCopy) :
    Summable fun q : {q : XiZeroCopy // q ∉ H} => ‖xiSliceGaussianReciprocal t q‖ :=
  (summable_norm_xiSliceGaussianReciprocal t).subtype _

theorem summable_sq_norm_xiSliceGaussianTail (t : ℝ) (H : Finset XiZeroCopy) :
    Summable fun q : {q : XiZeroCopy // q ∉ H} => ‖xiSliceGaussianReciprocal t q‖ ^ 2 :=
  summable_gaussianTail_norm_sq _ (summable_norm_xiSliceGaussianTail t H)

/-- Subtracting the exact quadratic exponential leaves a fourth-moment error. -/
theorem norm_xiSliceGaussianTail_sub_exp_le (t : ℝ) (H : Finset XiZeroCopy) (z : ℂ) :
    ‖xiSliceGaussianTail t H z - Complex.exp (z ^ 2 * xiSliceGaussianTailQuadratic t H)‖ ≤
      Real.exp (2 * ‖z‖ ^ 2 * xiSliceGaussianTailMass t H) *
        (‖z‖ ^ 4 * xiSliceGaussianTailFourth t H) := by
  have hs : Summable fun q : {q : XiZeroCopy // q ∉ H} =>
      ‖z ^ 2 * xiSliceGaussianReciprocal t q‖ := by
    simpa only [norm_mul, norm_pow] using
      (summable_norm_xiSliceGaussianTail t H).mul_left (‖z‖ ^ 2)
  have h := norm_tprod_one_add_sub_exp_tsum_le
    (fun q : {q : XiZeroCopy // q ∉ H} => z ^ 2 * xiSliceGaussianReciprocal t q) hs
  have hquad : (∑' q : {q : XiZeroCopy // q ∉ H}, z ^ 2 * xiSliceGaussianReciprocal t q) =
      z ^ 2 * xiSliceGaussianTailQuadratic t H := tsum_mul_left
  have hmass : (∑' q : {q : XiZeroCopy // q ∉ H}, ‖z ^ 2 * xiSliceGaussianReciprocal t q‖) =
      ‖z‖ ^ 2 * xiSliceGaussianTailMass t H := by
    simp only [norm_mul, norm_pow, tsum_mul_left, xiSliceGaussianTailMass]
  have hfourth : (∑' q : {q : XiZeroCopy // q ∉ H}, ‖z ^ 2 * xiSliceGaussianReciprocal t q‖ ^ 2) =
      ‖z‖ ^ 4 * xiSliceGaussianTailFourth t H := by
    simp only [norm_mul, norm_pow, mul_pow, ← pow_mul, tsum_mul_left,
      xiSliceGaussianTailFourth]
  simpa only [hquad, hmass, hfourth, xiSliceGaussianTail, mul_assoc] using h

/-- The finite head and complementary product reconstruct the actual normalized Xi slice. -/
theorem xiSliceProduct_div_eq_gaussianHead_mul_tail {t : ℝ} (ht : XiC t ≠ 0)
    (H : Finset XiZeroCopy) (z : ℂ) :
    xiSliceProduct t z / xiSliceProduct t 0 = xiSliceGaussianHead t H z * xiSliceGaussianTail t H z := by
  have hs : Summable fun q : XiZeroCopy => ‖z ^ 2 * xiSliceGaussianReciprocal t q‖ := by
    simpa only [norm_mul, norm_pow] using
      (summable_norm_xiSliceGaussianReciprocal t).mul_left (‖z‖ ^ 2)
  have hp : Multipliable (fun q : XiZeroCopy => 1 + z ^ 2 * xiSliceGaussianReciprocal t q) :=
    multipliable_one_add_of_summable hs
  have hlim : Tendsto (fun F : Finset XiZeroCopy =>
      ∏ q ∈ F, (1 + z ^ 2 * xiSliceGaussianReciprocal t q)) atTop
      (𝓝 (xiSliceProduct t z / xiSliceProduct t 0)) := by
    simpa only [xiSliceGaussianReciprocal, div_eq_mul_inv] using
      tendsto_prod_one_add_sq_div_xiSliceProduct ht z
  have heq : (∏' q : XiZeroCopy, (1 + z ^ 2 * xiSliceGaussianReciprocal t q)) =
      xiSliceProduct t z / xiSliceProduct t 0 := tendsto_nhds_unique hp.hasProd hlim
  have hh : Multipliable (fun q : {q : XiZeroCopy // q ∈ H} =>
      1 + z ^ 2 * xiSliceGaussianReciprocal t q) :=
    multipliable_one_add_of_summable (hs.subtype (fun q => q ∈ H))
  have hc : Multipliable (fun q : {q : XiZeroCopy // q ∉ H} =>
      1 + z ^ 2 * xiSliceGaussianReciprocal t q) :=
    multipliable_one_add_of_summable (hs.subtype (fun q => q ∉ H))
  have hsplit := Multipliable.tprod_mul_tprod_compl
    (f := fun q : XiZeroCopy => 1 + z ^ 2 * xiSliceGaussianReciprocal t q)
    (s := (H : Set XiZeroCopy)) hh hc
  have hhead : (∏' q : (H : Set XiZeroCopy),
      (1 + z ^ 2 * xiSliceGaussianReciprocal t q)) = xiSliceGaussianHead t H z :=
    Finset.tprod_subtype' H (fun q : XiZeroCopy => 1 + z ^ 2 * xiSliceGaussianReciprocal t q)
  rw [hhead] at hsplit
  exact heq.symm.trans hsplit.symm

/-- An actual Xi slice equals a finite zero block times its Gaussian tail model, with an
explicit fourth-moment error and no approximation or zero-spacing premise. -/
theorem norm_xiSliceProduct_sub_gaussianHead_exp_le {t : ℝ} (ht : XiC t ≠ 0)
    (H : Finset XiZeroCopy) (z : ℂ) :
    ‖xiSliceProduct t z / xiSliceProduct t 0 -
      xiSliceGaussianHead t H z * Complex.exp (z ^ 2 * xiSliceGaussianTailQuadratic t H)‖ ≤
      ‖xiSliceGaussianHead t H z‖ *
        (Real.exp (2 * ‖z‖ ^ 2 * xiSliceGaussianTailMass t H) *
          (‖z‖ ^ 4 * xiSliceGaussianTailFourth t H)) := by
  rw [xiSliceProduct_div_eq_gaussianHead_mul_tail ht, ← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_xiSliceGaussianTail_sub_exp_le t H z) (norm_nonneg _)

end
end RHTower
