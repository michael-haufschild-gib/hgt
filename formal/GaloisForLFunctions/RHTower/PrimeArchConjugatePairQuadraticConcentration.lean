import GaloisForLFunctions.RHTower.PrimeArchHighFrequencyAccretivity
import GaloisForLFunctions.HTGeometry.PoissonKernelIntegrals

/-!
# Quadratic concentration of an off-line conjugate pair

One line-conjugate relative-resolvent pair is a difference of two normalized Poisson densities
across frequency.  Its signed frequency mass is exactly zero, so first-moment averaging is blind to
the pair.  Squaring before integration retains the mixed incidence and gives the exact energy

`π y² / (b (b² - y²))`,

where `b` is the zero's transverse displacement and `0 < y < b` is probe height.  This energy
diverges as the probe approaches the off-line displacement.  Thus the source spikes left by false
RH are concentration defects: cancellation kills their signed mass but not their quadratic energy.

The result is a new bridge, not an RH proof.  Closing Route Q now requires an arithmetic-side finite
quadratic-energy ceiling which retains this pair profile.  The same concentration primitive is the
candidate cross-route invariant for shifted-Hankel Christoffel walls in Route U.
-/

open Complex Filter MeasureTheory Topology

namespace RHTower

noncomputable section

/-- Difference of the two Poisson densities in a line-conjugate off-line resolvent pair. -/
def lineConjugateCauchyConcentrationProfile (b y t : ℝ) : ℝ :=
  (b - y) / ((b - y) ^ (2 : ℕ) + t ^ (2 : ℕ)) -
    (b + y) / ((b + y) ^ (2 : ℕ) + t ^ (2 : ℕ))

/-- The signed off-line pair profile is integrable across frequency. -/
theorem integrable_lineConjugateCauchyConcentrationProfile
    {b y : ℝ} (hy : 0 < y) (hyb : y < b) :
    Integrable (lineConjugateCauchyConcentrationProfile b y) := by
  have ha : 0 < b - y := sub_pos.mpr hyb
  have hbeta : 0 < b + y := by linarith
  have hleft :=
    (GaloisForLFunctions.HTGeometry.integrable_inv_sq_add_sq ha).const_mul (b - y)
  have hright :=
    (GaloisForLFunctions.HTGeometry.integrable_inv_sq_add_sq hbeta).const_mul (b + y)
  refine (hleft.sub hright).congr (Filter.Eventually.of_forall fun t => ?_)
  rfl

/-- **First-moment blindness.**  The two Poisson lobes have equal mass, so the signed frequency
integral of every off-line conjugate-pair profile vanishes exactly. -/
theorem integral_lineConjugateCauchyConcentrationProfile_eq_zero
    {b y : ℝ} (hy : 0 < y) (hyb : y < b) :
    (∫ t : ℝ, lineConjugateCauchyConcentrationProfile b y t) = 0 := by
  have ha : 0 < b - y := sub_pos.mpr hyb
  have hbeta : 0 < b + y := by linarith
  change (∫ t : ℝ,
    (b - y) * (((b - y) ^ (2 : ℕ) + t ^ (2 : ℕ))⁻¹) -
      (b + y) * (((b + y) ^ (2 : ℕ) + t ^ (2 : ℕ))⁻¹)) = 0
  rw [integral_sub]
  · rw [integral_const_mul, integral_const_mul,
      GaloisForLFunctions.HTGeometry.integral_inv_sq_add_sq ha,
      GaloisForLFunctions.HTGeometry.integral_inv_sq_add_sq hbeta]
    field_simp [ne_of_gt ha, ne_of_gt hbeta]
    ring
  · exact (GaloisForLFunctions.HTGeometry.integrable_inv_sq_add_sq ha).const_mul (b - y)
  · exact (GaloisForLFunctions.HTGeometry.integrable_inv_sq_add_sq hbeta).const_mul (b + y)

/-- The squared off-line pair profile is integrable across frequency. -/
theorem integrable_sq_lineConjugateCauchyConcentrationProfile
    {b y : ℝ} (hy : 0 < y) (hyb : y < b) :
    Integrable (fun t : ℝ => lineConjugateCauchyConcentrationProfile b y t ^ (2 : ℕ)) := by
  let a := b - y
  let c := b + y
  have ha : 0 < a := by dsimp [a]; linarith
  have hc : 0 < c := by dsimp [c]; linarith
  have hA :=
    (GaloisForLFunctions.HTGeometry.integrable_inv_sq_add_sq_sq ha).const_mul (a ^ (2 : ℕ))
  have hC :=
    (GaloisForLFunctions.HTGeometry.integrable_inv_sq_add_sq_sq hc).const_mul (c ^ (2 : ℕ))
  have hcross :=
    (GaloisForLFunctions.HTGeometry.integrable_inv_sq_add_sq_mul ha hc).const_mul
      (2 * a * c)
  refine (hA.add hC |>.sub hcross).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply, Pi.sub_apply]
  dsimp only [lineConjugateCauchyConcentrationProfile, a, c]
  have h1 : (b - y) ^ (2 : ℕ) + t ^ (2 : ℕ) ≠ 0 := by positivity
  have h2 : (b + y) ^ (2 : ℕ) + t ^ (2 : ℕ) ≠ 0 := by positivity
  field_simp [h1, h2]
  ring

/-- **Exact quadratic concentration law.**  Squaring retains the mixed incidence canceled by the
signed integral.  The resulting energy is an explicit positive rational function of probe height
and off-line displacement. -/
theorem integral_sq_lineConjugateCauchyConcentrationProfile
    {b y : ℝ} (hy : 0 < y) (hyb : y < b) :
    (∫ t : ℝ, lineConjugateCauchyConcentrationProfile b y t ^ (2 : ℕ)) =
      Real.pi * y ^ (2 : ℕ) / (b * (b ^ (2 : ℕ) - y ^ (2 : ℕ))) := by
  let a := b - y
  let c := b + y
  have ha : 0 < a := by dsimp [a]; linarith
  have hc : 0 < c := by dsimp [c]; linarith
  have hA := GaloisForLFunctions.HTGeometry.integrable_inv_sq_add_sq_sq ha
  have hC := GaloisForLFunctions.HTGeometry.integrable_inv_sq_add_sq_sq hc
  have hcross := GaloisForLFunctions.HTGeometry.integrable_inv_sq_add_sq_mul ha hc
  have hexpand : ∀ t : ℝ,
      lineConjugateCauchyConcentrationProfile b y t ^ (2 : ℕ) =
        a ^ (2 : ℕ) * ((a ^ (2 : ℕ) + t ^ (2 : ℕ)) ^ (2 : ℕ))⁻¹ +
          c ^ (2 : ℕ) * ((c ^ (2 : ℕ) + t ^ (2 : ℕ)) ^ (2 : ℕ))⁻¹ -
            (2 * a * c) * (((a ^ (2 : ℕ) + t ^ (2 : ℕ)) * (c ^ (2 : ℕ) + t ^ (2 : ℕ)))⁻¹) := by
    intro t
    dsimp only [lineConjugateCauchyConcentrationProfile, a, c]
    have h1 : (b - y) ^ (2 : ℕ) + t ^ (2 : ℕ) ≠ 0 := by positivity
    have h2 : (b + y) ^ (2 : ℕ) + t ^ (2 : ℕ) ≠ 0 := by positivity
    field_simp [h1, h2]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hexpand)]
  have hsplit :
      (∫ t : ℝ,
        a ^ (2 : ℕ) * ((a ^ (2 : ℕ) + t ^ (2 : ℕ)) ^ (2 : ℕ))⁻¹ +
          c ^ (2 : ℕ) * ((c ^ (2 : ℕ) + t ^ (2 : ℕ)) ^ (2 : ℕ))⁻¹ -
            (2 * a * c) * (((a ^ (2 : ℕ) + t ^ (2 : ℕ)) * (c ^ (2 : ℕ) + t ^ (2 : ℕ)))⁻¹)) =
        (∫ t : ℝ, a ^ (2 : ℕ) * ((a ^ (2 : ℕ) + t ^ (2 : ℕ)) ^ (2 : ℕ))⁻¹) +
          (∫ t : ℝ, c ^ (2 : ℕ) * ((c ^ (2 : ℕ) + t ^ (2 : ℕ)) ^ (2 : ℕ))⁻¹) -
            (∫ t : ℝ,
              (2 * a * c) * (((a ^ (2 : ℕ) + t ^ (2 : ℕ)) * (c ^ (2 : ℕ) + t ^ (2 : ℕ)))⁻¹)) := by
    calc
      _ = (∫ t : ℝ,
            a ^ (2 : ℕ) * ((a ^ (2 : ℕ) + t ^ (2 : ℕ)) ^ (2 : ℕ))⁻¹ +
              c ^ (2 : ℕ) * ((c ^ (2 : ℕ) + t ^ (2 : ℕ)) ^ (2 : ℕ))⁻¹) -
            (∫ t : ℝ,
              (2 * a * c) * (((a ^ (2 : ℕ) + t ^ (2 : ℕ)) * (c ^ (2 : ℕ) + t ^ (2 : ℕ)))⁻¹)) := by
          simpa only [Pi.add_apply, Pi.sub_apply] using
            integral_sub
              ((hA.const_mul (a ^ (2 : ℕ))).add (hC.const_mul (c ^ (2 : ℕ))))
              (hcross.const_mul (2 * a * c))
      _ = _ := by
        rw [integral_add (hA.const_mul (a ^ (2 : ℕ))) (hC.const_mul (c ^ (2 : ℕ)))]
  have hane : a ≠ 0 := ne_of_gt ha
  have hcne : c ≠ 0 := ne_of_gt hc
  have hacpos : 0 < a + c := add_pos ha hc
  have hAred : a ^ (2 : ℕ) * (Real.pi / (2 * a ^ (3 : ℕ))) = Real.pi / (2 * a) := by
    field_simp [hane]
  have hCred : c ^ (2 : ℕ) * (Real.pi / (2 * c ^ (3 : ℕ))) = Real.pi / (2 * c) := by
    field_simp [hcne]
  have hcrossRed :
      (2 * a * c) * (Real.pi / (a * c * (a + c))) = 2 * Real.pi / (a + c) := by
    field_simp [hane, hcne, ne_of_gt hacpos]
  rw [hsplit, integral_const_mul, integral_const_mul, integral_const_mul,
    GaloisForLFunctions.HTGeometry.integral_inv_sq_add_sq_sq ha,
    GaloisForLFunctions.HTGeometry.integral_inv_sq_add_sq_sq hc,
    GaloisForLFunctions.HTGeometry.integral_inv_sq_add_sq_mul' ha hc,
    hAred, hCred, hcrossRed]
  dsimp only [a, c]
  have hb : 0 < b := hy.trans hyb
  have hsqdiff : 0 < b ^ (2 : ℕ) - y ^ (2 : ℕ) := by nlinarith
  have hminus : b - y ≠ 0 := ne_of_gt (sub_pos.mpr hyb)
  have hplus : b + y ≠ 0 := ne_of_gt (by linarith)
  field_simp [ne_of_gt hb, ne_of_gt hsqdiff, hminus, hplus]
  ring

/-- **Off-line wall blow-up.**  Quadratic frequency energy diverges when probe height approaches
the transverse displacement from below, despite the signed mass remaining identically zero. -/
theorem tendsto_integral_sq_lineConjugateCauchyConcentrationProfile_at_offLineWall
    {b : ℝ} (hb : 0 < b) :
    Tendsto
      (fun y : ℝ => ∫ t : ℝ,
        lineConjugateCauchyConcentrationProfile b y t ^ (2 : ℕ))
      (𝓝[<] b) atTop := by
  let numerator : ℝ → ℝ := fun y => Real.pi * y ^ (2 : ℕ)
  let denominator : ℝ → ℝ := fun y => b * (b ^ (2 : ℕ) - y ^ (2 : ℕ))
  have hnum : Tendsto numerator (𝓝[<] b) (nhds (Real.pi * b ^ (2 : ℕ))) := by
    apply (show ContinuousAt numerator b by fun_prop).tendsto.mono_left
    exact nhdsWithin_le_nhds
  have hnumPos : 0 < Real.pi * b ^ (2 : ℕ) := mul_pos Real.pi_pos (sq_pos_of_pos hb)
  have hden0 : Tendsto denominator (𝓝[<] b) (nhds 0) := by
    have h : Tendsto denominator (𝓝[<] b) (𝓝 (denominator b)) :=
      (show ContinuousAt denominator b by fun_prop).tendsto.mono_left nhdsWithin_le_nhds
    simpa only [denominator, sub_self, mul_zero] using h
  have hyPos : ∀ᶠ y : ℝ in 𝓝[<] b, 0 < y :=
    nhdsWithin_le_nhds (eventually_gt_nhds hb)
  have hdenPos : ∀ᶠ y : ℝ in 𝓝[<] b, 0 < denominator y := by
    filter_upwards [hyPos, self_mem_nhdsWithin] with y hy hylt
    dsimp only [denominator]
    have hsum : 0 < b + y := by linarith
    have hdiff : 0 < b - y := sub_pos.mpr hylt
    rw [show b ^ (2 : ℕ) - y ^ (2 : ℕ) = (b - y) * (b + y) by ring]
    exact mul_pos hb (mul_pos hdiff hsum)
  have hdenWithin : Tendsto denominator (𝓝[<] b) (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      denominator hden0 hdenPos
  have hdenInv : Tendsto (fun y => (denominator y)⁻¹) (𝓝[<] b) atTop :=
    tendsto_inv_nhdsGT_zero.comp hdenWithin
  have hquot : Tendsto (fun y => numerator y * (denominator y)⁻¹)
      (𝓝[<] b) atTop :=
    hnum.pos_mul_atTop hnumPos hdenInv
  apply hquot.congr'
  filter_upwards [hyPos, self_mem_nhdsWithin] with y hy hylt
  rw [integral_sq_lineConjugateCauchyConcentrationProfile hy hylt]
  rfl

/-- **Universal boundary residue.**  The divergence has exactly one inverse-width quantum:
multiplying quadratic energy by the remaining distance to the off-line wall converges to `π / 2`,
independently of the zero height and transverse displacement.  This is the scale-normalized charge
that survives when the Poisson lobe collapses to a boundary atom. -/
theorem tendsto_boundaryWidth_mul_integral_sq_lineConjugateCauchyConcentrationProfile
    {b : ℝ} (hb : 0 < b) :
    Tendsto
      (fun y : ℝ => (b - y) *
        (∫ t : ℝ, lineConjugateCauchyConcentrationProfile b y t ^ (2 : ℕ)))
      (𝓝[<] b) (𝓝 (Real.pi / 2)) := by
  let reduced : ℝ → ℝ := fun y => Real.pi * y ^ (2 : ℕ) / (b * (b + y))
  have hden : b * (b + b) ≠ 0 := by positivity
  have hvalue : reduced b = Real.pi / 2 := by
    dsimp only [reduced]
    field_simp [hden, ne_of_gt hb]
    ring
  have hreduced : Tendsto reduced (𝓝[<] b) (𝓝 (Real.pi / 2)) := by
    have hcont : ContinuousAt reduced b := by
      dsimp only [reduced]
      fun_prop
    rw [← hvalue]
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply hreduced.congr'
  have hyPos : ∀ᶠ y : ℝ in 𝓝[<] b, 0 < y :=
    nhdsWithin_le_nhds (eventually_gt_nhds hb)
  filter_upwards [hyPos, self_mem_nhdsWithin] with y hy hylt
  rw [integral_sq_lineConjugateCauchyConcentrationProfile hy hylt]
  dsimp only [reduced]
  have hminus : b - y ≠ 0 := ne_of_gt (sub_pos.mpr hylt)
  have hbne : b ≠ 0 := ne_of_gt hb
  rw [show b ^ (2 : ℕ) - y ^ (2 : ℕ) = (b - y) * (b + y) by ring]
  field_simp [hminus, hbne]

/-- **Xi pair identification.**  On a frequency line through zero height `A`, the imaginary part
of the exact line-conjugate relative-resolvent pair is precisely the concentration profile above.
The zero height translates the profile but does not change its mass or quadratic energy. -/
theorem relativeResolvent_conj_pair_im_eq_lineConjugateCauchyConcentrationProfile
    (A b y t : ℝ) (hy : 0 < y) (hyb : y < b) :
    let a : ℂ := (A : ℂ) + (b : ℂ) * I
    let z : ℂ := ((A + t : ℝ) : ℂ) + (y : ℂ) * I
    ((a⁻¹ - (a - z)⁻¹) +
      (((starRingEnd ℂ) a)⁻¹ - ((starRingEnd ℂ) a - z)⁻¹)).im =
        lineConjugateCauchyConcentrationProfile b y t := by
  dsimp only
  have ha : (A : ℂ) + (b : ℂ) * I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hza : ((A + t : ℝ) : ℂ) + (y : ℂ) * I ≠ (A : ℂ) + (b : ℂ) * I := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hzac : ((A + t : ℝ) : ℂ) + (y : ℂ) * I ≠
      (starRingEnd ℂ) ((A : ℂ) + (b : ℂ) * I) := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hminusPos : 0 < b - y := sub_pos.mpr hyb
  have hplusPos : 0 < b + y := by linarith
  have h1 : (b - y) ^ (2 : ℕ) + t ^ (2 : ℕ) ≠ 0 := by nlinarith [sq_pos_of_pos hminusPos]
  have h2 : (b + y) ^ (2 : ℕ) + t ^ (2 : ℕ) ≠ 0 := by nlinarith [sq_pos_of_pos hplusPos]
  have hybNeg : y - b < 0 := sub_neg.mpr hyb
  have hybPos : 0 < y + b := by linarith
  have hleft : t ^ (2 : ℕ) + (y - b) ^ (2 : ℕ) ≠ 0 := by nlinarith [sq_pos_of_neg hybNeg]
  have hright : t ^ (2 : ℕ) + (y + b) ^ (2 : ℕ) ≠ 0 := by nlinarith [sq_pos_of_pos hybPos]
  have hformula :
      -2 * y * (t ^ (2 : ℕ) + y ^ (2 : ℕ) - b ^ (2 : ℕ)) /
          ((t ^ (2 : ℕ) + (y - b) ^ (2 : ℕ)) * (t ^ (2 : ℕ) + (y + b) ^ (2 : ℕ))) =
        lineConjugateCauchyConcentrationProfile b y t := by
    dsimp only [lineConjugateCauchyConcentrationProfile]
    field_simp [h1, h2, hleft, hright]
    ring
  have hAt : A + t - A = t := by ring
  rw [relativeResolvent_conj_pair_im_formula _ _ ha hza hzac]
  simpa only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
    zero_mul, sub_zero, add_im, mul_im, zero_add, add_zero, mul_one, hAt,
    sub_neg_eq_add] using hformula

end

end RHTower
