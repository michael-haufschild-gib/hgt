import GaloisForLFunctions.RHTower.CompletedZetaGrowth
import GaloisForLFunctions.RHTower.SoninPerronSupportTransfer

/-!
# The completed xi theta source is an exact two-sided seam

Mathlib constructs `completedRiemannZeta₀` as half the Mellin transform of the modified even theta
kernel `modifiedEvenKernel`.  In logarithmic Mellin coordinates the critical normalization is

`h(u) = exp(u/4) * modifiedEvenKernel(exp u)`.

The weight-`1/2` theta functional equation becomes literal reflection invariance `h(-u)=h(u)`.
The positive theta series is strictly positive, so `h` is nonzero on both open half-lines.  Hence
the actual completed source is not lower-supported at any finite threshold.

The correct one-sided object is its positive half `h₊`; the full source splits pointwise as
`h(u)=h₊(u)+h₊(-u)`.  Thus the reflected half is not an optional defect.  It is the exact seam
forced by completion.
-/

open Complex Real MeasureTheory Set Filter Topology HurwitzZeta
open scoped ENNReal Topology

noncomputable section

namespace RHTower

/-- The logarithmically normalized physical theta source of `completedRiemannZeta₀`. -/
def xiThetaLogSource (u : ℝ) : ℂ :=
  (Real.exp (u / 4) : ℂ) * modifiedEvenKernel (Real.exp u)

/-- On the positive physical half, the modified kernel is exactly the ordinary theta tail. -/
theorem modifiedEvenKernel_of_one_lt {t : ℝ} (ht : 1 < t) :
    modifiedEvenKernel t = (((evenKernel 0 t - 1 : ℝ)) : ℂ) := by
  rw [modifiedEvenKernel, WeakFEPair.f_modif, Pi.add_apply,
    indicator_of_mem (mem_Ioi.mpr ht), indicator_of_notMem (notMem_Ioo_of_ge ht.le), add_zero]
  simp [hurwitzEvenFEPair, Function.comp_def]

/-- The positive theta tail is strictly positive at every positive physical scale. -/
theorem evenKernel_zero_sub_one_pos {t : ℝ} (ht : 0 < t) :
    0 < evenKernel 0 t - 1 := by
  have hs := hasSum_nat_cosKernel₀ 0 ht
  have hs' : HasSum (fun n : ℕ =>
      2 * Real.exp (-Real.pi * (n + 1) ^ 2 * t))
      (cosKernel (0 : UnitAddCircle) t - 1) := by
    simpa using hs
  have hpos : 0 < ∑' n : ℕ, 2 * Real.exp (-Real.pi * (n + 1) ^ 2 * t) :=
    hs'.summable.tsum_pos (fun _ => by positivity) 0 (by positivity)
  rw [hs'.tsum_eq] at hpos
  have heq := congrFun evenKernel_eq_cosKernel_of_zero t
  rw [heq]
  exact hpos

/-- The modified theta kernel's reciprocal law in exponential coordinates. -/
theorem modifiedEvenKernel_exp_neg (u : ℝ) :
    modifiedEvenKernel (Real.exp (-u)) =
      (Real.exp (u / 2) : ℂ) * modifiedEvenKernel (Real.exp u) := by
  have h := (hurwitzEvenFEPair 0).hf_modif_FE (Real.exp u) (Real.exp_pos u)
  rw [one_div, ← Real.exp_neg] at h
  have hgf : (hurwitzEvenFEPair 0).g_modif = (hurwitzEvenFEPair 0).f_modif := by
    funext x
    rw [WeakFEPair.g_modif, WeakFEPair.f_modif]
    simp [hurwitzEvenFEPair, Function.comp_def, evenKernel_eq_cosKernel_of_zero]
  have hrpow : Real.exp u ^ (1 / 2 : ℝ) = Real.exp (u / 2) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp]
    congr 1
    ring
  rw [hgf, show (hurwitzEvenFEPair 0).ε = 1 from rfl,
    show (hurwitzEvenFEPair 0).k = 1 / 2 from rfl,
    one_mul, hrpow, smul_eq_mul] at h
  simpa [modifiedEvenKernel] using h

/-- **Completion becomes a fixed-point constraint.**  The logarithmic theta source is even. -/
theorem xiThetaLogSource_neg (u : ℝ) : xiThetaLogSource (-u) = xiThetaLogSource u := by
  rw [xiThetaLogSource, xiThetaLogSource, neg_div,
    modifiedEvenKernel_exp_neg]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

@[simp] theorem xiThetaLogSource_zero : xiThetaLogSource 0 = 0 := by
  simp [xiThetaLogSource, modifiedEvenKernel, WeakFEPair.f_modif]

/-- The explicit positive-half formula in logarithmic coordinates. -/
def xiThetaPositiveFormula (u : ℝ) : ℂ :=
  (Real.exp (u / 4) : ℂ) * (((evenKernel 0 (Real.exp u) - 1 : ℝ)) : ℂ)

theorem xiThetaLogSource_eq_positiveFormula {u : ℝ} (hu : 0 < u) :
    xiThetaLogSource u = xiThetaPositiveFormula u := by
  have ht : 1 < Real.exp u := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hu
  rw [xiThetaLogSource, modifiedEvenKernel_of_one_lt ht]
  rfl

theorem continuous_xiThetaPositiveFormula : Continuous xiThetaPositiveFormula := by
  have hk : Continuous (fun u : ℝ => evenKernel 0 (Real.exp u)) := by
    rw [continuous_iff_continuousAt]
    intro u
    have hwithin := continuousOn_evenKernel (0 : UnitAddCircle)
      (Real.exp u) (Real.exp_pos u)
    have hat : ContinuousAt (evenKernel 0) (Real.exp u) :=
      hwithin.continuousAt (isOpen_Ioi.mem_nhds (Real.exp_pos u))
    exact hat.comp Real.continuous_exp.continuousAt
  unfold xiThetaPositiveFormula
  have he : Continuous (fun u : ℝ => ((Real.exp (u / 4) : ℝ) : ℂ)) := by fun_prop
  exact he.mul (continuous_ofReal.comp (hk.sub continuous_const))

theorem continuousOn_xiThetaLogSource_pos : ContinuousOn xiThetaLogSource (Ioi 0) := by
  refine continuous_xiThetaPositiveFormula.continuousOn.congr ?_
  intro u hu
  exact xiThetaLogSource_eq_positiveFormula hu

theorem continuousOn_xiThetaLogSource_neg : ContinuousOn xiThetaLogSource (Iio 0) := by
  have hc : Continuous (fun u : ℝ => xiThetaPositiveFormula (-u)) :=
    continuous_xiThetaPositiveFormula.comp (by fun_prop)
  refine hc.continuousOn.congr ?_
  intro u hu
  calc
    xiThetaLogSource u = xiThetaLogSource (-u) := (xiThetaLogSource_neg u).symm
    _ = xiThetaPositiveFormula (-u) :=
      xiThetaLogSource_eq_positiveFormula (neg_pos.mpr hu)

/-- The completed logarithmic source is nonzero away from the reflection point. -/
theorem xiThetaLogSource_ne_zero {u : ℝ} (hu : u ≠ 0) : xiThetaLogSource u ≠ 0 := by
  rcases lt_trichotomy u 0 with hneg | hzero | hpos
  · have hp : xiThetaLogSource (-u) ≠ 0 := by
      rw [xiThetaLogSource_eq_positiveFormula (neg_pos.mpr hneg)]
      unfold xiThetaPositiveFormula
      apply mul_ne_zero
      · exact_mod_cast (Real.exp_pos ((-u) / 4)).ne'
      · exact Complex.ofReal_ne_zero.mpr
          (ne_of_gt (evenKernel_zero_sub_one_pos (Real.exp_pos (-u))))
    rwa [xiThetaLogSource_neg] at hp
  · exact (hu hzero).elim
  · rw [xiThetaLogSource_eq_positiveFormula hpos]
    unfold xiThetaPositiveFormula
    apply mul_ne_zero
    · exact_mod_cast (Real.exp_pos (u / 4)).ne'
    · exact Complex.ofReal_ne_zero.mpr
        (ne_of_gt (evenKernel_zero_sub_one_pos (Real.exp_pos u)))

/-! ## The canonical one-sided source and reflected seam -/

/-- The positive logarithmic half of the completed theta source. -/
def xiThetaPositiveSource (u : ℝ) : ℂ :=
  (Ioi (0 : ℝ)).indicator xiThetaLogSource u

/-- The reflected half-source. -/
def xiThetaReflectedSource (u : ℝ) : ℂ := xiThetaPositiveSource (-u)

/-- The positive half discharges the existing lower-support interface at threshold `0`. -/
theorem xiThetaPositiveSource_hasAELowerSupport :
    HasAELowerSupport xiThetaPositiveSource 0 := by
  filter_upwards [] with u
  intro hu
  rw [xiThetaPositiveSource, indicator_of_notMem]
  simpa only [mem_Ioi, not_lt] using hu.le

/-- **Exact completed-source seam.**  The full theta source is the sum of its lower-supported
positive half and the reflected half.  The equality is pointwise, including the fixed point where
the modified kernel was defined to vanish. -/
theorem xiThetaLogSource_split (u : ℝ) :
    xiThetaLogSource u = xiThetaPositiveSource u + xiThetaReflectedSource u := by
  rcases lt_trichotomy u 0 with hneg | hzero | hpos
  · have hnegmem : u ∉ Ioi (0 : ℝ) := by
      simpa only [mem_Ioi, not_lt] using hneg.le
    have hposmem : -u ∈ Ioi (0 : ℝ) := neg_pos.mpr hneg
    rw [xiThetaPositiveSource, xiThetaReflectedSource, xiThetaPositiveSource,
      indicator_of_notMem hnegmem, indicator_of_mem hposmem, zero_add,
      xiThetaLogSource_neg]
  · subst u
    simp [xiThetaPositiveSource, xiThetaReflectedSource]
  · have hposmem : u ∈ Ioi (0 : ℝ) := hpos
    have hnegmem : -u ∉ Ioi (0 : ℝ) := by
      simpa only [mem_Ioi, not_lt] using neg_nonpos.mpr hpos.le
    rw [xiThetaPositiveSource, xiThetaReflectedSource, xiThetaPositiveSource,
      indicator_of_mem hposmem, indicator_of_notMem hnegmem, add_zero]

/-- The reflected seam is the negative-half truncation of the full source. -/
theorem xiThetaReflectedSource_eq (u : ℝ) :
    xiThetaReflectedSource u = (Iio (0 : ℝ)).indicator xiThetaLogSource u := by
  rcases lt_trichotomy u 0 with hneg | hzero | hpos
  · have hnposmem : -u ∈ Ioi (0 : ℝ) := neg_pos.mpr hneg
    have hnegmem : u ∈ Iio (0 : ℝ) := hneg
    simp only [xiThetaReflectedSource]
    rw [xiThetaPositiveSource,
      indicator_of_mem hnposmem, indicator_of_mem hnegmem,
      xiThetaLogSource_neg]
  · subst u
    simp [xiThetaReflectedSource, xiThetaPositiveSource]
  · have hnmem : -u ∉ Ioi (0 : ℝ) := by
      simpa only [mem_Ioi, not_lt] using neg_nonpos.mpr hpos.le
    have hpmem : u ∉ Iio (0 : ℝ) := by
      simpa only [mem_Iio, not_lt] using hpos.le
    simp only [xiThetaReflectedSource]
    rw [xiThetaPositiveSource, indicator_of_notMem hnmem,
      indicator_of_notMem hpmem]

/-- **The completed target source is never lower-supported.**  For every finite threshold `τ`,
the actual logarithmic theta source has nonzero values on an open interval below `τ`.  This rules
out feeding the full completed source into the Sonin lower-support transfer. -/
theorem xiThetaLogSource_not_hasAELowerSupport (τ : ℝ) :
    ¬ HasAELowerSupport xiThetaLogSource τ := by
  intro hsupp
  let b : ℝ := min (τ - 1) (-1)
  let a : ℝ := b - 1
  have hab : a < b := by simp [a]
  have hbτ : b < τ := by
    have hle : b ≤ τ - 1 := min_le_left _ _
    linarith
  have hb0 : b < 0 := by
    have hle : b ≤ -1 := min_le_right _ _
    linarith
  have hae : xiThetaLogSource =ᵐ[volume.restrict (Ioo a b)] (fun _ => (0 : ℂ)) := by
    change ∀ᵐ u : ℝ ∂volume.restrict (Ioo a b), xiThetaLogSource u = 0
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hsupp] with u hu
    intro humem
    exact hu (lt_trans humem.2 hbτ)
  have hcont : ContinuousOn xiThetaLogSource (Ioo a b) :=
    continuousOn_xiThetaLogSource_neg.mono (fun _ hu => lt_trans hu.2 hb0)
  have heq : EqOn xiThetaLogSource (fun _ => (0 : ℂ)) (Ioo a b) :=
    Measure.eqOn_open_of_ae_eq hae isOpen_Ioo hcont continuous_const.continuousOn
  let u : ℝ := (a + b) / 2
  have huab : u ∈ Ioo a b := by
    constructor <;> dsimp [u] <;> linarith
  have hu0 : u ≠ 0 := by
    have : u < 0 := lt_trans huab.2 hb0
    exact ne_of_lt this
  exact xiThetaLogSource_ne_zero hu0 (heq huab)

end RHTower
