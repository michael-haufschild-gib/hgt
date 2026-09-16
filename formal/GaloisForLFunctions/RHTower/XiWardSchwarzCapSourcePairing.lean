import GaloisForLFunctions.RHTower.XiWardAllHeightCapAdmissibility
import GaloisForLFunctions.RHTower.XiWardSchwarzCapKernel
import GaloisForLFunctions.RHTower.XiHurwitzOrientationPositivePairedSource

/-!
# Literal completed-source pairing on canonical Ward caps

The completed prime--polar--Gamma trace is exactly odd under centered
negative conjugation on its source domain.  Combined with all-height a.e.
admissibility of a canonical lower cap, this converts the reflected pair of
*literal source values* into the Schwarz two-pole kernel times one unmodified
completed trace.  No spectral replacement, sign estimate, or limiting
argument occurs here.

The remaining cap question is consequently precise: bound the signed
height integral of this displayed source product.  The factorization itself
does not imply such a bound, since one kernel pole remains resonant.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- Literal lower point of the canonical Ward cap at height `x`. -/
def xiWardLowerCapPoint (s x : ℝ) : ℂ :=
  (x : ℂ) - (xiWardTransverseLevel s : ℂ) * I

/-- Source-faithful reflected cap pair: a lower-cap trace response plus the
conjugate reflected response. -/
def xiWardSchwarzCapSourcePair (tau s x : ℝ) : ℂ :=
  let w : ℂ := ((51 / 100 : ℝ) : ℂ) + I * (tau : ℂ)
  let z := xiWardLowerCapPoint s x
  xiWardCauchySourceWeight w z * continuedPrimeArchSourceRelativeTrace z +
    starRingEnd ℂ
      (xiWardCauchySourceWeight w (xiCenteredNegConj z) *
        continuedPrimeArchSourceRelativeTrace (xiCenteredNegConj z))

/-- Symmetric finite height cap of the literal reflected source pair. -/
def xiWardSchwarzCapSourceIntegral (tau s H : ℝ) : ℂ :=
  ∫ x in (-H)..H, xiWardSchwarzCapSourcePair tau s x

/-- The same finite cap after exact source-pair factorization.  This is the
single source functional whose cofinal signed control remains to be proved. -/
def xiWardSchwarzCapFactorIntegral (tau s H : ℝ) : ℂ :=
  ∫ x in (-H)..H,
    xiWardSchwarzCapDifference tau s x *
      continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x)

/-- Exact source-level Schwarz factorization, simultaneously at all cap
heights on the conull family of canonical levels. -/
theorem ae_forall_xiWardSchwarzCapSourcePair_eq :
    ∀ᵐ s : ℝ ∂volume, ∀ tau x : ℝ,
      xiWardSchwarzCapSourcePair tau s x =
        xiWardSchwarzCapDifference tau s x *
          continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x) := by
  filter_upwards [ae_forall_XiExplicitAdmissible_canonicalLowerCapLine] with s hs
  intro tau x
  let z := xiWardLowerCapPoint s x
  let w : ℂ := ((51 / 100 : ℝ) : ℂ) + I * (tau : ℂ)
  have hlevel := xiWardTransverseLevel_mem_Ioo s
  have hXi : XiC z ≠ 0 := by
    apply XiC_ne_zero_of_admissible (hs x)
  have hconjXi : XiC (starRingEnd ℂ z) ≠ 0 := XiC_ne_zero_conj hXi
  have hconj : XiExplicitAdmissible (starRingEnd ℂ z) := by
    apply SlabFullWidthAdmissibility.XiExplicitAdmissible_of_abs_im_lt_half
    · have him : (starRingEnd ℂ z).im = xiWardTransverseLevel s := by
        dsimp [z, xiWardLowerCapPoint]
        simp
      rw [him, abs_of_pos hlevel.1]
      exact hlevel.2
    · exact hconjXi
  have hdom : CCMContinuedCauchyDomain z :=
    ⟨(hs x).re_pos, (hs x).ne_one, (hs x).zeta_ne,
      hconj.re_pos, hconj.ne_one, hconj.zeta_ne⟩
  have hreflect : xiCenteredNegConj z =
      ((-x : ℝ) : ℂ) - (xiWardTransverseLevel s : ℂ) * I := by
    dsimp [xiCenteredNegConj, z, xiWardLowerCapPoint]
    rw [map_sub, Complex.conj_ofReal, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  unfold xiWardSchwarzCapSourcePair
  dsimp only [w, z]
  rw [continuedPrimeArchSourceRelativeTrace_negConj hdom]
  unfold xiWardSchwarzCapDifference
  rw [← hreflect]
  simp only [map_mul, map_neg]
  simp only [xiWardLowerCapPoint]
  have hzreorder : z =
      -(I * (xiWardTransverseLevel s : ℂ)) + (x : ℂ) := by
    dsimp [z, xiWardLowerCapPoint]
    ring
  rw [hzreorder]
  rw [starRingEnd_self_apply]
  ring_nf

/-- The literal finite reflected source cap is exactly the signed two-pole
source functional on the conull canonical-cap family. -/
theorem ae_forall_xiWardSchwarzCapSourceIntegral_eq :
    ∀ᵐ s : ℝ ∂volume, ∀ tau H : ℝ,
      xiWardSchwarzCapSourceIntegral tau s H =
        xiWardSchwarzCapFactorIntegral tau s H := by
  filter_upwards [ae_forall_xiWardSchwarzCapSourcePair_eq] with s hs
  intro tau H
  apply intervalIntegral.integral_congr
  intro x hx
  exact hs tau x

/-- Each finite factorized cap is a genuine interval integral on the conull
canonical-cap family; no default value for a non-integrable integral is being
used in the finite cap identity. -/
theorem ae_forall_intervalIntegrable_xiWardSchwarzCapFactor :
    ∀ᵐ s : ℝ ∂volume, ∀ tau H : ℝ,
      IntervalIntegrable
        (fun x : ℝ => xiWardSchwarzCapDifference tau s x *
          continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x))
        volume (-H) H := by
  filter_upwards [ae_forall_XiExplicitAdmissible_canonicalLowerCapLine] with s hs
  intro tau H
  have he : Continuous (xiWardLowerCapPoint s) := by
    unfold xiWardLowerCapPoint
    fun_prop
  have hcont : ContinuousOn (fun x : ℝ =>
      xiWardSchwarzCapDifference tau s x *
        logDeriv XiC (xiWardLowerCapPoint s x)) (uIcc (-H) H) := by
    apply ContinuousOn.mul
    · exact (continuous_xiWardSchwarzCapDifference tau s).continuousOn
    · intro x hx
      have hXi : XiC (xiWardLowerCapPoint s x) ≠ 0 :=
        XiC_ne_zero_of_admissible (hs x)
      have hA : AnalyticAt ℂ (logDeriv XiC) (xiWardLowerCapPoint s x) := by
        have hXiA := XiC_analytic (xiWardLowerCapPoint s x)
          (Set.mem_univ (xiWardLowerCapPoint s x))
        exact hXiA.deriv.div hXiA hXi
      exact (hA.continuousAt.comp he.continuousAt).continuousWithinAt
  refine hcont.intervalIntegrable.congr ?_
  intro x hx
  have hx' : x ∈ uIcc (-H) H := uIoc_subset_uIcc hx
  have hadm := hs x
  have hsource :
      continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x) =
        logDeriv XiC (xiWardLowerCapPoint s x) := by
    change continuedPrimeArchSourceRelativeTrace
        ((x : ℂ) - (xiWardTransverseLevel s : ℂ) * I) =
      logDeriv XiC ((x : ℂ) - (xiWardTransverseLevel s : ℂ) * I)
    rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hadm.re_pos hadm.ne_one hadm.zeta_ne]
    exact (logDeriv_XiC_eq_relativeResolventTrace
      (XiC_ne_zero_of_admissible hadm)).symm
  change xiWardSchwarzCapDifference tau s x *
      logDeriv XiC (xiWardLowerCapPoint s x) =
    xiWardSchwarzCapDifference tau s x *
      continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x)
  rw [hsource]

end

end RHTower
