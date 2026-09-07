import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAngularSeriesSmooth
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinFullCuspSectorAssembly

/-!
# Joint spatial regularity of the literal completed Eisenstein cusp legs

The full signed Fourier tails are the smooth infinite family already bounded
on every positive height interval. Both Maass words are finite combinations
of these tails. The two Weyl constant terms are smooth on the same domain.
This certifies all three literal cusp legs without a spectral half-plane
assumption and without substituting a finite Fourier truncation.
-/

open Complex Real Set Filter Topology
open scoped ContDiff
namespace RHTower.D4BMAngularSeries
noncomputable section

/-- Exact equality with the pre-existing signed infinite Whittaker tail. -/
theorem signedTail_eq_value (u nu : ℂ) (negative : Bool) (j m : ℕ)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    d4BMCompletedEisensteinSignedSqrtWhittakerTail u nu negative (z 0) j m (z 1) =
      value u nu ((m : ℝ) + 1 / 2) j negative z := by
  unfold d4BMCompletedEisensteinSignedSqrtWhittakerTail value
  apply tsum_congr
  intro N
  dsimp only [term, coefficient]
  have hpow : Real.rpow (z 1) ((m : ℝ) + 1 / 2) = (z 1) ^ m * Real.sqrt (z 1) := by
    change (z 1) ^ ((m : ℝ) + 1 / 2) = _
    rw [Real.rpow_add hz, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  rw [hpow]
  push_cast
  ring

/-- All signed tails are jointly smooth in horizontal position and positive height. -/
theorem signedTail_contDiffOn (u nu : ℂ) (negative : Bool) (j m : ℕ) :
    ContDiffOn ℝ ∞ (fun z : Fin 2 → ℝ =>
      d4BMCompletedEisensteinSignedSqrtWhittakerTail u nu negative (z 0) j m (z 1)) domain :=
  (value_contDiffOn u nu ((m : ℝ) + 1 / 2) j negative).congr
    fun z hz => signedTail_eq_value u nu negative j m z hz

/-- Each exact two-step Maass word inherits joint smoothness from its shifted tails. -/
theorem phasedMaassWord_contDiffOn (raise negative : Bool) (u nu : ℂ) :
    ContDiffOn ℝ ∞ (fun z : Fin 2 → ℝ =>
      d4BMCompletedEisensteinPhasedMaassWord raise negative u nu (z 0) (z 1)) domain := by
  unfold d4BMCompletedEisensteinPhasedMaassWord
  repeat first
    | apply ContDiffOn.add
    | apply ContDiffOn.sub
    | apply ContDiffOn.mul
    | exact contDiffOn_const
    | exact signedTail_contDiffOn _ _ _ _ _

/-- The complete signed scalar tail is smooth. -/
theorem fullSignedZeroWord_contDiffOn (u nu : ℂ) :
    ContDiffOn ℝ ∞ (fun z : Fin 2 → ℝ =>
      d4BMCompletedEisensteinFullSignedZeroWord u nu (z 0) (z 1)) domain :=
  (signedTail_contDiffOn u nu false 0 0).add (signedTail_contDiffOn u nu true 0 0)

/-- The complete signed raised tail is smooth. -/
theorem fullSignedRaiseWord_contDiffOn (u nu : ℂ) :
    ContDiffOn ℝ ∞ (fun z : Fin 2 → ℝ =>
      d4BMCompletedEisensteinFullSignedRaiseWord u nu (z 0) (z 1)) domain :=
  (phasedMaassWord_contDiffOn true false u nu).add (phasedMaassWord_contDiffOn false true u nu)

/-- The complete signed lowered tail is smooth. -/
theorem fullSignedLowerWord_contDiffOn (u nu : ℂ) :
    ContDiffOn ℝ ∞ (fun z : Fin 2 → ℝ =>
      d4BMCompletedEisensteinFullSignedLowerWord u nu (z 0) (z 1)) domain :=
  (phasedMaassWord_contDiffOn false false u nu).add (phasedMaassWord_contDiffOn true true u nu)

/-- Every complex height monomial is smooth at positive heights. -/
theorem height_cpow_contDiffOn (w : ℂ) (m : WithTop ℕ∞) :
    ContDiffOn ℝ m (fun z : Fin 2 → ℝ => (z 1 : ℂ) ^ w) domain := by
  intro z hz
  have hY : ContDiffAt ℝ m (fun v : Fin 2 → ℝ => v 1) z :=
    (show (Fin 2 → ℝ) →L[ℝ] ℝ from ContinuousLinearMap.proj 1).contDiff.contDiffAt
  have hlog := (Real.contDiffAt_log.mpr (show z 1 ≠ 0 from hz.ne')).comp z hY
  have hlogC := Complex.ofRealCLM.contDiff.contDiffAt.comp z hlog
  have hs := (hlogC.mul (contDiffAt_const (c := w))).cexp
  have he : (fun v : Fin 2 → ℝ => (v 1 : ℂ) ^ w) =ᶠ[𝓝 z]
      (fun v => Complex.exp ((Real.log (v 1) : ℂ) * w)) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with v hv
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hv.ne'),
      ← Complex.ofReal_log hv.le]
  exact (hs.congr_of_eventuallyEq he).contDiffWithinAt

/-- Each literal Weyl term has joint spatial regularity. -/
theorem cuspConstantTerm_contDiffOn (kind : D4BMCompletedEisensteinCuspLegKind)
    (u : ℂ) (epsilon : Bool) :
    ContDiffOn ℝ ∞ (fun z : Fin 2 → ℝ =>
      d4BMCompletedEisensteinCuspConstantTerm kind u epsilon (z 1)) domain :=
  contDiffOn_const.mul (height_cpow_contDiffOn (d4BMCompletedEisensteinCuspWeylExponent u epsilon) ∞)

/-- The two literal Weyl terms together are smooth. -/
theorem cuspConstantPart_contDiffOn (kind : D4BMCompletedEisensteinCuspLegKind) (u : ℂ) :
    ContDiffOn ℝ ∞ (fun z : Fin 2 → ℝ =>
      d4BMCompletedEisensteinCuspConstantPart kind u (z 1)) domain :=
  (cuspConstantTerm_contDiffOn kind u false).add (cuspConstantTerm_contDiffOn kind u true)

/-- All three complete cusp tail kinds are jointly smooth. -/
theorem cuspTailPart_contDiffOn (kind : D4BMCompletedEisensteinCuspLegKind) (u : ℂ) :
    ContDiffOn ℝ ∞ (fun z : Fin 2 → ℝ =>
      d4BMCompletedEisensteinCuspTailPart kind u (z 0) (z 1)) domain := by
  cases kind with
  | scalar => exact contDiffOn_const.mul (fullSignedZeroWord_contDiffOn u u)
  | raise => exact contDiffOn_const.mul (fullSignedRaiseWord_contDiffOn u u)
  | lower => exact contDiffOn_const.mul (fullSignedLowerWord_contDiffOn u u)

/-- Joint smoothness of each literal full cusp leg, including both constant terms. -/
theorem cuspLeg_contDiffOn (kind : D4BMCompletedEisensteinCuspLegKind) (u : ℂ) :
    ContDiffOn ℝ ∞ (fun z : Fin 2 → ℝ =>
      d4BMCompletedEisensteinCuspLeg kind u (z 0) (z 1)) domain :=
  (cuspConstantPart_contDiffOn kind u).add (cuspTailPart_contDiffOn kind u)

/-- Every finite spatial jet of the literal cusp leg exists at positive height. -/
theorem cuspLeg_contDiffAt (kind : D4BMCompletedEisensteinCuspLegKind) (u : ℂ)
    (k : ℕ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    ContDiffAt ℝ k (fun v : Fin 2 → ℝ =>
      d4BMCompletedEisensteinCuspLeg kind u (v 0) (v 1)) z :=
  ((contDiffOn_infty.mp (cuspLeg_contDiffOn kind u)) k).contDiffAt
    ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)

/-- The literal balanced angular boundary current has all joint spatial derivatives. -/
theorem balancedBoundaryCurrent_contDiffOn (u v : ℂ) :
    ContDiffOn ℝ ∞ (fun z : Fin 2 → ℝ =>
      d4BMCompletedEisensteinBalancedFullBoundaryCurrent u v (z 0) (z 1)) domain :=
  (((height_cpow_contDiffOn (-1) ∞).mul (cuspLeg_contDiffOn .raise u)).mul
    (cuspLeg_contDiffOn .lower u)).mul (cuspLeg_contDiffOn .scalar v)

/-- Every finite spatial jet of the complete balanced current exists at positive height. -/
theorem balancedBoundaryCurrent_contDiffAt (u v : ℂ) (k : ℕ)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    ContDiffAt ℝ k (fun q : Fin 2 → ℝ =>
      d4BMCompletedEisensteinBalancedFullBoundaryCurrent u v (q 0) (q 1)) z :=
  ((contDiffOn_infty.mp (balancedBoundaryCurrent_contDiffOn u v)) k).contDiffAt
    ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)

end
end RHTower.D4BMAngularSeries
