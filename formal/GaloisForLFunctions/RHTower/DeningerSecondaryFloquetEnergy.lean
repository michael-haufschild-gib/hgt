import GaloisForLFunctions.RHTower.DeningerAllPrimeFloquetRadical
import GaloisForLFunctions.RHTower.DeningerSecondaryCollarDefect
import GaloisForLFunctions.RHTower.DeningerTomographyNonstrict

/-!
# The all-prime energy of the secondary two-collar defect

The centred two-collar defect is the half-density lift of `h₊ - J h₋`, so it is a source cochain and
its all-prime Floquet energy is defined.  That energy is finite, translation invariant — hence
invariant under the contragredient collar flow — and its radical is exactly the reflected Calderón
graph.

* `deningerSecondaryDefectSource` : the defect as a source cochain.
* `deningerFloquetEnergy_shift` : **the energy is translation invariant.**
* `deningerSecondaryFloquetEnergy` : **`E_sec(h₊,h₋)`.**
* `deningerSecondaryFloquetEnergy_eq_zero_iff` : **its radical is the graph of the collar
  exchange.**
* `deningerSecondaryFloquetEnergy_flow` : **it is invariant under the contragredient flow.**
-/

namespace RHTower

open SchwartzMap MeasureTheory

noncomputable section

/-! ## The defect as a source cochain -/

/-- **The centred two-collar defect as a source cochain**, `d_sec = U(h₊ - J h₋)`. -/
def deningerSecondaryDefectSource (hp hm : DeningerExpSchwartz) : DeningerExpSchwartz :=
  deningerHalfDensityLift (hp - deningerCollarExchange hm)

@[simp]
theorem deningerSecondaryDefectSource_apply (hp hm : DeningerExpSchwartz) (t : ℝ) :
    ((deningerSecondaryDefectSource hp hm : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
      = deningerSecondaryDefect hp hm t := by
  rw [deningerSecondaryDefectSource, deningerHalfDensityLift_apply, deningerSecondaryDefect,
    deningerHalfDensityLift_apply, deningerHalfDensityLift_apply]
  show ((Real.exp (t / 2) : ℝ) : ℂ)
      * (((hp : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
        - ((deningerCollarExchange hm : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t) = _
  rw [deningerCollarExchange_apply, mul_sub, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3
  ring

/-- The defect vanishes identically exactly when the source cochain is zero. -/
theorem deningerSecondaryDefectSource_eq_zero_iff (hp hm : DeningerExpSchwartz) :
    deningerSecondaryDefectSource hp hm = 0 ↔ ∀ t : ℝ, deningerSecondaryDefect hp hm t = 0 := by
  constructor
  · intro hzero t
    have := congrArg (fun u : DeningerExpSchwartz => ((u : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t) hzero
    simpa using this
  · intro hall
    refine Subtype.ext (SchwartzMap.ext fun t => ?_)
    rw [deningerSecondaryDefectSource_apply]
    simpa using hall t

/-! ## Translation invariance of the energy -/

/-- **The all-prime energy is translation invariant.**  Periodization turns the translation into a
rotation of the orbit, and the integral of a periodic function over one period is unchanged. -/
theorem deningerFloquetEnergy_shift (g : DeningerExpSchwartz) (a : ℝ) :
    deningerFloquetEnergy (deningerEscapeFamily 0 a g) = deningerFloquetEnergy g := by
  have hterm : ∀ q : Nat.Primes,
      deningerFloquetTerm (deningerEscapeFamily 0 a g) (q : ℕ) = deningerFloquetTerm g (q : ℕ) := by
    intro q
    have hq : 2 ≤ (q : ℕ) := q.2.two_le
    have hqR : (2 : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast hq
    have hLpos : 0 < Real.log (q : ℕ) :=
      Real.log_pos (by linarith)
    set L := Real.log (q : ℕ) with hLdef
    set S := deningerPeriodizationSum ((g : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L with hS
    have hrot : ∀ t : ℝ,
        deningerPeriodizationSum
          ((deningerEscapeFamily 0 a g : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L t = S (t - a) := by
      intro t
      rw [deningerEscapeFamily_periodizationSum]
      have hone : ((Real.exp (-(0 * a)) : ℝ) : ℂ) = 1 := by norm_num
      rw [hone, one_mul, hS]
    have hper : Function.Periodic (fun t : ℝ => ‖S t‖ ^ (2 : ℕ)) L := by
      intro s
      show ‖S (s + L)‖ ^ (2 : ℕ) = ‖S s‖ ^ (2 : ℕ)
      rw [hS, deningerPeriodizationSum_periodic]
    have hshift : (∫ t in (0 : ℝ)..L, ‖S (t - a)‖ ^ (2 : ℕ)) = ∫ t in (0 : ℝ)..L, ‖S t‖ ^ (2 : ℕ) := by
      have hcomp : (∫ t in (0 : ℝ)..L, ‖S (t - a)‖ ^ (2 : ℕ))
          = ∫ t in (0 - a)..(L - a), ‖S t‖ ^ (2 : ℕ) :=
        intervalIntegral.integral_comp_sub_right (fun t => ‖S t‖ ^ (2 : ℕ)) a
      rw [hcomp]
      have hrange : (∫ t in (-a)..(-a + L), ‖S t‖ ^ (2 : ℕ)) = ∫ t in (0 : ℝ)..(0 + L), ‖S t‖ ^ (2 : ℕ) :=
        hper.intervalIntegral_add_eq (-a) 0
      have hL1 : (0 : ℝ) - a = -a := by ring
      have hL2 : L - a = -a + L := by ring
      rw [hL1, hL2, hrange, zero_add]
    rw [deningerFloquetTerm, deningerFloquetTerm]
    congr 1
    have hfun : (fun t : ℝ => ‖deningerPeriodizationSum
        ((deningerEscapeFamily 0 a g : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L t‖ ^ (2 : ℕ))
        = fun t : ℝ => ‖S (t - a)‖ ^ (2 : ℕ) := funext fun t => by rw [hrot t]
    rw [hfun, hshift]
  rw [deningerFloquetEnergy, deningerFloquetEnergy, tsum_congr hterm]

/-! ## The secondary energy -/

/-- **The all-prime energy of the secondary two-collar defect.** -/
def deningerSecondaryFloquetEnergy (hp hm : DeningerExpSchwartz) : ℝ :=
  deningerFloquetEnergy (deningerSecondaryDefectSource hp hm)

theorem deningerSecondaryFloquetEnergy_nonneg (hp hm : DeningerExpSchwartz) :
    0 ≤ deningerSecondaryFloquetEnergy hp hm :=
  deningerFloquetEnergy_nonneg _

/-- **The secondary energy is finite and dominated by the Meyer seminorm of the defect.** -/
theorem deningerSecondaryFloquetEnergy_le (hp hm : DeningerExpSchwartz) :
    deningerSecondaryFloquetEnergy hp hm
      ≤ 25 * deningerMeyerSeminormFun 1 0 (deningerSecondaryDefectSource hp hm) ^ (2 : ℕ)
        * ∑' q : Nat.Primes, Real.log (q : ℕ) / ((q : ℕ) : ℝ) ^ (2 : ℕ) :=
  deningerFloquetEnergy_le _

/-- **The radical of the secondary energy is the reflected Calderón graph.**  This is `(6)` ⟺ `(7)`
at the level of the all-prime energy. -/
theorem deningerSecondaryFloquetEnergy_eq_zero_iff (hp hm : DeningerExpSchwartz) :
    deningerSecondaryFloquetEnergy hp hm = 0
      ↔ ∀ t : ℝ, ((hp : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
          = ((deningerCollarExchange hm : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t := by
  rw [deningerSecondaryFloquetEnergy, deningerFloquetEnergy_eq_zero_iff,
    deningerSecondaryDefectSource_eq_zero_iff, deningerSecondaryDefect_eq_zero_iff]

/-- The contragredient collar flow `(h₊,h₋) ↦ (V_a h₊, V_{-a} h₋)` translates the defect. -/
theorem deningerSecondaryDefectSource_flow (hp hm : DeningerExpSchwartz) (a : ℝ) :
    deningerSecondaryDefectSource (deningerEscapeFamily (1 / 2) a hp)
        (deningerEscapeFamily (1 / 2) (-a) hm)
      = deningerEscapeFamily 0 a (deningerSecondaryDefectSource hp hm) := by
  refine Subtype.ext (SchwartzMap.ext fun t => ?_)
  rw [deningerSecondaryDefectSource_apply, deningerEscapeFamily_apply,
    deningerSecondaryDefectSource_apply, deningerSecondaryDefect, deningerSecondaryDefect,
    deningerHalfDensityLift_apply, deningerHalfDensityLift_apply, deningerHalfDensityLift_apply,
    deningerHalfDensityLift_apply, deningerEscapeFamily_apply, deningerEscapeFamily_apply]
  have hexp1 : ((Real.exp (t / 2) : ℝ) : ℂ) * ((Real.exp (-(1 / 2 * a)) : ℝ) : ℂ)
      = ((Real.exp (-(0 * a)) : ℝ) : ℂ) * ((Real.exp ((t - a) / 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  have hexp2 : ((Real.exp (-t / 2) : ℝ) : ℂ) * ((Real.exp (-(1 / 2 * -a)) : ℝ) : ℂ)
      = ((Real.exp (-(0 * a)) : ℝ) : ℂ) * ((Real.exp (-(t - a) / 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  have harg : -t - -a = -(t - a) := by ring
  rw [mul_sub]
  rw [show ((Real.exp (t / 2) : ℝ) : ℂ)
      * (((Real.exp (-(1 / 2 * a)) : ℝ) : ℂ) * ((hp : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (t - a))
      = (((Real.exp (t / 2) : ℝ) : ℂ) * ((Real.exp (-(1 / 2 * a)) : ℝ) : ℂ))
        * ((hp : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (t - a) by ring]
  rw [show ((Real.exp (-t / 2) : ℝ) : ℂ)
      * (((Real.exp (-(1 / 2 * -a)) : ℝ) : ℂ) * ((hm : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (-t - -a))
      = (((Real.exp (-t / 2) : ℝ) : ℂ) * ((Real.exp (-(1 / 2 * -a)) : ℝ) : ℂ))
        * ((hm : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (-t - -a) by ring]
  rw [hexp1, hexp2, harg]
  ring

/-- **`(8)`: the secondary energy is invariant under the contragredient collar flow.** -/
theorem deningerSecondaryFloquetEnergy_flow (hp hm : DeningerExpSchwartz) (a : ℝ) :
    deningerSecondaryFloquetEnergy (deningerEscapeFamily (1 / 2) a hp)
        (deningerEscapeFamily (1 / 2) (-a) hm)
      = deningerSecondaryFloquetEnergy hp hm := by
  rw [deningerSecondaryFloquetEnergy, deningerSecondaryDefectSource_flow,
    deningerFloquetEnergy_shift, deningerSecondaryFloquetEnergy]

end

end RHTower
