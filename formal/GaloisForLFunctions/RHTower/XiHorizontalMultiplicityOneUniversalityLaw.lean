import GaloisForLFunctions.RHTower.HorizontalSingletonZeroFiber
import GaloisForLFunctions.RHTower.BornTemperatureFactorType

/-!
# Xi horizontal multiplicity-one universality law

Critical-line reflection turns exact-height multiplicity into a joint location/simplicity detector.
Every horizontal Xi-zero fiber has mass one exactly when RH holds and every Xi zero has analytic
order one.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Every nonempty exact-height Xi-zero fiber has total analytic multiplicity one. -/
def XiHorizontalFibersMultiplicityOne : Prop :=
  ∀ ρ : ℂ, xi ρ = 0 → xiHorizontalMultiplicity ρ.im = 1

/-- Under RH, the complete exact-height fiber through a Xi zero consists only of that zero, so its
total horizontal multiplicity is exactly the zero's local analytic order. -/
theorem xiHorizontalMultiplicity_eq_order_of_RH
    (hRH : RiemannHypothesis) {ρ : ℂ} (hzero : xi ρ = 0) :
    xiHorizontalMultiplicity ρ.im = (analyticOrderAt xi ρ).toNat := by
  classical
  have hstrip := xi_zero_re_mem_open_unit hzero
  have hρmem : ρ ∈ stripHeightFinset ρ.im := by
    rw [mem_stripHeightFinset]
    exact ⟨hstrip.1, hstrip.2, rfl, hzero⟩
  rw [xiHorizontalMultiplicity, Finset.sum_eq_single ρ]
  · intro z hz hzne
    have hzdata := mem_stripHeightFinset.mp hz
    have hzline := xi_zero_re_eq_half_of_RH hRH hzdata.2.2.2
    have hρline := xi_zero_re_eq_half_of_RH hRH hzero
    have hzr : z = ρ := by
      apply Complex.ext
      · rw [hzline, hρline]
      · exact hzdata.2.2.1
    exact (hzne hzr).elim
  · intro hρnot
    exact (hρnot hρmem).elim

/-- **Xi horizontal multiplicity-one universality law.**  Exact-height divisor mass one is
equivalent to the conjunction of RH and analytic simplicity of every Xi zero. -/
theorem xiHorizontalFibersMultiplicityOne_iff_rh_and_orderOne :
    XiHorizontalFibersMultiplicityOne ↔
      RiemannHypothesis ∧
        ∀ ρ : ℂ, xi ρ = 0 → (analyticOrderAt xi ρ).toNat = 1 := by
  constructor
  · intro hsingle
    have hlocal : ∀ ρ : ℂ, xi ρ = 0 → XiHorizontalSingletonZero ρ := by
      intro ρ hzero
      have hstrip := xi_zero_re_mem_open_unit hzero
      refine ⟨(mem_stripHeightFinset.mpr ?_), hsingle ρ hzero⟩
      exact ⟨hstrip.1, hstrip.2, rfl, hzero⟩
    refine ⟨?_, fun ρ hzero => xiHorizontalSingletonZero_order_eq_one (hlocal ρ hzero)⟩
    rw [rh_iff_xi_ne_zero_right]
    intro ρ hright hzero
    have hline := xiHorizontalSingletonZero_re_eq_half (hlocal ρ hzero)
    rw [mem_rightHalf] at hright
    linarith
  · rintro ⟨hRH, horder⟩ ρ hzero
    exact (xiHorizontalMultiplicity_eq_order_of_RH hRH hzero).trans (horder ρ hzero)

end

end RHTower
