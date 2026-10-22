import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularMasterCurrent

/-!
# Nonreal physical-rate horizon factors

The literal source lift has a three-factor horizon prefactor.  Each spectral
factor is forced away from zero by the nonzero imaginary part of every actual
Xi divisor.  Thus a horizon-current cancellation cannot be attributed to a
root of this radial prefactor; only an amplitude or an angular pairing can
remain.
-/

namespace RHTower.D4BMModularCore

noncomputable section

/-- Every physical stream rate inherits the nonzero imaginary part of its Xi
divisor, on either physical branch. -/
theorem physicalRate_im_ne_zero (q : XiZeroCopy) (branch : Bool) :
    (physicalRate q branch).im ≠ 0 := by
  cases branch <;> simpa [physicalRate] using xi_divisor_support_im_ne_zero q.1

private theorem add_real_ne_zero_of_im_ne_zero (s : ℂ) (c : ℝ) (hs : s.im ≠ 0) :
    s + (c : ℂ) ≠ 0 := by
  intro h
  apply hs
  have him := congrArg Complex.im h
  simpa using him

/-- The spectral part of the literal physical-lift horizon coefficient never
vanishes.  This is the exact three-factor coefficient in
`D4BMPhysicalLiftCurrent.horizonFactor`, before amplitudes and the angular
pairing are inserted. -/
theorem physicalRate_horizon_spectral_factor_ne_zero (q : XiZeroCopy) (branch : Bool) :
    let s := physicalRate q branch
    (2 * s + 3) * ((s + 1) * (s + 2) - 2) * ((s + 1) * (s + 2) - 6) ≠ 0 := by
  dsimp only
  have hs := physicalRate_im_ne_zero q branch
  have h2 : 2 * physicalRate q branch + 3 ≠ 0 := by
    intro h
    apply hs
    have him := congrArg Complex.im h
    norm_num at him ⊢
    linarith
  have h0 : physicalRate q branch ≠ 0 := by
    intro h
    apply hs
    rw [h]
    rfl
  have h3 := add_real_ne_zero_of_im_ne_zero (physicalRate q branch) 3 hs
  have hm1 := add_real_ne_zero_of_im_ne_zero (physicalRate q branch) (-1) hs
  have h4 := add_real_ne_zero_of_im_ne_zero (physicalRate q branch) 4 hs
  have hfirst : (physicalRate q branch + 1) * (physicalRate q branch + 2) - 2 ≠ 0 := by
    rw [show (physicalRate q branch + 1) * (physicalRate q branch + 2) - 2 =
      physicalRate q branch * (physicalRate q branch + 3) by ring]
    exact mul_ne_zero h0 h3
  have hsecond : (physicalRate q branch + 1) * (physicalRate q branch + 2) - 6 ≠ 0 := by
    rw [show (physicalRate q branch + 1) * (physicalRate q branch + 2) - 6 =
      (physicalRate q branch - 1) * (physicalRate q branch + 4) by ring]
    exact mul_ne_zero (by simpa [sub_eq_add_neg] using hm1) h4
  exact mul_ne_zero (mul_ne_zero h2 hfirst) hsecond

end

end RHTower.D4BMModularCore
