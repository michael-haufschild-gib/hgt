import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularMasterCurrent

/-!
# Self-copy inverse-square noncancellation for cyclic Peierls

The cap/square leading residual has an affine radial scalar.  This leaf proves
that its inverse-radius-square coefficient cannot vanish at any literal
self-copy Xi source.  The fundamental-frequency normal form is the one stated
by `physicalFundamentalFrequency_eq`; attaching that existing equality to this
closed normal-form theorem gives the physical-reader instance.

Proof-chain role:
`self-copy inverse-square coefficient ≠ 0`
`-> cap/square leading residual is not radially identically zero`
`-> choose a nonexceptional radial fibre`
`-> noncompact B2 growth transport -> RBH/PW extinction`.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsSelfInverseSquareNormalForm

open Set D4BMModularCore
noncomputable section
set_option autoImplicit false

/-- Normal form of the physical fundamental frequency. -/
def fundamentalFrequencyNormalForm (q : XiZeroCopy) (side : Bool) : ℂ :=
  if side then -1 - (q.1 : ℂ) / 2 else -2 + (q.1 : ℂ) / 2

/-- Inverse-square radial factor of the self-copy cap/square residual. -/
def selfInverseSquareFactor (q : XiZeroCopy) (branch side : Bool) : ℂ :=
  let s := physicalRate q branch
  let w := fundamentalFrequencyNormalForm q side
  s * (w + 2 * s + 3) * (s + 1) * (2 * s + 2 - w) / 2

/-- No self-copy source arm can lose the inverse-square coefficient. -/
theorem selfInverseSquareFactor_ne_zero (q : XiZeroCopy) (branch side : Bool) :
    selfInverseSquareFactor q branch side ≠ 0 := by
  have hi := xi_divisor_support_im_ne_zero q.1
  unfold selfInverseSquareFactor fundamentalFrequencyNormalForm
  cases branch <;> cases side <;>
    simp only [physicalRate, Bool.false_eq_true, if_true, if_false]
  all_goals
    apply div_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · intro h
            apply hi
            have him := congrArg Complex.im h
            norm_num [Complex.sub_im] at him ⊢
            linarith
          · intro h
            apply hi
            have him := congrArg Complex.im h
            norm_num [Complex.add_im, Complex.sub_im, Complex.div_im,
              Complex.mul_im, Complex.neg_im] at him ⊢
            linarith
        · intro h
          apply hi
          have him := congrArg Complex.im h
          norm_num [Complex.add_im, Complex.sub_im, Complex.div_im,
            Complex.mul_im, Complex.neg_im] at him ⊢
          linarith
      · intro h
        apply hi
        have him := congrArg Complex.im h
        norm_num [Complex.add_im, Complex.sub_im, Complex.div_im,
          Complex.mul_im, Complex.neg_im] at him ⊢
        linarith
    · norm_num

/-- The leading residual after adding any radial-constant cap contribution. -/
def affineResidual (q : XiZeroCopy) (branch side : Bool) (A K : ℂ)
    (r : Ioi (1 : ℝ)) : ℂ :=
  (A + selfInverseSquareFactor q branch side / (r.val : ℂ) ^ 2) / 2 - K

/-- No radial-constant cap contribution can cancel the self-copy leading
residual on every exterior radial fibre. -/
theorem exists_affineResidual_ne_zero (q : XiZeroCopy) (branch side : Bool) (A K : ℂ) :
    ∃ r : Ioi (1 : ℝ), affineResidual q branch side A K r ≠ 0 := by
  by_contra h
  push Not at h
  have h2 := h ⟨2, by norm_num⟩
  have h3 := h ⟨3, by norm_num⟩
  have hB : (5 : ℂ) * selfInverseSquareFactor q branch side = 0 := by
    unfold affineResidual at h2 h3
    norm_num at h2 h3
    linear_combination 72 * h2 - 72 * h3
  exact selfInverseSquareFactor_ne_zero q branch side
    ((mul_eq_zero.mp hB).resolve_left (by norm_num))

end
end RHTower.D4BMLiteralCyclicPeierlsSelfInverseSquareNormalForm
