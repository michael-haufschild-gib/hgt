import GaloisForLFunctions.RHTower.RiemannTower

/-!
# A finite prime-power mark collision forces RH

For a base `p > 1`, attach to a spectral point `s` the centered prime mark

`u_p(s) = exp(log(p) * (1/2 - s))`.

Its norm is one exactly on the critical line, and the actual base Adams operation
`p -> p^m` sends the mark to `u_p(s)^m`.  At a hypothetical right-half Xi zero the
mark is nonzero and has norm strictly below one, so two distinct levels of its
prime-power ray cannot coincide.  Consequently, a source-derived finite collision
between two levels at every hypothetical right-half zero proves RH.

The file proves the complete consumer endpoint and the unconditional base-Adams
identity.  It does not assert that the completed prime--Gamma source identifies two
levels of the ray.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- The prime-local spectral mark centered at the functional-equation line. -/
def centeredPrimeMark (p : ℕ) (s : ℂ) : ℂ :=
  Complex.exp ((Real.log p : ℂ) * (1 / 2 - s))

/-- The exact radial coordinate of the centered prime mark. -/
theorem norm_centeredPrimeMark (p : ℕ) (s : ℂ) :
    ‖centeredPrimeMark p s‖ = Real.exp (Real.log p * (1 / 2 - s.re)) := by
  rw [centeredPrimeMark, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
    zero_mul, sub_zero]
  norm_num

/-- A centered prime mark is contractive exactly in the open right half-plane. -/
theorem centeredPrimeMark_norm_lt_one_iff {p : ℕ} (hp : 1 < p) (s : ℂ) :
    ‖centeredPrimeMark p s‖ < 1 ↔ 1 / 2 < s.re := by
  rw [norm_centeredPrimeMark, Real.exp_lt_one_iff]
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  constructor <;> intro h <;> nlinarith

/-- The critical line is exactly the unit circle of any centered prime mark. -/
theorem centeredPrimeMark_norm_eq_one_iff {p : ℕ} (hp : 1 < p) (s : ℂ) :
    ‖centeredPrimeMark p s‖ = 1 ↔ s.re = 1 / 2 := by
  rw [norm_centeredPrimeMark, Real.exp_eq_one_iff]
  have hlog : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp)).ne'
  constructor
  · intro h
    apply (sub_eq_zero.mp ?_).symm
    exact (mul_eq_zero.mp h).resolve_left hlog
  · intro h
    rw [h]
    ring

/-- **Base Adams law.** Replacing `p` by `p^m` raises the centered mark to the
`m`-th power.  This is the source-correct prime-power operation, with no divisor data. -/
theorem centeredPrimeMark_primePower (p m : ℕ) (s : ℂ) :
    centeredPrimeMark (p ^ m) s = centeredPrimeMark p s ^ m := by
  have hlog : Real.log (p ^ m : ℕ) = (m : ℝ) * Real.log p := by
    rw [show ((p ^ m : ℕ) : ℝ) = (p : ℝ) ^ m by norm_cast, Real.log_pow]
  rw [centeredPrimeMark, centeredPrimeMark, hlog]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Functional-equation reflection inverts the centered prime mark. -/
theorem centeredPrimeMark_one_sub (p : ℕ) (s : ℂ) :
    centeredPrimeMark p (1 - s) = (centeredPrimeMark p s)⁻¹ := by
  rw [centeredPrimeMark, centeredPrimeMark, ← Complex.exp_neg]
  congr 1
  ring

/-- Source target: every hypothetical right-half Xi zero makes two distinct levels of
one fixed centered prime-power ray coincide. -/
def XiRightPrimePowerMarkCollision (p : ℕ) : Prop :=
  ∀ rho : ℂ, rho ∈ rightHalf → xi rho = 0 →
    ∃ a b : ℕ, a < b ∧ centeredPrimeMark p rho ^ a = centeredPrimeMark p rho ^ b

/-- **Finite prime-power collision criterion for RH.** One collision on one fixed base
at each hypothetical right-half zero is impossible because its mark has radius in `(0,1)`. -/
theorem riemannHypothesis_of_xiRightPrimePowerMarkCollision {p : ℕ} (hp : 1 < p)
    (hcollision : XiRightPrimePowerMarkCollision p) : RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hright hzero
  have hcontract : ‖centeredPrimeMark p rho‖ < 1 :=
    (centeredPrimeMark_norm_lt_one_iff hp rho).mpr (Set.mem_setOf.mp hright)
  have hmark0 : centeredPrimeMark p rho ≠ 0 := Complex.exp_ne_zero _
  obtain ⟨a, b, hab, hpowers⟩ := hcollision rho hright hzero
  have hnorm : ‖centeredPrimeMark p rho‖ ^ a = ‖centeredPrimeMark p rho‖ ^ b := by
    simpa only [norm_pow] using congrArg norm hpowers
  have hab' : a = b :=
    pow_right_injective₀ (norm_pos_iff.mpr hmark0) (ne_of_lt hcontract) hnorm
  exact (ne_of_lt hab) hab'

/-- **Circularity audit.**  As a bare zero-indexed predicate, the collision certificate is
equivalent to RH: under RH there are no right-half zeros, so its source obligation is vacuous.
It becomes a route only if a separately defined completed-source construction supplies the
collision before zero location is read. -/
theorem xiRightPrimePowerMarkCollision_iff_riemannHypothesis {p : ℕ} (hp : 1 < p) :
    XiRightPrimePowerMarkCollision p ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_xiRightPrimePowerMarkCollision hp
  · intro hRH rho hright hzero
    exact (rh_iff_xi_ne_zero_right.mp hRH rho hright hzero).elim

end


end RHTower
