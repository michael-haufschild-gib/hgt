import GaloisForLFunctions.HTGeometry.ZetaTailBound
import GaloisForLFunctions.HTGeometry.GammaRayShiftAsymptotic

/-!
# The zeta-moment coefficients have a complex factorial slope

For `α` with `Re α > 0` the functional equation turns the coefficients

`aₙ = (-1)ⁿ ζ(-αn)`

into an exact product

`aₙ = C · Λⁿ · Γ(1 + αn) · (ζ(1 + αn)(1 - qⁿ))`,

where `Λ = -exp(εiπα/2)(2π)^{-α}`, `C = -ε/(2πi)` and `q = exp(-εiπα)`, with the branch sign
`ε = -1` for `Im α > 0` and `ε = +1` for `Im α < 0`.  The choice of `ε` selects the exponentially
dominant branch of the sine, so that `‖q‖ = exp(-π|Im α|)` is the exponentially small one.

The identity itself holds for either sign of `ε`; only the size of `q` depends on the choice.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The dominant branch of the sine -/

/-- Either branch of the sine, isolated with its complementary exponential. -/
theorem sin_branch_split {ε : ℂ} (hε : ε ^ 2 = 1) (w : ℂ) :
    Complex.sin w
      = ε * Complex.exp (ε * Complex.I * w)
          * (1 - Complex.exp (-(2 * ε * Complex.I * w))) / (2 * Complex.I) := by
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h2I : (2 * Complex.I : ℂ) ≠ 0 := by
    simp [Complex.I_ne_zero]
  have hmerge : Complex.exp (ε * Complex.I * w) * Complex.exp (-(2 * ε * Complex.I * w))
      = Complex.exp (-(ε * Complex.I * w)) := by
    rw [← Complex.exp_add]
    ring_nf
  have hkey : ε * Complex.exp (ε * Complex.I * w)
        * (1 - Complex.exp (-(2 * ε * Complex.I * w)))
      = ε * (Complex.exp (ε * Complex.I * w) - Complex.exp (-(ε * Complex.I * w))) := by
    rw [← hmerge]; ring
  have hbase : Complex.sin w
      = (Complex.exp (w * Complex.I) - Complex.exp (-w * Complex.I)) / (2 * Complex.I) := by
    have hsin : Complex.sin w
        = (Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2 := rfl
    rw [hsin, eq_div_iff h2I]
    linear_combination (Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * hI2
  have hcases : ε = 1 ∨ ε = -1 := by
    have hfac : (ε - 1) * (ε + 1) = 0 := by linear_combination hε
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  rw [hkey, hbase]
  rcases hcases with rfl | rfl
  · have e1 : (1 : ℂ) * Complex.I * w = w * Complex.I := by ring
    have e2 : -((1 : ℂ) * Complex.I * w) = -w * Complex.I := by ring
    rw [e2, e1]
    ring
  · have e1 : (-1 : ℂ) * Complex.I * w = -w * Complex.I := by ring
    have e2 : -((-1 : ℂ) * Complex.I * w) = w * Complex.I := by ring
    rw [e2, e1]
    ring

/-! ## Complex powers along a ray -/

/-- A complex power with a natural multiple in the exponent is an integer power. -/
theorem cpow_mul_natCast {x : ℂ} (hx : x ≠ 0) (z : ℂ) (n : ℕ) :
    x ^ (z * (n : ℂ)) = (x ^ z) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hcast : ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 := by push_cast; ring
      rw [hcast, mul_add, mul_one, Complex.cpow_add _ _ hx, ih, pow_succ]

/-! ## The zeta-moment family -/

/-- The coefficients of the formal zeta-moment series. -/
def zetaMomentCoeff (α : ℂ) (n : ℕ) : ℂ := (-1) ^ n * riemannZeta (-(α * (n : ℂ)))

/-- The dominant branch sign: `-1` above the real axis, `+1` below it. -/
def branchSign (α : ℂ) : ℂ := if 0 < α.im then -1 else 1

theorem branchSign_sq (α : ℂ) : branchSign α ^ 2 = 1 := by
  rw [branchSign]
  split_ifs <;> ring

theorem branchSign_ne_zero (α : ℂ) : branchSign α ≠ 0 := by
  rw [branchSign]
  split_ifs <;> norm_num

/-- The factorial slope base of the zeta-moment family. -/
def zetaMomentLam (α : ℂ) : ℂ :=
  -(Complex.exp (branchSign α * Complex.I * (Real.pi : ℂ) * α / 2)
      * ((2 * (Real.pi : ℂ)) ^ (-α)))

/-- The leading constant of the zeta-moment family. -/
def zetaMomentConst (α : ℂ) : ℂ :=
  -branchSign α / (2 * (Real.pi : ℂ) * Complex.I)

/-- The subdominant sine branch, as a ratio. -/
def zetaMomentQ (α : ℂ) : ℂ :=
  Complex.exp (-(branchSign α * Complex.I * (Real.pi : ℂ) * α))

/-- The relative error factor of the zeta-moment family. -/
def zetaMomentErr (α : ℂ) (n : ℕ) : ℂ :=
  riemannZeta (rayPoint α n) * (1 - zetaMomentQ α ^ n)

theorem twoPi_ne_zero : (2 * (Real.pi : ℂ)) ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact mul_ne_zero two_ne_zero hpi

theorem zetaMomentLam_ne_zero (α : ℂ) : zetaMomentLam α ≠ 0 := by
  rw [zetaMomentLam]
  refine neg_ne_zero.mpr (mul_ne_zero (Complex.exp_ne_zero _) ?_)
  rw [Complex.cpow_def_of_ne_zero twoPi_ne_zero]
  exact Complex.exp_ne_zero _

theorem zetaMomentConst_ne_zero (α : ℂ) : zetaMomentConst α ≠ 0 := by
  rw [zetaMomentConst]
  refine div_ne_zero (neg_ne_zero.mpr (branchSign_ne_zero α)) ?_
  exact mul_ne_zero twoPi_ne_zero Complex.I_ne_zero

/-! ## The functional-equation identity -/

/-- The reflected cosine on the ray is the negated sine of the half-ray. -/
theorem cos_pi_rayPoint_div_two (α : ℂ) (n : ℕ) :
    Complex.cos ((Real.pi : ℂ) * rayPoint α n / 2)
      = -Complex.sin ((Real.pi : ℂ) * α * (n : ℂ) / 2) := by
  have harg : (Real.pi : ℂ) * rayPoint α n / 2
      = (Real.pi : ℂ) / 2 + (Real.pi : ℂ) * α * (n : ℂ) / 2 := by
    rw [rayPoint]; ring
  rw [harg, Complex.cos_add, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  ring

/-- **The zeta-moment factorial identity.**  This is the card's `(22)` with the dominant sine
branch isolated. -/
theorem zetaMomentCoeff_eq {α : ℂ} (hre : 0 < α.re) {n : ℕ} (hn : n ≠ 0) :
    zetaMomentCoeff α n
      = zetaMomentConst α * zetaMomentLam α ^ n * Complex.Gamma (rayPoint α n)
          * zetaMomentErr α n := by
  have hα : α ≠ 0 := by
    intro hc
    rw [hc] at hre
    simp at hre
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := Nat.pos_of_ne_zero hn
    exact_mod_cast this
  -- the two side conditions of the functional equation
  have hsre : 0 < (rayPoint α n).re := rayPoint_re_pos hre n
  have hsm : ∀ m : ℕ, rayPoint α n ≠ -(m : ℂ) := by
    intro m hc
    rw [hc] at hsre
    simp at hsre
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hs1 : rayPoint α n ≠ 1 := by
    intro hc
    rw [rayPoint] at hc
    have hzero : α * (n : ℂ) = 0 := by linear_combination hc
    rcases mul_eq_zero.mp hzero with h | h
    · exact hα h
    · exact absurd (by exact_mod_cast h : (n : ℝ) = 0) (ne_of_gt hnpos)
  -- the functional equation
  have hone_sub : 1 - rayPoint α n = -(α * (n : ℂ)) := by rw [rayPoint]; ring
  have hfe := riemannZeta_one_sub hsm hs1
  rw [hone_sub, cos_pi_rayPoint_div_two] at hfe
  -- the dominant branch of the sine
  set ε : ℂ := branchSign α with hεdef
  have hsin := sin_branch_split (branchSign_sq α) ((Real.pi : ℂ) * α * (n : ℂ) / 2)
  have hexp1 : Complex.exp (ε * Complex.I * ((Real.pi : ℂ) * α * (n : ℂ) / 2))
      = Complex.exp (ε * Complex.I * (Real.pi : ℂ) * α / 2) ^ n := by
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  have hexp2 : Complex.exp (-(2 * ε * Complex.I * ((Real.pi : ℂ) * α * (n : ℂ) / 2)))
      = zetaMomentQ α ^ n := by
    rw [zetaMomentQ, ← Complex.exp_nat_mul, ← hεdef]
    congr 1
    ring
  rw [hexp1, hexp2] at hsin
  -- the complex power on the ray
  have hcpow : (2 * (Real.pi : ℂ)) ^ (-rayPoint α n)
      = (2 * (Real.pi : ℂ))⁻¹ * ((2 * (Real.pi : ℂ)) ^ (-α)) ^ n := by
    have hsplit : -rayPoint α n = (-1 : ℂ) + (-α) * (n : ℂ) := by rw [rayPoint]; ring
    rw [hsplit, Complex.cpow_add _ _ twoPi_ne_zero, Complex.cpow_neg_one,
      cpow_mul_natCast twoPi_ne_zero]
  rw [hcpow] at hfe
  -- assemble
  rw [zetaMomentCoeff, hfe, hsin, zetaMomentConst, zetaMomentLam, zetaMomentErr, ← hεdef]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  field_simp
  ring

end

end GaloisForLFunctions.HTGeometry
