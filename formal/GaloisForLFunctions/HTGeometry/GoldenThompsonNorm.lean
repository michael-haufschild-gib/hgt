import GaloisForLFunctions.HTGeometry.LieTrotterProduct
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# Cordes' inequality and the Golden–Thompson inequality for the norm

For self-adjoint elements of a C⋆-algebra,

```text
‖exp (x/2) * exp (y/2)‖ ^ (2 : ℕ) ≤ ‖exp x * exp y‖,
```

which is Cordes' inequality at exponent one half, written for exponentials.  Its only analytic
input is operator monotonicity of the square root: the norm bound on `exp y exp (2x) exp y` is
transported by conjugation to `exp (2x) ≤ (c exp (-y)) ^ (2 : ℕ)`, the square root turns that into
`exp x ≤ c exp (-y)`, and a second conjugation returns the claim.
-/

namespace GaloisForLFunctions.HTGeometry

open NormedSpace Filter Topology

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-! ## Elementary exponential identities -/

omit [PartialOrder A] [StarOrderedRing A] in
theorem exp_add_of_commute' {x y : A} (h : Commute x y) :
    NormedSpace.exp (x + y) = NormedSpace.exp x * NormedSpace.exp y := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  exact NormedSpace.exp_add_of_commute h

omit [PartialOrder A] [StarOrderedRing A] in
theorem exp_neg_mul_exp (x : A) : NormedSpace.exp (-x) * NormedSpace.exp x = 1 := by
  rw [← exp_add_of_commute' ((Commute.refl x).neg_left), neg_add_cancel, NormedSpace.exp_zero]

omit [PartialOrder A] [StarOrderedRing A] in
theorem exp_mul_exp_neg (x : A) : NormedSpace.exp x * NormedSpace.exp (-x) = 1 := by
  rw [← exp_add_of_commute' ((Commute.refl x).neg_right), add_neg_cancel, NormedSpace.exp_zero]

omit [PartialOrder A] [StarOrderedRing A] in
theorem exp_two_smul (x : A) :
    NormedSpace.exp ((2 : ℝ) • x) = NormedSpace.exp x * NormedSpace.exp x := by
  rw [two_smul, exp_add_of_commute' (Commute.refl x)]

omit [PartialOrder A] [StarOrderedRing A] in
theorem exp_half_smul_mul_self (x : A) :
    NormedSpace.exp (((2 : ℝ)⁻¹) • x) * NormedSpace.exp (((2 : ℝ)⁻¹) • x) = NormedSpace.exp x := by
  rw [← exp_add_of_commute' (Commute.refl _), ← two_smul ℝ, smul_smul]
  norm_num

omit [PartialOrder A] [StarOrderedRing A] in
theorem isSelfAdjoint_smul_real {r : ℝ} {x : A} (hx : IsSelfAdjoint x) :
    IsSelfAdjoint (r • x) := (IsSelfAdjoint.all r).smul hx

/-- **The exponential of a self-adjoint element is nonnegative.** -/
theorem nonneg_exp {x : A} (hx : IsSelfAdjoint x) : 0 ≤ NormedSpace.exp x := by
  have h := star_mul_self_nonneg (NormedSpace.exp (((2 : ℝ)⁻¹) • x))
  rwa [(isSelfAdjoint_smul_real hx).exp.star_eq, exp_half_smul_mul_self] at h

omit [PartialOrder A] [StarOrderedRing A] in
theorem sq_exp_half_smul (x : A) :
    NormedSpace.exp (((2 : ℝ)⁻¹) • x) ^ (2 : ℕ) = NormedSpace.exp x := by
  rw [sq, exp_half_smul_mul_self]

/-- **The square root of an exponential is the exponential of the half.** -/
theorem sqrt_exp {x : A} (hx : IsSelfAdjoint x) :
    CFC.sqrt (NormedSpace.exp x) = NormedSpace.exp (((2 : ℝ)⁻¹) • x) := by
  rw [← sq_exp_half_smul x]
  exact CFC.sqrt_sq _ (nonneg_exp (isSelfAdjoint_smul_real hx))

/-! ## Cordes' inequality at exponent one half -/

variable [NormOneClass A]

/-- **Cordes' inequality at exponent one half**, in exponential form.  The only analytic input is
operator monotonicity of the square root. -/
theorem norm_exp_half_mul_exp_half_sq_le {x y : A} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) :
    ‖NormedSpace.exp (((2 : ℝ)⁻¹) • x) * NormedSpace.exp (((2 : ℝ)⁻¹) • y)‖ ^ (2 : ℕ)
      ≤ ‖NormedSpace.exp x * NormedSpace.exp y‖ := by
  set c : ℝ := ‖NormedSpace.exp x * NormedSpace.exp y‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  have hnegy : IsSelfAdjoint (-y) := hy.neg
  have hhalfy : IsSelfAdjoint (((2 : ℝ)⁻¹) • y) := isSelfAdjoint_smul_real hy
  -- the middle element
  have hmid : NormedSpace.exp y * NormedSpace.exp ((2 : ℝ) • x) * NormedSpace.exp y
      = star (NormedSpace.exp x * NormedSpace.exp y) * (NormedSpace.exp x * NormedSpace.exp y) := by
    rw [star_mul, hx.exp.star_eq, hy.exp.star_eq, exp_two_smul]
    noncomm_ring
  have hmidnonneg : 0 ≤ NormedSpace.exp y * NormedSpace.exp ((2 : ℝ) • x) * NormedSpace.exp y := by
    rw [hmid]
    exact star_mul_self_nonneg _
  have hmidnorm : ‖NormedSpace.exp y * NormedSpace.exp ((2 : ℝ) • x) * NormedSpace.exp y‖
      = c * c := by
    rw [hmid, CStarRing.norm_star_mul_self]
  -- step one: the middle element is dominated by a scalar
  have hstep1 : NormedSpace.exp y * NormedSpace.exp ((2 : ℝ) • x) * NormedSpace.exp y
      ≤ (c * c) • (1 : A) := by
    have h := IsSelfAdjoint.le_algebraMap_norm_self (IsSelfAdjoint.of_nonneg hmidnonneg)
    rwa [hmidnorm, Algebra.algebraMap_eq_smul_one] at h
  -- step two: conjugate by `exp (-y)`
  have hstep2 : NormedSpace.exp ((2 : ℝ) • x) ≤ (c • NormedSpace.exp (-y)) ^ (2 : ℕ) := by
    have hconj := hnegy.exp.conjugate_le_conjugate hstep1
    have hleft : NormedSpace.exp (-y)
        * (NormedSpace.exp y * NormedSpace.exp ((2 : ℝ) • x) * NormedSpace.exp y)
        * NormedSpace.exp (-y) = NormedSpace.exp ((2 : ℝ) • x) := by
      have h1 : NormedSpace.exp (-y)
          * (NormedSpace.exp y * NormedSpace.exp ((2 : ℝ) • x) * NormedSpace.exp y)
          * NormedSpace.exp (-y)
          = (NormedSpace.exp (-y) * NormedSpace.exp y) * NormedSpace.exp ((2 : ℝ) • x)
            * (NormedSpace.exp y * NormedSpace.exp (-y)) := by noncomm_ring
      rw [h1, exp_neg_mul_exp, exp_mul_exp_neg, one_mul, mul_one]
    have hright : NormedSpace.exp (-y) * ((c * c) • (1 : A)) * NormedSpace.exp (-y)
        = (c • NormedSpace.exp (-y)) ^ (2 : ℕ) := by
      rw [sq, smul_mul_smul_comm, mul_smul_comm, smul_mul_assoc, mul_one]
    rwa [hleft, hright] at hconj
  -- step three: take square roots
  have hRnonneg : 0 ≤ c • NormedSpace.exp (-y) := smul_nonneg hc0 (nonneg_exp hnegy)
  have hstep3 : NormedSpace.exp x ≤ c • NormedSpace.exp (-y) := by
    have h := CFC.sqrt_le_sqrt _ _ hstep2
    rw [CFC.sqrt_sq _ hRnonneg] at h
    rwa [exp_two_smul, ← sq, CFC.sqrt_sq _ (nonneg_exp hx)] at h
  -- step four: conjugate by `exp (y / 2)`
  have hstep4 : NormedSpace.exp (((2 : ℝ)⁻¹) • y) * NormedSpace.exp x
      * NormedSpace.exp (((2 : ℝ)⁻¹) • y) ≤ c • (1 : A) := by
    have hconj := hhalfy.exp.conjugate_le_conjugate hstep3
    have hnegsplit : NormedSpace.exp (-y)
        = NormedSpace.exp (-(((2 : ℝ)⁻¹) • y)) * NormedSpace.exp (-(((2 : ℝ)⁻¹) • y)) := by
      rw [← smul_neg, exp_half_smul_mul_self (-y)]
    have hright : NormedSpace.exp (((2 : ℝ)⁻¹) • y) * (c • NormedSpace.exp (-y))
        * NormedSpace.exp (((2 : ℝ)⁻¹) • y) = c • (1 : A) := by
      rw [mul_smul_comm, smul_mul_assoc, hnegsplit]
      congr 1
      have h1 : NormedSpace.exp (((2 : ℝ)⁻¹) • y)
          * (NormedSpace.exp (-(((2 : ℝ)⁻¹) • y)) * NormedSpace.exp (-(((2 : ℝ)⁻¹) • y)))
          * NormedSpace.exp (((2 : ℝ)⁻¹) • y)
          = (NormedSpace.exp (((2 : ℝ)⁻¹) • y) * NormedSpace.exp (-(((2 : ℝ)⁻¹) • y)))
            * (NormedSpace.exp (-(((2 : ℝ)⁻¹) • y))
              * NormedSpace.exp (((2 : ℝ)⁻¹) • y)) := by noncomm_ring
      rw [h1, exp_mul_exp_neg, exp_neg_mul_exp, one_mul]
    rwa [hright] at hconj
  -- conclude
  have hid : NormedSpace.exp (((2 : ℝ)⁻¹) • y) * NormedSpace.exp x
      * NormedSpace.exp (((2 : ℝ)⁻¹) • y)
      = star (NormedSpace.exp (((2 : ℝ)⁻¹) • x) * NormedSpace.exp (((2 : ℝ)⁻¹) • y))
        * (NormedSpace.exp (((2 : ℝ)⁻¹) • x) * NormedSpace.exp (((2 : ℝ)⁻¹) • y)) := by
    rw [star_mul, (isSelfAdjoint_smul_real hx).exp.star_eq, hhalfy.exp.star_eq,
      ← exp_half_smul_mul_self x]
    noncomm_ring
  have hleftnonneg : 0 ≤ NormedSpace.exp (((2 : ℝ)⁻¹) • y) * NormedSpace.exp x
      * NormedSpace.exp (((2 : ℝ)⁻¹) • y) := by
    rw [hid]
    exact star_mul_self_nonneg _
  have hfinal := CStarAlgebra.norm_le_norm_of_nonneg_of_le hleftnonneg hstep4
  rw [norm_smul, norm_one, mul_one, Real.norm_eq_abs, abs_of_nonneg hc0] at hfinal
  rwa [sq, ← CStarRing.norm_star_mul_self, ← hid]

/-! ## The Golden–Thompson inequality for the norm -/

/-- The dyadic Cordes sequence is bounded by its first term. -/
theorem norm_exp_dyadic_le {x y : A} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) (m : ℕ) :
    ‖NormedSpace.exp ((((2 : ℝ) ^ m))⁻¹ • x) * NormedSpace.exp ((((2 : ℝ) ^ m))⁻¹ • y)‖ ^ (2 ^ m)
      ≤ ‖NormedSpace.exp x * NormedSpace.exp y‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : ∀ z : A, (((2 : ℝ) ^ (m + 1)))⁻¹ • z
        = ((2 : ℝ)⁻¹) • ((((2 : ℝ) ^ m))⁻¹ • z) := by
      intro z
      rw [smul_smul, pow_succ]
      congr 1
      field_simp
    have hcordes := norm_exp_half_mul_exp_half_sq_le
      (x := (((2 : ℝ) ^ m))⁻¹ • x) (y := (((2 : ℝ) ^ m))⁻¹ • y)
      (isSelfAdjoint_smul_real hx) (isSelfAdjoint_smul_real hy)
    rw [hsplit x, hsplit y]
    calc ‖NormedSpace.exp (((2 : ℝ)⁻¹) • ((((2 : ℝ) ^ m))⁻¹ • x))
            * NormedSpace.exp (((2 : ℝ)⁻¹) • ((((2 : ℝ) ^ m))⁻¹ • y))‖ ^ (2 ^ (m + 1))
        = (‖NormedSpace.exp (((2 : ℝ)⁻¹) • ((((2 : ℝ) ^ m))⁻¹ • x))
            * NormedSpace.exp (((2 : ℝ)⁻¹) • ((((2 : ℝ) ^ m))⁻¹ • y))‖ ^ (2 : ℕ)) ^ (2 ^ m) := by
          rw [← pow_mul, pow_succ, mul_comm (2 ^ m) 2]
      _ ≤ ‖NormedSpace.exp ((((2 : ℝ) ^ m))⁻¹ • x)
            * NormedSpace.exp ((((2 : ℝ) ^ m))⁻¹ • y)‖ ^ (2 ^ m) :=
          pow_le_pow_left₀ (by positivity) hcordes _
      _ ≤ ‖NormedSpace.exp x * NormedSpace.exp y‖ := ih

/-- **The Golden–Thompson inequality for the norm.**  For self-adjoint elements of a C⋆-algebra the
norm of the exponential of a sum is at most the norm of the product of the exponentials. -/
theorem norm_exp_add_le {x y : A} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) :
    ‖NormedSpace.exp (x + y)‖ ≤ ‖NormedSpace.exp x * NormedSpace.exp y‖ := by
  have hsub : Tendsto (fun m : ℕ => 2 ^ m) atTop atTop :=
    Filter.tendsto_atTop_mono (fun _ => Nat.lt_two_pow_self.le) Filter.tendsto_id
  have hlim := (tendsto_pow_exp_smul_inv x y).comp hsub
  have hnorm := hlim.norm
  refine le_of_tendsto hnorm ?_
  filter_upwards with m
  have hcast : (((2 ^ m : ℕ) : ℝ))⁻¹ = (((2 : ℝ) ^ m))⁻¹ := by
    push_cast
    ring
  calc ‖(NormedSpace.exp ((((2 ^ m : ℕ) : ℝ))⁻¹ • x)
        * NormedSpace.exp ((((2 ^ m : ℕ) : ℝ))⁻¹ • y)) ^ (2 ^ m)‖
      ≤ ‖NormedSpace.exp ((((2 ^ m : ℕ) : ℝ))⁻¹ • x)
        * NormedSpace.exp ((((2 ^ m : ℕ) : ℝ))⁻¹ • y)‖ ^ (2 ^ m) := norm_pow_le _ _
    _ ≤ ‖NormedSpace.exp x * NormedSpace.exp y‖ := by
        rw [hcast]
        exact norm_exp_dyadic_le hx hy m

end GaloisForLFunctions.HTGeometry
