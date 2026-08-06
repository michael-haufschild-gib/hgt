import GaloisForLFunctions.HTGeometry.GoldenThompsonNorm
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Cordes' inequality at a general exponent

For self-adjoint elements of a C⋆-algebra and `s ∈ [0,1]`,

```text
‖exp (s x) * exp (s y)‖ ≤ ‖exp x * exp y‖ ^ s.
```

The proof is the one used at exponent one half, with operator monotonicity of the square root
replaced by operator monotonicity of the `s`-th power: the scalar bound on `exp y exp (2x) exp y`
is transported by conjugation to `exp (2x) ≤ exp (2z)`, where `z = (log c) 1 - y` absorbs the
scalar into the exponent; the `s`-th power keeps that inequality; and a second conjugation
returns the claim.

Writing the scalar as part of the exponent is what makes the middle step available: the
functional calculus is applied only to exponentials, where `(exp x) ^ s = exp (s x)`.
-/

namespace GaloisForLFunctions.HTGeometry

open NormedSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-! ## Exponentials of scalars -/

omit [PartialOrder A] [StarOrderedRing A] in
theorem exp_smul_one (r : ℝ) : NormedSpace.exp (r • (1 : A)) = Real.exp r • (1 : A) := by
  rw [← Algebra.algebraMap_eq_smul_one, ← NormedSpace.algebraMap_exp_comm r,
    Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one]

omit [PartialOrder A] [StarOrderedRing A] in
/-- An exponential with a scalar absorbed into the exponent. -/
theorem exp_smul_sub (r t : ℝ) (y : A) :
    NormedSpace.exp (t • (r • (1 : A) - y)) = Real.exp (t * r) • NormedSpace.exp (t • (-y)) := by
  have hsplit : t • (r • (1 : A) - y) = (t * r) • (1 : A) + t • (-y) := by
    rw [smul_sub, smul_smul, smul_neg, sub_eq_add_neg]
  have hcomm : Commute (((t * r) • (1 : A))) (t • (-y)) := by
    refine Commute.smul_left ?_ _
    exact (Commute.one_left _).smul_right _
  rw [hsplit, exp_add_of_commute' hcomm, exp_smul_one, smul_mul_assoc, one_mul]

/-! ## The `s`-th power of an exponential -/

/-- **The functional calculus power of an exponential is the exponential of the scaled
exponent.** -/
theorem exp_rpow {x : A} (hx : IsSelfAdjoint x) {s : ℝ} (hs : 0 ≤ s) :
    (NormedSpace.exp x) ^ s = NormedSpace.exp (s • x) := by
  have hsa : IsSelfAdjoint (s • x) := isSelfAdjoint_smul_real hx
  have hg : ContinuousOn (fun z : ℝ => z ^ s) (Real.exp '' spectrum ℝ x) :=
    ContinuousOn.rpow_const continuousOn_id fun z _ => Or.inr hs
  have hf : ContinuousOn Real.exp (spectrum ℝ x) := Real.continuous_exp.continuousOn
  have hcomp : cfc ((fun z : ℝ => z ^ s) ∘ Real.exp) x
      = cfc (fun z : ℝ => z ^ s) (cfc Real.exp x) := cfc_comp _ _ x hx hg hf
  have hsmul : cfc (fun z : ℝ => Real.exp (s • z)) x = cfc Real.exp (s • x) :=
    cfc_comp_smul s Real.exp x Real.continuous_exp.continuousOn hx
  have hfun : ((fun z : ℝ => z ^ s) ∘ Real.exp) = fun z : ℝ => Real.exp (s • z) := by
    funext z
    rw [Function.comp_apply, ← Real.exp_mul, smul_eq_mul, mul_comm]
  calc (NormedSpace.exp x) ^ s
      = (cfc Real.exp x) ^ s := by rw [CFC.real_exp_eq_normedSpace_exp hx]
    _ = cfc (fun z : ℝ => z ^ s) (cfc Real.exp x) :=
        CFC.rpow_eq_cfc_real (by rw [CFC.real_exp_eq_normedSpace_exp hx]; exact nonneg_exp hx)
    _ = cfc ((fun z : ℝ => z ^ s) ∘ Real.exp) x := hcomp.symm
    _ = cfc (fun z : ℝ => Real.exp (s • z)) x := by rw [hfun]
    _ = cfc Real.exp (s • x) := hsmul
    _ = NormedSpace.exp (s • x) := CFC.real_exp_eq_normedSpace_exp hsa

/-! ## Cordes' inequality -/

variable [NormOneClass A]

omit [PartialOrder A] [StarOrderedRing A] in
theorem exp_mul_exp_ne_zero (x y : A) : NormedSpace.exp x * NormedSpace.exp y ≠ 0 := by
  intro h
  have h1 : NormedSpace.exp (-x) * (NormedSpace.exp x * NormedSpace.exp y)
      * NormedSpace.exp (-y) = 1 := by
    have hre : NormedSpace.exp (-x) * (NormedSpace.exp x * NormedSpace.exp y)
        * NormedSpace.exp (-y)
        = (NormedSpace.exp (-x) * NormedSpace.exp x)
          * (NormedSpace.exp y * NormedSpace.exp (-y)) := by
      noncomm_ring
    rw [hre, exp_neg_mul_exp, exp_mul_exp_neg, one_mul]
  rw [h] at h1
  have hone : ‖(1 : A)‖ = 1 := norm_one
  rw [← h1] at hone
  simp at hone

/-- **Cordes' inequality**, in exponential form: for `s ∈ [0,1]` the `s`-th powers contract the
norm of the product.  The analytic input is operator monotonicity of the `s`-th power. -/
theorem norm_exp_smul_mul_exp_smul_le {x y : A} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖NormedSpace.exp (s • x) * NormedSpace.exp (s • y)‖
      ≤ ‖NormedSpace.exp x * NormedSpace.exp y‖ ^ s := by
  set c : ℝ := ‖NormedSpace.exp x * NormedSpace.exp y‖ with hc
  have hcpos : 0 < c := norm_pos_iff.2 (exp_mul_exp_ne_zero x y)
  set r : ℝ := Real.log c with hr
  set z : A := r • (1 : A) - y with hz
  have hzsa : IsSelfAdjoint z := by
    refine IsSelfAdjoint.sub ?_ hy
    exact isSelfAdjoint_smul_real (IsSelfAdjoint.one A)
  have hnegy : IsSelfAdjoint (-y) := hy.neg
  have hsy : IsSelfAdjoint (s • y) := isSelfAdjoint_smul_real hy
  -- the middle element and its scalar bound
  have hmid : NormedSpace.exp y * NormedSpace.exp ((2 : ℝ) • x) * NormedSpace.exp y
      = star (NormedSpace.exp x * NormedSpace.exp y)
        * (NormedSpace.exp x * NormedSpace.exp y) := by
    rw [star_mul, hx.exp.star_eq, hy.exp.star_eq, exp_two_smul]
    noncomm_ring
  have hmidnonneg : 0 ≤ NormedSpace.exp y * NormedSpace.exp ((2 : ℝ) • x) * NormedSpace.exp y := by
    rw [hmid]
    exact star_mul_self_nonneg _
  have hmidnorm : ‖NormedSpace.exp y * NormedSpace.exp ((2 : ℝ) • x) * NormedSpace.exp y‖
      = c * c := by
    rw [hmid, CStarRing.norm_star_mul_self]
  have hstep1 : NormedSpace.exp y * NormedSpace.exp ((2 : ℝ) • x) * NormedSpace.exp y
      ≤ (c * c) • (1 : A) := by
    have h := IsSelfAdjoint.le_algebraMap_norm_self (IsSelfAdjoint.of_nonneg hmidnonneg)
    rwa [hmidnorm, Algebra.algebraMap_eq_smul_one] at h
  -- conjugate by `exp (-y)`: the scalar is absorbed into the exponent
  have hstep2 : NormedSpace.exp ((2 : ℝ) • x) ≤ NormedSpace.exp ((2 : ℝ) • z) := by
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
    have hcc : Real.exp ((2 : ℝ) * r) = c * c := by
      rw [hr, show (2 : ℝ) * Real.log c = Real.log c + Real.log c by ring, Real.exp_add,
        Real.exp_log hcpos]
    have hright : NormedSpace.exp (-y) * ((c * c) • (1 : A)) * NormedSpace.exp (-y)
        = NormedSpace.exp ((2 : ℝ) • z) := by
      rw [hz, exp_smul_sub, hcc, mul_smul_comm, smul_mul_assoc, mul_one]
      congr 1
      have hsplit : (2 : ℝ) • (-y) = (-y) + (-y) := by
        rw [two_smul]
      rw [hsplit, exp_add_of_commute' (Commute.refl _)]
    rwa [hleft, hright] at hconj
  -- operator monotonicity of the `s`-th power
  have hstep3 : NormedSpace.exp ((s * 2) • x) ≤ NormedSpace.exp ((s * 2) • z) := by
    have h := CFC.rpow_le_rpow (p := s) ⟨hs0, hs1⟩ hstep2
    rwa [exp_rpow (isSelfAdjoint_smul_real hx) hs0, exp_rpow (isSelfAdjoint_smul_real hzsa) hs0,
      smul_smul, smul_smul] at h
  -- conjugate back by `exp (s y)`
  have hstep4 : NormedSpace.exp (s • y) * NormedSpace.exp ((s * 2) • x)
      * NormedSpace.exp (s • y) ≤ (c ^ s * c ^ s) • (1 : A) := by
    have hconj := hsy.exp.conjugate_le_conjugate hstep3
    have hcs : Real.exp ((s * 2) * r) = c ^ s * c ^ s := by
      rw [hr, show (s * 2) * Real.log c = Real.log c * s + Real.log c * s by ring,
        Real.exp_add, Real.exp_mul, Real.exp_log hcpos]
    have hright : NormedSpace.exp (s • y) * NormedSpace.exp ((s * 2) • z)
        * NormedSpace.exp (s • y) = (c ^ s * c ^ s) • (1 : A) := by
      rw [hz, exp_smul_sub, hcs, mul_smul_comm, smul_mul_assoc]
      congr 1
      have hsplit : (s * 2) • (-y) = -(s • y) + -(s • y) := by
        rw [mul_comm, ← smul_smul, two_smul, smul_neg]
      rw [hsplit, exp_add_of_commute' (Commute.refl _)]
      have hre : NormedSpace.exp (s • y)
          * (NormedSpace.exp (-(s • y)) * NormedSpace.exp (-(s • y)))
          * NormedSpace.exp (s • y)
          = (NormedSpace.exp (s • y) * NormedSpace.exp (-(s • y)))
            * (NormedSpace.exp (-(s • y)) * NormedSpace.exp (s • y)) := by noncomm_ring
      rw [hre, exp_mul_exp_neg, exp_neg_mul_exp, one_mul]
    rwa [hright] at hconj
  -- read off the norm
  have hid : NormedSpace.exp (s • y) * NormedSpace.exp ((s * 2) • x) * NormedSpace.exp (s • y)
      = star (NormedSpace.exp (s • x) * NormedSpace.exp (s • y))
        * (NormedSpace.exp (s • x) * NormedSpace.exp (s • y)) := by
    have hdouble : NormedSpace.exp ((s * 2) • x)
        = NormedSpace.exp (s • x) * NormedSpace.exp (s • x) := by
      have hsplit : (s * 2) • x = s • x + s • x := by
        rw [mul_comm, ← smul_smul, two_smul]
      rw [hsplit, exp_add_of_commute' (Commute.refl _)]
    rw [star_mul, (isSelfAdjoint_smul_real hx).exp.star_eq, hsy.exp.star_eq, hdouble]
    noncomm_ring
  have hnonneg : 0 ≤ NormedSpace.exp (s • y) * NormedSpace.exp ((s * 2) • x)
      * NormedSpace.exp (s • y) := by
    rw [hid]
    exact star_mul_self_nonneg _
  have hfinal := CStarAlgebra.norm_le_norm_of_nonneg_of_le hnonneg hstep4
  rw [norm_smul, norm_one, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (le_of_lt hcpos) s)
      (Real.rpow_nonneg (le_of_lt hcpos) s)), hid, CStarRing.norm_star_mul_self] at hfinal
  nlinarith [norm_nonneg (NormedSpace.exp (s • x) * NormedSpace.exp (s • y)),
    Real.rpow_nonneg (le_of_lt hcpos) s]


/-! ## The homothety contraction in the operator order -/

omit [NormOneClass A] in
/-- **A domination of exponentials survives raising to a power `s ∈ [0,1]`.**

```text
exp y ≤ c exp x   →   exp (s y) ≤ c ^ s exp (s x).
```

Only operator monotonicity of the `s`-th power is used: the scalar is carried inside the exponent,
where the power acts on it as an ordinary real power. -/
theorem exp_smul_le_of_exp_le {x y : A} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
    {c : ℝ} (hc : 0 < c) (h : NormedSpace.exp y ≤ c • NormedSpace.exp x)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    NormedSpace.exp (s • y) ≤ (c ^ s) • NormedSpace.exp (s • x) := by
  set z : A := Real.log c • (1 : A) + x with hzdef
  have hzsa : IsSelfAdjoint z := by
    refine IsSelfAdjoint.add ?_ hx
    exact isSelfAdjoint_smul_real (IsSelfAdjoint.one A)
  have hgen : ∀ t : ℝ, NormedSpace.exp (t • z)
      = Real.exp (t * Real.log c) • NormedSpace.exp (t • x) := by
    intro t
    have ht := exp_smul_sub (Real.log c) t (-x)
    rwa [sub_neg_eq_add, neg_neg] at ht
  have h1 : NormedSpace.exp y ≤ NormedSpace.exp z := by
    have := hgen 1
    rw [one_smul, one_smul, one_mul, Real.exp_log hc] at this
    rw [this]
    exact h
  have h2 := CFC.rpow_le_rpow (p := s) ⟨hs0, hs1⟩ h1
  rw [exp_rpow hy hs0, exp_rpow hzsa hs0, hgen s,
    show Real.exp (s * Real.log c) = c ^ s from by
      rw [Real.rpow_def_of_pos hc, mul_comm]] at h2
  exact h2

end GaloisForLFunctions.HTGeometry
