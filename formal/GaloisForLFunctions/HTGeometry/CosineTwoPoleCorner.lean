import GaloisForLFunctions.HTGeometry.CosinePoleUnit
import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch

/-! # The general two-pole logarithmic conic corner

Two analytic logarithmic units and arbitrary positive pole orders give an
analytic conic branch. Integer periods then yield exact cosine coordinates.
Only the scalar analytic implicit-function theorem is used from the legacy
parametric-branch import; no spectral argument enters this proof.
-/

namespace GaloisForLFunctions.HTGeometry.CosineTwoPoleCorner

open Complex Filter
open scoped Topology

noncomputable section

private theorem partial_apply_one
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {f : P × ℂ → ℂ} {p : P} {u d : ℂ}
    (hf : DifferentiableAt ℂ f (p, u))
    (hd : HasDerivAt (fun z : ℂ ↦ f (p, z)) d u) :
    (fderiv ℂ f (p, u)) (0, 1) = d := by
  have hi : HasFDerivAt (fun z : ℂ ↦ (p, z)) (ContinuousLinearMap.inr ℂ P ℂ) u := by
    simpa using ((ContinuousLinearMap.inr ℂ P ℂ).hasFDerivAt (x := u)).add_const (p, (0 : ℂ))
  have hc := hf.hasFDerivAt.comp u hi
  have he := congrArg (fun L : ℂ →L[ℂ] ℂ ↦ L 1) (hc.unique hd.hasFDerivAt)
  simpa using he

def small (p : (ℂ × ℂ) × ℂ) : ℂ := p.1.2 * exp p.2

def argument (α : ℂ → ℂ) (m : ℕ) (p : (ℂ × ℂ) × ℂ) : ℂ :=
  I * m * p.2 - I * α (small p)

def direction (m r : ℕ) : ℂ := 2 * Real.pi * ((r : ℂ) - I * m)

def equation (α β : ℂ → ℂ) (m r : ℕ) (c : ℂ) (p : (ℂ × ℂ) × ℂ) : ℂ :=
  2 * direction m r * (argument α m p - I * argument β r p) +
    p.1.1 * (argument α m p ^ 2 + argument β r p ^ 2 - c)

def center (α β : ℂ → ℂ) (m r : ℕ) : ℂ :=
  (β 0 + I * α 0) / ((r : ℂ) + I * m)

theorem exponential_pole_lift (L ell a : ℂ) (k : ℤ) (m : ℕ) :
    exp ((2 * Real.pi * k + I * m * (ell - L) - I * a) * I) =
      exp a / (exp (-L) * exp ell) ^ m := by
  calc
    _ = exp ((k : ℂ) * (2 * Real.pi * I)) * exp (a - (m : ℂ) * (ell - L)) := by
      rw [← exp_add]
      congr 1
      ring_nf
      simp only [I_sq]
      ring
    _ = exp a / (exp (-L) * exp ell) ^ m := by
      rw [exp_int_mul_two_pi_mul_I, one_mul, exp_sub, exp_nat_mul, ← exp_add]
      congr 3
      ring

theorem equation_corner (α β : ℂ → ℂ) (m r : ℕ) (c ell : ℂ) :
    equation α β m r c ((0, 0), ell) =
      2 * direction m r * (((r : ℂ) + I * m) * ell - (β 0 + I * α 0)) := by
  simp only [equation, argument, small, zero_mul, add_zero]
  ring_nf
  simp only [I_sq]
  ring

theorem direction_ne_zero (m r : ℕ) (hr : 0 < r) : direction m r ≠ 0 := by
  apply mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
  intro h
  have h' := congrArg Complex.re h
  simp at h'
  exact (Nat.ne_of_gt hr) h'

theorem center_denominator_ne_zero (m r : ℕ) (hr : 0 < r) :
    (r : ℂ) + I * m ≠ 0 := by
  intro h
  have h' := congrArg Complex.re h
  simp at h'
  exact (Nat.ne_of_gt hr) h'

theorem argument_analyticAt {α : ℂ → ℂ} (hα : AnalyticAt ℂ α 0) (m : ℕ) (ell : ℂ) :
    AnalyticAt ℂ (argument α m) ((0, 0), ell) := by
  have hs : AnalyticAt ℂ small ((0, 0), ell) :=
    (analyticAt_snd.comp (f := Prod.fst) analyticAt_fst).mul
      ((Complex.differentiable_exp.analyticAt ell).comp
        (f := fun p : (ℂ × ℂ) × ℂ => p.2) analyticAt_snd)
  have hα' : AnalyticAt ℂ α (small ((0, 0), ell)) := by simpa [small] using hα
  exact (analyticAt_const.mul analyticAt_snd).sub
    (analyticAt_const.mul (hα'.comp hs))

theorem equation_analyticAt {α β : ℂ → ℂ}
    (hα : AnalyticAt ℂ α 0) (hβ : AnalyticAt ℂ β 0) (m r : ℕ) (c ell : ℂ) :
    AnalyticAt ℂ (equation α β m r c) ((0, 0), ell) := by
  have hu := argument_analyticAt hα m ell
  have hv := argument_analyticAt hβ r ell
  have ht : AnalyticAt ℂ (fun p : (ℂ × ℂ) × ℂ => p.1.1) ((0, 0), ell) :=
    analyticAt_fst.comp (f := Prod.fst) analyticAt_fst
  exact (analyticAt_const.mul (hu.sub (analyticAt_const.mul hv))).add
    (ht.mul (((hu.pow 2).add (hv.pow 2)).sub analyticAt_const))

theorem exists_corner {α β : ℂ → ℂ}
    (hα : AnalyticAt ℂ α 0) (hβ : AnalyticAt ℂ β 0) (m r : ℕ) (hr : 0 < r) (c : ℂ) :
    ∃ ell : ℂ × ℂ → ℂ, AnalyticAt ℂ ell (0, 0) ∧
      ell (0, 0) = center α β m r ∧
      ∀ᶠ p in 𝓝 (0, 0), equation α β m r c (p, ell p) = 0 := by
  have hf := equation_analyticAt hα hβ m r c (center α β m r)
  have hroot : equation α β m r c ((0, 0), center α β m r) = 0 := by
    rw [equation_corner, center, mul_div_cancel₀ _ (center_denominator_ne_zero m r hr),
      sub_self, mul_zero]
  have hd : HasDerivAt (fun z : ℂ => equation α β m r c ((0, 0), z))
      (2 * direction m r * ((r : ℂ) + I * m)) (center α β m r) := by
    simp_rw [equation_corner]
    simpa using (((hasDerivAt_id (center α β m r)).const_mul ((r : ℂ) + I * m)).sub_const
      (β 0 + I * α 0)).const_mul (2 * direction m r)
  apply parametric_holo_implicit hf hroot
  rw [partial_apply_one hf.differentiableAt hd]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (direction_ne_zero m r hr))
    (center_denominator_ne_zero m r hr)

theorem conic_of_equation {n q ell c : ℂ} {α β : ℂ → ℂ} {m r : ℕ}
    (hn : n ≠ 0) (he : equation α β m r c ((n⁻¹, q), ell) = 0) :
    (n * direction m r + argument α m ((n⁻¹, q), ell)) ^ 2 +
      (-I * n * direction m r + argument β r ((n⁻¹, q), ell)) ^ 2 = c := by
  let u := argument α m ((n⁻¹, q), ell)
  let v := argument β r ((n⁻¹, q), ell)
  let C := direction m r
  change 2 * C * (u - I * v) + n⁻¹ * (u ^ 2 + v ^ 2 - c) = 0 at he
  have h : 2 * n * C * (u - I * v) + (u ^ 2 + v ^ 2 - c) = 0 := by
    have h' := congrArg (fun z : ℂ => n * z) he
    simpa only [mul_add, ← mul_assoc, mul_inv_cancel₀ hn, one_mul, mul_zero, mul_comm n 2]
      using h'
  change (n * C + u) ^ 2 + (-I * n * C + v) ^ 2 = c
  linear_combination h + (n * C) ^ 2 * I_sq

def parameters (n : ℕ) : ℂ × ℂ :=
  ((n : ℂ)⁻¹, exp (-(n : ℂ) * (2 * Real.pi)))

def firstLift (α : ℂ → ℂ) (m r n : ℕ) (ell : ℂ) : ℂ :=
  n * direction m r + argument α m (parameters n, ell)

def secondLift (β : ℂ → ℂ) (m r n : ℕ) (ell : ℂ) : ℂ :=
  -I * n * direction m r + argument β r (parameters n, ell)

theorem firstLift_exp (α : ℂ → ℂ) (m r n : ℕ) (ell : ℂ) :
    exp (firstLift α m r n ell * I) =
      exp (α (small (parameters n, ell))) / small (parameters n, ell) ^ m := by
  have h := exponential_pole_lift ((n : ℂ) * (2 * Real.pi)) ell
    (α (small (parameters n, ell))) (n * r : ℤ) m
  convert! h using 1
  · congr 1
    dsimp [firstLift, direction, argument]
    push_cast
    ring
  · simp only [small, parameters, neg_mul]

theorem secondLift_exp (β : ℂ → ℂ) (m r n : ℕ) (ell : ℂ) :
    exp (secondLift β m r n ell * I) =
      exp (β (small (parameters n, ell))) / small (parameters n, ell) ^ r := by
  have h := exponential_pole_lift ((n : ℂ) * (2 * Real.pi)) ell
    (β (small (parameters n, ell))) (-(n * m) : ℤ) r
  convert! h using 1
  · congr 1
    dsimp [secondLift, direction, argument]
    push_cast
    ring_nf
    simp only [I_sq, show I ^ 3 = -I by linear_combination I * I_sq]
    ring
  · simp only [small, parameters, neg_mul]

theorem small_parameters_ne_zero (n : ℕ) (ell : ℂ) : small (parameters n, ell) ≠ 0 :=
  mul_ne_zero (exp_ne_zero _) (exp_ne_zero _)

theorem cosine_lifts {A B α β : ℂ → ℂ} {m r n : ℕ} {ell : ℂ}
    (hA : exp (α (small (parameters n, ell))) ^ 2 -
      2 * A (small (parameters n, ell)) * exp (α (small (parameters n, ell))) +
      small (parameters n, ell) ^ (2 * m) = 0)
    (hB : exp (β (small (parameters n, ell))) ^ 2 -
      2 * B (small (parameters n, ell)) * exp (β (small (parameters n, ell))) +
      small (parameters n, ell) ^ (2 * r) = 0) :
    cos (firstLift α m r n ell) = A (small (parameters n, ell)) / small (parameters n, ell) ^ m ∧
    cos (secondLift β m r n ell) = B (small (parameters n, ell)) / small (parameters n, ell) ^ r := by
  exact ⟨CosinePoleUnit.cosine_of_unit_equation (small_parameters_ne_zero n ell)
      (exp_ne_zero _) hA (firstLift_exp α m r n ell),
    CosinePoleUnit.cosine_of_unit_equation (small_parameters_ne_zero n ell)
      (exp_ne_zero _) hB (secondLift_exp β m r n ell)⟩

end

end GaloisForLFunctions.HTGeometry.CosineTwoPoleCorner
