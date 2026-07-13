import Mathlib
import GaloisForLFunctions.HTGeometry.EntireJetEvaluation

/-!
# Structure constants of the Taylor conditions of a differential polynomial

For an entire function whose derivatives at the origin all lie in a subfield `K ⊆ ℂ`, every
Taylor coefficient of every jet monomial also lies in `K`: products propagate membership
through the Leibniz formula with integer binomial weights, the point slot contributes the
derivatives of the identity, and the jet slots contribute shifted derivatives of the
function (`iteratedDeriv_jetEval_monomial_mem`).  Consequently the `k`-th Taylor condition
of a candidate annihilator is an explicit `K`-linear form in its coefficients
(`iteratedDeriv_jetEval_eq_sum`): the structure constants of the countable condition family
of the differential-algebraicity criterion are defined over `K`.
-/

open MvPolynomial

namespace GaloisForLFunctions

section MembershipClosure

variable {K : Subfield ℂ}

/-- Derivatives of the identity at the origin lie in every subfield. -/
theorem iteratedDeriv_id_zero_mem (k : ℕ) :
    iteratedDeriv k (fun z : ℂ => z) 0 ∈ K := by
  match k with
  | 0 => simp [iteratedDeriv_zero]
  | 1 =>
    rw [iteratedDeriv_one]
    simp
  | (k + 2) =>
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    have h1 : deriv (fun z : ℂ => z) = fun _ => 1 := by
      funext z
      simp
    rw [h1]
    have h2 : deriv (fun _ : ℂ => (1 : ℂ)) = fun _ => 0 := by
      funext z
      simp
    rw [h2]
    simp

/-- Shifted derivatives: derivatives of a jet are higher derivatives of the function. -/
theorem iteratedDeriv_iteratedDeriv (j k : ℕ) (f : ℂ → ℂ) :
    iteratedDeriv k (iteratedDeriv j f) = iteratedDeriv (k + j) f := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    ← Function.iterate_add_apply]

/-- Membership at the origin propagates through products of entire functions, by Leibniz. -/
theorem iteratedDeriv_mul_zero_mem {u v : ℂ → ℂ}
    (hu : Differentiable ℂ u) (hv : Differentiable ℂ v)
    (hum : ∀ k, iteratedDeriv k u 0 ∈ K) (hvm : ∀ k, iteratedDeriv k v 0 ∈ K) (k : ℕ) :
    iteratedDeriv k (u * v) 0 ∈ K := by
  have hcu : ContDiffAt ℂ (k : WithTop ℕ∞) u 0 :=
    ((hu.differentiableOn.analyticOnNhd isOpen_univ) 0 (Set.mem_univ 0)).contDiffAt
  have hcv : ContDiffAt ℂ (k : WithTop ℕ∞) v 0 :=
    ((hv.differentiableOn.analyticOnNhd isOpen_univ) 0 (Set.mem_univ 0)).contDiffAt
  rw [iteratedDeriv_mul hcu hcv]
  exact sum_mem fun i _ =>
    mul_mem (mul_mem (natCast_mem K _) (hum i)) (hvm (k - i))

/-- Membership propagates through powers of entire functions. -/
theorem iteratedDeriv_pow_zero_mem {u : ℂ → ℂ} (hu : Differentiable ℂ u)
    (hum : ∀ k, iteratedDeriv k u 0 ∈ K) (r : ℕ) (k : ℕ) :
    iteratedDeriv k (u ^ r) 0 ∈ K := by
  induction r generalizing k with
  | zero =>
    rw [pow_zero]
    match k with
    | 0 => simp [iteratedDeriv_zero]
    | (k + 1) =>
      rw [iteratedDeriv_succ']
      have h1 : deriv ((1 : ℂ → ℂ)) = fun _ => 0 := by
        funext z
        simp [Pi.one_def]
      rw [h1]
      simp
  | succ r ih =>
    rw [pow_succ]
    exact iteratedDeriv_mul_zero_mem (hu.pow r) hu (fun k' => ih k') hum k

end MembershipClosure

section StructureConstants

variable {K : Subfield ℂ} {f : ℂ → ℂ}

/-- The jet-slot functions of the differential-algebraicity frame. -/
noncomputable def jetSlot (f : ℂ → ℂ) (n : ℕ) (i : Fin (n + 2)) : ℂ → ℂ :=
  Fin.cases (fun z => z) (fun j => iteratedDeriv (j : ℕ) f) i

theorem differentiable_jetSlot (hf : Differentiable ℂ f) (n : ℕ) (i : Fin (n + 2)) :
    Differentiable ℂ (jetSlot f n i) := by
  induction i using Fin.cases with
  | zero => simp [jetSlot]
  | succ j =>
    simpa [jetSlot] using differentiable_iteratedDeriv_of_entire hf (j : ℕ)

theorem iteratedDeriv_jetSlot_zero_mem (n : ℕ)
    (hK : ∀ j, iteratedDeriv j f 0 ∈ K) (i : Fin (n + 2)) (k : ℕ) :
    iteratedDeriv k (jetSlot f n i) 0 ∈ K := by
  induction i using Fin.cases with
  | zero => simpa [jetSlot] using iteratedDeriv_id_zero_mem (K := K) k
  | succ j =>
    have h : iteratedDeriv k (iteratedDeriv (j : ℕ) f) 0 = iteratedDeriv (k + j) f 0 := by
      rw [iteratedDeriv_iteratedDeriv]
    simpa [jetSlot, h] using hK (k + j)

/-- **Structure constants lie in the coefficient field**: every origin Taylor coefficient of
every jet monomial of an entire function with `K`-rational derivatives lies in `K`. -/
theorem iteratedDeriv_jetEval_monomial_mem (hf : Differentiable ℂ f) (n : ℕ)
    (hK : ∀ j, iteratedDeriv j f 0 ∈ K) (m : Fin (n + 2) →₀ ℕ) (k : ℕ) :
    iteratedDeriv k (fun z => MvPolynomial.eval
      (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)
      (monomial m (1 : ℂ))) 0 ∈ K := by
  have hfun : (fun z => MvPolynomial.eval
      (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) (monomial m (1 : ℂ)))
      = ∏ i ∈ m.support, (jetSlot f n i) ^ (m i) := by
    funext z
    rw [eval_monomial, one_mul, Finsupp.prod, Finset.prod_apply]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.pow_apply]
    congr 1
    induction i using Fin.cases with
    | zero => simp [jetSlot]
    | succ j => simp [jetSlot]
  rw [hfun]
  clear hfun
  induction m.support using Finset.induction_on generalizing k with
  | empty =>
    rw [Finset.prod_empty]
    match k with
    | 0 => simp [iteratedDeriv_zero]
    | (k + 1) =>
      rw [iteratedDeriv_succ']
      have h1 : deriv ((1 : ℂ → ℂ)) = fun _ => 0 := by
        funext z
        simp [Pi.one_def]
      rw [h1]
      simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    refine iteratedDeriv_mul_zero_mem ?_ ?_ ?_ (fun k' => ih k') k
    · exact (differentiable_jetSlot hf n i).pow (m i)
    · exact Finset.prod_induction _ _ (fun a b ha hb => ha.mul hb)
        (differentiable_const 1) (fun j _ => (differentiable_jetSlot hf n j).pow (m j))
    · exact fun k' => iteratedDeriv_pow_zero_mem (differentiable_jetSlot hf n i)
        (iteratedDeriv_jetSlot_zero_mem n hK i) (m i) k'

end StructureConstants

end GaloisForLFunctions
