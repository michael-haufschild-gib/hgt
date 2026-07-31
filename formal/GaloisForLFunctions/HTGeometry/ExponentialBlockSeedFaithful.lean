import GaloisForLFunctions.HTGeometry.ExponentialBlockSeed

/-!
# The block seed is faithful modulo constants

The symbols of the block seed at the parameters `t = m · 2πi / step k` evaluate the polynomial at the
points `u j ^ m − 1`, `u j = exp (2πi · step j / step k)`.  Integer independence of the block steps
makes the nodes `∏_j u j ^ ν j` pairwise distinct on exponents supported in `B ∖ {k}`, so an
exponential-sum Vandermonde argument turns the vanishing of all those symbols into the vanishing of
every coefficient.

Consequently a polynomial with a monomial supported inside `B` but missing a vertex of `B` has a
nonconstant carrier: choosing `k` to be a missing vertex makes its coefficient survive.

* `exponentialSum_coeff_eq_zero` — vanishing of `∑ c i z i ^ m` for all `m ≥ 1` with distinct
  nonzero nodes forces `c = 0`;
* `StepIndep` — integer independence of the block steps;
* `exists_ne_seedCarrierPoly_blockSeedFun` — the faithfulness statement.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### An exponential-sum Vandermonde lemma -/

/-- **Distinct nonzero nodes are separated by the powers `m ≥ 1`.**  Subtracting `z a` times the
`m`-th equation from the `(m+1)`-st removes one node, which drives an induction on the index set. -/
theorem exponentialSum_coeff_eq_zero {ι : Type*} [DecidableEq ι] (z : ι → ℂ) :
    ∀ S : Finset ι, Set.InjOn z ↑S → (∀ i ∈ S, z i ≠ 0) →
      ∀ c : ι → ℂ, (∀ m : ℕ, 1 ≤ m → ∑ i ∈ S, c i * z i ^ m = 0) → ∀ i ∈ S, c i = 0 := by
  intro S
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S' ha ih =>
    intro hinj hz0 c h
    have hstep : ∀ m : ℕ, 1 ≤ m → ∑ i ∈ S', (c i * (z i - z a)) * z i ^ m = 0 := by
      intro m hm
      have h1 := h (m + 1) (by omega)
      have h2 := h m hm
      have hkey : ∑ i ∈ insert a S', c i * z i ^ m * (z i - z a)
          = ∑ i ∈ insert a S', c i * z i ^ (m + 1)
            - z a * ∑ i ∈ insert a S', c i * z i ^ m := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [h1, h2] at hkey
      have hzero : ∑ i ∈ insert a S', c i * z i ^ m * (z i - z a) = 0 := by
        rw [hkey]; ring
      rw [Finset.sum_insert ha] at hzero
      have hane : c a * z a ^ m * (z a - z a) = 0 := by rw [sub_self, mul_zero]
      rw [hane, zero_add] at hzero
      rw [← hzero]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hS' : ∀ i ∈ S', c i * (z i - z a) = 0 :=
      ih (hinj.mono (Finset.coe_subset.mpr (Finset.subset_insert a S')))
        (fun i hi => hz0 i (Finset.mem_insert_of_mem hi))
        (fun i => c i * (z i - z a)) hstep
    have hczero : ∀ i ∈ S', c i = 0 := by
      intro i hi
      have hne : z i - z a ≠ 0 := by
        intro hz
        have hza : z i = z a := sub_eq_zero.mp hz
        have hia : i = a :=
          hinj (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hi))
            (Finset.mem_coe.mpr (Finset.mem_insert_self a S')) hza
        exact ha (hia ▸ hi)
      exact (mul_eq_zero.mp (hS' i hi)).resolve_right hne
    have ha0 : c a = 0 := by
      have h1 := h 1 le_rfl
      rw [Finset.sum_insert ha] at h1
      have hrest : ∑ i ∈ S', c i * z i ^ 1 = 0 :=
        Finset.sum_eq_zero fun i hi => by rw [hczero i hi, zero_mul]
      rw [hrest, add_zero, pow_one] at h1
      exact (mul_eq_zero.mp h1).resolve_right (hz0 a (Finset.mem_insert_self a S'))
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact ha0
    · exact hczero i hi'

/-! ### Restriction and translation of polynomials -/

variable {α : Type*} [DecidableEq α]

/-- The part of a polynomial supported on a given vertex set. -/
def restrictPoly (T : Finset α) (P : MvPolynomial α ℂ) : MvPolynomial α ℂ :=
  ∑ d ∈ P.support.filter (fun d => d.support ⊆ T), monomial d (coeff d P)

theorem coeff_restrictPoly {T : Finset α} (P : MvPolynomial α ℂ) {ν : α →₀ ℕ}
    (hν : ν.support ⊆ T) : coeff ν (restrictPoly T P) = coeff ν P := by
  classical
  rw [restrictPoly, coeff_sum]
  by_cases hmem : ν ∈ P.support
  · rw [Finset.sum_eq_single ν]
    · rw [coeff_monomial, if_pos rfl]
    · intro d _ hdν
      rw [coeff_monomial, if_neg hdν]
    · intro hcon
      exact absurd (Finset.mem_filter.mpr ⟨hmem, hν⟩) hcon
  · have hzero : coeff ν P = 0 := by
      simpa [MvPolynomial.mem_support_iff] using hmem
    rw [hzero]
    refine Finset.sum_eq_zero fun d hd => ?_
    rw [coeff_monomial, if_neg]
    intro hdν
    subst hdν
    exact hmem (Finset.mem_filter.mp hd).1

theorem vars_monomial_subset_support (d : α →₀ ℕ) (a : ℂ) :
    (monomial d a).vars ⊆ d.support := by
  classical
  by_cases ha : a = 0
  · rw [ha, map_zero]
    simp
  · rw [vars_monomial ha]

theorem vars_restrictPoly (T : Finset α) (P : MvPolynomial α ℂ) :
    (restrictPoly T P).vars ⊆ T := by
  classical
  refine (vars_sum_subset _ _).trans ?_
  refine Finset.biUnion_subset.mpr fun d hd => ?_
  exact (vars_monomial_subset_support d (coeff d P)).trans (Finset.mem_filter.mp hd).2

theorem eval_restrictPoly {T : Finset α} (P : MvPolynomial α ℂ) {y : α → ℂ}
    (hy : ∀ j ∉ T, y j = 0) : eval y (restrictPoly T P) = eval y P := by
  classical
  have hL : eval y (restrictPoly T P)
      = ∑ d ∈ P.support.filter (fun d => d.support ⊆ T),
          coeff d P * ∏ i ∈ d.support, y i ^ d i := by
    rw [restrictPoly, map_sum]
    exact Finset.sum_congr rfl fun d _ => by rw [eval_monomial, Finsupp.prod]
  have hR : eval y P
      = (∑ d ∈ P.support.filter (fun d => d.support ⊆ T),
          coeff d P * ∏ i ∈ d.support, y i ^ d i)
        + ∑ d ∈ P.support.filter (fun d => ¬ d.support ⊆ T),
          coeff d P * ∏ i ∈ d.support, y i ^ d i := by
    rw [MvPolynomial.eval_eq, Finset.sum_filter_add_sum_filter_not]
  have hvanish : ∑ d ∈ P.support.filter (fun d => ¬ d.support ⊆ T),
      coeff d P * ∏ i ∈ d.support, y i ^ d i = 0 := by
    refine Finset.sum_eq_zero fun d hd => ?_
    obtain ⟨j, hjd, hjT⟩ := Finset.not_subset.mp (Finset.mem_filter.mp hd).2
    have hprod : ∏ i ∈ d.support, y i ^ d i = 0 := by
      refine Finset.prod_eq_zero hjd ?_
      rw [hy j hjT, zero_pow]
      exact Finsupp.mem_support_iff.mp hjd
    rw [hprod, mul_zero]
  rw [hL, hR, hvanish, add_zero]

/-! ### Integer independence of the steps -/

/-- Integer independence of the block steps. -/
def StepIndep (B : Finset α) (step : α → ℂ) : Prop :=
  ∀ g : α → ℤ, (∑ v ∈ B, (g v : ℂ) * step v) = 0 → ∀ v ∈ B, g v = 0

theorem stepIndep_ne_zero {B : Finset α} {step : α → ℂ} (h : StepIndep B step) {v : α}
    (hv : v ∈ B) : step v ≠ 0 := by
  intro hzero
  classical
  set g : α → ℤ := fun u => if u = v then 1 else 0 with hg
  have hsum : (∑ u ∈ B, (g u : ℂ) * step u) = 0 := by
    refine Finset.sum_eq_zero fun u _ => ?_
    by_cases hu : u = v
    · subst hu
      rw [hzero, mul_zero]
    · simp [hg, hu]
  have hv0 := h g hsum v hv
  simp [hg] at hv0

/-- Two-element integer relations among the steps are trivial. -/
theorem step_pair_relation {B : Finset α} {step : α → ℂ} (h : StepIndep B step)
    {j k : α} (hj : j ∈ B) (hk : k ∈ B) (hjk : j ≠ k) {p q : ℤ}
    (hrel : (p : ℂ) * step j + (q : ℂ) * step k = 0) : p = 0 := by
  classical
  set g : α → ℤ := fun v => if v = j then p else if v = k then q else 0 with hg
  have hsum : (∑ v ∈ B, (g v : ℂ) * step v) = 0 := by
    have hsub : ({j, k} : Finset α) ⊆ B := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact hj
      · rw [Finset.mem_singleton] at hx'; subst hx'; exact hk
    rw [← Finset.sum_subset hsub]
    · rw [Finset.sum_pair hjk]
      have hgj : g j = p := by simp [hg]
      have hgk : g k = q := by simp [hg, hjk.symm]
      rw [hgj, hgk]
      exact hrel
    · intro x _ hx
      have hxj : x ≠ j := fun hc => hx (by rw [hc]; simp)
      have hxk : x ≠ k := fun hc => hx (by rw [hc]; simp)
      simp [hg, hxj, hxk]
  have := h g hsum j hj
  simpa [hg] using this

end

end GaloisForLFunctions.HTGeometry
