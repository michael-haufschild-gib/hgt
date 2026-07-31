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

omit [DecidableEq α] in
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

/-! ### The nodes attached to exponents -/

/-- The ratio character of a block vertex relative to the base vertex `k`. -/
def stepRatio (step : α → ℂ) (k : α) : α → ℂ :=
  fun j => Complex.exp (expStepRate (step k) * step j)

/-- The Vandermonde node attached to an exponent. -/
def stepNode (step : α → ℂ) (k : α) (ν : α →₀ ℕ) : ℂ :=
  ∏ i ∈ ν.support, stepRatio step k i ^ ν i

omit [DecidableEq α] in
theorem stepNode_ne_zero (step : α → ℂ) (k : α) (ν : α →₀ ℕ) : stepNode step k ν ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  exact pow_ne_zero _ (Complex.exp_ne_zero _)

omit [DecidableEq α] in
theorem stepNode_eq_exp (step : α → ℂ) (k : α) (ν : α →₀ ℕ) :
    stepNode step k ν
      = Complex.exp (expStepRate (step k) * ∑ i ∈ ν.support, (ν i : ℂ) * step i) := by
  rw [stepNode, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [stepRatio, ← Complex.exp_nat_mul]
  ring_nf

/-- **The nodes separate exponents supported off the base vertex.** -/
theorem stepNode_injective_of_stepIndep {B : Finset α} {step : α → ℂ}
    (hindep : StepIndep B step) {k : α} (hk : k ∈ B) {ν ν' : α →₀ ℕ}
    (hν : ν.support ⊆ B.erase k) (hν' : ν'.support ⊆ B.erase k)
    (heq : stepNode step k ν = stepNode step k ν') : ν = ν' := by
  classical
  have hk0 : step k ≠ 0 := stepIndep_ne_zero hindep hk
  rw [stepNode_eq_exp, stepNode_eq_exp] at heq
  have hexp : Complex.exp (expStepRate (step k) *
      ((∑ i ∈ ν.support, (ν i : ℂ) * step i) - ∑ i ∈ ν'.support, (ν' i : ℂ) * step i)) = 1 := by
    rw [mul_sub, Complex.exp_sub, heq, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  have hstepk : expStepRate (step k) = 2 * Real.pi * Complex.I / step k := rfl
  have hrel : (∑ i ∈ ν.support, (ν i : ℂ) * step i)
      - (∑ i ∈ ν'.support, (ν' i : ℂ) * step i) - (n : ℂ) * step k = 0 := by
    rw [hstepk] at hn
    field_simp at hn
    linear_combination hn
  set g : α → ℤ := fun v => (ν v : ℤ) - (ν' v : ℤ) - (if v = k then n else 0) with hg
  have hsupp : ∀ i ∈ B, ((ν i : ℂ) * step i) = if i ∈ ν.support then (ν i : ℂ) * step i else 0 := by
    intro i _
    by_cases hi : i ∈ ν.support
    · rw [if_pos hi]
    · rw [if_neg hi, Finsupp.notMem_support_iff.mp hi]
      simp
  have hsum1 : ∑ i ∈ B, (ν i : ℂ) * step i = ∑ i ∈ ν.support, (ν i : ℂ) * step i := by
    refine (Finset.sum_subset (hν.trans (Finset.erase_subset k B)) ?_).symm
    intro x _ hx
    rw [Finsupp.notMem_support_iff.mp hx]
    simp
  have hsum2 : ∑ i ∈ B, (ν' i : ℂ) * step i = ∑ i ∈ ν'.support, (ν' i : ℂ) * step i := by
    refine (Finset.sum_subset (hν'.trans (Finset.erase_subset k B)) ?_).symm
    intro x _ hx
    rw [Finsupp.notMem_support_iff.mp hx]
    simp
  have hsum : (∑ v ∈ B, (g v : ℂ) * step v) = 0 := by
    have hsplit : (∑ v ∈ B, (g v : ℂ) * step v)
        = (∑ v ∈ B, (ν v : ℂ) * step v) - (∑ v ∈ B, (ν' v : ℂ) * step v)
          - ∑ v ∈ B, (if v = k then (n : ℂ) else 0) * step v := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [hg]
      by_cases hv : v = k <;> push_cast [hv] <;> ring
    have hk' : ∑ v ∈ B, (if v = k then (n : ℂ) else 0) * step v = (n : ℂ) * step k := by
      rw [Finset.sum_eq_single k]
      · rw [if_pos rfl]
      · intro b _ hb
        rw [if_neg hb, zero_mul]
      · intro hcon
        exact absurd hk hcon
    rw [hsplit, hk', hsum1, hsum2, hrel]
  have hzero := hindep g hsum
  ext v
  by_cases hvB : v ∈ B
  · have hgv := hzero v hvB
    by_cases hvk : v = k
    · subst hvk
      have h1 : ν v = 0 := Finsupp.notMem_support_iff.mp fun hc =>
        (Finset.notMem_erase v B) (hν hc)
      have h2 : ν' v = 0 := Finsupp.notMem_support_iff.mp fun hc =>
        (Finset.notMem_erase v B) (hν' hc)
      rw [h1, h2]
    · rw [hg] at hgv
      simp only [if_neg hvk, sub_zero] at hgv
      omega
  · have h1 : ν v = 0 := Finsupp.notMem_support_iff.mp fun hc =>
      hvB (Finset.mem_of_mem_erase (hν hc))
    have h2 : ν' v = 0 := Finsupp.notMem_support_iff.mp fun hc =>
      hvB (Finset.mem_of_mem_erase (hν' hc))
    rw [h1, h2]

/-! ### Faithfulness of the block seed -/

omit [DecidableEq α] in
theorem aeval_eq_eval' (y : α → ℂ) (p : MvPolynomial α ℂ) : aeval y p = eval y p := rfl

omit [DecidableEq α] in
theorem stepRatio_pow (step : α → ℂ) (k j : α) (m : ℕ) :
    stepRatio step k j ^ m = Complex.exp ((m : ℂ) * expStepRate (step k) * step j) := by
  rw [stepRatio, ← Complex.exp_nat_mul, mul_assoc]

/-- The ratio character is trivial off the block and at the base vertex. -/
theorem stepRatio_eq_one {B : Finset α} {step : α → ℂ} (hoff : ∀ v ∉ B, step v = 0)
    {k : α} (hk0 : step k ≠ 0) {j : α} (hj : j ∉ B.erase k) : stepRatio step k j = 1 := by
  by_cases hjB : j ∈ B
  · have hjk : j = k := by
      by_contra hc
      exact hj (Finset.mem_erase.mpr ⟨hc, hjB⟩)
    subst hjk
    rw [stepRatio, expStepRate, div_mul_cancel₀ _ hk0, Complex.exp_two_pi_mul_I]
  · rw [stepRatio, hoff j hjB, mul_zero, Complex.exp_zero]

/-- Off the base vertex the ratio characters are not roots of unity. -/
theorem stepRatio_pow_ne_one {B : Finset α} {step : α → ℂ} (hindep : StepIndep B step)
    {k j : α} (hk : k ∈ B) (hj : j ∈ B) (hjk : j ≠ k) {m : ℕ} (hm : 1 ≤ m) :
    stepRatio step k j ^ m ≠ 1 := by
  intro hone
  rw [stepRatio_pow] at hone
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hone
  have hk0 : step k ≠ 0 := stepIndep_ne_zero hindep hk
  have hrel : ((m : ℤ) : ℂ) * step j + ((-n : ℤ) : ℂ) * step k = 0 := by
    rw [expStepRate] at hn
    field_simp at hn
    push_cast
    linear_combination hn
  have := step_pair_relation hindep hj hk hjk hrel
  omega

/-- **The block seed is faithful modulo constants.**  A polynomial with a monomial supported inside
the block and missing a block vertex has a nonconstant carrier. -/
theorem exists_ne_seedCarrierPoly_blockSeedFun {B : Finset α} {step : α → ℂ}
    (hoff : ∀ v ∉ B, step v = 0) (hindep : StepIndep B step) (P : MvPolynomial α ℂ)
    (hP : ∃ d ∈ P.support, d.support ⊆ B ∧ ¬ B ⊆ d.support) :
    ∃ x y, seedCarrierPoly step (blockSeedFun B step) P x
      ≠ seedCarrierPoly step (blockSeedFun B step) P y := by
  classical
  obtain ⟨d₀, hd₀P, hd₀B, hd₀ns⟩ := hP
  obtain ⟨k, hkB, hkd₀⟩ := Finset.not_subset.mp hd₀ns
  by_contra hcontra
  have hcon : ∀ x y : ℂ, seedCarrierPoly step (blockSeedFun B step) P x
      = seedCarrierPoly step (blockSeedFun B step) P y := by
    intro x y
    by_contra hxy
    exact hcontra ⟨x, y, hxy⟩
  have hne : ∀ v ∈ B, step v ≠ 0 := fun v hv => stepIndep_ne_zero hindep hv
  have hk0 : step k ≠ 0 := hne k hkB
  set T : Finset α := B.erase k with hT
  -- every symbol along the progression vanishes
  have hsymb : ∀ m : ℕ, 1 ≤ m → symb step ((m : ℂ) * expStepRate (step k)) P = 0 := by
    intro m hm
    have hvan := blockSeed_symb_vanishing B step hne hkB P hcon hm
    have hprod : (∏ j ∈ B.erase k,
        (Complex.exp ((m : ℂ) * expStepRate (step k) * step j) - 1)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
      obtain ⟨hjk, hjB⟩ := Finset.mem_erase.mp hj
      intro hzero
      refine stepRatio_pow_ne_one hindep hkB hjB hjk hm ?_
      rw [stepRatio_pow]
      exact sub_eq_zero.mp hzero
    exact (mul_eq_zero.mp hvan).resolve_left hprod
  -- transport to the restricted, translated polynomial
  set Q : MvPolynomial α ℂ := restrictPoly T P with hQ
  set Qt : MvPolynomial α ℂ := bind₁ (fun j => X j - 1) Q with hQt
  have hXsub : ∀ i : α, ((X i : MvPolynomial α ℂ) - 1).vars ⊆ ({i} : Finset α) := by
    intro i
    have hrw : (X i : MvPolynomial α ℂ) - 1 = X i + C (-1 : ℂ) := by
      rw [map_neg, map_one]
      ring
    rw [hrw]
    refine (vars_add_subset _ _).trans ?_
    rw [vars_C, Finset.union_empty, vars_X]
  have hvarsQt : Qt.vars ⊆ T := by
    refine (vars_bind₁ _ _).trans ?_
    refine Finset.biUnion_subset.mpr fun i hi => ?_
    refine (hXsub i).trans ?_
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact vars_restrictPoly T P hi
  have hsuppQt : ∀ ν ∈ Qt.support, ν.support ⊆ T := by
    intro ν hν x hx
    exact hvarsQt (mem_vars_iff_mem_support x |>.mpr ⟨ν, hν, hx⟩)
  have heval : ∀ m : ℕ, 1 ≤ m →
      ∑ ν ∈ Qt.support, coeff ν Qt * (stepNode step k ν) ^ m = 0 := by
    intro m hm
    have h1 : eval (fun j => stepRatio step k j ^ m) Qt
        = ∑ ν ∈ Qt.support, coeff ν Qt * (stepNode step k ν) ^ m := by
      rw [MvPolynomial.eval_eq]
      refine Finset.sum_congr rfl fun ν _ => ?_
      congr 1
      rw [stepNode, ← Finset.prod_pow]
      exact Finset.prod_congr rfl fun i _ => by rw [pow_right_comm]
    have h2 : eval (fun j => stepRatio step k j ^ m) Qt
        = eval (fun j => stepRatio step k j ^ m - 1) Q := by
      rw [hQt, ← aeval_eq_eval', aeval_bind₁]
      refine congrArg (fun f => (aeval f) Q) ?_
      funext i
      rw [map_sub, aeval_X, map_one]
    have h3 : eval (fun j => stepRatio step k j ^ m - 1) Q
        = eval (fun j => stepRatio step k j ^ m - 1) P := by
      refine eval_restrictPoly P ?_
      intro j hj
      rw [stepRatio_eq_one hoff hk0 hj, one_pow, sub_self]
    have h4 : eval (fun j => stepRatio step k j ^ m - 1) P
        = symb step ((m : ℂ) * expStepRate (step k)) P := by
      rw [symb, aeval_eq_eval']
      refine congrArg (fun f => eval f P) ?_
      funext j
      rw [stepRatio_pow]
    rw [← h1, h2, h3, h4, hsymb m hm]
  -- the Vandermonde argument
  have hcoeff : ∀ ν ∈ Qt.support, coeff ν Qt = 0 := by
    refine exponentialSum_coeff_eq_zero (stepNode step k) Qt.support ?_ ?_ _ heval
    · intro ν hν ν' hν' hzz
      exact stepNode_injective_of_stepIndep hindep hkB (hsuppQt ν (Finset.mem_coe.mp hν))
        (hsuppQt ν' (Finset.mem_coe.mp hν')) hzz
    · intro ν _
      exact stepNode_ne_zero step k ν
  have hQt0 : Qt = 0 := by
    ext ν
    by_cases hν : ν ∈ Qt.support
    · rw [hcoeff ν hν, coeff_zero]
    · rw [MvPolynomial.notMem_support_iff.mp hν, coeff_zero]
  have hQ0 : Q = 0 := by
    have hback : bind₁ (fun j => (X j : MvPolynomial α ℂ) + 1) Qt = Q := by
      rw [hQt, bind₁_bind₁]
      have hid : (fun i => bind₁ (fun j => (X j : MvPolynomial α ℂ) + 1) (X i - 1))
          = fun i : α => (X i : MvPolynomial α ℂ) := by
        funext i
        simp
      rw [hid, bind₁_X_left]
      rfl
    rw [← hback, hQt0, map_zero]
  have hd₀T : d₀.support ⊆ T := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun hc => hkd₀ (hc ▸ hx), hd₀B hx⟩
  have : coeff d₀ P = 0 := by
    rw [← coeff_restrictPoly P hd₀T, ← hQ, hQ0, coeff_zero]
  exact (MvPolynomial.mem_support_iff.mp hd₀P) this

end

end GaloisForLFunctions.HTGeometry
