import GaloisForLFunctions.HTGeometry.RationalAffineTransport

/-!
# The unicritical family `α z^p + β` carries a Ritt cocycle only in the two integrable cases

A Ritt relation for a linearizer transports into a *homogeneous* affine transport equation for a
rational function `A`,

`A(g(z)) · g'(z)^k = b · A(z)`,   `b` a nonzero constant, `k ≠ 0`,

which is the statement that the map preserves a rational `k`-differential up to scale.  For the
unicritical polynomial `g = α X^p + β` the equation can be solved completely by counting zeros and
poles, with no dynamical or analytic input.

The map has the single critical point `0`, with critical value `β`, and every other fibre consists
of `p` distinct points.  Writing `n_z` for the order of `A` at `z`, the transport equation reads

`n_{g(z)} = n_z`  away from the critical point,  `p·n_β + k(p−1) = n_0`  at it.

So the finite set `S` where `n` does not vanish swallows the full `p`-element fibre over each of its
own points other than `β`, whence `p·|S \ {β}| ≤ |S| ≤ |S \ {β}| + 1`.  For `p ≥ 3` this forces
`S \ {β} = ∅`; the critical value is then not periodic, because `g(β) = β` would need `αβ^p = 0`, so
`S` is empty and the critical equation degenerates to `k(p−1) = 0`.  For `p = 2` one extra
configuration survives the count, `S = {y₀, β}` with `g(y₀) = y₀` and `g(β) = y₀`, and the two
evaluations force `y₀ = −β` and then `αβ = −2`: the Chebyshev parameter.

Hence for `β ≠ 0` — the map is not the power map — and outside the single Chebyshev parameter in
degree two, no nonzero rational function satisfies the equation.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

noncomputable section

/-- The unicritical polynomial `α X^p + β`. -/
def unicriticalPoly (p : ℕ) (α β : K) : K[X] := C α * X ^ p + C β

omit [CharZero K] in
@[simp] theorem unicriticalPoly_eval (p : ℕ) (α β z : K) :
    (unicriticalPoly p α β).eval z = α * z ^ p + β := by
  simp [unicriticalPoly]

omit [CharZero K] in
theorem natDegree_unicriticalPoly (p : ℕ) {α : K} (hα : α ≠ 0) (β : K) :
    (unicriticalPoly p α β).natDegree = p := by
  rw [unicriticalPoly, Polynomial.natDegree_add_C, Polynomial.natDegree_C_mul_X_pow p α hα]

omit [CharZero K] in
theorem unicriticalPoly_ne_zero {p : ℕ} (hp : 0 < p) {α : K} (hα : α ≠ 0) (β : K) :
    unicriticalPoly p α β ≠ 0 := by
  intro h
  have := natDegree_unicriticalPoly p hα β
  rw [h, natDegree_zero] at this
  omega

omit [CharZero K] in
/-- Subtracting a constant stays in the family. -/
theorem unicriticalPoly_sub_C (p : ℕ) (α β y : K) :
    unicriticalPoly p α β - C y = unicriticalPoly p α (β - y) := by
  rw [unicriticalPoly, unicriticalPoly, map_sub]
  ring

omit [CharZero K] in
theorem derivative_unicriticalPoly (p : ℕ) (α β : K) :
    derivative (unicriticalPoly p α β) = C (α * (p : K)) * X ^ (p - 1) := by
  rw [unicriticalPoly, derivative_add, derivative_C, add_zero, derivative_C_mul,
    derivative_X_pow, map_mul]
  ring

omit [CharZero K] in
@[simp] theorem derivative_unicriticalPoly_eval (p : ℕ) (α β z : K) :
    (derivative (unicriticalPoly p α β)).eval z = α * (p : K) * z ^ (p - 1) := by
  rw [derivative_unicriticalPoly]
  simp

/-! ## The two local multiplicities -/

omit [CharZero K] in
theorem rootMultiplicity_X_eq [DecidableEq K] (z : K) :
    rootMultiplicity z (X : K[X]) = if z = 0 then 1 else 0 := by
  by_cases h : z = 0
  · subst h
    rw [if_pos rfl, show (X : K[X]) = X - C 0 by simp, Polynomial.rootMultiplicity_X_sub_C_self]
  · rw [if_neg h]
    exact Polynomial.rootMultiplicity_eq_zero (by simp [Polynomial.IsRoot, h])

/-- The derivative vanishes to order `p − 1` at the critical point. -/
theorem rootMultiplicity_derivative_unicriticalPoly {p : ℕ} (hp : 0 < p) {α : K} (hα : α ≠ 0)
    (β : K) : rootMultiplicity (0 : K) (derivative (unicriticalPoly p α β)) = p - 1 := by
  classical
  have hcoeff : α * (p : K) ≠ 0 :=
    mul_ne_zero hα (Nat.cast_ne_zero.mpr (by omega))
  have hC : (C (α * (p : K)) : K[X]) ≠ 0 := by
    simpa using hcoeff
  have hX : (X : K[X]) ≠ 0 := Polynomial.X_ne_zero
  rw [derivative_unicriticalPoly,
    rootMultiplicity_mul (mul_ne_zero hC (pow_ne_zero _ hX)),
    Polynomial.rootMultiplicity_eq_zero (by simp [Polynomial.IsRoot, hcoeff]),
    rootMultiplicity_pow hX, rootMultiplicity_X_eq, if_pos rfl]
  omega

omit [CharZero K] in
/-- The critical point is totally ramified. -/
theorem rootMultiplicity_unicriticalPoly_critical {p : ℕ} (hp : 0 < p) {α : K} (hα : α ≠ 0)
    (β : K) :
    rootMultiplicity (0 : K)
        (unicriticalPoly p α β - C ((unicriticalPoly p α β).eval 0)) = p := by
  classical
  have hX : (X : K[X]) ≠ 0 := Polynomial.X_ne_zero
  have hC : (C α : K[X]) ≠ 0 := by simpa using hα
  have hval : (unicriticalPoly p α β).eval 0 = β := by
    simp [zero_pow (by omega : p ≠ 0)]
  have hEq : unicriticalPoly p α β - C ((unicriticalPoly p α β).eval 0) = C α * X ^ p := by
    rw [hval, unicriticalPoly]
    ring
  rw [hEq, rootMultiplicity_mul (mul_ne_zero hC (pow_ne_zero _ hX)),
    Polynomial.rootMultiplicity_eq_zero (by simp [Polynomial.IsRoot, hα]),
    rootMultiplicity_pow hX, rootMultiplicity_X_eq, if_pos rfl]
  omega

/-! ## The regular fibres -/

/-- The fibre of the unicritical map over a point. -/
def unicriticalFiber [DecidableEq K] (p : ℕ) (α β y : K) : Finset K :=
  (unicriticalPoly p α β - C y).roots.toFinset

omit [CharZero K] in
theorem mem_unicriticalFiber [DecidableEq K] {p : ℕ} (hp : 0 < p) {α : K} (hα : α ≠ 0)
    (β y z : K) : z ∈ unicriticalFiber p α β y ↔ (unicriticalPoly p α β).eval z = y := by
  rw [unicriticalFiber, Multiset.mem_toFinset,
    Polynomial.mem_roots (by rw [unicriticalPoly_sub_C]; exact unicriticalPoly_ne_zero hp hα _)]
  simp [Polynomial.IsRoot, sub_eq_zero]

/-- Every fibre over a point other than the critical value has exactly `p` points. -/
theorem card_unicriticalFiber [DecidableEq K] [IsAlgClosed K] {p : ℕ} (hp : 0 < p) {α : K}
    (hα : α ≠ 0) {β y : K} (hy : y ≠ β) :
    (unicriticalFiber p α β y).card = p := by
  have hc : (y - β) / α ≠ 0 := div_ne_zero (sub_ne_zero.mpr hy) hα
  have hEq : unicriticalPoly p α β - C y = C α * (X ^ p - C ((y - β) / α)) := by
    have hcancel : α * ((y - β) / α) = y - β := by field_simp
    rw [unicriticalPoly, mul_sub, ← map_mul, hcancel, map_sub]
    ring
  have hsep : (X ^ p - C ((y - β) / α) : K[X]).Separable :=
    Polynomial.separable_X_pow_sub_C _ (Nat.cast_ne_zero.mpr (by omega)) hc
  have hroots : (unicriticalPoly p α β - C y).roots = (X ^ p - C ((y - β) / α) : K[X]).roots := by
    rw [hEq, Polynomial.roots_C_mul _ hα]
  rw [unicriticalFiber, hroots,
    Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
    Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _),
    Polynomial.natDegree_X_pow_sub_C]

/-! ## No homogeneous transport -/

/-- **The unicritical no-cocycle theorem.**  For `β ≠ 0` and outside the single Chebyshev parameter
in degree two, the map `α z^p + β` preserves no rational `k`-differential up to scale. -/
theorem no_ritt_cocycle_unicritical [IsAlgClosed K] {p : ℕ} (hp : 2 ≤ p)
    {α β : K} (hα : α ≠ 0) (hβ : β ≠ 0) (hcheb : ¬ (p = 2 ∧ α * β = -2))
    {hg : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) (unicriticalPoly p α β)) = RatFunc.C c}
    {k : ℤ} (hk : k ≠ 0) {b : K} (hb : b ≠ 0) {A : RatFunc K} (hA : A ≠ 0)
    (heq : IsAffineTransport (unicriticalPoly p α β) hg k (RatFunc.C b) 0 A) : False := by
  classical
  have hp0 : 0 < p := by omega
  have hdeg : (unicriticalPoly p α β).natDegree ≠ 0 := by
    rw [natDegree_unicriticalPoly p hα]; omega
  have hbC : (RatFunc.C b : RatFunc K) ≠ 0 := by
    simpa using hb
  -- the order of the right-hand side
  have hrhs : ∀ z : K, ratOrder (RatFunc.C b * A + 0) z = ratOrder A z := by
    intro z
    rw [add_zero, ratOrder_mul hbC hA, ratOrder_C, zero_add]
  -- away from the critical point the order is constant along the map
  have hstep : ∀ z : K, z ≠ 0 →
      ratOrder A ((unicriticalPoly p α β).eval z) = ratOrder A z := by
    intro z hz
    have hderiv : (derivative (unicriticalPoly p α β)).eval z ≠ 0 := by
      rw [derivative_unicriticalPoly_eval]
      exact mul_ne_zero (mul_ne_zero hα (Nat.cast_ne_zero.mpr (by omega)))
        (pow_ne_zero _ hz)
    have hlhs := ratOrder_affineTransport_lhs_of_deriv_ne_zero hdeg hg hA k hderiv
    rw [isAffineTransport_def heq, hrhs z] at hlhs
    exact hlhs.symm
  -- the equation at the critical point
  have hval0 : (unicriticalPoly p α β).eval 0 = β := by
    simp [zero_pow (by omega : p ≠ 0)]
  have hcrit : ratOrder A β * (p : ℤ) + k * ((p : ℤ) - 1) = ratOrder A 0 := by
    have hlhs := ratOrder_affineTransport_lhs hdeg hg hA k (0 : K)
    rw [isAffineTransport_def heq, hrhs 0,
      rootMultiplicity_derivative_unicriticalPoly hp0 hα,
      rootMultiplicity_unicriticalPoly_critical hp0 hα, hval0] at hlhs
    have hcast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
    rw [hlhs, hcast]
  -- the support of the order
  set S : Finset K := (finite_support_ratOrder hA).toFinset with hS
  have hmemS : ∀ z : K, z ∈ S ↔ ratOrder A z ≠ 0 := by
    intro z
    rw [hS, Set.Finite.mem_toFinset]
    rfl
  set T : Finset K := S.erase β with hT
  have hmemT : ∀ z : K, z ∈ T ↔ (z ≠ β ∧ ratOrder A z ≠ 0) := by
    intro z
    rw [hT, Finset.mem_erase, hmemS]
  -- each regular fibre over the support lies in the support
  have hfibsub : ∀ y ∈ T, unicriticalFiber p α β y ⊆ S := by
    intro y hy z hz
    rw [mem_unicriticalFiber hp0 hα] at hz
    obtain ⟨hyβ, hyord⟩ := (hmemT y).mp hy
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, hval0] at hz
      exact hyβ hz.symm
    rw [hmemS]
    rw [← hstep z hz0, hz]
    exact hyord
  have hdisj : (↑T : Set K).PairwiseDisjoint (unicriticalFiber p α β) := by
    intro y hy y' hy' hne
    refine Finset.disjoint_left.mpr ?_
    intro z hz hz'
    rw [mem_unicriticalFiber hp0 hα] at hz hz'
    exact hne (hz.symm.trans hz')
  have hcount : p * T.card ≤ S.card := by
    have hsub : T.biUnion (unicriticalFiber p α β) ⊆ S := by
      intro z hz
      obtain ⟨y, hy, hzy⟩ := Finset.mem_biUnion.mp hz
      exact hfibsub y hy hzy
    have hcard : (T.biUnion (unicriticalFiber p α β)).card = p * T.card := by
      rw [Finset.card_biUnion hdisj]
      rw [Finset.sum_congr rfl (fun y hy => card_unicriticalFiber hp0 hα ((hmemT y).mp hy).1)]
      rw [Finset.sum_const, smul_eq_mul]
      ring
    rw [← hcard]
    exact Finset.card_le_card hsub
  have hSle : S.card ≤ T.card + 1 := by
    rw [hT]
    by_cases hmem : β ∈ S
    · rw [Finset.card_erase_of_mem hmem]
      have : 1 ≤ S.card := Finset.card_pos.mpr ⟨β, hmem⟩
      omega
    · rw [Finset.erase_eq_of_notMem hmem]
      omega
  rcases Nat.eq_zero_or_pos T.card with hT0 | hT1
  · -- the support is empty: the critical equation degenerates
    have hβord : ratOrder A β = 0 := by
      by_contra hne
      have himg : (unicriticalPoly p α β).eval β ≠ β := by
        rw [unicriticalPoly_eval]
        intro h
        exact hβ (pow_eq_zero_iff (by omega : p ≠ 0) |>.mp
          (by
            have : α * β ^ p = 0 := by linear_combination h
            exact (mul_eq_zero.mp this).resolve_left hα))
      have hmem : (unicriticalPoly p α β).eval β ∈ T := by
        rw [hmemT]
        refine ⟨himg, ?_⟩
        rw [hstep β hβ]
        exact hne
      have : 0 < T.card := Finset.card_pos.mpr ⟨_, hmem⟩
      omega
    have hβnot : β ∉ S := by
      rw [hmemS]
      simpa using hβord
    have hTS : T = S := by rw [hT, Finset.erase_eq_of_notMem hβnot]
    have hScard : S.card = 0 := by rw [← hTS]; exact hT0
    have hSempty : S = ∅ := Finset.card_eq_zero.mp hScard
    have h0ord : ratOrder A 0 = 0 := by
      by_contra hne
      have : (0 : K) ∈ S := (hmemS 0).mpr hne
      rw [hSempty] at this
      exact absurd this (Finset.notMem_empty 0)
    rw [hβord, h0ord] at hcrit
    have hpk : k * ((p : ℤ) - 1) = 0 := by linear_combination hcrit
    have hp1 : ((p : ℤ) - 1) ≠ 0 := by
      have : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
      omega
    exact hk ((mul_eq_zero.mp hpk).resolve_right hp1)
  · -- the count leaves only the Chebyshev configuration in degree two
    have hmul : p * T.card ≤ T.card + 1 := le_trans hcount hSle
    have h2t : 2 * T.card ≤ p * T.card := Nat.mul_le_mul hp (le_refl T.card)
    have hTcard : T.card = 1 := by
      have hchain : 2 * T.card ≤ T.card + 1 := le_trans h2t hmul
      omega
    have hpeq : p = 2 := by
      rw [hTcard, mul_one] at hmul
      omega
    obtain ⟨y₀, hy₀⟩ := Finset.card_eq_one.mp hTcard
    have hScard : S.card = 2 := by
      rw [hpeq, hTcard, mul_one] at hcount
      rw [hTcard] at hSle
      omega
    have hβmem : β ∈ S := by
      by_contra hmem
      rw [hT, Finset.erase_eq_of_notMem hmem] at hTcard
      omega
    have hfibS : unicriticalFiber p α β y₀ = S := by
      refine Finset.eq_of_subset_of_card_le (hfibsub y₀ (by rw [hy₀]; exact Finset.mem_singleton_self y₀)) ?_
      rw [card_unicriticalFiber hp0 hα ((hmemT y₀).mp (by rw [hy₀]; exact Finset.mem_singleton_self y₀)).1,
        hScard, hpeq]
    have hy₀S : y₀ ∈ S := Finset.mem_of_mem_erase (by rw [← hT, hy₀]; exact Finset.mem_singleton_self y₀)
    have hy₀ne : y₀ ≠ β := ((hmemT y₀).mp (by rw [hy₀]; exact Finset.mem_singleton_self y₀)).1
    have hfix : α * y₀ ^ p + β = y₀ := by
      have := (mem_unicriticalFiber hp0 hα β y₀ y₀).mp (by rw [hfibS]; exact hy₀S)
      simpa using this
    have hcrit2 : α * β ^ p + β = y₀ := by
      have := (mem_unicriticalFiber hp0 hα β y₀ β).mp (by rw [hfibS]; exact hβmem)
      simpa using this
    rw [hpeq] at hfix hcrit2
    have hsq : α * (y₀ ^ 2 - β ^ 2) = 0 := by linear_combination hfix - hcrit2
    have hdiff : (y₀ - β) * (y₀ + β) = 0 := by
      have := (mul_eq_zero.mp hsq).resolve_left hα
      linear_combination this
    have hy₀val : y₀ = -β := by
      rcases mul_eq_zero.mp hdiff with h | h
      · exact absurd (by linear_combination h : y₀ = β) hy₀ne
      · linear_combination h
    rw [hy₀val] at hcrit2
    have : β * (α * β + 2) = 0 := by linear_combination hcrit2
    exact hcheb ⟨hpeq, by
      have := (mul_eq_zero.mp this).resolve_left hβ
      linear_combination this⟩

end

end GaloisForLFunctions.HTGeometry
