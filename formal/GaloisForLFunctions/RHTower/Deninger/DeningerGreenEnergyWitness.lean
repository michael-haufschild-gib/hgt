import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticPositiveCalderonKoszul

/-!
# The global Green-energy interface is satisfiable: an explicit non-vacuous witness

The global layer of the arithmetic Calderón–Green chain rests on one clause, supplied to
`deningerTsumEnergy_eq_zero_iff_mem_boundaries` as the hypothesis

`hlocal_zero_is_boundary : ∀ x, (∀ i, localEnergy i x = 0) → x ∈ boundaries`,

and on its strict form `hdetects : ∀ x, energy x = 0 → x = 0` used by
`deningerStrictPositive_of_greenEnergy_detects_zero`.  Both are anonymous hypotheses rather than
named `Prop` interfaces or bundled data, so neither of the corpus's discharge instruments records
them, and nothing in the tree had exhibited a family satisfying them.

An interface nobody can satisfy proves nothing.  This file removes that possibility by exhibiting
the Dirichlet energy of a conductance family and discharging **every** hypothesis of the global
theorem simultaneously, with a boundary submodule that is a proper subspace — so the conclusion is
not vacuous either.

The general statement is the classical one: a nonnegative Dirichlet energy vanishes exactly on the
functions that are constant along every edge of positive conductance, and hence — when the
conductance graph is connected — exactly on the constants.  That is the shape the arithmetic Green
energy is supposed to have, with "constants" replaced by the boundary submodule.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The Dirichlet energy of a conductance family -/

variable {V : Type*}

/-- Edgewise Dirichlet energy of `u` for the conductance `c`. -/
def conductanceEnergy (c : V → V → ℝ) (u : V → ℝ) (e : V × V) : ℝ :=
  c e.1 e.2 * (u e.1 - u e.2) ^ (2 : ℕ)

theorem conductanceEnergy_nonneg {c : V → V → ℝ} (hc : ∀ a b, 0 ≤ c a b) (u : V → ℝ) (e : V × V) :
    0 ≤ conductanceEnergy c u e :=
  mul_nonneg (hc e.1 e.2) (sq_nonneg _)

/-- **Radical of the Dirichlet energy.**  All edge energies vanish exactly when `u` is constant
along every edge of positive conductance. -/
theorem conductanceEnergy_eq_zero_iff {c : V → V → ℝ} (hc : ∀ a b, 0 ≤ c a b) (u : V → ℝ) :
    (∀ e : V × V, conductanceEnergy c u e = 0) ↔ ∀ a b : V, 0 < c a b → u a = u b := by
  constructor
  · intro h a b hab
    have he := h (a, b)
    rw [conductanceEnergy] at he
    have : (u a - u b) ^ (2 : ℕ) = 0 := by
      rcases mul_eq_zero.mp he with h1 | h2
      · exact absurd h1 hab.ne'
      · exact h2
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  · intro h e
    rw [conductanceEnergy]
    rcases lt_or_eq_of_le (hc e.1 e.2) with hpos | hzero
    · rw [h e.1 e.2 hpos]
      ring
    · rw [← hzero]
      ring

/-- Along a chain of positive-conductance edges the value is constant. -/
theorem eq_of_reflTransGen_of_edge_const {c : V → V → ℝ} {u : V → ℝ}
    (h : ∀ a b : V, 0 < c a b → u a = u b) {x y : V}
    (hxy : Relation.ReflTransGen (fun a b : V => 0 < c a b) x y) : u x = u y := by
  induction hxy with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (h _ _ hstep)

/-- **Connected radical law.**  On a connected conductance graph the Dirichlet energy vanishes
exactly on the constants. -/
theorem conductanceEnergy_eq_zero_iff_const {c : V → V → ℝ} (hc : ∀ a b, 0 ≤ c a b)
    (hconn : ∀ x y : V, Relation.ReflTransGen (fun a b : V => 0 < c a b) x y) (u : V → ℝ) :
    (∀ e : V × V, conductanceEnergy c u e = 0) ↔ ∀ x y : V, u x = u y := by
  rw [conductanceEnergy_eq_zero_iff hc]
  constructor
  · intro h x y
    exact eq_of_reflTransGen_of_edge_const h (hconn x y)
  · intro h a b _
    exact h a b

/-! ## A non-vacuous witness for the global Green-energy interface

Take the complete graph on `Fin n` with unit conductances inside the Euclidean model, and the
boundary submodule spanned by the all-ones vector.  Every hypothesis of
`deningerTsumEnergy_eq_zero_iff_mem_boundaries` holds. -/

section Witness

variable (n : ℕ)

/-- The all-ones vector of the Euclidean model. -/
def onesVector : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ => (1 : ℝ))

@[simp] theorem onesVector_apply (i : Fin n) : onesVector n i = 1 := by
  simp [onesVector]

/-- The boundary submodule of the witness: the constants. -/
def witnessBoundaries : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ {onesVector n}

/-- Unit-conductance edge energy on the Euclidean model. -/
def witnessLocalEnergy (e : Fin n × Fin n) (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (u e.1 - u e.2) ^ (2 : ℕ)

theorem witnessLocalEnergy_nonneg (e : Fin n × Fin n) (u : EuclideanSpace ℝ (Fin n)) :
    0 ≤ witnessLocalEnergy n e u :=
  sq_nonneg _

theorem witnessLocalEnergy_summable (u : EuclideanSpace ℝ (Fin n)) :
    Summable fun e : Fin n × Fin n => witnessLocalEnergy n e u :=
  Summable.of_finite

theorem mem_witnessBoundaries_iff (u : EuclideanSpace ℝ (Fin n)) :
    u ∈ witnessBoundaries n ↔ ∀ i j : Fin n, u i = u j := by
  rw [witnessBoundaries, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩ i j
    simp
  · intro h
    rcases Nat.eq_zero_or_pos n with hn | hn
    · refine ⟨0, ?_⟩
      ext i
      subst hn
      exact absurd i.isLt (by omega)
    · refine ⟨u ⟨0, hn⟩, ?_⟩
      ext i
      simpa using h ⟨0, hn⟩ i

theorem witnessLocalEnergy_zero_of_mem (u : EuclideanSpace ℝ (Fin n))
    (hu : u ∈ witnessBoundaries n) : ∀ e : Fin n × Fin n, witnessLocalEnergy n e u = 0 := by
  intro e
  rw [witnessLocalEnergy, (mem_witnessBoundaries_iff n u).mp hu e.1 e.2]
  ring

theorem mem_witnessBoundaries_of_witnessLocalEnergy_zero (u : EuclideanSpace ℝ (Fin n))
    (hu : ∀ e : Fin n × Fin n, witnessLocalEnergy n e u = 0) : u ∈ witnessBoundaries n := by
  rw [mem_witnessBoundaries_iff]
  intro i j
  have he := hu (i, j)
  rw [witnessLocalEnergy] at he
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp he
  linarith

/-- **The global Green-energy interface is satisfiable.**  Every hypothesis of
`deningerTsumEnergy_eq_zero_iff_mem_boundaries` is discharged by the unit-conductance Dirichlet
energy on the complete graph, so the theorem's conclusion holds for that family with no hypothesis
left standing. -/
theorem witnessTsumEnergy_eq_zero_iff_mem_boundaries (u : EuclideanSpace ℝ (Fin n)) :
    (∑' e : Fin n × Fin n, witnessLocalEnergy n e u) = 0 ↔ u ∈ witnessBoundaries n :=
  deningerTsumEnergy_eq_zero_iff_mem_boundaries
    (witnessBoundaries n) (witnessLocalEnergy n)
    (fun x => witnessLocalEnergy_summable n x)
    (fun e x => witnessLocalEnergy_nonneg n e x)
    (fun x hx => witnessLocalEnergy_zero_of_mem n x hx)
    (fun x hx => mem_witnessBoundaries_of_witnessLocalEnergy_zero n x hx)
    u

/-- The witness is not vacuous in the other direction either: for `n ≥ 2` the boundary submodule is
a **proper** subspace, so the radical law is a genuine restriction and not the whole space. -/
theorem witnessBoundaries_ne_top (hn : 2 ≤ n) : witnessBoundaries n ≠ ⊤ := by
  intro htop
  have h0 : (0 : ℕ) < n := by omega
  have h1 : (1 : ℕ) < n := by omega
  set i0 : Fin n := ⟨0, h0⟩ with hi0
  set i1 : Fin n := ⟨1, h1⟩ with hi1
  set v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => if i = i0 then (1 : ℝ) else 0) with hvdef
  have hmem : v ∈ witnessBoundaries n := htop ▸ Submodule.mem_top
  have hval := (mem_witnessBoundaries_iff n v).mp hmem i0 i1
  have hne : i1 ≠ i0 := by
    simp [hi0, hi1, Fin.ext_iff]
  rw [hvdef] at hval
  simp [hne] at hval

end Witness

end

end RHTower
