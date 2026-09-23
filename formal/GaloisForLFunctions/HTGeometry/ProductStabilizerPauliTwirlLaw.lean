import GaloisForLFunctions.HTGeometry.ConservedLocalTwoQuerySignalLaw

/-!
# Exact product-stabilizer Pauli twirl

This module proves the finite probability identity behind the physical
two-query locality test.  At each qubit, a product-stabilizer state chooses
one of the three Pauli axes and one of its two eigenvalue signs uniformly.
The resulting local second moment is diagonal in the Pauli label, with value
`1 / 3` on every nonidentity axis.  Independence across qubits gives the
exact weight `3^{-w}` for a Pauli string of weight `w`.

Combining this twirl with `twoQueryProductStabilizerSignal_ge` turns the
conserved-coordinate bound into the signal of the actual randomized
product-state, two-copy protocol.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Expectation of one single-qubit Pauli label in a stabilizer eigenstate.
The sample records its uniformly selected axis and eigenvalue sign. -/
def stabilizerAxisExpectation
    (u : Fin 3 × Bool) : Option (Fin 3) → ℝ
  | none => 1
  | some p =>
      if u.1 = p then
        if u.2 then 1 else -1
      else 0

/-- Uniform single-qubit second moment over the six stabilizer states. -/
def localProductStabilizerTwirl
    (p q : Option (Fin 3)) : ℝ :=
  (∑ u : Fin 3 × Bool,
      stabilizerAxisExpectation u p *
        stabilizerAxisExpectation u q) / 6

/-- Exact single-qubit product-stabilizer twirl.  Distinct Pauli labels are
orthogonal; a matching nonidentity label survives with weight `1 / 3`. -/
theorem localProductStabilizerTwirl_eq
    (p q : Option (Fin 3)) :
    localProductStabilizerTwirl p q =
      if p = q then
        if p = none then 1 else (1 : ℝ) / 3
      else 0 := by
  fin_cases p <;> fin_cases q <;>
    norm_num [localProductStabilizerTwirl,
      stabilizerAxisExpectation, Fintype.sum_prod_type,
      Fintype.sum_bool, Fin.sum_univ_succ] <;>
    simp_all

/-- Number of nonidentity sites in a Pauli string. -/
def finitePauliWeight {σ : Type*} [Fintype σ]
    (P : σ → Option (Fin 3)) : ℕ :=
  (Finset.univ.filter fun s => P s ≠ none).card

/-- Product second moment of two Pauli strings under independent stabilizer
choices at every site. -/
def productStabilizerPauliTwirl
    {σ : Type*} [Fintype σ]
    (P Q : σ → Option (Fin 3)) : ℝ :=
  ∏ s, localProductStabilizerTwirl (P s) (Q s)

/-- A Pauli string of weight `w` has exact product-stabilizer second moment
`3^{-w}`. -/
theorem productStabilizerPauliTwirl_self
    {σ : Type*} [Fintype σ]
    (P : σ → Option (Fin 3)) :
    productStabilizerPauliTwirl P P =
      ((1 : ℝ) / 3) ^ finitePauliWeight P := by
  classical
  rw [productStabilizerPauliTwirl]
  calc
    (∏ s, localProductStabilizerTwirl (P s) (P s)) =
        ∏ s, if P s = none then 1 else (1 : ℝ) / 3 := by
      apply Finset.prod_congr rfl
      intro s _hs
      rw [localProductStabilizerTwirl_eq]
      simp
    _ = ∏ s, if P s ≠ none then (1 : ℝ) / 3 else 1 := by
      apply Finset.prod_congr rfl
      intro s _hs
      by_cases hs : P s = none <;> simp [hs]
    _ = ((1 : ℝ) / 3) ^ finitePauliWeight P := by
      rw [← Finset.prod_filter]
      simp [finitePauliWeight]

/-- Distinct Pauli strings are exactly orthogonal under the product-stabilizer
second moment. -/
theorem productStabilizerPauliTwirl_eq_zero_of_ne
    {σ : Type*} [Fintype σ]
    (P Q : σ → Option (Fin 3)) (hPQ : P ≠ Q) :
    productStabilizerPauliTwirl P Q = 0 := by
  classical
  obtain ⟨s, hs⟩ : ∃ s, P s ≠ Q s := by
    simpa only [Function.ne_iff] using hPQ
  apply Finset.prod_eq_zero (Finset.mem_univ s)
  rw [localProductStabilizerTwirl_eq]
  simp [hs]

/-- Expanding the squared output expectation and applying the exact Pauli
twirl deletes every off-diagonal coefficient pair. -/
theorem productStabilizer_coefficient_twirl
    {σ ι : Type*} [Fintype σ] [Fintype ι]
    (label : ι → σ → Option (Fin 3))
    (hinj : Function.Injective label)
    (C : Matrix ι ι ℝ) :
    (∑ i, ∑ j, ∑ k,
      C j i * C k i *
        productStabilizerPauliTwirl (label j) (label k)) =
      ∑ i, ∑ j,
        ((1 : ℝ) / 3) ^ finitePauliWeight (label j) *
          (C j i) ^ (2 : ℕ) := by
  classical
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Finset.sum_eq_single j]
  · rw [productStabilizerPauliTwirl_self]
    ring
  · intro k _hk hkj
    rw [productStabilizerPauliTwirl_eq_zero_of_ne
      (label j) (label k) (fun h => hkj (hinj h).symm)]
    ring
  · simp

/-- Signal produced by the randomized product-stabilizer, two-copy Pauli
protocol after expanding each evolved input Pauli in the output dictionary. -/
def productStabilizerTwoQueryProtocolSignal
    {σ ι : Type*} [Fintype σ] [Fintype ι]
    (label : ι → σ → Option (Fin 3))
    (C : Matrix ι ι ℝ) : ℝ :=
  (∑ i, ∑ j, ∑ k,
      C j i * C k i *
        productStabilizerPauliTwirl (label j) (label k)) /
    (Fintype.card ι : ℝ)

/-- The operational protocol signal is exactly the dimension-linear weighted
coefficient signal used by `twoQueryProductStabilizerSignal_ge`. -/
theorem productStabilizerTwoQueryProtocolSignal_eq
    {σ ι : Type*} [Fintype σ] [Fintype ι]
    (label : ι → σ → Option (Fin 3))
    (hinj : Function.Injective label)
    (C : Matrix ι ι ℝ) :
    productStabilizerTwoQueryProtocolSignal label C =
      twoQueryProductStabilizerSignal
        (fun j => finitePauliWeight (label j)) C := by
  rw [productStabilizerTwoQueryProtocolSignal,
    twoQueryProductStabilizerSignal,
    productStabilizer_coefficient_twirl label hinj C]

/-- **Operational conserved-local signal.** If every dictionary Pauli has
weight at most `q`, any nonzero conserved local coefficient produces
two-query product-stabilizer signal at least `3^{-q}/M`, at every time. -/
theorem productStabilizerTwoQueryProtocolSignal_ge
    {σ ι : Type*} [Fintype σ] [Fintype ι] [Nonempty ι]
    (q : ℕ) (label : ι → σ → Option (Fin 3))
    (hinj : Function.Injective label)
    (hweight : ∀ j, finitePauliWeight (label j) ≤ q)
    (C : Matrix ι ι ℝ) (h : ι → ℝ) (hh : h ≠ 0)
    (hfix : C *ᵥ h = h) :
    ((1 : ℝ) / 3) ^ q / (Fintype.card ι : ℝ) ≤
      productStabilizerTwoQueryProtocolSignal label C := by
  rw [productStabilizerTwoQueryProtocolSignal_eq label hinj C]
  exact twoQueryProductStabilizerSignal_ge
    q (fun j => finitePauliWeight (label j))
      hweight C h hh hfix

end

end GaloisForLFunctions.HTGeometry
