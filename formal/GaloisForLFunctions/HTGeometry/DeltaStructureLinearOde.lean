import GaloisForLFunctions.HTGeometry.DifferenceDifferential

/-!
# A compatible derivation makes every solution differentially algebraic

If a rank-two shift recurrence `σ²y = y + b σy` carries a compatible derivation, that is a pair
`p, q` of coefficients with `δ y = p y + q σy`, then the coefficient span `⟨y, σy⟩` is stable under
the derivation, because `δ (σ y) = σ (δ y)` re-expands through the recurrence.  Three elements of a
two-dimensional span are dependent, so `y` satisfies a nonzero linear differential equation of
order at most two.

This is the converse of the isomonodromy obstruction: a rational compatible derivation would force
every solution to be differentially algebraic, so the obstruction is exactly the right one to
exclude.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem deriv_add' {L : Type*} [CommRing L] [Differential L] (x y : L) :
    Differential.deriv (x + y) = Differential.deriv x + Differential.deriv y :=
  map_add _ _ _

theorem deriv_mul' {L : Type*} [CommRing L] [Differential L] (x y : L) :
    Differential.deriv (x * y) = x * Differential.deriv y + y * Differential.deriv x := by
  simp [(Differential.deriv : Derivation ℤ L L).leibniz x y]

/-- **A compatible derivation forces a linear differential equation.**  A solution of a rank-two
shift recurrence carrying a compatible derivation satisfies a nonzero linear differential equation
of order at most two, with coefficients in any subring containing the data and closed under the
shift and the derivation. -/
theorem exists_nontrivial_linear_ode_of_deltaStructure
    {L : Type*} [Field L] [Differential L] (σ : L ≃+* L)
    (hcomm : ∀ x : L, σ (Differential.deriv x) = Differential.deriv (σ x))
    (K : Subring L) (hσ : ∀ x ∈ K, σ x ∈ K)
    (hd : ∀ x ∈ K, Differential.deriv x ∈ K)
    {b p q y : L} (hb : b ∈ K) (hp : p ∈ K) (hq : q ∈ K)
    (hrec : σ (σ y) = y + b * σ y)
    (hδ : Differential.deriv y = p * y + q * σ y) :
    ∃ a₀ a₁ a₂ : L, a₀ ∈ K ∧ a₁ ∈ K ∧ a₂ ∈ K ∧ ¬(a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) ∧
      a₀ * y + a₁ * Differential.deriv y
        + a₂ * Differential.deriv (Differential.deriv y) = 0 := by
  classical
  set r : L := σ q with hrdef
  set s : L := σ p + b * σ q with hsdef
  have hrK : r ∈ K := hσ q hq
  have hsK : s ∈ K := K.add_mem (hσ p hp) (K.mul_mem hb (hσ q hq))
  have hshift : Differential.deriv (σ y) = r * y + s * σ y := by
    have h1 : Differential.deriv (σ y) = σ (Differential.deriv y) := (hcomm y).symm
    rw [h1, hδ, map_add, map_mul, map_mul, hrec, hrdef, hsdef]
    ring
  set R : L := Differential.deriv p + p * p + q * r with hRdef
  set S : L := p * q + Differential.deriv q + q * s with hSdef
  have hRK : R ∈ K :=
    K.add_mem (K.add_mem (hd p hp) (K.mul_mem hp hp)) (K.mul_mem hq hrK)
  have hSK : S ∈ K :=
    K.add_mem (K.add_mem (K.mul_mem hp hq) (hd q hq)) (K.mul_mem hq hsK)
  have hsecond : Differential.deriv (Differential.deriv y) = R * y + S * σ y := by
    rw [hδ, deriv_add', deriv_mul', deriv_mul', hδ, hshift, hRdef, hSdef]
    ring
  by_cases hcase : q = 0 ∧ S = 0
  · refine ⟨p, -1, 0, hp, K.neg_mem K.one_mem, K.zero_mem, ?_, ?_⟩
    · rintro ⟨-, h1, -⟩
      exact one_ne_zero (neg_eq_zero.mp h1)
    · rw [hδ, hcase.1]
      ring
  · refine ⟨q * R - S * p, S, -q, K.sub_mem (K.mul_mem hq hRK) (K.mul_mem hSK hp), hSK,
      K.neg_mem hq, ?_, ?_⟩
    · rintro ⟨-, h1, h2⟩
      exact hcase ⟨neg_eq_zero.mp h2, h1⟩
    · rw [hsecond, hδ]
      ring

end

end GaloisForLFunctions.HTGeometry
