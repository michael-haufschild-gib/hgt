import GaloisForLFunctions.HTGeometry.BigradedCorankLattice

/-!
# The corank seam invariant

`corank-seam-invariant.md` studies the multiplicative relation lattice `Λ_M ⊂ ℤ^{(P)}` of an
infinite-base multi-`q` module, its corank `rank(ℤ^{(P)}/Λ_M)`, and the graded refinement

```text
corank^{(T)} = dim_ℚ span_ℚ { ∏_p (log p)^{a_p} : Σ_p a_p ≤ T }.
```

This file proves the card's Lean targets.

* `primeLog_ker_eq_bot` and `aleph0_le_rank_quotient_primeLog` — over `ℚ` unique factorization kills
  every relation, so the quotient is the whole free module and the corank is infinite;
* `rank_quotient_ker_eq_one` — the function-field border: a single multiplier (a surjective degree
  map) leaves quotient rank one;
* `algebraicIndependent_iff_forall_degreeBox` — the graded ladder: algebraic independence is
  exactly linear independence of the monomials of every bounded degree;
* `aleph0_le_gradedCorank_primeLog` — the proven floor `corank^{(1)} = ∞`;
* `linearIndependent_of_algebraicIndependent` and
  `exists_linearIndependent_not_algebraicIndependent` — the level-separation theorem: linear
  independence is implied by, but strictly weaker than, algebraic independence.

The apex (`corank^{(T)} = ∞` for all `T`, i.e. Schanuel-for-prime-logs) is not claimed.
-/

noncomputable section

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry.CorankSeam

open GaloisForLFunctions.HTGeometry.BigradedCorank

universe uF uE uI

variable {F : Type uF} {E : Type uE} {ι : Type uI}
variable [Field F] [CommRing E] [Algebra F E]

/-! ## The graded corank -/

/-- The degree box of exponent vectors of total degree at most `T`. -/
def degreeBox (ι : Type*) (T : ℕ) : Set (ι →₀ ℕ) := {a | expDegree a ≤ T}

/-- The graded span of all monomials of degree at most `T`. -/
def gradedSpan (F : Type*) [Field F] {E ι : Type*} [CommRing E] [Algebra F E]
    (u : ι → E) (T : ℕ) : Submodule F E :=
  Submodule.span F (monomialValue u '' degreeBox ι T)

/-- The graded corank `corank^{(T)}`. -/
def gradedCorank (F : Type*) [Field F] {E ι : Type*} [CommRing E] [Algebra F E]
    (u : ι → E) (T : ℕ) : Cardinal :=
  Module.rank F (gradedSpan F u T)

theorem mem_degreeBox {a : ι →₀ ℕ} {T : ℕ} : a ∈ degreeBox ι T ↔ expDegree a ≤ T := Iff.rfl

theorem iUnion_degreeBox : (⋃ T : ℕ, degreeBox ι T) = Set.univ :=
  Set.eq_univ_of_forall (fun a => Set.mem_iUnion.mpr ⟨expDegree a, mem_degreeBox.mpr le_rfl⟩)

theorem directed_degreeBox : Directed (· ⊆ ·) (fun T : ℕ => degreeBox ι T) := by
  intro T U
  refine ⟨max T U, fun x hx => ?_, fun x hx => ?_⟩
  · exact mem_degreeBox.mpr (le_trans (mem_degreeBox.mp hx) (le_max_left _ _))
  · exact mem_degreeBox.mpr (le_trans (mem_degreeBox.mp hx) (le_max_right _ _))

/-- **The graded ladder.**  A family is algebraically independent exactly when the monomials of
every bounded degree are linearly independent. -/
theorem algebraicIndependent_iff_forall_degreeBox (u : ι → E) :
    AlgebraicIndependent F u ↔ ∀ T : ℕ, LinearIndepOn F (monomialValue u) (degreeBox ι T) := by
  rw [algebraicIndependent_iff_linearIndependent_monomialValue]
  constructor
  · intro h T
    exact h.linearIndepOn _
  · intro h
    rw [← linearIndepOn_univ_iff, ← iUnion_degreeBox]
    exact linearIndepOn_iUnion_of_directed directed_degreeBox h

/-- **The proven floor `corank^{(1)} = ∞`.** -/
theorem aleph0_le_gradedCorank_primeLog :
    Cardinal.aleph0 ≤ gradedCorank ℚ (fun p : Nat.Primes => Real.log (p : ℕ)) 1 := by
  classical
  set u : Nat.Primes → ℝ := fun p => Real.log (p : ℕ) with hu
  set S : Submodule ℚ ℝ := gradedSpan ℚ u 1 with hSdef
  have hmem : ∀ p : Nat.Primes, u p ∈ S := by
    intro p
    refine Submodule.subset_span ⟨Finsupp.single p 1, ?_, ?_⟩
    · exact mem_degreeBox.mpr (le_of_eq (expDegree_single p))
    · exact monomialValue_single u p
  have hli : LinearIndependent ℚ (fun p : Nat.Primes => (⟨u p, hmem p⟩ : S)) :=
    LinearIndependent.of_comp (S.subtype) GaloisForLFunctions.linearIndependent_log_primes
  exact le_trans (Cardinal.aleph0_le_mk Nat.Primes) hli.cardinal_le_rank

/-! ## The relation lattice of the multipliers -/

/-- **Unique factorization kills every relation.**  The `ℤ`-relation lattice of the prime
logarithms is trivial. -/
theorem primeLog_ker_eq_bot :
    LinearMap.ker (Finsupp.linearCombination ℤ (fun p : Nat.Primes => Real.log (p : ℕ))) = ⊥ := by
  have hli : LinearIndependent ℤ (fun p : Nat.Primes => Real.log (p : ℕ)) :=
    GaloisForLFunctions.linearIndependent_log_primes.restrict_scalars (by
      intro a b hab
      simp only [zsmul_eq_mul, mul_one] at hab
      exact_mod_cast hab)
  rw [LinearMap.ker_eq_bot]
  exact (linearIndependent_iff_injective_finsuppLinearCombination).mp hli

/-- **`corank = ∞` over `ℚ`.**  With trivial relation lattice the quotient is the whole free module,
whose rank is the number of primes. -/
theorem aleph0_le_rank_quotient_primeLog :
    Cardinal.aleph0
      ≤ Module.rank ℤ ((Nat.Primes →₀ ℤ) ⧸
          LinearMap.ker (Finsupp.linearCombination ℤ (fun p : Nat.Primes => Real.log (p : ℕ)))) := by
  classical
  rw [primeLog_ker_eq_bot]
  have hequiv : ((Nat.Primes →₀ ℤ) ⧸ (⊥ : Submodule ℤ (Nat.Primes →₀ ℤ)))
      ≃ₗ[ℤ] (Nat.Primes →₀ ℤ) := Submodule.quotEquivOfEqBot ⊥ rfl
  rw [hequiv.rank_eq]
  have hbasis : Module.Basis Nat.Primes ℤ (Nat.Primes →₀ ℤ) := Finsupp.basisSingleOne
  have := hbasis.mk_eq_rank
  refine le_trans (Cardinal.aleph0_le_mk Nat.Primes) ?_
  exact hbasis.linearIndependent.cardinal_le_rank

/-- **The function-field border `corank = 1`.**  A single multiplier — a surjective degree map —
leaves quotient rank one. -/
theorem rank_quotient_ker_eq_one {P : Type*} (φ : (P →₀ ℤ) →ₗ[ℤ] ℤ)
    (hφ : Function.Surjective φ) :
    Module.rank ℤ ((P →₀ ℤ) ⧸ LinearMap.ker φ) = 1 := by
  have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hφ
  have hequiv : ((P →₀ ℤ) ⧸ LinearMap.ker φ) ≃ₗ[ℤ] LinearMap.range φ := φ.quotKerEquivRange
  have htop : (LinearMap.range φ : Submodule ℤ ℤ) = ⊤ := hrange
  have hequiv2 : (LinearMap.range φ : Submodule ℤ ℤ) ≃ₗ[ℤ] ℤ := by
    rw [htop]
    exact Submodule.topEquiv
  have hlift := (hequiv.trans hequiv2).lift_rank_eq
  rw [Module.rank_self, Cardinal.lift_one, Cardinal.lift_uzero] at hlift
  exact hlift

/-! ## The level separation -/

/-- Algebraic independence implies linear independence. -/
theorem linearIndependent_of_algebraicIndependent {v : ι → E} (h : AlgebraicIndependent F v) :
    LinearIndependent F v := h.linearIndependent

/-- **Level separation.**  Linear independence is strictly weaker than algebraic independence: a
single nonzero algebraic number is `ℚ`-linearly independent but algebraically dependent. -/
theorem exists_linearIndependent_not_algebraicIndependent :
    ∃ v : Fin 1 → ℝ, LinearIndependent ℚ v ∧ ¬ AlgebraicIndependent ℚ v := by
  classical
  refine ⟨fun _ => Real.sqrt 2, ?_, ?_⟩
  · rw [linearIndependent_unique_iff]
    intro hcon
    have h2 : Real.sqrt 2 ≠ 0 := by positivity
    exact h2 hcon
  · intro hind
    have hp : (MvPolynomial.X (0 : Fin 1) ^ 2 - MvPolynomial.C (2 : ℚ)) ≠ 0 := by
      intro hcon
      have hcoeff := congrArg (MvPolynomial.coeff (Finsupp.single (0 : Fin 1) 2)) hcon
      have hne : (Finsupp.single (0 : Fin 1) 2) ≠ 0 := by
        intro hz
        have := congrArg (fun d : Fin 1 →₀ ℕ => d 0) hz
        simp at this
      simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_zero, MvPolynomial.coeff_X_pow,
        MvPolynomial.coeff_C, if_pos rfl, if_neg (Ne.symm hne)] at hcoeff
      norm_num at hcoeff
    refine hp ((algebraicIndependent_iff.mp hind) _ ?_)
    rw [map_sub, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num

end GaloisForLFunctions.HTGeometry.CorankSeam
