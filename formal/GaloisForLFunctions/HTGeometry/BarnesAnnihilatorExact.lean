import GaloisForLFunctions.HTGeometry.DiffTranslateOperatorAction
import GaloisForLFunctions.HTGeometry.TranslationFaceSplitting
import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary

/-!
# The exact differential-translation annihilator of a laddered source

Let the periods be rationally independent and let `Ψ` be a source with the Barnes ladder property:
applying the complementary product `D_j = ∏_{k ≠ j} (T_k - 1)` produces, modulo the differentially
algebraic sector, a solution `φ_j` of the order-one ladder equation `φ(z + ω_j) - φ(z) = 1/z`; and
the full product `∏_j (T_j - 1)` already lands in that sector.

Then a constant-coefficient differential-translation operator sends `Ψ` into the differentially
algebraic sector exactly when the full ladder product divides it:

```text
P Ψ  is DA   ↔   ∏_j (T_j - 1) ∣ P.
```

The forward direction is the ring action: write `P = (∏_j (T_j - 1)) T` and apply `T` to an already
differentially algebraic element.  For the reverse direction, if the product does not divide `P`
then some restriction `Q = P|_{T_j = 1}` is nonzero; splitting `P = Q + (T_j - 1) S` and applying
`D_j` turns the hypothesis into differential algebraicity of `P φ_j`, whence of `Q φ_j`, because
`(T_j - 1) φ_j = 1/z` is rational.  But `Q` avoids `T_j`, so `Q φ_j` is a nonzero
constant-coefficient differential-linear form in translates on distinct orbits, hence
hypertranscendental.
-/

open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic zeroNomeScalarTower

/-! ## The ladder products -/

/-- The full ladder product `∏_j (T_j - 1)`. -/
def fullLadder (N : ℕ) : MvPolynomial (Fin N) (Polynomial ℂ) :=
  ∏ k, (MvPolynomial.X k - 1)

/-- The complementary ladder product `∏_{k ≠ j} (T_k - 1)`. -/
def complementaryLadder {N : ℕ} (j : Fin N) : MvPolynomial (Fin N) (Polynomial ℂ) :=
  ∏ k ∈ Finset.univ.erase j, (MvPolynomial.X k - 1)

theorem X_sub_one_mul_complementaryLadder {N : ℕ} (j : Fin N) :
    (MvPolynomial.X j - 1) * complementaryLadder j = fullLadder N :=
  Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)

/-! ## Subtraction and the ladder generator -/

theorem diffTranslateApply_neg {N : ℕ} (ω : Fin N → ℂ)
    (P : MvPolynomial (Fin N) (Polynomial ℂ)) (y : meroField (Set.univ : Set ℂ)) :
    diffTranslateApply ω (-P) y = - diffTranslateApply ω P y := by
  have h := diffTranslateApply_add ω P (-P) y
  rw [add_neg_cancel, diffTranslateApply_zero_op] at h
  linear_combination -h

theorem diffTranslateApply_sub {N : ℕ} (ω : Fin N → ℂ)
    (P Q : MvPolynomial (Fin N) (Polynomial ℂ)) (y : meroField (Set.univ : Set ℂ)) :
    diffTranslateApply ω (P - Q) y = diffTranslateApply ω P y - diffTranslateApply ω Q y := by
  rw [sub_eq_add_neg, diffTranslateApply_add, diffTranslateApply_neg, ← sub_eq_add_neg]

theorem monomialShift_single {N : ℕ} (ω : Fin N → ℂ) (j : Fin N) :
    monomialShift ω (Finsupp.single j 1) = ω j := by
  classical
  rw [monomialShift, Finset.sum_eq_single j]
  · rw [Finsupp.single_eq_same, Nat.cast_one, one_mul]
  · intro k _ hk
    rw [Finsupp.single_apply, if_neg (show ¬ j = k from fun h => hk h.symm), Nat.cast_zero,
      zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- The ladder generator acts as the translation defect. -/
theorem diffTranslateApply_X_sub_one {N : ℕ} (ω : Fin N → ℂ) (j : Fin N)
    (y : meroField (Set.univ : Set ℂ)) :
    diffTranslateApply ω (MvPolynomial.X j - 1) y = addTranslationMeroEquiv (ω j) y - y := by
  rw [diffTranslateApply_sub, diffTranslateApply_one,
    show (MvPolynomial.X j : MvPolynomial (Fin N) (Polynomial ℂ))
      = MvPolynomial.monomial (Finsupp.single j 1) 1 from rfl,
    diffTranslateApply_monomial, differentialOperatorApply_one, monomialShift_single]

/-! ## The exact annihilator -/

/-- **The exact differential-translation annihilator.**  For rationally independent periods and a
source with the ladder property, an operator sends the source into the differentially algebraic
sector exactly when the full ladder product divides it. -/
theorem differentialAlgebraicOver_diffTranslateApply_iff_fullLadder_dvd {N : ℕ} (ω : Fin N → ℂ)
    (hindep : ∀ n : Fin N → ℤ, ∑ k, (n k : ℂ) * ω k = 0 → ∀ k, n k = 0)
    (Ψ : meroField (Set.univ : Set ℂ)) (φ : Fin N → meroField (Set.univ : Set ℂ)) (b : Fin N → ℂ)
    (hφ : ∀ j, addTranslationMeroEquiv (ω j) (φ j)
      = φ j + algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
        (1 / (RatFunc.X + RatFunc.C (b j))))
    (cc : Fin N → ℂ) (hcc : ∀ j, cc j ≠ 0)
    (hladder : ∀ j, DifferentialAlgebraicOver (RatFunc ℂ)
      (diffTranslateApply ω (complementaryLadder j) Ψ
        - algebraMap ℂ (meroField (Set.univ : Set ℂ)) (cc j) * φ j))
    (hN : 0 < N) (P : MvPolynomial (Fin N) (Polynomial ℂ)) :
    DifferentialAlgebraicOver (RatFunc ℂ) (diffTranslateApply ω P Ψ) ↔ fullLadder N ∣ P := by
  classical
  -- the full ladder product already lands in the differentially algebraic sector
  have hfull : DifferentialAlgebraicOver (RatFunc ℂ)
      (diffTranslateApply ω (fullLadder N) Ψ) := by
    set j : Fin N := ⟨0, hN⟩ with hj
    set D : meroField (Set.univ : Set ℂ) := diffTranslateApply ω (complementaryLadder j) Ψ with hD
    have hstep : diffTranslateApply ω (fullLadder N) Ψ
        = addTranslationMeroEquiv (ω j) D - D := by
      rw [← X_sub_one_mul_complementaryLadder j, diffTranslateApply_mul,
        diffTranslateApply_X_sub_one]
    set cφ : meroField (Set.univ : Set ℂ) :=
      algebraMap ℂ (meroField (Set.univ : Set ℂ)) (cc j) * φ j with hcφ
    have hsplit : addTranslationMeroEquiv (ω j) D - D
        = (addTranslationMeroEquiv (ω j) cφ - cφ)
          + (addTranslationMeroEquiv (ω j) (D - cφ) - (D - cφ)) := by
      rw [map_sub]
      ring
    rw [hstep, hsplit]
    refine differentialAlgebraicOver_add ?_ ?_
    · rw [hcφ, map_mul, addTranslationMeroEquiv_algebraMap_complex, hφ j]
      have hcancel : algebraMap ℂ (meroField (Set.univ : Set ℂ)) (cc j) *
            (φ j + algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
              (1 / (RatFunc.X + RatFunc.C (b j))))
            - algebraMap ℂ (meroField (Set.univ : Set ℂ)) (cc j) * φ j
          = algebraMap ℂ (meroField (Set.univ : Set ℂ)) (cc j) *
            algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
              (1 / (RatFunc.X + RatFunc.C (b j))) := by ring
      rw [hcancel]
      exact differentialAlgebraicOver_mul (differentialAlgebraicOver_algebraMap_complex _)
        (differentialAlgebraicOver_algebraMap _)
    · exact differentialAlgebraicOver_sub
        (differentialAlgebraicOver_addTranslationMeroEquiv _ (hladder j)) (hladder j)
  constructor
  · intro hDA
    by_contra hnd
    obtain ⟨j, -, hQne⟩ :=
      exists_evalOneAt_ne_zero_of_not_dvd (S := (Finset.univ : Finset (Fin N))) (P := P)
        (by rw [fullLadder] at hnd; exact hnd)
    obtain ⟨S, hS⟩ := Ideal.mem_span_singleton.mp (sub_evalOneAt_mem_span j P)
    -- differential algebraicity travels to the reduced source
    have h1 : DifferentialAlgebraicOver (RatFunc ℂ)
        (diffTranslateApply ω P (diffTranslateApply ω (complementaryLadder j) Ψ)) := by
      have h0 := differentialAlgebraicOver_diffTranslateApply ω (complementaryLadder j) hDA
      rwa [← diffTranslateApply_mul, mul_comm, diffTranslateApply_mul] at h0
    have h2 : DifferentialAlgebraicOver (RatFunc ℂ) (diffTranslateApply ω P (φ j)) := by
      have hsplit : diffTranslateApply ω (complementaryLadder j) Ψ
          = algebraMap ℂ (meroField (Set.univ : Set ℂ)) (cc j) * φ j
            + (diffTranslateApply ω (complementaryLadder j) Ψ
              - algebraMap ℂ (meroField (Set.univ : Set ℂ)) (cc j) * φ j) := by ring
      rw [hsplit, diffTranslateApply_add_input,
        diffTranslateApply_algebraMap_complex_mul] at h1
      have hrest := differentialAlgebraicOver_diffTranslateApply ω P (hladder j)
      have hsub := differentialAlgebraicOver_sub h1 hrest
      have hsub' : DifferentialAlgebraicOver (RatFunc ℂ)
          (algebraMap ℂ (meroField (Set.univ : Set ℂ)) (cc j) *
            diffTranslateApply ω P (φ j)) := by simpa using hsub
      have hscaled := differentialAlgebraicOver_mul
        (differentialAlgebraicOver_algebraMap_complex (cc j)⁻¹) hsub'
      have hcancel : algebraMap ℂ (meroField (Set.univ : Set ℂ)) (cc j)⁻¹ *
            (algebraMap ℂ (meroField (Set.univ : Set ℂ)) (cc j) *
              diffTranslateApply ω P (φ j))
          = diffTranslateApply ω P (φ j) := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (hcc j), map_one, one_mul]
      rwa [hcancel] at hscaled
    -- the ladder factor makes its part rational
    have h3 : DifferentialAlgebraicOver (RatFunc ℂ)
        (diffTranslateApply ω (evalOneAt j P) (φ j)) := by
      have hP : P = evalOneAt j P + (MvPolynomial.X j - 1) * S := by
        rw [← hS]
        ring
      rw [hP, diffTranslateApply_add] at h2
      have hrat : DifferentialAlgebraicOver (RatFunc ℂ)
          (diffTranslateApply ω ((MvPolynomial.X j - 1) * S) (φ j)) := by
        rw [mul_comm, diffTranslateApply_mul, diffTranslateApply_X_sub_one, hφ j]
        have hcancel : φ j + algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
              (1 / (RatFunc.X + RatFunc.C (b j))) - φ j
            = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
              (1 / (RatFunc.X + RatFunc.C (b j))) := by
          ring
        rw [hcancel]
        exact differentialAlgebraicOver_diffTranslateApply ω S
          (differentialAlgebraicOver_algebraMap _)
      have hsub := differentialAlgebraicOver_sub h2 hrat
      simpa using hsub
    exact hypertranscendentalOver_diffTranslateApply_of_avoid ω hindep j (b j) (φ j) (hφ j)
      (evalOneAt j P) hQne (fun n hn => support_evalOneAt_apply_eq_zero j P hn) h3
  · rintro ⟨T, rfl⟩
    have hmul : diffTranslateApply ω (fullLadder N * T) Ψ
        = diffTranslateApply ω T (diffTranslateApply ω (fullLadder N) Ψ) := by
      rw [← diffTranslateApply_mul, mul_comm]
    rw [hmul]
    exact differentialAlgebraicOver_diffTranslateApply ω T hfull

end

end GaloisForLFunctions.HTGeometry
