import GaloisForLFunctions.HTGeometry.BarnesLadderDescent
import GaloisForLFunctions.HTGeometry.BarnesFieldLadderOrderOne

/-!
# The exact differential-translation annihilator of the Barnes source

Everything the annihilator theorem asks of a source is now proved for the Barnes source itself: the
descent reaches the single-direction source modulo the differentially algebraic sector, and the
single-direction source, corrected by a linear term, solves the order-one ladder equation with
defect a simple pole.  Hence

```text
P Ψ_N is DA over ℂ(z)   ↔   ∏_j (T_j - 1) ∣ P
```

for rationally independent periods in a half-plane.  This is theorem `(A)` of the card, for the
Barnes multiple-gamma logarithmic derivative.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic zeroNomeScalarTower

variable {N : ℕ}

/-- The full frame is the frame carried by all directions. -/
theorem barnesSourceLogDerivMero_subframe_univ [NeZero N] (ω : Fin N → ℂ)
    (hω : ∀ i, 0 < (ω i).im) :
    letI : Nonempty {i : Fin N // i ∈ (Finset.univ : Finset (Fin N))} :=
      ⟨⟨(0 : Fin N), Finset.mem_univ _⟩⟩
    barnesSourceLogDerivMero (subframe ω Finset.univ) (subframe_im_pos hω Finset.univ)
      = barnesSourceLogDerivMero ω hω := by
  letI : Nonempty {i : Fin N // i ∈ (Finset.univ : Finset (Fin N))} :=
    ⟨⟨(0 : Fin N), Finset.mem_univ _⟩⟩
  exact barnesSourceLogDerivMero_comp_equiv
    (Equiv.subtypeUnivEquiv (fun i : Fin N => Finset.mem_univ i)) ω hω _

theorem card_singleton_subtype (j : Fin N) :
    Fintype.card {i : Fin N // i ∈ ({j} : Finset (Fin N))} = 1 := by
  rw [Fintype.card_coe, Finset.card_singleton]

/-- **The exact differential-translation annihilator of the Barnes source.**  For rationally
independent periods in a common half-plane, a constant-coefficient differential-translation
operator sends the Barnes source into the differentially algebraic sector exactly when the full
ladder product divides it. -/
theorem differentialAlgebraicOver_diffTranslateApply_barnesSource_iff [NeZero N] (ω : Fin N → ℂ)
    (hω : ∀ i, 0 < (ω i).im)
    (hindep : ∀ n : Fin N → ℤ, ∑ k, (n k : ℂ) * ω k = 0 → ∀ k, n k = 0)
    (P : MvPolynomial (Fin N) (Polynomial ℂ)) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (diffTranslateApply ω P (barnesSourceLogDerivMero ω hω))
      ↔ fullLadder N ∣ P := by
  classical
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  letI : Nonempty {i : Fin N // i ∈ (Finset.univ : Finset (Fin N))} :=
    ⟨⟨(0 : Fin N), Finset.mem_univ _⟩⟩
  -- the single-direction data
  letI : ∀ j : Fin N, Nonempty {i : Fin N // i ∈ ({j} : Finset (Fin N))} :=
    fun j => ⟨⟨j, Finset.mem_singleton_self j⟩⟩
  set φ : Fin N → meroField (Set.univ : Set ℂ) := fun j =>
    barnesLadderSolutionOne (subframe ω ({j} : Finset (Fin N)))
      (subframe_im_pos hω ({j} : Finset (Fin N))) ⟨j, Finset.mem_singleton_self j⟩ with hφdef
  have hφ : ∀ j, addTranslationMeroEquiv (ω j) (φ j)
      = φ j + algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
        (1 / (RatFunc.X + RatFunc.C (ω j))) := by
    intro j
    have h := addTranslationMeroEquiv_barnesLadderSolutionOne
      (subframe ω ({j} : Finset (Fin N))) (subframe_im_pos hω ({j} : Finset (Fin N)))
      (card_singleton_subtype j) ⟨j, Finset.mem_singleton_self j⟩
    exact h
  -- the descent supplies the ladder hypothesis
  have hladder : ∀ j : Fin N, DifferentialAlgebraicOver (RatFunc ℂ)
      (diffTranslateApply ω (complementaryLadder j) (barnesSourceLogDerivMero ω hω)
        - algebraMap ℂ (meroField (Set.univ : Set ℂ)) ((-1 : ℂ) ^ N) * φ j) := by
    intro j
    have hdesc := differentialAlgebraicOver_ladderProd_descent ω hω j N Finset.univ
      (by rw [Finset.card_univ, Fintype.card_fin]) (Finset.mem_univ j)
    rw [barnesSourceLogDerivMero_subframe_univ ω hω] at hdesc
    set Ψj : meroField (Set.univ : Set ℂ) :=
      barnesSourceLogDerivMero (subframe ω ({j} : Finset (Fin N)))
        (subframe_im_pos hω ({j} : Finset (Fin N))) with hΨj
    set w : meroField (Set.univ : Set ℂ) :=
      ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty Set.infinite_univ
        (RatFunc.C ((((subframe ω ({j} : Finset (Fin N))) ⟨j, Finset.mem_singleton_self j⟩)⁻¹ +
          barnesLadderConstOne (subframe ω ({j} : Finset (Fin N)))
            ⟨j, Finset.mem_singleton_self j⟩) /
          (subframe ω ({j} : Finset (Fin N))) ⟨j, Finset.mem_singleton_self j⟩) *
          RatFunc.X) with hw
    have hφval : φ j = -Ψj + w := rfl
    have hsign : algebraMap ℂ (meroField (Set.univ : Set ℂ)) ((-1 : ℂ) ^ N)
        = (-1 : meroField (Set.univ : Set ℂ)) ^ N := by
      rw [map_pow, map_neg, map_one]
    have hpow : (-1 : meroField (Set.univ : Set ℂ)) ^ N
        = -((-1 : meroField (Set.univ : Set ℂ)) ^ (N - 1)) := by
      obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
      rw [show N' + 1 - 1 = N' by omega, pow_succ]
      ring
    have hrw : diffTranslateApply ω (complementaryLadder j) (barnesSourceLogDerivMero ω hω)
          - algebraMap ℂ (meroField (Set.univ : Set ℂ)) ((-1 : ℂ) ^ N) * φ j
        = (diffTranslateApply ω (ladderProd (Finset.univ.erase j))
              (barnesSourceLogDerivMero ω hω)
            - (-1 : meroField (Set.univ : Set ℂ)) ^ (N - 1) * Ψj)
          + (-1 : meroField (Set.univ : Set ℂ)) ^ (N - 1) * w := by
      rw [ladderProd_univ_erase, hsign, hpow, hφval]
      ring
    rw [hrw]
    refine differentialAlgebraicOver_add hdesc ?_
    refine differentialAlgebraicOver_mul ?_ (differentialAlgebraicOver_algebraMap _)
    have hpowmem : ((-1 : meroField (Set.univ : Set ℂ)) ^ (N - 1))
        = algebraMap ℂ (meroField (Set.univ : Set ℂ)) ((-1 : ℂ) ^ (N - 1)) := by
      rw [map_pow, map_neg, map_one]
    rw [hpowmem]
    exact differentialAlgebraicOver_algebraMap_complex _
  exact differentialAlgebraicOver_diffTranslateApply_iff_fullLadder_dvd ω hindep
    (barnesSourceLogDerivMero ω hω) φ (fun j => ω j) hφ (fun _ => (-1 : ℂ) ^ N)
    (fun _ => pow_ne_zero _ (by norm_num)) hladder hN P

end

end GaloisForLFunctions.HTGeometry
