import GaloisForLFunctions.HTGeometry.PrimeFrequencyInfiniteRank
import GaloisForLFunctions.RHTower.LadderNesting
import GaloisForLFunctions.RHTower.ZeroResonanceIndependence

/-!
# Prime-resonance algebraic-coefficient rank universality

Baker independence of finite prime-log packets survives multiplication by every nonzero complex
resonance scale.  Thus the corpus's rational resonance independence strengthens uniformly to
independence over the algebraic numbers.  Every finite scaled packet has full algebraic-coefficient
rank, while the global rational prime-frequency module is not finitely generated.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Every nonzero complex scaling preserves Baker's algebraic-number linear independence of a
finite packet of distinct prime logarithms. -/
theorem resonanceExponent_algClosure_linearIndependent_fin
    (α : ℂ) (hα : α ≠ 0) {n : ℕ}
    (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (hpinj : Function.Injective p) :
    LinearIndependent (algebraicClosure ℚ ℂ)
      (fun i => α * (Real.log (p i) : ℂ)) := by
  let scale : ℂ →ₗ[algebraicClosure ℚ ℂ] ℂ :=
    LinearMap.mulLeft (algebraicClosure ℚ ℂ) α
  have hker : scale.ker = ⊥ := LinearMap.ker_eq_bot.mpr (fun x y hxy => by
    change α * x = α * y at hxy
    exact mul_left_cancel₀ hα hxy)
  have hmap := (primeLogs_algClosure_linearIndependent p hp hpinj).map' scale hker
  simpa [scale, Function.comp_def] using hmap

/-- A scaled finite prime-resonance packet has rank exactly its number of primes over the algebraic
numbers. -/
theorem resonanceExponent_algClosure_finrank_span
    (α : ℂ) (hα : α ≠ 0) {n : ℕ}
    (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (hpinj : Function.Injective p) :
    Module.finrank (algebraicClosure ℚ ℂ)
      (Submodule.span (algebraicClosure ℚ ℂ)
        (Set.range fun i => α * (Real.log (p i) : ℂ))) = n := by
  rw [finrank_span_eq_card
    (resonanceExponent_algClosure_linearIndependent_fin α hα p hp hpinj)]
  exact Fintype.card_fin n

/-- **Prime-resonance algebraic-coefficient rank universality law.**  Nonzero resonance scaling is
blind not only to rational relations but to every algebraic-coefficient relation: each finite packet
has full rank over `ℚ̄`.  At the global level the underlying rational prime-frequency module remains
non-finitely generated, so no finite phase dictionary can capture the tower. -/
theorem primeResonance_algebraicCoefficientRank_universality
    (α : ℂ) (hα : α ≠ 0) {n : ℕ}
    (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (hpinj : Function.Injective p) :
    LinearIndependent (algebraicClosure ℚ ℂ)
        (fun i => α * (Real.log (p i) : ℂ)) ∧
      Module.finrank (algebraicClosure ℚ ℂ)
        (Submodule.span (algebraicClosure ℚ ℂ)
          (Set.range fun i => α * (Real.log (p i) : ℂ))) = n ∧
      ¬ Module.Finite ℚ GaloisForLFunctions.primeLogFullSpan := by
  exact ⟨resonanceExponent_algClosure_linearIndependent_fin α hα p hp hpinj,
    resonanceExponent_algClosure_finrank_span α hα p hp hpinj,
    GaloisForLFunctions.primeLogFullSpan_not_finite⟩

end

end GaloisForLFunctions.RHTower
