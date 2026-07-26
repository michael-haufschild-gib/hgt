import GaloisForLFunctions.RHTower.WeldAffineTrivialization
import GaloisForLFunctions.RHTower.WeldBoundedSpectralGauge

/-!
# Prime-weld affine exactness versus bounded spectral obstruction

The prime weld cocycle is algebraically exact after passing to its natural affine coefficient
module, even with functional-equation covariance imposed.  Independently, every bounded spectral
realization of an affine cochain is forced to have order zero and therefore cannot trivialize the
prime weld.  Together these facts identify the exact category wall: affine primitives exist, but
every one contains a forced derivation coefficient and is spectrally unbounded.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- **Prime weld affine-exact/bounded-spectral obstruction universality.**  FE-covariant algebraic
trivializations exist, while every exact affine primitive has derivation coefficient one and no
bounded realization on the fixed spectral `L²` space. -/
theorem primeWeld_affineExact_boundedSpectralObstructionUniversality
    {p : ℕ} (hp : p.Prime) :
    (∃ b : WeldGroup → WeldAffineCoeff (Real.log p),
      IsFECovariantAffineCochain (Real.log p) b ∧
        twoCoboundary b = weldAffineCocycle (Real.log p)) ∧
      ∀ b : WeldGroup → WeldAffineCoeff (Real.log p),
        twoCoboundary b = weldAffineCocycle (Real.log p) →
          (b weldGenD).1 = 1 ∧
            ¬ Nonempty (BoundedWeldSpectralCochain (Real.log p) b) := by
  refine ⟨prime_exists_FECovariantAffinePrimitive hp, ?_⟩
  intro b hb
  have hlog : Real.log p ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt))
  refine ⟨weldAffinePrimitive_derivCoeff_eq_one hlog hb, ?_⟩
  intro hbounded
  exact prime_no_boundedWeldSpectralPrimitive hp ⟨b, hbounded, hb⟩

end

end GaloisForLFunctions.RHTower
