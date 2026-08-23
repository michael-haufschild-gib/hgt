import GaloisForLFunctions.RHTower.DeningerArithmeticCofiniteDivisorQuotient

/-!
# Cofinite divisor Hasse principle

A finitely supported global divisor lies on retained prime coordinates exactly when all outside
local residues vanish.  Equality modulo retained-prime divisors is therefore detected at every
outside coordinate, and each finite local residue profile has a global divisor realization.
-/

namespace RHTower

universe u v

noncomputable section

variable {R : Type u} {ι : Type v} [CommRing R]

/-- A global finite divisor is supported on the retained primes exactly when every outside local
residue vanishes. -/
theorem deningerCofiniteDivisor_hasse_iff (S : ι → Prop) (x : ι →₀ R) :
    x ∈ LinearMap.range (deningerInsideDivisorEmbedding (R := R) S) ↔
      ∀ i : DeningerOutsidePrime S, x i.1 = 0 := by
  have hexact := LinearMap.exact_iff.mp (deningerCofiniteDivisor_exact (R := R) S)
  constructor
  · intro hx i
    have hxker : x ∈ LinearMap.ker (deningerOutsideResidue (R := R) S) := by
      rw [hexact]
      exact hx
    have hzero := LinearMap.mem_ker.mp hxker
    have hi := congrArg (fun y : DeningerOutsidePrime S →₀ R => y i) hzero
    simpa [deningerOutsideResidue, Finsupp.lcomapDomain_apply] using hi
  · intro h
    rw [← hexact]
    rw [LinearMap.mem_ker]
    ext i
    simpa [deningerOutsideResidue, Finsupp.lcomapDomain_apply] using h i

/-- Two global finite divisors agree modulo retained-prime divisors exactly when all outside local
residues agree. -/
theorem deningerCofiniteDivisor_congr_iff_forall_local
    (S : ι → Prop) (x y : ι →₀ R) :
    x - y ∈ LinearMap.range (deningerInsideDivisorEmbedding (R := R) S) ↔
      ∀ i : DeningerOutsidePrime S, x i.1 = y i.1 := by
  rw [deningerCofiniteDivisor_hasse_iff]
  simp only [Finsupp.sub_apply, sub_eq_zero]

/-- Every finitely supported collection of outside local residues is realized by a global finite
divisor. -/
theorem deningerCofiniteDivisor_hasse_surjective
    (S : ι → Prop) (r : DeningerOutsidePrime S →₀ R) :
    ∃ x : ι →₀ R, ∀ i, x i.1 = r i := by
  obtain ⟨x, hx⟩ := deningerOutsideResidue_surjective (R := R) S r
  refine ⟨x, fun i => ?_⟩
  have hi := congrArg (fun y : DeningerOutsidePrime S →₀ R => y i) hx
  simpa [deningerOutsideResidue, Finsupp.lcomapDomain_apply] using hi

end


end RHTower
