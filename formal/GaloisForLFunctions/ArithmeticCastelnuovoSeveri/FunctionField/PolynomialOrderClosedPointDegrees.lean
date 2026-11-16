import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.PolynomialOrderClosedPoints
import Mathlib.FieldTheory.Finite.Extension

/-!
# Bounded-degree closed points of polynomial orders

All closed primes of degree at most `N` support points over the extension of
degree `N!`. This gives finite degree cutoffs, and hence literal finite sums
for the point count in every positive extension degree.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolynomialOrderClosedPoints
open Polynomial IsDedekindDomain
variable (K B : Type*) [Field K] [Finite K] [CommRing B]
    [IsDedekindDomain B] [Infinite B] [Algebra K B] [Algebra K[X] B]
    [IsScalarTower K K[X] B] [Module.Free K[X] B] [Module.Finite K[X] B]
    (p : ℕ) [Fact p.Prime] [CharP K p]

include p in
/-- A finite degree cutoff contains only finitely many actual closed primes. -/
theorem finite_places_degree_le (N : ℕ) :
    {v : HeightOneSpectrum B | placeDegree K B v ≤ N}.Finite := by
  letI : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩
  have hf := finite_places_degree_dvd K B (FiniteField.Extension K p N.factorial)
  rw [FiniteField.finrank_extension] at hf
  exact hf.subset fun v hv => Nat.dvd_factorial (placeDegree_pos K B v) hv

/-- The finite set of closed primes below a residue-degree cutoff. -/
def placesDegreeLe (N : ℕ) : Finset (HeightOneSpectrum B) :=
  (finite_places_degree_le K B p N).toFinset

@[simp] theorem mem_placesDegreeLe (v : HeightOneSpectrum B) (N : ℕ) :
    v ∈ placesDegreeLe K B p N ↔ placeDegree K B v ≤ N :=
  Set.Finite.mem_toFinset _

theorem placesDegreeLe_mono {N M : ℕ} (hNM : N ≤ M) :
    placesDegreeLe K B p N ⊆ placesDegreeLe K B p M := by
  intro v hv
  exact (mem_placesDegreeLe K B p v M).mpr
    (((mem_placesDegreeLe K B p v N).mp hv).trans hNM)

/-- A closed prime appears over degree `e` precisely when its degree divides `e`. -/
theorem placesOver_extension_eq (e : ℕ) [NeZero e] :
    placesOver K B (FiniteField.Extension K p e) =
      (placesDegreeLe K B p e).filter (fun v => placeDegree K B v ∣ e) := by
  classical
  ext v
  rw [mem_placesOver_iff, FiniteField.finrank_extension,
    Finset.mem_filter, mem_placesDegreeLe]
  exact ⟨fun hv => ⟨Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne e)) hv, hv⟩,
    fun hv => hv.2⟩

/-- The point count over an extension is the degree-weighted sum of its splitting closed primes. -/
theorem card_algHom_extension_eq_closed_degree_sum (e : ℕ) [NeZero e] :
    Nat.card (B →ₐ[K] FiniteField.Extension K p e) =
      ∑ v ∈ placesDegreeLe K B p e, if placeDegree K B v ∣ e then placeDegree K B v else 0 := by
  classical
  rw [card_algHom_eq_closed_place_sum, placesOver_extension_eq]
  simp only [Finset.sum_coe_sort, Finset.sum_filter]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolynomialOrderClosedPoints
