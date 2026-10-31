import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticClosedPoints
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticZeta
import Mathlib.FieldTheory.Finite.Extension

/-!
# Bounded-degree closed places and extension point counts

Every place of degree at most `N` splits over the extension of degree `N!`.
Its point maps therefore place it in one finite set. The resulting literal
finite sums give every coefficient of the curve's point-count ghost.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open IsDedekindDomain
noncomputable section

private theorem ellipticExtension_finrank (n : ℕ) [NeZero n] :
    Module.finrank Constants (FiniteField.Extension Constants 3 n) = n := by
  convert! FiniteField.finrank_extension Constants 3 n using 1
  congr 1
  exact Subsingleton.elim _ _

/-- The actual affine primes have finite bounded-degree sets. -/
theorem finite_affinePlaces_degree_le (N : ℕ) :
    {v : HeightOneSpectrum A | affinePlaceDegree v ≤ N}.Finite := by
  letI : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩
  have hf := finite_affinePlaces_degree_dvd (FiniteField.Extension Constants 3 N.factorial)
  rw [ellipticExtension_finrank] at hf
  exact hf.subset fun v hv => Nat.dvd_factorial (affinePlaceDegree_pos v) hv

/-- Literal finite set of affine primes below a residue-degree cutoff. -/
def affinePlacesDegreeLe (N : ℕ) : Finset (HeightOneSpectrum A) :=
  (finite_affinePlaces_degree_le N).toFinset

@[simp] theorem mem_affinePlacesDegreeLe (v : HeightOneSpectrum A) (N : ℕ) :
    v ∈ affinePlacesDegreeLe N ↔ affinePlaceDegree v ≤ N :=
  Set.Finite.mem_toFinset _

theorem affinePlacesDegreeLe_mono {N M : ℕ} (hNM : N ≤ M) :
    affinePlacesDegreeLe N ⊆ affinePlacesDegreeLe M := by
  intro v hv
  exact (mem_affinePlacesDegreeLe v M).mpr ((mem_affinePlacesDegreeLe v N).mp hv |>.trans hNM)

/-- The degree-dividing support is the corresponding filter of the degree cutoff. -/
theorem affinePlacesOver_extension_eq (n : ℕ) [NeZero n] :
    affinePlacesOver (FiniteField.Extension Constants 3 n) =
      (affinePlacesDegreeLe n).filter (fun v => affinePlaceDegree v ∣ n) := by
  classical
  ext v
  rw [mem_affinePlacesOver_iff, ellipticExtension_finrank,
    Finset.mem_filter, mem_affinePlacesDegreeLe]
  exact ⟨fun hv => ⟨Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) hv, hv⟩,
    fun hv => hv.2⟩

/-- Every positive ghost coefficient counts the actual finite places and infinity. -/
theorem extensionPointCount_eq_closed_degree_sum (n : ℕ) [NeZero n] :
    extensionPointCount n = 1 +
      ∑ v ∈ affinePlacesDegreeLe n, if affinePlaceDegree v ∣ n then affinePlaceDegree v else 0 := by
  classical
  rw [extensionPointCount, dif_neg (NeZero.ne n), card_points_eq_closed_place_sum]
  rw [affinePlacesOver_extension_eq]
  simpa only [Finset.sum_coe_sort, Finset.sum_filter, Nat.add_comm]

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.finite_affinePlaces_degree_le
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.extensionPointCount_eq_closed_degree_sum
