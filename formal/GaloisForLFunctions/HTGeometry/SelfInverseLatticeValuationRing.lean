import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Localization.FractionRing

/-!
# A rank-one lattice equal to its own inverse is trivial

Over a valuation ring `O` with fraction field `K` (in particular over a discrete valuation ring),
the only fractional ideal `𝔞 = a · O` with `𝔞 = 𝔞⁻¹` is `O` itself.

This is the step

> "Since the only fractional ideal `𝔭_K^n` (where `n ∈ ℤ`) satisfying `𝔭_K^n = 𝔭_K^{-n}` in `K`
> is `𝔭_K^n = O_K` (so `n = 0`), we obtain the statement of the proposition in this case."

in the proof of Proposition 3.4 of Suzuki, *Duality invariance of Faltings heights, Hodge line
bundles and global periods* (arXiv:2504.04993).  In the paper it is applied to
`𝔞 = det Lie 𝒜 ⊗ (det Lie ℬ)^{⊗ -1}`, the comparison of the two Hodge lattices inside the common
generic fibre; the conclusion is `det Lie 𝒜 = det Lie ℬ` as lattices
(`SelfInverseLattice.span_eq_of_ratio_eq_inv_ratio` below).

The proof needs no discreteness: in a valuation ring every element of `K` or its inverse is
integral, and `u² ` a unit forces `u` a unit.
-/

namespace GaloisForLFunctions.HTGeometry.SelfInverseLattice

open Submodule

variable {O K : Type*} [CommRing O] [IsDomain O] [ValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K]

theorem span_unit_eq_span_one {u : O} (hu : IsUnit u) :
    Submodule.span O {algebraMap O K u} = Submodule.span O {(1 : K)} := by
  obtain ⟨v, hv⟩ := hu
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    exact ⟨u, by simp [Algebra.smul_def]⟩
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    refine ⟨((v⁻¹ : Oˣ) : O), ?_⟩
    rw [Algebra.smul_def, ← hv, ← map_mul]
    simp

/-- **A rank-one lattice equal to its own inverse is the unit lattice.** -/
theorem span_eq_span_one_of_span_eq_span_inv {a : K} (ha : a ≠ 0)
    (h : Submodule.span O {a} = Submodule.span O {a⁻¹}) :
    Submodule.span O {a} = Submodule.span O {(1 : K)} := by
  have hinv : a⁻¹ ≠ 0 := inv_ne_zero ha
  -- `a = c • a⁻¹` and `a⁻¹ = d • a` with `c d = 1` in `O`
  obtain ⟨c, hc⟩ : ∃ c : O, c • a⁻¹ = a := by
    rw [← Submodule.mem_span_singleton, ← h]; exact Submodule.mem_span_singleton_self a
  obtain ⟨d, hd⟩ : ∃ d : O, d • a = a⁻¹ := by
    rw [← Submodule.mem_span_singleton, h]; exact Submodule.mem_span_singleton_self a⁻¹
  have hc' : algebraMap O K c = a * a := by
    rw [Algebra.smul_def] at hc
    field_simp at hc
    rw [hc]; ring
  have hd' : algebraMap O K d = a⁻¹ * a⁻¹ := by
    rw [Algebra.smul_def] at hd
    field_simp at hd
    field_simp
    linear_combination hd
  have hcd : c * d = 1 := by
    have : algebraMap O K (c * d) = algebraMap O K 1 := by
      rw [map_mul, hc', hd', map_one]
      field_simp
    exact (IsFractionRing.injective O K) this
  have hcu : IsUnit c := ⟨⟨c, d, hcd, by rw [mul_comm]; exact hcd⟩, rfl⟩
  have hdu : IsUnit d := ⟨⟨d, c, by rw [mul_comm]; exact hcd, hcd⟩, rfl⟩
  rcases ValuationRing.isInteger_or_isInteger O a with ⟨e, he⟩ | ⟨e, he⟩
  · -- `a` is integral
    have hee : e * e = c := by
      refine (IsFractionRing.injective O K) ?_
      rw [map_mul, he, hc']
    have : IsUnit e := isUnit_of_mul_isUnit_left (hee ▸ hcu)
    rw [← he]
    exact span_unit_eq_span_one this
  · -- `a⁻¹` is integral
    have hee : e * e = d := by
      refine (IsFractionRing.injective O K) ?_
      rw [map_mul, he, hd']
    have heu : IsUnit e := isUnit_of_mul_isUnit_left (hee ▸ hdu)
    obtain ⟨u, hu⟩ := heu
    have hau : a = algebraMap O K ((u⁻¹ : Oˣ) : O) := by
      have hne : algebraMap O K e ≠ 0 := by rw [he]; exact hinv
      have : a = (algebraMap O K e)⁻¹ := by rw [he, inv_inv]
      rw [this, ← hu, ← map_units_inv (algebraMap O K) u]
    rw [hau]
    exact span_unit_eq_span_one (Units.isUnit _)

/-- The form in which the lemma is used: if the ratio of two rank-one lattices equals its own
inverse, the two lattices coincide. -/
theorem span_eq_of_ratio_eq_inv_ratio {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Submodule.span O {a / b} = Submodule.span O {b / a}) :
    Submodule.span O {a} = Submodule.span O {b} := by
  have hab : a / b ≠ 0 := div_ne_zero ha hb
  have hinv : (a / b)⁻¹ = b / a := by field_simp
  have hkey := span_eq_span_one_of_span_eq_span_inv (O := O) hab (by rw [hinv]; exact h)
  -- `a / b` generates the unit lattice, hence `a` and `b` generate the same lattice
  have hmem : (a / b) ∈ Submodule.span O {(1 : K)} := by
    rw [← hkey]; exact Submodule.mem_span_singleton_self _
  have hmem' : (b / a) ∈ Submodule.span O {(1 : K)} := by
    rw [← hkey, h]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hmem'
  have hc2 : algebraMap O K c = a / b := by rw [Algebra.smul_def, mul_one] at hc; exact hc
  have hd2 : algebraMap O K d = b / a := by rw [Algebra.smul_def, mul_one] at hd; exact hd
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    rw [Algebra.smul_def, hc2]
    field_simp
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    refine ⟨d, ?_⟩
    rw [Algebra.smul_def, hd2]
    field_simp

end GaloisForLFunctions.HTGeometry.SelfInverseLattice
