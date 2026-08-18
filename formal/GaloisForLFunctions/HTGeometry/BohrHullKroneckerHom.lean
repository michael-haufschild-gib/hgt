import GaloisForLFunctions.HTGeometry.BohrHullCharCombination
import GaloisForLFunctions.HTGeometry.RealSubgroupIntBasis
import GaloisForLFunctions.HTGeometry.BohrHullTorusQuotient

/-!
# Kronecker realization for arbitrary finite frequency sets

Kronecker's theorem realises prescribed phases only on rationally independent frequencies.  An
arbitrary finite set of frequencies generates a free group whose basis is rationally independent and
still consists of hull frequencies, and every member of the set is an integer combination of that
basis.  So any multiplicative unimodular prescription — one that respects the integer relations —
is realised on the whole finite set by a single point of the hull.
-/

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open Finset

variable {E : Type*} [NormedAddCommGroup E] {f : ℝ →ᵇ E}

/-- **Kronecker realization with relations.** -/
theorem exists_bohrHull_char_eq_finset (htb : HasTotallyBoundedOrbit (fun x => f x))
    {F : Finset ℝ} (hF : ∀ γ ∈ F, IsBohrHullFrequency f γ) {ω : ℝ → ℂ}
    (hmul : ∀ a b, ω (a + b) = ω a * ω b) (hnorm : ∀ a, ‖ω a‖ = 1) :
    ∃ x : BohrHull f, ∀ γ ∈ F, bohrHullChar f γ x = ω γ := by
  classical
  obtain ⟨k, b, hind, hbmem, hspan⟩ := exists_rat_independent_intSpanning F
  have hsub : AddSubgroup.closure (F : Set ℝ) ≤ bohrHullFrequencies f := by
    rw [AddSubgroup.closure_le]
    intro γ hγ
    exact mem_bohrHullFrequencies.mpr (hF γ hγ)
  have hbfreq : ∀ i, IsBohrHullFrequency f (b i) := fun i =>
    mem_bohrHullFrequencies.mp (hsub (hbmem i))
  obtain ⟨x, hx⟩ := exists_bohrHull_charPacket_eq_of_norm_one htb hind hbfreq
    (fun i => ω (b i)) (fun i => hnorm (b i))
  refine ⟨x, fun γ hγ => ?_⟩
  obtain ⟨n, hn⟩ := hspan γ hγ
  rw [hn, bohrHullChar_intCombination hbfreq n x, char_intCombination hmul hnorm b n]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hx i]

end GaloisForLFunctions
