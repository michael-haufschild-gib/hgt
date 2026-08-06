import GaloisForLFunctions.HTGeometry.MonogenicOfDigitExpansion
import GaloisForLFunctions.HTGeometry.EisensteinCriterion

/-!
# The powers of a uniformizer are independent

Distinct powers of a uniformizer below the ramification index carry valuations in distinct residue
classes modulo that index, so no two terms of a relation among them can have equal valuation.  The
strict minimum principle then gives the relation a finite valuation, which a vanishing sum cannot
have.

Together with the generation statement this makes the powers of a uniformizer a basis of the
extension, so the rank is the ramification index and the extension has a power basis.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDiscreteValuationRing

variable {A B : Type*}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]

/-- **The powers of a uniformizer below the ramification index are linearly independent.** -/
theorem linearIndependent_pow {πA : A} (hπA : Irreducible πA) (e : ℕ)
    (hram : addVal B (algebraMap A B πA) = (e : ℕ∞)) {x : B} (hx : addVal B x = 1) :
    LinearIndependent A fun i : Fin e => x ^ (i : ℕ) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i₀ hi₀
  by_contra hne
  set t : Fin e → B := fun i => algebraMap A B (g i) * x ^ (i : ℕ) with ht
  set n : Fin e → ℕ := fun i => (addVal A (g i)).toNat with hn
  have hterm : ∀ i : Fin e, g i ≠ 0 →
      addVal B (t i) = ((e * n i + (i : ℕ) : ℕ) : ℕ∞) := by
    intro i hc
    have hfin : addVal A (g i) ≠ ⊤ := by
      rw [Ne, addVal_eq_top_iff]
      exact hc
    have hv : addVal A (g i) = ((n i : ℕ) : ℕ∞) := (ENat.coe_toNat hfin).symm
    rw [ht]
    simp only
    rw [AddValuation.map_mul, addVal_map_eq_mul_ramification (algebraMap A B) hπA e hram _ hc, hv,
      addVal_pow, hx, nsmul_eq_mul, mul_one]
    push_cast
    ring
  set S : Finset (Fin e) := s.filter fun i => g i ≠ 0 with hS
  have hSsum : ∑ i ∈ S, t i = ∑ i ∈ s, t i := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro i _ hi
    have hzero : g i = 0 := by
      by_contra hcon
      exact hi (Finset.mem_filter.mpr ⟨‹_›, hcon⟩)
    rw [ht]
    simp [hzero]
  have hi₀S : i₀ ∈ S := Finset.mem_filter.mpr ⟨hi₀, hne⟩
  have hSne : S.Nonempty := ⟨i₀, hi₀S⟩
  obtain ⟨j₀, hj₀S, hj₀min⟩ := S.exists_min_image (fun i => addVal B (t i)) hSne
  have hj₀ne : g j₀ ≠ 0 := (Finset.mem_filter.mp hj₀S).2
  have hdistinct : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → addVal B (t i) ≠ addVal B (t j) := by
    intro i hi j hj hij
    rw [hterm i (Finset.mem_filter.mp hi).2, hterm j (Finset.mem_filter.mp hj).2]
    intro hcon
    have hnat : e * n i + (i : ℕ) = e * n j + (j : ℕ) := by exact_mod_cast hcon
    have hmod : (i : ℕ) % e = (j : ℕ) % e := by
      have h1 : (e * n i + (i : ℕ)) % e = (i : ℕ) % e := by simp
      have h2 : (e * n j + (j : ℕ)) % e = (j : ℕ) % e := by simp
      rw [← h1, ← h2, hnat]
    rw [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hmod
    exact hij (Fin.ext hmod)
  have hstrict : ∀ j ∈ S.erase j₀, addVal B (t j₀) + 1 ≤ addVal B (t j) := by
    intro j hj
    have hjS : j ∈ S := Finset.mem_of_mem_erase hj
    have hjne : j ≠ j₀ := Finset.ne_of_mem_erase hj
    exact Order.add_one_le_of_lt
      (lt_of_le_of_ne (hj₀min j hjS) (hdistinct j₀ hj₀S j hjS (Ne.symm hjne)))
  have htne : t j₀ ≠ 0 := by
    intro h0
    have hval := hterm j₀ hj₀ne
    rw [h0, AddValuation.map_zero] at hval
    exact (ENat.top_ne_coe _) hval
  have hzero : ∑ i ∈ s, t i = 0 := by
    rw [ht]
    simpa [Algebra.smul_def] using hsum
  have hfin : addVal B (∑ i ∈ S, t i) = addVal B (t j₀) :=
    addVal_sum_eq_of_strict_min S t hj₀S htne hstrict
  rw [hSsum, hzero, AddValuation.map_zero] at hfin
  rw [hterm j₀ hj₀ne] at hfin
  exact (ENat.top_ne_coe _) hfin

/-- **The powers of a uniformizer form a basis of the extension.** -/
noncomputable def uniformizerPowBasis [Module.Finite A B] {πA : A} (hπA : Irreducible πA) (e : ℕ)
    (hram : addVal B (algebraMap A B πA) = (e : ℕ∞)) {x : B} (hx : addVal B x = 1)
    (hres : ∀ b : B, ∃ a : A, addVal B (b - algebraMap A B a) ≠ 0)
    (hdvd : algebraMap A B πA ∣ x ^ e) :
    Module.Basis (Fin e) A B :=
  Module.Basis.mk (linearIndependent_pow hπA e hram hx)
    (le_of_eq (span_pow_eq_top hπA hx e hres hdvd).symm)

/-- **The rank of the extension is the ramification index.**  For a finite extension of discrete
valuation rings with trivial residue extension the two agree, so the extension is totally
ramified in the numerical sense as well. -/
theorem finrank_eq_ramificationIndex [Module.Finite A B] {πA : A} (hπA : Irreducible πA) (e : ℕ)
    (hram : addVal B (algebraMap A B πA) = (e : ℕ∞)) {x : B} (hx : addVal B x = 1)
    (hres : ∀ b : B, ∃ a : A, addVal B (b - algebraMap A B a) ≠ 0)
    (hdvd : algebraMap A B πA ∣ x ^ e) :
    Module.finrank A B = e := by
  rw [Module.finrank_eq_card_basis (uniformizerPowBasis hπA e hram hx hres hdvd)]
  simp

end GaloisForLFunctions.HTGeometry
