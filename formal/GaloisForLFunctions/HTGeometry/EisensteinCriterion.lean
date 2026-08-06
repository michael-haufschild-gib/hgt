import GaloisForLFunctions.HTGeometry.AddValuationStrictMin

/-!
# A monic relation satisfied by a uniformizer is Eisenstein

If a uniformizer of the upper ring satisfies a monic relation of degree the ramification index,
that relation is automatically Eisenstein.  The reason is arithmetic rather than topological: the
term of index `i` has valuation `e * v(c_i) + i`, and these are pairwise distinct because their
residues modulo `e` are the distinct indices.  The minimum is therefore attained once, so the
valuation of the sum is exactly that minimum.  Since the sum has valuation `e`, the minimising index
is the only one congruent to zero, which pins the constant coefficient and pushes every other
coefficient into the maximal ideal.

No completeness is needed for this direction.  Completeness enters only in producing the monic
relation in the first place.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial IsDiscreteValuationRing

variable {A B : Type*}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

/-- **A monic relation of degree the ramification index satisfied by a uniformizer is
Eisenstein.** -/
theorem eisenstein_of_monic_uniformizer_root (ψ : A →+* B) {πA : A} (hπA : Irreducible πA)
    (e : ℕ) (he : 0 < e) (hram : addVal B (ψ πA) = (e : ℕ∞))
    {x : B} (hx : addVal B x = 1)
    {g : A[X]} (hmonic : g.Monic) (hdeg : g.natDegree = e)
    (hroot : eval x (g.map ψ) = 0) :
    (∀ i < e, addVal A (g.coeff i) ≠ 0) ∧ addVal A (g.coeff 0) = 1 := by
  classical
  set t : ℕ → B := fun i => ψ (g.coeff i) * x ^ i with ht
  set n : ℕ → ℕ := fun i => (addVal A (g.coeff i)).toNat with hn
  -- the valuation of a nonzero term
  have hterm : ∀ i : ℕ, g.coeff i ≠ 0 → addVal B (t i) = ((e * n i + i : ℕ) : ℕ∞) := by
    intro i hc
    have hfin : addVal A (g.coeff i) ≠ ⊤ := by
      rw [Ne, addVal_eq_top_iff]
      exact hc
    have hv : addVal A (g.coeff i) = ((n i : ℕ) : ℕ∞) := (ENat.coe_toNat hfin).symm
    rw [ht]
    simp only
    rw [AddValuation.map_mul, addVal_map_eq_mul_ramification ψ hπA e hram _ hc, hv, addVal_pow, hx,
      nsmul_eq_mul, mul_one]
    push_cast
    ring
  -- the expansion of the relation
  have hexp : x ^ e + ∑ i ∈ Finset.range e, t i = 0 := by
    rw [ht, ← hdeg, ← eval_map_monic ψ hmonic x]
    exact hroot
  have hxne : x ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hx
    simp at hx
  have hsumval : addVal B (∑ i ∈ Finset.range e, t i) = (e : ℕ∞) := by
    have hneg : ∑ i ∈ Finset.range e, t i = -x ^ e := by
      linear_combination (norm := ring_nf) hexp
    rw [hneg, AddValuation.map_neg, addVal_pow, hx, nsmul_eq_mul, mul_one]
  -- restrict to the nonzero terms
  set S : Finset ℕ := (Finset.range e).filter fun i => g.coeff i ≠ 0 with hS
  have hSsum : ∑ i ∈ S, t i = ∑ i ∈ Finset.range e, t i := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro i _ hi
    have hzero : g.coeff i = 0 := by
      by_contra hcon
      exact hi (Finset.mem_filter.mpr ⟨‹_›, hcon⟩)
    rw [ht]
    simp [hzero]
  have hSne : S.Nonempty := by
    rcases Finset.eq_empty_or_nonempty S with hempty | hne
    · exfalso
      rw [hempty, Finset.sum_empty] at hSsum
      rw [← hSsum, AddValuation.map_zero] at hsumval
      exact (ENat.top_ne_coe _) hsumval
    · exact hne
  -- pick the term of least valuation
  obtain ⟨i₀, hi₀S, hi₀min⟩ := S.exists_min_image (fun i => addVal B (t i)) hSne
  have hi₀range : i₀ < e := Finset.mem_range.mp (Finset.mem_filter.mp hi₀S).1
  have hi₀ne : g.coeff i₀ ≠ 0 := (Finset.mem_filter.mp hi₀S).2
  -- the valuations of distinct nonzero terms differ
  have hdistinct : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → addVal B (t i) ≠ addVal B (t j) := by
    intro i hi j hj hij
    rw [hterm i (Finset.mem_filter.mp hi).2, hterm j (Finset.mem_filter.mp hj).2]
    intro hcon
    have hnat : e * n i + i = e * n j + j := by exact_mod_cast hcon
    have hmod : i % e = j % e := by
      have h1 : (e * n i + i) % e = i % e := by simp
      have h2 : (e * n j + j) % e = j % e := by simp
      rw [← h1, ← h2, hnat]
    rw [Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hi).1),
      Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)] at hmod
    exact hij hmod
  -- the sum has the valuation of the least term
  have hstrict : ∀ j ∈ S.erase i₀, addVal B (t i₀) + 1 ≤ addVal B (t j) := by
    intro j hj
    have hjS : j ∈ S := Finset.mem_of_mem_erase hj
    have hjne : j ≠ i₀ := Finset.ne_of_mem_erase hj
    exact Order.add_one_le_of_lt
      (lt_of_le_of_ne (hi₀min j hjS) (hdistinct i₀ hi₀S j hjS (Ne.symm hjne)))
  have htne : t i₀ ≠ 0 := by
    intro h0
    have hval := hterm i₀ hi₀ne
    rw [h0, AddValuation.map_zero] at hval
    exact (ENat.top_ne_coe _) hval
  have hmin : addVal B (t i₀) = (e : ℕ∞) := by
    rw [← hsumval, ← hSsum, addVal_sum_eq_of_strict_min S t hi₀S htne hstrict]
  -- the minimising index is zero and the constant coefficient has valuation one
  have hi₀eq : e * n i₀ + i₀ = e := by
    have := hterm i₀ hi₀ne
    rw [hmin] at this
    exact_mod_cast this.symm
  have hi₀zero : i₀ = 0 := by
    have hmod : i₀ % e = 0 := by
      have : (e * n i₀ + i₀) % e = 0 := by rw [hi₀eq, Nat.mod_self]
      simpa [Nat.mul_add_mod] using this
    have := Nat.mod_eq_of_lt hi₀range
    omega
  subst hi₀zero
  have hn0 : n 0 = 1 := by
    have he' : e ≠ 0 := by omega
    have h2 : e * n 0 = e * 1 := by rw [mul_one]; omega
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero he') h2
  have hc0 : addVal A (g.coeff 0) = 1 := by
    have hfin : addVal A (g.coeff 0) ≠ ⊤ := by
      rw [Ne, addVal_eq_top_iff]
      exact hi₀ne
    rw [(ENat.coe_toNat hfin).symm]
    show ((n 0 : ℕ) : ℕ∞) = 1
    rw [hn0]
    rfl
  refine ⟨fun i hi => ?_, hc0⟩
  by_cases hzero : g.coeff i = 0
  · rw [hzero, AddValuation.map_zero]
    exact fun hcon => by simp at hcon
  · intro hcon
    have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hzero⟩
    have hni : n i = 0 := by
      show (addVal A (g.coeff i)).toNat = 0
      rw [hcon]
      rfl
    have hval : addVal B (t i) = ((i : ℕ) : ℕ∞) := by
      rw [hterm i hzero, hni]
      simp
    have hge : addVal B (t 0) ≤ addVal B (t i) := hi₀min i hiS
    rw [hmin, hval] at hge
    have : e ≤ i := by exact_mod_cast hge
    omega

end GaloisForLFunctions.HTGeometry
