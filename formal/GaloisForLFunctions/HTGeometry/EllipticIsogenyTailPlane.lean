import GaloisForLFunctions.HTGeometry.EllipticIsogenyDeck
import GaloisForLFunctions.HTGeometry.PeriodRigidity

/-!
# The phase tail of a degree-expanding elliptic isogeny protocol is the constants

For a sequence of accumulated isogeny degrees whose norms tend to infinity, an elliptic function
that is a pullback at every depth is invariant under translations by arbitrarily small nonzero
division points of the lattice, hence constant.

This is the deck-closure statement for the elliptic column: the Zariski closure of the union of the
prefix kernels is the whole curve, and the phase tail is exactly its invariant field.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The first period of a period pair is nonzero. -/
theorem periodPair_ω₁_ne_zero (L : PeriodPair) : L.ω₁ ≠ 0 := by
  intro h
  have := L.indep.ne_zero 0
  simp only [Matrix.cons_val_zero] at this
  exact this h

/-- **Arbitrarily small periods force a constant.**  An element of the meromorphic plane field
invariant under translations by a sequence of nonzero vectors tending to zero is a constant. -/
theorem eq_const_of_small_periods (p : ℕ → ℂ) (hpne : ∀ n, p n ≠ 0)
    (hp0 : Tendsto p atTop (𝓝 0)) {x : MeromorphicPlane}
    (hx : ∀ n, planeTranslate (p n) x = x) :
    ∃ c : ℂ, x = algebraMap ℂ MeromorphicPlane c := by
  obtain ⟨f, hf, rfl⟩ := x.exists_rep
  have hgerm : ∀ n : ℕ, ∀ y : ℂ, (fun w => f (w + p n)) =ᶠ[𝓝[≠] y] f := by
    intro n
    have hn := hx n
    rw [planeTranslate_ofMeromorphic] at hn
    exact (ofMeromorphic_eq_iff _ _).mp hn
  have hFper : ∀ n : ℕ, Function.Periodic (toMeromorphicNFOn f Set.univ) (p n) :=
    fun n => periodic_toMeromorphicNFOn_of_eventuallyEq hf (hgerm n)
  have hconst := meromorphicNF_constant_of_small_periods (toMeromorphicNFOn f Set.univ)
    (meromorphicNFOn_toMeromorphicNFOn f Set.univ) p hp0 hpne hFper
  refine ⟨toMeromorphicNFOn f Set.univ 0, ?_⟩
  rw [algebraMap_plane, ← ofMeromorphic_toMeromorphicNFOn hf]
  refine (ofMeromorphic_eq_iff _ _).mpr fun y => ?_
  exact Filter.Eventually.of_forall fun w => hconst w 0

/-- The division points of a lattice along a degree-expanding sequence are arbitrarily small. -/
theorem tendsto_lattice_division_points (L : PeriodPair) (M : ℕ → ℂ) (hM : ∀ n, M n ≠ 0)
    (hMinf : Tendsto (fun n => ‖M n‖) atTop atTop) :
    (∀ n, L.ω₁ / M n ≠ 0) ∧ Tendsto (fun n => L.ω₁ / M n) atTop (𝓝 0) := by
  refine ⟨fun n => div_ne_zero (periodPair_ω₁_ne_zero L) (hM n), ?_⟩
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : ∀ n, ‖L.ω₁ / M n‖ = ‖L.ω₁‖ / ‖M n‖ := fun n => norm_div _ _
  simp only [hnorm]
  exact Filter.Tendsto.const_div_atTop hMinf _

/-- **The elliptic phase tail is the constants.**  An element that is a pullback along every
accumulated isogeny is invariant under translations by arbitrarily small division points of the
lattice, hence constant. -/
theorem eq_const_of_forall_mem_range_planeScale (L : PeriodPair) (M : ℕ → ℂ)
    (hM : ∀ n, M n ≠ 0) (hMinf : Tendsto (fun n => ‖M n‖) atTop atTop)
    {x : MeromorphicPlane}
    (hx : ∀ n, ∃ y ∈ ellipticSubfield L, planeScale (M n) (hM n) y = x) :
    ∃ c : ℂ, x = algebraMap ℂ MeromorphicPlane c := by
  obtain ⟨hpne, hp0⟩ := tendsto_lattice_division_points L M hM hMinf
  refine eq_const_of_small_periods _ hpne hp0 fun n => ?_
  have hdeck := (exists_mem_ellipticSubfield_planeScale_iff L (hM n) _).mp (hx n)
  refine hdeck (L.ω₁ / M n) ?_
  rw [mul_comm, div_mul_cancel₀ _ (hM n)]
  exact L.ω₁_mem_lattice

end GaloisForLFunctions.HTGeometry
