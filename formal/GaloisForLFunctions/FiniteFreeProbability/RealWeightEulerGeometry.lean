import GaloisForLFunctions.FiniteFreeProbability.PositiveResidueRootGeometry

/-!
# Root geometry of Euler filters with real weights

A positive real Euler weight supplies one extra pole at zero. A regular
filter zero is the barycenter of these poles. On any enclosing circle a
nonzero boundary point survives a filter precisely when it was already
a multiple root. These statements apply directly to complex polynomials.
-/

open Polynomial Finset

namespace FiniteFreeProbability

noncomputable section

/-- The weighted Euler filter, with the weight in the coefficient field. -/
def weightedEuler {K : Type*} [CommSemiring K] (a : K) (p : K[X]) : K[X] :=
  C a * p + X * derivative p

theorem weightedEuler_coeff {K : Type*} [CommSemiring K] (a : K) (p : K[X]) (j : ℕ) :
    (weightedEuler a p).coeff j = (a+j)*p.coeff j := by
  cases j with
  | zero => simp [weightedEuler]
  | succ j =>
    simp only [weightedEuler, coeff_add, coeff_C_mul, coeff_X_mul, coeff_derivative, Nat.cast_succ]
    ring

private def poles (p : ℂ[X]) := insertNone p.roots.toFinset
private def pole : Option ℂ → ℂ := fun o => o.getD 0
private def residue (a : ℝ) (p : ℂ[X]) : Option ℂ → ℝ :=
  fun o => o.elim a (fun w => (p.rootMultiplicity w : ℝ))

private theorem residue_pos {a : ℝ} (ha : 0 < a) {p : ℂ[X]} (hp : p ≠ 0) :
    ∀ i ∈ poles p, 0 < residue a p i := by
  intro i hi
  cases i with
  | none => exact ha
  | some w =>
    have hw := (mem_roots hp).mp (Multiset.mem_toFinset.mp (some_mem_insertNone.mp hi))
    exact Nat.cast_pos.mpr ((rootMultiplicity_pos hp).mpr hw)

private theorem reg_zero {a : ℝ} (ha : 0 < a) {p : ℂ[X]} {z : ℂ}
    (h0 : (weightedEuler (a : ℂ) p).IsRoot z) (hpz : p.eval z ≠ 0) :
    (∀ i ∈ poles p, z ≠ pole i) ∧ residueField (poles p) pole (residue a p) z = 0 := by
  have hzval : (a : ℂ)*p.eval z + z*p.derivative.eval z = 0 := by
    simpa only [Polynomial.IsRoot, weightedEuler, eval_add, eval_mul, eval_C, eval_X] using h0
  have hz : z ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne') hpz (by simpa using hzval)
  refine ⟨?_, ?_⟩
  · intro i hi
    cases i with
    | none => exact hz
    | some w =>
      change z ≠ w
      rintro rfl
      exact hpz (isRoot_of_mem_roots (Multiset.mem_toFinset.mp (some_mem_insertNone.mp hi)))
  · have hlog : (∑ w ∈ p.roots.toFinset, (p.rootMultiplicity w : ℂ)/(z-w)) =
        p.derivative.eval z / p.eval z := by
      rw [(IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero hpz]
      calc
        _ = ∑ w ∈ p.roots.toFinset, p.rootMultiplicity w • (1/(z-w)) := by
          simp only [nsmul_eq_mul, div_eq_mul_inv, one_mul]
        _ = _ := by simp only [Finset.sum_multiset_map_count, count_roots]
    simp only [residueField, poles, sum_insertNone, pole, residue, Option.elim, Option.getD,
      sub_zero, Complex.ofReal_natCast, hlog]
    field_simp [hz, hpz]
    linear_combination hzval

private theorem pole_mem {p : ℂ[X]} : ∀ i ∈ poles p, pole i ∈ insert 0 (p.rootSet ℂ) := by
  intro i hi
  cases i with
  | none => exact Set.mem_insert _ _
  | some w =>
    apply Set.mem_insert_of_mem
    have hw := Multiset.mem_toFinset.mp (some_mem_insertNone.mp hi)
    simpa [pole, mem_rootSet, coe_aeval_eq_eval] using
      (show p ≠ 0 ∧ p.eval w = 0 from ⟨fun hp => by simp [hp] at hw, isRoot_of_mem_roots hw⟩)

/-- Positive real weights preserve the anchored convex hull, with no restriction on
the arguments or multiplicities of the input zeros. -/
theorem weightedEuler_root_hull {a : ℝ} (ha : 0 < a) (p : ℂ[X]) :
    (weightedEuler (a : ℂ) p).rootSet ℂ ⊆ convexHull ℝ (insert 0 (p.rootSet ℂ)) := by
  intro z hz
  rw [mem_rootSet, coe_aeval_eq_eval] at hz
  have hp : p ≠ 0 := fun he => hz.1 (by simp [weightedEuler, he])
  by_cases hpz : p.eval z = 0
  · exact subset_convexHull ℝ _ (Set.mem_insert_of_mem _ (by
      rw [mem_rootSet, coe_aeval_eq_eval]; exact ⟨hp, hpz⟩))
  obtain ⟨hreg,hfield⟩ := reg_zero ha hz.2 hpz
  exact convexHull_mono (Set.image_subset_iff.mpr (pole_mem (p := p)))
    (residue_zero_mem_hull _ _ _ _ insertNone_nonempty (residue_pos ha hp) hreg hfield)

/-- A nonzero point on an enclosing circle is a filtered root iff it was a multiple
root of the input. The origin and all input roots are in the specified closed disk. -/
theorem weightedEuler_boundary_root_iff {a : ℝ} (ha : 0 < a) {p : ℂ[X]} (hp : p ≠ 0)
    {c z : ℂ} (hz : z ≠ 0) (hc : ‖c‖ ≤ ‖z-c‖)
    (hd : ∀ w ∈ p.rootSet ℂ, ‖w-c‖ ≤ ‖z-c‖) :
    (weightedEuler (a : ℂ) p).IsRoot z ↔ 1 < p.rootMultiplicity z := by
  rw [one_lt_rootMultiplicity_iff_isRoot hp]
  constructor
  · intro h
    have hpz : p.IsRoot z := by
      by_contra hn
      obtain ⟨hreg,hfield⟩ := reg_zero ha h hn
      apply (lt_irrefl ‖z-c‖)
      apply residue_zero_in_open_disk (poles p) pole (residue a p) z c _ insertNone_nonempty
        (residue_pos ha hp) hreg hfield
      intro i hi
      rcases pole_mem i hi with he | he
      · simpa [he] using hc
      · exact hd _ he
    refine ⟨hpz, ?_⟩
    simpa only [Polynomial.IsRoot, weightedEuler, eval_add, eval_mul, eval_C, eval_X,
      hpz.eq_zero, mul_zero, zero_add, mul_eq_zero, hz, false_or] using h
  · rintro ⟨h₁,h₂⟩
    simp [Polynomial.IsRoot, weightedEuler, h₁.eq_zero, h₂.eq_zero]

#print axioms weightedEuler_root_hull
#print axioms weightedEuler_boundary_root_iff

end

end FiniteFreeProbability
