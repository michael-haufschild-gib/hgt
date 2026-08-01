import GaloisForLFunctions.HTGeometry.CompactAbelianCharSpan

/-!
# Splitting a finite-dimensional invariant subspace off a character vector

Translation is unitary, so the orthogonal complement of a character line inside an invariant
subspace is again invariant.  Peeling off one character line at a time therefore exhausts a
finite-dimensional invariant subspace by character lines.

The form used below is the one the Peter–Weyl argument needs: if every continuous character is
trivial at `g`, then the translation by `g` is the identity on every finite-dimensional invariant
subspace of an eigenspace of a convolution operator.
-/

open MeasureTheory TopologicalSpace

namespace GaloisForLFunctions

namespace CompactAbelian

noncomputable section

variable {G : Type*} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

omit [T2Space G] in
/-- **Translation is unitary**: its adjoint is the opposite translation. -/
theorem inner_transOp (a : G) (u v : Lp ℂ 2 (haarProb G)) :
    inner ℂ (transOp a u) v = inner ℂ u (transOp (-a) v) := by
  have hL : inner ℂ (transOp a u) v
      = ∫ x, (starRingEnd ℂ) (u (x + a)) * v x ∂(haarProb G) := by
    rw [inner_lp_eq]
    refine integral_congr_ae ?_
    filter_upwards [transOp_coeFn a u] with x hx
    rw [hx]
  have hR : inner ℂ u (transOp (-a) v)
      = ∫ x, (starRingEnd ℂ) (u x) * v (x + -a) ∂(haarProb G) := by
    rw [inner_lp_eq]
    refine integral_congr_ae ?_
    filter_upwards [transOp_coeFn (-a) v] with x hx
    rw [hx]
  rw [hL, hR]
  have h := integral_add_right
    (fun x : G => (starRingEnd ℂ) ((u : G → ℂ) x) * (v : G → ℂ) (x + -a)) a
  refine Eq.trans ?_ h
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (starRingEnd ℂ) ((u : G → ℂ) (x + a)) * (v : G → ℂ) x
      = (starRingEnd ℂ) ((u : G → ℂ) (x + a)) * (v : G → ℂ) (x + a + -a)
  have hxa : x + a + -a = x := by abel
  rw [hxa]

variable (k : G → ℂ) (hk : Continuous k) {C : ℝ} (hC : ∀ z, ‖k z‖ ≤ C)

omit [T2Space G] in
include hk hC in
/-- **If every continuous character is trivial at `g`, translation by `g` is the identity on every
finite-dimensional invariant subspace of an eigenspace.** -/
theorem transOp_eq_self_of_finite_invariant {lam : ℂ} (hlam : lam ≠ 0) {g : G}
    (hchar : ∀ χ : G → ℂ, Continuous χ → (∀ a b, χ (a + b) = χ a * χ b) →
      (∀ a, ‖χ a‖ = 1) → χ g = 1) :
    ∀ (n : ℕ) (W : Submodule ℂ (Lp ℂ 2 (haarProb G))), FiniteDimensional ℂ W →
      Module.finrank ℂ W = n →
      (∀ a : G, ∀ u ∈ W, transOp a u ∈ W) →
      (∀ u ∈ W, convOp k hk hC u = lam • u) →
      ∀ u ∈ W, transOp g u = u := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W hWfin hWrank hWinv hWeig u hu
    haveI := hWfin
    by_cases hWbot : W = ⊥
    · rw [hWbot, Submodule.mem_bot] at hu
      rw [hu, map_zero]
    -- a character vector
    obtain ⟨w, χ, hw0, hwW, hχ⟩ := exists_char_vector hWbot hWinv
    obtain ⟨hχc, hχm, hχn⟩ :=
      continuous_character_of_char_vector k hk hC hlam hw0 (hWeig w hwW) hχ
    have hg : transOp g w = w := by
      rw [hχ g, hchar χ hχc hχm hχn, one_smul]
    -- split off the character line
    set K : Submodule ℂ (Lp ℂ 2 (haarProb G)) := Submodule.span ℂ {w} with hK
    haveI : FiniteDimensional ℂ K := by
      rw [hK]
      exact FiniteDimensional.span_of_finite ℂ (Set.finite_singleton w)
    have hKW : K ≤ W := by
      rw [hK, Submodule.span_le, Set.singleton_subset_iff]
      exact hwW
    have hsup : K ⊔ (Kᗮ ⊓ W) = W :=
      Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hKW
    set W' : Submodule ℂ (Lp ℂ 2 (haarProb G)) := Kᗮ ⊓ W with hW'
    -- the complement is invariant
    have hW'inv : ∀ a : G, ∀ x ∈ W', transOp a x ∈ W' := by
      intro a x hx
      refine ⟨?_, hWinv a x hx.2⟩
      show transOp a x ∈ Kᗮ
      rw [Submodule.mem_orthogonal]
      intro y hy
      have hyw : ∃ c : ℂ, y = c • w := by
        rw [hK, Submodule.mem_span_singleton] at hy
        obtain ⟨c, hc⟩ := hy
        exact ⟨c, hc.symm⟩
      obtain ⟨c, rfl⟩ := hyw
      have hxK : ∀ z ∈ K, inner ℂ z x = (0 : ℂ) := by
        intro z hz
        exact (Submodule.mem_orthogonal K x).mp hx.1 z hz
      have h1 : inner ℂ (c • w) (transOp a x) = inner ℂ (transOp (-a) (c • w)) x := by
        rw [inner_transOp (-a) (c • w) x, neg_neg]
      rw [h1, map_smul, hχ (-a), smul_smul]
      have h2 : inner ℂ ((c * χ (-a)) • w) x = (starRingEnd ℂ) (c * χ (-a)) * inner ℂ w x := by
        rw [inner_smul_left]
      rw [h2, hxK w (Submodule.mem_span_singleton_self w), mul_zero]
    have hW'eig : ∀ x ∈ W', convOp k hk hC x = lam • x := fun x hx => hWeig x hx.2
    haveI : FiniteDimensional ℂ W' := Submodule.finiteDimensional_of_le (inf_le_right)
    -- the complement is strictly smaller
    have hwnotW' : w ∉ W' := by
      intro hw
      have := (Submodule.mem_orthogonal K w).mp hw.1 w (Submodule.mem_span_singleton_self w)
      exact hw0 (inner_self_eq_zero.mp this)
    have hlt : W' < W := lt_of_le_of_ne inf_le_right (by
      intro hEq
      exact hwnotW' (hEq ▸ hwW))
    have hrank : Module.finrank ℂ W' < n := by
      rw [← hWrank]
      exact Submodule.finrank_lt_finrank_of_lt hlt
    have hW'id : ∀ x ∈ W', transOp g x = x :=
      ih (Module.finrank ℂ W') hrank W' inferInstance rfl hW'inv hW'eig
    -- conclude on the sum
    have huW : u ∈ K ⊔ W' := by rw [hsup]; exact hu
    rw [Submodule.mem_sup] at huW
    obtain ⟨y, hy, z, hz, rfl⟩ := huW
    obtain ⟨c, hc⟩ : ∃ c : ℂ, y = c • w := by
      rw [hK, Submodule.mem_span_singleton] at hy
      obtain ⟨c, hcy⟩ := hy
      exact ⟨c, hcy.symm⟩
    rw [map_add, hc, map_smul, hg, hW'id z hz]

end

end CompactAbelian

end GaloisForLFunctions
