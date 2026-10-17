import GaloisForLFunctions.HTGeometry.CompactOperatorFiniteSchurReduction

/-!
# Uniform finite capacity of nonpositive subspaces

For an identity-minus-compact form, every algebraic nonpositive subspace
injects into one fixed finite-dimensional observation space. Consequently
these subspaces are automatically finite-dimensional, with a common bound;
closedness is a conclusion rather than an extra premise.
-/

open Complex Set
open scoped InnerProduct BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry

theorem exists_nonpositive_subspace_dimension_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : H →L[ℂ] H) (hK : IsCompactOperator K) :
    ∃ n : ℕ, ∀ V : Submodule ℂ H,
      (∀ x ∈ V, (inner ℂ ((1-K) x) x).re ≤ 0) →
      FiniteDimensional ℂ V ∧ Module.finrank ℂ V ≤ n := by
  obtain ⟨M,hMclosed,hMfin,hcontract⟩ :=
    exists_finiteCodimensional_strictContractionKernel_of_isCompactOperator K hK
  letI : CompleteSpace M := hMclosed.completeSpace_coe
  letI : FiniteDimensional ℂ Mᗮ := hMfin
  have hpos (x : H) (hx : x ∈ M) (hne : x ≠ 0) :
      0 < (inner ℂ ((1-K) x) x).re := by
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hne
    have hb := hcontract x hx hne
    have hi : (inner ℂ (K x) x).re ≤ ‖K x‖*‖x‖ :=
      (Complex.re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) (K x) x)
    change 0 < (inner ℂ (x-K x) x).re
    rw [inner_sub_left,Complex.sub_re]
    have hs : (inner ℂ x x).re = ‖x‖^2 :=
      (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
    rw [hs]
    nlinarith [mul_lt_mul_of_pos_right hb hn,sq_pos_of_pos hn]
  refine ⟨Module.finrank ℂ Mᗮ,fun V hV => ?_⟩
  let P : V →ₗ[ℂ] Mᗮ := (Mᗮ).orthogonalProjectionOnto.toLinearMap.comp V.subtype
  have hPinj : Function.Injective P := by
    intro x y hxy
    have hproj : (Mᗮ).orthogonalProjectionOnto ((x-y : V) : H) = 0 := by
      have he : P (x-y) = 0 := by rw [map_sub,hxy,sub_self]
      exact he
    have hm : ((x-y : V) : H) ∈ M := by
      have hh := (Mᗮ).orthogonalProjectionOnto_eq_zero_iff.mp hproj
      rwa [M.orthogonal_orthogonal] at hh
    have hz : ((x-y : V) : H) = 0 := by
      by_contra hn
      exact (not_lt_of_ge (hV _ (x-y).property)) (hpos _ hm hn)
    exact sub_eq_zero.mp (Subtype.ext hz)
  letI : FiniteDimensional ℂ V := FiniteDimensional.of_injective P hPinj
  exact ⟨inferInstance,LinearMap.finrank_le_finrank_of_injective hPinj⟩

private theorem negativeGram_pair_sum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (B : H →L[ℂ] H) {m : ℕ} (v : Fin m → H)
    (horth : ∀ i j, i ≠ j → inner ℂ (B (v i)) (v j) = 0)
    (c : Fin m → ℂ) (i : Fin m) :
    inner ℂ (B (v i)) (∑ j, c j • v j) = c i*inner ℂ (B (v i)) (v i) := by
  classical
  rw [inner_sum]
  simp only [inner_smul_right]
  apply Finset.sum_eq_single i
  · intro j _hj hji
    rw [horth i j hji.symm,mul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private theorem negativeGram_sum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (B : H →L[ℂ] H) {m : ℕ} (v : Fin m → H)
    (horth : ∀ i j, i ≠ j → inner ℂ (B (v i)) (v j) = 0)
    (c : Fin m → ℂ) :
    (inner ℂ (B (∑ j, c j • v j)) (∑ j, c j • v j)).re =
      ∑ i, ‖c i‖^2*(inner ℂ (B (v i)) (v i)).re := by
  have he : inner ℂ (B (∑ j, c j • v j)) (∑ j, c j • v j) =
      ∑ i, ((‖c i‖^2 : ℝ) : ℂ)*inner ℂ (B (v i)) (v i) := by
    rw [map_sum,sum_inner]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [map_smul,inner_smul_left,negativeGram_pair_sum B v horth c i,
      ← mul_assoc,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  simpa only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] using congrArg Complex.re he

/-- The number of mutually form-orthogonal negative directions is bounded
uniformly, even when the family is not orthogonal in the ambient norm. -/
theorem exists_negative_orthogonal_family_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : H →L[ℂ] H) (hK : IsCompactOperator K) :
    ∃ n : ℕ, ∀ m : ℕ, ∀ v : Fin m → H,
      (∀ i, (inner ℂ ((1-K) (v i)) (v i)).re < 0) →
      (∀ i j, i ≠ j → inner ℂ ((1-K) (v i)) (v j) = 0) → m ≤ n := by
  obtain ⟨n,hn⟩ := exists_nonpositive_subspace_dimension_bound K hK
  refine ⟨n,fun m v hneg horth => ?_⟩
  let B : H →L[ℂ] H := 1-K
  let V : Submodule ℂ H := Submodule.span ℂ (range v)
  have hnonpos : ∀ x ∈ V, (inner ℂ ((1-K) x) x).re ≤ 0 := by
    intro x hx
    obtain ⟨c,rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
    rw [negativeGram_sum (1-K) v horth c]
    exact Finset.sum_nonpos fun i _hi => mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hneg i).le
  obtain ⟨hVfin,hdim⟩ := hn V hnonpos
  letI : FiniteDimensional ℂ V := hVfin
  let w : Fin m → V := fun i => ⟨v i,Submodule.subset_span (mem_range_self i)⟩
  have hli : LinearIndependent ℂ w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hs : ∑ j, c j • v j = 0 := by
      have hh := congrArg (fun x : V => (x : H)) hc
      simpa only [Submodule.coe_sum,Submodule.coe_smul,Submodule.coe_zero,w] using hh
    have hp := congrArg (fun x : H => inner ℂ (B (v i)) x) hs
    rw [negativeGram_pair_sum B v horth c i,inner_zero_right] at hp
    apply (mul_eq_zero.mp hp).resolve_right
    intro hz
    have hh := hneg i
    change (inner ℂ (B (v i)) (v i)).re < 0 at hh
    rw [hz,Complex.zero_re] at hh
    exact lt_irrefl 0 hh
  have hb := hli.fintype_card_le_finrank
  simpa only [Fintype.card_fin] using hb.trans hdim

end GaloisForLFunctions.HTGeometry
