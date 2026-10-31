import GaloisForLFunctions.AdelicKreinGeometry.Haar.PolynomialIndexPreservation
import GaloisForLFunctions.AdelicKreinGeometry.Haar.SubgroupEndpoints
import GaloisForLFunctions.BiarithmeticGeometry.Affine.FiniteSubgroupAvoidance

/-!
# Polynomial index preservation for every proper rational successor

Factorial division separates any finite quadrature grid modulo a proper rational
subgroup. Polynomial reproduction is exact at every grid scale, while positive
Gram diagonals decrease inversely with the number of blocks.
-/

open Complex Finset Filter Topology Matrix
open scoped ComplexConjugate Classical
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.BiarithmeticGeometry
open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- A suitable grid scale makes each translated column family orthonormal for a proper successor. -/
theorem exists_subgroup_quadrature_scale {ι : Type*} [Fintype ι]
    (H : AddSubgroup ℚ) (hH : H ≠ ⊤) {p : AffineGroupQ → ℂ}
    (hs : HasSubgroupSuccessor H p) (g : ι → AffineGroupQ) (n N : ℕ) :
    ∃ ε : ℚ, ∀ a (i j : Fin n × Fin N),
      p ((quadratureTranslatedFamily g ε n N (a, i))⁻¹ *
        quadratureTranslatedFamily g ε n N (a, j)) = if i = j then 1 else 0 := by
  let x : Fin n × Fin N → ℚ := fun j => quadratureTranslationNode 1 j.1 j.2.val
  have hx : Function.Injective x := by
    intro i j he
    have h := @quadratureTranslationNode_injective n 1 (show (0 : ℚ) < 1 by norm_num)
      (i.1, i.2.val) (j.1, j.2.val) he
    exact Prod.ext (congrArg (fun z : Fin n × ℕ => z.1) h)
      (Fin.ext (congrArg (fun z : Fin n × ℕ => z.2) h))
  obtain ⟨ε, _, hsep⟩ := exists_scale_grid_differences_not_mem H hH
    (fun a => affSlope (g a)) (fun a => affSlope_ne_zero (g a)) x hx
  have hnode (j : Fin n × Fin N) :
      quadratureTranslationNode ε j.1 j.2.val = ε * x j := by
    dsimp only [x, quadratureTranslationNode]
    ring
  have h1 : p 1 = 1 := hasSubgroupSuccessor_one hs
  refine ⟨ε, ?_⟩
  intro a i j
  by_cases hij : i = j
  · subst j
    rw [inv_mul_cancel, h1, if_pos rfl]
  · have hnot : (quadratureTranslationNode ε j.1 j.2.val -
        quadratureTranslationNode ε i.1 i.2.val) / affSlope (g a) ∉ H := by
      rw [hnode, hnode]
      exact hsep a i j hij
    simp only [quadratureTranslatedFamily, translated_affine_quotient,
      sub_self, zero_add, inv_mul_cancel, map_one, mul_one]
    rw [hs, if_neg hnot, if_neg hij]

/-- Positive carriers of any proper subgroup preserve every polynomial-fibre negative index. -/
theorem negIndex_add_positive_subgroup_polynomial (H : AddSubgroup ℚ) (hH : H ≠ ⊤)
    {p h : AffineGroupQ → ℂ} (hp : IsPosDefKernel p) (hs : HasSubgroupSuccessor H p)
    (hh : IsHermKernel h) (hpoly : HasPolynomialTranslationFibres h) :
    negIndex (fun g => p g + h g) = negIndex h := by
  apply le_antisymm (negIndex_add_posDef_le hp)
  apply negIndex_le_iff.mpr
  intro m g
  obtain ⟨n, _, hquad⟩ := exists_polynomial_gram_quadrature_order hpoly g
  choose ε hε using fun N => exists_subgroup_quadrature_scale H hH hs g n (N + 1)
  let C : ℝ := ∑ i : Fin n, normSq (originQuadratureWeight n i)
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => normSq_nonneg _
  let P : ℕ → Matrix (Fin m) (Fin m) ℂ := fun N =>
    weightedKernelGram p (quadratureTranslatedFamily g (ε N) n (N + 1))
      (translationQuadratureWeight n (N + 1))
  have hdiag (N : ℕ) (a : Fin m) : P N a a = ((C / (N + 1 : ℕ) : ℝ) : ℂ) := by
    change weightedKernelGram p _ _ a a = _
    rw [weightedKernelGram_diagonal_of_orthonormal _ _ _ a (fun i j => by
      by_cases hij : i = j
      · simpa only [if_pos hij] using hε N a i j
      · simpa only [if_neg hij] using hε N a i j),
      sum_normSq_translationQuadratureWeight (Nat.succ_pos N)]
  have hbound (N : ℕ) (a b : Fin m) : ‖P N a b‖ ≤ C / (N + 1 : ℕ) :=
    norm_entry_le_constant_posSemidef_diagonal (weightedKernelGram_posSemidef hp _ _)
      (div_nonneg hC (Nat.cast_nonneg _)) (hdiag N) a b
  have hindex (N : ℕ) :
      (hermNegIndex (HeckeKreinToeplitz.gram h g + P N) : ℕ∞) ≤
        negIndex (fun u => p u + h u) := by
    have he : weightedKernelGram (fun u => p u + h u)
        (quadratureTranslatedFamily g (ε N) n (N + 1)) (translationQuadratureWeight n (N + 1)) =
          HeckeKreinToeplitz.gram h g + P N := by
      rw [weightedKernelGram_add, hquad (ε N) (N + 1) (Nat.succ_pos N)]
      exact add_comm _ _
    rw [← he]
    exact hermNegIndex_weightedKernelGram_le _ _ _
  have hinv : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hδ : Tendsto (fun N : ℕ => C / (N + 1 : ℕ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul C
  have hlim (a b : Fin m) : Tendsto (fun N => P N a b) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    filter_upwards [hδ.eventually (gt_mem_nhds hη)] with N hN
    simpa only [dist_zero_right] using (hbound N a b).trans_lt hN
  have hconv (a b : Fin m) :
      Tendsto (fun N => (HeckeKreinToeplitz.gram h g + P N) a b) atTop
        (𝓝 (HeckeKreinToeplitz.gram h g a b)) := by
    simpa only [Matrix.add_apply, add_zero] using tendsto_const_nhds.add (hlim a b)
  obtain ⟨N, hN⟩ := (eventually_le_hermNegIndex (gram_isHermitian hh g) hconv).exists
  exact (Nat.cast_le.mpr hN).trans (hindex N)

/-- Positive carriers of the same proper successor cannot differ by a polynomial-fibre kernel. -/
theorem positive_subgroup_carriers_polynomial_rigid (H : AddSubgroup ℚ) (hH : H ≠ ⊤)
    {p q : AffineGroupQ → ℂ} (hp : IsPosDefKernel p) (hq : IsPosDefKernel q)
    (hps : HasSubgroupSuccessor H p) (hqs : HasSubgroupSuccessor H q)
    (hpoly : HasPolynomialTranslationFibres (fun g => p g - q g)) : p = q := by
  have hh : IsHermKernel (fun g => p g - q g) := by
    intro g
    change p g⁻¹ - q g⁻¹ = (starRingEnd ℂ) (p g - q g)
    rw [hp.1, hq.1, map_sub]
  have he : (fun g => q g + (p g - q g)) = p := by
    funext g
    ring
  have hi := negIndex_add_positive_subgroup_polynomial H hH hq hqs hh hpoly
  rw [he, hp.negIndex_eq_zero] at hi
  have hpos : IsPosDefKernel (fun g => p g - q g) := (isPosDefKernel_iff hh).mpr hi.symm
  have hp1 : p 1 = 1 := hasSubgroupSuccessor_one hps
  have hq1 : q 1 = 1 := hasSubgroupSuccessor_one hqs
  funext g
  have hb := hpos.norm_le g
  change ‖p g - q g‖ ≤ (p 1 - q 1).re at hb
  rw [hp1, hq1, sub_self, Complex.zero_re] at hb
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))

/-- Properness is exactly the condition for universal polynomial-fibre index preservation. -/
theorem proper_subgroup_iff_polynomial_index_preservation (H : AddSubgroup ℚ) :
    H ≠ ⊤ ↔ ∀ p h : AffineGroupQ → ℂ,
      IsPosDefKernel p → HasSubgroupSuccessor H p → IsHermKernel h →
      HasPolynomialTranslationFibres h → negIndex (fun g => p g + h g) = negIndex h := by
  constructor
  · intro hH p h hp hs hh hpoly
    exact negIndex_add_positive_subgroup_polynomial H hH hp hs hh hpoly
  · intro hpres hH
    subst H
    have hs : HasSubgroupSuccessor ⊤ (fun _ : AffineGroupQ => (1 : ℂ)) := by
      intro b
      simp only [AddSubgroup.mem_top, if_true]
    have hh : IsHermKernel (fun _ : AffineGroupQ => (-1 : ℂ)) := by
      intro g
      simp only [map_neg, map_one]
    have hpoly : HasPolynomialTranslationFibres (fun _ : AffineGroupQ => (-1 : ℂ)) := by
      intro u
      exact ⟨Polynomial.C (-1), fun _ => (Polynomial.eval_C).symm⟩
    have hz : negIndex (fun _ : AffineGroupQ => (0 : ℂ)) = 0 := by
      apply negIndex_eq_zero_iff.mpr
      intro n x c
      simp only [hermQuad_gram, mul_zero, zero_mul, Finset.sum_const_zero, Complex.zero_re,
        le_refl]
    have he := hpres (fun _ => 1) (fun _ => -1) positive_constant_one hs hh hpoly
    simp only [add_neg_cancel] at he
    rw [hz] at he
    have hneg := (negIndex_eq_zero_iff.mp he.symm) 1 (fun _ => (1 : AffineGroupQ))
      (fun _ => (1 : ℂ))
    norm_num [hermQuad_gram] at hneg

#print axioms exists_subgroup_quadrature_scale
#print axioms negIndex_add_positive_subgroup_polynomial
#print axioms positive_subgroup_carriers_polynomial_rigid
#print axioms proper_subgroup_iff_polynomial_index_preservation
end GaloisForLFunctions.AdelicKreinGeometry
