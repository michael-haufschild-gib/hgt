import GaloisForLFunctions.AdelicKreinGeometry.Haar.IndexPreservation
import GaloisForLFunctions.BiarithmeticGeometry.Affine.PolynomialFibres
import GaloisForLFunctions.BiarithmeticGeometry.Affine.TranslationQuadrature
import GaloisForLFunctions.HeckeKreinToeplitz.Index.WeightedGrams
import GaloisForLFunctions.HeckeKreinToeplitz.FiniteIndexIsPositiveMinusFiniteRank

/-!
# Haar addition preserves the index of polynomial translation fibres

Signed translation quadrature reproduces every polynomial Gram entry while its positive
Haar Gram tends to zero. Thus a positive Haar summand leaves the entire residual index unchanged.
-/

open Complex Polynomial Finset Filter Topology Matrix
open scoped ComplexConjugate Classical
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.BiarithmeticGeometry
open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

private theorem slope_translation (b : ℚ) : slopeUnit (translation b) = 1 :=
  Units.ext (affSlope_translation b)

private theorem slope_dilation (u : ℚˣ) : slopeUnit (dilation u) = u :=
  Units.ext (affSlope_dilation u)

/-- Translate two affine columns before taking their group quotient. -/
theorem translated_affine_quotient (g h : AffineGroupQ) (s t : ℚ) :
    (translation s * g)⁻¹ * (translation t * h) =
      translation ((affShift h - affShift g + t - s) / affSlope g) *
        dilation ((slopeUnit g)⁻¹ * slopeUnit h) := by
  calc
    _ = translation (affShift ((translation s * g)⁻¹ * (translation t * h))) *
        dilation (slopeUnit ((translation s * g)⁻¹ * (translation t * h))) :=
      eq_translation_mul_dilation _
    _ = _ := by
      congr 1
      · congr 1
        simp only [affShift_mul, affShift_inv, affSlope_mul, affSlope_inv,
          affShift_translation, affSlope_translation, one_mul, div_eq_mul_inv]
        ring
      · congr 1
        simp only [map_mul, map_inv, slope_translation, one_mul]

private theorem den_ne_one_of_small_nonzero {q : ℚ} (hq : q ≠ 0) (hsmall : |q| < 1) :
    q.den ≠ 1 := by
  intro hd
  obtain ⟨m, rfl⟩ := (den_eq_one_iff_exists q).mp hd
  have hmlo : (-1 : ℤ) < m := by exact_mod_cast (abs_lt.mp hsmall).1
  have hmhi : m < (1 : ℤ) := by exact_mod_cast (abs_lt.mp hsmall).2
  have hm : m = 0 := by omega
  exact hq (by rw [hm, Int.cast_zero])

/-- The finite affine family obtained by translating each original column along the same grid. -/
def quadratureTranslatedFamily {ι : Type*} (g : ι → AffineGroupQ)
    (ε : ℚ) (n N : ℕ) : ι × (Fin n × Fin N) → AffineGroupQ :=
  fun z => translation (quadratureTranslationNode ε z.2.1 z.2.2.val) * g z.1

private theorem quadratureTranslatedFamily_pairing {ι : Type*} {p : AffineGroupQ → ℂ}
    (hs : HasIntegerSuccessor p) (g : ι → AffineGroupQ) {ε : ℚ} (hε : 0 < ε)
    (hsmall : ∀ i, ε < |affSlope (g i)|) {n N : ℕ}
    (a : ι) (i j : Fin n × Fin N) :
    p ((quadratureTranslatedFamily g ε n N (a, i))⁻¹ *
      quadratureTranslatedFamily g ε n N (a, j)) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    rw [inv_mul_cancel, hasIntegerSuccessor_one hs, if_pos rfl]
  · have hnodes : quadratureTranslationNode ε i.1 i.2.val ≠
        quadratureTranslationNode ε j.1 j.2.val := by
      intro he
      have h := @quadratureTranslationNode_injective n ε hε
        (i.1, i.2.val) (j.1, j.2.val) he
      exact hij (Prod.ext (congrArg (fun z : Fin n × ℕ => z.1) h)
        (Fin.ext (congrArg (fun z : Fin n × ℕ => z.2) h)))
    have hi := quadratureTranslationNode_pos_lt hε i.1 i.2.val
    have hj := quadratureTranslationNode_pos_lt hε j.1 j.2.val
    have hdiff : |quadratureTranslationNode ε j.1 j.2.val -
        quadratureTranslationNode ε i.1 i.2.val| < ε := by
      apply abs_lt.mpr
      constructor <;> linarith only [hi.1, hi.2, hj.1, hj.2]
    have hquot : |(quadratureTranslationNode ε j.1 j.2.val -
        quadratureTranslationNode ε i.1 i.2.val) / affSlope (g a)| < 1 := by
      rw [abs_div]
      apply (div_lt_iff₀ (abs_pos.mpr (affSlope_ne_zero (g a)))).mpr
      simpa only [one_mul] using hdiff.trans (hsmall a)
    have hden := den_ne_one_of_small_nonzero
      (div_ne_zero (sub_ne_zero.mpr hnodes.symm) (affSlope_ne_zero (g a))) hquot
    simp only [quadratureTranslatedFamily, translated_affine_quotient,
      sub_self, zero_add, inv_mul_cancel, map_one, mul_one]
    rw [hs, if_neg hden, if_neg hij]

private theorem weightedQuadrature_positive_diagonal {ι : Type*} [Fintype ι]
    {p : AffineGroupQ → ℂ} (hs : HasIntegerSuccessor p) (g : ι → AffineGroupQ)
    {ε : ℚ} (hε : 0 < ε) (hsmall : ∀ i, ε < |affSlope (g i)|)
    {n N : ℕ} (hN : 0 < N) (a : ι) :
    weightedKernelGram p (quadratureTranslatedFamily g ε n N)
      (translationQuadratureWeight n N) a a =
      (((∑ i : Fin n, normSq (originQuadratureWeight n i)) / (N : ℝ) : ℝ) : ℂ) := by
  rw [weightedKernelGram_diagonal_of_orthonormal _ _ _ a
    (fun i j => by
      by_cases hij : i = j
      · simpa only [if_pos hij] using
          quadratureTranslatedFamily_pairing hs g hε hsmall (n := n) (N := N) a i j
      · simpa only [if_neg hij] using
          quadratureTranslatedFamily_pairing hs g hε hsmall (n := n) (N := N) a i j),
    sum_normSq_translationQuadratureWeight hN]

private theorem weightedQuadrature_polynomial_entry {ι : Type*} [Fintype ι]
    (h : AffineGroupQ → ℂ) (g : ι → AffineGroupQ) (ε : ℚ) {n N : ℕ} (hN : 0 < N)
    (a b : ι) (P : ℂ[X]) (hPdeg : P.natDegree < n)
    (hP : ∀ t : ℚ, h (translation t * dilation ((slopeUnit (g a))⁻¹ * slopeUnit (g b))) =
      P.eval (t : ℂ)) :
    weightedKernelGram h (quadratureTranslatedFamily g ε n N)
      (translationQuadratureWeight n N) a b = h ((g a)⁻¹ * g b) := by
  let A : ℂ := ((affSlope (g a) : ℚ) : ℂ)⁻¹
  let B : ℂ := (((affShift (g b) - affShift (g a)) / affSlope (g a) : ℚ) : ℂ)
  let w := translationQuadratureWeight n N
  let node : Fin n × Fin N → ℂ := fun j => (quadratureTranslationNode ε j.1 j.2.val : ℂ)
  have hentry (i j : Fin n × Fin N) :
      h ((quadratureTranslatedFamily g ε n N (a, i))⁻¹ *
        quadratureTranslatedFamily g ε n N (b, j)) =
          P.eval (A * node j + (-A * node i + B)) := by
    rw [quadratureTranslatedFamily, quadratureTranslatedFamily, translated_affine_quotient, hP]
    congr 1
    simp only [A, B, node, Rat.cast_div, Rat.cast_sub, Rat.cast_add]
    ring
  have hrow (i : Fin n × Fin N) :
      (∑ j, w j * h ((quadratureTranslatedFamily g ε n N (a, i))⁻¹ *
        quadratureTranslatedFamily g ε n N (b, j))) = P.eval (-A * node i + B) := by
    simp only [hentry]
    exact translationQuadrature_eval hN ε P hPdeg A (-A * node i + B)
  rw [weightedKernelGram_apply]
  simp only [conj_translationQuadratureWeight]
  change (∑ i, ∑ j, w i * w j * h ((quadratureTranslatedFamily g ε n N (a, i))⁻¹ *
    quadratureTranslatedFamily g ε n N (b, j))) = _
  calc
    _ = ∑ i, w i * ∑ j, w j * h ((quadratureTranslatedFamily g ε n N (a, i))⁻¹ *
        quadratureTranslatedFamily g ε n N (b, j)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i, w i * P.eval (-A * node i + B) := by simp only [hrow]
    _ = P.eval B := translationQuadrature_eval hN ε P hPdeg (-A) B
    _ = h ((g a)⁻¹ * g b) := by
      have he := translated_affine_quotient (g a) (g b) 0 0
      simp only [translation_zero, one_mul, add_zero, sub_zero] at he
      rw [he, hP]

/-- A single quadrature order reproduces every entry of a fixed finite polynomial-fibre Gram. -/
theorem exists_polynomial_gram_quadrature_order {ι : Type*} [Fintype ι]
    {h : AffineGroupQ → ℂ} (hpoly : HasPolynomialTranslationFibres h)
    (g : ι → AffineGroupQ) :
    ∃ n : ℕ, 0 < n ∧ ∀ (ε : ℚ) (N : ℕ), 0 < N →
      weightedKernelGram h (quadratureTranslatedFamily g ε n N)
        (translationQuadratureWeight n N) = HeckeKreinToeplitz.gram h g := by
  choose P hP using fun a b => hpoly ((slopeUnit (g a))⁻¹ * slopeUnit (g b))
  let M := ∑ a, ∑ b, (P a b).natDegree
  have hdeg (a b : ι) : (P a b).natDegree < M + 1 := by
    have hb := Finset.single_le_sum (f := fun b => (P a b).natDegree)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
    have ha := Finset.single_le_sum (f := fun a => ∑ b, (P a b).natDegree)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    exact Nat.lt_succ_of_le (hb.trans ha)
  refine ⟨M + 1, Nat.succ_pos M, ?_⟩
  intro ε N hN
  ext a b
  exact weightedQuadrature_polynomial_entry h g ε hN a b (P a b) (hdeg a b) (hP a b)

/-- Adding a positive Haar kernel preserves the full index of every polynomial-fibre kernel. -/
theorem negIndex_add_positive_haar_polynomial {p h : AffineGroupQ → ℂ}
    (hp : IsPosDefKernel p) (hs : HasIntegerSuccessor p)
    (hh : IsHermKernel h) (hpoly : HasPolynomialTranslationFibres h) :
    negIndex (fun g => p g + h g) = negIndex h := by
  apply le_antisymm (negIndex_add_posDef_le hp)
  apply negIndex_le_iff.mpr
  intro m g
  obtain ⟨n, hn, hquad⟩ := exists_polynomial_gram_quadrature_order hpoly g
  obtain ⟨ε, hε, hsmall⟩ := exists_positive_lt_abs_slopes
    (fun i => affSlope (g i)) (fun i => affSlope_ne_zero (g i))
  let C : ℝ := ∑ i : Fin n, normSq (originQuadratureWeight n i)
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => normSq_nonneg _
  let P : ℕ → Matrix (Fin m) (Fin m) ℂ := fun N =>
    weightedKernelGram p (quadratureTranslatedFamily g ε n (N + 1))
      (translationQuadratureWeight n (N + 1))
  have hbound (N : ℕ) (a b : Fin m) : ‖P N a b‖ ≤ C / (N + 1 : ℕ) := by
    apply norm_entry_le_constant_posSemidef_diagonal
      (weightedKernelGram_posSemidef hp _ _) (div_nonneg hC (Nat.cast_nonneg _))
    intro i
    exact weightedQuadrature_positive_diagonal hs g hε hsmall (Nat.succ_pos N) i
  have hindex (N : ℕ) : (hermNegIndex (HeckeKreinToeplitz.gram h g + P N) : ℕ∞) ≤
      negIndex (fun u => p u + h u) := by
    have he : weightedKernelGram (fun u => p u + h u)
        (quadratureTranslatedFamily g ε n (N + 1)) (translationQuadratureWeight n (N + 1)) =
          HeckeKreinToeplitz.gram h g + P N := by
      rw [weightedKernelGram_add, hquad ε (N + 1) (Nat.succ_pos N)]
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
  have hconv (a b : Fin m) : Tendsto (fun N => (HeckeKreinToeplitz.gram h g + P N) a b) atTop (𝓝 (HeckeKreinToeplitz.gram h g a b)) := by
    simpa only [Matrix.add_apply, add_zero] using tendsto_const_nhds.add (hlim a b)
  obtain ⟨N, hN⟩ := (eventually_le_hermNegIndex (gram_isHermitian hh g) hconv).exists
  exact (Nat.cast_le.mpr hN).trans (hindex N)

/-- A positive Haar summand leaves exactly the joint slope-and-polynomial index. -/
theorem negIndex_positive_haar_slope_polynomial_eq {p q : AffineGroupQ → ℂ} {ψ : ℚˣ → ℂ}
    (hp : IsPosDefKernel p) (hs : HasIntegerSuccessor p) (hψ : IsHermKernel ψ)
    (hq : IsHermKernel q) (hpoly : HasPolynomialTranslationFibres q) :
    negIndex (fun g => p g + ψ (slopeUnit g) + q g) =
      negIndex (fun g => ψ (slopeUnit g) + q g) := by
  have hh : IsHermKernel (fun g => ψ (slopeUnit g) + q g) := by
    intro g
    change ψ (slopeUnit g⁻¹) + q g⁻¹ = starRingEnd ℂ (ψ (slopeUnit g) + q g)
    rw [map_inv, hψ, hq, map_add]
  have hpoly' : HasPolynomialTranslationFibres (fun g => ψ (slopeUnit g) + q g) := by
    intro u
    obtain ⟨P, hP⟩ := hpoly u
    refine ⟨C (ψ u) + P, ?_⟩
    intro b
    change ψ (slopeUnit (translation b * dilation u)) + q (translation b * dilation u) = _
    rw [map_mul, slope_translation, slope_dilation, one_mul, hP, eval_add, eval_C]
  simpa only [add_assoc] using negIndex_add_positive_haar_polynomial hp hs hh hpoly'

/-- Subadditivity bounds the relative index by the slope and polynomial indices. -/
theorem negIndex_positive_haar_slope_polynomial_le {p q : AffineGroupQ → ℂ} {ψ : ℚˣ → ℂ}
    (hp : IsPosDefKernel p) (hs : HasIntegerSuccessor p) (hψ : IsHermKernel ψ)
    (hq : IsHermKernel q) (hpoly : HasPolynomialTranslationFibres q) :
    negIndex (fun g => p g + ψ (slopeUnit g) + q g) ≤ negIndex ψ + negIndex q := by
  rw [negIndex_positive_haar_slope_polynomial_eq hp hs hψ hq hpoly]
  have hsum : negIndex (fun g => ψ (slopeUnit g) + q g) ≤
      negIndex (ψ ∘ slopeUnit) + negIndex q :=
    negIndex_add_le (k₁ := ψ ∘ slopeUnit) (k₂ := q) (hψ.comp slopeUnit) hq
  exact hsum.trans (_root_.add_le_add (negIndex_comp_le ψ slopeUnit) le_rfl)

/-- Zero dilation values make the slope index a lower bound even in the presence of polynomial corrections. -/
theorem negIndex_slope_le_positive_haar_polynomial {p q : AffineGroupQ → ℂ} {ψ : ℚˣ → ℂ}
    (hp : IsPosDefKernel p) (hs : HasIntegerSuccessor p) (hψ : IsHermKernel ψ)
    (hq : IsHermKernel q) (hpoly : HasPolynomialTranslationFibres q)
    (hd : ∀ u : ℚˣ, q (dilation u) = 0) :
    negIndex ψ ≤ negIndex (fun g => p g + ψ (slopeUnit g) + q g) := by
  rw [negIndex_positive_haar_slope_polynomial_eq hp hs hψ hq hpoly]
  have he : (fun g => ψ (slopeUnit g) + q g) ∘ dilation = ψ := by
    funext u
    change ψ (slopeUnit (dilation u)) + q (dilation u) = ψ u
    rw [slope_dilation, hd, add_zero]
  have hi := negIndex_comp_le (fun g => ψ (slopeUnit g) + q g) dilation
  rwa [he] at hi

#print axioms negIndex_add_positive_haar_polynomial
#print axioms negIndex_positive_haar_slope_polynomial_eq
#print axioms negIndex_positive_haar_slope_polynomial_le
#print axioms negIndex_slope_le_positive_haar_polynomial
end GaloisForLFunctions.AdelicKreinGeometry
