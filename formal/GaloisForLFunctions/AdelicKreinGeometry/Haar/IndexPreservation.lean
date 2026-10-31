import GaloisForLFunctions.AdelicKreinGeometry.ThePontryaginExtensionsOfWeilsCorrelation
import GaloisForLFunctions.HeckeKreinToeplitz.BoundedIndexIsClosedUnderPointwiseLimits
import GaloisForLFunctions.HTGeometry.ReductionPencilKPositivity

/-!
# Positive integer-successor carriers preserve slope index

For a positive affine kernel `p` with integer successor and a Hermitian kernel `ψ` on `ℚˣ`,
the affine kernel `g ↦ p g + ψ (slopeUnit g)` has exactly the negative index of `ψ`.
Haar addition is a special case.

Rational translates make each vector's averaged squared norm `1/N`. Semidefinite
Cauchy–Schwarz bounds the mixed pairings by `1/N`, so the averaged positive Gram matrix tends
to zero. The slope Gram matrix is unchanged, and lower semicontinuity of index gives the
reverse of the immediate positivity bound.
-/

open Complex Finset Filter Topology
open scoped ComplexConjugate ComplexOrder
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

/-- A prime denominator separates two finite families by a rational translation. -/
private theorem exists_translation_escape {φ : AffineGroupQ → ℂ}
    (hφ : IsHeckeSupported φ) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → AffineGroupQ) (y : κ → AffineGroupQ) :
    ∃ c : ℚ, ∀ a b, φ ((x a)⁻¹ * (translation c * y b)) = 0 := by
  let f : ι → κ → ℕ := fun a b => ((affSlope (x a))⁻¹ * affSlope (y b)).den +
    (affSlope (x a)).den + (affShift (y b) - affShift (x a)).den
  let bound : ℕ := ∑ a, ∑ b, f a b
  obtain ⟨P, hPge, hP⟩ := Nat.exists_infinite_primes (bound + 1)
  refine ⟨1 / P, fun a b => ?_⟩
  by_contra hne
  have h1 := hφ _ hne
  rw [affSlope_inv_mul_translation_mul, affShift_inv_mul_translation_mul] at h1
  have hfab : f a b ≤ bound :=
    (Finset.single_le_sum (f := fun b => f a b) (fun _ _ => Nat.zero_le _) (mem_univ b)).trans
      (Finset.single_le_sum (f := fun a => ∑ b, f a b) (fun _ _ => Nat.zero_le _) (mem_univ a))
  have hnd : ∀ v : ℕ, 0 < v → v ≤ f a b → ¬ P ∣ v := fun v hv hvb hdv => by
    have := Nat.le_of_dvd hv hdv
    omega
  exact den_ne_one_of_prime hP (affSlope_ne_zero _)
    (hnd _ (Rat.den_pos _) (by simp only [f]; omega))
    (hnd _ (Rat.den_pos _) (by simp only [f]; omega))
    (hnd _ (Rat.den_pos _) (by simp only [f]; omega)) h1

private theorem haar_supported : IsHeckeSupported haarState := by
  intro g hg
  by_contra h
  exact hg (by simp only [haarState, haarWeight, if_neg h, Complex.ofReal_zero])

private theorem haar_hermitian : IsHermKernel haarState :=
  (isPosDefKernel_iff_isPosDefOnGroup.mpr isPosDefOnGroup_haarState).1

/-- Every finite family has arbitrarily many mutually Haar-orthogonal translates. -/
private theorem exists_haar_orthogonal_copies {ι : Type*} [Fintype ι]
    (x : ι → AffineGroupQ) (N : ℕ) :
    ∃ t : Fin N → ℚ, ∀ i j, i ≠ j → ∀ a b,
      haarState ((translation (t i) * x a)⁻¹ * (translation (t j) * x b)) = 0 := by
  classical
  induction N with
  | zero => exact ⟨Fin.elim0, fun i => i.elim0⟩
  | succ N ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨c, hc⟩ := exists_translation_escape haar_supported
      (fun p : Fin N × ι => translation (t p.1) * x p.2) x
    refine ⟨Fin.cons c t, ?_⟩
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro h
        exact False.elim (h rfl)
      · intro _ a b
        change haarState ((translation c * x a)⁻¹ * (translation (t j) * x b)) = 0
        rw [show (translation c * x a)⁻¹ * (translation (t j) * x b) =
          ((translation (t j) * x b)⁻¹ * (translation c * x a))⁻¹ by group]
        rw [haar_hermitian, hc (j, b) a, map_zero]
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro _ a b
        exact hc (i, a) b
      · intro hij a b
        exact ht i j (fun h => hij (congrArg Fin.succ h)) a b

/-- Compress a Gram matrix by assigning the same weights to each block. -/
private def weightedGram {G ι J : Type*} [Group G] [Fintype J]
    (k : G → ℂ) (x : ι × J → G) (w : J → ℂ) : Matrix ι ι ℂ :=
  fun a b => ∑ i, ∑ j, conj (w i) * w j * k ((x (a, i))⁻¹ * x (b, j))

private theorem hermQuad_weightedGram {G ι J : Type*} [Group G] [Fintype ι] [Fintype J]
    (k : G → ℂ) (x : ι × J → G) (w : J → ℂ) (c : ι → ℂ) :
    hermQuad (weightedGram k x w) c =
      hermQuad (HeckeKreinToeplitz.gram k x) (fun p => c p.1 * w p.2) := by
  simp only [hermQuad, weightedGram, HeckeKreinToeplitz.gram, Matrix.mulVec, dotProduct,
    Pi.star_apply, Complex.star_def, mul_sum, sum_mul, Fintype.sum_prod_type]
  congr 1
  refine sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun b _ => sum_congr rfl fun j _ => ?_
  rw [map_mul]
  ring

private theorem hermNegIndex_weightedGram_le {G ι J : Type*} [Group G] [Fintype ι] [Fintype J]
    (k : G → ℂ) (x : ι × J → G) (w : J → ℂ) :
    (hermNegIndex (weightedGram k x w) : ℕ∞) ≤ negIndex k := by
  let L : (ι → ℂ) →ₗ[ℂ] (ι × J → ℂ) :=
    { toFun := fun c p => c p.1 * w p.2
      map_add' := fun c d => funext fun p => by simp only [Pi.add_apply, add_mul]
      map_smul' := fun z c => funext fun p => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc] }
  exact (Nat.cast_le.mpr (hermNegIndex_le_of_hermQuad_eq _ _ L
    (fun c => (hermQuad_weightedGram k x w c).symm))).trans
    (hermNegIndex_gram_le_negIndex k x)

private theorem slope_translation_eq_one (b : ℚ) : slopeUnit (translation b) = 1 :=
  Units.ext (affSlope_translation b)

private theorem slope_dilation_eq (u : ℚˣ) : slopeUnit (dilation u) = u :=
  Units.ext (affSlope_dilation u)

/-- Averaging a constant block and a diagonal block retains `A` and divides `P` by `N`. -/
private theorem mean_block_entry (N : ℕ) (hN : 0 < N) (A P : ℂ) :
    (∑ i : Fin N, ∑ j : Fin N, conj ((N : ℂ)⁻¹) * (N : ℂ)⁻¹ *
      ((if i = j then P else 0) + A)) = A + (N : ℂ)⁻¹ * P := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [map_inv₀, map_natCast, mul_add, mul_ite, mul_zero, sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

private theorem weightedGram_isHermitian {G ι J : Type*} [Group G] [Fintype J]
    {p : G → ℂ} (hp : IsHermKernel p) (x : ι × J → G) (w : J → ℂ) :
    (weightedGram p x w).IsHermitian := by
  ext a b
  change conj (∑ i, ∑ j, conj (w i) * w j * p ((x (b, i))⁻¹ * x (a, j))) = _
  simp only [map_sum, map_mul, conj_conj]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [← hp, mul_inv_rev, inv_inv]
  ring

private theorem weightedGram_posSemidef {G ι J : Type*} [Group G] [Fintype ι] [Fintype J]
    {p : G → ℂ} (hp : IsPosDefKernel p) (x : ι × J → G) (w : J → ℂ) :
    (weightedGram p x w).PosSemidef := by
  refine posSemidef_of_matSesq_re_nonneg (weightedGram_isHermitian hp.1 x w) fun c => ?_
  rw [matSesq_eq_dotProduct]
  change 0 ≤ hermQuad (weightedGram p x w) c
  rw [hermQuad_weightedGram]
  exact hp.hermQuad_nonneg x _

/-- A positive matrix with constant diagonal `δ` has every entry bounded in norm by `δ`. -/
private theorem norm_entry_le_constant_diagonal {ι : Type*} [Fintype ι]
    {P : Matrix ι ι ℂ} (hP : P.PosSemidef) {δ : ℝ} (hδ : 0 ≤ δ)
    (hd : ∀ a, P a a = (δ : ℂ)) (a b : ι) : ‖P a b‖ ≤ δ := by
  classical
  have he (i j : ι) : matSesq P (Pi.single j 1) (Pi.single i 1) = P i j := by
    simp [matSesq, Pi.single_apply]
  have h := matSesq_norm_sq_le hP (Pi.single b 1) (Pi.single a 1)
  rw [he, he, he, hd, hd, Complex.ofReal_re] at h
  nlinarith only [h, norm_nonneg (P a b), hδ]

private theorem translated_dilation_quotient (u : ℚˣ) (s t : ℚ) :
    (translation s * dilation u)⁻¹ * (translation t * dilation u) =
      translation ((t - s) / (u : ℚ)) := by
  apply affine_ext
  · simp only [affSlope_mul, affSlope_inv, affSlope_translation, affSlope_dilation,
      one_mul, inv_mul_cancel₀ u.ne_zero]
  · simp only [affShift_mul, affShift_inv, affShift_translation, affShift_dilation,
      affSlope_mul, affSlope_inv, affSlope_translation, affSlope_dilation,
      one_mul, mul_zero, div_eq_mul_inv]
    ring

/-- Translation averages compress the affine Gram matrix to its slope part plus a vanishing
positive matrix. Only the translation reading of the positive carrier is used. -/
private theorem exists_averaged_positive_error {p : AffineGroupQ → ℂ}
    (hp : IsPosDefKernel p) (hs : HasIntegerSuccessor p) (ψ : ℚˣ → ℂ) {n : ℕ}
    (u : Fin n → ℚˣ) (N : ℕ) (hN : 0 < N) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ,
      (∀ a b, ‖P a b‖ ≤ (N : ℝ)⁻¹) ∧
      (hermNegIndex (HeckeKreinToeplitz.gram ψ u + P) : ℕ∞) ≤
        negIndex (fun g => p g + ψ (slopeUnit g)) := by
  classical
  obtain ⟨t, ht⟩ := exists_haar_orthogonal_copies (fun a => dilation (u a)) N
  let y : Fin n × Fin N → AffineGroupQ :=
    fun q => translation (t q.2) * dilation (u q.1)
  let w : Fin N → ℂ := fun _ => (N : ℂ)⁻¹
  have hpair (a : Fin n) (i j : Fin N) :
      p ((y (a, i))⁻¹ * y (a, j)) = if i = j then 1 else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [inv_mul_cancel, hasIntegerSuccessor_one hs, ite_true]
    · rw [if_neg hij]
      change p ((translation (t i) * dilation (u a))⁻¹ *
        (translation (t j) * dilation (u a))) = 0
      rw [translated_dilation_quotient, hs, ← haarState_hasIntegerSuccessor,
        ← translated_dilation_quotient]
      exact ht i j hij a a
  have hd (a : Fin n) : weightedGram p y w a a = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by
    change (∑ i, ∑ j, conj ((N : ℂ)⁻¹) * (N : ℂ)⁻¹ *
      p ((y (a, i))⁻¹ * y (a, j))) = _
    simp only [hpair]
    have he := mean_block_entry N hN 0 1
    simpa only [add_zero, zero_add, mul_one, Complex.ofReal_inv, Complex.ofReal_natCast] using he
  refine ⟨weightedGram p y w,
    norm_entry_le_constant_diagonal (weightedGram_posSemidef hp y w) (by positivity) hd, ?_⟩
  have hmatrix : weightedGram (fun g => p g + ψ (slopeUnit g)) y w =
      HeckeKreinToeplitz.gram ψ u + weightedGram p y w := by
    ext a b
    simp only [weightedGram, y, w, map_mul, map_inv, slope_translation_eq_one,
      slope_dilation_eq, one_mul, mul_add, sum_add_distrib, Matrix.add_apply,
      HeckeKreinToeplitz.gram]
    have he := mean_block_entry N hN (ψ ((u a)⁻¹ * u b)) 0
    simp only [ite_self, zero_add, mul_zero, add_zero] at he
    rw [he, add_comm]
  rw [← hmatrix]
  exact hermNegIndex_weightedGram_le _ _ _

/-- A positive affine kernel with integer successor preserves the index of every slope correction. -/
theorem negIndex_add_slope_of_integer_successor {p : AffineGroupQ → ℂ}
    (hp : IsPosDefKernel p) (hs : HasIntegerSuccessor p)
    (ψ : ℚˣ → ℂ) (hψ : IsHermKernel ψ) :
    negIndex (fun g => p g + ψ (slopeUnit g)) = negIndex ψ := by
  apply le_antisymm
  · exact (negIndex_add_posDef_le (k := ψ ∘ slopeUnit) hp).trans (negIndex_comp_le ψ slopeUnit)
  · rw [negIndex_le_iff]
    intro n u
    choose P hP hindex using
      fun N : ℕ => exists_averaged_positive_error hp hs ψ u (N + 1) (Nat.succ_pos N)
    have hinv : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa only [Nat.cast_add, Nat.cast_one, one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hlim (a b : Fin n) : Tendsto (fun N => P N a b) atTop (𝓝 0) := by
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      filter_upwards [hinv.eventually (gt_mem_nhds hε)] with N hN
      simpa only [dist_zero_right] using (hP N a b).trans_lt hN
    have hconv (a b : Fin n) : Tendsto
        (fun N => (HeckeKreinToeplitz.gram ψ u + P N) a b) atTop
        (𝓝 ((HeckeKreinToeplitz.gram ψ u) a b)) := by
      simpa only [Matrix.add_apply, add_zero] using tendsto_const_nhds.add (hlim a b)
    obtain ⟨N, hN⟩ := (eventually_le_hermNegIndex (gram_isHermitian hψ u) hconv).exists
    exact (Nat.cast_le.mpr hN).trans (hindex N)

/-- Adding Haar to a slope kernel preserves its negative index, finite or infinite. -/
theorem negIndex_haar_add_slope (ψ : ℚˣ → ℂ) (hψ : IsHermKernel ψ) :
    negIndex (fun g => haarState g + ψ (slopeUnit g)) = negIndex ψ :=
  negIndex_add_slope_of_integer_successor
    (isPosDefKernel_iff_isPosDefOnGroup.mpr isPosDefOnGroup_haarState)
    haarState_hasIntegerSuccessor ψ hψ

end GaloisForLFunctions.AdelicKreinGeometry
