import GaloisForLFunctions.RHTower.XiGaussianHeatHankelDeterminants
import GaloisForLFunctions.HTGeometry.HermitianInertia

/-!
# Finite sections of the heat Hankel form: inertia and the sign of the determinants

Let `Δ_N(a) = det (M_{i+j}(a))_{i,j<N}` be the heat Hankel determinants and `U` the set of
off-line heat frequencies in the upper half-plane (one per off-line zero quadruple).

* The negative inertia of the `N`-th section never exceeds `#U`
  (`hermNegIndex_heatMomentSection_le`).
* It equals `#U` for all large `N` when `U` is finite
  (`exists_hermNegIndex_heatMomentSection_eq`), and it is unbounded when `U` is infinite
  (`exists_le_hermNegIndex_heatMomentSection_of_infinite`).
* **Sign law.**  If `U` is finite then `(−1)^{#U} Δ_N(a) ≥ 0` for all large `N`
  (`exists_neg_one_pow_card_mul_heatMomentDet_nonneg`).  The sign of the large determinants
  therefore reads the parity of the number of off-line quadruples.
* **Parity corollary.**  If `Δ_N(a) > 0` for infinitely many `N`, then a finite `U` has even
  cardinality (`even_card_of_frequently_heatMomentDet_pos`).

The sections are compressions of the heat Hankel form to polynomials of degree `< N`.  So their
negative-definite subspaces map injectively into negative-definite subspaces of polynomials, which
gives the upper bound.  A finite-dimensional negative subspace of polynomials has bounded degree,
so its coefficient vectors give the lower bound.  The sign follows from the product of the
eigenvalues.
-/

open Complex Filter Topology Set Polynomial Matrix
open GaloisForLFunctions.HTGeometry (leadingMatrix hermQuad hermQuad_neg IsPosDefOn hermPosIndex
  hermNegIndex exists_isPosDefOn_finrank_eq_posIndex finrank_le_posIndex
  negIndex_eq_card_neg_eigenvalues)

namespace RHTower

noncomputable section

/-! ## The sections as Hermitian matrices -/

/-- The `N`-th heat moment section `(M_{i+j}(a))_{i,j<N}` as a complex Hermitian matrix. -/
def heatMomentSection (a : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  (leadingMatrix (heatMomentArray a) N).map fun r : ℝ => (r : ℂ)

theorem isHermitian_heatMomentSection (a : ℝ) (N : ℕ) : (heatMomentSection a N).IsHermitian := by
  ext i j
  simp [heatMomentSection, leadingMatrix, conjTranspose_apply, heatMomentArray_symm]

theorem det_heatMomentSection (a : ℝ) (N : ℕ) :
    (heatMomentSection a N).det = ((leadingMatrix (heatMomentArray a) N).det : ℂ) :=
  (RingHom.map_det Complex.ofRealHom _).symm

/-- The polynomial `Σ_{i<N} x_i X^i` with coefficient vector `x`. -/
def heatCoeffPoly {N : ℕ} (x : Fin N → ℂ) : ℂ[X] := ∑ i : Fin N, C (x i) * X ^ (i : ℕ)

theorem coeff_heatCoeffPoly {N : ℕ} (x : Fin N → ℂ) (k : ℕ) :
    (heatCoeffPoly x).coeff k = if h : k < N then x ⟨k, h⟩ else 0 := by
  rw [heatCoeffPoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨k, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hk
      exact hb (Fin.ext hk.symm)
    · intro hk; exact absurd (Finset.mem_univ _) hk
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    intro hk
    exact h (hk ▸ i.2)

theorem natDegree_heatCoeffPoly_lt {N : ℕ} (hN : 0 < N) (x : Fin N → ℂ) :
    (heatCoeffPoly x).natDegree < N := by
  by_cases hP0 : heatCoeffPoly x = 0
  · rw [hP0, natDegree_zero]; exact hN
  · rw [natDegree_lt_iff_degree_lt hP0, degree_lt_iff_coeff_zero]
    intro m hm
    rw [coeff_heatCoeffPoly, dif_neg (by omega)]

/-- The coefficient-vector embedding of `ℂ^N` into polynomials of degree `< N`. -/
def heatCoeffPolyMap (N : ℕ) : (Fin N → ℂ) →ₗ[ℂ] ℂ[X] where
  toFun := heatCoeffPoly
  map_add' x y := by
    ext k
    simp only [coeff_add, coeff_heatCoeffPoly]
    split_ifs <;> simp
  map_smul' c x := by
    ext k
    simp only [coeff_smul, coeff_heatCoeffPoly, RingHom.id_apply]
    split_ifs <;> simp

theorem heatCoeffPolyMap_apply {N : ℕ} (x : Fin N → ℂ) : heatCoeffPolyMap N x = heatCoeffPoly x :=
  rfl

theorem heatCoeffPolyMap_injective (N : ℕ) : Function.Injective (heatCoeffPolyMap N) := by
  intro x y h
  funext i
  have := congrArg (fun P : ℂ[X] => P.coeff i) h
  simpa [heatCoeffPolyMap_apply, coeff_heatCoeffPoly, i.2] using this

/-- The Hermitian form of the `N`-th section is the heat Hankel form of the polynomial with that
coefficient vector. -/
theorem hermQuad_heatMomentSection {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : 0 < N) (x : Fin N → ℂ) :
    hermQuad (heatMomentSection a N) x =
      (heatHankel a (heatCoeffPoly x) (heatCoeffPoly x)).re := by
  rw [re_heatHankel_eq_quadratic ha _ (natDegree_heatCoeffPoly_lt hN x)]
  simp only [coeff_heatCoeffPoly, Fin.is_lt, dif_pos, Fin.eta]
  simp only [hermQuad, dotProduct, mulVec, heatMomentSection, leadingMatrix, map_apply, of_apply,
    Finset.mul_sum, re_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.star_apply, RCLike.star_def, mul_re, mul_im, conj_re, conj_im, ofReal_re,
    ofReal_im]
  ring

/-! ## Inertia of the sections -/

/-- **Upper bound.**  Every section has negative inertia at most `#U`. -/
theorem hermNegIndex_heatMomentSection_le {a : ℝ} (ha : 0 < a) (hU : xiUpperFrequencies.Finite)
    (N : ℕ) : hermNegIndex (heatMomentSection a N) ≤ hU.toFinset.card := by
  obtain ⟨W, hW, hpos⟩ := exists_isPosDefOn_finrank_eq_posIndex (-heatMomentSection a N)
  rw [hermNegIndex, ← hW]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h := Submodule.finrank_le W
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega
  set Φ := (heatCoeffPolyMap N).comp W.subtype with hΦ
  have hinj : Function.Injective Φ :=
    (heatCoeffPolyMap_injective N).comp Subtype.val_injective
  rw [← LinearMap.finrank_range_of_inj hinj]
  refine finrank_le_of_heatHankel_neg ha hU _ fun P hP hP0 => ?_
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hP
  have hy0 : (y : Fin N → ℂ) ≠ 0 := by
    intro h
    apply hP0
    rw [hΦ, LinearMap.comp_apply, Submodule.subtype_apply, h, map_zero]
  have h := hpos y y.2 hy0
  rw [hermQuad_neg, hermQuad_heatMomentSection ha hN] at h
  simpa [hΦ, heatCoeffPolyMap_apply] using neg_pos.1 h

/-- **Lower bound.**  A finite-dimensional negative subspace of polynomials is seen by every
section of large order. -/
theorem exists_le_hermNegIndex_heatMomentSection {a : ℝ} (ha : 0 < a) (V : Submodule ℂ ℂ[X])
    [FiniteDimensional ℂ V] (hV : ∀ P ∈ V, P ≠ 0 → (heatHankel a P P).re < 0) :
    ∃ N₀, ∀ N ≥ N₀, Module.finrank ℂ V ≤ hermNegIndex (heatMomentSection a N) := by
  classical
  obtain ⟨S, hS⟩ := (Submodule.fg_iff_finiteDimensional V).2 inferInstance
  refine ⟨S.sup natDegree + 1, fun N hN => ?_⟩
  have hNpos : 0 < N := by omega
  have hdeg : ∀ P ∈ V, P.natDegree < N := by
    have hle : V ≤ degreeLT ℂ (S.sup natDegree + 1) := by
      rw [← hS, Submodule.span_le]
      intro P hP
      rw [SetLike.mem_coe, mem_degreeLT]
      exact lt_of_le_of_lt (degree_le_natDegree.trans
        (WithBot.coe_le_coe.2 (Finset.le_sup (f := natDegree) hP)))
        (WithBot.coe_lt_coe.2 (Nat.lt_succ_self _))
    intro P hP
    have hm := mem_degreeLT.1 (hle hP)
    by_cases hP0 : P = 0
    · rw [hP0, natDegree_zero]; exact hNpos
    · rw [degree_eq_natDegree hP0] at hm
      have : P.natDegree < S.sup natDegree + 1 := by exact_mod_cast hm
      omega
  have hpoly : ∀ P ∈ V, heatCoeffPoly (fun i : Fin N => P.coeff i) = P := by
    intro P hP
    ext k
    rw [coeff_heatCoeffPoly]
    split_ifs with h
    · rfl
    · exact (coeff_eq_zero_of_natDegree_lt (by have := hdeg P hP; omega)).symm
  set κ : ℂ[X] →ₗ[ℂ] (Fin N → ℂ) := LinearMap.pi fun i : Fin N => Polynomial.lcoeff ℂ i with hκ
  set Ψ := κ.comp V.subtype with hΨ
  have hΨapp : ∀ P : V, Ψ P = fun i : Fin N => (P : ℂ[X]).coeff i := fun _ => rfl
  have hinj : Function.Injective Ψ := by
    intro P Q h
    apply Subtype.ext
    have := congrArg heatCoeffPoly h
    rwa [hΨapp, hΨapp, hpoly P P.2, hpoly Q Q.2] at this
  rw [← LinearMap.finrank_range_of_inj hinj, hermNegIndex]
  refine finrank_le_posIndex fun y hy hy0 => ?_
  obtain ⟨P, rfl⟩ := LinearMap.mem_range.1 hy
  rw [hermQuad_neg, hermQuad_heatMomentSection ha hNpos, hΨapp, hpoly P P.2]
  have hP0 : (P : ℂ[X]) ≠ 0 := by
    intro h
    apply hy0
    rw [show P = 0 from Subtype.ext h, map_zero]
  linarith [hV P P.2 hP0]

/-- **Stabilization.**  If there are finitely many off-line quadruples, every section of large
order has negative inertia exactly `#U`. -/
theorem exists_hermNegIndex_heatMomentSection_eq {a : ℝ} (ha : 0 < a)
    (hU : xiUpperFrequencies.Finite) :
    ∃ N₀, ∀ N ≥ N₀, hermNegIndex (heatMomentSection a N) = hU.toFinset.card := by
  rcases Nat.eq_zero_or_pos hU.toFinset.card with h0 | hpos
  · exact ⟨0, fun N _ => by have := hermNegIndex_heatMomentSection_le ha hU N; omega⟩
  obtain ⟨V, hVr, hVneg⟩ := exists_heatHankel_negative_subspace ha hU.toFinset
    fun u hu => hU.mem_toFinset.1 hu
  haveI : FiniteDimensional ℂ V := Module.finite_of_finrank_pos (hVr ▸ hpos)
  obtain ⟨N₀, hN₀⟩ := exists_le_hermNegIndex_heatMomentSection ha V hVneg
  exact ⟨N₀, fun N hN => le_antisymm (hermNegIndex_heatMomentSection_le ha hU N)
    (hVr ▸ hN₀ N hN)⟩

/-- With infinitely many off-line quadruples, the negative inertia of the sections is unbounded. -/
theorem exists_le_hermNegIndex_heatMomentSection_of_infinite {a : ℝ} (ha : 0 < a)
    (hU : xiUpperFrequencies.Infinite) (n : ℕ) :
    ∃ N₀, ∀ N ≥ N₀, n ≤ hermNegIndex (heatMomentSection a N) := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact ⟨0, fun _ _ => Nat.zero_le _⟩
  obtain ⟨V, hVr, hVneg⟩ := heatHankel_negative_subspace_of_infinite ha hU n
  haveI : FiniteDimensional ℂ V := Module.finite_of_finrank_pos (hVr ▸ hpos)
  obtain ⟨N₀, hN₀⟩ := exists_le_hermNegIndex_heatMomentSection ha V hVneg
  exact ⟨N₀, fun N hN => hVr ▸ hN₀ N hN⟩

/-! ## The sign law -/

/-- A product of reals, `m` of them negative, has sign `(−1)^m`. -/
theorem neg_one_pow_card_neg_mul_prod_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → ℝ) : 0 ≤ (-1 : ℝ) ^ ({i | μ i < 0} : Finset ι).card * ∏ i, μ i := by
  have hsplit : ∀ i, μ i = (if μ i < 0 then (-1 : ℝ) else 1) * |μ i| := fun i => by
    split_ifs with h
    · rw [abs_of_neg h]; ring
    · rw [abs_of_nonneg (not_lt.1 h), one_mul]
  have hprod : ∏ i, μ i = (-1 : ℝ) ^ ({i | μ i < 0} : Finset ι).card * ∏ i, |μ i| := by
    rw [Finset.prod_congr rfl fun i _ => hsplit i, Finset.prod_mul_distrib, Finset.prod_ite,
      Finset.prod_const_one, mul_one, Finset.prod_const]
  rw [hprod, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  exact Finset.prod_nonneg fun i _ => abs_nonneg _

/-- The determinant of a Hermitian matrix is real with sign `(−1)^{negative inertia}`. -/
theorem neg_one_pow_negIndex_mul_det_re_nonneg {N : ℕ} {H : Matrix (Fin N) (Fin N) ℂ}
    (hH : H.IsHermitian) : 0 ≤ (-1 : ℝ) ^ hermNegIndex H * H.det.re := by
  rw [negIndex_eq_card_neg_eigenvalues hH, hH.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
  exact neg_one_pow_card_neg_mul_prod_nonneg _

/-- **Sign law for the heat Hankel determinants.**  If the zeta function has finitely many
off-line zero quadruples, then `(−1)^{#U} Δ_N(a) ≥ 0` for every large `N`. -/
theorem exists_neg_one_pow_card_mul_heatMomentDet_nonneg {a : ℝ} (ha : 0 < a)
    (hU : xiUpperFrequencies.Finite) :
    ∃ N₀, ∀ N ≥ N₀,
      0 ≤ (-1 : ℝ) ^ hU.toFinset.card * (leadingMatrix (heatMomentArray a) N).det := by
  obtain ⟨N₀, hN₀⟩ := exists_hermNegIndex_heatMomentSection_eq ha hU
  refine ⟨N₀, fun N hN => ?_⟩
  have h := neg_one_pow_negIndex_mul_det_re_nonneg (isHermitian_heatMomentSection a N)
  rwa [hN₀ N hN, det_heatMomentSection, ofReal_re] at h

/-- **Parity corollary.**  If infinitely many heat Hankel determinants at one heat time are positive,
then a finite set of off-line zero quadruples has even cardinality. -/
theorem even_card_of_frequently_heatMomentDet_pos {a : ℝ} (ha : 0 < a)
    (hpos : ∃ᶠ N in atTop, 0 < (leadingMatrix (heatMomentArray a) N).det)
    (hU : xiUpperFrequencies.Finite) : Even hU.toFinset.card := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨N₀, hN₀⟩ := exists_neg_one_pow_card_mul_heatMomentDet_nonneg ha hU
  obtain ⟨N, hdet, hN⟩ := (hpos.and_eventually (eventually_ge_atTop N₀)).exists
  have h := hN₀ N hN
  rw [hodd.neg_one_pow] at h
  linarith

end

end RHTower
