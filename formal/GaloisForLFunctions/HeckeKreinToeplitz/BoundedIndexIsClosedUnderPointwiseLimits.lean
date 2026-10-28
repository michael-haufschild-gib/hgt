import GaloisForLFunctions.HeckeKreinToeplitz.HyperbolicPairsAndTheIndexFormula

/-!
# Bounded index is closed under pointwise limits

The transfer theorem of the theory: the topology in which indefinite kernels of bounded index
form a closed set is pointwise convergence of kernels.

**Matrix level** (`eventually_le_hermNegIndex`). If `H_n → H` entrywise, then eventually
`hermNegIndex H ≤ hermNegIndex H_n`. A negative-definite subspace of `H` is parametrized by a
linear map `L` on `ℂ^m`; on the unit sphere of `ℂ^m` (compact) the form `−H∘L` has a positive
minimum `δ` and `‖L a‖ ≤ C`, so a perturbation with entrywise sum `< δ / C²` keeps it negative.

**Kernel level** (`negIndex_le_of_tendsto`). If `k_n → k` pointwise and eventually
`κ(k_n) ≤ m`, then `κ(k) ≤ m`: the negative index is lower semicontinuous. Atomic and truncated
families converge in this topology; the Weil form is not continuous on `L²` of tests, and that
topology does not carry index bounds.
-/

open Complex Matrix Finset Filter Topology Metric
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {ι : Type*} [Fintype ι]

theorem hermQuad_add (A B : Matrix ι ι ℂ) (x : ι → ℂ) :
    hermQuad (A + B) x = hermQuad A x + hermQuad B x := by
  simp only [hermQuad, Matrix.add_mulVec, dotProduct_add, Complex.add_re]

/-- The Hermitian form is bounded by the entrywise `ℓ¹` norm times the squared sup norm. -/
theorem abs_hermQuad_le (D : Matrix ι ι ℂ) (x : ι → ℂ) :
    |hermQuad D x| ≤ (∑ a, ∑ b, ‖D a b‖) * ‖x‖ ^ 2 := by
  rw [hermQuad, sq, sum_mul, ← Real.norm_eq_abs]
  refine (norm_re_le_norm _).trans ?_
  simp only [dotProduct, mulVec, Pi.star_apply]
  refine (norm_sum_le _ _).trans (sum_le_sum fun a _ => ?_)
  rw [mul_sum, sum_mul]
  refine (norm_mul_le _ _).trans ?_
  rw [norm_star]
  calc ‖x a‖ * ‖∑ b, D a b * x b‖ ≤ ‖x‖ * ∑ b, ‖D a b‖ * ‖x‖ := by
        gcongr
        · exact norm_le_pi_norm x a
        · refine (norm_sum_le _ _).trans (sum_le_sum fun b _ => ?_)
          rw [norm_mul]
          gcongr
          exact norm_le_pi_norm x b
    _ = ∑ b, ‖D a b‖ * ‖x‖ * ‖x‖ := by rw [mul_sum]; exact sum_congr rfl fun b _ => by ring

/-- A negative-definite subspace of maximal dimension, parametrized by `ℂ^m`. -/
theorem exists_linearMap_neg (H : Matrix ι ι ℂ) :
    ∃ L : (Fin (hermNegIndex H) → ℂ) →ₗ[ℂ] (ι → ℂ), ∀ a, a ≠ 0 → hermQuad H (L a) < 0 := by
  obtain ⟨W, hrank, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-H)
  have e : (Fin (hermNegIndex H) → ℂ) ≃ₗ[ℂ] W :=
    LinearEquiv.ofFinrankEq _ _ (by rw [Module.finrank_fin_fun, hrank]; rfl)
  refine ⟨W.subtype ∘ₗ e.toLinearMap, fun a ha => ?_⟩
  have hne : ((e a : W) : ι → ℂ) ≠ 0 := by
    intro h
    exact ha (e.injective (by rw [map_zero]; exact Subtype.ext h))
  have := hW _ (e a).2 hne
  rw [hermQuad_neg] at this
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe]
  linarith

/-- **Lower semicontinuity of the negative index for matrices.** -/
theorem eventually_le_hermNegIndex {β : Type*} {l : Filter β} {H : β → Matrix ι ι ℂ}
    {H₀ : Matrix ι ι ℂ} (hH : ∀ a b, Tendsto (fun n => H n a b) l (𝓝 (H₀ a b))) :
    ∀ᶠ n in l, hermNegIndex H₀ ≤ hermNegIndex (H n) := by
  obtain ⟨L, hL⟩ := exists_linearMap_neg H₀
  set m := hermNegIndex H₀
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exact Eventually.of_forall fun n => by rw [hm]; exact Nat.zero_le _
  set S : Set (Fin m → ℂ) := sphere 0 1
  have hS : IsCompact S := isCompact_sphere 0 1
  have hSne : S.Nonempty := by
    refine ⟨Pi.single ⟨0, hm⟩ 1, ?_⟩
    rw [mem_sphere_zero_iff_norm, Pi.norm_single, norm_one]
  have hLc : Continuous L := LinearMap.continuous_of_finiteDimensional L
  have hfc : Continuous fun a => hermQuad H₀ (L a) := by
    have : Continuous fun x : ι → ℂ => hermQuad H₀ x := by
      simp only [hermQuad, dotProduct, mulVec, Pi.star_apply]
      fun_prop
    exact this.comp hLc
  obtain ⟨a₀, ha₀S, ha₀⟩ := hS.exists_isMaxOn hSne hfc.continuousOn
  obtain ⟨a₁, -, ha₁⟩ := hS.exists_isMaxOn hSne (continuous_norm.comp hLc).continuousOn
  have ha₀ne : a₀ ≠ 0 := by
    rintro rfl
    rw [mem_sphere_zero_iff_norm, norm_zero] at ha₀S
    exact zero_ne_one ha₀S
  set δ := -hermQuad H₀ (L a₀)
  have hδ : 0 < δ := neg_pos.mpr (hL a₀ ha₀ne)
  set C := ‖L a₁‖
  have hsum : Tendsto (fun n => ∑ a, ∑ b, ‖H n a b - H₀ a b‖) l (𝓝 0) := by
    have := tendsto_finset_sum (univ : Finset ι) fun a _ =>
      tendsto_finset_sum (univ : Finset ι) fun b _ => ((hH a b).sub_const (H₀ a b)).norm
    simpa using this
  filter_upwards [hsum.eventually (gt_mem_nhds (div_pos hδ (by positivity : (0:ℝ) < C ^ 2 + 1)))]
    with n hn
  refine (Fintype.card_fin m).symm.le.trans (card_le_hermNegIndex_of_forall_neg _ L fun a ha => ?_)
  -- reduce to the unit sphere
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  set a' : Fin m → ℂ := ((‖a‖⁻¹ : ℝ) : ℂ) • a
  have ha'S : a' ∈ S := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hna), inv_mul_cancel₀ hna.ne']
  have haa' : a = ((‖a‖ : ℝ) : ℂ) • a' := by
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hna.ne', Complex.ofReal_one, one_smul]
  rw [haa', map_smul, ArithmeticCastelnuovoSeveri.hermQuad_smul]
  refine mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr (by exact_mod_cast hna.ne')) ?_
  have hsplit : H n = H₀ + (H n - H₀) := by abel
  rw [hsplit, hermQuad_add]
  have h1 : hermQuad H₀ (L a') ≤ -δ := by
    have := ha₀ ha'S
    simp only [δ, neg_neg]
    exact this
  have h2 : |hermQuad (H n - H₀) (L a')| ≤ (∑ a, ∑ b, ‖H n a b - H₀ a b‖) * C ^ 2 := by
    refine (abs_hermQuad_le _ _).trans ?_
    have hC : ‖L a'‖ ≤ C := ha₁ ha'S
    simp only [Matrix.sub_apply]
    gcongr
  have h3 : (∑ a, ∑ b, ‖H n a b - H₀ a b‖) * C ^ 2 < δ := by
    have hpos : 0 ≤ ∑ a, ∑ b, ‖H n a b - H₀ a b‖ :=
      sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _
    calc (∑ a, ∑ b, ‖H n a b - H₀ a b‖) * C ^ 2
        ≤ (∑ a, ∑ b, ‖H n a b - H₀ a b‖) * (C ^ 2 + 1) := by gcongr; linarith
      _ < δ / (C ^ 2 + 1) * (C ^ 2 + 1) := by gcongr
      _ = δ := div_mul_cancel₀ _ (by positivity)
  linarith [(abs_le.mp h2).2]

variable {G : Type*} [Group G]

/-- **Transfer: bounded index is closed under pointwise limits.** If `k_n → k` pointwise and
eventually `κ(k_n) ≤ m`, then `κ(k) ≤ m`. -/
theorem negIndex_le_of_tendsto {β : Type*} {l : Filter β} [l.NeBot] {k : β → G → ℂ}
    {k₀ : G → ℂ} (hk : ∀ g, Tendsto (fun n => k n g) l (𝓝 (k₀ g))) {m : ℕ∞}
    (hm : ∀ᶠ n in l, negIndex (k n) ≤ m) : negIndex k₀ ≤ m := by
  rw [negIndex_le_iff]
  intro N x
  have hconv := eventually_le_hermNegIndex (H := fun n => gram (k n) x) (H₀ := gram k₀ x)
    fun a b => hk _
  obtain ⟨n, hn, hnm⟩ := (hconv.and hm).exists
  exact (Nat.cast_le.mpr hn).trans ((hermNegIndex_gram_le_negIndex _ x).trans hnm)

/-- Positive definiteness is closed under pointwise limits of Hermitian kernels. -/
theorem negIndex_eq_zero_of_tendsto {β : Type*} {l : Filter β} [l.NeBot] {k : β → G → ℂ}
    {k₀ : G → ℂ} (hk : ∀ g, Tendsto (fun n => k n g) l (𝓝 (k₀ g)))
    (hm : ∀ᶠ n in l, negIndex (k n) = 0) : negIndex k₀ = 0 :=
  nonpos_iff_eq_zero.mp (negIndex_le_of_tendsto hk (hm.mono fun _ h => h.le))

end GaloisForLFunctions.HeckeKreinToeplitz
