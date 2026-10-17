import GaloisForLFunctions.HTGeometry.SymbolicTraceSplitting

/-!
# Quasi-compactness of transfer operators on the Hölder space

With `Tⁿ = Tⁿ E_n + Tⁿ(1 − E_n)`, the first summand has rank at most `k^n` and the second has norm
`O((ϑ e^κ)ⁿ)` by Lasota–Yorke.  This file turns the uniform partition-function bounds into:

* `exists_admissibleRadius` — a circle in the resolvent set between any two radii above
  `ϑ e^κ`;
* `finiteDimensional_outerProj` — the outer spectral subspace has dimension at most `k^{n₀}`;
* `outerProj_apply_mem_levelSpace` — for an `m`-local potential it lies in `V_{m−1}`;
* `uniform_partition_bounds`, `transferOp_bounds` — partition functions and operator norms are
  `O(e^{nκ})`, uniformly for `s` in a bounded part of `Re s > 1 − ε` and for all level potentials
  of sufficiently high level.
-/

namespace GaloisForLFunctions.HTGeometry.Symbolic

open Metric Filter Topology FiniteRank Module

noncomputable section

variable {k : ℕ} {A : Fin k → Fin k → Prop} {ϑ : ℝ}

/-- The range of `X E_N` is finite dimensional, of dimension at most `k^N`. -/
theorem finiteDimensional_opRange_mul_cylAverage (hϑ : 0 < ϑ)
    (X : HolderSpace A ϑ →L[ℂ] HolderSpace A ϑ) (N : ℕ) :
    FiniteDimensional ℂ (opRange (X * cylAverage hϑ N)) ∧
      finrank ℂ (opRange (X * cylAverage hϑ N)) ≤ k ^ N := by
  have hle : opRange (X * cylAverage hϑ N) ≤
      (levelSpace A ϑ N).map (X : HolderSpace A ϑ →ₗ[ℂ] HolderSpace A ϑ) := by
    rintro _ ⟨v, rfl⟩
    exact ⟨cylAverage hϑ N v, cylAverage_mem hϑ N v, rfl⟩
  haveI : FiniteDimensional ℂ ((levelSpace A ϑ N).map
    (X : HolderSpace A ϑ →ₗ[ℂ] HolderSpace A ϑ)) := inferInstance
  refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
  calc finrank ℂ (opRange (X * cylAverage hϑ N))
      ≤ finrank ℂ ((levelSpace A ϑ N).map (X : HolderSpace A ϑ →ₗ[ℂ] HolderSpace A ϑ)) :=
        Submodule.finrank_mono hle
    _ ≤ finrank ℂ (levelSpace A ϑ N) := Submodule.finrank_map_le _ _
    _ ≤ k ^ N := finrank_levelSpace_le N

theorem pow_eq_mul_cylAverage_add (hϑ : 0 < ϑ) (X : HolderSpace A ϑ →L[ℂ] HolderSpace A ϑ)
    (N : ℕ) : X ^ N = X ^ N * cylAverage hϑ N + X ^ N * (1 - cylAverage hϑ N) := by
  rw [← mul_add, add_sub_cancel, mul_one]

/-- **A circle in the resolvent set** between `ρ₁ < ρ₂` once `‖Xᴺ(1 − E_N)‖ < ρ₁ᴺ`. -/
theorem exists_admissibleRadius (hϑ : 0 < ϑ) (X : HolderSpace A ϑ →L[ℂ] HolderSpace A ϑ)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (h12 : ρ₁ < ρ₂) {N : ℕ} (hN : 1 ≤ N)
    (hS : ‖X ^ N * (1 - cylAverage hϑ N)‖ < ρ₁ ^ N) :
    ∃ ρ, IsAdmissibleRadius X ρ₁ ρ₂ ρ := by
  haveI := (finiteDimensional_opRange_mul_cylAverage hϑ (X ^ N) N).1
  obtain ⟨ρ, hρ, hres⟩ := exists_sphere_subset_resolventSet_of_pow_eq_add X hN
    (X ^ N * cylAverage hϑ N) (X ^ N * (1 - cylAverage hϑ N))
    (pow_eq_mul_cylAverage_add hϑ X N) hρ₁ hS h12
  exact ⟨ρ, ⟨hρ.1.le, hρ.2.le⟩, hres⟩

/-- **The outer spectral subspace is finite dimensional**, of dimension at most `k^n`. -/
theorem finiteDimensional_outerProj (hϑ : 0 < ϑ) (X : HolderSpace A ϑ →L[ℂ] HolderSpace A ϑ)
    {ρ Λ : ℝ} (hρ : 0 < ρ) (h : ∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ X)
    (hΛ : ∀ w ∈ sphere (0 : ℂ) ρ, ‖resolvent X w‖ ≤ Λ) {n : ℕ} (hn : 1 ≤ n)
    (hsmall : ρ * Λ * ‖X ^ n * (1 - cylAverage hϑ n)‖ < ρ ^ n) :
    FiniteDimensional ℂ (opRange (outerProj X ρ)) ∧
      finrank ℂ (opRange (outerProj X ρ)) ≤ k ^ n := by
  obtain ⟨hFD, hFr⟩ := finiteDimensional_opRange_mul_cylAverage hϑ (X ^ n) n
  haveI := hFD
  obtain ⟨h1, h2⟩ := finiteDimensional_range_one_sub_rieszProjection X hρ h hΛ hn
    (X ^ n * cylAverage hϑ n) (X ^ n * (1 - cylAverage hϑ n))
    (pow_eq_mul_cylAverage_add hϑ X n) hsmall
  exact ⟨h1, h2.trans hFr⟩

section Local

variable (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {ψ : (ℕ → Fin k) → ℝ} {R₀ C θ : ℝ}
  (hψ : IsHolderPotential A ψ R₀ C θ) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθϑ : θ ≤ ϑ) (hθ1 : θ < 1)

include hθ0 hθϑ hθ1 in
/-- **The outer spectral subspace of an `m`-local transfer operator lies in `V_{m−1}`.** -/
theorem outerProj_apply_mem_levelSpace {m : ℕ} (hloc : IsLocal A ψ m) (hm : 2 ≤ m) (s : ℂ)
    {ρ Λ : ℝ} (hρ : 0 < ρ)
    (h : ∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ (transferOp hϑ hϑ1 hψ hC hθ0 hθϑ hθ1 s))
    (hΛ : ∀ w ∈ sphere (0 : ℂ) ρ,
      ‖resolvent (transferOp hϑ hϑ1 hψ hC hθ0 hθϑ hθ1 s) w‖ ≤ Λ)
    {K c : ℝ} (hc0 : 0 ≤ c) (hc : c < ρ)
    (hS : ∀ j, 1 ≤ j → ‖transferOp hϑ hϑ1 hψ hC hθ0 hθϑ hθ1 s ^ j * (1 - cylAverage hϑ j)‖ ≤
      K * c ^ j)
    (v : HolderSpace A ϑ) :
    outerProj (transferOp hϑ hϑ1 hψ hC hθ0 hθϑ hθ1 s) ρ v ∈ levelSpace A ϑ (m - 1) := by
  set T := transferOp hϑ hϑ1 hψ hC hθ0 hθϑ hθ1 s
  refine one_sub_rieszProjection_apply_mem T hρ h hΛ (levelSpace A ϑ (m - 1))
    (isClosed_levelSpace (m - 1)) (fun j => T ^ j * cylAverage hϑ j)
    (fun j => T ^ j * (1 - cylAverage hϑ j)) (fun j _ => pow_eq_mul_cylAverage_add hϑ T j)
    (fun j v hj => ?_) ?_ v
  · have := transferOp_pow_mem_levelSpace hϑ hϑ1 hψ hC hθ0 hθϑ hθ1 hloc hm s j
      (cylAverage_mem hϑ j v)
    rwa [Nat.sub_self, Nat.max_zero] at this
  · have hq0 : 0 ≤ c / ρ := div_nonneg hc0 hρ.le
    have hq1 : c / ρ < 1 := (div_lt_one hρ).mpr hc
    have hlim : Tendsto (fun j : ℕ => |K| * (c / ρ) ^ j) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul |K|
    refine squeeze_zero' (Eventually.of_forall fun j => by positivity) ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with j hj
    rw [div_le_iff₀ (pow_pos hρ j), div_pow, mul_div_assoc', div_mul_cancel₀ _
      (pow_pos hρ j).ne']
    exact (hS j hj).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (pow_nonneg hc0 j))

include hψ hC hθ0 hθϑ hθ1 in
/-- **Operator bounds from partition bounds**: `‖Tⁿ‖ ≤ max(1, K(L̄+1)) e^{nκ}` and
`‖Tⁿ(1 − E_n)‖ ≤ K (L̄ + 2) (ϑ e^κ)ⁿ`, where `L̄` bounds the Lasota–Yorke constant. -/
theorem transferOp_bounds (s : ℂ) {S K κ : ℝ} (hS : ‖s‖ ≤ S) (hK : 0 ≤ K)
    (hΨ : ∀ n, 1 ≤ n → ∀ x, partitionFun A ψ s.re n x ≤ K * Real.exp (n * κ)) :
    (∀ n : ℕ, ‖transferOp hϑ hϑ1 hψ hC hθ0 hθϑ hθ1 s ^ n‖ ≤
      max 1 (K * (2 + S * (C / (1 - θ)) * Real.exp (S * (C / (1 - θ))) + 1)) *
        Real.exp (n * κ)) ∧
    ∀ n : ℕ, 1 ≤ n → ‖transferOp hϑ hϑ1 hψ hC hθ0 hθϑ hθ1 s ^ n * (1 - cylAverage hϑ n)‖ ≤
      K * (2 + S * (C / (1 - θ)) * Real.exp (S * (C / (1 - θ))) + 2) * (ϑ * Real.exp κ) ^ n := by
  set Lb := 2 + S * (C / (1 - θ)) * Real.exp (S * (C / (1 - θ)))
  have hD : 0 ≤ C / (1 - θ) := div_nonneg hC (by linarith)
  have hLy : lyConst C θ s ≤ Lb := by
    unfold lyConst
    have h1 : ‖s‖ * (C / (1 - θ)) ≤ S * (C / (1 - θ)) := mul_le_mul_of_nonneg_right hS hD
    have h2 : Real.exp (‖s‖ * (C / (1 - θ))) ≤ Real.exp (S * (C / (1 - θ))) :=
      Real.exp_le_exp.mpr h1
    have h3 : 0 ≤ ‖s‖ * (C / (1 - θ)) := by positivity
    nlinarith [Real.exp_pos (‖s‖ * (C / (1 - θ)))]
  have hLy0 := lyConst_nonneg hC hθ1 s
  refine ⟨fun n => ?_, fun n hn => ?_⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pow_zero, Nat.cast_zero, zero_mul, Real.exp_zero, mul_one]
      exact (ContinuousLinearMap.norm_id_le).trans (le_max_left _ _)
    · have h := norm_transferOp_pow_le hϑ hϑ1 hψ hC hθ0 hθϑ hθ1 s n
        (by positivity : 0 ≤ K * Real.exp (n * κ)) fun x _ => hΨ n hn x
      refine h.trans ?_
      calc K * Real.exp (n * κ) * (lyConst C θ s + 1) ≤ K * (Lb + 1) * Real.exp (n * κ) := by
            have := mul_le_mul_of_nonneg_left (add_le_add_right hLy 1)
              (by positivity : 0 ≤ K * Real.exp (n * κ))
            linarith
        _ ≤ max 1 (K * (Lb + 1)) * Real.exp (n * κ) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · have h := norm_transferOp_pow_comp_sub_cylAverage_le hϑ hϑ1 hψ hC hθ0 hθϑ hθ1 s n
      (by positivity : 0 ≤ K * Real.exp (n * κ)) fun x _ => hΨ n hn x
    refine h.trans ?_
    have hϑn : 0 ≤ ϑ ^ n := pow_nonneg hϑ.le n
    calc K * Real.exp (n * κ) * ϑ ^ n * (lyConst C θ s + 2)
        ≤ K * Real.exp (n * κ) * ϑ ^ n * (Lb + 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = K * (Lb + 2) * (ϑ * Real.exp κ) ^ n := by
          rw [mul_pow, ← Real.exp_nat_mul]; ring_nf

end Local

/-- **Uniform partition bounds** for `s` in a bounded part of `Re s > 1 − ε`, for the potential and
for all its level potentials of high level: `Φₙ ≤ K e^{n ε (2R₀ + 2)}`. -/
theorem uniform_partition_bounds {M : ℕ} (hmix : IsMixing A M) (hM : 1 ≤ M)
    {φ : (ℕ → Fin k) → ℝ} {R₀ C θ : ℝ} (hφ : IsHolderPotential A φ R₀ C θ) (hR₀ : 0 ≤ R₀)
    (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hpos : ∀ y, IsAdmissible A y → 0 ≤ φ y)
    {ε B : ℝ} (hε : 0 < ε) (hB0 : 0 ≤ B)
    (hB : ∀ n : ℕ, periodicSumR A φ (n + 1) (1 + ε) ≤ B * ((n : ℝ) + 1)) (S : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ m₀ : ℕ, 2 ≤ m₀ ∧ ∀ s : ℂ, ‖s‖ ≤ S → 1 - ε < s.re → ∀ n, 1 ≤ n → ∀ x,
      partitionFun A φ s.re n x ≤ K * Real.exp (n * (ε * (2 * R₀ + 2))) ∧
      ∀ m, m₀ ≤ m → partitionFun A (levelPotential A φ m) s.re n x ≤
        K * Real.exp (n * (ε * (2 * R₀ + 2))) := by
  set K := Real.exp (S * (C / (1 - θ) + (M - 1) * R₀)) * B * (M + ε⁻¹) *
    Real.exp (M * (2 * ε) * R₀)
  have hK : 0 ≤ K := by positivity
  have hθm : Tendsto (fun m : ℕ => S * C * θ ^ m) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).const_mul (S * C)
  obtain ⟨m₁, hm₁⟩ := (eventually_atTop.mp (hθm.eventually (ge_mem_nhds hε)))
  refine ⟨K, hK, max m₁ 2, le_max_right _ _, fun s hs hσ n hn x => ?_⟩
  have hσS : |s.re| ≤ S := (Complex.abs_re_le_norm s).trans hs
  have hM1 : (0 : ℝ) ≤ (M : ℝ) - 1 := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hbase := partitionFun_le_exp hmix hM hφ hR₀ hθ0 hθ1 hpos hε hB0 hB hσ hn x
  have hconst : Real.exp (|s.re| * (C / (1 - θ) + (M - 1) * R₀)) * B * (M + ε⁻¹) *
      Real.exp (M * (2 * ε) * R₀) ≤ K := by
    have hD : 0 ≤ C / (1 - θ) + (M - 1) * R₀ := by
      have : 0 ≤ C / (1 - θ) := div_nonneg hC (by linarith)
      positivity
    have := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hσS hD)
    have hB' : 0 ≤ B * (M + ε⁻¹) * Real.exp (M * (2 * ε) * R₀) := by positivity
    calc _ = Real.exp (|s.re| * (C / (1 - θ) + (M - 1) * R₀)) *
          (B * (M + ε⁻¹) * Real.exp (M * (2 * ε) * R₀)) := by ring
      _ ≤ Real.exp (S * (C / (1 - θ) + (M - 1) * R₀)) *
          (B * (M + ε⁻¹) * Real.exp (M * (2 * ε) * R₀)) := mul_le_mul_of_nonneg_right this hB'
      _ = K := by simp only [K]; ring
  have hexp1 : Real.exp (n * (ε * (2 * R₀ + 1))) ≤ Real.exp (n * (ε * (2 * R₀ + 2))) := by
    refine Real.exp_le_exp.mpr ?_
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hφbound : partitionFun A φ s.re n x ≤ K * Real.exp (n * (ε * (2 * R₀ + 1))) :=
    hbase.trans (mul_le_mul_of_nonneg_right hconst (Real.exp_pos _).le)
  refine ⟨hφbound.trans (mul_le_mul_of_nonneg_left hexp1 hK), fun m hm => ?_⟩
  have hclose : ∀ y, IsAdmissible A y → |levelPotential A φ m y - φ y| ≤ C * θ ^ m :=
    fun y hy => abs_levelPotential_sub_le hφ m hy
  have h1 := partitionFun_le_of_close hclose s.re n x
  have hsmall : |s.re| * (n * (C * θ ^ m)) ≤ n * ε := by
    have h2 : S * C * θ ^ m ≤ ε := hm₁ m (le_of_max_le_left hm)
    have h3 : |s.re| * (C * θ ^ m) ≤ S * C * θ ^ m := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hσS hC) (pow_nonneg hθ0 m)
    have h4 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  calc partitionFun A (levelPotential A φ m) s.re n x
      ≤ Real.exp (|s.re| * (n * (C * θ ^ m))) * partitionFun A φ s.re n x := h1
    _ ≤ Real.exp (n * ε) * (K * Real.exp (n * (ε * (2 * R₀ + 1)))) :=
        mul_le_mul (Real.exp_le_exp.mpr hsmall) hφbound (partitionFun_nonneg _ _ _ _)
          (Real.exp_pos _).le
    _ = K * Real.exp (n * (ε * (2 * R₀ + 2))) := by
        rw [show (n : ℝ) * (ε * (2 * R₀ + 2)) = n * ε + n * (ε * (2 * R₀ + 1)) by ring,
          Real.exp_add]; ring

end

end GaloisForLFunctions.HTGeometry.Symbolic
