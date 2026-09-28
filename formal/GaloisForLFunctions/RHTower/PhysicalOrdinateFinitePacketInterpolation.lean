import GaloisForLFunctions.RHTower.PhysicalOrdinateTransportNoGo
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Finite zero-selected packets do not inherit the all-height obstruction

For finitely many distinct heights `γ₁, …, γ_m` and arbitrary targets `z₁, …, z_m` in a Hilbert
space, the source Gram matrix `G_σ = (⟨x_{σ,γ_i}, x_{σ,γ_j}⟩)` tends to the identity, so eventually
`Σ_{ij} |G_{ij} - δ_{ij}| ≤ 1/2` and `‖Σ cᵢ x_{σ,γ_i}‖² ≥ ‖c‖²/2`.  The finite-rank map
`S_σ f = Σ_i (G_σ⁻¹ a(f))_i zᵢ`, `a(f)_i = ⟨x_{σ,γ_i}, f⟩`, interpolates exactly,
`S_σ x_{σ,γ_i} = zᵢ`, and `‖S_σ‖ ≤ √2 ‖Z‖` with `Z` the synthesis map `eᵢ ↦ zᵢ`.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology Set Matrix

namespace RHTower

local notation "ℓ²ℕ" => lp (fun _ : ℕ => ℂ) 2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The synthesis map `eᵢ ↦ zᵢ` on `ℂ^m` with the Euclidean norm. -/
def synthesisMap {m : ℕ} (z : Fin m → H) : EuclideanSpace ℂ (Fin m) →L[ℂ] H :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => ∑ i, c i • z i
      map_add' := fun c d => by
        simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul] }

theorem synthesisMap_apply {m : ℕ} (z : Fin m → H) (c : EuclideanSpace ℂ (Fin m)) :
    synthesisMap z c = ∑ i, c i • z i := rfl

/-- The packet Gram matrix `G_{ij} = ⟨x_{σ,γ_i}, x_{σ,γ_j}⟩`. -/
def packetGram (σ : ℝ) {m : ℕ} (γ : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => inner ℂ (ordinateSource σ (γ i)) (ordinateSource σ (γ j))

theorem tendsto_packetGram_defect {m : ℕ} {γ : Fin m → ℝ} (hγ : Function.Injective γ) :
    Tendsto (fun σ => ∑ i, ∑ j, ‖packetGram σ γ i j - (1 : Matrix (Fin m) (Fin m) ℂ) i j‖)
      (𝓝[>] 1) (𝓝 0) := by
  have h : Tendsto (fun σ => ∑ i, ∑ j, ‖packetGram σ γ i j - (1 : Matrix (Fin m) (Fin m) ℂ) i j‖)
      (𝓝[>] 1) (𝓝 (∑ _i : Fin m, ∑ _j : Fin m, (0 : ℝ))) := by
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
    have hij := tendsto_inner_ordinateSource (γ i) (γ j)
    have hval : (if γ i = γ j then (1 : ℂ) else 0) = (1 : Matrix (Fin m) (Fin m) ℂ) i j := by
      rw [Matrix.one_apply]
      by_cases h : i = j
      · subst h; simp
      · rw [if_neg (fun h' => h (hγ h')), if_neg h]
    rw [hval] at hij
    have := (hij.sub_const ((1 : Matrix (Fin m) (Fin m) ℂ) i j)).norm
    simp only [sub_self, norm_zero] at this
    exact this
  simpa using h

/-- `Σ_{ij} conj(cᵢ) G_{ij} c_j = ‖Σ cᵢ x_{σ,γ_i}‖²`. -/
theorem quadForm_packetGram (σ : ℝ) {m : ℕ} (γ : Fin m → ℝ) (c : Fin m → ℂ) :
    ∑ i, ∑ j, (starRingEnd ℂ) (c i) * packetGram σ γ i j * c j =
      inner ℂ (∑ i, c i • ordinateSource σ (γ i)) (∑ j, c j • ordinateSource σ (γ j)) := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_right, packetGram]
  ring

theorem norm_mul_norm_le_sum_sq {m : ℕ} (c : Fin m → ℂ) (i j : Fin m) :
    ‖c i‖ * ‖c j‖ ≤ ∑ k, ‖c k‖ ^ 2 := by
  have hi : ‖c i‖ ^ 2 ≤ ∑ k, ‖c k‖ ^ 2 :=
    Finset.single_le_sum (f := fun k => ‖c k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ i)
  have hj : ‖c j‖ ^ 2 ≤ ∑ k, ‖c k‖ ^ 2 :=
    Finset.single_le_sum (f := fun k => ‖c k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)
  nlinarith [sq_nonneg (‖c i‖ - ‖c j‖)]

/-- **Lower Riesz bound.**  If the Gram defect has entry sum at most `1/2`, then
`‖Σ cᵢ x_{σ,γ_i}‖² ≥ Σ |cᵢ|²/2`. -/
theorem half_sum_sq_le_norm_sq {σ : ℝ} {m : ℕ} {γ : Fin m → ℝ}
    (hdef : ∑ i, ∑ j, ‖packetGram σ γ i j - (1 : Matrix (Fin m) (Fin m) ℂ) i j‖ ≤ 1 / 2)
    (c : Fin m → ℂ) :
    (∑ k, ‖c k‖ ^ 2) / 2 ≤ ‖∑ i, c i • ordinateSource σ (γ i)‖ ^ 2 := by
  set S := ∑ k, ‖c k‖ ^ 2 with hS
  set E : Matrix (Fin m) (Fin m) ℂ := packetGram σ γ - 1 with hE
  have hsplit : ∑ i, ∑ j, (starRingEnd ℂ) (c i) * packetGram σ γ i j * c j =
      (S : ℂ) + ∑ i, ∑ j, (starRingEnd ℂ) (c i) * E i j * c j := by
    have h1 : ∀ i j, packetGram σ γ i j = (1 : Matrix (Fin m) (Fin m) ℂ) i j + E i j := by
      intro i j; simp [hE]
    simp_rw [h1, mul_add, add_mul, Finset.sum_add_distrib, Matrix.one_apply]
    congr 1
    rw [hS]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (Ne.symm hj)]; simp) (by simp),
      if_pos rfl, mul_one, Complex.conj_mul']
  have hbound : ‖∑ i, ∑ j, (starRingEnd ℂ) (c i) * E i j * c j‖ ≤ S / 2 := by
    calc ‖∑ i, ∑ j, (starRingEnd ℂ) (c i) * E i j * c j‖
        ≤ ∑ i, ∑ j, ‖E i j‖ * S := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [norm_mul, norm_mul, Complex.norm_conj]
          have := norm_mul_norm_le_sum_sq c i j
          nlinarith [norm_nonneg (E i j), norm_nonneg (c i), norm_nonneg (c j)]
      _ = (∑ i, ∑ j, ‖E i j‖) * S := by rw [Finset.sum_mul]; simp_rw [Finset.sum_mul]
      _ ≤ 1 / 2 * S := by
          gcongr
          simpa [hE] using hdef
      _ = S / 2 := by ring
  have hq := quadForm_packetGram σ γ c
  rw [hsplit] at hq
  have hre : ‖∑ i, c i • ordinateSource σ (γ i)‖ ^ 2 =
      S + (∑ i, ∑ j, (starRingEnd ℂ) (c i) * E i j * c j).re := by
    rw [@norm_sq_eq_re_inner ℂ, ← hq]
    simp
  have hge := neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans hbound)
  linarith

/-- **Finite packets interpolate.**  For distinct heights and arbitrary targets, eventually there are
finite-rank maps with `S_σ x_{σ,γ_i} = zᵢ` exactly and `‖S_σ f‖ ≤ √2 ‖Z‖ ‖f‖`. -/
theorem eventually_exists_packet_interpolation {m : ℕ} {γ : Fin m → ℝ}
    (hγ : Function.Injective γ) (z : Fin m → H) :
    ∀ᶠ σ in 𝓝[>] 1, ∃ S : ℓ²ℕ →L[ℂ] H, (∀ i, S (ordinateSource σ (γ i)) = z i) ∧
      (∀ f, S f ∈ Submodule.span ℂ (Set.range z)) ∧
      ∀ f, ‖S f‖ ≤ Real.sqrt 2 * ‖synthesisMap z‖ * ‖f‖ := by
  classical
  filter_upwards [(tendsto_packetGram_defect hγ).eventually (ge_mem_nhds (by norm_num :
    (0 : ℝ) < 1 / 2))] with σ hdef
  set G := packetGram σ γ with hG
  -- `G` is invertible
  have hinj : ∀ c : Fin m → ℂ, G *ᵥ c = 0 → c = 0 := by
    intro c hc
    have hq := quadForm_packetGram σ γ c
    rw [← hG] at hq
    have h0 : ∑ i, ∑ j, (starRingEnd ℂ) (c i) * G i j * c j = 0 := by
      have : ∀ i, ∑ j, (starRingEnd ℂ) (c i) * G i j * c j =
          (starRingEnd ℂ) (c i) * (G *ᵥ c) i := by
        intro i; rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      simp_rw [this, hc, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    rw [h0] at hq
    have hv0 := inner_self_eq_zero.mp hq.symm
    have hlow := half_sum_sq_le_norm_sq hdef c
    rw [hv0, norm_zero] at hlow
    funext k
    have hk : ‖c k‖ ^ 2 ≤ ∑ k, ‖c k‖ ^ 2 :=
      Finset.single_le_sum (f := fun k => ‖c k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ k)
    have : ‖c k‖ ^ 2 ≤ 0 := by nlinarith
    simpa using (pow_eq_zero_iff (n := 2) two_ne_zero).mp (le_antisymm this (sq_nonneg _))
  have hdet : IsUnit G.det := by
    rw [isUnit_iff_ne_zero]
    intro h
    obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
    exact hv (hinj v hGv)
  -- the coefficient map
  let a : ℓ²ℕ →ₗ[ℂ] (Fin m → ℂ) :=
    { toFun := fun f i => inner ℂ (ordinateSource σ (γ i)) f
      map_add' := fun f g => by funext i; simp
      map_smul' := fun r f => by funext i; simp }
  let cmap : ℓ²ℕ →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    (WithLp.linearEquiv 2 ℂ (Fin m → ℂ)).symm.toLinearMap ∘ₗ (G⁻¹.mulVecLin ∘ₗ a)
  have hc_apply : ∀ f, (cmap f : Fin m → ℂ) = G⁻¹ *ᵥ a f := fun f => rfl
  -- the key bound `‖c(f)‖ ≤ √2 ‖f‖`
  have hcbound : ∀ f, ‖cmap f‖ ≤ Real.sqrt 2 * ‖f‖ := by
    intro f
    set c : Fin m → ℂ := G⁻¹ *ᵥ a f with hcdef
    have hGc : G *ᵥ c = a f := by
      rw [hcdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hdet, Matrix.one_mulVec]
    set v : ℓ²ℕ := ∑ i, c i • ordinateSource σ (γ i) with hv
    have hq := quadForm_packetGram σ γ c
    rw [← hG] at hq
    have hqa : ∑ i, ∑ j, (starRingEnd ℂ) (c i) * G i j * c j = inner ℂ v f := by
      have : ∀ i, ∑ j, (starRingEnd ℂ) (c i) * G i j * c j = (starRingEnd ℂ) (c i) * a f i := by
        intro i
        rw [← hGc, Matrix.mulVec, dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      simp_rw [this]
      rw [hv, sum_inner]
      exact Finset.sum_congr rfl fun i _ => by rw [inner_smul_left]; rfl
    rw [hqa, ← hv] at hq
    have hvf : ‖v‖ ^ 2 ≤ ‖v‖ * ‖f‖ := by
      rw [@norm_sq_eq_re_inner ℂ, ← hq]
      exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
    have hvle : ‖v‖ ≤ ‖f‖ := by
      by_cases h : ‖v‖ = 0
      · rw [h]; exact norm_nonneg _
      · have hpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
        nlinarith
    have hlow := half_sum_sq_le_norm_sq hdef c
    have hE : ‖cmap f‖ ^ 2 = ∑ k, ‖c k‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      rfl
    have : ‖cmap f‖ ^ 2 ≤ (Real.sqrt 2 * ‖f‖) ^ 2 := by
      rw [hE, mul_pow, Real.sq_sqrt (by norm_num)]
      have := pow_le_pow_left₀ (norm_nonneg _) hvle 2
      linarith
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp this
  let S : ℓ²ℕ →L[ℂ] H :=
    LinearMap.mkContinuous ((synthesisMap z).toLinearMap ∘ₗ cmap)
      (Real.sqrt 2 * ‖synthesisMap z‖) fun f => by
        simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply]
        calc ‖synthesisMap z (cmap f)‖ ≤ ‖synthesisMap z‖ * ‖cmap f‖ :=
              (synthesisMap z).le_opNorm _
          _ ≤ ‖synthesisMap z‖ * (Real.sqrt 2 * ‖f‖) := by gcongr; exact hcbound f
          _ = Real.sqrt 2 * ‖synthesisMap z‖ * ‖f‖ := by ring
  refine ⟨S, fun i => ?_, fun f => ?_, fun f => ?_⟩
  · have ha : a (ordinateSource σ (γ i)) = G *ᵥ Pi.single i 1 := by
      funext k
      rw [Matrix.mulVec_single_one]
      rfl
    have hci : (cmap (ordinateSource σ (γ i)) : Fin m → ℂ) = Pi.single i 1 := by
      rw [hc_apply, ha, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G hdet, Matrix.one_mulVec]
    change synthesisMap z (cmap (ordinateSource σ (γ i))) = z i
    rw [synthesisMap_apply]
    simp_rw [show ∀ k, (cmap (ordinateSource σ (γ i))) k = (Pi.single i (1 : ℂ) : Fin m → ℂ) k from
      fun k => congrFun hci k]
    rw [Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, zero_smul])
      (by simp), Pi.single_eq_same, one_smul]
  · change synthesisMap z (cmap f) ∈ _
    rw [synthesisMap_apply]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · change ‖synthesisMap z (cmap f)‖ ≤ _
    calc ‖synthesisMap z (cmap f)‖ ≤ ‖synthesisMap z‖ * ‖cmap f‖ :=
          (synthesisMap z).le_opNorm _
      _ ≤ ‖synthesisMap z‖ * (Real.sqrt 2 * ‖f‖) := by gcongr; exact hcbound f
      _ = Real.sqrt 2 * ‖synthesisMap z‖ * ‖f‖ := by ring

end RHTower
