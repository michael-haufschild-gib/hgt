import GaloisForLFunctions.RHTower.STCPhysicalOrdinateSourceOrthogonality
import GaloisForLFunctions.RHTower.XiPrimeSeamPairAsymptotics
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import GaloisForLFunctions.HTGeometry.WeightedDirichletReadout
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Physical-ordinate landing: norm divergence and countable support

The normalized signed squarefree source at physical ordinate `γ` is the unit vector
`x_{σ,γ}(n) = μ(n) √(μ(n)² n^{-σ}/Q(σ)) n^{-iγ}` in `ℓ²(ℕ)`, `Q = ζ(s)/ζ(2s)`, with Gram
`⟨x_{σ,γ}, x_{σ,δ}⟩ = Q(σ + i(δ-γ))/Q(σ)`; distinct heights become orthogonal as `σ ↓ 1`.
The prime seam `v_{β,γ}(p) = (log p/√p)(p^{-β} - p^{β-1}) p^{iγ}` is a norm-continuous family of
nonzero vectors of `ℓ²(P)` for `0 < β < 1`, `β ≠ 1/2`, with `‖v_{β,γ}‖²` the canonical seam energy.

* **Norm divergence.**  If `T_σ x_{σ,γ} → y_γ` for all `γ` near a point where `y` is continuous and
  nonzero, then `‖T_σ‖ → ∞` (finite packets of distinct heights).
* **Countable support.**  If `sup ‖T_σ‖ < ∞` and `T_σ x_{σ,γ} → y_γ` for all `γ` in a separable
  target, then `y_γ ≠ 0` for at most countably many heights (finite Bessel inequality).
* **Sharpness.**  Absolutely summable combinations of source vectors give bounded functionals whose
  limits are supported exactly on the chosen heights.
* A single prime coordinate of the seam already has uncountable support.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology Set

namespace RHTower

open GaloisForLFunctions.HTGeometry

local notation "ℓ²ℕ" => lp (fun _ : ℕ => ℂ) 2
local notation "ℓ²P" => lp (fun _ : Nat.Primes => ℂ) 2

/-! ### The source -/

/-- The physical-ordinate source `x_{σ,γ}` (zero for `σ ≤ 1`). -/
def ordinateSource (σ γ : ℝ) : ℓ²ℕ :=
  if h : 1 < σ then physicalOrdinateMobiusSource σ γ h else 0

theorem ordinateSource_of_gt {σ : ℝ} (h : 1 < σ) (γ : ℝ) :
    ordinateSource σ γ = physicalOrdinateMobiusSource σ γ h := dif_pos h

theorem ordinateSource_of_le {σ : ℝ} (h : σ ≤ 1) (γ : ℝ) : ordinateSource σ γ = 0 :=
  dif_neg (not_lt.mpr h)

/-- Coordinates: `x_{σ,γ}(n) = e^{-iγ log n} μ(n) √(prob_σ(n))`. -/
theorem ordinateSource_apply {σ : ℝ} (h : 1 < σ) (γ : ℝ) (n : ℕ) :
    (ordinateSource σ γ : ℕ → ℂ) n =
      GaloisForLFunctions.expChar (-Real.log n) γ * infiniteMobiusSignedWeight σ n := by
  rw [ordinateSource_of_gt h]
  change infiniteMobiusCriticalComplexDampedSignedWeight σ _ n = _
  rw [infiniteMobiusCriticalComplexDampedSignedWeight, infiniteMobiusCriticalDampedSignedWeight]
  have hs : (σ - 1) ≠ 0 := sub_ne_zero.mpr h.ne'
  simp only [mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, zero_mul,
    neg_zero, Real.exp_zero, ofReal_one, one_mul, mul_im, add_zero]
  rw [GaloisForLFunctions.expChar]
  congr 1
  congr 1
  field_simp
  push_cast
  ring

theorem squarefreePartition_ofReal_ne_zero {σ : ℝ} (h : 1 < σ) :
    GaloisForLFunctions.squarefreePartition (σ : ℂ) ≠ 0 := by
  unfold GaloisForLFunctions.squarefreePartition
  refine div_ne_zero (riemannZeta_ne_zero_of_one_lt_re (by simpa using h))
    (riemannZeta_ne_zero_of_one_lt_re (by simp; linarith))

/-- `‖x_{σ,γ}‖ = 1`. -/
theorem inner_ordinateSource_self {σ : ℝ} (h : 1 < σ) (γ : ℝ) :
    inner ℂ (ordinateSource σ γ) (ordinateSource σ γ) = 1 := by
  rw [ordinateSource_of_gt h, physicalOrdinateMobiusSource_inner]
  simp only [sub_self, ofReal_zero, zero_mul, add_zero]
  exact div_self (squarefreePartition_ofReal_ne_zero h)

theorem norm_ordinateSource {σ : ℝ} (h : 1 < σ) (γ : ℝ) : ‖ordinateSource σ γ‖ = 1 := by
  have h1 := inner_ordinateSource_self h γ
  rw [inner_self_eq_norm_sq_to_K] at h1
  have h2 : ‖ordinateSource σ γ‖ ^ 2 = 1 := by
    have h3 : ((‖ordinateSource σ γ‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; exact h1
    exact_mod_cast h3
  nlinarith [norm_nonneg (ordinateSource σ γ)]

theorem norm_ordinateSource_le (σ γ : ℝ) : ‖ordinateSource σ γ‖ ≤ 1 := by
  by_cases h : 1 < σ
  · rw [norm_ordinateSource h]
  · rw [ordinateSource_of_le (not_lt.mp h), norm_zero]; norm_num

theorem norm_inner_ordinateSource_le (σ γ δ : ℝ) :
    ‖inner ℂ (ordinateSource σ γ) (ordinateSource σ δ)‖ ≤ 1 :=
  (norm_inner_le_norm _ _).trans (by
    have := norm_ordinateSource_le σ γ
    have := norm_ordinateSource_le σ δ
    nlinarith [norm_nonneg (ordinateSource σ γ), norm_nonneg (ordinateSource σ δ)])

/-- **(3)** The source Gram tends to the identity: distinct fixed heights become orthogonal. -/
theorem tendsto_inner_ordinateSource (γ δ : ℝ) :
    Tendsto (fun σ => inner ℂ (ordinateSource σ γ) (ordinateSource σ δ)) (𝓝[>] 1)
      (𝓝 (if γ = δ then 1 else 0)) := by
  by_cases hγδ : γ = δ
  · subst hγδ
    rw [if_pos rfl]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (inner_ordinateSource_self hσ γ).symm
  · rw [if_neg hγδ]
    refine (physicalOrdinateMobiusSource_offDiagonal_tendsto_zero hγδ).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hs : 1 < σ := hσ
    simp [hs, ordinateSource_of_gt hs]

/-- The squared norm of a finite packet tends to the sum of squared coefficients. -/
theorem tendsto_norm_sq_packet (F : Finset ℝ) (a : ℝ → ℂ) :
    Tendsto (fun σ => ‖∑ γ ∈ F, a γ • ordinateSource σ γ‖ ^ 2) (𝓝[>] 1)
      (𝓝 (∑ γ ∈ F, ‖a γ‖ ^ 2)) := by
  classical
  have hform : ∀ σ, inner ℂ (∑ γ ∈ F, a γ • ordinateSource σ γ)
      (∑ γ ∈ F, a γ • ordinateSource σ γ) = ∑ γ ∈ F, ∑ δ ∈ F,
        (starRingEnd ℂ) (a γ) * a δ * inner ℂ (ordinateSource σ γ) (ordinateSource σ δ) := by
    intro σ
    rw [sum_inner]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [inner_smul_left, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [inner_smul_right]
    ring
  have hin : Tendsto (fun σ => inner ℂ (∑ γ ∈ F, a γ • ordinateSource σ γ)
      (∑ γ ∈ F, a γ • ordinateSource σ γ)) (𝓝[>] 1)
      (𝓝 (∑ γ ∈ F, ∑ δ ∈ F, (starRingEnd ℂ) (a γ) * a δ * (if γ = δ then 1 else 0))) := by
    simp only [hform]
    exact tendsto_finsetSum F fun γ _ => tendsto_finsetSum F fun δ _ =>
      (tendsto_inner_ordinateSource γ δ).const_mul _
  have hval : (∑ γ ∈ F, ∑ δ ∈ F, (starRingEnd ℂ) (a γ) * a δ * (if γ = δ then 1 else 0)) =
      ((∑ γ ∈ F, ‖a γ‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [Finset.sum_eq_single γ (fun δ _ hδ => by rw [if_neg (Ne.symm hδ), mul_zero])
      (fun h => absurd hγ h), if_pos rfl, mul_one, Complex.conj_mul']
  rw [hval] at hin
  have hre := (Complex.continuous_re.tendsto _).comp hin
  simp only [Function.comp_def, ofReal_re] at hre
  refine hre.congr fun σ => ?_
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rfl

/-! ### Norm divergence -/

/-- **No uniformly bounded landing on a height interval.**  If `T_σ x_{σ,γ} → y_γ` for every `γ` in a
neighbourhood of `γ₀`, where `y` is continuous at `γ₀` with `y_{γ₀} ≠ 0`, then `‖T_σ‖ → ∞`. -/
theorem tendsto_norm_atTop_of_ordinate_landing {Y : Type*} [NormedAddCommGroup Y]
    [InnerProductSpace ℂ Y] (T : ℝ → ℓ²ℕ →L[ℂ] Y) (y : ℝ → Y) {I : Set ℝ} {γ₀ : ℝ}
    (hI : I ∈ 𝓝 γ₀) (hy : ContinuousAt y γ₀) (hne : y γ₀ ≠ 0)
    (hland : ∀ γ ∈ I, Tendsto (fun σ => T σ (ordinateSource σ γ)) (𝓝[>] 1) (𝓝 (y γ))) :
    Tendsto (fun σ => ‖T σ‖) (𝓝[>] 1) atTop := by
  classical
  set N₀ : ℝ := ‖y γ₀‖ with hN₀
  have hN₀pos : 0 < N₀ := norm_pos_iff.mpr hne
  set w : Y := ((N₀⁻¹ : ℝ) : ℂ) • y γ₀ with hw
  have hwnorm : ‖w‖ = 1 := by
    rw [hw, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hN₀pos),
      inv_mul_cancel₀ hN₀pos.ne']
  have hwy : (inner ℂ (y γ₀) w).re = N₀ := by
    rw [hw, inner_smul_right, inner_self_eq_norm_sq_to_K, ← hN₀]
    change (((N₀⁻¹ : ℝ) : ℂ) * ((N₀ : ℝ) : ℂ) ^ 2).re = N₀
    rw [← ofReal_pow, ← ofReal_mul, ofReal_re]
    field_simp
  set c : ℝ := N₀ / 2 with hc
  have hcpos : 0 < c := by positivity
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, Metric.ball γ₀ ε ⊆ I ∧
      ∀ γ ∈ Metric.ball γ₀ ε, ‖y γ - y γ₀‖ < c := by
    obtain ⟨ε₁, hε₁, h1⟩ := Metric.mem_nhds_iff.mp hI
    obtain ⟨ε₂, hε₂, h2⟩ := Metric.continuousAt_iff.mp hy c hcpos
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (Metric.ball_subset_ball (min_le_left _ _)).trans h1,
      fun γ hγ => ?_⟩
    rw [← dist_eq_norm]
    exact h2 ((Metric.mem_ball.mp hγ).trans_le (min_le_right _ _))
  have hlow : ∀ γ ∈ Metric.ball γ₀ ε, c ≤ (inner ℂ (y γ) w).re := by
    intro γ hγ
    have h1 := (hball.2 γ hγ)
    have hsplit : (inner ℂ (y γ) w).re = (inner ℂ (y γ₀) w).re + (inner ℂ (y γ - y γ₀) w).re := by
      rw [inner_sub_left]; simp
    have h2 : |(inner ℂ (y γ - y γ₀) w).re| ≤ ‖y γ - y γ₀‖ := by
      refine (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
      rw [hwnorm, mul_one]
    rw [hsplit, hwy]
    have := neg_abs_le (inner ℂ (y γ - y γ₀) w).re
    linarith
  rw [tendsto_atTop]
  intro B
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 0 < m ∧ B < c * Real.sqrt m / 4 := by
    obtain ⟨m, hm⟩ := exists_nat_gt ((4 * (|B| + 1) / c) ^ 2)
    refine ⟨m, ?_, ?_⟩
    · have : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
      exact_mod_cast this
    · have hsq : 4 * (|B| + 1) / c < Real.sqrt m := by
        rw [Real.lt_sqrt (by positivity)]; exact hm
      have : 4 * (|B| + 1) < c * Real.sqrt m := by
        rw [div_lt_iff₀ hcpos] at hsq; linarith
      linarith [le_abs_self B]
  obtain ⟨hm0, hmB⟩ := hm
  set g : ℕ → ℝ := fun k => γ₀ + (k + 1) * ε / (2 * (m + 1)) with hg
  have hginj : Function.Injective g := by
    intro a b hab
    simp only [hg, add_right_inj] at hab
    have hne' : (0 : ℝ) < ε / (2 * (m + 1)) := by positivity
    rw [mul_div_assoc, mul_div_assoc] at hab
    have h2 := mul_right_cancel₀ hne'.ne' hab
    exact_mod_cast (by linarith : (a : ℝ) = b)
  set F : Finset ℝ := (Finset.range m).image g with hF
  have hFcard : F.card = m := by
    rw [hF, Finset.card_image_of_injective _ hginj, Finset.card_range]
  have hFball : ∀ γ ∈ F, γ ∈ Metric.ball γ₀ ε := by
    intro γ hγ
    rw [hF, Finset.mem_image] at hγ
    obtain ⟨k, hk, rfl⟩ := hγ
    rw [Finset.mem_range] at hk
    rw [Metric.mem_ball, Real.dist_eq, hg]
    simp only [add_sub_cancel_left]
    have hk' : (k : ℝ) + 1 ≤ m := by exact_mod_cast hk
    rw [abs_of_pos (by positivity)]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  set X : ℝ → ℓ²ℕ := fun σ => ∑ γ ∈ F, (1 : ℂ) • ordinateSource σ γ with hX
  have hXnorm := tendsto_norm_sq_packet F (fun _ => (1 : ℂ))
  simp only [norm_one, one_pow, Finset.sum_const, hFcard, nsmul_eq_mul, mul_one] at hXnorm
  have hXev : ∀ᶠ σ in 𝓝[>] 1, ‖X σ‖ ^ 2 < 4 * m := by
    have hm' : (m : ℝ) < 4 * m := by
      have : (0 : ℝ) < m := by exact_mod_cast hm0
      linarith
    exact hXnorm.eventually (gt_mem_nhds hm')
  have hpair : Tendsto (fun σ => (inner ℂ (T σ (X σ)) w).re) (𝓝[>] 1)
      (𝓝 (∑ γ ∈ F, (inner ℂ (y γ) w).re)) := by
    simp only [hX, map_sum, one_smul, sum_inner, Complex.re_sum]
    exact tendsto_finsetSum F fun γ hγ =>
      (Complex.continuous_re.tendsto _).comp
        (((hland γ (hball.1 (hFball γ hγ))).inner tendsto_const_nhds))
  have hsumlow : m * c ≤ ∑ γ ∈ F, (inner ℂ (y γ) w).re := by
    calc (m : ℝ) * c = ∑ _γ ∈ F, c := by rw [Finset.sum_const, hFcard, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun γ hγ => hlow γ (hFball γ hγ)
  have hpairev : ∀ᶠ σ in 𝓝[>] 1, m * c / 2 < (inner ℂ (T σ (X σ)) w).re := by
    have hmc : (m : ℝ) * c / 2 < ∑ γ ∈ F, (inner ℂ (y γ) w).re := by
      have : (0 : ℝ) < m * c := by
        have : (0 : ℝ) < m := by exact_mod_cast hm0
        positivity
      linarith
    exact hpair.eventually (lt_mem_nhds hmc)
  filter_upwards [hXev, hpairev] with σ h1 h2
  have hXle : ‖X σ‖ ≤ 2 * Real.sqrt m := by
    have hsq : Real.sqrt (4 * m) = 2 * Real.sqrt m := by
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    rw [← hsq]
    exact Real.le_sqrt_of_sq_le h1.le
  have hTX : (inner ℂ (T σ (X σ)) w).re ≤ ‖T σ‖ * (2 * Real.sqrt m) := by
    calc (inner ℂ (T σ (X σ)) w).re ≤ ‖inner ℂ (T σ (X σ)) w‖ := Complex.re_le_norm _
      _ ≤ ‖T σ (X σ)‖ * ‖w‖ := norm_inner_le_norm _ _
      _ = ‖T σ (X σ)‖ := by rw [hwnorm, mul_one]
      _ ≤ ‖T σ‖ * ‖X σ‖ := (T σ).le_opNorm _
      _ ≤ ‖T σ‖ * (2 * Real.sqrt m) := by gcongr
  have hsqrt_pos : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm0)
  have hsqm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt (by positivity)
  have : c * Real.sqrt m / 4 ≤ ‖T σ‖ := by
    have h3 : (m : ℝ) * c / 2 < ‖T σ‖ * (2 * Real.sqrt m) := lt_of_lt_of_le h2 hTX
    rw [← hsqm] at h3
    nlinarith [norm_nonneg (T σ)]
  linarith

/-! ### Countable support -/

/-- **Finite Bessel inequality (4).**  For a uniformly bounded landing and distinct heights,
`Σ |⟨y_γ, w⟩|² ≤ B² ‖w‖²`. -/
theorem sum_norm_inner_sq_le_of_bounded_landing {Y : Type*} [NormedAddCommGroup Y]
    [InnerProductSpace ℂ Y] (T : ℝ → ℓ²ℕ →L[ℂ] Y) {B : ℝ}
    (hB : ∀ᶠ σ in 𝓝[>] 1, ‖T σ‖ ≤ B) (y : ℝ → Y) (F : Finset ℝ)
    (hland : ∀ γ ∈ F, Tendsto (fun σ => T σ (ordinateSource σ γ)) (𝓝[>] 1) (𝓝 (y γ)))
    (w : Y) : ∑ γ ∈ F, ‖inner ℂ (y γ) w‖ ^ 2 ≤ B ^ 2 * ‖w‖ ^ 2 := by
  classical
  set a : ℝ → ℂ := fun γ => inner ℂ (y γ) w with ha
  set S : ℝ := ∑ γ ∈ F, ‖a γ‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hB0 : 0 ≤ B := by
    obtain ⟨σ, hσ⟩ := hB.exists
    exact (norm_nonneg _).trans hσ
  set X : ℝ → ℓ²ℕ := fun σ => ∑ γ ∈ F, a γ • ordinateSource σ γ with hX
  have hXn : Tendsto (fun σ => ‖X σ‖) (𝓝[>] 1) (𝓝 (Real.sqrt S)) := by
    have h := (Real.continuous_sqrt.tendsto _).comp (tendsto_norm_sq_packet F a)
    refine h.congr fun σ => ?_
    simp only [Function.comp_apply, hX]
    rw [Real.sqrt_sq (norm_nonneg _)]
  have hpair : Tendsto (fun σ => inner ℂ (T σ (X σ)) w) (𝓝[>] 1) (𝓝 (S : ℂ)) := by
    have h : Tendsto (fun σ => inner ℂ (T σ (X σ)) w) (𝓝[>] 1)
        (𝓝 (∑ γ ∈ F, (starRingEnd ℂ) (a γ) * inner ℂ (y γ) w)) := by
      simp only [hX, map_sum, map_smul, sum_inner, inner_smul_left]
      exact tendsto_finsetSum F fun γ hγ =>
        ((hland γ hγ).inner tendsto_const_nhds).const_mul _
    convert h using 2
    rw [hS]
    push_cast
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [ha, Complex.conj_mul']
  have hle : S ≤ B * Real.sqrt S * ‖w‖ := by
    have hl := hpair.norm
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0] at hl
    refine le_of_tendsto_of_tendsto hl ((hXn.const_mul B).mul_const ‖w‖) ?_
    filter_upwards [hB] with σ hσ
    calc ‖inner ℂ (T σ (X σ)) w‖ ≤ ‖T σ (X σ)‖ * ‖w‖ := norm_inner_le_norm _ _
      _ ≤ ‖T σ‖ * ‖X σ‖ * ‖w‖ := by gcongr; exact (T σ).le_opNorm _
      _ ≤ B * ‖X σ‖ * ‖w‖ := by gcongr
  have hsq := Real.sq_sqrt hS0
  have hsqrt0 := Real.sqrt_nonneg S
  by_cases h0 : Real.sqrt S = 0
  · have : S = 0 := by rw [← hsq, h0]; ring
    rw [this]; positivity
  · have hpos : 0 < Real.sqrt S := lt_of_le_of_ne hsqrt0 (Ne.symm h0)
    have h1 : Real.sqrt S ≤ B * ‖w‖ := by
      have : Real.sqrt S * Real.sqrt S ≤ B * ‖w‖ * Real.sqrt S := by
        rw [← sq, hsq]; linarith
      exact le_of_mul_le_mul_right this hpos
    calc S = Real.sqrt S ^ 2 := hsq.symm
      _ ≤ (B * ‖w‖) ^ 2 := pow_le_pow_left₀ hsqrt0 h1 2
      _ = B ^ 2 * ‖w‖ ^ 2 := by ring

theorem countable_setOf_inner_ne_zero {Y : Type*} [NormedAddCommGroup Y]
    [InnerProductSpace ℂ Y] (T : ℝ → ℓ²ℕ →L[ℂ] Y) {B : ℝ}
    (hB : ∀ᶠ σ in 𝓝[>] 1, ‖T σ‖ ≤ B) (y : ℝ → Y)
    (hland : ∀ γ, Tendsto (fun σ => T σ (ordinateSource σ γ)) (𝓝[>] 1) (𝓝 (y γ))) (w : Y) :
    {γ : ℝ | inner ℂ (y γ) w ≠ 0}.Countable := by
  have hsub : {γ : ℝ | inner ℂ (y γ) w ≠ 0} ⊆
      ⋃ k : ℕ, {γ : ℝ | 1 / ((k : ℝ) + 1) < ‖inner ℂ (y γ) w‖} := by
    intro γ hγ
    have hpos : 0 < ‖inner ℂ (y γ) w‖ := norm_pos_iff.mpr hγ
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
    exact mem_iUnion.mpr ⟨k, hk⟩
  refine Countable.mono hsub (countable_iUnion fun k => Set.Finite.countable ?_)
  by_contra hinf
  obtain ⟨N, hN⟩ := exists_nat_gt (B ^ 2 * ‖w‖ ^ 2 * ((k : ℝ) + 1) ^ 2)
  obtain ⟨t, ht, htcard⟩ := Set.Infinite.exists_subset_card_eq hinf N
  have hbessel := sum_norm_inner_sq_le_of_bounded_landing T hB y t (fun γ _ => hland γ) w
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlow : (N : ℝ) * (1 / ((k : ℝ) + 1)) ^ 2 ≤ ∑ γ ∈ t, ‖inner ℂ (y γ) w‖ ^ 2 := by
    calc (N : ℝ) * (1 / ((k : ℝ) + 1)) ^ 2 = ∑ _γ ∈ t, (1 / ((k : ℝ) + 1)) ^ 2 := by
          rw [Finset.sum_const, htcard, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun γ hγ => by
          have := ht hγ
          simp only [mem_setOf_eq] at this
          exact pow_le_pow_left₀ (by positivity) this.le 2
  have : (N : ℝ) ≤ B ^ 2 * ‖w‖ ^ 2 * ((k : ℝ) + 1) ^ 2 := by
    have h := hlow.trans hbessel
    rw [div_pow, one_pow, ← div_eq_mul_one_div, div_le_iff₀ (by positivity)] at h
    exact h
  linarith

/-- **Countable support classification.**  A uniformly bounded landing into a separable Hilbert
space has nonzero limits at no more than countably many heights. -/
theorem countable_support_of_bounded_landing {Y : Type*} [NormedAddCommGroup Y]
    [InnerProductSpace ℂ Y] [TopologicalSpace.SeparableSpace Y] (T : ℝ → ℓ²ℕ →L[ℂ] Y) {B : ℝ}
    (hB : ∀ᶠ σ in 𝓝[>] 1, ‖T σ‖ ≤ B) (y : ℝ → Y)
    (hland : ∀ γ, Tendsto (fun σ => T σ (ordinateSource σ γ)) (𝓝[>] 1) (𝓝 (y γ))) :
    {γ : ℝ | y γ ≠ 0}.Countable := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense Y
  have hsub : {γ : ℝ | y γ ≠ 0} ⊆ ⋃ w ∈ D, {γ : ℝ | inner ℂ (y γ) w ≠ 0} := by
    intro γ hγ
    by_contra hnot
    simp only [mem_iUnion, mem_setOf_eq, not_exists, not_not] at hnot
    have hzero : ∀ w, inner ℂ (y γ) w = 0 := by
      have hc : Continuous fun w : Y => inner ℂ (y γ) w := continuous_const.inner continuous_id
      have := Continuous.ext_on hDd hc (continuous_const (y := (0 : ℂ))) fun w hw => hnot w hw
      exact fun w => congrFun this w
    exact hγ (inner_self_eq_zero.mp (hzero (y γ)))
  exact (hDc.biUnion fun w _ => countable_setOf_inner_ne_zero T hB y hland w).mono hsub

/-! ### The prime seam -/

/-- The seam amplitude `b_β(n) = (log n/√n)(n^{-β} - n^{β-1})`. -/
def seamAmplitude (β : ℝ) (n : ℕ) : ℝ :=
  Real.log n / Real.sqrt n * ((n : ℝ) ^ (-β) - (n : ℝ) ^ (β - 1))

theorem abs_rpow_neg_sub_rpow_le {x β : ℝ} (hx : 1 ≤ x) :
    |x ^ (-β) - x ^ (β - 1)| ≤ 2 * x ^ (-min β (1 - β)) := by
  have hx0 : 0 < x := by linarith
  have h1 : x ^ (-β) ≤ x ^ (-min β (1 - β)) :=
    Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg (min_le_left _ _))
  have h2 : x ^ (β - 1) ≤ x ^ (-min β (1 - β)) :=
    Real.rpow_le_rpow_of_exponent_le hx (by have := min_le_right β (1 - β); linarith)
  have h3 := Real.rpow_nonneg hx0.le (-β)
  have h4 := Real.rpow_nonneg hx0.le (β - 1)
  rw [abs_le]; constructor <;> linarith

theorem rpow_half_sq {x : ℝ} (hx : 0 ≤ x) (a : ℝ) : (x ^ (a / 2)) ^ 2 = x ^ a := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

theorem sq_seamAmplitude_le {β : ℝ} (hβ : β ∈ Ioo 0 1) (n : ℕ) :
    seamAmplitude β n ^ 2 ≤ 16 / min β (1 - β) ^ 2 * (n : ℝ) ^ (-(1 + min β (1 - β))) := by
  set κ := min β (1 - β) with hκ
  have hκpos : 0 < κ := lt_min hβ.1 (by linarith [hβ.2])
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp [seamAmplitude]; positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hpos
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlog : Real.log n ≤ (n : ℝ) ^ (κ / 2) / (κ / 2) :=
    Real.log_le_rpow_div hn0.le (by positivity)
  have habs := abs_rpow_neg_sub_rpow_le (β := β) hn1
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0.le
  have hl2 : Real.log n ^ 2 ≤ 4 / κ ^ 2 * (n : ℝ) ^ κ := by
    have := pow_le_pow_left₀ hlog0 hlog 2
    rw [div_pow, rpow_half_sq hn0.le] at this
    calc Real.log n ^ 2 ≤ (n : ℝ) ^ κ / (κ / 2) ^ 2 := this
      _ = 4 / κ ^ 2 * (n : ℝ) ^ κ := by field_simp; ring
  have hd2 : ((n : ℝ) ^ (-β) - (n : ℝ) ^ (β - 1)) ^ 2 ≤ 4 * (n : ℝ) ^ (-(2 * κ)) := by
    have h := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rw [sq_abs, mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (-κ)), ← Real.rpow_mul hn0.le] at h
    norm_num at h
    calc _ ≤ 4 * (n : ℝ) ^ (-(κ * 2)) := h
      _ = 4 * (n : ℝ) ^ (-(2 * κ)) := by ring_nf
  rw [seamAmplitude, mul_pow, div_pow, hsq]
  have hpow0 : 0 ≤ (n : ℝ) ^ κ := by positivity
  calc Real.log n ^ 2 / n * ((n : ℝ) ^ (-β) - (n : ℝ) ^ (β - 1)) ^ 2
      ≤ (4 / κ ^ 2 * (n : ℝ) ^ κ) / n * (4 * (n : ℝ) ^ (-(2 * κ))) := by
        gcongr
    _ = 16 / κ ^ 2 * ((n : ℝ) ^ κ * (n : ℝ) ^ (-1 : ℝ) * (n : ℝ) ^ (-(2 * κ))) := by
        rw [Real.rpow_neg_one]; field_simp; ring
    _ = 16 / κ ^ 2 * (n : ℝ) ^ (-(1 + κ)) := by
        rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]; ring_nf

theorem summable_seamAmplitude_sq {β : ℝ} (hβ : β ∈ Ioo 0 1) :
    Summable fun n : ℕ => seamAmplitude β n ^ 2 := by
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (sq_seamAmplitude_le hβ) ?_
  have h : 1 < 1 + min β (1 - β) := by
    have := lt_min hβ.1 (by linarith [hβ.2] : (0 : ℝ) < 1 - β); linarith
  refine ((Real.summable_nat_rpow_inv.mpr h).mul_left (16 / min β (1 - β) ^ 2)).congr
    fun n => ?_
  rw [Real.rpow_neg (Nat.cast_nonneg n)]

theorem summable_seamAmplitude_sq_primes {β : ℝ} (hβ : β ∈ Ioo 0 1) :
    Summable fun p : Nat.Primes => seamAmplitude β p ^ 2 :=
  (summable_seamAmplitude_sq hβ).comp_injective Subtype.val_injective

theorem memℓp_seam {β : ℝ} (hβ : β ∈ Ioo 0 1) (γ : ℝ) :
    Memℓp (fun p : Nat.Primes =>
      (seamAmplitude β p : ℂ) * GaloisForLFunctions.expChar (Real.log p) γ) 2 := by
  refine HilbertSchmidt.memℓp_of_sq ((summable_seamAmplitude_sq_primes hβ).congr fun p => ?_)
  rw [norm_mul, GaloisForLFunctions.norm_expChar, mul_one, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]

/-- The weighted canonical FE--Schwarz seam `v_{β,γ}(p) = b_β(p) p^{iγ}` **(1)**. -/
def seamVector (β : ℝ) (hβ : β ∈ Ioo 0 1) (γ : ℝ) : ℓ²P := ⟨_, memℓp_seam hβ γ⟩

theorem seamVector_apply {β : ℝ} (hβ : β ∈ Ioo 0 1) (γ : ℝ) (p : Nat.Primes) :
    (seamVector β hβ γ : Nat.Primes → ℂ) p =
      (seamAmplitude β p : ℂ) * GaloisForLFunctions.expChar (Real.log p) γ := rfl

/-- The seam energy is independent of the height. -/
theorem norm_sq_seamVector {β : ℝ} (hβ : β ∈ Ioo 0 1) (γ : ℝ) :
    ‖seamVector β hβ γ‖ ^ 2 = ∑' p : Nat.Primes, seamAmplitude β p ^ 2 := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  refine tsum_congr fun p => ?_
  rw [seamVector_apply, norm_mul, GaloisForLFunctions.norm_expChar, mul_one, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

/-- `|charge(p, β+iγ)|²/p = b_β(p)²`: the seam coordinates are the canonical orbitwise seam charges
weighted by `p^{-1/2}`. -/
theorem norm_orbitwiseNatPrimeSeamCharge_sq_div {β γ : ℝ} {n : ℕ} (hn : 0 < n) :
    ‖orbitwiseNatPrimeSeamCharge n ((β : ℂ) + γ * I)‖ ^ 2 / (n : ℝ) = seamAmplitude β n ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have e1 : -(starRingEnd ℂ) ((β : ℂ) + γ * I) = ((-β : ℝ) : ℂ) + (γ * I) := by
    simp [map_add, Complex.conj_ofReal]; ring
  have e2 : -(1 - ((β : ℂ) + γ * I)) = ((β - 1 : ℝ) : ℂ) + (γ * I) := by push_cast; ring
  have hphase : ‖((n : ℝ) : ℂ) ^ ((γ : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0]; simp
  rw [orbitwiseNatPrimeSeamCharge, orbitwiseScaleSeamCharge, e1, e2,
    Complex.cpow_add _ _ hx, Complex.cpow_add _ _ hx, ← Complex.ofReal_cpow hn0.le,
    ← Complex.ofReal_cpow hn0.le, ← sub_mul, norm_mul, norm_mul, hphase, mul_one,
    ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, mul_pow, sq_abs, sq_abs, seamAmplitude, mul_pow, div_pow,
    Real.sq_sqrt hn0.le]
  ring

/-- `‖v_{β,γ}‖²` is the canonical orbitwise seam energy at `ρ = β + iγ`. -/
theorem norm_sq_seamVector_eq_orbitwise {β : ℝ} (hβ : β ∈ Ioo 0 1) (γ : ℝ) :
    ‖seamVector β hβ γ‖ ^ 2 = orbitwisePrimeSeamWeightedNormSq ((β : ℂ) + γ * I) := by
  rw [norm_sq_seamVector, orbitwisePrimeSeamWeightedNormSq]
  exact tsum_congr fun p => (norm_orbitwiseNatPrimeSeamCharge_sq_div p.2.pos).symm

theorem seamAmplitude_ne_zero {β : ℝ} (hβ2 : β ≠ 1 / 2) {n : ℕ} (hn : 2 ≤ n) :
    seamAmplitude β n ≠ 0 := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  refine mul_ne_zero (div_ne_zero (Real.log_pos hn1).ne' (Real.sqrt_pos.mpr hn0).ne') ?_
  rw [sub_ne_zero]
  intro h
  rcases lt_or_gt_of_ne (show -β ≠ β - 1 by intro h'; apply hβ2; linarith) with hlt | hgt
  · exact (Real.rpow_lt_rpow_of_exponent_lt hn1 hlt).ne h
  · exact (Real.rpow_lt_rpow_of_exponent_lt hn1 hgt).ne' h

theorem seamVector_apply_ne_zero {β : ℝ} (hβ : β ∈ Ioo 0 1) (hβ2 : β ≠ 1 / 2) (γ : ℝ)
    (p : Nat.Primes) : (seamVector β hβ γ : Nat.Primes → ℂ) p ≠ 0 := by
  rw [seamVector_apply]
  refine mul_ne_zero (Complex.ofReal_ne_zero.mpr (seamAmplitude_ne_zero hβ2 p.2.two_le)) ?_
  intro h
  have := GaloisForLFunctions.norm_expChar (Real.log p) γ
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem seamVector_ne_zero {β : ℝ} (hβ : β ∈ Ioo 0 1) (hβ2 : β ≠ 1 / 2) (γ : ℝ) :
    seamVector β hβ γ ≠ 0 := fun h =>
  seamVector_apply_ne_zero hβ hβ2 γ ⟨2, Nat.prime_two⟩ (by rw [h]; rfl)

/-- The seam family is norm-continuous in the height. -/
theorem continuous_seamVector {β : ℝ} (hβ : β ∈ Ioo 0 1) : Continuous (seamVector β hβ) := by
  rw [continuous_iff_continuousAt]
  intro γ
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have e : ∀ δ, ‖seamVector β hβ δ - seamVector β hβ γ‖ ^ 2 = ∑' p : Nat.Primes,
      seamAmplitude β p ^ 2 * ‖GaloisForLFunctions.expChar (Real.log p) δ -
        GaloisForLFunctions.expChar (Real.log p) γ‖ ^ 2 := by
    intro δ
    rw [HilbertSchmidt.lp_norm_sq_eq]
    refine tsum_congr fun p => ?_
    rw [lp.coeFn_sub, Pi.sub_apply, seamVector_apply, seamVector_apply, ← mul_sub, norm_mul,
      mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hsq : Tendsto (fun δ => ‖seamVector β hβ δ - seamVector β hβ γ‖ ^ 2) (𝓝 γ) (𝓝 0) := by
    simp_rw [e]
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝 γ)
      (f := fun δ (p : Nat.Primes) => seamAmplitude β p ^ 2 *
        ‖GaloisForLFunctions.expChar (Real.log p) δ - GaloisForLFunctions.expChar (Real.log p) γ‖ ^ 2)
      (g := fun _ => 0) (bound := fun p => 4 * seamAmplitude β p ^ 2)
      ((summable_seamAmplitude_sq_primes hβ).mul_left 4) (fun p => ?_) ?_
    · simpa using h
    · have hc : Continuous fun δ => seamAmplitude β p ^ 2 *
          ‖GaloisForLFunctions.expChar (Real.log p) δ -
            GaloisForLFunctions.expChar (Real.log p) γ‖ ^ 2 :=
        continuous_const.mul (((GaloisForLFunctions.continuous_expChar _).sub
          continuous_const).norm.pow 2)
      simpa using hc.tendsto γ
    · refine Eventually.of_forall fun δ p => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h2 : ‖GaloisForLFunctions.expChar (Real.log p) δ -
          GaloisForLFunctions.expChar (Real.log p) γ‖ ≤ 2 := by
        refine (norm_sub_le _ _).trans ?_
        rw [GaloisForLFunctions.norm_expChar, GaloisForLFunctions.norm_expChar]; norm_num
      have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      nlinarith [sq_nonneg (seamAmplitude β p)]
  have h := (Real.continuous_sqrt.tendsto 0).comp hsq
  simp only [Real.sqrt_zero, Function.comp_def] at h
  refine h.congr fun δ => ?_
  rw [Real.sqrt_sq (norm_nonneg _)]

/-- **No uniformly bounded all-height landing on the seam (2).**  For `0 < β < 1`, `β ≠ 1/2`, if
`T_σ x_{σ,γ} → v_{β,γ}` for every `γ` in a set with nonempty interior then `‖T_σ‖ → ∞`. -/
theorem tendsto_norm_atTop_of_seam_landing {β : ℝ} (hβ : β ∈ Ioo 0 1) (hβ2 : β ≠ 1 / 2)
    (T : ℝ → ℓ²ℕ →L[ℂ] ℓ²P) {I : Set ℝ} (hI : (interior I).Nonempty)
    (hland : ∀ γ ∈ I, Tendsto (fun σ => T σ (ordinateSource σ γ)) (𝓝[>] 1)
      (𝓝 (seamVector β hβ γ))) :
    Tendsto (fun σ => ‖T σ‖) (𝓝[>] 1) atTop := by
  obtain ⟨γ₀, hγ₀⟩ := hI
  exact tendsto_norm_atTop_of_ordinate_landing T (seamVector β hβ) (mem_interior_iff_mem_nhds.mp hγ₀)
    (continuous_seamVector hβ).continuousAt (seamVector_ne_zero hβ hβ2 γ₀) hland

/-! ### Sharpness of the countability boundary -/

/-- **The countability boundary is sharp.**  For distinct heights `γ_j` and absolutely summable
`a_j`, the functionals `⟨Σ a_j x_{σ,γ_j}, ·⟩` are bounded by `Σ ‖a_j‖` and their landing limits are
`conj a_j` at `γ_j` and zero elsewhere. -/
theorem exists_bounded_landing_supported (γs : ℕ → ℝ) {a : ℕ → ℂ}
    (ha : Summable fun j => ‖a j‖) :
    ∃ L : ℝ → ℓ²ℕ →L[ℂ] ℂ, (∀ σ, ‖L σ‖ ≤ ∑' j, ‖a j‖) ∧
      ∀ γ, Tendsto (fun σ => L σ (ordinateSource σ γ)) (𝓝[>] 1)
        (𝓝 (∑' j, if γs j = γ then (starRingEnd ℂ) (a j) else 0)) := by
  classical
  have hsum : ∀ σ, Summable fun j => a j • ordinateSource σ (γs j) := fun σ =>
    Summable.of_norm_bounded ha fun j => by
      rw [norm_smul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (norm_ordinateSource_le σ (γs j)))
  set v : ℝ → ℓ²ℕ := fun σ => ∑' j, a j • ordinateSource σ (γs j) with hv
  refine ⟨fun σ => innerSL ℂ (v σ), fun σ => ?_, fun γ => ?_⟩
  · rw [innerSL_apply_norm]
    refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => by
        rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _)
          (norm_ordinateSource_le σ (γs j))) ha
    · refine Summable.tsum_le_tsum (fun j => ?_) ?_ ha
      · rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) (norm_ordinateSource_le σ (γs j))
      · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => by
          rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _)
            (norm_ordinateSource_le σ (γs j))) ha
  · have happ : ∀ σ, innerSL ℂ (v σ) (ordinateSource σ γ) = ∑' j, (starRingEnd ℂ) (a j) *
        inner ℂ (ordinateSource σ (γs j)) (ordinateSource σ γ) := by
      intro σ
      rw [innerSL_apply_apply]
      have h1 := ((hsum σ).hasSum.mapL (innerSL ℂ (ordinateSource σ γ)))
      have h2 := h1.map (starRingEnd ℂ) Complex.continuous_conj
      simp only [Function.comp_def, innerSL_apply_apply, inner_conj_symm, inner_smul_left] at h2
      exact h2.tsum_eq.symm
    simp_rw [happ]
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (1 : ℝ))
      (f := fun σ j => (starRingEnd ℂ) (a j) * inner ℂ (ordinateSource σ (γs j)) (ordinateSource σ γ))
      (g := fun j => (starRingEnd ℂ) (a j) * (if γs j = γ then 1 else 0))
      (bound := fun j => ‖a j‖) ha
      (fun j => (tendsto_inner_ordinateSource (γs j) γ).const_mul _)
      (Eventually.of_forall fun σ j => by
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_of_le_one_right (norm_nonneg _) (norm_inner_ordinateSource_le σ _ _))
    have hval : (∑' j, (starRingEnd ℂ) (a j) * (if γs j = γ then (1 : ℂ) else 0)) =
        ∑' j, if γs j = γ then (starRingEnd ℂ) (a j) else 0 :=
      tsum_congr fun j => by split_ifs <;> simp
    rw [← hval]
    exact h

theorem tsum_ite_conj_ne_zero_iff {γs : ℕ → ℝ} (hinj : Function.Injective γs) (a : ℕ → ℂ)
    (γ : ℝ) : (∑' j, if γs j = γ then (starRingEnd ℂ) (a j) else 0) ≠ 0 ↔
      ∃ j, γs j = γ ∧ a j ≠ 0 := by
  classical
  constructor
  · intro h
    by_contra hnot
    push Not at hnot
    apply h
    refine (tsum_congr fun j => ?_).trans tsum_zero
    split_ifs with hj
    · rw [hnot j hj, map_zero]
    · rfl
  · rintro ⟨j, hj, haj⟩
    rw [tsum_eq_single j fun j' hj' => by
      rw [if_neg]; intro h'; exact hj' (hinj (h'.trans hj.symm))]
    rw [if_pos hj]
    simpa using haj

/-- **A single prime coordinate already obstructs.**  No uniformly bounded family of functionals can
carry the whole source family to one prime coordinate of the seam. -/
theorem not_bounded_landing_seam_coordinate {β : ℝ} (hβ : β ∈ Ioo 0 1) (hβ2 : β ≠ 1 / 2)
    (p : Nat.Primes) (T : ℝ → ℓ²ℕ →L[ℂ] ℂ) {B : ℝ} (hB : ∀ᶠ σ in 𝓝[>] 1, ‖T σ‖ ≤ B)
    (hland : ∀ γ, Tendsto (fun σ => T σ (ordinateSource σ γ)) (𝓝[>] 1)
      (𝓝 ((seamVector β hβ γ : Nat.Primes → ℂ) p))) : False := by
  have hc := countable_support_of_bounded_landing T hB _ hland
  have huniv : {γ : ℝ | (seamVector β hβ γ : Nat.Primes → ℂ) p ≠ 0} = univ :=
    eq_univ_of_forall fun γ => seamVector_apply_ne_zero hβ hβ2 γ p
  rw [huniv] at hc
  exact Cardinal.not_countable_real hc

/-- The same for maps into the whole prime space: any uniformly bounded all-height seam landing is
impossible. -/
theorem not_bounded_seam_landing {β : ℝ} (hβ : β ∈ Ioo 0 1) (hβ2 : β ≠ 1 / 2)
    (T : ℝ → ℓ²ℕ →L[ℂ] ℓ²P) {B : ℝ} (hB : ∀ᶠ σ in 𝓝[>] 1, ‖T σ‖ ≤ B)
    (hland : ∀ γ, Tendsto (fun σ => T σ (ordinateSource σ γ)) (𝓝[>] 1)
      (𝓝 (seamVector β hβ γ))) : False := by
  classical
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  let e : ℓ²P →L[ℂ] ℂ := innerSL ℂ (lp.single 2 p (1 : ℂ))
  have he : ∀ f : ℓ²P, e f = (f : Nat.Primes → ℂ) p := fun f => by
    simp [e, innerSL_apply_apply, lp.inner_single_left]
  have hen : ‖e‖ ≤ 1 := by
    rw [innerSL_apply_norm, lp.norm_single (by norm_num)]; simp
  refine not_bounded_landing_seam_coordinate hβ hβ2 p (fun σ => e.comp (T σ)) (B := B) ?_ ?_
  · filter_upwards [hB] with σ hσ
    calc ‖e.comp (T σ)‖ ≤ ‖e‖ * ‖T σ‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * B := by gcongr
      _ = B := one_mul B
  · intro γ
    have := ((e.continuous.tendsto _).comp (hland γ))
    simpa [Function.comp_def, he] using this

end RHTower
