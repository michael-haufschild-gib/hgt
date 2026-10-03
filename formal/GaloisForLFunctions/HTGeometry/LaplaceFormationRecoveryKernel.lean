import GaloisForLFunctions.HTGeometry.LaplaceFormationDefectHistory

/-!
# Recovery kernels, source reconstruction, fusion, and passive selection

The squared history amplitudes `K_ν(k, j) = (1 - a_k²) a_k^{2j}` form, for each response index, the
unique probability law on `ℕ₀` with geometric survival `K(k, j+1) = a_k² K(k, j)`; the kernel
recovers `a_k = √(1 - K_ν(k, 0))`, and the kernel family determines the source law `ν`
(Hausdorff/Laplace lattice uniqueness on `[0, ∞)`).

Half-line convolution multiplies Laplace responses, `L_{ν*μ}(n) = L_ν(n) L_μ(n)`, and the defect
splits in ordered first-failure layers `1 - (ac)² = (1 - a²) + a²(1 - c²)`; the three-channel
cascade is isometric with an exact contractive decoder, and every finite chain obeys the
telescoping ledger.  Finally, if a contraction recovers the Laplace response of a finite zero-mass
current `J` from the response of `J * ν`, then `J = 0`.
-/

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

namespace HalfLineFormationLaw

variable (ν : HalfLineFormationLaw)

/-! ## The recovery kernel -/

/-- **(LFD.25)** Recovery kernel `K_ν(k, j) = (1 - a_k²) a_k^{2j}`. -/
def recoveryKernel (k j : ℕ) : ℝ := (1 - ν.visible k ^ 2) * ν.visible k ^ (2 * j)

theorem recoveryKernel_eq_sq (k j : ℕ) : ν.recoveryKernel k j = ν.historyAmplitude k j ^ 2 := by
  rw [recoveryKernel, historyAmplitude, mul_pow, ← pow_mul, mul_comm j 2]
  have := ν.visible_sq_add_hidden_sq k
  congr 1
  linarith

theorem recoveryKernel_nonneg (k j : ℕ) : 0 ≤ ν.recoveryKernel k j := by
  rw [recoveryKernel_eq_sq]; positivity

/-- **Theorem 6.1** Each `K_ν(k, ·)` is a probability law on `ℕ₀`. -/
theorem hasSum_recoveryKernel (k : ℕ) : HasSum (ν.recoveryKernel k) 1 := by
  refine (ν.hasSum_historyAmplitude_sq k).congr_fun fun j => ?_
  rw [recoveryKernel_eq_sq]

/-- **(LFD.26)** The geometric survival equation `K(k, j+1) = a_k² K(k, j)`. -/
theorem recoveryKernel_succ (k j : ℕ) :
    ν.recoveryKernel k (j + 1) = ν.visible k ^ 2 * ν.recoveryKernel k j := by
  rw [recoveryKernel, recoveryKernel, mul_add, mul_one, pow_add]
  ring

/-- **Theorem 6.1, uniqueness.**  The recovery kernel is the unique probability law satisfying the
survival equation. -/
theorem recoveryKernel_unique (k : ℕ) (K : ℕ → ℝ) (hsum : HasSum K 1)
    (hsurv : ∀ j, K (j + 1) = ν.visible k ^ 2 * K j) : K = ν.recoveryKernel k := by
  have hgeom : ∀ j, K j = (ν.visible k ^ 2) ^ j * K 0 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [hsurv, ih, pow_succ]; ring
  have ha2 : ν.visible k ^ 2 < 1 := by nlinarith [ν.visible_pos k, ν.visible_lt_one k]
  have hg : HasSum K (K 0 * (1 - ν.visible k ^ 2)⁻¹) := by
    have := (hasSum_geometric_of_lt_one (sq_nonneg (ν.visible k)) ha2).mul_left (K 0)
    refine this.congr_fun fun j => ?_
    rw [hgeom j]; ring
  have hK0 : K 0 = 1 - ν.visible k ^ 2 := by
    have h := hsum.unique hg
    have hne : (1 - ν.visible k ^ 2) ≠ 0 := by linarith
    field_simp at h
    linarith
  funext j
  rw [hgeom j, hK0, recoveryKernel, ← pow_mul, mul_comm (2 : ℕ) j, pow_mul]
  ring

/-- **(LFD.27)** The kernel reconstructs the visible amplitude: `a_k = √(1 - K_ν(k, 0))`. -/
theorem visible_eq_sqrt_recoveryKernel (k : ℕ) :
    ν.visible k = Real.sqrt (1 - ν.recoveryKernel k 0) := by
  rw [recoveryKernel, mul_zero, pow_zero, mul_one, sub_sub_cancel,
    Real.sqrt_sq (ν.visible_pos k).le]

/-- **(LFD.28)** Under `y = e^{-x}` the Laplace response is the Hausdorff moment sequence of the
pushed-forward law on `[0, 1]`. -/
theorem laplace_eq_moment (n : ℕ) :
    ν.laplace n = ∫ y, y ^ n ∂(Measure.map (fun x : ℝ => Real.exp (-x)) ν.measure) := by
  rw [laplace, integral_map (by fun_prop) (by fun_prop)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  change Real.exp (-(n * x)) = Real.exp (-x) ^ n
  rw [← Real.exp_nat_mul]
  ring_nf

/-- **Theorem 6.1, reconstruction.**  The family of recovery kernels determines the source law. -/
theorem measure_eq_of_recoveryKernel_eq (μ : HalfLineFormationLaw)
    (h : ∀ k j, ν.recoveryKernel k j = μ.recoveryKernel k j) : ν.measure = μ.measure := by
  refine measure_eq_of_laplace_nat_eq ν.support μ.support one_pos fun n => ?_
  have hform : ∀ ρ : HalfLineFormationLaw, ∀ n : ℕ,
      ∫ r, Real.exp (-((n : ℝ) * 1) * r) ∂ρ.measure = ρ.laplace n := by
    intro ρ n
    rw [laplace]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [mul_one, neg_mul]
  rw [hform ν n, hform μ n]
  rcases n with _ | k
  · rw [ν.laplace_zero, μ.laplace_zero]
  · change ν.visible k = μ.visible k
    rw [ν.visible_eq_sqrt_recoveryKernel, μ.visible_eq_sqrt_recoveryKernel, h]

end HalfLineFormationLaw

/-! ## Laplace response of finite half-line measures and convolution -/

/-- Laplace response `∫ e^{-nx} dμ` of a measure on the line. -/
def lineLaplace (μ : Measure ℝ) (n : ℕ) : ℝ := ∫ x, Real.exp (-(n * x)) ∂μ

theorem integrable_exp_neg_of_support {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : μ (Ici 0)ᶜ = 0)
    (n : ℕ) : Integrable (fun x => Real.exp (-(n * x))) μ := by
  refine Integrable.of_bound (by fun_prop : Continuous fun x : ℝ =>
    Real.exp (-(n * x))).aestronglyMeasurable 1 ?_
  have hae : ∀ᵐ x ∂μ, 0 ≤ x := by
    rw [ae_iff]; refine measure_mono_null (fun x hx => ?_) hμ; simpa using hx
  filter_upwards [hae] with x hx
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff, neg_nonpos]
  positivity

theorem conv_support {μ ν : Measure ℝ} [SFinite μ] [SFinite ν] (hμ : μ (Ici 0)ᶜ = 0)
    (hν : ν (Ici 0)ᶜ = 0) : (μ.conv ν) (Ici 0)ᶜ = 0 := by
  rw [Measure.conv, Measure.map_apply (by fun_prop) measurableSet_Ici.compl]
  have hsub : (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' (Ici 0)ᶜ ⊆
      ((Ici 0)ᶜ ×ˢ univ) ∪ (univ ×ˢ (Ici 0)ᶜ) := by
    intro p hp
    simp only [mem_preimage, mem_compl_iff, mem_Ici, not_le] at hp
    by_contra hc
    simp only [mem_union, mem_prod, mem_compl_iff, mem_Ici, not_le, mem_univ, and_true,
      true_and, not_or, not_lt] at hc
    linarith [hc.1, hc.2]
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · rw [Measure.prod_prod, hμ, zero_mul]
  · rw [Measure.prod_prod, hν, mul_zero]

/-- **(LFD.8), (LFD.30)** Convolution multiplies Laplace responses. -/
theorem lineLaplace_conv {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (n : ℕ) :
    lineLaplace (μ.conv ν) n = lineLaplace μ n * lineLaplace ν n := by
  rw [lineLaplace, Measure.conv, integral_map (by fun_prop) (by fun_prop)]
  rw [lineLaplace, lineLaplace, ← integral_prod_mul]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  change Real.exp (-(n * (p.1 + p.2))) = Real.exp (-(n * p.1)) * Real.exp (-(n * p.2))
  rw [← Real.exp_add]
  ring_nf

namespace HalfLineFormationLaw

variable (ν : HalfLineFormationLaw)

theorem laplace_eq_lineLaplace (n : ℕ) : ν.laplace n = lineLaplace ν.measure n := rfl

/-- The convolution of two nontrivial half-line formation laws. -/
def conv (μ : HalfLineFormationLaw) : HalfLineFormationLaw where
  measure := ν.measure.conv μ.measure
  isProbability := by
    constructor
    rw [Measure.conv, Measure.map_apply (by fun_prop) MeasurableSet.univ, preimage_univ,
      ← univ_prod_univ, Measure.prod_prod, measure_univ, measure_univ, one_mul]
  support := conv_support ν.support μ.support
  ne_dirac := by
    intro h
    have h1 : lineLaplace (ν.measure.conv μ.measure) 1 = 1 := by
      rw [h, lineLaplace, integral_dirac]; simp
    rw [lineLaplace_conv] at h1
    have hν := ν.laplace_one_lt_one
    have hμ := μ.laplace_one_lt_one
    have hν0 := ν.laplace_pos 1
    have hμ0 := μ.laplace_pos 1
    rw [← laplace_eq_lineLaplace, ← laplace_eq_lineLaplace] at h1
    nlinarith

theorem visible_conv (μ : HalfLineFormationLaw) (k : ℕ) :
    (ν.conv μ).visible k = ν.visible k * μ.visible k :=
  lineLaplace_conv (k + 1)

/-- **Theorem 7.1 (LFD.31)** Ordered defect conservation under source fusion. -/
theorem defect_conv (μ : HalfLineFormationLaw) (k : ℕ) :
    1 - (ν.conv μ).visible k ^ 2 = (1 - ν.visible k ^ 2) + ν.visible k ^ 2 * (1 - μ.visible k ^ 2) := by
  rw [visible_conv]; ring

/-- Cascade fibre space `ℓ^∞(ℂ³)`. -/
abbrev CascadeSpace := lp (fun _ : ℕ => EuclideanSpace ℂ (Fin 3)) ⊤

theorem norm_euclidean_three (u v w : ℂ) :
    ‖(WithLp.toLp 2 ![u, v, w] : EuclideanSpace ℂ (Fin 3))‖ =
      Real.sqrt (‖u‖ ^ 2 + ‖v‖ ^ 2 + ‖w‖ ^ 2) := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  rfl

theorem norm_cascade_fibre (μ : HalfLineFormationLaw) (k : ℕ) (z : ℂ) :
    ‖(WithLp.toLp 2 ![(ν.visible k * μ.visible k : ℝ) * z, (ν.visible k * μ.hidden k : ℝ) * z,
        (ν.hidden k : ℝ) * z] : EuclideanSpace ℂ (Fin 3))‖ = ‖z‖ := by
  rw [norm_euclidean_three]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have h1 := ν.visible_sq_add_hidden_sq k
  have h2 := μ.visible_sq_add_hidden_sq k
  have : (ν.visible k) ^ 2 * (μ.visible k) ^ 2 * ‖z‖ ^ 2 +
      (ν.visible k) ^ 2 * (μ.hidden k) ^ 2 * ‖z‖ ^ 2 + (ν.hidden k) ^ 2 * ‖z‖ ^ 2 = ‖z‖ ^ 2 := by
    have : (ν.visible k) ^ 2 * ((μ.visible k) ^ 2 + (μ.hidden k) ^ 2) + (ν.hidden k) ^ 2 = 1 := by
      rw [h2, mul_one, h1]
    linear_combination (‖z‖ ^ 2) * this
  rw [this, Real.sqrt_sq (norm_nonneg _)]

/-- **(LFD.32)** The three-channel cascade `b ↦ (a c b, a e b, d b)` is isometric. -/
def cascadeEncoder (μ : HalfLineFormationLaw) (b : LaplaceResponseSpace) : CascadeSpace :=
  ⟨fun k => WithLp.toLp 2 ![(ν.visible k * μ.visible k : ℝ) * b k,
      (ν.visible k * μ.hidden k : ℝ) * b k, (ν.hidden k : ℝ) * b k],
    memℓp_infty ⟨‖b‖, by
      rintro _ ⟨k, rfl⟩
      dsimp only
      rw [ν.norm_cascade_fibre]
      exact lp.norm_apply_le_norm (by simp) b k⟩⟩

theorem norm_cascadeEncoder (μ : HalfLineFormationLaw) (b : LaplaceResponseSpace) :
    ‖ν.cascadeEncoder μ b‖ = ‖b‖ := by
  rw [lp.norm_eq_ciSup, lp.norm_eq_ciSup]
  congr 1
  funext k
  exact ν.norm_cascade_fibre μ k (b k)

theorem cascade_decode_le (μ : HalfLineFormationLaw) (k : ℕ) (y : EuclideanSpace ℂ (Fin 3)) :
    ‖((ν.visible k * μ.visible k : ℝ) : ℂ) * y.ofLp 0 + ((ν.visible k * μ.hidden k : ℝ) : ℂ) * y.ofLp 1 +
        ((ν.hidden k : ℝ) : ℂ) * y.ofLp 2‖ ≤ ‖y‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  have h1 := ν.visible_sq_add_hidden_sq k
  have h2 := μ.visible_sq_add_hidden_sq k
  set p := ν.visible k * μ.visible k
  set q := ν.visible k * μ.hidden k
  set r := ν.hidden k
  have hpqr : p ^ 2 + q ^ 2 + r ^ 2 = 1 := by
    simp only [p, q, r, mul_pow]
    have : ν.visible k ^ 2 * (μ.visible k ^ 2 + μ.hidden k ^ 2) + ν.hidden k ^ 2 = 1 := by
      rw [h2, mul_one, h1]
    linarith
  refine norm_add₃_le.trans ?_
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  apply Real.le_sqrt_of_sq_le
  set A := ‖y.ofLp 0‖
  set B := ‖y.ofLp 1‖
  set C := ‖y.ofLp 2‖
  have hA := norm_nonneg (y.ofLp 0)
  have hB := norm_nonneg (y.ofLp 1)
  have hC := norm_nonneg (y.ofLp 2)
  have hp2 : |p| ^ 2 = p ^ 2 := sq_abs p
  have hq2 : |q| ^ 2 = q ^ 2 := sq_abs q
  have hr2 : |r| ^ 2 = r ^ 2 := sq_abs r
  nlinarith [sq_nonneg (|p| * B - |q| * A), sq_nonneg (|p| * C - |r| * A),
    sq_nonneg (|q| * C - |r| * B), abs_nonneg p, abs_nonneg q, abs_nonneg r]

/-- **(LFD.32a)** The fibrewise row decoder of the cascade. -/
def cascadeDecoder (μ : HalfLineFormationLaw) (y : CascadeSpace) : LaplaceResponseSpace :=
  ⟨fun k => ((ν.visible k * μ.visible k : ℝ) : ℂ) * (y k).ofLp 0 +
      ((ν.visible k * μ.hidden k : ℝ) : ℂ) * (y k).ofLp 1 + ((ν.hidden k : ℝ) : ℂ) * (y k).ofLp 2,
    memℓp_infty ⟨‖y‖, by
      rintro _ ⟨k, rfl⟩
      exact (ν.cascade_decode_le μ k (y k)).trans (lp.norm_apply_le_norm (by simp) y k)⟩⟩

theorem norm_cascadeDecoder_le (μ : HalfLineFormationLaw) (y : CascadeSpace) :
    ‖ν.cascadeDecoder μ y‖ ≤ ‖y‖ :=
  lp.norm_le_of_forall_le (norm_nonneg _) fun k =>
    (ν.cascade_decode_le μ k (y k)).trans (lp.norm_apply_le_norm (by simp) y k)

theorem cascadeDecoder_cascadeEncoder (μ : HalfLineFormationLaw) (b : LaplaceResponseSpace) :
    ν.cascadeDecoder μ (ν.cascadeEncoder μ b) = b := by
  apply lp.ext
  funext k
  change ((ν.visible k * μ.visible k : ℝ) : ℂ) * (((ν.visible k * μ.visible k : ℝ) : ℂ) * b k) +
    ((ν.visible k * μ.hidden k : ℝ) : ℂ) * (((ν.visible k * μ.hidden k : ℝ) : ℂ) * b k) +
      ((ν.hidden k : ℝ) : ℂ) * (((ν.hidden k : ℝ) : ℂ) * b k) = b k
  have h1 := ν.visible_sq_add_hidden_sq k
  have h2 := μ.visible_sq_add_hidden_sq k
  have hc : ((ν.visible k * μ.visible k : ℝ) : ℂ) ^ 2 + ((ν.visible k * μ.hidden k : ℝ) : ℂ) ^ 2 +
      ((ν.hidden k : ℝ) : ℂ) ^ 2 = 1 := by
    have : (ν.visible k * μ.visible k) ^ 2 + (ν.visible k * μ.hidden k) ^ 2 + ν.hidden k ^ 2 = 1 := by
      have : ν.visible k ^ 2 * (μ.visible k ^ 2 + μ.hidden k ^ 2) + ν.hidden k ^ 2 = 1 := by
        rw [h2, mul_one, h1]
      linear_combination this
    exact_mod_cast this
  linear_combination (b k) * hc

end HalfLineFormationLaw

/-- **(LFD.33)** Telescoping ledger of a finite chain:
`1 - ∏_r a_r² = ∑_r (∏_{i<r} a_i²)(1 - a_r²)`. -/
theorem chain_defect_ledger (a : ℕ → ℝ) (m : ℕ) :
    1 - ∏ r ∈ Finset.range m, a r ^ 2 =
      ∑ r ∈ Finset.range m, (∏ i ∈ Finset.range r, a i ^ 2) * (1 - a r ^ 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ, ← ih]
    ring

/-! ## Passive source selection -/

namespace HalfLineFormationLaw

variable (ν : HalfLineFormationLaw)

/-- Complete Laplace response `(T μ)_k = ∫ e^{-(k+1)x} dμ` of a finite half-line measure. -/
def responseOf (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ (Ici 0)ᶜ = 0) : LaplaceResponseSpace :=
  ⟨fun k => (lineLaplace μ (k + 1) : ℂ), memℓp_infty ⟨(μ univ).toReal, by
    rintro _ ⟨k, rfl⟩
    dsimp only
    rw [Complex.norm_real, lineLaplace]
    refine (norm_integral_le_of_norm_le_const (C := 1) ?_).trans (by simp [Measure.real])
    have hae : ∀ᵐ x ∂μ, 0 ≤ x := by
      rw [ae_iff]; refine measure_mono_null (fun x hx => ?_) hμ; simpa using hx
    filter_upwards [hae] with x hx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff, neg_nonpos]
    positivity⟩⟩

/-- **(LFD.8)** The response of `μ * ν` is the visible formation of the response of `μ`. -/
theorem responseOf_conv (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ (Ici 0)ᶜ = 0) :
    responseOf (μ.conv ν.measure) (conv_support hμ ν.support) =
      ν.visibleFormation (responseOf μ hμ) := by
  apply lp.ext
  funext k
  change (lineLaplace (μ.conv ν.measure) (k + 1) : ℂ) = (ν.visible k : ℂ) * lineLaplace μ (k + 1)
  rw [lineLaplace_conv]
  push_cast
  rw [mul_comm]
  rfl

/-- **(LFD.8), signed currents.**  For `J = μ₁ - μ₂`, `𝒯(J * ν) = A_ν 𝒯 J`. -/
theorem responseOf_sub_conv (μ₁ μ₂ : Measure ℝ) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (h₁ : μ₁ (Ici 0)ᶜ = 0) (h₂ : μ₂ (Ici 0)ᶜ = 0) :
    responseOf (μ₁.conv ν.measure) (conv_support h₁ ν.support) -
        responseOf (μ₂.conv ν.measure) (conv_support h₂ ν.support) =
      ν.visibleFormation (responseOf μ₁ h₁ - responseOf μ₂ h₂) := by
  rw [responseOf_conv ν μ₁ h₁, responseOf_conv ν μ₂ h₂]
  apply lp.ext; funext k
  change (ν.visible k : ℂ) * _ - (ν.visible k : ℂ) * _ = (ν.visible k : ℂ) * (_ - _)
  ring

/-- **(LFD.38)–(LFD.39) Passive source selection.**  Let `J = μ₁ - μ₂` be a finite zero-mass
current on `[0, ∞)`.  If a contraction `R` of the response space recovers the response of `J`
from the response of `J * ν`, then `J = 0`. -/
theorem passive_selection (μ₁ μ₂ : Measure ℝ) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (h₁ : μ₁ (Ici 0)ᶜ = 0) (h₂ : μ₂ (Ici 0)ᶜ = 0) (hmass : μ₁ univ = μ₂ univ)
    (R : LaplaceResponseSpace → LaplaceResponseSpace) (hR : ∀ x, ‖R x‖ ≤ ‖x‖)
    (hrec : R (responseOf (μ₁.conv ν.measure) (conv_support h₁ ν.support) -
        responseOf (μ₂.conv ν.measure) (conv_support h₂ ν.support)) =
      responseOf μ₁ h₁ - responseOf μ₂ h₂) :
    μ₁ = μ₂ := by
  rw [ν.responseOf_sub_conv μ₁ μ₂ h₁ h₂] at hrec
  have hzero := ν.eq_zero_of_visible_recovery R hR hrec
  refine measure_eq_of_laplace_nat_eq h₁ h₂ one_pos fun n => ?_
  rcases n with _ | k
  · simp only [Nat.cast_zero, zero_mul, neg_zero, Real.exp_zero, integral_const, smul_eq_mul,
      mul_one, Measure.real, hmass]
  · have hk := congrArg (fun y : LaplaceResponseSpace => y k) hzero
    change (lineLaplace μ₁ (k + 1) : ℂ) - lineLaplace μ₂ (k + 1) = 0 at hk
    have hk' : lineLaplace μ₁ (k + 1) = lineLaplace μ₂ (k + 1) := by
      exact_mod_cast sub_eq_zero.1 hk
    simp only [lineLaplace, mul_one] at hk' ⊢
    simpa only [neg_mul] using hk'

end HalfLineFormationLaw

end GaloisForLFunctions.HTGeometry
