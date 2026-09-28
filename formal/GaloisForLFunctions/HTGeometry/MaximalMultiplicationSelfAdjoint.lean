import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Multiplication by a real symbol on `L²(μ)` is self-adjoint

For an arbitrary measure `μ` and a real measurable symbol `φ`, multiplication by `φ` on its
maximal domain `{f ∈ L²(μ) : φ f ∈ L²(μ)}` is a densely defined self-adjoint operator `A`.

* Truncations `1_{|φ| ≤ n} φ^j f` lie in the domain; a vector orthogonal to all of them vanishes
  on every level set, so the domain is dense.
* If `y` lies in the adjoint domain with `A† y = h`, testing against the truncation
  `1_{|φ| ≤ n} (φ y - h)` gives `∫_{|φ| ≤ n} |φ y - h|² = 0`, so `φ y = h` almost everywhere; hence
  `A† ≤ A`, and symmetry gives equality.
* If `‖φ - ζ‖ ≥ c > 0` almost everywhere, multiplication by `(φ - ζ)⁻¹` is a bounded two-sided
  inverse of `A - ζ`, and for a finite measure `⟨1, (A - ζ)⁻¹ 1⟩ = ∫ (φ - ζ)⁻¹ dμ`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MeasureTheory Filter Set
open scoped InnerProductSpace ComplexConjugate LinearPMap

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The maximal domain of multiplication by a real symbol `φ` on `L²(μ)`. -/
def maximalMulDomain (μ : Measure α) (φ : α → ℝ) : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f | MemLp (fun x => (φ x : ℂ) * (f : α → ℂ) x) 2 μ}
  zero_mem' := by
    change MemLp _ 2 μ
    refine (MemLp.zero (ε := ℂ)).ae_eq ?_
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
    show (0 : α → ℂ) x = (φ x : ℂ) * ((0 : Lp ℂ 2 μ) : α → ℂ) x
    rw [hx]; simp
  add_mem' := by
    intro f g hf hg
    change MemLp _ 2 μ
    refine (MemLp.add hf hg).ae_eq ?_
    filter_upwards [Lp.coeFn_add f g] with x hx
    show (φ x : ℂ) * (f : α → ℂ) x + (φ x : ℂ) * (g : α → ℂ) x =
      (φ x : ℂ) * ((f + g : Lp ℂ 2 μ) : α → ℂ) x
    rw [hx, Pi.add_apply, mul_add]
  smul_mem' := by
    intro c f hf
    change MemLp _ 2 μ
    refine (MemLp.const_smul hf c).ae_eq ?_
    filter_upwards [Lp.coeFn_smul c f] with x hx
    show c • ((φ x : ℂ) * (f : α → ℂ) x) = (φ x : ℂ) * ((c • f : Lp ℂ 2 μ) : α → ℂ) x
    rw [hx, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    ring

theorem memLp_of_mem_maximalMulDomain {φ : α → ℝ} {f : Lp ℂ 2 μ}
    (hf : f ∈ maximalMulDomain μ φ) : MemLp (fun x => (φ x : ℂ) * (f : α → ℂ) x) 2 μ := hf

/-- Multiplication by a real symbol on its maximal domain in `L²(μ)`. -/
def maximalMul (μ : Measure α) (φ : α → ℝ) : Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ where
  domain := maximalMulDomain μ φ
  toFun :=
    { toFun := fun f => (memLp_of_mem_maximalMulDomain f.2).toLp _
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_of_mem_maximalMulDomain (f + g).2),
          Lp.coeFn_add ((memLp_of_mem_maximalMulDomain f.2).toLp _)
            ((memLp_of_mem_maximalMulDomain g.2).toLp _),
          MemLp.coeFn_toLp (memLp_of_mem_maximalMulDomain f.2),
          MemLp.coeFn_toLp (memLp_of_mem_maximalMulDomain g.2),
          Lp.coeFn_add (f : Lp ℂ 2 μ) g] with x h1 h2 h3 h4 h5
        rw [h1, h2, Pi.add_apply, h3, h4, Submodule.coe_add, h5, Pi.add_apply, mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_of_mem_maximalMulDomain (c • f).2),
          Lp.coeFn_smul c ((memLp_of_mem_maximalMulDomain f.2).toLp _),
          MemLp.coeFn_toLp (memLp_of_mem_maximalMulDomain f.2),
          Lp.coeFn_smul c (f : Lp ℂ 2 μ)] with x h1 h2 h3 h4
        rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, Submodule.coe_smul, h4, Pi.smul_apply,
          smul_eq_mul, smul_eq_mul]
        ring }

theorem maximalMul_domain (φ : α → ℝ) : (maximalMul μ φ).domain = maximalMulDomain μ φ := rfl

theorem maximalMul_coeFn (φ : α → ℝ) (f : (maximalMul μ φ).domain) :
    ((maximalMul μ φ f : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ] fun x => (φ x : ℂ) * (f : α → ℂ) x :=
  MemLp.coeFn_toLp (memLp_of_mem_maximalMulDomain f.2)

/-- A real multiplication operator is symmetric. -/
theorem maximalMul_isFormalAdjoint (φ : α → ℝ) :
    (maximalMul μ φ).IsFormalAdjoint (maximalMul μ φ) := by
  intro f g
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [maximalMul_coeFn φ f, maximalMul_coeFn φ g] with x h1 h2
  rw [h1, h2]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

/-! ## Cutoffs -/

/-- The level set `{|φ| ≤ n}`. -/
def mulCutoffSet (φ : α → ℝ) (n : ℕ) : Set α := {x | |φ x| ≤ n}

theorem measurableSet_mulCutoffSet {φ : α → ℝ} (hφ : Measurable φ) (n : ℕ) :
    MeasurableSet (mulCutoffSet φ n) :=
  measurableSet_le (continuous_abs.measurable.comp hφ) measurable_const

omit [MeasurableSpace α] in
theorem exists_mem_mulCutoffSet (φ : α → ℝ) (x : α) : ∃ n : ℕ, x ∈ mulCutoffSet φ n := by
  obtain ⟨n, hn⟩ := exists_nat_ge |φ x|
  exact ⟨n, hn⟩

/-- A function vanishing almost everywhere on every level set vanishes almost everywhere. -/
theorem ae_of_forall_mulCutoffSet {φ : α → ℝ} {p : α → Prop}
    (h : ∀ n : ℕ, ∀ᵐ x ∂μ, x ∈ mulCutoffSet φ n → p x) : ∀ᵐ x ∂μ, p x := by
  filter_upwards [ae_all_iff.mpr h] with x hx
  obtain ⟨n, hn⟩ := exists_mem_mulCutoffSet φ x
  exact hx n hn

omit [MeasurableSpace α] in
/-- A bounded symbol supported on `{|φ| ≤ n}` times `φ^j` is bounded by `n^j`. -/
theorem norm_indicator_mul_pow_le (φ : α → ℝ) (n : ℕ) (j : ℕ) (x : α) :
    ‖(mulCutoffSet φ n).indicator (fun y => (φ y : ℂ) ^ j) x‖ ≤ (n : ℝ) ^ j := by
  by_cases hx : x ∈ mulCutoffSet φ n
  · rw [indicator_of_mem hx, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hx j
  · rw [indicator_of_notMem hx, norm_zero]; positivity

theorem measurable_indicator_mul_pow {φ : α → ℝ} (hφ : Measurable φ) (n j : ℕ) :
    Measurable ((mulCutoffSet φ n).indicator (fun y => (φ y : ℂ) ^ j)) :=
  (by fun_prop : Measurable fun y => (φ y : ℂ) ^ j).indicator (measurableSet_mulCutoffSet hφ n)

/-- Truncation to `{|φ| ≤ n}` followed by multiplication by `φ^j`, as a bounded operator. -/
def mulCutoff {φ : α → ℝ} (hφ : Measurable φ) (n j : ℕ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  lpBoundedMulCLM (measurable_indicator_mul_pow hφ n j) (by positivity)
    (norm_indicator_mul_pow_le φ n j)

theorem mulCutoff_coeFn {φ : α → ℝ} (hφ : Measurable φ) (n j : ℕ) (f : Lp ℂ 2 μ) :
    ((mulCutoff (μ := μ) hφ n j f : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ]
      fun x => (mulCutoffSet φ n).indicator (fun y => (φ y : ℂ) ^ j) x * (f : α → ℂ) x :=
  lpBoundedMulCLM_coeFn _ _ _ f

/-- A truncated vector lies in the maximal domain. -/
theorem mulCutoff_mem_domain {φ : α → ℝ} (hφ : Measurable φ) (n j : ℕ) (f : Lp ℂ 2 μ) :
    mulCutoff (μ := μ) hφ n j f ∈ maximalMulDomain μ φ := by
  change MemLp _ 2 μ
  refine (memLp_mul_of_bound (measurable_indicator_mul_pow hφ n (j + 1)) (by positivity)
    (norm_indicator_mul_pow_le φ n (j + 1)) f).ae_eq ?_
  filter_upwards [mulCutoff_coeFn (μ := μ) hφ n j f] with x hx
  rw [hx]
  by_cases h : x ∈ mulCutoffSet φ n
  · rw [indicator_of_mem h, indicator_of_mem h]; ring
  · rw [indicator_of_notMem h, indicator_of_notMem h]; ring

theorem inner_self_eq_norm_sq_ofReal (z : ℂ) : inner ℂ z z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [RCLike.inner_apply, Complex.mul_conj']
  push_cast; rfl

/-- If the integral of a nonnegative function that is almost everywhere equal to an integrable
complex function vanishes, the function vanishes almost everywhere. -/
theorem ae_eq_zero_of_integral_ofReal_eq_zero {F : α → ℝ} {G : α → ℂ} (hG : Integrable G μ)
    (hGF : G =ᵐ[μ] fun x => (F x : ℂ)) (hF : ∀ x, 0 ≤ F x) (h0 : ∫ x, G x ∂μ = 0) :
    F =ᵐ[μ] 0 := by
  have hFi : Integrable F μ := by
    have := (hG.congr hGF).re
    simpa using this
  have hint : ∫ x, F x ∂μ = 0 := by
    have h := integral_congr_ae hGF
    rw [h0, integral_complex_ofReal] at h
    exact_mod_cast h.symm
  exact (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hF) hFi).mp hint

/-- **The maximal domain is dense.** A vector orthogonal to every truncation vanishes on every
level set `{|φ| ≤ n}`. -/
theorem dense_maximalMulDomain {φ : α → ℝ} (hφ : Measurable φ) :
    Dense (maximalMulDomain μ φ : Set (Lp ℂ 2 μ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro g hg
  rw [Submodule.mem_orthogonal] at hg
  have hzero : ∀ n : ℕ, ∀ᵐ x ∂μ, x ∈ mulCutoffSet φ n → (g : α → ℂ) x = 0 := by
    intro n
    have h := hg _ (mulCutoff_mem_domain (μ := μ) hφ n 0 g)
    rw [L2.inner_def] at h
    set F : α → ℝ := fun x => (mulCutoffSet φ n).indicator (fun y => ‖(g : α → ℂ) y‖ ^ 2) x
    have hGF : (fun x => inner ℂ ((mulCutoff (μ := μ) hφ n 0 g : Lp ℂ 2 μ) x)
        ((g : α → ℂ) x)) =ᵐ[μ] fun x => (F x : ℂ) := by
      filter_upwards [mulCutoff_coeFn (μ := μ) hφ n 0 g] with x hx
      rw [hx]
      by_cases hmem : x ∈ mulCutoffSet φ n
      · simp only [F, indicator_of_mem hmem, pow_zero, one_mul]
        exact inner_self_eq_norm_sq_ofReal _
      · simp [F, indicator_of_notMem hmem]
    have hF := ae_eq_zero_of_integral_ofReal_eq_zero (L2.integrable_inner _ _) hGF
      (fun x => by simp only [F]; exact indicator_nonneg (fun _ _ => by positivity) _) h
    filter_upwards [hF] with x hx hmem
    simp only [F, indicator_of_mem hmem, Pi.zero_apply] at hx
    simpa using hx
  exact Lp.eq_zero_iff_ae_eq_zero.mpr (ae_of_forall_mulCutoffSet hzero)

/-- **The adjoint acts by the same multiplication.** -/
theorem maximalMul_adjoint_ae {φ : α → ℝ} (hφ : Measurable φ)
    (y : (maximalMul μ φ)†.domain) :
    (fun x => (φ x : ℂ) * (y : α → ℂ) x) =ᵐ[μ] (((maximalMul μ φ)† y : Lp ℂ 2 μ) : α → ℂ) := by
  set h : Lp ℂ 2 μ := (maximalMul μ φ)† y
  have hd : Dense ((maximalMul μ φ).domain : Set (Lp ℂ 2 μ)) := dense_maximalMulDomain hφ
  have hformal := LinearPMap.adjoint_isFormalAdjoint (T := maximalMul μ φ) hd
  have hzero : ∀ n : ℕ, ∀ᵐ x ∂μ, x ∈ mulCutoffSet φ n →
      (φ x : ℂ) * (y : α → ℂ) x - (h : α → ℂ) x = 0 := by
    intro n
    set f : Lp ℂ 2 μ := mulCutoff (μ := μ) hφ n 1 y - mulCutoff (μ := μ) hφ n 0 h
    have hf : f ∈ maximalMulDomain μ φ :=
      sub_mem (mulCutoff_mem_domain hφ n 1 _) (mulCutoff_mem_domain hφ n 0 _)
    have key := hformal y ⟨f, hf⟩
    change inner ℂ h f = inner ℂ (y : Lp ℂ 2 μ) (maximalMul μ φ ⟨f, hf⟩) at key
    rw [L2.inner_def, L2.inner_def] at key
    have h0 : ∫ x, (inner ℂ ((y : Lp ℂ 2 μ) x) ((maximalMul μ φ ⟨f, hf⟩ : Lp ℂ 2 μ) x) -
        inner ℂ ((h : α → ℂ) x) ((f : α → ℂ) x)) ∂μ = 0 := by
      rw [integral_sub (L2.integrable_inner _ _) (L2.integrable_inner _ _), key, sub_self]
    set F : α → ℝ := fun x => (mulCutoffSet φ n).indicator
      (fun z => ‖(φ z : ℂ) * (y : α → ℂ) z - (h : α → ℂ) z‖ ^ 2) x
    have hGF : (fun x => inner ℂ ((y : Lp ℂ 2 μ) x) ((maximalMul μ φ ⟨f, hf⟩ : Lp ℂ 2 μ) x) -
        inner ℂ ((h : α → ℂ) x) ((f : α → ℂ) x)) =ᵐ[μ] fun x => (F x : ℂ) := by
      filter_upwards [maximalMul_coeFn (μ := μ) φ ⟨f, hf⟩, Lp.coeFn_sub
        (mulCutoff (μ := μ) hφ n 1 y) (mulCutoff (μ := μ) hφ n 0 h),
        mulCutoff_coeFn (μ := μ) hφ n 1 y, mulCutoff_coeFn (μ := μ) hφ n 0 h] with x h1 h2 h3 h4
      rw [h1]
      change inner ℂ ((y : α → ℂ) x) ((φ x : ℂ) * (f : α → ℂ) x) -
        inner ℂ ((h : α → ℂ) x) ((f : α → ℂ) x) = _
      rw [h2, Pi.sub_apply, h3, h4]
      by_cases hmem : x ∈ mulCutoffSet φ n
      · simp only [F, indicator_of_mem hmem, pow_one, pow_zero, one_mul]
        rw [← inner_self_eq_norm_sq_ofReal]
        simp only [RCLike.inner_apply, map_sub, map_mul, Complex.conj_ofReal]
        ring
      · simp [F, indicator_of_notMem hmem]
    have hF := ae_eq_zero_of_integral_ofReal_eq_zero
      ((L2.integrable_inner _ _).sub (L2.integrable_inner _ _)) hGF
      (fun x => by simp only [F]; exact indicator_nonneg (fun _ _ => by positivity) _) h0
    filter_upwards [hF] with x hx hmem
    simp only [F, indicator_of_mem hmem, Pi.zero_apply] at hx
    simpa using hx
  filter_upwards [ae_of_forall_mulCutoffSet hzero] with x hx
  exact sub_eq_zero.mp hx

theorem maximalMul_adjoint_le {φ : α → ℝ} (hφ : Measurable φ) :
    (maximalMul μ φ)† ≤ maximalMul μ φ := by
  refine ⟨fun y hy => ?_, fun y z hyz => ?_⟩
  · change MemLp _ 2 μ
    exact (Lp.memLp ((maximalMul μ φ)† ⟨y, hy⟩)).ae_eq (maximalMul_adjoint_ae hφ ⟨y, hy⟩).symm
  · apply Lp.ext
    filter_upwards [maximalMul_adjoint_ae hφ y, maximalMul_coeFn φ z] with x h1 h2
    rw [← h1, h2, hyz]

/-- **Multiplication by a real measurable symbol on its maximal domain is self-adjoint.** -/
theorem maximalMul_isSelfAdjoint {φ : α → ℝ} (hφ : Measurable φ) :
    IsSelfAdjoint (maximalMul μ φ) := by
  rw [LinearPMap.isSelfAdjoint_def]
  have hd : Dense ((maximalMul μ φ).domain : Set (Lp ℂ 2 μ)) := dense_maximalMulDomain hφ
  exact le_antisymm (maximalMul_adjoint_le hφ) ((maximalMul_isFormalAdjoint φ).le_adjoint hd)

/-! ## The resolvent -/

/-- The resolvent symbol `(φ - ζ)⁻¹`, set to zero where `‖φ - ζ‖ < c`. -/
def resolventSymbol (φ : α → ℝ) (ζ : ℂ) (c : ℝ) (x : α) : ℂ :=
  if c ≤ ‖(φ x : ℂ) - ζ‖ then ((φ x : ℂ) - ζ)⁻¹ else 0

omit [MeasurableSpace α] in
theorem norm_resolventSymbol_le (φ : α → ℝ) (ζ : ℂ) {c : ℝ} (hc : 0 < c) (x : α) :
    ‖resolventSymbol φ ζ c x‖ ≤ c⁻¹ := by
  unfold resolventSymbol
  split_ifs with h
  · rw [norm_inv]; exact inv_anti₀ hc h
  · rw [norm_zero]; positivity

theorem measurable_resolventSymbol {φ : α → ℝ} (hφ : Measurable φ) (ζ : ℂ) (c : ℝ) :
    Measurable (resolventSymbol φ ζ c) := by
  unfold resolventSymbol
  refine Measurable.ite ?_ (by fun_prop) measurable_const
  exact measurableSet_le measurable_const (by fun_prop)

omit [MeasurableSpace α] in
theorem sub_mul_resolventSymbol (φ : α → ℝ) (ζ : ℂ) {c : ℝ} (hc : 0 < c) {x : α}
    (hx : c ≤ ‖(φ x : ℂ) - ζ‖) : ((φ x : ℂ) - ζ) * resolventSymbol φ ζ c x = 1 := by
  have hne : (φ x : ℂ) - ζ ≠ 0 := fun h => by rw [h, norm_zero] at hx; linarith
  rw [resolventSymbol, if_pos hx, mul_inv_cancel₀ hne]

omit [MeasurableSpace α] in
theorem norm_mul_resolventSymbol_le (φ : α → ℝ) (ζ : ℂ) {c : ℝ} (hc : 0 < c) (x : α) :
    ‖(φ x : ℂ) * resolventSymbol φ ζ c x‖ ≤ 1 + ‖ζ‖ * c⁻¹ := by
  by_cases hx : c ≤ ‖(φ x : ℂ) - ζ‖
  · rw [show (φ x : ℂ) * resolventSymbol φ ζ c x =
        ((φ x : ℂ) - ζ) * resolventSymbol φ ζ c x + ζ * resolventSymbol φ ζ c x by ring,
      sub_mul_resolventSymbol φ ζ hc hx]
    calc ‖(1 : ℂ) + ζ * resolventSymbol φ ζ c x‖
        ≤ ‖(1 : ℂ)‖ + ‖ζ‖ * ‖resolventSymbol φ ζ c x‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ 1 + ‖ζ‖ * c⁻¹ := by
          rw [norm_one]; gcongr; exact norm_resolventSymbol_le φ ζ hc x
  · rw [resolventSymbol, if_neg hx, mul_zero, norm_zero]; positivity

/-- Multiplication by the resolvent symbol, a bounded operator of norm at most `1/c`. -/
def mulResolvent {φ : α → ℝ} (hφ : Measurable φ) (ζ : ℂ) {c : ℝ} (hc : 0 < c) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  lpBoundedMulCLM (measurable_resolventSymbol hφ ζ c) (inv_nonneg.mpr hc.le)
    (norm_resolventSymbol_le φ ζ hc)

theorem mulResolvent_coeFn {φ : α → ℝ} (hφ : Measurable φ) (ζ : ℂ) {c : ℝ} (hc : 0 < c)
    (f : Lp ℂ 2 μ) :
    ((mulResolvent (μ := μ) hφ ζ hc f : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ]
      fun x => resolventSymbol φ ζ c x * (f : α → ℂ) x :=
  lpBoundedMulCLM_coeFn _ _ _ f

/-- The resolvent maps `L²(μ)` into the maximal domain. -/
theorem mulResolvent_mem_domain {φ : α → ℝ} (hφ : Measurable φ) (ζ : ℂ) {c : ℝ} (hc : 0 < c)
    (f : Lp ℂ 2 μ) : mulResolvent (μ := μ) hφ ζ hc f ∈ maximalMulDomain μ φ := by
  change MemLp _ 2 μ
  refine (memLp_mul_of_bound (φ := fun x => (φ x : ℂ) * resolventSymbol φ ζ c x)
    ((by fun_prop : Measurable fun x => (φ x : ℂ)).mul (measurable_resolventSymbol hφ ζ c))
    (by positivity) (norm_mul_resolventSymbol_le φ ζ hc) f).ae_eq ?_
  filter_upwards [mulResolvent_coeFn (μ := μ) hφ ζ hc f] with x hx
  rw [hx]; ring

/-- **The resolvent is a right inverse of `A - ζ`.** If `‖φ - ζ‖ ≥ c > 0` almost everywhere,
then `(A - ζ) R_ζ f = f` for every `f ∈ L²(μ)`. -/
theorem maximalMul_mulResolvent {φ : α → ℝ} (hφ : Measurable φ) {ζ : ℂ} {c : ℝ} (hc : 0 < c)
    (hae : ∀ᵐ x ∂μ, c ≤ ‖(φ x : ℂ) - ζ‖) (f : Lp ℂ 2 μ) :
    maximalMul μ φ ⟨mulResolvent (μ := μ) hφ ζ hc f, mulResolvent_mem_domain hφ ζ hc f⟩ -
      ζ • mulResolvent (μ := μ) hφ ζ hc f = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (maximalMul μ φ ⟨mulResolvent (μ := μ) hφ ζ hc f,
      mulResolvent_mem_domain hφ ζ hc f⟩) (ζ • mulResolvent (μ := μ) hφ ζ hc f),
    maximalMul_coeFn (μ := μ) φ ⟨mulResolvent (μ := μ) hφ ζ hc f,
      mulResolvent_mem_domain hφ ζ hc f⟩,
    Lp.coeFn_smul ζ (mulResolvent (μ := μ) hφ ζ hc f), mulResolvent_coeFn (μ := μ) hφ ζ hc f,
    hae] with x h1 h2 h3 h4 h5
  rw [h1, Pi.sub_apply, h2, h3, Pi.smul_apply, smul_eq_mul]
  change (φ x : ℂ) * ((mulResolvent (μ := μ) hφ ζ hc f : Lp ℂ 2 μ) : α → ℂ) x -
    ζ * ((mulResolvent (μ := μ) hφ ζ hc f : Lp ℂ 2 μ) : α → ℂ) x = _
  rw [h4, ← sub_mul, ← mul_assoc, sub_mul_resolventSymbol φ ζ hc h5, one_mul]

/-- **The resolvent is a left inverse of `A - ζ`.** `R_ζ (A - ζ) g = g` on the maximal domain. -/
theorem mulResolvent_maximalMul {φ : α → ℝ} (hφ : Measurable φ) {ζ : ℂ} {c : ℝ} (hc : 0 < c)
    (hae : ∀ᵐ x ∂μ, c ≤ ‖(φ x : ℂ) - ζ‖) (g : (maximalMul μ φ).domain) :
    mulResolvent (μ := μ) hφ ζ hc (maximalMul μ φ g - ζ • (g : Lp ℂ 2 μ)) = g := by
  apply Lp.ext
  filter_upwards [mulResolvent_coeFn (μ := μ) hφ ζ hc (maximalMul μ φ g - ζ • (g : Lp ℂ 2 μ)),
    Lp.coeFn_sub (maximalMul μ φ g) (ζ • (g : Lp ℂ 2 μ)), maximalMul_coeFn (μ := μ) φ g,
    Lp.coeFn_smul ζ (g : Lp ℂ 2 μ), hae] with x h1 h2 h3 h4 h5
  rw [h1, h2, Pi.sub_apply, h3, h4, Pi.smul_apply, smul_eq_mul, ← sub_mul, ← mul_assoc,
    mul_comm (resolventSymbol φ ζ c x), sub_mul_resolventSymbol φ ζ hc h5, one_mul]

/-- **The resolvent matrix element of the constant vector.** For a finite measure,
`⟨1, R_ζ 1⟩ = ∫ (φ - ζ)⁻¹ dμ`. -/
theorem inner_const_mulResolvent_const [IsFiniteMeasure μ] {φ : α → ℝ} (hφ : Measurable φ)
    {ζ : ℂ} {c : ℝ} (hc : 0 < c) (hae : ∀ᵐ x ∂μ, c ≤ ‖(φ x : ℂ) - ζ‖) :
    inner ℂ (Lp.const 2 μ (1 : ℂ)) (mulResolvent (μ := μ) hφ ζ hc (Lp.const 2 μ (1 : ℂ))) =
      ∫ x, ((φ x : ℂ) - ζ)⁻¹ ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_const 2 μ (1 : ℂ), mulResolvent_coeFn (μ := μ) hφ ζ hc
    (Lp.const 2 μ (1 : ℂ)), hae] with x h1 h2 h3
  rw [h2, h1, Function.const_apply, resolventSymbol, if_pos h3]
  simp [RCLike.inner_apply]

end

end GaloisForLFunctions.HTGeometry
