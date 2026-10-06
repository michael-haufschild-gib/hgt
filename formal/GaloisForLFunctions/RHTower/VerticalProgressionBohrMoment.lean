import GaloisForLFunctions.RHTower.VerticalProgressionFirstMomentLimit
import GaloisForLFunctions.RHTower.VerticalProgressionSecondMomentLimit
import GaloisForLFunctions.RHTower.BohrOrbitClosureHaar

/-!
# The Bohr-twisted mollified first moment

For `θ ∈ ℝ^K`, a continuous `W : 𝕋^K → ℂ` and a weight `φ` supported in `[1, 2]`,

`S₁(W) = Σ_ℓ φ(ℓ/T) W(ℓθ̄) ζM_N(½ + i(αℓ + β))`.

**Theorem** (`tendsto_bohrMoment_div`). `S₁(W)/T → (∫ W dμ_H)(∫ φ)`, `μ_H` the Haar measure of
the orbit closure `H = cl ℤθ̄`.

**Proof.** For a character `W = e_m`, `e_m(ℓθ̄) = e(ℓ⟨m,θ⟩)` and `S₁(e_m)` is the twisted first
moment at `γ = ⟨m,θ⟩`, which tends to `[γ ∈ ℤ] T∫φ` (`tendsto_firstMoment_div`), while
`∫ e_m dμ_H = [⟨m, θ⟩ ∈ ℤ]`. Both sides are linear in `W`, so the limit holds on trigonometric
polynomials. A general `W` is a uniform limit of trigonometric polynomials (Stone–Weierstrass), and
`|S₁(W) − S₁(P)| ≤ ‖W − P‖_∞ Σφ|ζM| ≤ ‖W − P‖_∞ (Σφ)^{1/2} S₂^{1/2} = O(‖W − P‖_∞ T)`.
-/

open Complex MeasureTheory Set Filter Topology UnitAddTorus
open scoped BigOperators

namespace RHTower.VerticalAP

noncomputable section

open BohrOrbit

variable {K : ℕ}

/-- The orbit point `xθ̄` at real time `x`. -/
def orbitPt (θ : Fin K → ℝ) (x : ℝ) : UnitAddTorus (Fin K) :=
  fun i => ((x * θ i : ℝ) : UnitAddCircle)

/-- `⟨m, θ⟩`. -/
def pairing (m : Fin K → ℤ) (θ : Fin K → ℝ) : ℝ := ∑ i, (m i : ℝ) * θ i

theorem mFourier_orbitPt_int (θ : Fin K → ℝ) (m : Fin K → ℤ) (ℓ : ℤ) :
    mFourier m (orbitPt θ ℓ) = unitExp (ℓ * pairing m θ) := by
  simp only [mFourier, ContinuousMap.coe_mk, orbitPt, fourier_coe_apply, unitExp, pairing]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem mFourier_orbitPoint_eq_one_iff (θ : Fin K → ℝ) (m : Fin K → ℤ) :
    mFourier m (orbitPoint θ) = 1 ↔ ∃ j : ℤ, pairing m θ = j := by
  rw [mFourier_orbitPoint, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h1 : ((pairing m θ : ℝ) : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ hpi
      have e : 2 * Real.pi * Complex.I * ((pairing m θ : ℝ) : ℂ) =
          2 * Real.pi * Complex.I * ∑ i, (m i : ℂ) * θ i := by
        unfold pairing; push_cast; ring
      rw [e, hn]; ring
    exact_mod_cast h1
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    have : ∑ i, (m i : ℂ) * θ i = (j : ℂ) := by
      have := congrArg (fun x : ℝ => (x : ℂ)) hj
      simp only [pairing] at this; push_cast at this; exact this
    rw [this]; ring

/-- The Bohr-twisted mollified first moment `S₁(W)`. -/
def bohrMoment (φ : ℝ → ℝ) (W : C(UnitAddTorus (Fin K), ℂ)) (θ : Fin K → ℝ) (α β : ℝ) (N : ℕ)
    (T : ℝ) : ℂ :=
  latticeSum (fun x => (φ (x / T) : ℂ) * (W (orbitPt θ x) * apMollZeta N α β x)) 0

theorem bohrMoment_eq_sum {φ : ℝ → ℝ} (hsupp : Function.support φ ⊆ Icc 1 2)
    (W : C(UnitAddTorus (Fin K), ℂ)) (θ : Fin K → ℝ) (α β : ℝ) (N : ℕ) {T : ℝ} (hT : 0 < T) :
    bohrMoment φ W θ α β N T = ∑ ℓ ∈ Finset.Icc ⌈T⌉ ⌊2 * T⌋,
      (φ ((ℓ : ℝ) / T) : ℂ) * (W (orbitPt θ ℓ) * apMollZeta N α β ℓ) := by
  unfold bohrMoment
  rw [latticeSum_eq_sum (support_cutoff_subset (complex_support_subset hsupp) hT _)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp [unitExp]

theorem bohrMoment_add {φ : ℝ → ℝ} (hsupp : Function.support φ ⊆ Icc 1 2)
    (W₁ W₂ : C(UnitAddTorus (Fin K), ℂ)) (θ : Fin K → ℝ) (α β : ℝ) (N : ℕ) {T : ℝ} (hT : 0 < T) :
    bohrMoment φ (W₁ + W₂) θ α β N T = bohrMoment φ W₁ θ α β N T + bohrMoment φ W₂ θ α β N T := by
  rw [bohrMoment_eq_sum hsupp _ _ _ _ _ hT, bohrMoment_eq_sum hsupp _ _ _ _ _ hT,
    bohrMoment_eq_sum hsupp _ _ _ _ _ hT, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [ContinuousMap.add_apply]
  ring

theorem bohrMoment_sub {φ : ℝ → ℝ} (hsupp : Function.support φ ⊆ Icc 1 2)
    (W₁ W₂ : C(UnitAddTorus (Fin K), ℂ)) (θ : Fin K → ℝ) (α β : ℝ) (N : ℕ) {T : ℝ} (hT : 0 < T) :
    bohrMoment φ (W₁ - W₂) θ α β N T = bohrMoment φ W₁ θ α β N T - bohrMoment φ W₂ θ α β N T := by
  rw [bohrMoment_eq_sum hsupp _ _ _ _ _ hT, bohrMoment_eq_sum hsupp _ _ _ _ _ hT,
    bohrMoment_eq_sum hsupp _ _ _ _ _ hT, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [ContinuousMap.sub_apply]
  ring

theorem bohrMoment_smul {φ : ℝ → ℝ} (hsupp : Function.support φ ⊆ Icc 1 2) (c : ℂ)
    (W : C(UnitAddTorus (Fin K), ℂ)) (θ : Fin K → ℝ) (α β : ℝ) (N : ℕ) {T : ℝ} (hT : 0 < T) :
    bohrMoment φ (c • W) θ α β N T = c * bohrMoment φ W θ α β N T := by
  rw [bohrMoment_eq_sum hsupp _ _ _ _ _ hT, bohrMoment_eq_sum hsupp _ _ _ _ _ hT, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [ContinuousMap.smul_apply, smul_eq_mul]
  ring

theorem bohrMoment_zero (φ : ℝ → ℝ) (θ : Fin K → ℝ) (α β : ℝ) (N : ℕ) (T : ℝ) :
    bohrMoment φ 0 θ α β N T = 0 := by
  unfold bohrMoment latticeSum
  simp

/-- For a character, `S₁(e_m)` is the twisted first moment at `⟨m, θ⟩`. -/
theorem bohrMoment_mFourier (φ : ℝ → ℝ) (θ : Fin K → ℝ) (m : Fin K → ℤ) (α β : ℝ) (N : ℕ)
    (T : ℝ) :
    bohrMoment φ (mFourier m) θ α β N T =
      firstMoment (fun y => (φ y : ℂ)) α β (pairing m θ) N T := by
  unfold bohrMoment firstMoment latticeSum
  refine tsum_congr fun ℓ => ?_
  dsimp only
  rw [mFourier_orbitPt_int]
  simp only [mul_zero, unitExp, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  ring

open Classical in
/-- **The twisted first moment at any twist.** -/
theorem tendsto_firstMoment_div {φ : ℝ → ℂ} (hφ : ∀ k : ℕ, ContDiff ℝ k φ)
    (hsupp : Function.support φ ⊆ Icc 1 2) {α β θ : ℝ} (hα : 0 < α) (hθ0 : 0 < θ)
    (hθ : θ ≤ 1 / 2) (γ : ℝ) :
    Tendsto (fun T => firstMoment φ α β γ (molLen θ T) T / T) atTop
      (𝓝 (if ∃ j : ℤ, γ = j then ∫ x, φ x else 0)) := by
  split_ifs with h
  · obtain ⟨j, rfl⟩ := h
    exact tendsto_firstMoment_div_int hφ hsupp (β := β) hα hθ0 hθ j
  · push Not at h
    exact tendsto_firstMoment_div_of_not_int hφ hsupp hα hθ0 hθ h

/-- **Trigonometric polynomials.** -/
theorem tendsto_bohrMoment_div_of_mem_span {φ : ℝ → ℝ} (hφ : ∀ k : ℕ, ContDiff ℝ k φ)
    (hsupp : Function.support φ ⊆ Icc 1 2) (θ : Fin K → ℝ) {α β ϑ : ℝ} (hα : 0 < α)
    (hϑ0 : 0 < ϑ) (hϑ : ϑ ≤ 1 / 2) {P : C(UnitAddTorus (Fin K), ℂ)}
    (hP : P ∈ Submodule.span ℂ (Set.range (mFourier (d := Fin K)))) :
    Tendsto (fun T => bohrMoment φ P θ α β (molLen ϑ T) T / T) atTop
      (𝓝 ((∫ x, P x ∂(orbitHaar θ)) * ((∫ x, φ x : ℝ) : ℂ))) := by
  have hφC : ∀ k : ℕ, ContDiff ℝ k (fun y : ℝ => (φ y : ℂ)) := fun k =>
    Complex.ofRealCLM.contDiff.comp (hφ k)
  have hsuppC := complex_support_subset hsupp
  induction hP using Submodule.span_induction with
  | mem W hW =>
      obtain ⟨m, rfl⟩ := hW
      simp_rw [bohrMoment_mFourier]
      have h := tendsto_firstMoment_div hφC hsuppC (β := β) hα hϑ0 hϑ (pairing m θ)
      rw [integral_mFourier_orbitHaar]
      rw [integral_complex_ofReal] at h
      convert h using 2
      by_cases hj : ∃ j : ℤ, pairing m θ = j
      · rw [if_pos ((mFourier_orbitPoint_eq_one_iff θ m).mpr hj), if_pos hj, one_mul]
      · rw [if_neg (fun h' => hj ((mFourier_orbitPoint_eq_one_iff θ m).mp h')), if_neg hj,
          zero_mul]
  | zero =>
      simp only [bohrMoment_zero, zero_div, ContinuousMap.zero_apply, integral_zero, zero_mul]
      exact tendsto_const_nhds
  | add W₁ W₂ _ _ h₁ h₂ =>
      have hint₁ : Integrable (fun x => W₁ x) (orbitHaar θ) :=
        W₁.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hint₂ : Integrable (fun x => W₂ x) (orbitHaar θ) :=
        W₂.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      simp only [ContinuousMap.add_apply, integral_add hint₁ hint₂, add_mul]
      refine (h₁.add h₂).congr' ?_
      filter_upwards [eventually_gt_atTop 0] with T hT
      rw [bohrMoment_add hsupp _ _ _ _ _ _ hT, add_div]
  | smul c W _ h =>
      simp only [ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul, mul_assoc]
      refine (h.const_mul c).congr' ?_
      filter_upwards [eventually_gt_atTop 0] with T hT
      rw [bohrMoment_smul hsupp _ _ _ _ _ _ hT, mul_div_assoc]

/-! ## Uniform approximation -/

theorem secondMoment_eq_sum {φ : ℝ → ℝ} (hsupp : Function.support φ ⊆ Icc 1 2) (α β : ℝ)
    (N : ℕ) {T : ℝ} (hT : 0 < T) :
    secondMoment φ α β N T = ∑ ℓ ∈ Finset.Icc ⌈T⌉ ⌊2 * T⌋,
      φ ((ℓ : ℝ) / T) * ‖apMollZeta N α β ℓ‖ ^ 2 := by
  unfold secondMoment
  rw [tsum_eq_sum]
  intro ℓ hℓ
  have : φ ((ℓ : ℝ) / T) = 0 := by
    by_contra h
    apply hℓ
    obtain ⟨h1, h2⟩ := hsupp h
    rw [le_div_iff₀ hT] at h1
    rw [div_le_iff₀ hT] at h2
    rw [Finset.mem_Icc]
    exact ⟨Int.ceil_le.mpr (by linarith), Int.le_floor.mpr (by linarith)⟩
  rw [this, zero_mul]

/-- **Cauchy–Schwarz**: `Σ φ|ζM| ≤ (Σ φ)^{1/2} S₂^{1/2}`. -/
theorem sum_mul_norm_le_sqrt {φ : ℝ → ℝ} (hsupp : Function.support φ ⊆ Icc 1 2)
    (hφ0 : ∀ y, 0 ≤ φ y) (α β : ℝ) (N : ℕ) {T : ℝ} (hT : 0 < T) :
    ∑ ℓ ∈ Finset.Icc ⌈T⌉ ⌊2 * T⌋, φ ((ℓ : ℝ) / T) * ‖apMollZeta N α β ℓ‖ ≤
      Real.sqrt (∑ ℓ ∈ Finset.Icc ⌈T⌉ ⌊2 * T⌋, φ ((ℓ : ℝ) / T)) *
        Real.sqrt (secondMoment φ α β N T) := by
  rw [secondMoment_eq_sum hsupp α β N hT, ← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => hφ0 _)]
  apply Real.le_sqrt_of_sq_le
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc ⌈T⌉ ⌊2 * T⌋)
    (fun ℓ : ℤ => Real.sqrt (φ ((ℓ : ℝ) / T)))
    (fun ℓ : ℤ => Real.sqrt (φ ((ℓ : ℝ) / T)) * ‖apMollZeta N α β ℓ‖)
  have e1 : ∀ ℓ : ℤ, Real.sqrt (φ ((ℓ : ℝ) / T)) *
      (Real.sqrt (φ ((ℓ : ℝ) / T)) * ‖apMollZeta N α β ℓ‖) = φ ((ℓ : ℝ) / T) * ‖apMollZeta N α β ℓ‖ :=
    fun ℓ => by rw [← mul_assoc, Real.mul_self_sqrt (hφ0 _)]
  have e2 : ∀ ℓ : ℤ, Real.sqrt (φ ((ℓ : ℝ) / T)) ^ 2 = φ ((ℓ : ℝ) / T) :=
    fun ℓ => Real.sq_sqrt (hφ0 _)
  have e3 : ∀ ℓ : ℤ, (Real.sqrt (φ ((ℓ : ℝ) / T)) * ‖apMollZeta N α β ℓ‖) ^ 2 =
      φ ((ℓ : ℝ) / T) * ‖apMollZeta N α β ℓ‖ ^ 2 :=
    fun ℓ => by rw [mul_pow, Real.sq_sqrt (hφ0 _)]
  simp only [e1, e2, e3] at h
  exact h

theorem norm_bohrMoment_le {φ : ℝ → ℝ} (hsupp : Function.support φ ⊆ Icc 1 2)
    (hφ0 : ∀ y, 0 ≤ φ y) (W : C(UnitAddTorus (Fin K), ℂ)) (θ : Fin K → ℝ) (α β : ℝ) (N : ℕ)
    {T : ℝ} (hT : 0 < T) :
    ‖bohrMoment φ W θ α β N T‖ ≤ ‖W‖ * (Real.sqrt (∑ ℓ ∈ Finset.Icc ⌈T⌉ ⌊2 * T⌋,
      φ ((ℓ : ℝ) / T)) * Real.sqrt (secondMoment φ α β N T)) := by
  rw [bohrMoment_eq_sum hsupp _ _ _ _ _ hT]
  refine (norm_sum_le _ _).trans ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (sum_mul_norm_le_sqrt hsupp hφ0 α β N hT)
    (norm_nonneg _))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ℓ _ => ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hφ0 _)]
  have hW := W.norm_coe_le_norm (orbitPt θ ℓ)
  have h0 := hφ0 ((ℓ : ℝ) / T)
  calc φ ((ℓ : ℝ) / T) * (‖W (orbitPt θ ℓ)‖ * ‖apMollZeta N α β ℓ‖)
      ≤ φ ((ℓ : ℝ) / T) * (‖W‖ * ‖apMollZeta N α β ℓ‖) := by gcongr
    _ = ‖W‖ * (φ ((ℓ : ℝ) / T) * ‖apMollZeta N α β ℓ‖) := by ring

theorem tendsto_sum_bump_div {φ : ℝ → ℝ} (hφ : ∀ k : ℕ, ContDiff ℝ k φ)
    (hsupp : Function.support φ ⊆ Icc 1 2) :
    Tendsto (fun T => (∑ ℓ ∈ Finset.Icc ⌈T⌉ ⌊2 * T⌋, φ ((ℓ : ℝ) / T)) / T) atTop
      (𝓝 (∫ x, φ x)) := by
  have hφC : ∀ k : ℕ, ContDiff ℝ k (fun y : ℝ => (φ y : ℂ)) := fun k =>
    Complex.ofRealCLM.contDiff.comp (hφ k)
  have hsuppC := complex_support_subset hsupp
  obtain ⟨Φ₁, hΦ₁⟩ := exists_bound_iteratedDeriv hφC hsuppC 1
  have hb := tendsto_bumpSum_div_int (hφC 1) hsuppC (Φ₁ := Φ₁) (by simpa using hΦ₁) 0
  rw [integral_complex_ofReal] at hb
  have hre := (Complex.continuous_re.tendsto _).comp hb
  rw [Complex.ofReal_re] at hre
  refine hre.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  simp only [Function.comp_apply]
  unfold bumpSum
  rw [latticeSum_eq_sum (support_cutoff_subset hsuppC hT (fun _ => (1 : ℂ)) |>.trans' (by
    intro x hx; simpa using hx))]
  simp only [Int.cast_zero, mul_zero, unitExp, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    mul_one]
  rw [show ((T : ℂ)) = ((T : ℝ) : ℂ) from rfl, ← Complex.ofReal_sum, ← Complex.ofReal_div,
    Complex.ofReal_re]

/-- **The Bohr-twisted first moment** `S₁(W)/T → (∫ W dμ_H)(∫φ)` for continuous `W`. -/
theorem tendsto_bohrMoment_div {φ : ℝ → ℝ} (hφ : ∀ k : ℕ, ContDiff ℝ k φ)
    (hsupp : Function.support φ ⊆ Icc 1 2) (hφ0 : ∀ y, 0 ≤ φ y) (θ : Fin K → ℝ) {α β ϑ : ℝ}
    (hα : 0 < α) (hϑ0 : 0 < ϑ) (hϑ : ϑ < 1 / 2) (W : C(UnitAddTorus (Fin K), ℂ)) :
    Tendsto (fun T => bohrMoment φ W θ α β (molLen ϑ T) T / T) atTop
      (𝓝 ((∫ x, W x ∂(orbitHaar θ)) * ((∫ x, φ x : ℝ) : ℂ))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set B : ℝ := ∫ x, φ x
  set A : ℝ := B * (1 + 1 / ϑ)
  set M₀ : ℝ := Real.sqrt (|B| + 1) * Real.sqrt (|A| + 1)
  have hM₀ : 0 ≤ M₀ := by positivity
  set δ : ℝ := ε / (3 * (M₀ + |B| + 1))
  have hδ : 0 < δ := by positivity
  -- a trigonometric polynomial `δ`-close to `W`
  have hW : W ∈ closure ((Submodule.span ℂ (Set.range (mFourier (d := Fin K)))) :
      Set C(UnitAddTorus (Fin K), ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, span_mFourier_closure_eq_top]
    trivial
  obtain ⟨P, hP, hWP⟩ := Metric.mem_closure_iff.mp hW δ hδ
  rw [dist_eq_norm] at hWP
  have hPlim := tendsto_bohrMoment_div_of_mem_span hφ hsupp θ (β := β) hα hϑ0 hϑ.le hP
  have hS₂ := tendsto_secondMoment_div hφ hsupp (β := β) hα hϑ0 hϑ
  have hS₀ := tendsto_sum_bump_div hφ hsupp
  obtain ⟨T₁, hT₁⟩ := Metric.tendsto_atTop.mp hPlim (ε / 3) (by positivity)
  obtain ⟨T₂, hT₂⟩ := Metric.tendsto_atTop.mp hS₂ 1 one_pos
  obtain ⟨T₃, hT₃⟩ := Metric.tendsto_atTop.mp hS₀ 1 one_pos
  refine ⟨max (max T₁ T₂) (max T₃ 1), fun T hT => ?_⟩
  have hT1 : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT2 : T₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT3 : T₃ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT0 : 0 < T := lt_of_lt_of_le one_pos (le_trans (le_trans (le_max_right _ _)
    (le_max_right _ _)) hT)
  -- the second-moment and Riemann-sum sizes
  have hS₂T : secondMoment φ α β (molLen ϑ T) T / T ≤ |A| + 1 := by
    have h1 := hT₂ T hT2
    rw [Real.dist_eq] at h1
    have h2 := le_abs_self A
    linarith [(abs_lt.mp h1).2]
  have hS₀T : (∑ ℓ ∈ Finset.Icc ⌈T⌉ ⌊2 * T⌋, φ ((ℓ : ℝ) / T)) / T ≤ |B| + 1 := by
    have h1 := hT₃ T hT3
    rw [Real.dist_eq] at h1
    have h2 := le_abs_self B
    linarith [(abs_lt.mp h1).2]
  have hS0 : 0 ≤ secondMoment φ α β (molLen ϑ T) T :=
    tsum_nonneg fun ℓ => mul_nonneg (hφ0 _) (by positivity)
  have hsum0 : 0 ≤ ∑ ℓ ∈ Finset.Icc ⌈T⌉ ⌊2 * T⌋, φ ((ℓ : ℝ) / T) :=
    Finset.sum_nonneg fun _ _ => hφ0 _
  -- `|S₁(W − P)|/T ≤ ‖W − P‖ M₀`
  have hdiff : ‖bohrMoment φ W θ α β (molLen ϑ T) T / T -
      bohrMoment φ P θ α β (molLen ϑ T) T / T‖ ≤ δ * M₀ := by
    have hsplit : bohrMoment φ W θ α β (molLen ϑ T) T - bohrMoment φ P θ α β (molLen ϑ T) T =
        bohrMoment φ (W - P) θ α β (molLen ϑ T) T :=
      (bohrMoment_sub hsupp _ _ _ _ _ _ hT0).symm
    rw [← sub_div, hsplit, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0,
      div_le_iff₀ hT0]
    refine (norm_bohrMoment_le hsupp hφ0 (W - P) θ α β (molLen ϑ T) hT0).trans ?_
    have hsq : Real.sqrt (∑ ℓ ∈ Finset.Icc ⌈T⌉ ⌊2 * T⌋, φ ((ℓ : ℝ) / T)) *
        Real.sqrt (secondMoment φ α β (molLen ϑ T) T) ≤ M₀ * T := by
      have e : Real.sqrt (∑ ℓ ∈ Finset.Icc ⌈T⌉ ⌊2 * T⌋, φ ((ℓ : ℝ) / T)) *
          Real.sqrt (secondMoment φ α β (molLen ϑ T) T) =
          Real.sqrt ((∑ ℓ ∈ Finset.Icc ⌈T⌉ ⌊2 * T⌋, φ ((ℓ : ℝ) / T)) / T) *
            Real.sqrt (secondMoment φ α β (molLen ϑ T) T / T) * T := by
        rw [Real.sqrt_div' _ hT0.le, Real.sqrt_div' _ hT0.le]
        have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
        field_simp
        rw [Real.sq_sqrt hT0.le]
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_right (mul_le_mul (Real.sqrt_le_sqrt hS₀T)
        (Real.sqrt_le_sqrt hS₂T) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hT0.le
    calc ‖W - P‖ * (Real.sqrt (∑ ℓ ∈ Finset.Icc ⌈T⌉ ⌊2 * T⌋, φ ((ℓ : ℝ) / T)) *
          Real.sqrt (secondMoment φ α β (molLen ϑ T) T))
        ≤ δ * (M₀ * T) := mul_le_mul hWP.le hsq (by positivity) hδ.le
      _ = δ * M₀ * T := by ring
  -- `|∫(W − P) dμ_H ∫φ| ≤ ‖W − P‖ |∫φ|`
  have hlim : ‖(∫ x, W x ∂(orbitHaar θ)) * ((B : ℝ) : ℂ) -
      (∫ x, P x ∂(orbitHaar θ)) * ((B : ℝ) : ℂ)‖ ≤ δ * |B| := by
    have hintW : Integrable (fun x => W x) (orbitHaar θ) :=
      W.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hintP : Integrable (fun x => P x) (orbitHaar θ) :=
      P.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [← sub_mul, ← integral_sub hintW hintP, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    have hb : ∀ᵐ x ∂(orbitHaar θ), ‖W x - P x‖ ≤ ‖W - P‖ :=
      Eventually.of_forall fun x => by simpa using (W - P).norm_coe_le_norm x
    refine (norm_integral_le_of_norm_le_const hb).trans ?_
    rw [probReal_univ, mul_one]; exact hWP.le
  have hP := hT₁ T hT1
  rw [dist_eq_norm] at hP ⊢
  calc ‖bohrMoment φ W θ α β (molLen ϑ T) T / T - (∫ x, W x ∂(orbitHaar θ)) * ((B : ℝ) : ℂ)‖
      ≤ ‖bohrMoment φ W θ α β (molLen ϑ T) T / T - bohrMoment φ P θ α β (molLen ϑ T) T / T‖ +
        ‖bohrMoment φ P θ α β (molLen ϑ T) T / T - (∫ x, P x ∂(orbitHaar θ)) * ((B : ℝ) : ℂ)‖ +
        ‖(∫ x, P x ∂(orbitHaar θ)) * ((B : ℝ) : ℂ) - (∫ x, W x ∂(orbitHaar θ)) * ((B : ℝ) : ℂ)‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub
          (bohrMoment φ W θ α β (molLen ϑ T) T / T) (bohrMoment φ P θ α β (molLen ϑ T) T / T)
          ((∫ x, W x ∂(orbitHaar θ)) * ((B : ℝ) : ℂ))
        have h2 := norm_sub_le_norm_sub_add_norm_sub
          (bohrMoment φ P θ α β (molLen ϑ T) T / T) ((∫ x, P x ∂(orbitHaar θ)) * ((B : ℝ) : ℂ))
          ((∫ x, W x ∂(orbitHaar θ)) * ((B : ℝ) : ℂ))
        linarith
    _ < δ * M₀ + ε / 3 + δ * |B| := by
        rw [norm_sub_rev ((∫ x, P x ∂(orbitHaar θ)) * _)]
        linarith
    _ ≤ ε := by
        have : δ * M₀ + δ * |B| ≤ ε / 3 := by
          rw [← mul_add]
          simp only [δ]
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [abs_nonneg B]
        linarith

end

end RHTower.VerticalAP
