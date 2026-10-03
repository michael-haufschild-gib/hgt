import GaloisForLFunctions.HTGeometry.LaplaceFormationRecoveryKernel
import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import GaloisForLFunctions.HTGeometry.DiagonalCompactOperator
import GaloisForLFunctions.HTGeometry.ObserverHorizonStability
import GaloisForLFunctions.HTGeometry.ConstitutiveFunctionalEquationPacketLift

/-!
# Completion topology and information geometry of a Laplace formation

Let `α = ν({0})`.  The visible amplitudes `a_k` decrease to `α` (dominated convergence), so on
`ℓ²` the visible diagonal `A_ν` is compact exactly when `α = 0`; in that chamber `D_ν - I` is
compact.  The hidden diagonal is always boundedly invertible, `‖D_ν⁻¹‖ ≤ d_1⁻¹`.  The visible range
is always dense, and it is closed exactly when `α ≠ 0`.

The recovery kernels form a Markov kernel `K_ν` on the response index; adjoining it to any two
observer laws preserves the Kullback–Leibler divergence, also after any measurable-embedding
action lifted through recovery and regeneration.  Finally, the source law, its visible response,
its hidden response, its history amplitudes and its recovery kernel determine one another.
-/

noncomputable section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

/-- A diagonal operator on `ℓ²` acts on a single coordinate by its multiplier. -/
theorem lpDiagonalCLM_single_apply (lam : ℕ → ℂ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, ‖lam i‖ ≤ C)
    (i : ℕ) (c : ℂ) :
    GaloisForLFunctions.lpDiagonalCLM lam hC0 hC (lp.single 2 i c) = lp.single 2 i (lam i * c) := by
  ext j
  rw [GaloisForLFunctions.lpDiagonalCLM_apply]
  simp only [lp.single_apply, Pi.single_apply]
  split_ifs with h
  · subst h; rfl
  · rw [mul_zero]

theorem lpDiagonalCLM_lpBasis (lam : ℕ → ℂ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, ‖lam i‖ ≤ C)
    (i : ℕ) :
    GaloisForLFunctions.lpDiagonalCLM lam hC0 hC (HilbertSchmidt.lpBasis ℕ i) =
      lam i • HilbertSchmidt.lpBasis ℕ i := by
  rw [HilbertSchmidt.lpBasis_apply, lpDiagonalCLM_single_apply, mul_one]
  ext j
  simp only [lp.single_apply, Pi.single_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · subst h; simp
  · simp

/-- A diagonal operator on `ℓ²` with multipliers tending to zero is compact. -/
theorem isCompactOperator_lpDiagonalCLM (lam : ℕ → ℂ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i, ‖lam i‖ ≤ C) (hlim : Tendsto (fun n => ‖lam n‖) atTop (𝓝 0)) :
    IsCompactOperator (GaloisForLFunctions.lpDiagonalCLM lam hC0 hC) := by
  refine isCompactOperator_of_diag_tendsto_cofinite (HilbertSchmidt.lpBasis ℕ)
    (lpDiagonalCLM_lpBasis lam hC0 hC) ?_
  rwa [Nat.cofinite_eq_atTop]

/-- The coordinates of an `ℓ²` vector tend to zero. -/
theorem tendsto_lp_two_apply (z : lp (fun _ : ℕ => ℂ) 2) : Tendsto (fun n => z n) atTop (𝓝 0) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) z
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  have h0 := h.summable.tendsto_atTop_zero
  have hs := (Real.continuous_sqrt.tendsto 0).comp h0
  rw [Real.sqrt_zero] at hs
  refine tendsto_zero_iff_norm_tendsto_zero.2 (hs.congr fun n => ?_)
  simp [Real.sqrt_sq (norm_nonneg _)]

/-- The coordinate vectors of `ℓ²` are weakly null. -/
theorem tendsto_inner_lp_single (z : lp (fun _ : ℕ => ℂ) 2) :
    Tendsto (fun n => ⟪z, lp.single 2 n (1 : ℂ)⟫_ℂ) atTop (𝓝 0) := by
  have h := tendsto_lp_two_apply z
  have hc := (Complex.continuous_conj.tendsto 0).comp h
  rw [map_zero] at hc
  refine hc.congr fun n => ?_
  rw [lp.inner_single_right]
  simp [RCLike.inner_apply]

/-- A compact diagonal operator on `ℓ²` has multipliers tending to zero. -/
theorem tendsto_norm_of_isCompactOperator_lpDiagonalCLM (lam : ℕ → ℂ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i, ‖lam i‖ ≤ C)
    (hK : IsCompactOperator (GaloisForLFunctions.lpDiagonalCLM lam hC0 hC)) :
    Tendsto (fun n => ‖lam n‖) atTop (𝓝 0) := by
  have h := tendsto_norm_compact_of_weaklyNull (𝕜 := ℂ)
    (GaloisForLFunctions.lpDiagonalCLM lam hC0 hC) hK (fun n => lp.single 2 n (1 : ℂ))
    (fun n => by rw [lp.norm_single (by norm_num), norm_one]) tendsto_inner_lp_single
  have hn := (continuous_norm.tendsto 0).comp h
  rw [norm_zero] at hn
  refine hn.congr fun n => ?_
  simp only [Function.comp_apply, lpDiagonalCLM_single_apply, mul_one,
    lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

namespace HalfLineFormationLaw

variable (ν : HalfLineFormationLaw)

/-! ## The delay atom is the limit of the visible amplitudes -/

/-- `ν({0}) ≤ a_k` for every response index. -/
theorem measureReal_zero_le_visible (k : ℕ) : ν.measure.real {0} ≤ ν.visible k := by
  rw [← integral_indicator_one (measurableSet_singleton 0)]
  refine integral_mono ((integrable_const (1 : ℝ)).indicator (measurableSet_singleton 0))
    (ν.integrable_exp_neg (k + 1)) fun x => ?_
  by_cases hx : x = 0
  · subst hx; simp
  · rw [indicator_of_notMem (by simpa using hx)]
    exact (Real.exp_pos _).le

/-- **(LFD.36), first step.** `a_k → ν({0})`. -/
theorem tendsto_visible : Tendsto ν.visible atTop (𝓝 (ν.measure.real {0})) := by
  rw [← integral_indicator_one (measurableSet_singleton 0)]
  refine tendsto_integral_of_dominated_convergence (fun _ => 1)
    (fun n => (ν.integrable_exp_neg (n + 1)).aestronglyMeasurable) (integrable_const 1)
    (fun n => ν.ae_nonneg.mono fun x hx => ?_) ?_
  · rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff, neg_nonpos]
    positivity
  · filter_upwards [ν.ae_nonneg] with x hx
    rcases hx.eq_or_lt with rfl | hpos
    · simp
    · rw [indicator_of_notMem (by simpa using hpos.ne')]
      have ht : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * x) atTop atTop :=
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).atTop_mul_const hpos
      exact Real.tendsto_exp_neg_atTop_nhds_zero.comp ht

/-- **(LFD.36), atom test.**  `a_k → 0` exactly when the source has no delay atom at `0`. -/
theorem tendsto_visible_zero_iff : Tendsto ν.visible atTop (𝓝 0) ↔ ν.measure {0} = 0 := by
  constructor
  · intro h
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 (tendsto_nhds_unique ν.tendsto_visible h)
  · intro h
    have h0 : ν.measure.real {0} = 0 := (measureReal_eq_zero_iff (measure_ne_top _ _)).2 h
    simpa [h0] using ν.tendsto_visible

theorem norm_visible_le (k : ℕ) : ‖(ν.visible k : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg (ν.visible_pos k).le]
  exact (ν.visible_lt_one k).le

theorem norm_hidden_le (k : ℕ) : ‖(ν.hidden k : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg (ν.hidden_pos k).le]
  exact (ν.hidden_lt_one k).le

/-! ## The visible and hidden formations on `ℓ²` -/

/-- Visible formation `A_ν` on `ℓ²`. -/
def visibleL2 : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  GaloisForLFunctions.lpDiagonalCLM (fun k => (ν.visible k : ℂ)) zero_le_one ν.norm_visible_le

/-- Hidden formation `D_ν` on `ℓ²`. -/
def hiddenL2 : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  GaloisForLFunctions.lpDiagonalCLM (fun k => (ν.hidden k : ℂ)) zero_le_one ν.norm_hidden_le

theorem visibleL2_single (i : ℕ) (c : ℂ) :
    ν.visibleL2 (lp.single 2 i c) = lp.single 2 i ((ν.visible i : ℂ) * c) :=
  lpDiagonalCLM_single_apply _ _ _ i c

/-- `‖A_ν‖ = a_1` on `ℓ²`. -/
theorem norm_visibleL2 : ‖ν.visibleL2‖ = ν.visible 0 := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (ν.visible_pos 0).le fun x => ?_) ?_
  · have h := lp.hasSum_norm (p := 2) (by norm_num) x
    have hA := lp.hasSum_norm (p := 2) (by norm_num) (ν.visibleL2 x)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h hA
    have hle : ‖ν.visibleL2 x‖ ^ 2 ≤ (ν.visible 0 * ‖x‖) ^ 2 := by
      rw [mul_pow, ← hA.tsum_eq, ← h.tsum_eq, ← tsum_mul_left]
      refine hA.summable.tsum_le_tsum (fun k => ?_) (h.summable.mul_left _)
      change ‖(ν.visible k : ℂ) * x k‖ ^ 2 ≤ _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ν.visible_pos k).le, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (ν.visible_pos k).le (ν.visible_le k) 2) (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (ν.visible_pos 0).le
      (norm_nonneg _)) two_ne_zero).1 hle
  · have h := ν.visibleL2.le_opNorm (lp.single 2 0 1)
    rwa [visibleL2_single, mul_one, lp.norm_single (by norm_num), lp.norm_single (by norm_num),
      norm_one, mul_one, Complex.norm_real, Real.norm_of_nonneg (ν.visible_pos 0).le] at h

/-- **Loop A.**  The positive visible formation is not an involution: `A_ν² ≠ I`. -/
theorem visibleL2_mul_self_ne_one : ν.visibleL2 * ν.visibleL2 ≠ 1 := by
  intro h
  have h1 : (ν.visibleL2 * ν.visibleL2) (lp.single 2 0 1) = lp.single 2 0 1 := by rw [h]; rfl
  change ν.visibleL2 (ν.visibleL2 (lp.single 2 0 1)) = _ at h1
  rw [visibleL2_single, mul_one, visibleL2_single] at h1
  have h2 := congrArg norm h1
  rw [lp.norm_single (by norm_num), lp.norm_single (by norm_num), norm_one, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (ν.visible_pos 0).le] at h2
  have := ν.visible_lt_one 0
  have := ν.visible_pos 0
  nlinarith

/-- **(LFD.36)** On `ℓ²`, the visible formation is compact exactly when `ν({0}) = 0`. -/
theorem isCompactOperator_visibleL2_iff : IsCompactOperator ν.visibleL2 ↔ ν.measure {0} = 0 := by
  have hnorm : (fun n => ‖(ν.visible n : ℂ)‖) = ν.visible := funext fun n => by
    rw [Complex.norm_real, Real.norm_of_nonneg (ν.visible_pos n).le]
  constructor
  · intro hK
    have h := tendsto_norm_of_isCompactOperator_lpDiagonalCLM _ zero_le_one ν.norm_visible_le hK
    rw [hnorm] at h
    exact ν.tendsto_visible_zero_iff.1 h
  · intro h0
    refine isCompactOperator_lpDiagonalCLM _ zero_le_one ν.norm_visible_le ?_
    rw [hnorm]
    exact ν.tendsto_visible_zero_iff.2 h0

theorem tendsto_hidden_one (h0 : ν.measure {0} = 0) : Tendsto ν.hidden atTop (𝓝 1) := by
  have h := ν.tendsto_visible_zero_iff.2 h0
  have hc : Continuous fun t : ℝ => Real.sqrt (1 - t ^ 2) := by fun_prop
  have := (hc.tendsto 0).comp h
  simp only [Function.comp_def, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
    Real.sqrt_one] at this
  exact this

/-- **(LFD.37)** In the atom-free chamber `D_ν - I` is compact. -/
theorem isCompactOperator_hiddenL2_sub_one (h0 : ν.measure {0} = 0) :
    IsCompactOperator ((ν.hiddenL2 - 1 : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2)) := by
  have hb : ∀ k, ‖((ν.hidden k : ℂ) - 1)‖ ≤ 2 := fun k => by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one]; linarith [ν.norm_hidden_le k]
  have heq : ν.hiddenL2 - 1 =
      GaloisForLFunctions.lpDiagonalCLM (fun k => (ν.hidden k : ℂ) - 1) zero_le_two hb := by
    ext x k
    change (ν.hidden k : ℂ) * x k - x k = ((ν.hidden k : ℂ) - 1) * x k
    ring
  rw [heq]
  refine isCompactOperator_lpDiagonalCLM _ _ hb ?_
  have h := ν.tendsto_hidden_one h0
  have h2 : Tendsto (fun k => ((ν.hidden k : ℂ) - 1)) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 1).comp h
    have := this.sub_const 1
    simpa [Function.comp_def] using this
  simpa using h2.norm

theorem norm_hidden_inv_le (k : ℕ) : ‖((ν.hidden k : ℂ))⁻¹‖ ≤ (ν.hidden 0)⁻¹ := by
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (ν.hidden_pos k).le]
  exact inv_anti₀ (ν.hidden_pos 0) (ν.hidden_zero_le k)

/-- The inverse hidden formation `D_ν⁻¹` on `ℓ²`. -/
def hiddenInverseL2 : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  GaloisForLFunctions.lpDiagonalCLM (fun k => ((ν.hidden k : ℂ))⁻¹)
    (inv_nonneg.2 (ν.hidden_pos 0).le) ν.norm_hidden_inv_le

/-- **(LFD.37)** `D_ν` is boundedly invertible on `ℓ²` with `‖D_ν⁻¹‖ ≤ d_1⁻¹`. -/
theorem hiddenL2_invertible :
    ν.hiddenL2 * ν.hiddenInverseL2 = 1 ∧ ν.hiddenInverseL2 * ν.hiddenL2 = 1 ∧
      ‖ν.hiddenInverseL2‖ ≤ (ν.hidden 0)⁻¹ := by
  have hne : ∀ k, (ν.hidden k : ℂ) ≠ 0 := fun k => Complex.ofReal_ne_zero.2 (ν.hidden_pos k).ne'
  refine ⟨?_, ?_, GaloisForLFunctions.norm_lpDiagonalCLM_le _ _ _⟩
  · ext x k
    change (ν.hidden k : ℂ) * (((ν.hidden k : ℂ))⁻¹ * x k) = x k
    rw [← mul_assoc, mul_inv_cancel₀ (hne k), one_mul]
  · ext x k
    change ((ν.hidden k : ℂ))⁻¹ * ((ν.hidden k : ℂ) * x k) = x k
    rw [← mul_assoc, inv_mul_cancel₀ (hne k), one_mul]

/-- The visible range on `ℓ²` is dense. -/
theorem denseRange_visibleL2 : DenseRange ν.visibleL2 := by
  classical
  intro y
  have hy := lp.hasSum_single (E := fun _ : ℕ => ℂ) (p := 2) (by norm_num) y
  refine mem_closure_of_tendsto hy (Eventually.of_forall fun F => ?_)
  refine ⟨∑ i ∈ F, lp.single 2 i (((ν.visible i : ℂ))⁻¹ * y i), ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [visibleL2_single, ← mul_assoc,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 (ν.visible_pos i).ne'), one_mul]

/-- In the atom-free chamber the visible formation is not bounded below. -/
theorem not_boundedBelow_visibleL2 (h0 : ν.measure {0} = 0) :
    ¬ ∃ C : ℝ, ∀ x, ‖x‖ ≤ C * ‖ν.visibleL2 x‖ := by
  rintro ⟨C, hC⟩
  have hlow : ∀ n, 1 ≤ C * ν.visible n := fun n => by
    have h := hC (lp.single 2 n 1)
    rwa [visibleL2_single, mul_one, lp.norm_single (by norm_num), lp.norm_single (by norm_num),
      norm_one, Complex.norm_real, Real.norm_of_nonneg (ν.visible_pos n).le] at h
  have ht := (ν.tendsto_visible_zero_iff.2 h0).const_mul C
  rw [mul_zero] at ht
  have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨n, hn⟩ := hev.exists
  linarith [hlow n]

/-- **(LFD.36)–(LFD.37), range topology.**  The visible range is closed exactly when the source
carries a delay atom at `0`. -/
theorem isClosed_range_visibleL2_iff :
    IsClosed (Set.range ν.visibleL2) ↔ ν.measure {0} ≠ 0 := by
  constructor
  · intro hcl h0
    have htop : LinearMap.range (ν.visibleL2 : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hy : y ∈ closure (Set.range ν.visibleL2) := ν.denseRange_visibleL2 y
      rw [hcl.closure_eq] at hy
      exact hy
    have hker : LinearMap.ker (ν.visibleL2 : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro x hx
      ext k
      have := congrArg (fun z : lp (fun _ : ℕ => ℂ) 2 => z k) hx
      change (ν.visible k : ℂ) * x k = 0 at this
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (Complex.ofReal_ne_zero.2 (ν.visible_pos k).ne')
      · exact h
    let e := ContinuousLinearEquiv.ofBijective ν.visibleL2 hker htop
    refine ν.not_boundedBelow_visibleL2 h0 ⟨‖(e.symm : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2)‖, fun x => ?_⟩
    calc ‖x‖ = ‖(e.symm : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2) (ν.visibleL2 x)‖ := by
          congr 1
          exact (e.symm_apply_apply x).symm
      _ ≤ _ := ContinuousLinearMap.le_opNorm _ _
  · intro h0
    have hα : 0 < ν.measure.real {0} := by
      rcases (measureReal_nonneg : 0 ≤ ν.measure.real {0}).eq_or_lt with h | h
      · exact absurd ((measureReal_eq_zero_iff (measure_ne_top _ _)).1 h.symm) h0
      · exact h
    have hinv : ∀ k, ‖((ν.visible k : ℂ))⁻¹‖ ≤ (ν.measure.real {0})⁻¹ := fun k => by
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (ν.visible_pos k).le]
      exact inv_anti₀ hα (ν.measureReal_zero_le_visible k)
    have hsurj : Set.range ν.visibleL2 = univ := by
      refine eq_univ_of_forall fun y => ⟨GaloisForLFunctions.lpDiagonalCLM
        (fun k => ((ν.visible k : ℂ))⁻¹) (inv_nonneg.2 hα.le) hinv y, ?_⟩
      ext k
      change (ν.visible k : ℂ) * (((ν.visible k : ℂ))⁻¹ * y k) = y k
      rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 (ν.visible_pos k).ne'), one_mul]
    rw [hsurj]
    exact isClosed_univ

/-! ## The recovery kernel as a Markov kernel; information isometry -/

theorem hasSum_ofReal_recoveryKernel (k : ℕ) :
    HasSum (fun j => ENNReal.ofReal (ν.recoveryKernel k j)) 1 := by
  have h := ν.hasSum_recoveryKernel k
  have he := ENNReal.ofReal_tsum_of_nonneg (ν.recoveryKernel_nonneg k) h.summable
  rw [h.tsum_eq, ENNReal.ofReal_one] at he
  rw [he]
  exact ENNReal.summable.hasSum

/-- The recovery law `K_ν(k, ·)` as a probability mass function. -/
def recoveryPMF (k : ℕ) : PMF ℕ :=
  ⟨fun j => ENNReal.ofReal (ν.recoveryKernel k j), ν.hasSum_ofReal_recoveryKernel k⟩

/-- **(LFD.34)** The recovery Markov kernel `k ↦ K_ν(k, ·)` on the response index. -/
def recoveryMarkovKernel : ProbabilityTheory.Kernel ℕ ℕ :=
  ⟨fun k => (ν.recoveryPMF k).toMeasure, Measurable.of_discrete⟩

instance : ProbabilityTheory.IsMarkovKernel ν.recoveryMarkovKernel :=
  ⟨fun k => PMF.toMeasure.isProbabilityMeasure (ν.recoveryPMF k)⟩

/-- **(LFD.34)** The joint observer/history packet has masses `ρ̂(n, j) = ρ(n) K_ν(n, j)`. -/
theorem splitFormation_recoveryMarkovKernel_singleton (ρ : Measure ℕ) [IsFiniteMeasure ρ]
    (n j : ℕ) :
    splitFormation ρ ν.recoveryMarkovKernel {(n, j)} = ρ {n} * ENNReal.ofReal (ν.recoveryKernel n j) := by
  rw [← singleton_prod_singleton, splitFormation,
    Measure.compProd_apply_prod (measurableSet_singleton n) (measurableSet_singleton j),
    lintegral_singleton, mul_comm]
  congr 1
  exact PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton j)

/-- **(LFD.35)** Adjoining the source-generated recovery kernel preserves KL divergence. -/
theorem klDiv_recoveryPacket (ρ η : Measure ℕ) [IsFiniteMeasure ρ] [IsFiniteMeasure η] :
    InformationTheory.klDiv (splitFormation ρ ν.recoveryMarkovKernel)
        (splitFormation η ν.recoveryMarkovKernel) = InformationTheory.klDiv ρ η :=
  klDiv_splitFormation ρ η ν.recoveryMarkovKernel

/-- **(LFD.35), lifted actions.**  A measurable-embedding action on the observer, lifted by
recovery, action and regeneration, preserves the KL divergence of the packets. -/
theorem klDiv_recoveryPacket_lift (ρ η : Measure ℕ) [IsFiniteMeasure ρ] [IsFiniteMeasure η]
    (A : ℕ → ℕ) (hA : MeasurableEmbedding A) :
    InformationTheory.klDiv
        (formationLiftKernel ν.recoveryMarkovKernel A hA.measurable ∘ₘ
          splitFormation ρ ν.recoveryMarkovKernel)
        (formationLiftKernel ν.recoveryMarkovKernel A hA.measurable ∘ₘ
          splitFormation η ν.recoveryMarkovKernel) = InformationTheory.klDiv ρ η := by
  rw [formationLiftKernel_klDiv_isometry ρ η _ A hA, klDiv_recoveryPacket]

/-- **(LFD.35), Jeffreys form.**  The symmetrized divergence is preserved as well. -/
theorem jeffreys_recoveryPacket (ρ η : Measure ℕ) [IsFiniteMeasure ρ] [IsFiniteMeasure η] :
    InformationTheory.klDiv (splitFormation ρ ν.recoveryMarkovKernel)
        (splitFormation η ν.recoveryMarkovKernel) +
      InformationTheory.klDiv (splitFormation η ν.recoveryMarkovKernel)
        (splitFormation ρ ν.recoveryMarkovKernel) =
      InformationTheory.klDiv ρ η + InformationTheory.klDiv η ρ := by
  rw [klDiv_recoveryPacket, klDiv_recoveryPacket]

/-- An injective map of the discrete response index is a measurable embedding. -/
theorem measurableEmbedding_of_injective_nat {A : ℕ → ℕ} (hA : Function.Injective A) :
    MeasurableEmbedding A :=
  ⟨hA, Measurable.of_discrete, fun _ _ => MeasurableSet.of_discrete⟩

/-- **(LFD.35), injective observer actions.** -/
theorem klDiv_recoveryPacket_lift_of_injective (ρ η : Measure ℕ) [IsFiniteMeasure ρ]
    [IsFiniteMeasure η] {A : ℕ → ℕ} (hA : Function.Injective A) :
    InformationTheory.klDiv
        (formationLiftKernel ν.recoveryMarkovKernel A Measurable.of_discrete ∘ₘ
          splitFormation ρ ν.recoveryMarkovKernel)
        (formationLiftKernel ν.recoveryMarkovKernel A Measurable.of_discrete ∘ₘ
          splitFormation η ν.recoveryMarkovKernel) = InformationTheory.klDiv ρ η :=
  ν.klDiv_recoveryPacket_lift ρ η A (measurableEmbedding_of_injective_nat hA)

/-! ## Source determination -/

theorem visible_eq_sqrt_hidden (k : ℕ) : ν.visible k = Real.sqrt (1 - ν.hidden k ^ 2) := by
  have h := ν.visible_sq_add_hidden_sq k
  rw [show 1 - ν.hidden k ^ 2 = ν.visible k ^ 2 by linarith, Real.sqrt_sq (ν.visible_pos k).le]

/-- **(LFD.40) Source determination.**  For two nontrivial half-line laws the following are
equivalent: equal source laws; equal visible responses; equal hidden responses; equal history
amplitudes; equal recovery kernels. -/
theorem source_determination_tfae (μ : HalfLineFormationLaw) :
    List.TFAE [ν.measure = μ.measure, ∀ k, ν.visible k = μ.visible k,
      ∀ k, ν.hidden k = μ.hidden k, ∀ k j, ν.historyAmplitude k j = μ.historyAmplitude k j,
      ∀ k j, ν.recoveryKernel k j = μ.recoveryKernel k j] := by
  tfae_have 1 → 2 := fun h k => by
    change ν.laplace (k + 1) = μ.laplace (k + 1)
    rw [laplace, laplace, h]
  tfae_have 2 → 3 := fun h k => by rw [hidden, hidden, h]
  tfae_have 3 → 4 := fun h k j => by
    rw [historyAmplitude, historyAmplitude, ν.visible_eq_sqrt_hidden, μ.visible_eq_sqrt_hidden, h]
  tfae_have 4 → 5 := fun h k j => by rw [recoveryKernel_eq_sq, recoveryKernel_eq_sq, h]
  tfae_have 5 → 1 := ν.measure_eq_of_recoveryKernel_eq μ
  tfae_finish

end HalfLineFormationLaw

end GaloisForLFunctions.HTGeometry
