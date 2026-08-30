import GaloisForLFunctions.RHTower.BurnolResidueCriticalLineKernelL2Continuity
import GaloisForLFunctions.RHTower.BurnolQuotientContour

/-!
# Burnol's quotient-weighted critical-line L² contour

Burnol's strong form of Theorem 5.2 treats

`(G(s) / ζ(s)) * ζ(Z)(2+s) / ((Z+2)(Z-s))`

as an `L²` vector in the critical-line variable `Z = -1/2 + it`.  This file realizes that vector,
proves its exact Bochner edge domination, and proves selected horizontal edges vanish in actual
`L²` norm.  The two additional powers in the kernel bound are paid by the source's rapid vertical
decrease.
-/

open Complex MeasureTheory Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Burnol's quotient-weighted residue kernel as an actual critical-line `L²` vector. -/
def burnolWeightedResidueCriticalLineKernelL2 (G : ℂ → ℂ)
    (s : BurnolSourceHalfStrip) : Lp ℂ 2 (volume : Measure ℝ) :=
  burnolQuotient G s.1 • burnolResidueCriticalLineKernelL2 s

theorem norm_burnolWeightedResidueCriticalLineKernelL2_le
    (G : ℂ → ℂ) (s : BurnolSourceHalfStrip) :
    ‖burnolWeightedResidueCriticalLineKernelL2 G s‖ ≤
      ‖burnolQuotient G s.1‖ *
        (9 * (1 + ‖(s : ℂ)‖ ^ 2) * ‖burnolCriticalLineBaseKernelL2‖) := by
  rw [burnolWeightedResidueCriticalLineKernelL2, norm_smul]
  exact mul_le_mul_of_nonneg_left
    (norm_burnolResidueCriticalLineKernelL2_le_quadratic s) (norm_nonneg _)

theorem continuous_burnolWeightedResidueCriticalLineKernelL2_comp
    {G : ℂ → ℂ} {γ : ℝ → BurnolSourceHalfStrip}
    (hγ : Continuous γ)
    (hquot : Continuous fun x : ℝ => burnolQuotient G (γ x).1) :
    Continuous fun x : ℝ => burnolWeightedResidueCriticalLineKernelL2 G (γ x) := by
  exact hquot.smul (continuous_burnolResidueCriticalLineKernelL2.comp hγ)

theorem intervalIntegrable_burnolWeightedResidueCriticalLineKernelL2_comp
    {G : ℂ → ℂ} {γ : ℝ → BurnolSourceHalfStrip}
    (hγ : Continuous γ)
    (hquot : Continuous fun x : ℝ => burnolQuotient G (γ x).1)
    (a b : ℝ) :
    IntervalIntegrable
      (fun x : ℝ => burnolWeightedResidueCriticalLineKernelL2 G (γ x)) volume a b :=
  (continuous_burnolWeightedResidueCriticalLineKernelL2_comp hγ hquot).intervalIntegrable a b

/-- The exact Bochner edge domination used in Burnol's strong `L²` residue convergence. -/
theorem norm_intervalIntegral_burnolWeightedResidueCriticalLineKernelL2_comp_le
    {G : ℂ → ℂ} {γ : ℝ → BurnolSourceHalfStrip}
    (hγ : Continuous γ)
    (hquot : Continuous fun x : ℝ => burnolQuotient G (γ x).1)
    {a b : ℝ} (hab : a ≤ b) :
    ‖∫ x in a..b, burnolWeightedResidueCriticalLineKernelL2 G (γ x)‖ ≤
      ∫ x in a..b, ‖burnolQuotient G (γ x).1‖ *
        (9 * (1 + ‖((γ x : BurnolSourceHalfStrip) : ℂ)‖ ^ 2) *
          ‖burnolCriticalLineBaseKernelL2‖) := by
  have hweighted : Continuous
      (fun x : ℝ => burnolWeightedResidueCriticalLineKernelL2 G (γ x)) :=
    continuous_burnolWeightedResidueCriticalLineKernelL2_comp hγ hquot
  have hγcoe : Continuous fun x : ℝ => ((γ x : BurnolSourceHalfStrip) : ℂ) :=
    continuous_subtype_val.comp hγ
  have hmajor : Continuous fun x : ℝ => ‖burnolQuotient G (γ x).1‖ *
      (9 * (1 + ‖((γ x : BurnolSourceHalfStrip) : ℂ)‖ ^ 2) *
        ‖burnolCriticalLineBaseKernelL2‖) := by
    fun_prop
  calc
    ‖∫ x in a..b, burnolWeightedResidueCriticalLineKernelL2 G (γ x)‖
        ≤ ∫ x in a..b, ‖burnolWeightedResidueCriticalLineKernelL2 G (γ x)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ x in a..b, ‖burnolQuotient G (γ x).1‖ *
        (9 * (1 + ‖((γ x : BurnolSourceHalfStrip) : ℂ)‖ ^ 2) *
          ‖burnolCriticalLineBaseKernelL2‖) := by
      exact intervalIntegral.integral_mono_on hab
        (hweighted.norm.intervalIntegrable a b) (hmajor.intervalIntegrable a b) fun x _ =>
          norm_burnolWeightedResidueCriticalLineKernelL2_le G (γ x)

/-- Horizontal source-contour path, globally clamped only to keep its real part in Burnol's
closed half-strip.  On every interval starting at `-1/4` or to its right the clamp is inactive. -/
def burnolHorizontalSourcePath (y x : ℝ) : BurnolSourceHalfStrip :=
  ⟨((max (-(1 / 4 : ℝ)) x : ℝ) : ℂ) + (y : ℂ) * I, by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
    exact le_max_left _ _⟩

@[simp] theorem burnolHorizontalSourcePath_coe_of_le {y x : ℝ}
    (hx : -(1 / 4 : ℝ) ≤ x) :
    ((burnolHorizontalSourcePath y x : BurnolSourceHalfStrip) : ℂ) =
      (x : ℂ) + (y : ℂ) * I := by
  simp only [burnolHorizontalSourcePath, Subtype.coe_mk]
  rw [max_eq_right hx]

/-- Actual Banach-valued horizontal edge in Burnol's source rectangle. -/
def burnolWeightedResidueHorizontalIntegralL2 (G : ℂ → ℂ)
    (x₁ x₂ y : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  ∫ x in x₁..x₂,
    burnolWeightedResidueCriticalLineKernelL2 G (burnolHorizontalSourcePath y x)

/-- Uniform quotient control on one horizontal edge gives the literal polynomial `L²` edge
bound. -/
theorem norm_burnolWeightedResidueHorizontalIntegralL2_le_of_bound
    {G : ℂ → ℂ} {x₁ x₂ y b M : ℝ}
    (hx₁q : -(1 / 4 : ℝ) ≤ x₁) (hx₂q : -(1 / 4 : ℝ) ≤ x₂)
    (hx₁ : -b ≤ x₁) (hx₁' : x₁ ≤ b)
    (hx₂ : -b ≤ x₂) (hx₂' : x₂ ≤ b) (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Set.uIoc x₁ x₂,
      ‖burnolQuotient G ((x : ℂ) + (y : ℂ) * I)‖ ≤ M) :
    ‖burnolWeightedResidueHorizontalIntegralL2 G x₁ x₂ y‖ ≤
      M * (9 * (1 + (b + |y|) ^ 2) * ‖burnolCriticalLineBaseKernelL2‖) *
        |x₂ - x₁| := by
  have hb0 : 0 ≤ b := by linarith
  have hpoint : ∀ x ∈ Set.uIoc x₁ x₂,
      ‖burnolWeightedResidueCriticalLineKernelL2 G (burnolHorizontalSourcePath y x)‖ ≤
        M * (9 * (1 + (b + |y|) ^ 2) * ‖burnolCriticalLineBaseKernelL2‖) := by
    intro x hx
    rw [Set.mem_uIoc] at hx
    have hxb : -b ≤ x ∧ x ≤ b := by
      rcases hx with hx | hx <;> constructor <;> linarith
    have hxq : -(1 / 4 : ℝ) ≤ x := by
      rcases hx with hx | hx <;> linarith
    have habsx : |x| ≤ b := (abs_le).2 hxb
    have hpath : ((burnolHorizontalSourcePath y x : BurnolSourceHalfStrip) : ℂ) =
        (x : ℂ) + (y : ℂ) * I := burnolHorizontalSourcePath_coe_of_le hxq
    have hpathnorm : ‖((burnolHorizontalSourcePath y x : BurnolSourceHalfStrip) : ℂ)‖ ≤
        b + |y| := by
      rw [hpath]
      calc
        ‖(x : ℂ) + (y : ℂ) * I‖ ≤ ‖(x : ℂ)‖ + ‖(y : ℂ) * I‖ := norm_add_le _ _
        _ = |x| + |y| := by simp [Real.norm_eq_abs]
        _ ≤ b + |y| := by linarith
    calc
      ‖burnolWeightedResidueCriticalLineKernelL2 G (burnolHorizontalSourcePath y x)‖
          ≤ ‖burnolQuotient G (burnolHorizontalSourcePath y x).1‖ *
            (9 * (1 + ‖((burnolHorizontalSourcePath y x : BurnolSourceHalfStrip) : ℂ)‖ ^ 2) *
              ‖burnolCriticalLineBaseKernelL2‖) :=
        norm_burnolWeightedResidueCriticalLineKernelL2_le G _
      _ ≤ M * (9 * (1 + (b + |y|) ^ 2) * ‖burnolCriticalLineBaseKernelL2‖) := by
        rw [hpath]
        gcongr
        · exact hM x (by rw [Set.mem_uIoc]; exact hx)
        · simpa only [hpath] using hpathnorm
  exact intervalIntegral.norm_integral_le_of_norm_le_const hpoint

/-- Burnol's selected horizontal edges vanish in the actual critical-line `L²` norm.  The extra
quadratic kernel growth is absorbed by two further powers of the source's rapid decrease. -/
theorem tendsto_burnolWeightedResidueHorizontalIntegralL2
    {G : ℂ → ℂ} (hG : HasStripRapidDecrease G)
    {T : ℕ → ℝ} (htop : Tendsto T atTop atTop) (hT1 : ∀ k : ℕ, 1 ≤ T k)
    {C A b : ℝ} {k₀ : ℕ} (hC : 0 < C) (hb : 2 ≤ b)
    {ε : ℝ} (hε : |ε| = 1)
    (hzeta : ∀ k : ℕ, k₀ ≤ k → ∀ σ : ℝ, -b ≤ σ → σ ≤ b →
      ‖(riemannZeta ((σ : ℂ) + ((ε * T k : ℝ) : ℂ) * I))⁻¹‖ ≤ C * (T k) ^ A)
    {x₁ x₂ : ℝ} (hx₁q : -(1 / 4 : ℝ) ≤ x₁) (hx₂q : -(1 / 4 : ℝ) ≤ x₂)
    (hx₁ : -b ≤ x₁) (hx₁' : x₁ ≤ b) (hx₂ : -b ≤ x₂) (hx₂' : x₂ ≤ b) :
    Tendsto
      (fun k : ℕ => burnolWeightedResidueHorizontalIntegralL2 G x₁ x₂ (ε * T k))
      atTop (𝓝 0) := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_ge (A + 4)
  obtain ⟨Tg, Cg, hCg0, hGb⟩ := hG (-b) b N
  let E : ℝ := 9 * (1 + (b + 1) ^ 2) * ‖burnolCriticalLineBaseKernelL2‖
  let D : ℝ := Cg * C * E * (2 * b)
  have hb0 : 0 ≤ b := by linarith
  have hneg : A - (N : ℝ) + 2 < 0 := by
    have : A + 4 ≤ (N : ℝ) := hN
    linarith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hmaj : Tendsto (fun k : ℕ => D * (T k) ^ (A - (N : ℝ) + 2))
      atTop (𝓝 0) := by
    have hrpow : Tendsto (fun x : ℝ => x ^ (A - (N : ℝ) + 2)) atTop (𝓝 0) := by
      have h := tendsto_rpow_neg_atTop
        (y := -(A - (N : ℝ) + 2)) (by linarith)
      refine h.congr fun x => ?_
      rw [neg_neg]
    simpa using (hrpow.comp htop).const_mul D
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmaj
    (Eventually.of_forall fun k => norm_nonneg _) ?_
  filter_upwards [Filter.eventually_ge_atTop k₀,
    htop.eventually_ge_atTop (max Tg 1)] with k hk hTk
  have hTk1 : (1 : ℝ) ≤ T k := hT1 k
  have hTk0 : (0 : ℝ) < T k := by linarith
  have hTg : Tg ≤ T k := le_trans (le_max_left _ _) hTk
  have habs : |ε * T k| = T k := by
    rw [abs_mul, hε, one_mul, abs_of_nonneg hTk0.le]
  let M : ℝ := Cg * C * (T k) ^ (A - (N : ℝ))
  have hM0 : 0 ≤ M := by
    dsimp [M]
    positivity
  have hquot : ∀ σ ∈ Set.uIoc x₁ x₂,
      ‖burnolQuotient G ((σ : ℂ) + ((ε * T k : ℝ) : ℂ) * I)‖ ≤ M := by
    intro σ hσ
    rw [Set.mem_uIoc] at hσ
    have hσ1 : -b ≤ σ := by rcases hσ with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
    have hσ2 : σ ≤ b := by rcases hσ with ⟨_, h2⟩ | ⟨_, h2⟩ <;> linarith
    let s : ℂ := (σ : ℂ) + ((ε * T k : ℝ) : ℂ) * I
    have hsre : s.re = σ := by simp [s]
    have hsim : s.im = ε * T k := by simp [s]
    have h1 : ‖G s‖ ≤ Cg * (1 + |s.im|) ^ (-(N : ℝ)) := by
      refine hGb s (by rw [hsre]; exact hσ1) (by rw [hsre]; exact hσ2) ?_
      rw [hsim, habs]
      exact hTg
    have h2 : ‖(riemannZeta s)⁻¹‖ ≤ C * (T k) ^ A := by
      simpa [s] using hzeta k hk σ hσ1 hσ2
    have hpowG : (1 + |s.im|) ^ (-(N : ℝ)) ≤ (T k) ^ (-(N : ℝ)) := by
      rw [hsim, habs]
      exact Real.rpow_le_rpow_of_nonpos hTk0 (by linarith)
        (neg_nonpos.2 (Nat.cast_nonneg N))
    have hmul : (T k) ^ (-(N : ℝ)) * (T k) ^ A =
        (T k) ^ (A - (N : ℝ)) := by
      rw [← Real.rpow_add hTk0]
      congr 1
      ring
    rw [burnolQuotient, norm_mul]
    calc
      ‖G s‖ * ‖(riemannZeta s)⁻¹‖
          ≤ (Cg * (1 + |s.im|) ^ (-(N : ℝ))) * (C * (T k) ^ A) := by
        exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ ≤ (Cg * (T k) ^ (-(N : ℝ))) * (C * (T k) ^ A) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hpowG hCg0
      _ = Cg * C * ((T k) ^ (-(N : ℝ)) * (T k) ^ A) := by ring
      _ = M := by rw [hmul]
  have hedge := norm_burnolWeightedResidueHorizontalIntegralL2_le_of_bound
    hx₁q hx₂q hx₁ hx₁' hx₂ hx₂' hM0 hquot
  have hlen : |x₂ - x₁| ≤ 2 * b := by
    rw [abs_le]
    constructor <;> linarith
  have hbt : b + T k ≤ (b + 1) * T k := by
    nlinarith
  have hbt0 : 0 ≤ b + T k := by linarith
  have hcoef0 : 0 ≤ Cg * C * (T k) ^ (A - (N : ℝ)) := by positivity
  have hkernel : 1 + (b + |ε * T k|) ^ 2 ≤
      (1 + (b + 1) ^ 2) * (T k) ^ 2 := by
    rw [habs]
    have hsq : (b + T k) ^ 2 ≤ ((b + 1) * T k) ^ 2 :=
      (sq_le_sq₀ hbt0 (by positivity)).2 hbt
    rw [mul_pow] at hsq
    have hT2 : (1 : ℝ) ≤ (T k) ^ 2 := one_le_pow₀ hTk1
    nlinarith [sq_nonneg (b + 1)]
  have hE : 9 * (1 + (b + |ε * T k|) ^ 2) *
      ‖burnolCriticalLineBaseKernelL2‖ ≤ E * (T k) ^ 2 := by
    dsimp [E]
    calc
      9 * (1 + (b + |ε * T k|) ^ 2) * ‖burnolCriticalLineBaseKernelL2‖
          ≤ 9 * ((1 + (b + 1) ^ 2) * (T k) ^ 2) *
              ‖burnolCriticalLineBaseKernelL2‖ := by gcongr
      _ = (9 * (1 + (b + 1) ^ 2) * ‖burnolCriticalLineBaseKernelL2‖) *
          (T k) ^ 2 := by ring
  have hpow : (T k) ^ (A - (N : ℝ)) * (T k) ^ 2 =
      (T k) ^ (A - (N : ℝ) + 2) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add hTk0]
    norm_num
  calc
    ‖burnolWeightedResidueHorizontalIntegralL2 G x₁ x₂ (ε * T k)‖
        ≤ M * (9 * (1 + (b + |ε * T k|) ^ 2) *
          ‖burnolCriticalLineBaseKernelL2‖) * |x₂ - x₁| := hedge
    _ ≤ M * (E * (T k) ^ 2) * (2 * b) := by
      gcongr
    _ = D * (T k) ^ (A - (N : ℝ) + 2) := by
      dsimp [M, D]
      rw [← hpow]
      ring

end

end RHTower
