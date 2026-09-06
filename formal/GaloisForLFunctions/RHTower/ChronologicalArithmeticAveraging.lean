import GaloisForLFunctions.RHTower.ChronologicalRawHeatObstruction

/-!
# Arithmetic averaging of chronological heat errors

Finite Abel summation expresses each decreasing arithmetic weighting as a
positive average of actual raw heat residuals, with the terminal term retained.
Weights whose terminal value tends to one preserve the raw convergence condition;
the proof obtains boundedness by the existing Volterra induction.

Consequently a successful power-damping schedule must have a cofinally positive
`epsilon * log N` scale. This excludes only asymptotically negligible damping.
It neither excludes general arithmetic averaging nor proves the bounded-array
approximation target. No numerical result is used.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RHTower
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

/-- Arithmetic weighting of the raw Möbius coefficients. -/
def chronologicalWeightedHeatError (w : ℕ → ℝ) (N : ℕ) : ℝ → ℝ :=
  chronologicalHeatError (fun k => (ArithmeticFunction.moebius k : ℝ) * w k) N

/-- Exact finite Abel decomposition, including the terminal raw residual. -/
theorem chronologicalWeightedHeatError_abel (w : ℕ → ℝ) (h0 : w 0 = 1)
    (N : ℕ) (t : ℝ) :
    chronologicalWeightedHeatError w N t = w N * chronologicalRawHeatError N t +
      ∑ k ∈ Finset.range N, (w k-w (k+1)) * chronologicalRawHeatError k t := by
  induction N with
  | zero => simp [chronologicalWeightedHeatError, chronologicalHeatError, chronologicalRawHeatError, h0]
  | succ N ih =>
    have hD : chronologicalWeightedHeatError w (N+1) t = chronologicalWeightedHeatError w N t +
        (ArithmeticFunction.moebius (N+1) : ℝ)*w (N+1)*fusionBoseDefect (((N+1:ℕ):ℝ)*t) := by
      simp only [chronologicalWeightedHeatError, chronologicalHeatError,
        Finset.sum_Ioc_succ_top (Nat.zero_le N)]
      ring
    have hR : chronologicalRawHeatError (N+1) t = chronologicalRawHeatError N t +
        (ArithmeticFunction.moebius (N+1) : ℝ)*fusionBoseDefect (((N+1:ℕ):ℝ)*t) := by
      simp only [chronologicalRawHeatError, Finset.sum_Ioc_succ_top (Nat.zero_le N)]
      ring
    rw [hD, ih, hR, Finset.sum_range_succ]
    ring

private theorem chronological_norm_const_mul {f : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c) :
    chronologicalL2Norm (fun t => c*f t) = c*chronologicalL2Norm f := by
  change lpNorm (c • f) 2 chronologicalPositiveVolume = c * lpNorm f 2 chronologicalPositiveVolume
  rw [lpNorm_const_smul]
  simp [Real.norm_eq_abs, abs_of_nonneg hc]

/-- The actual normalized discrepancy is controlled solely by strict earlier
raw errors, with exact total averaging mass `(1-w N)/w N`. -/
theorem chronologicalWeightedHeatError_discrepancy (w : ℕ → ℝ) (h0 : w 0 = 1)
    (hw : Antitone w) (hp : ∀ n, 0 < w n) (N : ℕ) (C : ℝ)
    (hprev : ∀ k < N, chronologicalL2Norm (chronologicalRawHeatError k) ≤ C) :
    chronologicalL2Norm (fun t => (w N)⁻¹ * chronologicalWeightedHeatError w N t -
      chronologicalRawHeatError N t) ≤ ((w N)⁻¹-1)*C := by
  let F : ℕ → ℝ → ℝ := fun k t => ((w N)⁻¹*(w k-w (k+1))) * chronologicalRawHeatError k t
  have hc (k : ℕ) : 0 ≤ (w N)⁻¹*(w k-w (k+1)) :=
    mul_nonneg (inv_pos.mpr (hp N)).le (sub_nonneg.mpr (hw (Nat.le_succ k)))
  have he : (fun t => (w N)⁻¹ * chronologicalWeightedHeatError w N t -
      chronologicalRawHeatError N t) = ∑ k ∈ Finset.range N, F k := by
    funext t
    simp only [Finset.sum_apply, F]
    rw [chronologicalWeightedHeatError_abel w h0 N t, mul_add, ← mul_assoc,
      inv_mul_cancel₀ (hp N).ne', one_mul, add_sub_cancel_left, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hm (k : ℕ) (_hk : k ∈ Finset.range N) : MemLp (F k) 2 chronologicalPositiveVolume :=
    (chronologicalRawHeatError_memLp k).const_mul _
  rw [he]
  calc
    _ ≤ ∑ k ∈ Finset.range N, chronologicalL2Norm (F k) := lpNorm_sum_le hm (by simp)
    _ = ∑ k ∈ Finset.range N, ((w N)⁻¹*(w k-w (k+1))) *
        chronologicalL2Norm (chronologicalRawHeatError k) := by
      apply Finset.sum_congr rfl
      intro k _
      exact chronological_norm_const_mul (hc k)
    _ ≤ ∑ k ∈ Finset.range N, ((w N)⁻¹*(w k-w (k+1))) * C := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hprev k (Finset.mem_range.mp hk)) (hc k)
    _ = ((w N)⁻¹-1)*C := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_range_sub', h0]
      have hn := (hp N).ne'
      field_simp

/-- Near-identity positive arithmetic weighting has precisely the raw norm
convergence condition; boundedness is proved by Volterra induction, not assumed. -/
theorem chronologicalWeightedHeatError_near_identity_iff (w : ℕ → ℕ → ℝ)
    (h0 : ∀ N, w N 0 = 1) (hw : ∀ N, Antitone (w N)) (hp : ∀ N k, 0 < w N k)
    (ht : Tendsto (fun N => w N N) atTop (𝓝 1)) :
    Tendsto (fun N => chronologicalL2Norm (chronologicalWeightedHeatError (w N) N)) atTop (𝓝 0) ↔
      Tendsto (fun N => chronologicalL2Norm (chronologicalRawHeatError N)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun N => (w N N)⁻¹) atTop (𝓝 1) := by
    simpa using ht.inv₀ (by simp : (1:ℝ) ≠ 0)
  have he : Tendsto (fun N => (w N N)⁻¹-1) atTop (𝓝 0) := by
    simpa using hinv.sub_const 1
  have hscaled := chronologicalVolterra_zero_convergence_iff
    (r := fun N => chronologicalL2Norm (chronologicalRawHeatError N))
    (s := fun N => (w N N)⁻¹ * chronologicalL2Norm (chronologicalWeightedHeatError (w N) N))
    (e := fun N => (w N N)⁻¹-1)
    (fun N => chronologicalL2Norm_nonneg _) (fun N => mul_nonneg
      (inv_pos.mpr (hp N N)).le (chronologicalL2Norm_nonneg _)) he (by
        intro N C hC hprev
        have hd := chronologicalWeightedHeatError_discrepancy (w N) (h0 N) (hw N)
          (hp N) N C hprev
        have hD : MemLp (chronologicalWeightedHeatError (w N) N) 2 chronologicalPositiveVolume :=
          chronologicalHeatError_memLp _ _
        have hscaledD := hD.const_mul ((w N N)⁻¹)
        have hR := lpNorm_le_lpNorm_add_lpNorm_sub' hscaledD (by simp : (1:ENNReal) ≤ 2)
          (f := chronologicalRawHeatError N)
        have hS := lpNorm_le_lpNorm_add_lpNorm_sub' (chronologicalRawHeatError_memLp N)
          (by simp : (1:ENNReal) ≤ 2)
          (f := fun t => (w N N)⁻¹*chronologicalWeightedHeatError (w N) N t)
        rw [lpNorm_sub_comm] at hR
        change chronologicalL2Norm (chronologicalRawHeatError N) ≤
          chronologicalL2Norm (fun t => (w N N)⁻¹*chronologicalWeightedHeatError (w N) N t) +
          chronologicalL2Norm (fun t => (w N N)⁻¹*chronologicalWeightedHeatError (w N) N t -
            chronologicalRawHeatError N t) at hR
        change chronologicalL2Norm (fun t => (w N N)⁻¹*chronologicalWeightedHeatError (w N) N t) ≤
          chronologicalL2Norm (chronologicalRawHeatError N) +
          chronologicalL2Norm (fun t => (w N N)⁻¹*chronologicalWeightedHeatError (w N) N t -
            chronologicalRawHeatError N t) at hS
        rw [chronological_norm_const_mul (inv_pos.mpr (hp N N)).le] at hR hS
        have hwN : w N N ≤ 1 := by simpa [h0 N] using hw N (Nat.zero_le N)
        have hinvN : 1 ≤ (w N N)⁻¹ := (one_le_inv₀ (hp N N)).mpr hwN
        constructor <;> nlinarith)
  constructor
  · intro hD
    apply hscaled.mp
    simpa using hinv.mul hD
  · intro hR
    have hs := ht.mul (hscaled.mpr hR)
    simp only [mul_zero] at hs
    convert hs using 1
    funext N
    rw [← mul_assoc, mul_inv_cancel₀ (hp N N).ne', one_mul]

/-- Arithmetic power damping, written with the real exponential and logarithm. -/
def chronologicalArithmeticWeight (ε : ℝ) (k : ℕ) : ℝ := Real.exp (-ε * Real.log k)

theorem chronologicalArithmeticWeight_zero (ε : ℝ) : chronologicalArithmeticWeight ε 0 = 1 := by
  simp [chronologicalArithmeticWeight]

theorem chronologicalArithmeticWeight_pos (ε : ℝ) (k : ℕ) :
    0 < chronologicalArithmeticWeight ε k := Real.exp_pos _

theorem chronologicalArithmeticWeight_antitone {ε : ℝ} (hε : 0 ≤ ε) :
    Antitone (chronologicalArithmeticWeight ε) := by
  intro a b hab
  apply Real.exp_le_exp.mpr
  have hlog : Real.log (a:ℝ) ≤ Real.log (b:ℝ) := by
    by_cases ha : a=0
    · simp only [ha, Nat.cast_zero, Real.log_zero]
      exact Real.log_natCast_nonneg _
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero ha) (by exact_mod_cast hab)
  exact mul_le_mul_of_nonpos_left hlog (neg_nonpos.mpr hε)

/-- Arithmetic damping keeps every actual Möbius coefficient in the unit box. -/
theorem chronologicalArithmetic_coefficient_bound {ε : ℝ} (hε : 0 ≤ ε) (k : ℕ) :
    |(ArithmeticFunction.moebius k : ℝ) * chronologicalArithmeticWeight ε k| ≤ 1 := by
  have hp := (chronologicalArithmeticWeight_pos ε k).le
  have hw : chronologicalArithmeticWeight ε k ≤ 1 := by
    simpa [chronologicalArithmeticWeight_zero] using
      chronologicalArithmeticWeight_antitone hε (Nat.zero_le k)
  have hmu : |(ArithmeticFunction.moebius k : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
  rw [abs_mul, abs_of_nonneg hp]
  exact (mul_le_mul_of_nonneg_right hmu hp).trans (by simpa using hw)

/-- Total mass of the finite chronological Abel average is exactly one. -/
theorem chronologicalAbel_average_mass (w : ℕ → ℝ) (h0 : w 0 = 1) (N : ℕ) :
    w N + (∑ k ∈ Finset.range N, (w k-w (k+1))) = 1 := by
  rw [Finset.sum_range_sub', h0]
  ring

/-- Closed scale obstruction: epsilon times log cutoff cannot tend to zero
along a successful arithmetic power-damping schedule. -/
theorem chronologicalArithmeticDamping_no_small_scale :
    ¬ ∃ ε : ℕ → ℝ, (∀ N, 0 ≤ ε N) ∧
      Tendsto (fun N => ε N * Real.log N) atTop (𝓝 0) ∧
      Tendsto (fun N => chronologicalL2Norm
        (chronologicalWeightedHeatError (chronologicalArithmeticWeight (ε N)) N))
        atTop (𝓝 0) := by
  rintro ⟨ε, hε, hscale, hD⟩
  have ht : Tendsto (fun N => chronologicalArithmeticWeight (ε N) N) atTop (𝓝 1) := by
    simpa [chronologicalArithmeticWeight, neg_mul, Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp hscale.neg
  exact chronologicalRawHeat_not_convergent
    ((chronologicalWeightedHeatError_near_identity_iff
      (fun N => chronologicalArithmeticWeight (ε N))
      (fun N => chronologicalArithmeticWeight_zero _) (fun N => chronologicalArithmeticWeight_antitone (hε N))
      (fun N k => chronologicalArithmeticWeight_pos _ _) ht).mp hD)

/-- Positive scale survivor: a successful power-damping schedule must move a
fixed positive fraction of its Abel mass away from the terminal cutoff
cofinally; equivalently epsilon times log cutoff has a cofinal positive floor. -/
theorem chronologicalArithmeticDamping_scale_floor (ε : ℕ → ℝ)
    (hε : ∀ N, 0 ≤ ε N)
    (hD : Tendsto (fun N => chronologicalL2Norm
      (chronologicalWeightedHeatError (chronologicalArithmeticWeight (ε N)) N))
      atTop (𝓝 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧ δ ≤ ε N * Real.log N := by
  by_contra hf
  push Not at hf
  apply chronologicalArithmeticDamping_no_small_scale
  refine ⟨ε, hε, ?_, hD⟩
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨M, hM⟩ := hf δ hδ
  refine ⟨M, ?_⟩
  intro N hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (hε N) (Real.log_natCast_nonneg N))]
  exact hM N hN

end RHTower
