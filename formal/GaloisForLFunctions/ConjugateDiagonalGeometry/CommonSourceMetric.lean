import GaloisForLFunctions.ConjugateDiagonalGeometry.CommonSourceRegulator

/-!
# Simultaneous arithmetic recovery of the collided metric

The source schedule is fixed by one weight, independently of every test.
Positivity converts convergence of that weight's mass and compact current
convergence into convergence for all dominated smooth tests. Every compact
source transform belongs to this class.
-/

open Complex MeasureTheory Filter Set Metric
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 ArithmeticPolarization _root_.RHTower

private theorem integrable_compact_source (n k : ℕ) (φ : ℂ → ℝ) (hφ : Continuous φ) :
    Integrable (fun z => sourceCutoff n z * φ z * xiCurvatureDensity (sourceRegulator k) z) :=
  (((sourceCutoff n).continuous.mul hφ).mul
    (continuous_xiCurvatureDensity (sourceRegulator_pos k))).integrable_of_hasCompactSupport
      (sourceCutoff n).hasCompactSupport.mul_right.mul_right

/-- Positivity is available at every finite stage of the common source sequence. -/
theorem commonSourceReading_mono (φ ψ : ℂ → ℝ) (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : ∀ z, φ z ≤ ψ z) (n : ℕ) : commonSourceReading φ n ≤ commonSourceReading ψ n := by
  unfold commonSourceReading xiCompactSourceReading
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr Real.pi_pos.le)
  apply integral_mono (integrable_compact_source n _ φ hφ)
    (integrable_compact_source n _ ψ hψ)
  intro z
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (h z) (sourceCutoff n).nonneg)
    (xiCurvatureDensity_nonneg (sourceRegulator_pos _).le z)

private theorem commonSourceReading_add (φ ψ : ℂ → ℝ)
    (hφ : Continuous φ) (hψ : Continuous ψ) (n : ℕ) :
    commonSourceReading (fun z => φ z + ψ z) n =
      commonSourceReading φ n + commonSourceReading ψ n := by
  unfold commonSourceReading xiCompactSourceReading
  simp_rw [mul_add, add_mul]
  rw [integral_add (integrable_compact_source n _ φ hφ)
    (integrable_compact_source n _ ψ hψ), mul_add]

private theorem commonSourceReading_sub (φ ψ : ℂ → ℝ)
    (hφ : Continuous φ) (hψ : Continuous ψ) (n : ℕ) :
    commonSourceReading (fun z => φ z - ψ z) n =
      commonSourceReading φ n - commonSourceReading ψ n := by
  unfold commonSourceReading xiCompactSourceReading
  simp_rw [mul_sub, sub_mul]
  rw [integral_sub (integrable_compact_source n _ φ hφ)
    (integrable_compact_source n _ ψ hψ), mul_sub]

private theorem commonSourceReading_const_mul (C : ℝ) (φ : ℂ → ℝ) (n : ℕ) :
    commonSourceReading (fun z => C * φ z) n = C * commonSourceReading φ n := by
  unfold commonSourceReading xiCompactSourceReading
  have he : (fun z => sourceCutoff n z * (C * φ z) *
      xiCurvatureDensity (sourceRegulator (commonSourceIndex n)) z) =
      (fun z => C * (sourceCutoff n z * φ z *
        xiCurvatureDensity (sourceRegulator (commonSourceIndex n)) z)) := by
    funext z
    ring
  rw [he, integral_const_mul]
  ring

private theorem tendsto_of_exhaustion_bounds {A : ℕ → ℝ} {a : ℝ}
    {lower upper : ℕ → ℕ → ℝ} {lowerLimit upperLimit : ℕ → ℝ}
    (hl : ∀ m, Tendsto (lower m) atTop (𝓝 (lowerLimit m)))
    (hu : ∀ m, Tendsto (upper m) atTop (𝓝 (upperLimit m)))
    (hll : Tendsto lowerLimit atTop (𝓝 a))
    (hul : Tendsto upperLimit atTop (𝓝 a))
    (hb : ∀ m n, lower m n ≤ A n ∧ A n ≤ upper m n) :
    Tendsto A atTop (𝓝 a) := by
  rw [tendsto_order]
  constructor
  · intro b hb'
    obtain ⟨m, hm⟩ := (hll.eventually_const_lt hb').exists
    exact ((hl m).eventually_const_lt hm).mono fun n hn => hn.trans_le (hb m n).1
  · intro b hb'
    obtain ⟨m, hm⟩ := (hul.eventually_lt_const hb').exists
    exact ((hu m).eventually_lt_const hm).mono fun n hn => (hb m n).2.trans_lt hn

/-- One source-defined sequence recovers every nonnegative smooth test controlled by the fixed weight. -/
theorem tendsto_commonSourceReading_of_dominated (φ : ℂ → ℝ)
    (hp : ContDiff ℝ 2 φ) (hn : ∀ z, 0 ≤ φ z)
    {C : ℝ} (hb : ∀ z, φ z ≤ C * universalSourceWeight z) :
    Tendsto (commonSourceReading φ) atTop (𝓝 (zetaSourceTrace φ)) := by
  let φm : ℕ → ℂ → ℝ := fun m z => sourceCutoff m z * φ z
  let wm : ℕ → ℂ → ℝ := fun m z => sourceCutoff m z * universalSourceWeight z
  have hφm (m : ℕ) : ContDiff ℝ 2 (φm m) := (sourceCutoff m).contDiff.mul hp
  have hwm (m : ℕ) : ContDiff ℝ 2 (wm m) :=
    (sourceCutoff m).contDiff.mul contDiff_universalSourceWeight
  have hs : Summable (fun ρ : zetaZeroConfig.carrier => (zetaZeroConfig.mult ρ : ℝ) * φ ρ) := by
    refine Summable.of_nonneg_of_le
      (fun ρ => mul_nonneg (Nat.cast_nonneg _) (hn ρ))
      (fun ρ => ?_) (summable_universalSourceWeight.mul_left C)
    calc
      (zetaZeroConfig.mult ρ : ℝ) * φ ρ ≤
          (zetaZeroConfig.mult ρ : ℝ) * (C * universalSourceWeight ρ) :=
        mul_le_mul_of_nonneg_left (hb ρ) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hl (m : ℕ) : Tendsto (commonSourceReading (φm m)) atTop
      (𝓝 (zetaSourceTrace (φm m))) :=
    tendsto_commonSourceReading_compact _ (hφm m) (sourceCutoff m).hasCompactSupport.mul_right
  have hw (m : ℕ) : Tendsto (commonSourceReading (wm m)) atTop
      (𝓝 (zetaSourceTrace (wm m))) :=
    tendsto_commonSourceReading_compact _ (hwm m) (sourceCutoff m).hasCompactSupport.mul_right
  have hφlim : Tendsto (fun m => zetaSourceTrace (φm m)) atTop (𝓝 (zetaSourceTrace φ)) :=
    tendsto_cutoff_zetaSourceTrace φ hs
  have hwlim : Tendsto (fun m => zetaSourceTrace (wm m)) atTop
      (𝓝 (zetaSourceTrace universalSourceWeight)) :=
    tendsto_cutoff_zetaSourceTrace universalSourceWeight summable_universalSourceWeight
  apply tendsto_of_exhaustion_bounds hl
    (fun m => (hl m).add ((tendsto_commonSourceReading_weight.sub (hw m)).const_mul C))
    hφlim
  · have hconst : Tendsto (fun _ : ℕ => zetaSourceTrace universalSourceWeight) atTop
        (𝓝 (zetaSourceTrace universalSourceWeight)) := tendsto_const_nhds
    simpa only [sub_self, mul_zero, add_zero] using
      hφlim.add ((hconst.sub hwlim).const_mul C)
  · intro m n
    constructor
    · apply commonSourceReading_mono _ _ (hφm m).continuous hp.continuous
      intro z
      exact mul_le_of_le_one_left (hn z) (sourceCutoff m).le_one
    · have hpoint (z : ℂ) : φ z ≤ φm m z + C * (universalSourceWeight z - wm m z) := by
        have hc : 0 ≤ 1 - sourceCutoff m z := sub_nonneg.mpr (sourceCutoff m).le_one
        calc
          φ z = φm m z + (1 - sourceCutoff m z) * φ z := by dsimp [φm]; ring
          _ ≤ φm m z + (1 - sourceCutoff m z) * (C * universalSourceWeight z) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left (hb z) hc)
          _ = _ := by dsimp [wm]; ring
      have h := commonSourceReading_mono φ
        (fun z => φm m z + C * (universalSourceWeight z - wm m z)) hp.continuous
        ((hφm m).continuous.add (continuous_const.mul
          (contDiff_universalSourceWeight.continuous.sub (hwm m).continuous))) hpoint n
      have hψ : Continuous (fun z => C * (universalSourceWeight z - wm m z)) :=
        continuous_const.mul (contDiff_universalSourceWeight.continuous.sub (hwm m).continuous)
      rw [commonSourceReading_add (φm m) (fun z => C * (universalSourceWeight z - wm m z))
        (hφm m).continuous hψ n,
        commonSourceReading_const_mul C (fun z => universalSourceWeight z - wm m z) n,
        commonSourceReading_sub universalSourceWeight (wm m)
          contDiff_universalSourceWeight.continuous (hwm m).continuous n] at h
      exact h

/-- The arithmetic sequence is independent of the compact test and recovers its full collided norm. -/
theorem tendsto_commonSourceReading_collided (f : CompactTest) :
    Tendsto (commonSourceReading (fun z => Complex.normSq (tr f.1 z))) atTop
      (𝓝 (collidedForm zetaZeroConfig f.1)) := by
  obtain ⟨C, _, hb⟩ := normSq_tr_le_universalSourceWeight f
  have hp : ContDiff ℝ 2 (fun z => Complex.normSq (tr f.1 z)) := by
    simpa only [Complex.normSq_eq_norm_sq] using ContDiff.norm_sq ℂ (contDiff_tr f)
  exact tendsto_commonSourceReading_of_dominated _ hp
    (fun z => Complex.normSq_nonneg _) hb

/-- Translation raises the depth-kernel moment by one through an exact symmetric difference. -/
theorem sourceDepthKernel_second_difference (f : CompactTest) (L : ℝ) (j : ℕ) (z : ℂ) :
    sourceDepthKernel (sourceTranslate L f) L j z +
      sourceDepthKernel (sourceTranslate (-L) f) L j z -
        2 * sourceDepthKernel f L j z = sourceDepthKernel f L (j + 1) z := by
  simp only [sourceDepthKernel, sourceTranslate, tr_translate, Complex.normSq_mul,
    normSq_exp_translate, pow_succ, depthKernel, Real.cosh_eq]
  rw [show 2 * (z.re - 1 / 2) * (-L) = -(2 * (z.re - 1 / 2) * L) by ring]
  ring

/-- The same weight controls every finite depth moment, at every fixed translation scale. -/
theorem sourceDepthKernel_le_universalSourceWeight (f : CompactTest) (L : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, sourceDepthKernel f L j z ≤ C * universalSourceWeight z := by
  induction j generalizing f with
  | zero =>
      simpa only [sourceDepthKernel, pow_zero, mul_one] using
        normSq_tr_le_universalSourceWeight f
  | succ j ih =>
      obtain ⟨Cp, hCp, hp⟩ := ih (sourceTranslate L f)
      obtain ⟨Cm, hCm, hm⟩ := ih (sourceTranslate (-L) f)
      refine ⟨Cp + Cm, add_nonneg hCp hCm, fun z => ?_⟩
      have hn : 0 ≤ sourceDepthKernel f L j z :=
        mul_nonneg (Complex.normSq_nonneg _) (pow_nonneg (depthKernel_nonneg _ _) j)
      rw [← sourceDepthKernel_second_difference]
      calc
        sourceDepthKernel (sourceTranslate L f) L j z +
            sourceDepthKernel (sourceTranslate (-L) f) L j z -
              2 * sourceDepthKernel f L j z ≤
            sourceDepthKernel (sourceTranslate L f) L j z +
              sourceDepthKernel (sourceTranslate (-L) f) L j z :=
          sub_le_self _ (mul_nonneg (by norm_num) hn)
        _ ≤ Cp * universalSourceWeight z + Cm * universalSourceWeight z :=
          add_le_add (hp z) (hm z)
        _ = _ := by ring

/-- A single arithmetic sequence computes all tests, scales and finite collided depth moments. -/
theorem tendsto_commonSourceReading_depth_moment (f : CompactTest) (L : ℝ) (j : ℕ) :
    Tendsto (commonSourceReading (sourceDepthKernel f L j)) atTop
      (𝓝 (∑' ρ : zetaZeroConfig.carrier,
        zetaWeight f ρ * depthKernel L (zetaDepth ρ) ^ j)) := by
  obtain ⟨C, _, hb⟩ := sourceDepthKernel_le_universalSourceWeight f L j
  have h := tendsto_commonSourceReading_of_dominated _ (contDiff_sourceDepthKernel f L j)
    (fun z => mul_nonneg (Complex.normSq_nonneg _) (pow_nonneg (depthKernel_nonneg _ _) j))
    hb
  have he : zetaSourceTrace (sourceDepthKernel f L j) =
      ∑' ρ : zetaZeroConfig.carrier,
        zetaWeight f ρ * depthKernel L (zetaDepth ρ) ^ j := by
    apply tsum_congr
    intro ρ
    dsimp [sourceDepthKernel, zetaWeight, zetaDepth]
    ring
  simpa only [he] using h

/-- The same sequence reads the complete symmetric Hecke defect. -/
theorem tendsto_commonSourceReading_heckeDefect (f : CompactTest) (L : ℝ) :
    Tendsto (commonSourceReading (sourceDepthKernel f L 1)) atTop (𝓝 (heckeDefect f L)) := by
  simpa only [pow_one, heckeDefect] using tendsto_commonSourceReading_depth_moment f L 1

end GaloisForLFunctions.ConjugateDiagonalGeometry
