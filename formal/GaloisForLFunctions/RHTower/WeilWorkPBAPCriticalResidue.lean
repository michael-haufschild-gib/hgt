import GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalLaplace

/-!
# The pole weight is the residue of every actual modified completion

The coefficient series and its residue follow from smooth full-test positivity.
No coefficient signs, summability, or continuation are separate premises.
-/

open Complex MeasureTheory Filter Topology Set Zeta23
open scoped Real ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

theorem continuous_autoLaplaceReal {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) :
    Continuous (autoLaplaceReal g) := by
  have hc := Complex.continuous_re.comp
    ((differentiable_autoLaplace hg hgc hsupp).continuous.comp Complex.continuous_ofReal)
  simpa only [Function.comp_def, autoLaplace_ofReal, Complex.ofReal_re] using hc

theorem poleConst_narrowG_pos : 0 < poleConst (narrowG 0) := by
  have hg : Continuous (narrowG 0) := (contDiff_narrowG 0).continuous
  have hgc := hasCompactSupport_narrowG 0
  have hg0 : narrowG 0 0 = 1 :=
    (narrowBump 0).one_of_mem_closedBall (Metric.mem_closedBall_self (narrowBump 0).rIn_pos.le)
  have hp (r : ℝ) : 0 < ∫ u : ℝ, narrowG 0 u * Real.exp (r * u / 2) := by
    exact Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hg.mul (by fun_prop)) hgc.mul_right
      (fun u => mul_nonneg (narrowBump 0).nonneg (Real.exp_pos _).le)
      (x := 0) (by simp [hg0])
  unfold poleConst
  exact mul_pos (by simpa only [neg_one_mul] using hp (-1))
    (by simpa only [one_mul] using hp 1)

/-- The residue is forced by actual positivity on every smooth compact test. -/
theorem criticalDirichletReal_residue {a b C : ℝ} (ha : 0 ≤ a) {lam : ℕ → ℝ}
    (h : ∀ f : SmoothTest, testAtoms lam f.1 ≤ criticalDatum a b C f.1.1) :
    Tendsto (fun x : ℝ => x * criticalDirichletReal lam (1 + x)) (𝓝[>] 0) (𝓝 b) := by
  let g := narrowG 0
  let P := poleConst g
  let B := autoLaplaceReal g
  have hP : 0 < P := poleConst_narrowG_pos
  have hg : ContDiff ℝ ∞ g := (narrowBump 0).contDiff
  have hgc : HasCompactSupport g := hasCompactSupport_narrowG 0
  obtain ⟨M, hM0, hM⟩ := critical_laplace_remainder_bound ha h hg hgc (narrowG_supp 0)
    (fun _ => (narrowBump 0).nonneg)
  let E : ℝ → ℝ := fun x => x * (B (1/2+x) * criticalDirichletReal lam (1+x)) -
    b*P - x*(b*P/(1+x))
  have hx : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hmajor : Tendsto (fun x : ℝ => x * M / (1/2+x)) (𝓝[>] 0) (𝓝 0) := by
    have ht := (hx.mul_const M).div (tendsto_const_nhds.add hx)
      (by norm_num : (1/2:ℝ)+0 ≠ 0)
    simp only [zero_mul, zero_div, add_zero] at ht
    exact ht.congr fun _ => rfl
  have hsmall : Tendsto E (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) _ hmajor
    filter_upwards [self_mem_nhdsWithin] with x hx0
    have hxpos : 0 < x := hx0
    have hbound := hM (1/2+x) (by linarith)
    have heq : E x = x * (B (1/2+x) * criticalDirichletReal lam (1+x) -
        b*P/x - b*P/(1+x)) := by
      dsimp [E]
      field_simp [hxpos.ne']
    have hden1 : (1/2:ℝ)+x-1/2 = x := by ring
    have hden2 : (1/2:ℝ)+x+1/2 = 1+x := by ring
    have harg : (1/2:ℝ)+(1/2+x) = 1+x := by ring
    rw [hden1, hden2, harg] at hbound
    rw [heq, abs_mul, abs_of_pos hxpos]
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hbound hxpos.le
  have hregular : Tendsto (fun x : ℝ => x * (b*P/(1+x))) (𝓝[>] 0) (𝓝 0) := by
    simpa using hx.mul (tendsto_const_nhds.div (tendsto_const_nhds.add hx)
      (by norm_num : (1:ℝ)+0 ≠ 0))
  have hproduct : Tendsto (fun x : ℝ => x * (B (1/2+x) * criticalDirichletReal lam (1+x)))
      (𝓝[>] 0) (𝓝 (b*P)) := by
    have ht := (hsmall.add_const (b*P)).add hregular
    simp only [zero_add, add_zero] at ht
    apply ht.congr
    intro x
    dsimp [E]
    ring
  have hB : Tendsto (fun x : ℝ => B (1/2+x)) (𝓝[>] 0) (𝓝 P) := by
    have hc := (continuous_autoLaplaceReal (contDiff_narrowG 0) hgc (narrowG_supp 0)).tendsto (1/2)
    have hxhalf : Tendsto (fun x : ℝ => 1/2+x) (𝓝[>] 0) (𝓝 (1/2)) := by
      simpa only [add_zero] using (tendsto_const_nhds.add hx :
        Tendsto (fun x : ℝ => 1/2+x) (𝓝[>] 0) (𝓝 (1/2+0)))
    have he := hc.comp hxhalf
    rw [autoLaplaceReal_half (contDiff_narrowG 0) (narrowG_supp 0)] at he
    exact he.congr fun _ => rfl
  have hdiv := hproduct.div hB hP.ne'
  have hBne : ∀ᶠ x : ℝ in 𝓝[>] 0, B (1/2+x) ≠ 0 :=
    hB.eventually_ne hP.ne'
  have heq : (fun x : ℝ => x * (B (1/2+x) * criticalDirichletReal lam (1+x)) / B (1/2+x))
      =ᶠ[𝓝[>] 0] (fun x => x * criticalDirichletReal lam (1+x)) := by
    filter_upwards [hBne] with x hbx
    calc
      _ = (x * criticalDirichletReal lam (1+x)) * B (1/2+x) / B (1/2+x) := by
        congr 1
        ring
      _ = _ := mul_div_cancel_right₀ _ hbx
  simpa only [mul_div_cancel_right₀ b hP.ne'] using hdiv.congr' heq

end RHTower.WeilWorkPBAP
