import GaloisForLFunctions.RHTower.Sieve.BorelCaratheodoryLogDeriv
import GaloisForLFunctions.HTGeometry.AnalyticBallFinsetFactorization
import Mathlib.Analysis.Complex.AbsMax

/-!
# Landau's lemma

Let `f` be analytic on a disc, nonzero at the centre, and bounded there by `M` times its value at
the centre.  Removing only the zeros in the half-disc leaves a factor `h` which is zero-free on the
half-disc and still satisfies `‖h‖ ≤ M ‖h c‖` — the comparison is *exact*, because on the boundary
circle every removed zero is at distance at least `R/2`, which is at least its distance to the
centre.  No counting of zeros is needed.

The Borel–Carathéodory estimate then controls the logarithmic derivative of `h`, and

```text
‖ f'/f (z) - ∑_{ρ : ‖ρ - c‖ ≤ R/2} m_ρ / (z - ρ) ‖ ≤ 16 log M / R      for ‖z - c‖ ≤ R/8.
```

Each retained term has nonnegative real part at points to the right of every `ρ`, so discarding all
but one of them is a valid inequality — that is the step which replaces the mean-value estimate in a
zero-free region argument.
-/

namespace RHTower.Sieve

open Metric HTGeometry

/-- **Landau's lemma.**  The logarithmic derivative is the sum over the nearby zeros, up to
`16 log M / R`. -/
theorem landau_logDeriv {f : ℂ → ℂ} {c : ℂ} {R R₀ M : ℝ}
    (hR : 0 < R) (hRR₀ : R < R₀) (hM : 1 < M)
    (hf : AnalyticOnNhd ℂ f (ball c R₀))
    (hfc : f c ≠ 0)
    (hbound : ∀ w ∈ ball c R₀, ‖f w‖ ≤ M * ‖f c‖) :
    ∃ (Z₁ : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ ∈ Z₁, ‖ρ - c‖ ≤ R / 2) ∧ (∀ ρ ∈ Z₁, f ρ = 0) ∧
      (∀ w : ℂ, ‖w - c‖ ≤ R / 2 → f w = 0 → w ∈ Z₁) ∧ (∀ ρ ∈ Z₁, 1 ≤ m ρ) ∧
      ∀ z : ℂ, ‖z - c‖ ≤ R / 8 → f z ≠ 0 →
        ‖logDeriv f z - ∑ ρ ∈ Z₁, (m ρ : ℂ) / (z - ρ)‖ ≤ 16 * Real.log M / R := by
  classical
  set R' : ℝ := (R + R₀) / 2 with hR'def
  have hRR' : R < R' := by rw [hR'def]; linarith
  have hR'R₀ : R' < R₀ := by rw [hR'def]; linarith
  have hR'0 : 0 < R' := by linarith
  have hsub : closedBall c R' ⊆ ball c R₀ := fun w hw => by
    have : ‖w - c‖ ≤ R' := by simpa [dist_eq_norm] using hw
    exact mem_ball_iff_norm.mpr (by linarith)
  have hfcb : AnalyticOnNhd ℂ f (closedBall c R') := fun w hw => hf w (hsub hw)
  have hcball' : c ∈ ball c R' := by simpa using hR'0
  obtain ⟨Z, m, g, hZball, hmZ, hzeroZ, hg, hg0, heq⟩ :=
    exists_finset_zeroFree_factorization hfcb hcball' hfc
  -- split the zeros into those in the half-disc and the rest
  set p : ℂ → Prop := fun ρ => ‖ρ - c‖ ≤ R / 2 with hpdef
  set Z₁ : Finset ℂ := Z.filter p with hZ₁def
  set Z₂ : Finset ℂ := Z.filter (fun ρ => ¬ p ρ) with hZ₂def
  set P₁ : ℂ → ℂ := fun w => ∏ ρ ∈ Z₁, (w - ρ) ^ m ρ with hP₁def
  set h : ℂ → ℂ := fun w => (∏ ρ ∈ Z₂, (w - ρ) ^ m ρ) * g w with hhdef
  have hZ₁mem : ∀ ρ ∈ Z₁, ρ ∈ Z ∧ ‖ρ - c‖ ≤ R / 2 := by
    intro ρ hρ
    rw [hZ₁def, Finset.mem_filter] at hρ
    exact ⟨hρ.1, hρ.2⟩
  have hZ₂mem : ∀ ρ ∈ Z₂, ρ ∈ Z ∧ R / 2 < ‖ρ - c‖ := by
    intro ρ hρ
    rw [hZ₂def, Finset.mem_filter] at hρ
    exact ⟨hρ.1, lt_of_not_ge hρ.2⟩
  have hZzero : ∀ ρ ∈ Z, f ρ = 0 := fun ρ hρ => (hzeroZ ρ (hZball ρ hρ)).mpr hρ
  -- the factorisation `f = P₁ · h`
  have hfact : ∀ w ∈ ball c R', f w = P₁ w * h w := by
    intro w hw
    have hsplit := Finset.prod_filter_mul_prod_filter_not Z p (fun ρ => (w - ρ) ^ m ρ)
    rw [heq hw, hP₁def, hhdef, hZ₁def, hZ₂def]
    simp only []
    rw [← hsplit]
    ring
  -- `h` is analytic
  have hhan : AnalyticOnNhd ℂ h (ball c R') := by
    intro w hw
    exact AnalyticAt.mul (by fun_prop) (hg w hw)
  -- `h` has no zero in the half-disc
  have hh0 : ∀ w ∈ ball c (R / 2), h w ≠ 0 := by
    intro w hw
    have hwn : ‖w - c‖ < R / 2 := by simpa [dist_eq_norm] using hw
    have hwball : w ∈ ball c R' := mem_ball_iff_norm.mpr (by linarith)
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun ρ hρ => ?_) (hg0 w hwball)
    refine pow_ne_zero _ (sub_ne_zero.mpr ?_)
    intro hcon
    have := (hZ₂mem ρ hρ).2
    rw [← hcon] at this
    linarith
  -- the comparison on the boundary circle
  have hP₁c : P₁ c ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr ?_)
    intro hcon
    exact hfc (by rw [hcon]; exact hZzero ρ (hZ₁mem ρ hρ).1)
  have hsphere : ∀ w ∈ sphere c R, ‖h w‖ ≤ M * ‖h c‖ := by
    intro w hw
    have hwn : ‖w - c‖ = R := by simpa [dist_eq_norm] using hw
    have hwball : w ∈ ball c R' := mem_ball_iff_norm.mpr (by rw [hwn]; exact hRR')
    have hwball₀ : w ∈ ball c R₀ := mem_ball_iff_norm.mpr (by rw [hwn]; linarith)
    have hP₁w : ‖P₁ c‖ ≤ ‖P₁ w‖ := by
      rw [hP₁def]
      simp only [norm_prod, norm_pow]
      refine Finset.prod_le_prod (fun ρ _ => by positivity) fun ρ hρ => ?_
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
      have hρc : ‖ρ - c‖ ≤ R / 2 := (hZ₁mem ρ hρ).2
      have h1 : ‖c - ρ‖ = ‖ρ - c‖ := norm_sub_rev c ρ
      have h2 : R ≤ ‖w - ρ‖ + ‖ρ - c‖ := by
        calc R = ‖w - c‖ := hwn.symm
          _ ≤ ‖w - ρ‖ + ‖ρ - c‖ := by
              simpa using norm_sub_le_norm_sub_add_norm_sub w ρ c
      rw [h1]
      linarith
    have hP₁wpos : (0 : ℝ) < ‖P₁ w‖ := lt_of_lt_of_le (norm_pos_iff.mpr hP₁c) hP₁w
    have hfw : ‖P₁ w‖ * ‖h w‖ = ‖f w‖ := by
      rw [← norm_mul, ← hfact w hwball]
    have hfcv : ‖P₁ c‖ * ‖h c‖ = ‖f c‖ := by
      rw [← norm_mul, ← hfact c hcball']
    have hstep : ‖P₁ w‖ * ‖h w‖ ≤ ‖P₁ w‖ * (M * ‖h c‖) := by
      calc ‖P₁ w‖ * ‖h w‖ = ‖f w‖ := hfw
        _ ≤ M * ‖f c‖ := hbound w hwball₀
        _ = M * (‖P₁ c‖ * ‖h c‖) := by rw [hfcv]
        _ ≤ M * (‖P₁ w‖ * ‖h c‖) := by
            have hhc : (0 : ℝ) ≤ ‖h c‖ := norm_nonneg _
            have h1 : ‖P₁ c‖ * ‖h c‖ ≤ ‖P₁ w‖ * ‖h c‖ :=
              mul_le_mul_of_nonneg_right hP₁w hhc
            exact mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = ‖P₁ w‖ * (M * ‖h c‖) := by ring
    exact le_of_mul_le_mul_left hstep hP₁wpos
  -- maximum principle on the disc of radius `R`
  have hRclosed : closedBall c R ⊆ ball c R' := fun w hw => by
    have : ‖w - c‖ ≤ R := by simpa [dist_eq_norm] using hw
    exact mem_ball_iff_norm.mpr (by linarith)
  have hdcc : DiffContOnCl ℂ h (ball c R) := by
    have hdiff : DifferentiableOn ℂ h (closedBall c R) :=
      (hhan.mono hRclosed).differentiableOn
    exact ⟨hdiff.mono ball_subset_closedBall,
      hdiff.continuousOn.mono closure_ball_subset_closedBall⟩
  have hmax : ∀ w ∈ closedBall c R, ‖h w‖ ≤ M * ‖h c‖ := by
    intro w hw
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball) hdcc ?_ ?_
    · intro v hv
      rw [frontier_ball c (ne_of_gt hR)] at hv
      exact hsphere v hv
    · rw [closure_ball c (ne_of_gt hR)]
      exact hw
  -- Borel–Carathéodory on the half-disc
  have hhalfsub : ball c (R / 2) ⊆ closedBall c R := fun w hw => by
    have : ‖w - c‖ < R / 2 := by simpa [dist_eq_norm] using hw
    simp only [mem_closedBall, dist_eq_norm]
    linarith
  have hhan2 : AnalyticOnNhd ℂ h (ball c (R / 2)) :=
    hhan.mono (fun w hw => hRclosed (hhalfsub hw))
  have hbd2 : ∀ w ∈ ball c (R / 2), ‖h w‖ ≤ M * ‖h c‖ := fun w hw => hmax w (hhalfsub hw)
  have hmem : ∀ w : ℂ, ‖w - c‖ ≤ R / 2 → f w = 0 → w ∈ Z₁ := by
    intro w hw hfw
    have hwball : w ∈ ball c R' := mem_ball_iff_norm.mpr (by linarith)
    rw [hZ₁def, Finset.mem_filter]
    exact ⟨(hzeroZ w hwball).mp hfw, hw⟩
  refine ⟨Z₁, m, fun ρ hρ => (hZ₁mem ρ hρ).2, fun ρ hρ => hZzero ρ (hZ₁mem ρ hρ).1, hmem,
    fun ρ hρ => hmZ ρ (hZ₁mem ρ hρ).1, ?_⟩
  intro z hz hfz
  have hzR2 : ‖z - c‖ ≤ (R / 2) / 4 := by linarith
  have hlog := norm_deriv_div_le_of_norm_le (by linarith : (0 : ℝ) < R / 2) hM hhan2 hh0 hbd2 hzR2
  -- transport to `f`
  have hzball : z ∈ ball c R' := mem_ball_iff_norm.mpr (by linarith)
  have hzne : ∀ ρ ∈ Z₁, z ≠ ρ := by
    intro ρ hρ hcon
    exact hfz (by rw [hcon]; exact hZzero ρ (hZ₁mem ρ hρ).1)
  have hP₁z : P₁ z ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
      pow_ne_zero _ (sub_ne_zero.mpr (hzne ρ hρ))
  have hhz : h z ≠ 0 := by
    intro hcon
    exact hfz (by rw [hfact z hzball, hcon, mul_zero])
  have hEq : f =ᶠ[nhds z] fun w => P₁ w * h w := by
    filter_upwards [isOpen_ball.mem_nhds hzball] with w hw
    exact hfact w hw
  have hP₁diff : DifferentiableAt ℂ P₁ z := by
    rw [hP₁def]
    fun_prop
  have hhdiff : DifferentiableAt ℂ h z := (hhan z hzball).differentiableAt
  have hlogf : logDeriv f z = logDeriv P₁ z + logDeriv h z := by
    have hmul := logDeriv_mul (f := P₁) (g := h) z hP₁z hhz hP₁diff hhdiff
    rw [logDeriv_apply, hEq.deriv_eq, hEq.eq_of_nhds, ← logDeriv_apply]
    exact hmul
  have hlogP : logDeriv P₁ z = ∑ ρ ∈ Z₁, (m ρ : ℂ) / (z - ρ) :=
    logDeriv_finset_prod_pow hzne
  rw [hlogf, hlogP]
  simp only [add_sub_cancel_left]
  rw [logDeriv_apply]
  calc ‖deriv h z / h z‖ ≤ 8 * Real.log M / (R / 2) := hlog
    _ = 16 * Real.log M / R := by field_simp; ring

end RHTower.Sieve
