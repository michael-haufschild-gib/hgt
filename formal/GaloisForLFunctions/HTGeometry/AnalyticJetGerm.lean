import GaloisForLFunctions.HTGeometry.UniformSecondOrderJet
import GaloisForLFunctions.HTGeometry.ElementaryHorizonJets
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Analytic horizon-jet germs

A family `F u z` has an analytic horizon-jet germ at `w₀` when, on some closed ball around `w₀`
and some horizon radius, it has a uniform second-order jet whose two coefficient functions are
analytic at `w₀`.  Germs are closed under sums, products, scalar multiples by functions analytic
at `w₀`, and powers, because analytic coefficients are bounded near `w₀`.  This packages the
bookkeeping needed to assemble the horizon jet of a product of many channels without writing the
composite coefficient functions explicitly.
-/

namespace GaloisForLFunctions.HTGeometry
open Set Filter Topology Metric
noncomputable section
set_option autoImplicit false

/-- Analytic horizon-jet germ at `w₀`. -/
def AnalyticJet2At (w₀ : ℂ) (F : ℂ → ℝ → ℂ) : Prop :=
  ∃ R b : ℝ, 0 < R ∧ 0 < b ∧ b ≤ 1 / 2 ∧ ∃ c₀ c₁ : ℂ → ℂ, ∃ C : ℝ, 0 ≤ C ∧
    AnalyticAt ℂ c₀ w₀ ∧ AnalyticAt ℂ c₁ w₀ ∧ HasUniformJet2 (closedBall w₀ R) b F c₀ c₁ C

/-- A function continuous at `w₀` is bounded on some closed ball around `w₀`. -/
theorem exists_closedBall_norm_le_of_continuousAt {w₀ : ℂ} {c : ℂ → ℂ} (hc : ContinuousAt c w₀) :
    ∃ r : ℝ, 0 < r ∧ ∀ u ∈ closedBall w₀ r, ‖c u‖ ≤ ‖c w₀‖ + 1 := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    (hc.eventually (Metric.ball_mem_nhds (c w₀) (zero_lt_one)))
  refine ⟨ε / 2, by positivity, fun u hu => ?_⟩
  have hd : dist u w₀ < ε := by
    have := mem_closedBall.mp hu; linarith
  have := mem_ball.mp (hball hd)
  rw [dist_eq_norm] at this
  calc ‖c u‖ = ‖(c u - c w₀) + c w₀‖ := by ring_nf
    _ ≤ ‖c u - c w₀‖ + ‖c w₀‖ := norm_add_le _ _
    _ ≤ ‖c w₀‖ + 1 := by linarith

theorem AnalyticJet2At.of_jet {w₀ : ℂ} {F : ℂ → ℝ → ℂ} {R b C : ℝ} {c₀ c₁ : ℂ → ℂ}
    (hR : 0 < R) (hb : 0 < b) (hb1 : b ≤ 1 / 2)
    (h₀ : AnalyticAt ℂ c₀ w₀) (h₁ : AnalyticAt ℂ c₁ w₀)
    (h : HasUniformJet2 (closedBall w₀ R) b F c₀ c₁ C) : AnalyticJet2At w₀ F :=
  ⟨R, b, hR, hb, hb1, c₀, c₁, max C 0, le_max_right _ _, h₀, h₁, h.mono_const (le_max_left _ _)⟩

/-- Restrict a germ to smaller radii, with bounded coefficients. -/
theorem AnalyticJet2At.exists_bounded {w₀ : ℂ} {F : ℂ → ℝ → ℂ} (h : AnalyticJet2At w₀ F)
    {R' b' : ℝ} (hR' : 0 < R') (hb' : 0 < b') :
    ∃ R b : ℝ, 0 < R ∧ R ≤ R' ∧ 0 < b ∧ b ≤ b' ∧ b ≤ 1 / 2 ∧ ∃ c₀ c₁ : ℂ → ℂ, ∃ C M : ℝ,
      0 ≤ C ∧ 0 ≤ M ∧ AnalyticAt ℂ c₀ w₀ ∧ AnalyticAt ℂ c₁ w₀ ∧
      (∀ u ∈ closedBall w₀ R, ‖c₀ u‖ ≤ M) ∧ (∀ u ∈ closedBall w₀ R, ‖c₁ u‖ ≤ M) ∧
      HasUniformJet2 (closedBall w₀ R) b F c₀ c₁ C := by
  obtain ⟨R, b, hR, hb, hbh, c₀, c₁, C, hC, h₀, h₁, hj⟩ := h
  obtain ⟨r₀, hr₀, hb₀⟩ := exists_closedBall_norm_le_of_continuousAt h₀.continuousAt
  obtain ⟨r₁, hr₁, hb₁⟩ := exists_closedBall_norm_le_of_continuousAt h₁.continuousAt
  refine ⟨min (min R R') (min r₀ r₁), min b b', ?_, ?_, ?_, ?_, ?_, c₀, c₁, C,
    max (‖c₀ w₀‖ + 1) (‖c₁ w₀‖ + 1), hC, ?_, h₀, h₁, ?_, ?_, ?_⟩
  · exact lt_min (lt_min hR hR') (lt_min hr₀ hr₁)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact lt_min hb hb'
  · exact min_le_right _ _
  · exact (min_le_left _ _).trans hbh
  · exact le_max_of_le_left (by positivity)
  · intro u hu
    exact (hb₀ u (closedBall_subset_closedBall ((min_le_right _ _).trans (min_le_left _ _)) hu)).trans
      (le_max_left _ _)
  · intro u hu
    exact (hb₁ u (closedBall_subset_closedBall ((min_le_right _ _).trans (min_le_right _ _)) hu)).trans
      (le_max_right _ _)
  · exact (hj.mono (closedBall_subset_closedBall ((min_le_left _ _).trans (min_le_left _ _)))).mono_radius
      (min_le_left _ _)

theorem AnalyticJet2At.add {w₀ : ℂ} {F G : ℂ → ℝ → ℂ} (hF : AnalyticJet2At w₀ F)
    (hG : AnalyticJet2At w₀ G) : AnalyticJet2At w₀ (fun u z => F u z + G u z) := by
  obtain ⟨R, b, hR, hb, hbh, c₀, c₁, C, hC, h₀, h₁, hj⟩ := hF
  obtain ⟨R', b', hR', hRR', hb', hbb', hbh', d₀, d₁, D, -, hD, -, k₀, k₁, -, -, hj'⟩ :=
    hG.exists_bounded hR hb
  exact ⟨R', b', hR', hb', hbh', _, _, C + D, by linarith, h₀.add k₀, h₁.add k₁,
    ((hj.mono (closedBall_subset_closedBall hRR')).mono_radius hbb').add hj'⟩

theorem AnalyticJet2At.sub {w₀ : ℂ} {F G : ℂ → ℝ → ℂ} (hF : AnalyticJet2At w₀ F)
    (hG : AnalyticJet2At w₀ G) : AnalyticJet2At w₀ (fun u z => F u z - G u z) := by
  obtain ⟨R, b, hR, hb, hbh, c₀, c₁, C, hC, h₀, h₁, hj⟩ := hF
  obtain ⟨R', b', hR', hRR', hb', hbb', hbh', d₀, d₁, D, -, hD, -, k₀, k₁, -, -, hj'⟩ :=
    hG.exists_bounded hR hb
  exact ⟨R', b', hR', hb', hbh', _, _, C + D, by linarith, h₀.sub k₀, h₁.sub k₁,
    ((hj.mono (closedBall_subset_closedBall hRR')).mono_radius hbb').sub hj'⟩

theorem AnalyticJet2At.mul {w₀ : ℂ} {F G : ℂ → ℝ → ℂ} (hF : AnalyticJet2At w₀ F)
    (hG : AnalyticJet2At w₀ G) : AnalyticJet2At w₀ (fun u z => F u z * G u z) := by
  have hF' := hF
  obtain ⟨R₀, b₀, hR₀, hb₀, -, -, -, -, -, -, -, -⟩ := hF'
  obtain ⟨R, b, hR, -, hb, -, hbh, c₀, c₁, C, M, hC, hM, h₀, h₁, hc₀, hc₁, hj⟩ :=
    hF.exists_bounded hR₀ hb₀
  obtain ⟨R', b', hR', hRR', hb', hbb', hbh', d₀, d₁, D, M', hD, hM', k₀, k₁, hd₀, hd₁, hj'⟩ :=
    hG.exists_bounded hR hb
  have hsub : closedBall w₀ R' ⊆ closedBall w₀ R := closedBall_subset_closedBall hRR'
  have hjr := (hj.mono hsub).mono_radius hbb'
  set N := max M M' with hN
  have hN0 : 0 ≤ N := le_max_of_le_left hM
  refine ⟨R', b', hR', hb', hbh', _, _, _, by positivity, h₀.mul k₀, (h₀.mul k₁).add (h₁.mul k₀),
    hjr.mul (by linarith) hj' hC hD hN0 ?_ ?_ ?_ ?_⟩
  · exact fun u hu => (hc₀ u (hsub hu)).trans (le_max_left _ _)
  · exact fun u hu => (hc₁ u (hsub hu)).trans (le_max_left _ _)
  · exact fun u hu => (hd₀ u hu).trans (le_max_right _ _)
  · exact fun u hu => (hd₁ u hu).trans (le_max_right _ _)

/-- A function of the frequency alone, analytic at `w₀`. -/
theorem AnalyticJet2At.const {w₀ : ℂ} {k : ℂ → ℂ} (hk : AnalyticAt ℂ k w₀) :
    AnalyticJet2At w₀ (fun u _ => k u) :=
  ⟨1, 1 / 2, one_pos, by norm_num, le_rfl, k, fun _ => 0, 0, le_rfl, hk, analyticAt_const,
    hasUniformJet2_const _ _ k⟩

theorem AnalyticJet2At.const_mul {w₀ : ℂ} {F : ℂ → ℝ → ℂ} (hF : AnalyticJet2At w₀ F) {k : ℂ → ℂ}
    (hk : AnalyticAt ℂ k w₀) : AnalyticJet2At w₀ (fun u z => k u * F u z) :=
  (AnalyticJet2At.const hk).mul hF

/-- A jet with constant coefficients on `Ioc 0 b`, for any positive `b`. -/
theorem AnalyticJet2At.of_constant_coefficients {w₀ : ℂ} {F : ℂ → ℝ → ℂ} {b C : ℝ} {a₀ a₁ : ℂ}
    (hb : 0 < b) (h : HasUniformJet2 univ b F (fun _ => a₀) (fun _ => a₁) C) :
    AnalyticJet2At w₀ F :=
  ⟨1, min b (1 / 2), one_pos, lt_min hb (by norm_num), min_le_right _ _, _, _, max C 0,
    le_max_right _ _, analyticAt_const, analyticAt_const,
    ((h.mono (subset_univ _)).mono_radius (min_le_left _ _)).mono_const (le_max_left _ _)⟩

theorem AnalyticJet2At.sqrt_one_sub (w₀ : ℂ) :
    AnalyticJet2At w₀ (fun _ z => (Real.sqrt (1 - z) : ℂ)) :=
  AnalyticJet2At.of_constant_coefficients (by norm_num) (hasUniformJet2_sqrt_one_sub univ)

theorem AnalyticJet2At.inv_sqrt_one_sub (w₀ : ℂ) :
    AnalyticJet2At w₀ (fun _ z => ((Real.sqrt (1 - z))⁻¹ : ℂ)) :=
  AnalyticJet2At.of_constant_coefficients (by norm_num) (hasUniformJet2_inv_sqrt_one_sub univ)

theorem AnalyticJet2At.pow {w₀ : ℂ} {F : ℂ → ℝ → ℂ} (hF : AnalyticJet2At w₀ F) (n : ℕ) :
    AnalyticJet2At w₀ (fun u z => F u z ^ n) := by
  induction n with
  | zero =>
    simpa using AnalyticJet2At.const (w₀ := w₀) (k := fun _ => (1:ℂ)) analyticAt_const
  | succ n ih =>
    have := ih.mul hF
    simpa [pow_succ] using this

/-- The parameter-dependent power `(1+√(1-z))^{α(u)}` with `α` analytic at `w₀`. -/
theorem AnalyticJet2At.cpow_one_add_sqrt {w₀ : ℂ} {α : ℂ → ℂ} (hα : AnalyticAt ℂ α w₀) :
    AnalyticJet2At w₀ (fun u z => ((1 + Real.sqrt (1 - z) : ℝ) : ℂ) ^ (α u)) := by
  obtain ⟨r, hr, hbnd⟩ := exists_closedBall_norm_le_of_continuousAt hα.continuousAt
  have hB : 0 ≤ ‖α w₀‖ + 1 := by positivity
  have hj := hasUniformJet2_cpow_one_add_sqrt (closedBall w₀ r) hB hbnd
  have h2 : AnalyticAt ℂ (fun u => (2:ℂ) ^ (α u)) w₀ := by
    have hent : AnalyticAt ℂ (fun v : ℂ => (2:ℂ) ^ v) (α w₀) :=
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr
        (differentiable_id.const_cpow (Or.inl two_ne_zero))) _ (mem_univ _)
    exact hent.comp hα
  refine AnalyticJet2At.of_jet hr (lt_min (by norm_num) (by positivity)) (min_le_left _ _)
    h2 ?_ hj
  exact (hα.neg.mul h2).div analyticAt_const (by norm_num)

/-- Pointwise-equal families have the same germs. -/
theorem AnalyticJet2At.congr {w₀ : ℂ} {F G : ℂ → ℝ → ℂ} (h : AnalyticJet2At w₀ F)
    (hFG : ∀ u z, G u z = F u z) : AnalyticJet2At w₀ G := by
  obtain ⟨R, b, hR, hb, hbh, c₀, c₁, C, hC, h₀, h₁, hj⟩ := h
  exact ⟨R, b, hR, hb, hbh, c₀, c₁, C, hC, h₀, h₁, hj.congr (fun u _ z _ => hFG u z)⟩

theorem AnalyticJet2At.neg {w₀ : ℂ} {F : ℂ → ℝ → ℂ} (h : AnalyticJet2At w₀ F) :
    AnalyticJet2At w₀ (fun u z => -F u z) :=
  (h.const_mul (k := fun _ => (-1:ℂ)) analyticAt_const).congr (fun u z => by ring)

theorem AnalyticJet2At.div_const {w₀ : ℂ} {F : ℂ → ℝ → ℂ} (h : AnalyticJet2At w₀ F) (c : ℂ) :
    AnalyticJet2At w₀ (fun u z => F u z / c) :=
  (h.const_mul (k := fun _ => c⁻¹) analyticAt_const).congr (fun u z => by ring)

/-- The frequency itself. -/
theorem AnalyticJet2At.id (w₀ : ℂ) : AnalyticJet2At w₀ (fun u _ => u) :=
  AnalyticJet2At.const analyticAt_id

/-- Polynomials with constant coefficients in a germ. -/
theorem AnalyticJet2At.polynomial_eval {w₀ : ℂ} {G : ℂ → ℝ → ℂ} (hG : AnalyticJet2At w₀ G)
    (p : Polynomial ℂ) : AnalyticJet2At w₀ (fun u z => p.eval (G u z)) := by
  induction p using Polynomial.induction_on with
  | C a =>
    simpa using AnalyticJet2At.const (w₀ := w₀) (k := fun _ => a) analyticAt_const
  | add p q hp hq =>
    simpa [Polynomial.eval_add] using hp.add hq
  | monomial n a h =>
    have := h.mul hG
    refine this.congr (fun u z => ?_)
    simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, pow_succ]
    ring

end
end GaloisForLFunctions.HTGeometry
