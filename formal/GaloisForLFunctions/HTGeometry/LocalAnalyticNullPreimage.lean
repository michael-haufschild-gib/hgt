/-
# The null-preimage law on an open domain

The global several-variable null-preimage law transfers to an arbitrary open domain through an
analytic chart: the logistic coordinate is an analytic bijection from the line onto a bounded
interval, so a product of them is an analytic bijection from the whole space onto any sup-metric
ball.  A nonconstant analytic function on the ball therefore pulls null sets back to null sets, and
a countable subcover of the domain by such balls finishes the argument.

Main results:
* `lineToUnit`, `ballChart` — the analytic chart onto a sup-metric ball.
* `analytic_preimage_volume_eq_zero_ball` — the law on one ball.
* `analytic_preimage_volume_eq_zero_isOpen` — **the law on an arbitrary open domain**.
-/
import GaloisForLFunctions.HTGeometry.MultivariateAnalyticNullPreimage
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Set MeasureTheory Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The logistic coordinate: an analytic bijection from the line onto `(0, 1)`. -/
def lineToUnit (t : ℝ) : ℝ := Real.exp t / (1 + Real.exp t)

theorem one_add_exp_pos (t : ℝ) : (0 : ℝ) < 1 + Real.exp t := by positivity

theorem analyticAt_lineToUnit (t : ℝ) : AnalyticAt ℝ lineToUnit t :=
  AnalyticAt.div analyticAt_rexp (analyticAt_const.add analyticAt_rexp) (one_add_exp_pos t).ne'

theorem lineToUnit_pos (t : ℝ) : 0 < lineToUnit t :=
  div_pos (Real.exp_pos t) (one_add_exp_pos t)

theorem lineToUnit_lt_one (t : ℝ) : lineToUnit t < 1 := by
  rw [lineToUnit, div_lt_one (one_add_exp_pos t)]
  linarith

theorem exists_lineToUnit_eq {u : ℝ} (h0 : 0 < u) (h1 : u < 1) : ∃ t : ℝ, lineToUnit t = u := by
  have h1u : (0 : ℝ) < 1 - u := by linarith
  refine ⟨Real.log (u / (1 - u)), ?_⟩
  rw [lineToUnit, Real.exp_log (div_pos h0 h1u)]
  field_simp
  ring

/-- The analytic chart from the whole space onto a sup-metric ball. -/
def ballChart {n : ℕ} (c : Fin n → ℝ) (r : ℝ) : (Fin n → ℝ) → (Fin n → ℝ) :=
  fun x i => c i - r + 2 * r * lineToUnit (x i)

theorem analyticAt_ballChart {n : ℕ} (c : Fin n → ℝ) (r : ℝ) (x : Fin n → ℝ) :
    AnalyticAt ℝ (ballChart c r) x := by
  refine AnalyticAt.pi fun i => ?_
  have hproj : AnalyticAt ℝ (fun y : Fin n → ℝ => y i) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).analyticAt x
  have hcomp : AnalyticAt ℝ (fun y : Fin n → ℝ => lineToUnit (y i)) x :=
    AnalyticAt.comp (g := lineToUnit) (f := fun y : Fin n → ℝ => y i) (x := x)
      (analyticAt_lineToUnit (x i)) hproj
  exact analyticAt_const.add (analyticAt_const.mul hcomp)

theorem ball_eq_pi_Ioo {n : ℕ} (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    Metric.ball c r = Set.pi Set.univ (fun i => Set.Ioo (c i - r) (c i + r)) := by
  rw [ball_pi c hr]
  exact Set.pi_congr rfl fun i _ => Real.ball_eq_Ioo (c i) r

theorem ballChart_mem_ball {n : ℕ} (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) (x : Fin n → ℝ) :
    ballChart c r x ∈ Metric.ball c r := by
  rw [ball_eq_pi_Ioo c hr]
  intro i _
  have h0 := lineToUnit_pos (x i)
  have h1 := lineToUnit_lt_one (x i)
  constructor
  · have : 0 < 2 * r * lineToUnit (x i) := by positivity
    simp only [ballChart]
    linarith
  · have : 2 * r * lineToUnit (x i) < 2 * r := by nlinarith
    simp only [ballChart]
    linarith

theorem exists_ballChart_eq {n : ℕ} (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) {y : Fin n → ℝ}
    (hy : y ∈ Metric.ball c r) : ∃ x : Fin n → ℝ, ballChart c r x = y := by
  rw [ball_eq_pi_Ioo c hr] at hy
  have hchoice : ∀ i : Fin n, ∃ t : ℝ, c i - r + 2 * r * lineToUnit t = y i := by
    intro i
    obtain ⟨hlo, hhi⟩ := hy i (Set.mem_univ i)
    have hu0 : 0 < (y i - (c i - r)) / (2 * r) := by
      apply div_pos <;> linarith
    have hu1 : (y i - (c i - r)) / (2 * r) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    obtain ⟨t, ht⟩ := exists_lineToUnit_eq hu0 hu1
    refine ⟨t, ?_⟩
    rw [ht]
    field_simp
    ring
  choose t ht using hchoice
  exact ⟨t, funext fun i => ht i⟩

/-- **The null-preimage law on one ball.** -/
theorem analytic_preimage_volume_eq_zero_ball {n : ℕ} {c : Fin n → ℝ} {r : ℝ} (hr : 0 < r)
    {U : Set (Fin n → ℝ)} (hsub : Metric.ball c r ⊆ U)
    {f : (Fin n → ℝ) → ℝ} (hf : AnalyticOnNhd ℝ f U)
    (hnc : ∃ p ∈ Metric.ball c r, ∃ q ∈ Metric.ball c r, f p ≠ f q)
    (E : Set ℝ) (hE : volume E = 0) :
    volume (Metric.ball c r ∩ f ⁻¹' E) = 0 := by
  have hgan : AnalyticOnNhd ℝ (fun x : Fin n → ℝ => f (ballChart c r x)) univ := by
    intro x _
    exact AnalyticAt.comp (g := f) (f := ballChart c r) (x := x)
      (hf _ (hsub (ballChart_mem_ball c hr x))) (analyticAt_ballChart c r x)
  have hgnc : ∃ a b : Fin n → ℝ,
      f (ballChart c r a) ≠ f (ballChart c r b) := by
    obtain ⟨p, hp, q, hq, hpq⟩ := hnc
    obtain ⟨a, ha⟩ := exists_ballChart_eq c hr hp
    obtain ⟨b, hb⟩ := exists_ballChart_eq c hr hq
    exact ⟨a, b, by rw [ha, hb]; exact hpq⟩
  have hgnull : volume ((fun x : Fin n → ℝ => f (ballChart c r x)) ⁻¹' E) = 0 :=
    analytic_preimage_volume_eq_zero_fin n _ hgan hgnc E hE
  have himg : Metric.ball c r ∩ f ⁻¹' E =
      ballChart c r '' ((fun x : Fin n → ℝ => f (ballChart c r x)) ⁻¹' E) := by
    ext y
    constructor
    · rintro ⟨hyball, hyE⟩
      obtain ⟨x, hx⟩ := exists_ballChart_eq c hr hyball
      exact ⟨x, by simpa [hx] using hyE, hx⟩
    · rintro ⟨x, hxE, rfl⟩
      exact ⟨ballChart_mem_ball c hr x, hxE⟩
  rw [himg]
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ hgnull
  intro x _
  exact ((analyticAt_ballChart c r x).differentiableAt).differentiableWithinAt

/-- **The null-preimage law on an arbitrary open domain.**  A real-analytic function which is
nonconstant on every nonempty open subset of an open set pulls every Lebesgue-null set back to a
Lebesgue-null subset of that open set. -/
theorem analytic_preimage_volume_eq_zero_isOpen {n : ℕ} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    {f : (Fin n → ℝ) → ℝ} (hf : AnalyticOnNhd ℝ f U)
    (hnc : ∀ V : Set (Fin n → ℝ), IsOpen V → V.Nonempty → V ⊆ U →
      ∃ p ∈ V, ∃ q ∈ V, f p ≠ f q)
    (E : Set ℝ) (hE : volume E = 0) :
    volume (U ∩ f ⁻¹' E) = 0 := by
  classical
  have hchoice : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ U := by
    intro x hx
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hU x hx
    exact ⟨r, hr, hrsub⟩
  choose rad hrad hradsub using hchoice
  have hcover : U ⊆ ⋃ x : U, Metric.ball (x : Fin n → ℝ) (rad x x.prop) := by
    intro x hx
    simp only [mem_iUnion]
    exact ⟨⟨x, hx⟩, Metric.mem_ball_self (hrad x hx)⟩
  have hLindelof : IsLindelof U := isLindelof_iff_lindelofSpace.mpr inferInstance
  obtain ⟨s, hscount, hscover⟩ :=
    hLindelof.elim_countable_subcover (fun x : U => Metric.ball (x : Fin n → ℝ) (rad x x.prop))
      (fun _ => Metric.isOpen_ball) hcover
  letI : Encodable s := hscount.toEncodable
  have hballnull : ∀ x : s,
      volume (Metric.ball ((x : U) : Fin n → ℝ) (rad (x : U) (x : U).prop) ∩ f ⁻¹' E) = 0 := by
    intro x
    refine analytic_preimage_volume_eq_zero_ball (hrad _ _) (hradsub _ _) hf ?_ E hE
    exact hnc _ Metric.isOpen_ball ⟨_, Metric.mem_ball_self (hrad _ _)⟩ (hradsub _ _)
  refine measure_mono_null ?_ (measure_iUnion_null hballnull)
  rintro y ⟨hyU, hyE⟩
  obtain ⟨i, hi, hyi⟩ := by simpa only [mem_iUnion, exists_prop] using hscover hyU
  simp only [mem_iUnion]
  exact ⟨⟨i, hi⟩, hyi, hyE⟩

end

end GaloisForLFunctions.HTGeometry
