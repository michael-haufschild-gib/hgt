import GaloisForLFunctions.RHTower.MertensClockDefectTraceClass
import GaloisForLFunctions.RHTower.ProlateFourierSignSectors
import GaloisForLFunctions.RHTower.ArithmeticDilationStageDeterminant
import GaloisForLFunctions.HTGeometry.LidskiiSelfAdjoint
import GaloisForLFunctions.HTGeometry.BurnolDepthCompletion

/-!
# Signed spectrum of the Mertens-clock defect

The defect `E = A - W` of the prime Poisson Gram against its Wiener–Hopf bulk is compact,
self-adjoint and trace class with `Tr E = 0`.  Here:

* the Wiener–Hopf operator `W` is strictly positive: `⟪f, W f⟫ = ∫_0^∞ u |L f(u)|² du` with the
  Laplace-type transform `L f(u) = ∫ 2 e^y e^{-u e^y} f(y) dy`, which is continuous in `u > 0`, and
  its integer samples are the moments of `2 e^y e^{-e^y} f(y)` in the bounded coordinate `e^{-e^y}`;
* on the infinite-dimensional space of mean-zero functions in a prime cell, `A f = 0`, so
  `⟪f, E f⟫ = -⟪f, W f⟫ < 0`: `E` has infinitely many negative eigenvalues, counted with
  multiplicity;
* by Lidskii's theorem `Tr E = ∑ λₙ(E) = 0`, so `E` also has a positive eigenvalue; in particular
  `E ≠ 0`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section
set_option autoImplicit false

local notation "L²₊" => Lp ℂ 2 halfLineMeasure

/-! ### Integrability of the Gram representation -/

section Gram

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

/-- The Laplace-type transform `u ↦ ∫ 2 e^{ψ(y)} e^{-u e^{ψ(y)}} f(y) dμ(y)` is square integrable
against `u du` on `(0, ∞)`. -/
theorem integrableOn_sechLaplace_gram (k : SchurKernel μ) {ψ : α → ℝ}
    (hψ : Measurable ψ) (hk : ∀ y z, k.toFun y z = (sechSqHalf (ψ y - ψ z) : ℂ))
    (f : Lp ℂ 2 μ) :
    IntegrableOn (fun u : ℝ =>
      u * ‖∫ y, (sechLaplaceFeature (ψ y) u : ℂ) * (f : α → ℂ) y ∂μ‖ ^ 2) (Ioi 0) := by
  set ν : Measure ℝ := volume.restrict (Ioi 0)
  have hf : Measurable (f : α → ℂ) := (Lp.stronglyMeasurable f).measurable
  set G : α → ℝ → ℝ := fun y u => sechLaplaceFeature (ψ y) u with hGdef
  have hGm : Measurable fun p : α × ℝ => G p.1 p.2 :=
    continuous_sechLaplaceFeature.measurable.comp ((hψ.comp measurable_fst).prodMk measurable_snd)
  set F : (α × α) × ℝ → ℂ := fun q => (starRingEnd ℂ) ((f : α → ℂ) q.1.1) * (f : α → ℂ) q.1.2 *
    ((q.2 * (G q.1.1 q.2 * G q.1.2 q.2) : ℝ) : ℂ) with hFdef
  have hFm : Measurable F := by
    refine ((Complex.continuous_conj.measurable.comp (hf.comp (measurable_fst.comp
      measurable_fst))).mul (hf.comp (measurable_snd.comp measurable_fst))).mul ?_
    refine Complex.measurable_ofReal.comp (measurable_snd.mul ?_)
    exact (hGm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (hGm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hnorm : ∀ p : α × α, ∫ u, ‖F (p, u)‖ ∂ν =
      ‖(starRingEnd ℂ) ((f : α → ℂ) p.1) * k.toFun p.1 p.2 * (f : α → ℂ) p.2‖ := by
    intro p
    have h1 : ∀ u ∈ Ioi (0 : ℝ), ‖F (p, u)‖ = ‖(f : α → ℂ) p.1‖ * ‖(f : α → ℂ) p.2‖ *
        (u * (G p.1 u * G p.2 u)) := by
      intro u hu
      have hG0 : 0 ≤ u * (G p.1 u * G p.2 u) := by
        have hu' : (0 : ℝ) < u := hu
        simp only [hGdef, sechLaplaceFeature]; positivity
      simp only [hFdef, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs]
      rw [← abs_mul, ← abs_mul, abs_of_nonneg hG0]
    rw [setIntegral_congr_fun measurableSet_Ioi h1, integral_const_mul, hGdef,
      integral_sechLaplace, hk, norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (sechSqHalf_pos _)]
    ring
  have hFint : Integrable F ((μ.prod μ).prod ν) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun p => ?_, ?_⟩
    · simp only [hFdef]
      refine Integrable.const_mul ?_ _
      exact (integrableOn_sechLaplace (ψ p.1) (ψ p.2)).ofReal
    · simp_rw [hnorm]
      exact (k.integrable_triple f f).norm
  have hval : ∀ u, ∫ p, F (p, u) ∂(μ.prod μ) =
      ((u * ‖∫ y, (G y u : ℂ) * (f : α → ℂ) y ∂μ‖ ^ 2 : ℝ) : ℂ) := by
    intro u
    simp only [hFdef]
    have hsplit : (fun p : α × α => (starRingEnd ℂ) ((f : α → ℂ) p.1) * (f : α → ℂ) p.2 *
        ((u * (G p.1 u * G p.2 u) : ℝ) : ℂ)) = fun p => (u : ℂ) *
          ((starRingEnd ℂ) ((G p.1 u : ℂ) * (f : α → ℂ) p.1) *
            ((G p.2 u : ℂ) * (f : α → ℂ) p.2)) := by
      funext p
      simp only [map_mul, Complex.conj_ofReal]
      push_cast
      ring
    rw [hsplit, integral_const_mul]
    rw [integral_prod_mul (fun y => (starRingEnd ℂ) ((G y u : ℂ) * (f : α → ℂ) y))
      (fun z => (G z u : ℂ) * (f : α → ℂ) z), integral_conj, RCLike.conj_mul]
    push_cast
    rfl
  have h := hFint.integral_prod_right
  have h2 : Integrable (fun u : ℝ => ((u * ‖∫ y, (G y u : ℂ) * (f : α → ℂ) y ∂μ‖ ^ 2 : ℝ) : ℂ))
      ν := h.congr (Eventually.of_forall hval)
  have h3 := h2.re
  refine h3.congr (Eventually.of_forall fun u => ?_)
  exact Complex.ofReal_re _

end Gram

/-! ### Strict positivity of the Wiener–Hopf operator -/

/-- The transform `L f(u) = ∫_0^∞ 2 e^y e^{-u e^y} f(y) dy`. -/
def sechLaplaceTransform (f : L²₊) (u : ℝ) : ℂ :=
  ∫ y, (sechLaplaceFeature y u : ℂ) * (f : ℝ → ℂ) y ∂halfLineMeasure

theorem inner_wienerHopfSechOp_eq (f : L²₊) :
    inner ℂ f (wienerHopfSechOp f) =
      ((∫ u in Ioi (0 : ℝ), u * ‖sechLaplaceTransform f u‖ ^ 2 : ℝ) : ℂ) :=
  wienerHopfSechKernel.inner_op_eq_of_sechSqHalf (ψ := id) measurable_id (fun _ _ => rfl) f

theorem integrableOn_sechLaplaceTransform_gram (f : L²₊) :
    IntegrableOn (fun u : ℝ => u * ‖sechLaplaceTransform f u‖ ^ 2) (Ioi 0) :=
  integrableOn_sechLaplace_gram wienerHopfSechKernel (ψ := id) measurable_id (fun _ _ => rfl) f

/-- `e^y e^{-c e^y} ≤ 2 e^{-y} / c²` for `c > 0`. -/
theorem exp_mul_exp_neg_mul_exp_le {c : ℝ} (hc : 0 < c) (y : ℝ) :
    Real.exp y * Real.exp (-(c * Real.exp y)) ≤ 2 / c ^ 2 * Real.exp (-y) := by
  have hx : 0 ≤ c * Real.exp y := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hx
  have hpos : 0 < Real.exp (c * Real.exp y) := Real.exp_pos _
  have hey := Real.exp_pos y
  have h1 : Real.exp (-(c * Real.exp y)) ≤ 2 / (c * Real.exp y) ^ 2 := by
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ hpos]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (c * Real.exp y)]
  have h2 : Real.exp (-y) = (Real.exp y)⁻¹ := Real.exp_neg y
  calc Real.exp y * Real.exp (-(c * Real.exp y)) ≤ Real.exp y * (2 / (c * Real.exp y) ^ 2) :=
        mul_le_mul_of_nonneg_left h1 hey.le
    _ = 2 / c ^ 2 * Real.exp (-y) := by rw [h2]; field_simp

/-- The Laplace weight `2 e^y e^{-c e^y}` is square integrable on the half-line. -/
theorem memLp_sechLaplaceWeight {c : ℝ} (hc : 0 < c) :
    MemLp (fun y : ℝ => ((2 * Real.exp y * Real.exp (-(c * Real.exp y)) : ℝ) : ℂ)) 2
      halfLineMeasure := by
  have hcont : Continuous (fun y : ℝ => ((2 * Real.exp y * Real.exp (-(c * Real.exp y)) : ℝ) : ℂ)) :=
    by fun_prop
  refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr ?_
  have hdom : Integrable (fun y : ℝ => (4 / c ^ 2) ^ 2 * Real.exp (-(2 * y))) halfLineMeasure := by
    refine Integrable.const_mul ?_ _
    have h : IntegrableOn (fun x : ℝ => Real.exp (-(2 * x))) (Ici 0) := by
      have h0 := (integrableOn_Ici_iff_integrableOn_Ioi (by simp)).mpr
        (exp_neg_integrableOn_Ioi 0 (two_pos : (0 : ℝ) < 2))
      simpa [neg_mul] using h0
    exact h
  refine hdom.mono' (hcont.norm.pow 2).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ici]
  refine Eventually.of_forall fun y _ => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  have h := exp_mul_exp_neg_mul_exp_le hc y
  have hb : 2 * Real.exp y * Real.exp (-(c * Real.exp y)) ≤ 4 / c ^ 2 * Real.exp (-y) :=
    calc 2 * Real.exp y * Real.exp (-(c * Real.exp y))
        = 2 * (Real.exp y * Real.exp (-(c * Real.exp y))) := by ring
      _ ≤ 2 * (2 / c ^ 2 * Real.exp (-y)) := by gcongr
      _ = 4 / c ^ 2 * Real.exp (-y) := by ring
  have hb0 : 0 ≤ 2 * Real.exp y * Real.exp (-(c * Real.exp y)) := by positivity
  calc (2 * Real.exp y * Real.exp (-(c * Real.exp y))) ^ 2 ≤ (4 / c ^ 2 * Real.exp (-y)) ^ 2 :=
        pow_le_pow_left₀ hb0 hb 2
    _ = (4 / c ^ 2) ^ 2 * Real.exp (-(2 * y)) := by
        rw [mul_pow, sq (Real.exp (-y)), ← Real.exp_add]; ring_nf

theorem integrable_sechLaplaceWeight_mul {c : ℝ} (hc : 0 < c) (f : L²₊) :
    Integrable (fun y : ℝ => ((2 * Real.exp y * Real.exp (-(c * Real.exp y)) : ℝ) : ℂ) *
      (f : ℝ → ℂ) y) halfLineMeasure :=
  (memLp_sechLaplaceWeight hc).integrable_mul (Lp.memLp f)

theorem sechLaplaceFeature_eq (a u : ℝ) :
    sechLaplaceFeature a u = 2 * Real.exp a * Real.exp (-(u * Real.exp a)) := rfl

/-- `L f` is continuous on `(0, ∞)`. -/
theorem continuousOn_sechLaplaceTransform (f : L²₊) :
    ContinuousOn (sechLaplaceTransform f) (Ioi 0) := by
  intro u₀ hu₀
  have hu0 : (0 : ℝ) < u₀ := hu₀
  refine ContinuousAt.continuousWithinAt ?_
  have hbound := integrable_sechLaplaceWeight_mul (half_pos hu0) f
  refine continuousAt_of_dominated (bound := fun y =>
    ‖((2 * Real.exp y * Real.exp (-(u₀ / 2 * Real.exp y)) : ℝ) : ℂ) * (f : ℝ → ℂ) y‖) ?_ ?_
    hbound.norm ?_
  · refine Eventually.of_forall fun u => ?_
    exact ((by unfold sechLaplaceFeature; fun_prop :
      Continuous fun y : ℝ => (sechLaplaceFeature y u : ℂ)).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable f)
  · filter_upwards [Ioi_mem_nhds (half_lt_self hu0)] with u hu
    refine Eventually.of_forall fun y => ?_
    have hu' : u₀ / 2 < u := hu
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, sechLaplaceFeature_eq]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    have hey := Real.exp_pos y
    have : Real.exp (-(u * Real.exp y)) ≤ Real.exp (-(u₀ / 2 * Real.exp y)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    nlinarith [Real.exp_pos (-(u * Real.exp y))]
  · exact Eventually.of_forall fun y => by
      unfold sechLaplaceFeature
      fun_prop

/-- Integer samples of `L f` are the moments of `2 e^y e^{-e^y} f(y)` in the coordinate
`e^{-e^y}`; if they all vanish, `f = 0`. -/
theorem eq_zero_of_sechLaplaceTransform_nat (f : L²₊)
    (h : ∀ n : ℕ, sechLaplaceTransform f ((n : ℝ) + 1) = 0) : f = 0 := by
  set φ : ℝ → ℝ := fun y => Real.exp (-Real.exp y) with hφdef
  set F : ℝ → ℂ := fun y => ((2 * Real.exp y * Real.exp (-(1 * Real.exp y)) : ℝ) : ℂ) *
    (f : ℝ → ℂ) y with hFdef
  have hφ : MeasurableEmbedding φ := by
    refine (show Continuous φ by fun_prop).measurableEmbedding ?_
    intro x y hxy
    have h1 := Real.exp_injective hxy
    have h2 : Real.exp x = Real.exp y := by linarith
    exact Real.exp_injective h2
  have hbound : ∀ᵐ y ∂halfLineMeasure, |φ y| ≤ 1 := Eventually.of_forall fun y => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith [Real.exp_pos y])
  have hF : Integrable F halfLineMeasure := integrable_sechLaplaceWeight_mul one_pos f
  have hmom : ∀ n : ℕ, ∫ y, (φ y : ℂ) ^ n * F y ∂halfLineMeasure = 0 := by
    intro n
    rw [← h n, sechLaplaceTransform]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have hr : Real.exp (-Real.exp y) ^ n * (2 * Real.exp y * Real.exp (-(1 * Real.exp y))) =
        sechLaplaceFeature y ((n : ℝ) + 1) := by
      rw [sechLaplaceFeature_eq, ← Real.exp_nat_mul]
      have e : Real.exp ((n : ℝ) * -Real.exp y) * Real.exp (-(1 * Real.exp y)) =
          Real.exp (-(((n : ℝ) + 1) * Real.exp y)) := by
        rw [← Real.exp_add]; congr 1; ring
      calc Real.exp ((n : ℝ) * -Real.exp y) * (2 * Real.exp y * Real.exp (-(1 * Real.exp y)))
          = 2 * Real.exp y * (Real.exp ((n : ℝ) * -Real.exp y) *
              Real.exp (-(1 * Real.exp y))) := by ring
        _ = _ := by rw [e]
    simp only [hFdef, hφdef]
    rw [← mul_assoc, ← Complex.ofReal_pow, ← Complex.ofReal_mul, hr]
  have hF0 := _root_.HTGeometry.ae_eq_zero_of_boundedCoordinate_complex_moments hφ hbound hF hmom
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hF0] with y hy
  simp only [hFdef, Pi.zero_apply, mul_eq_zero, Complex.ofReal_eq_zero] at hy ⊢
  rcases hy with h1 | h1
  · exfalso
    rcases h1 with (h2 | h2) | h2
    · norm_num at h2
    · exact (Real.exp_pos y).ne' h2
    · exact (Real.exp_pos _).ne' h2
  · exact h1

/-- **The Wiener–Hopf operator is strictly positive**: `⟪f, W f⟫ > 0` for `f ≠ 0`. -/
theorem re_inner_wienerHopfSechOp_pos {f : L²₊} (hf : f ≠ 0) :
    0 < (inner ℂ f (wienerHopfSechOp f)).re := by
  rw [inner_wienerHopfSechOp_eq, Complex.ofReal_re]
  have hint := integrableOn_sechLaplaceTransform_gram f
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun u : ℝ => u * ‖sechLaplaceTransform f u‖ ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have : (0 : ℝ) < u := hu
    exact mul_nonneg this.le (sq_nonneg _)
  have hge : 0 ≤ ∫ u in Ioi (0 : ℝ), u * ‖sechLaplaceTransform f u‖ ^ 2 :=
    integral_nonneg_of_ae hnn
  rcases hge.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    apply hf
    have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp heq.symm
    have hL : sechLaplaceTransform f =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
      filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with u hu hu0
      have hu0' : (0 : ℝ) < u := hu0
      simp only [Pi.zero_apply, mul_eq_zero, hu0'.ne', false_or, pow_eq_zero_iff two_ne_zero,
        norm_eq_zero] at hu ⊢
      exact hu
    have heqOn : EqOn (sechLaplaceTransform f) 0 (Ioi 0) :=
      Measure.eqOn_open_of_ae_eq hL isOpen_Ioi (continuousOn_sechLaplaceTransform f)
        continuousOn_const
    exact eq_zero_of_sechLaplaceTransform_nat f fun n =>
      heqOn (show (0 : ℝ) < (n : ℝ) + 1 by positivity)

/-! ### Mean-zero steps inside a prime cell -/

theorem halfLineMeasure_Ico_ne_top (a b : ℝ) : halfLineMeasure (Ico a b) ≠ ∞ :=
  ((Measure.restrict_apply_le _ _).trans_lt measure_Ico_lt_top).ne

theorem halfLineMeasure_real_Ico {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    halfLineMeasure.real (Ico a b) = b - a := by
  rw [measureReal_def, halfLineMeasure, Measure.restrict_apply measurableSet_Ico,
    Set.inter_eq_left.mpr (show Ico a b ⊆ Ici (0 : ℝ) from fun x hx => ha.trans hx.1),
    Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]

/-- Dyadic points `t_n = y_p + 2^{-n}/p` of the cell of `p`. -/
def cellDyadic (p n : ℕ) : ℝ := primeCellStart p + 1 / (p : ℝ) / 2 ^ n

/-- The midpoint of `[t_{n+1}, t_n)`. -/
def cellDyadicMid (p n : ℕ) : ℝ := (cellDyadic p (n + 1) + cellDyadic p n) / 2

theorem cellDyadic_succ_lt {p : ℕ} (hp : 0 < p) (n : ℕ) : cellDyadic p (n + 1) < cellDyadic p n := by
  unfold cellDyadic
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  rw [pow_succ, ← div_div]
  have h2 : (0 : ℝ) < 1 / (p : ℝ) / 2 ^ n := by positivity
  linarith [half_lt_self h2]

theorem cellDyadic_anti {p : ℕ} (hp : 0 < p) {m n : ℕ} (h : m ≤ n) :
    cellDyadic p n ≤ cellDyadic p m := by
  unfold cellDyadic
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  gcongr
  · norm_num

theorem cellDyadic_le_end {p : ℕ} (hp : 0 < p) (n : ℕ) :
    cellDyadic p n ≤ primeCellStart p + 1 / (p : ℝ) := by
  have h := cellDyadic_anti hp (Nat.zero_le n)
  simpa [cellDyadic] using h

theorem start_lt_cellDyadic {p : ℕ} (hp : 0 < p) (n : ℕ) : primeCellStart p < cellDyadic p n := by
  unfold cellDyadic
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have : (0 : ℝ) < 1 / (p : ℝ) / 2 ^ n := by positivity
  linarith

/-- The mean-zero step `1_{[t_{n+1}, m_n)} - 1_{[m_n, t_n)}` in the cell of `p`. -/
def cellHaar (p n : ℕ) : L²₊ :=
  indicatorConstLp 2 measurableSet_Ico (halfLineMeasure_Ico_ne_top (cellDyadic p (n + 1))
    (cellDyadicMid p n)) (1 : ℂ) -
  indicatorConstLp 2 measurableSet_Ico (halfLineMeasure_Ico_ne_top (cellDyadicMid p n)
    (cellDyadic p n)) (1 : ℂ)

theorem inner_indicator_Ico (a b c d : ℝ) :
    inner ℂ (indicatorConstLp 2 measurableSet_Ico (halfLineMeasure_Ico_ne_top a b) (1 : ℂ) : L²₊)
      (indicatorConstLp 2 measurableSet_Ico (halfLineMeasure_Ico_ne_top c d) (1 : ℂ)) =
      (halfLineMeasure.real (Ico a b ∩ Ico c d) : ℂ) :=
  L2.inner_indicatorConstLp_one_indicatorConstLp_one _ _ _ _

theorem Ico_inter_Ico_eq_empty_of_le {a b c d : ℝ} (h : b ≤ c) : Ico a b ∩ Ico c d = ∅ := by
  ext x; simp only [mem_inter_iff, mem_Ico, mem_empty_iff_false, iff_false, not_and]
  intro _ hxb hcx; linarith

/-- The steps of different dyadic levels have disjoint supports. -/
theorem inner_cellHaar_of_ne {p : ℕ} (hp : 0 < p) {i j : ℕ} (hij : i ≠ j) :
    inner ℂ (cellHaar p i) (cellHaar p j) = 0 := by
  wlog hlt : i < j generalizing i j
  · have h := this hij.symm (lt_of_le_of_ne (not_lt.mp hlt) hij.symm)
    rw [← inner_conj_symm, h, map_zero]
  have hle : cellDyadic p j ≤ cellDyadic p (i + 1) := cellDyadic_anti hp hlt
  have hmj : cellDyadicMid p j < cellDyadic p j := by
    unfold cellDyadicMid; linarith [cellDyadic_succ_lt hp j]
  have hmi : cellDyadic p (i + 1) < cellDyadicMid p i := by
    unfold cellDyadicMid; linarith [cellDyadic_succ_lt hp i]
  simp only [cellHaar, inner_sub_left, inner_sub_right, inner_indicator_Ico]
  rw [Set.inter_comm (Ico (cellDyadic p (i + 1)) (cellDyadicMid p i)),
    Set.inter_comm (Ico (cellDyadic p (i + 1)) (cellDyadicMid p i)),
    Set.inter_comm (Ico (cellDyadicMid p i) (cellDyadic p i)),
    Set.inter_comm (Ico (cellDyadicMid p i) (cellDyadic p i)),
    Ico_inter_Ico_eq_empty_of_le (by linarith), Ico_inter_Ico_eq_empty_of_le (by linarith),
    Ico_inter_Ico_eq_empty_of_le (by linarith), Ico_inter_Ico_eq_empty_of_le (by linarith)]
  simp

theorem cellHaar_ne_zero {p : ℕ} (hp : 0 < p) (n : ℕ) : cellHaar p n ≠ 0 := by
  intro h
  have h0 : inner ℂ (cellHaar p n) (cellHaar p n) = 0 := by rw [h, inner_zero_left]
  have hlo := cellDyadic_succ_lt hp n
  have hm1 : cellDyadic p (n + 1) < cellDyadicMid p n := by unfold cellDyadicMid; linarith
  have hm2 : cellDyadicMid p n < cellDyadic p n := by unfold cellDyadicMid; linarith
  have h0' : 0 ≤ cellDyadic p (n + 1) := (primeCellStart_nonneg p).trans
    (start_lt_cellDyadic hp (n + 1)).le
  simp only [cellHaar, inner_sub_left, inner_sub_right, inner_indicator_Ico, Set.inter_self] at h0
  have e1 : Ico (cellDyadicMid p n) (cellDyadic p n) ∩
      Ico (cellDyadic p (n + 1)) (cellDyadicMid p n) = ∅ := by
    rw [Set.inter_comm]; exact Ico_inter_Ico_eq_empty_of_le le_rfl
  have e2 : Ico (cellDyadic p (n + 1)) (cellDyadicMid p n) ∩
      Ico (cellDyadicMid p n) (cellDyadic p n) = ∅ := Ico_inter_Ico_eq_empty_of_le le_rfl
  rw [halfLineMeasure_real_Ico h0' hm1.le, halfLineMeasure_real_Ico (by linarith) hm2.le, e1, e2,
    measureReal_empty] at h0
  have h1 := congrArg Complex.re h0
  simp at h1
  linarith

/-- Each step has zero integral against every prime cell. -/
theorem inner_primeCellVec_cellHaar (p : Nat.Primes) (q : Nat.Primes) (n : ℕ) :
    inner ℂ (primeCellVec q) (cellHaar p n) = 0 := by
  have hp : 0 < (p : ℕ) := p.prop.pos
  rw [inner_primeCellVec_eq, cellHaar]
  have hint : ∫ z in primeCell q, ((indicatorConstLp 2 measurableSet_Ico
      (halfLineMeasure_Ico_ne_top (cellDyadic p (n + 1)) (cellDyadicMid p n)) (1 : ℂ) -
      indicatorConstLp 2 measurableSet_Ico (halfLineMeasure_Ico_ne_top (cellDyadicMid p n)
        (cellDyadic p n)) (1 : ℂ) : L²₊) : ℝ → ℂ) z ∂halfLineMeasure =
      (halfLineMeasure.real (Ico (cellDyadic p (n + 1)) (cellDyadicMid p n) ∩ primeCell q) -
        halfLineMeasure.real (Ico (cellDyadicMid p n) (cellDyadic p n) ∩ primeCell q) : ℝ) := by
    rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_sub _ _))]
    simp only [Pi.sub_apply]
    rw [integral_sub (integrable_indicatorConstLp _ _ _).integrableOn
      (integrable_indicatorConstLp _ _ _).integrableOn,
      setIntegral_indicatorConstLp (measurableSet_primeCell q),
      setIntegral_indicatorConstLp (measurableSet_primeCell q)]
    simp
  rw [hint]
  have hlo := cellDyadic_succ_lt hp n
  have hm1 : cellDyadic p (n + 1) < cellDyadicMid p n := by unfold cellDyadicMid; linarith
  have hm2 : cellDyadicMid p n < cellDyadic p n := by unfold cellDyadicMid; linarith
  have hs := start_lt_cellDyadic hp (n + 1)
  have he := cellDyadic_le_end hp n
  have hL : Ico (cellDyadic p (n + 1)) (cellDyadicMid p n) ⊆ primeCell p := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hR : Ico (cellDyadicMid p n) (cellDyadic p n) ⊆ primeCell p := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  by_cases hpq : (q : ℕ) = p
  · rw [hpq, Set.inter_eq_left.mpr hL, Set.inter_eq_left.mpr hR,
      halfLineMeasure_real_Ico ((primeCellStart_nonneg _).trans hs.le) hm1.le,
      halfLineMeasure_real_Ico (by linarith [primeCellStart_nonneg (p : ℕ)]) hm2.le]
    unfold cellDyadicMid
    push_cast
    ring
  · have hdisj := disjoint_primeCell p.prop q.prop (Ne.symm hpq)
    have hL0 : Ico (cellDyadic p (n + 1)) (cellDyadicMid p n) ∩ primeCell q = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp (hdisj.mono_left hL)
    have hR0 : Ico (cellDyadicMid p n) (cellDyadic p n) ∩ primeCell q = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp (hdisj.mono_left hR)
    rw [hL0, hR0, measureReal_empty]
    simp

/-- The steps are linearly independent: nonzero and pairwise orthogonal. -/
theorem linearIndependent_cellHaar {p : ℕ} (hp : 0 < p) (m : ℕ) :
    LinearIndependent ℂ (fun i : Fin m => cellHaar p i) :=
  linearIndependent_of_ne_zero_of_inner_eq_zero (fun i => cellHaar_ne_zero hp i)
    fun _ _ hij => inner_cellHaar_of_ne hp (fun h => hij (Fin.ext h))

/-- The span of the first `m` cell steps. -/
def cellHaarSpan (p : ℕ) (m : ℕ) : Submodule ℂ L²₊ :=
  Submodule.span ℂ (Set.range fun i : Fin m => cellHaar p i)

theorem finrank_cellHaarSpan {p : ℕ} (hp : 0 < p) (m : ℕ) :
    Module.finrank ℂ (cellHaarSpan p m) = m := by
  rw [cellHaarSpan, finrank_span_eq_card (linearIndependent_cellHaar hp m), Fintype.card_fin]

/-- The vectors orthogonal to every prime cell. -/
def cellOrthogonal : Submodule ℂ L²₊ :=
  ⨅ q : Nat.Primes, LinearMap.ker (innerSL ℂ (primeCellVec q)).toLinearMap

theorem mem_cellOrthogonal {f : L²₊} :
    f ∈ cellOrthogonal ↔ ∀ q : Nat.Primes, inner ℂ (primeCellVec q) f = 0 := by
  simp [cellOrthogonal, Submodule.mem_iInf, LinearMap.mem_ker]

theorem cellHaarSpan_le_cellOrthogonal (p : Nat.Primes) (m : ℕ) :
    cellHaarSpan p m ≤ cellOrthogonal := by
  rw [cellHaarSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact mem_cellOrthogonal.mpr fun q => inner_primeCellVec_cellHaar p q i

/-- The step operator `A` kills every vector orthogonal to the prime cells. -/
theorem mertensStepSechOp_eq_zero_of_mem {f : L²₊} (hf : f ∈ cellOrthogonal) :
    mertensStepSechOp f = 0 :=
  clockKernel_op_eq_zero _ _ _ _ _ (mem_cellOrthogonal.mp hf)

/-! ### The signed spectrum of `E = A - W` -/

/-- The Mertens-clock defect `E = A - W`. -/
def mertensClockDefectOp : L²₊ →L[ℂ] L²₊ := mertensStepSechOp - wienerHopfSechOp

theorem isSelfAdjoint_mertensClockDefectOp : IsSelfAdjoint mertensClockDefectOp :=
  isSelfAdjoint_mertensStepSechOp.sub isSelfAdjoint_wienerHopfSechOp

theorem isSymmetric_mertensClockDefectOp : mertensClockDefectOp.IsSymmetric :=
  isSelfAdjoint_mertensClockDefectOp.isSymmetric

theorem memSchattenClass_one_mertensClockDefectOp : MemSchattenClass 1 mertensClockDefectOp :=
  memSchattenClass_one_mertensStepSechOp_sub

theorem isCompactOperator_mertensClockDefectOp : IsCompactOperator mertensClockDefectOp :=
  memSchattenClass_one_mertensClockDefectOp.isCompactOperator one_pos

/-- `⟪E f, f⟫ = -⟪W f, f⟫ < 0` on nonzero vectors orthogonal to every prime cell. -/
theorem re_inner_mertensClockDefectOp_neg {f : L²₊} (hf : f ∈ cellOrthogonal) (hf0 : f ≠ 0) :
    RCLike.re (inner ℂ (mertensClockDefectOp f) f) < 0 := by
  rw [mertensClockDefectOp, _root_.sub_apply, mertensStepSechOp_eq_zero_of_mem hf,
    zero_sub, inner_neg_left, map_neg, inner_re_symm, neg_lt_zero]
  exact re_inner_wienerHopfSechOp_pos hf0

/-- **Infinitely many negative eigenvalues.**  For every `m`, `E` has `m` orthonormal eigenvectors
with negative eigenvalues. -/
theorem exists_orthonormal_negative_eigenfamily_mertensClockDefectOp (m : ℕ) :
    ∃ e : Fin m → L²₊, Orthonormal ℂ e ∧
      ∀ i, ∃ c : ℝ, c < 0 ∧ mertensClockDefectOp (e i) = (c : ℂ) • e i :=
  ContinuousLinearMap.exists_orthonormal_negative_eigenfamily_of_finrank_le
    isCompactOperator_mertensClockDefectOp isSymmetric_mertensClockDefectOp (cellHaarSpan 2 m)
    (by rw [finrank_cellHaarSpan two_pos])
    fun x hx hx0 => re_inner_mertensClockDefectOp_neg
      (cellHaarSpan_le_cellOrthogonal ⟨2, Nat.prime_two⟩ m hx) hx0

/-- The negative signed eigenvalues of `E`, counted with multiplicity, form an infinite set of
indices. -/
theorem infinite_setOf_sgVal_neg_mertensClockDefectOp :
    Set.Infinite {n : ℕ | ContinuousLinearMap.sgVal mertensClockDefectOp n < 0} := by
  intro hfin
  obtain ⟨r, hr, hneg⟩ := ContinuousLinearMap.exists_injective_negative_sgVal_indices_of_finrank_le
    isCompactOperator_mertensClockDefectOp isSymmetric_mertensClockDefectOp
    (cellHaarSpan 2 (hfin.toFinset.card + 1))
    (by rw [finrank_cellHaarSpan two_pos])
    fun x hx hx0 => re_inner_mertensClockDefectOp_neg
      (cellHaarSpan_le_cellOrthogonal ⟨2, Nat.prime_two⟩ _ hx) hx0
  have hsub : ∀ i, r i ∈ hfin.toFinset := fun i => by
    rw [Set.Finite.mem_toFinset]; exact hneg i
  have hcard := Finset.card_le_card_of_injOn (s := Finset.univ) r (fun i _ => hsub i)
    (fun i _ j _ h => hr h)
  simp at hcard

/-- **Trace neutrality forces a positive eigenvalue**: `∑ λₙ(E) = Tr E = 0`, and some `λₙ < 0`. -/
theorem exists_sgVal_pos_mertensClockDefectOp :
    ∃ n, 0 < ContinuousLinearMap.sgVal mertensClockDefectOp n := by
  by_contra hall
  push Not at hall
  obtain ⟨n₀, hn₀⟩ := infinite_setOf_sgVal_neg_mertensClockDefectOp.nonempty
  have hsum : Summable fun n => ContinuousLinearMap.sgVal mertensClockDefectOp n :=
    (summable_abs_sgVal memSchattenClass_one_mertensClockDefectOp
      isSymmetric_mertensClockDefectOp).of_abs
  obtain ⟨A, B, hA, hB, hE⟩ := isTraceClass_mertensStepSechOp_sub
  have htr := ContinuousLinearMap.opTrace_eq_tsum_sgVal isCompactOperator_mertensClockDefectOp
    isSymmetric_mertensClockDefectOp hA hB hE
  rw [show mertensClockDefectOp = mertensStepSechOp - wienerHopfSechOp from rfl,
    opTrace_mertensStepSechOp_sub, ← Complex.ofReal_tsum] at htr
  have hlt : ∑' n, ContinuousLinearMap.sgVal mertensClockDefectOp n < ∑' _n : ℕ, (0 : ℝ) :=
    Summable.tsum_lt_tsum hall hn₀ hsum summable_zero
  rw [tsum_zero] at hlt
  have h0 : ∑' n, ContinuousLinearMap.sgVal mertensClockDefectOp n = 0 := by
    exact_mod_cast htr.symm
  linarith

/-- **A positive eigenvalue**, with a unit eigenvector. -/
theorem exists_pos_eigenpair_mertensClockDefectOp :
    ∃ (c : ℝ) (v : L²₊), 0 < c ∧ ‖v‖ = 1 ∧ mertensClockDefectOp v = (c : ℂ) • v := by
  obtain ⟨n, hn⟩ := exists_sgVal_pos_mertensClockDefectOp
  refine ⟨_, _, hn, ?_, ContinuousLinearMap.apply_sgVec _ n⟩
  rcases ContinuousLinearMap.norm_sgVec_zero_or_one mertensClockDefectOp n with h | h
  · exact absurd (ContinuousLinearMap.sgVal_zero_of_dead h) hn.ne'
  · exact h

theorem mertensClockDefectOp_ne_zero : mertensClockDefectOp ≠ 0 := by
  obtain ⟨c, v, hc, hv, heig⟩ := exists_pos_eigenpair_mertensClockDefectOp
  intro h
  rw [h, _root_.zero_apply] at heig
  have hv0 : v ≠ 0 := fun h0 => by rw [h0, norm_zero] at hv; exact zero_ne_one hv
  have := (smul_eq_zero.mp heig.symm).resolve_right hv0
  exact hc.ne' (by exact_mod_cast this)

end

end RHTower
