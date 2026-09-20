import GaloisForLFunctions.HTGeometry.CellAveragePoincare
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Witness-line ingredients for rectangular Rellich estimates

The two results below isolate the two operations that make a bounded-core
Rellich argument avoid differentiating a line average: a coordinate-free
pairwise estimate, and Fubini on a finite `Ioc` rectangle.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Two Hilbert-space values are controlled by their deviations from any common center. -/
theorem normSq_sub_le_two_center {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v c : E) :
    ‖u - v‖ ^ 2 ≤ 2 * ‖u - c‖ ^ 2 + 2 * ‖v - c‖ ^ 2 := by
  have huv : u - v = (u - c) - (v - c) := by abel
  rw [huv]
  calc
    ‖(u - c) - (v - c)‖ ^ 2 ≤ (‖u - c‖ + ‖v - c‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (norm_sub_le _ _)
    _ ≤ 2 * ‖u - c‖ ^ 2 + 2 * ‖v - c‖ ^ 2 := by
      nlinarith [sq_nonneg (‖u - c‖ - ‖v - c‖)]

/-- Integrating the common-center pairwise estimate over one interval. -/
theorem intervalIntegral_normSq_sub_le_two_center {a b : ℝ} (hab : a ≤ b)
    {f g q : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (hq : Continuous q) :
    (∫ x in Set.Ioc a b, Complex.normSq (f x - g x)) ≤
      2 * (∫ x in Set.Ioc a b, Complex.normSq (f x - q x)) +
        2 * ∫ x in Set.Ioc a b, Complex.normSq (g x - q x) := by
  have hleft : Continuous fun x => Complex.normSq (f x - g x) :=
    Complex.continuous_normSq.comp (hf.sub hg)
  have hfirst : Continuous fun x => Complex.normSq (f x - q x) :=
    Complex.continuous_normSq.comp (hf.sub hq)
  have hsecond : Continuous fun x => Complex.normSq (g x - q x) :=
    Complex.continuous_normSq.comp (hg.sub hq)
  have hsum : Continuous fun x =>
      2 * Complex.normSq (f x - q x) + 2 * Complex.normSq (g x - q x) :=
    (continuous_const.mul hfirst).add (continuous_const.mul hsecond)
  have hpoint (x : ℝ) : Complex.normSq (f x - g x) ≤
      2 * Complex.normSq (f x - q x) + 2 * Complex.normSq (g x - q x) := by
    simpa only [Complex.normSq_eq_norm_sq] using
      normSq_sub_le_two_center (f x) (g x) (q x)
  have hmono : (∫ x in a..b, Complex.normSq (f x - g x)) ≤
      ∫ x in a..b, 2 * Complex.normSq (f x - q x) +
        2 * Complex.normSq (g x - q x) :=
    intervalIntegral.integral_mono_on hab (hleft.intervalIntegrable a b)
      (hsum.intervalIntegrable a b) (fun x _ => hpoint x)
  calc
    (∫ x in Set.Ioc a b, Complex.normSq (f x - g x)) ≤
        ∫ x in Set.Ioc a b, 2 * Complex.normSq (f x - q x) +
          2 * Complex.normSq (g x - q x) := by
      simpa only [intervalIntegral.integral_of_le hab] using hmono
    _ = (∫ x in Set.Ioc a b, 2 * Complex.normSq (f x - q x)) +
          ∫ x in Set.Ioc a b, 2 * Complex.normSq (g x - q x) := by
      exact integral_add
        ((continuous_const.mul hfirst).integrableOn_Ioc)
        ((continuous_const.mul hsecond).integrableOn_Ioc)
    _ = 2 * (∫ x in Set.Ioc a b, Complex.normSq (f x - q x)) +
          2 * ∫ x in Set.Ioc a b, Complex.normSq (g x - q x) := by
      rw [integral_const_mul, integral_const_mul]

/-- Horizontal cell mean of a complex field. -/
def horizontalCellAverage (a b : ℝ) (F : ℝ × ℝ → ℂ) (y : ℝ) : ℂ :=
  ⨍ x, F (x, y) ∂(volume.restrict (Set.Ioc a b))

/-- A horizontal cell mean of a continuous field varies continuously with the height. -/
theorem continuous_horizontalCellAverage {a b : ℝ} {F : ℝ × ℝ → ℂ}
    (hF : Continuous F) : Continuous (horizontalCellAverage a b F) := by
  let G : ℝ → ℝ → ℂ := fun y x => F (x, y)
  have hG : Continuous (Function.uncurry G) := by
    change Continuous fun p : ℝ × ℝ => F (p.2, p.1)
    exact hF.comp (continuous_snd.prodMk continuous_fst)
  have hIcc : Continuous (fun y => ∫ x in Set.Icc a b, F (x, y)) := by
    simpa only [G] using
      (continuous_parametric_integral_of_continuous hG isCompact_Icc)
  have hIoc : Continuous (fun y => ∫ x in Set.Ioc a b, F (x, y)) := by
    simpa only [integral_Icc_eq_integral_Ioc] using hIcc
  unfold horizontalCellAverage
  simp_rw [setAverage_eq]
  exact continuous_const.smul hIoc

/-- Integrating the one-dimensional horizontal cell-mean bound over height. -/
theorem horizontal_cell_mean_iterated_le
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {F Fx : ℝ × ℝ → ℂ} (hF : Continuous F) (hFx : Continuous Fx)
    (hderiv : ∀ x y : ℝ, HasDerivAt (fun t => F (t, y)) (Fx (x, y)) x) :
    (∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
      Complex.normSq (F (x, y) - horizontalCellAverage a b F y)) ≤
      (b - a) ^ 2 * ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
        Complex.normSq (Fx (x, y)) := by
  let L : ℝ → ℝ := fun y => ∫ x in Set.Ioc a b,
    Complex.normSq (F (x, y) - horizontalCellAverage a b F y)
  let R : ℝ → ℝ := fun y => ∫ x in Set.Ioc a b, Complex.normSq (Fx (x, y))
  have hAvg : Continuous (horizontalCellAverage a b F) :=
    continuous_horizontalCellAverage hF
  have hErr : Continuous fun p : ℝ × ℝ =>
      Complex.normSq (F p - horizontalCellAverage a b F p.2) :=
    Complex.continuous_normSq.comp (hF.sub (hAvg.comp continuous_snd))
  have hL : Continuous L := by
    let K : ℝ → ℝ → ℝ := fun y x =>
      Complex.normSq (F (x, y) - horizontalCellAverage a b F y)
    have hK : Continuous (Function.uncurry K) := by
      change Continuous fun p : ℝ × ℝ =>
        Complex.normSq (F (p.2, p.1) - horizontalCellAverage a b F p.1)
      exact hErr.comp (continuous_snd.prodMk continuous_fst)
    have hIcc : Continuous (fun y => ∫ x in Set.Icc a b, K y x) := by
      exact continuous_parametric_integral_of_continuous hK isCompact_Icc
    have hIoc : Continuous (fun y => ∫ x in Set.Ioc a b, K y x) := by
      simpa only [integral_Icc_eq_integral_Ioc] using hIcc
    simpa only [L, K] using hIoc
  have hR : Continuous R := by
    let K : ℝ → ℝ → ℝ := fun y x => Complex.normSq (Fx (x, y))
    have hK : Continuous (Function.uncurry K) := by
      change Continuous fun p : ℝ × ℝ => Complex.normSq (Fx (p.2, p.1))
      exact (Complex.continuous_normSq.comp hFx).comp
        (continuous_snd.prodMk continuous_fst)
    have hIcc : Continuous (fun y => ∫ x in Set.Icc a b, K y x) := by
      exact continuous_parametric_integral_of_continuous hK isCompact_Icc
    have hIoc : Continuous (fun y => ∫ x in Set.Ioc a b, K y x) := by
      simpa only [integral_Icc_eq_integral_Ioc] using hIcc
    simpa only [R, K] using hIoc
  have hpoint (y : ℝ) : L y ≤ (b - a) ^ 2 * R y := by
    dsimp [L, R]
    simpa only [horizontalCellAverage] using
      (integral_normSq_sub_average_le_of_hasDerivAt hab
        (fun x => hderiv x y)
        (hFx.comp (continuous_id.prodMk continuous_const)))
  have hRscaled : Continuous fun y => (b - a) ^ 2 * R y :=
    continuous_const.mul hR
  have hmono : (∫ y in c..d, L y) ≤ ∫ y in c..d, (b - a) ^ 2 * R y :=
    intervalIntegral.integral_mono_on hcd (hL.intervalIntegrable c d)
      (hRscaled.intervalIntegrable c d) (fun y _ => hpoint y)
  change (∫ y in Set.Ioc c d, L y) ≤ (b - a) ^ 2 * ∫ y in Set.Ioc c d, R y
  calc
    (∫ y in Set.Ioc c d, L y) ≤ ∫ y in Set.Ioc c d, (b - a) ^ 2 * R y := by
      simpa only [intervalIntegral.integral_of_le hcd] using hmono
    _ = (b - a) ^ 2 * ∫ y in Set.Ioc c d, R y := by
      rw [integral_const_mul]

/-- A finite nondegenerate interval contains a point no larger than its set average. -/
theorem exists_mem_Ioc_le_setAverage {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Set.Ioc a b) volume) :
    ∃ x ∈ Set.Ioc a b, f x ≤ ⨍ t in Set.Ioc a b, f t := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc a b)
  have hμ : μ ≠ 0 := by
    intro hzero
    have hzeroVol : volume (Set.Ioc a b) = 0 := by
      rw [← Measure.restrict_apply_univ]
      rw [show volume.restrict (Set.Ioc a b) = μ by rfl, hzero]
      rfl
    have hpos : 0 < volume (Set.Ioc a b) := by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
    exact hpos.ne' hzeroVol
  have hcomp : μ (Set.Ioc a b)ᶜ = 0 := by
    simp [μ, Measure.restrict_apply, measurableSet_Ioc]
  have hfi : Integrable f μ := by
    change Integrable f (volume.restrict (Set.Ioc a b))
    exact hf
  obtain ⟨x, hx, hle⟩ := exists_notMem_null_le_average hμ hfi hcomp
  refine ⟨x, by simpa only [mem_compl_iff, not_not] using hx, ?_⟩
  simpa only [μ] using hle

/-- An integral budget on a nondegenerate interval yields a point meeting the normalized budget. -/
theorem exists_mem_Ioc_le_of_integral_le {a b C : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Set.Ioc a b) volume)
    (hbudget : (∫ x in Set.Ioc a b, f x) ≤ (b - a) * C) :
    ∃ x ∈ Set.Ioc a b, f x ≤ C := by
  obtain ⟨x, hx, hsel⟩ := exists_mem_Ioc_le_setAverage hab hf
  refine ⟨x, hx, ?_⟩
  rw [setAverage_eq] at hsel
  have hlen : 0 < b - a := sub_pos.mpr hab
  have hsel' : f x ≤ (b - a)⁻¹ * ∫ t in Set.Ioc a b, f t := by
    simpa [measureReal_def, Real.volume_Ioc, hab.le] using hsel
  have hscaled : (b - a) * f x ≤ ∫ t in Set.Ioc a b, f t := by
    calc
      (b - a) * f x ≤ (b - a) * ((b - a)⁻¹ * ∫ t in Set.Ioc a b, f t) :=
        mul_le_mul_of_nonneg_left hsel' hlen.le
      _ = ∫ t in Set.Ioc a b, f t := by
        field_simp [hlen.ne']
  nlinarith

/-- Horizontal error to a fixed witness line is bounded through the horizontal cell mean. -/
theorem horizontal_line_error_le {a b : ℝ} (hab : a ≤ b)
    {F : ℝ × ℝ → ℂ} (hF : Continuous F) (x0 y : ℝ) :
    (∫ x in Set.Ioc a b, Complex.normSq (F (x, y) - F (x0, y))) ≤
      2 * (∫ x in Set.Ioc a b,
        Complex.normSq (F (x, y) - horizontalCellAverage a b F y)) +
      2 * (b - a) * Complex.normSq (F (x0, y) - horizontalCellAverage a b F y) := by
  have hbase := intervalIntegral_normSq_sub_le_two_center hab
    (f := fun x => F (x, y))
    (g := fun _x => F (x0, y))
    (q := fun _x => horizontalCellAverage a b F y)
    (hF.comp (continuous_id.prodMk continuous_const))
    continuous_const continuous_const
  calc
    (∫ x in Set.Ioc a b, Complex.normSq (F (x, y) - F (x0, y))) ≤
        2 * (∫ x in Set.Ioc a b,
          Complex.normSq (F (x, y) - horizontalCellAverage a b F y)) +
        2 * ∫ x in Set.Ioc a b,
          Complex.normSq (F (x0, y) - horizontalCellAverage a b F y) := hbase
    _ = 2 * (∫ x in Set.Ioc a b,
          Complex.normSq (F (x, y) - horizontalCellAverage a b F y)) +
        2 * (b - a) * Complex.normSq
          (F (x0, y) - horizontalCellAverage a b F y) := by
      rw [MeasureTheory.setIntegral_const]
      simp [measureReal_def, Real.volume_Ioc, hab]
      ring

/-- Averaging horizontal line errors over the witness coordinate. -/
theorem horizontal_witness_average_le {a b : ℝ} (hab : a ≤ b)
    {F : ℝ × ℝ → ℂ} (hF : Continuous F) (y : ℝ) :
    (∫ x0 in Set.Ioc a b, ∫ x in Set.Ioc a b,
      Complex.normSq (F (x, y) - F (x0, y))) ≤
      4 * (b - a) * ∫ x in Set.Ioc a b,
        Complex.normSq (F (x, y) - horizontalCellAverage a b F y) := by
  let A : ℝ := ∫ x in Set.Ioc a b,
    Complex.normSq (F (x, y) - horizontalCellAverage a b F y)
  let E : ℝ → ℝ := fun x0 =>
    Complex.normSq (F (x0, y) - horizontalCellAverage a b F y)
  let L : ℝ → ℝ := fun x0 => ∫ x in Set.Ioc a b,
    Complex.normSq (F (x, y) - F (x0, y))
  have hE : Continuous E := by
    dsimp [E]
    exact Complex.continuous_normSq.comp
      ((hF.comp (continuous_id.prodMk continuous_const)).sub continuous_const)
  have hL : Continuous L := by
    let K : ℝ → ℝ → ℝ := fun x0 x =>
      Complex.normSq (F (x, y) - F (x0, y))
    have hK : Continuous (Function.uncurry K) := by
      change Continuous fun p : ℝ × ℝ => Complex.normSq (F (p.2, y) - F (p.1, y))
      exact Complex.continuous_normSq.comp
        ((hF.comp (continuous_snd.prodMk continuous_const)).sub
          (hF.comp (continuous_fst.prodMk continuous_const)))
    have hIcc : Continuous (fun x0 => ∫ x in Set.Icc a b, K x0 x) := by
      exact continuous_parametric_integral_of_continuous hK isCompact_Icc
    have hIoc : Continuous (fun x0 => ∫ x in Set.Ioc a b, K x0 x) := by
      simpa only [integral_Icc_eq_integral_Ioc] using hIcc
    simpa only [L, K] using hIoc
  have hpoint (x0 : ℝ) : L x0 ≤ 2 * A + 2 * (b - a) * E x0 := by
    dsimp [L, A, E]
    exact horizontal_line_error_le hab hF x0 y
  have hR : Continuous fun x0 => 2 * A + 2 * (b - a) * E x0 :=
    continuous_const.add (continuous_const.mul hE)
  have hmono : (∫ x0 in a..b, L x0) ≤ ∫ x0 in a..b, 2 * A + 2 * (b - a) * E x0 :=
    intervalIntegral.integral_mono_on hab (hL.intervalIntegrable a b)
      (hR.intervalIntegrable a b) (fun x0 _ => hpoint x0)
  have hfinite : volume (Set.Ioc a b) ≠ (⊤ : ENNReal) := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  change (∫ x0 in Set.Ioc a b, L x0) ≤ 4 * (b - a) * A
  calc
    (∫ x0 in Set.Ioc a b, L x0) ≤ ∫ x0 in Set.Ioc a b,
        2 * A + 2 * (b - a) * E x0 := by
      simpa only [intervalIntegral.integral_of_le hab] using hmono
    _ = (∫ _x0 in Set.Ioc a b, 2 * A) +
        ∫ x0 in Set.Ioc a b, (2 * (b - a)) * E x0 := by
      rw [show (fun x0 => 2 * A + 2 * (b - a) * E x0) =
        fun x0 => 2 * A + (2 * (b - a)) * E x0 by funext x0; ring]
      exact integral_add (integrableOn_const hfinite)
        ((continuous_const.mul hE).integrableOn_Ioc)
    _ = 4 * (b - a) * A := by
      rw [MeasureTheory.setIntegral_const, integral_const_mul]
      simp [measureReal_def, Real.volume_Ioc, hab]
      change (b - a) * (2 * A) + 2 * (b - a) *
        (∫ x0 in Set.Ioc a b, E x0) = _
      rw [show (∫ x0 in Set.Ioc a b, E x0) = A by rfl]
      ring

/-- The horizontal two-witness average is controlled by horizontal rectangle energy. -/
theorem horizontal_witness_average_iterated_le
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {F Fx : ℝ × ℝ → ℂ} (hF : Continuous F) (hFx : Continuous Fx)
    (hderiv : ∀ x y : ℝ, HasDerivAt (fun t => F (t, y)) (Fx (x, y)) x) :
    (∫ y in Set.Ioc c d, ∫ x0 in Set.Ioc a b, ∫ x in Set.Ioc a b,
      Complex.normSq (F (x, y) - F (x0, y))) ≤
      4 * (b - a) * ((b - a) ^ 2 * ∫ y in Set.Ioc c d,
        ∫ x in Set.Ioc a b, Complex.normSq (Fx (x, y))) := by
  let A : ℝ → ℝ := fun y => ∫ x in Set.Ioc a b,
    Complex.normSq (F (x, y) - horizontalCellAverage a b F y)
  let M : ℝ → ℝ := fun y => ∫ x0 in Set.Ioc a b, ∫ x in Set.Ioc a b,
    Complex.normSq (F (x, y) - F (x0, y))
  have hAvg : Continuous (horizontalCellAverage a b F) :=
    continuous_horizontalCellAverage hF
  have hA : Continuous A := by
    let K : ℝ → ℝ → ℝ := fun y x =>
      Complex.normSq (F (x, y) - horizontalCellAverage a b F y)
    have hK : Continuous (Function.uncurry K) := by
      change Continuous fun p : ℝ × ℝ =>
        Complex.normSq (F (p.2, p.1) - horizontalCellAverage a b F p.1)
      exact Complex.continuous_normSq.comp
        ((hF.comp (continuous_snd.prodMk continuous_fst)).sub
          (hAvg.comp continuous_fst))
    have hIcc : Continuous (fun y => ∫ x in Set.Icc a b, K y x) := by
      exact continuous_parametric_integral_of_continuous hK isCompact_Icc
    have hIoc : Continuous (fun y => ∫ x in Set.Ioc a b, K y x) := by
      simpa only [integral_Icc_eq_integral_Ioc] using hIcc
    simpa only [A, K] using hIoc
  have hM : Continuous M := by
    let K : (ℝ × ℝ) → ℝ → ℝ := fun p x =>
      Complex.normSq (F (x, p.1) - F (p.2, p.1))
    have hK : Continuous (Function.uncurry K) := by
      change Continuous fun p : (ℝ × ℝ) × ℝ =>
        Complex.normSq (F (p.2, p.1.1) - F (p.1.2, p.1.1))
      exact Complex.continuous_normSq.comp
        ((hF.comp (continuous_snd.prodMk (continuous_fst.comp continuous_fst))).sub
          (hF.comp ((continuous_snd.comp continuous_fst).prodMk
            (continuous_fst.comp continuous_fst))))
    have hInner : Continuous fun p : ℝ × ℝ => ∫ x in Set.Ioc a b, K p x := by
      have hIcc : Continuous fun p : ℝ × ℝ => ∫ x in Set.Icc a b, K p x := by
        exact continuous_parametric_integral_of_continuous hK isCompact_Icc
      simpa only [integral_Icc_eq_integral_Ioc] using hIcc
    let G : ℝ → ℝ → ℝ := fun y x0 => ∫ x in Set.Ioc a b, K (y, x0) x
    have hG : Continuous (Function.uncurry G) := by
      change Continuous fun p : ℝ × ℝ => ∫ x in Set.Ioc a b, K (p.1, p.2) x
      exact hInner
    have hIcc : Continuous (fun y => ∫ x0 in Set.Icc a b, G y x0) := by
      exact continuous_parametric_integral_of_continuous hG isCompact_Icc
    have hIoc : Continuous (fun y => ∫ x0 in Set.Ioc a b, G y x0) := by
      simpa only [integral_Icc_eq_integral_Ioc] using hIcc
    simpa only [M, G, K] using hIoc
  have hpoint (y : ℝ) : M y ≤ 4 * (b - a) * A y := by
    dsimp [M, A]
    exact horizontal_witness_average_le hab hF y
  have hR : Continuous fun y => 4 * (b - a) * A y :=
    continuous_const.mul hA
  have hmono : (∫ y in c..d, M y) ≤ ∫ y in c..d, 4 * (b - a) * A y :=
    intervalIntegral.integral_mono_on hcd (hM.intervalIntegrable c d)
      (hR.intervalIntegrable c d) (fun y _ => hpoint y)
  have hintermediate : (∫ y in Set.Ioc c d, M y) ≤
      4 * (b - a) * ∫ y in Set.Ioc c d, A y := by
    calc
      (∫ y in Set.Ioc c d, M y) ≤ ∫ y in Set.Ioc c d, 4 * (b - a) * A y := by
        simpa only [intervalIntegral.integral_of_le hcd] using hmono
      _ = 4 * (b - a) * ∫ y in Set.Ioc c d, A y := by
        rw [integral_const_mul]
  have henergy := horizontal_cell_mean_iterated_le hab hcd hF hFx hderiv
  have hfactor : 0 ≤ 4 * (b - a) := by positivity
  change (∫ y in Set.Ioc c d, M y) ≤
    4 * (b - a) * ((b - a) ^ 2 * ∫ y in Set.Ioc c d,
      ∫ x in Set.Ioc a b, Complex.normSq (Fx (x, y)))
  exact hintermediate.trans (mul_le_mul_of_nonneg_left henergy hfactor)

/-- Vertical cell mean of a complex field. -/
def verticalCellAverage (c d : ℝ) (F : ℝ × ℝ → ℂ) (x : ℝ) : ℂ :=
  horizontalCellAverage c d (fun p => F (p.2, p.1)) x

/-- Integrating the vertical cell-mean bound over horizontal position. -/
theorem vertical_cell_mean_iterated_le
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {F Fy : ℝ × ℝ → ℂ} (hF : Continuous F) (hFy : Continuous Fy)
    (hderiv : ∀ x y : ℝ, HasDerivAt (fun t => F (x, t)) (Fy (x, y)) y) :
    (∫ x in Set.Ioc a b, ∫ y in Set.Ioc c d,
      Complex.normSq (F (x, y) - verticalCellAverage c d F x)) ≤
      (d - c) ^ 2 * ∫ x in Set.Ioc a b,
        ∫ y in Set.Ioc c d, Complex.normSq (Fy (x, y)) := by
  let Fswap : ℝ × ℝ → ℂ := fun p => F (p.2, p.1)
  let Fyswap : ℝ × ℝ → ℂ := fun p => Fy (p.2, p.1)
  have hFswap : Continuous Fswap := by
    exact hF.comp (continuous_snd.prodMk continuous_fst)
  have hFyswap : Continuous Fyswap := by
    exact hFy.comp (continuous_snd.prodMk continuous_fst)
  have hderivSwap : ∀ u v : ℝ,
      HasDerivAt (fun t => Fswap (t, v)) (Fyswap (u, v)) u := by
    intro u v
    exact hderiv v u
  simpa only [Fswap, Fyswap, verticalCellAverage] using
    (horizontal_cell_mean_iterated_le hcd hab hFswap hFyswap hderivSwap)

/-- A full rectangle is controlled by horizontal displacement to one line and vertical error on it. -/
theorem rectangle_error_to_vertical_witness_le
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {F : ℝ × ℝ → ℂ} (hF : Continuous F) (x0 : ℝ) :
    (∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
      Complex.normSq (F (x, y) - verticalCellAverage c d F x0)) ≤
      2 * (∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
        Complex.normSq (F (x, y) - F (x0, y))) +
      2 * (b - a) * ∫ y in Set.Ioc c d,
        Complex.normSq (F (x0, y) - verticalCellAverage c d F x0) := by
  let c0 : ℂ := verticalCellAverage c d F x0
  let Q : ℝ → ℝ := fun y => ∫ x in Set.Ioc a b,
    Complex.normSq (F (x, y) - c0)
  let H : ℝ → ℝ := fun y => ∫ x in Set.Ioc a b,
    Complex.normSq (F (x, y) - F (x0, y))
  let V : ℝ → ℝ := fun y => Complex.normSq (F (x0, y) - c0)
  have hQ : Continuous Q := by
    let K : ℝ → ℝ → ℝ := fun y x => Complex.normSq (F (x, y) - c0)
    have hK : Continuous (Function.uncurry K) := by
      change Continuous fun p : ℝ × ℝ => Complex.normSq (F (p.2, p.1) - c0)
      exact Complex.continuous_normSq.comp
        ((hF.comp (continuous_snd.prodMk continuous_fst)).sub continuous_const)
    have hIcc : Continuous (fun y => ∫ x in Set.Icc a b, K y x) := by
      exact continuous_parametric_integral_of_continuous hK isCompact_Icc
    have hIoc : Continuous (fun y => ∫ x in Set.Ioc a b, K y x) := by
      simpa only [integral_Icc_eq_integral_Ioc] using hIcc
    simpa only [Q, K] using hIoc
  have hH : Continuous H := by
    let K : ℝ → ℝ → ℝ := fun y x => Complex.normSq (F (x, y) - F (x0, y))
    have hK : Continuous (Function.uncurry K) := by
      change Continuous fun p : ℝ × ℝ =>
        Complex.normSq (F (p.2, p.1) - F (x0, p.1))
      exact Complex.continuous_normSq.comp
        ((hF.comp (continuous_snd.prodMk continuous_fst)).sub
          (hF.comp (continuous_const.prodMk continuous_fst)))
    have hIcc : Continuous (fun y => ∫ x in Set.Icc a b, K y x) := by
      exact continuous_parametric_integral_of_continuous hK isCompact_Icc
    have hIoc : Continuous (fun y => ∫ x in Set.Ioc a b, K y x) := by
      simpa only [integral_Icc_eq_integral_Ioc] using hIcc
    simpa only [H, K] using hIoc
  have hV : Continuous V := by
    dsimp [V]
    exact Complex.continuous_normSq.comp
      ((hF.comp (continuous_const.prodMk continuous_id)).sub continuous_const)
  have hpoint (y : ℝ) : Q y ≤ 2 * H y + 2 * (b - a) * V y := by
    dsimp [Q, H, V]
    have hbase := intervalIntegral_normSq_sub_le_two_center hab
      (f := fun x => F (x, y))
      (g := fun _x => c0)
      (q := fun _x => F (x0, y))
      (hF.comp (continuous_id.prodMk continuous_const))
      continuous_const continuous_const
    have hsymm : Complex.normSq (c0 - F (x0, y)) =
        Complex.normSq (F (x0, y) - c0) := by
      rw [show c0 - F (x0, y) = -(F (x0, y) - c0) by ring,
        Complex.normSq_neg]
    rw [hsymm] at hbase
    calc
      (∫ x in Set.Ioc a b, Complex.normSq (F (x, y) - c0)) ≤
          2 * (∫ x in Set.Ioc a b, Complex.normSq (F (x, y) - F (x0, y))) +
          2 * ∫ x in Set.Ioc a b, Complex.normSq (F (x0, y) - c0) := hbase
      _ = 2 * (∫ x in Set.Ioc a b, Complex.normSq (F (x, y) - F (x0, y))) +
          2 * (b - a) * Complex.normSq (F (x0, y) - c0) := by
        rw [MeasureTheory.setIntegral_const]
        simp [measureReal_def, Real.volume_Ioc, hab]
        ring
  have hR : Continuous fun y => 2 * H y + 2 * (b - a) * V y :=
    (continuous_const.mul hH).add (continuous_const.mul hV)
  have hmono : (∫ y in c..d, Q y) ≤ ∫ y in c..d, 2 * H y + 2 * (b - a) * V y :=
    intervalIntegral.integral_mono_on hcd (hQ.intervalIntegrable c d)
      (hR.intervalIntegrable c d) (fun y _ => hpoint y)
  change (∫ y in Set.Ioc c d, Q y) ≤
    2 * (∫ y in Set.Ioc c d, H y) + 2 * (b - a) * ∫ y in Set.Ioc c d, V y
  calc
    (∫ y in Set.Ioc c d, Q y) ≤ ∫ y in Set.Ioc c d, 2 * H y + 2 * (b - a) * V y := by
      simpa only [intervalIntegral.integral_of_le hcd] using hmono
    _ = (∫ y in Set.Ioc c d, 2 * H y) +
        ∫ y in Set.Ioc c d, (2 * (b - a)) * V y := by
      rw [show (fun y => 2 * H y + 2 * (b - a) * V y) =
        fun y => 2 * H y + (2 * (b - a)) * V y by funext y; ring]
      exact integral_add ((continuous_const.mul hH).integrableOn_Ioc)
        ((continuous_const.mul hV).integrableOn_Ioc)
    _ = 2 * (∫ y in Set.Ioc c d, H y) +
        2 * (b - a) * ∫ y in Set.Ioc c d, V y := by
      rw [integral_const_mul, integral_const_mul]

/-- Fubini on a finite rectangle written with the `Ioc` convention of cell Poincaré. -/
theorem rectangle_fubini_y {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b c d : ℝ} (F : ℝ × ℝ → E) (hF : Continuous F) :
    (∫ p in Set.Ioc a b ×ˢ Set.Ioc c d, F p) =
      ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b, F (x, y) := by
  have hsubset : Set.Ioc a b ×ˢ Set.Ioc c d ⊆ Set.Icc a b ×ˢ Set.Icc c d := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨⟨hx.1.le, hx.2⟩, ⟨hy.1.le, hy.2⟩⟩
  have hIcc : IntegrableOn F (Set.Icc a b ×ˢ Set.Icc c d) volume :=
    hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hi : IntegrableOn F (Set.Ioc a b ×ˢ Set.Ioc c d) volume :=
    hIcc.mono_set hsubset
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hi
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact integral_prod_symm _ hi

/-- A scalar `C¹` field on a rectangle has one vertical witness line whose vertical mean is a
constant approximation with mesh-squared Dirichlet error. -/
theorem exists_rectangle_witness_line
    {a b c d : ℝ} (hab : a < b) (hcd : c ≤ d)
    {F Fx Fy : ℝ × ℝ → ℂ} (hF : Continuous F) (hFx : Continuous Fx) (hFy : Continuous Fy)
    (hderivX : ∀ x y : ℝ, HasDerivAt (fun t => F (t, y)) (Fx (x, y)) x)
    (hderivY : ∀ x y : ℝ, HasDerivAt (fun t => F (x, t)) (Fy (x, y)) y) :
    ∃ x0 ∈ Set.Ioc a b,
      (∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
        Complex.normSq (F (x, y) - verticalCellAverage c d F x0)) ≤
        8 * (b - a) ^ 2 * (∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
          Complex.normSq (Fx (x, y))) +
        2 * (d - c) ^ 2 * (∫ x in Set.Ioc a b, ∫ y in Set.Ioc c d,
          Complex.normSq (Fy (x, y))) := by
  let E_x : ℝ := ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b, Complex.normSq (Fx (x, y))
  let E_y : ℝ := ∫ x in Set.Ioc a b, ∫ y in Set.Ioc c d, Complex.normSq (Fy (x, y))
  let C : ℝ := 8 * (b - a) ^ 2 * E_x + 2 * (d - c) ^ 2 * E_y
  let Q : ℝ → ℝ := fun x0 => ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
    Complex.normSq (F (x, y) - verticalCellAverage c d F x0)
  let H : ℝ → ℝ := fun x0 => ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
    Complex.normSq (F (x, y) - F (x0, y))
  let V : ℝ → ℝ := fun x0 => ∫ y in Set.Ioc c d,
    Complex.normSq (F (x0, y) - verticalCellAverage c d F x0)
  have hC : Continuous (verticalCellAverage c d F) := by
    unfold verticalCellAverage
    exact continuous_horizontalCellAverage
      (hF.comp (continuous_snd.prodMk continuous_fst))
  have hQ : Continuous Q := by
    let K : (ℝ × ℝ) → ℝ → ℝ := fun p x =>
      Complex.normSq (F (x, p.2) - verticalCellAverage c d F p.1)
    have hK : Continuous (Function.uncurry K) := by
      change Continuous fun p : (ℝ × ℝ) × ℝ =>
        Complex.normSq (F (p.2, p.1.2) - verticalCellAverage c d F p.1.1)
      exact Complex.continuous_normSq.comp
        ((hF.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))).sub
          (hC.comp (continuous_fst.comp continuous_fst)))
    have hInner : Continuous fun p : ℝ × ℝ => ∫ x in Set.Ioc a b, K p x := by
      have hIcc : Continuous fun p : ℝ × ℝ => ∫ x in Set.Icc a b, K p x := by
        exact continuous_parametric_integral_of_continuous hK isCompact_Icc
      simpa only [integral_Icc_eq_integral_Ioc] using hIcc
    let G : ℝ → ℝ → ℝ := fun x0 y => ∫ x in Set.Ioc a b, K (x0, y) x
    have hG : Continuous (Function.uncurry G) := by
      change Continuous fun p : ℝ × ℝ => ∫ x in Set.Ioc a b, K (p.1, p.2) x
      exact hInner
    have hIcc : Continuous (fun x0 => ∫ y in Set.Icc c d, G x0 y) := by
      exact continuous_parametric_integral_of_continuous hG isCompact_Icc
    have hIoc : Continuous (fun x0 => ∫ y in Set.Ioc c d, G x0 y) := by
      simpa only [integral_Icc_eq_integral_Ioc] using hIcc
    simpa only [Q, G, K] using hIoc
  let W : ℝ → ℝ → ℝ := fun x0 y => ∫ x in Set.Ioc a b,
    Complex.normSq (F (x, y) - F (x0, y))
  have hW : Continuous (Function.uncurry W) := by
    let K : (ℝ × ℝ) → ℝ → ℝ := fun p x =>
      Complex.normSq (F (x, p.2) - F (p.1, p.2))
    have hK : Continuous (Function.uncurry K) := by
      change Continuous fun p : (ℝ × ℝ) × ℝ =>
        Complex.normSq (F (p.2, p.1.2) - F (p.1.1, p.1.2))
      exact Complex.continuous_normSq.comp
        ((hF.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))).sub
          (hF.comp ((continuous_fst.comp continuous_fst).prodMk
            (continuous_snd.comp continuous_fst))))
    have hInner : Continuous fun p : ℝ × ℝ => ∫ x in Set.Ioc a b, K p x := by
      have hIcc : Continuous fun p : ℝ × ℝ => ∫ x in Set.Icc a b, K p x := by
        exact continuous_parametric_integral_of_continuous hK isCompact_Icc
      simpa only [integral_Icc_eq_integral_Ioc] using hIcc
    change Continuous fun p : ℝ × ℝ => ∫ x in Set.Ioc a b, K p x
    exact hInner
  have hH : Continuous H := by
    have hIcc : Continuous (fun x0 => ∫ y in Set.Icc c d, W x0 y) := by
      exact continuous_parametric_integral_of_continuous hW isCompact_Icc
    have hIoc : Continuous (fun x0 => ∫ y in Set.Ioc c d, W x0 y) := by
      simpa only [integral_Icc_eq_integral_Ioc] using hIcc
    simpa only [H, W] using hIoc
  have hV : Continuous V := by
    let K : ℝ → ℝ → ℝ := fun x0 y =>
      Complex.normSq (F (x0, y) - verticalCellAverage c d F x0)
    have hK : Continuous (Function.uncurry K) := by
      change Continuous fun p : ℝ × ℝ =>
        Complex.normSq (F (p.1, p.2) - verticalCellAverage c d F p.1)
      exact Complex.continuous_normSq.comp
        (hF.sub (hC.comp continuous_fst))
    have hIcc : Continuous (fun x0 => ∫ y in Set.Icc c d, K x0 y) := by
      exact continuous_parametric_integral_of_continuous hK isCompact_Icc
    have hIoc : Continuous (fun x0 => ∫ y in Set.Ioc c d, K x0 y) := by
      simpa only [integral_Icc_eq_integral_Ioc] using hIcc
    simpa only [V, K] using hIoc
  have hpoint (x0 : ℝ) : Q x0 ≤ 2 * H x0 + 2 * (b - a) * V x0 := by
    dsimp [Q, H, V]
    exact rectangle_error_to_vertical_witness_le hab.le hcd hF x0
  have hR : Continuous fun x0 => 2 * H x0 + 2 * (b - a) * V x0 :=
    (continuous_const.mul hH).add (continuous_const.mul hV)
  have hmono : (∫ x0 in a..b, Q x0) ≤ ∫ x0 in a..b, 2 * H x0 + 2 * (b - a) * V x0 :=
    intervalIntegral.integral_mono_on hab.le (hQ.intervalIntegrable a b)
      (hR.intervalIntegrable a b) (fun x0 _ => hpoint x0)
  have hqint : (∫ x0 in Set.Ioc a b, Q x0) ≤
      2 * (∫ x0 in Set.Ioc a b, H x0) + 2 * (b - a) * ∫ x0 in Set.Ioc a b, V x0 := by
    calc
      (∫ x0 in Set.Ioc a b, Q x0) ≤ ∫ x0 in Set.Ioc a b, 2 * H x0 + 2 * (b - a) * V x0 := by
        simpa only [intervalIntegral.integral_of_le hab.le] using hmono
      _ = (∫ x0 in Set.Ioc a b, 2 * H x0) +
          ∫ x0 in Set.Ioc a b, (2 * (b - a)) * V x0 := by
        rw [show (fun x0 => 2 * H x0 + 2 * (b - a) * V x0) =
          fun x0 => 2 * H x0 + (2 * (b - a)) * V x0 by funext x0; ring]
        exact integral_add ((continuous_const.mul hH).integrableOn_Ioc)
          ((continuous_const.mul hV).integrableOn_Ioc)
      _ = 2 * (∫ x0 in Set.Ioc a b, H x0) +
          2 * (b - a) * ∫ x0 in Set.Ioc a b, V x0 := by
        rw [integral_const_mul, integral_const_mul]
  have hhorizontal := horizontal_witness_average_iterated_le hab.le hcd hF hFx hderivX
  have hvertical := vertical_cell_mean_iterated_le hab.le hcd hF hFy hderivY
  have hwidth : 0 ≤ b - a := sub_nonneg.mpr hab.le
  have hWint : Integrable (Function.uncurry W)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc c d))) := by
    have hsubset : Set.Ioc a b ×ˢ Set.Ioc c d ⊆ Set.Icc a b ×ˢ Set.Icc c d := by
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      exact ⟨⟨hx.1.le, hx.2⟩, ⟨hy.1.le, hy.2⟩⟩
    have hIcc : IntegrableOn (Function.uncurry W)
        (Set.Icc a b ×ˢ Set.Icc c d) volume :=
      hW.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have hi : IntegrableOn (Function.uncurry W)
        (Set.Ioc a b ×ˢ Set.Ioc c d) volume := hIcc.mono_set hsubset
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hi
    exact hi
  have hhorizontal' : (∫ x0 in Set.Ioc a b, H x0) ≤
      4 * (b - a) * ((b - a) ^ 2 * E_x) := by
    calc
      (∫ x0 in Set.Ioc a b, H x0) = ∫ y in Set.Ioc c d, ∫ x0 in Set.Ioc a b,
          ∫ x in Set.Ioc a b, Complex.normSq (F (x, y) - F (x0, y)) := by
        simpa only [H, W] using (integral_integral_swap hWint)
      _ ≤ 4 * (b - a) * ((b - a) ^ 2 * E_x) := hhorizontal
  have hbudget : (∫ x0 in Set.Ioc a b, Q x0) ≤ (b - a) * C := by
    calc
      (∫ x0 in Set.Ioc a b, Q x0) ≤
          2 * (∫ x0 in Set.Ioc a b, H x0) + 2 * (b - a) * ∫ x0 in Set.Ioc a b, V x0 := hqint
      _ ≤ 2 * (4 * (b - a) * ((b - a) ^ 2 * E_x)) +
          2 * (b - a) * ((d - c) ^ 2 * E_y) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hhorizontal' (by norm_num))
          (mul_le_mul_of_nonneg_left hvertical (by positivity))
      _ = (b - a) * C := by
        dsimp [C]
        ring
  obtain ⟨x0, hx0, hx0bound⟩ := exists_mem_Ioc_le_of_integral_le hab hQ.integrableOn_Ioc hbudget
  refine ⟨x0, hx0, ?_⟩
  exact hx0bound

/-- A single coordinate works simultaneously for a finite family once the total
horizontal and vertical witness budgets are controlled. -/
theorem exists_common_witness_of_finite_budget
    {ι : Type*} [Fintype ι] {a b A B : ℝ} (hab : a < b)
    {Q H V : ι → ℝ → ℝ}
    (hQ : ∀ i, Continuous (Q i)) (hH : ∀ i, Continuous (H i))
    (hV : ∀ i, Continuous (V i))
    (hpoint : ∀ i x, Q i x ≤ 2 * H i x + 2 * (b - a) * V i x)
    (hHbudget : (∑ i, ∫ x in Set.Ioc a b, H i x) ≤ (b - a) * A)
    (hVbudget : (∑ i, ∫ x in Set.Ioc a b, V i x) ≤ B) :
    ∃ x0 ∈ Set.Ioc a b, (∑ i, Q i x0) ≤ 2 * A + 2 * B := by
  let QS : ℝ → ℝ := fun x => ∑ i, Q i x
  let HS : ℝ → ℝ := fun x => ∑ i, H i x
  let VS : ℝ → ℝ := fun x => ∑ i, V i x
  have hQS : Continuous QS := by
    dsimp [QS]
    exact continuous_finsetSum Finset.univ fun i _ => hQ i
  have hHS : Continuous HS := by
    dsimp [HS]
    exact continuous_finsetSum Finset.univ fun i _ => hH i
  have hVS : Continuous VS := by
    dsimp [VS]
    exact continuous_finsetSum Finset.univ fun i _ => hV i
  have hsumQ : (∫ x in Set.Ioc a b, QS x) = ∑ i, ∫ x in Set.Ioc a b, Q i x := by
    dsimp [QS]
    exact MeasureTheory.integral_finsetSum Finset.univ
      (fun i _ => (hQ i).integrableOn_Ioc)
  have hsumH : (∫ x in Set.Ioc a b, HS x) = ∑ i, ∫ x in Set.Ioc a b, H i x := by
    dsimp [HS]
    exact MeasureTheory.integral_finsetSum Finset.univ
      (fun i _ => (hH i).integrableOn_Ioc)
  have hsumV : (∫ x in Set.Ioc a b, VS x) = ∑ i, ∫ x in Set.Ioc a b, V i x := by
    dsimp [VS]
    exact MeasureTheory.integral_finsetSum Finset.univ
      (fun i _ => (hV i).integrableOn_Ioc)
  have hpointSum (x : ℝ) : QS x ≤ 2 * HS x + 2 * (b - a) * VS x := by
    calc
      QS x = ∑ i, Q i x := rfl
      _ ≤ ∑ i, (2 * H i x + 2 * (b - a) * V i x) :=
        Finset.sum_le_sum fun i _ => hpoint i x
      _ = 2 * HS x + 2 * (b - a) * VS x := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hR : Continuous fun x => 2 * HS x + 2 * (b - a) * VS x :=
    (continuous_const.mul hHS).add (continuous_const.mul hVS)
  have hmono : (∫ x in a..b, QS x) ≤ ∫ x in a..b, 2 * HS x + 2 * (b - a) * VS x :=
    intervalIntegral.integral_mono_on hab.le (hQS.intervalIntegrable a b)
      (hR.intervalIntegrable a b) (fun x _ => hpointSum x)
  have hqint : (∫ x in Set.Ioc a b, QS x) ≤
      2 * (∫ x in Set.Ioc a b, HS x) +
        2 * (b - a) * ∫ x in Set.Ioc a b, VS x := by
    calc
      (∫ x in Set.Ioc a b, QS x) ≤
          ∫ x in Set.Ioc a b, 2 * HS x + 2 * (b - a) * VS x := by
        simpa only [intervalIntegral.integral_of_le hab.le] using hmono
      _ = (∫ x in Set.Ioc a b, 2 * HS x) +
          ∫ x in Set.Ioc a b, (2 * (b - a)) * VS x := by
        rw [show (fun x => 2 * HS x + 2 * (b - a) * VS x) =
          fun x => 2 * HS x + (2 * (b - a)) * VS x by funext x; ring]
        exact integral_add ((continuous_const.mul hHS).integrableOn_Ioc)
          ((continuous_const.mul hVS).integrableOn_Ioc)
      _ = 2 * (∫ x in Set.Ioc a b, HS x) +
          2 * (b - a) * ∫ x in Set.Ioc a b, VS x := by
        rw [integral_const_mul, integral_const_mul]
  have hwidth : 0 ≤ b - a := sub_nonneg.mpr hab.le
  have hbudget : (∫ x in Set.Ioc a b, QS x) ≤
      (b - a) * (2 * A + 2 * B) := by
    calc
      (∫ x in Set.Ioc a b, QS x) ≤
          2 * (∫ x in Set.Ioc a b, HS x) +
            2 * (b - a) * ∫ x in Set.Ioc a b, VS x := hqint
      _ = 2 * (∑ i, ∫ x in Set.Ioc a b, H i x) +
            2 * (b - a) * (∑ i, ∫ x in Set.Ioc a b, V i x) := by
        rw [hsumH, hsumV]
      _ ≤ 2 * ((b - a) * A) + 2 * (b - a) * B := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hHbudget (by norm_num))
          (mul_le_mul_of_nonneg_left hVbudget (by positivity))
      _ = (b - a) * (2 * A + 2 * B) := by ring
  obtain ⟨x0, hx0, hx0bound⟩ :=
    exists_mem_Ioc_le_of_integral_le hab hQS.integrableOn_Ioc hbudget
  exact ⟨x0, hx0, hx0bound⟩

/-- A vertical cell mean of a continuous field varies continuously with the horizontal coordinate. -/
theorem continuous_verticalCellAverage {c d : ℝ} {F : ℝ × ℝ → ℂ}
    (hF : Continuous F) : Continuous (verticalCellAverage c d F) := by
  unfold verticalCellAverage
  exact continuous_horizontalCellAverage
    (hF.comp (continuous_snd.prodMk continuous_fst))

/-- The rectangle error to the vertical mean on a chosen witness line is continuous in that line. -/
theorem continuous_rectangle_error_to_vertical_witness
    {a b c d : ℝ} {F : ℝ × ℝ → ℂ} (hF : Continuous F) :
    Continuous fun x0 => ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
      Complex.normSq (F (x, y) - verticalCellAverage c d F x0) := by
  have hC : Continuous (verticalCellAverage c d F) :=
    continuous_verticalCellAverage hF
  let K : (ℝ × ℝ) → ℝ → ℝ := fun p x =>
    Complex.normSq (F (x, p.2) - verticalCellAverage c d F p.1)
  have hK : Continuous (Function.uncurry K) := by
    change Continuous fun p : (ℝ × ℝ) × ℝ =>
      Complex.normSq (F (p.2, p.1.2) - verticalCellAverage c d F p.1.1)
    exact Complex.continuous_normSq.comp
      ((hF.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))).sub
        (hC.comp (continuous_fst.comp continuous_fst)))
  have hInner : Continuous fun p : ℝ × ℝ => ∫ x in Set.Ioc a b, K p x := by
    have hIcc : Continuous fun p : ℝ × ℝ => ∫ x in Set.Icc a b, K p x := by
      exact continuous_parametric_integral_of_continuous hK isCompact_Icc
    simpa only [integral_Icc_eq_integral_Ioc] using hIcc
  let G : ℝ → ℝ → ℝ := fun x0 y => ∫ x in Set.Ioc a b, K (x0, y) x
  have hG : Continuous (Function.uncurry G) := by
    change Continuous fun p : ℝ × ℝ => ∫ x in Set.Ioc a b, K (p.1, p.2) x
    exact hInner
  have hIcc : Continuous (fun x0 => ∫ y in Set.Icc c d, G x0 y) := by
    exact continuous_parametric_integral_of_continuous hG isCompact_Icc
  have hIoc : Continuous (fun x0 => ∫ y in Set.Ioc c d, G x0 y) := by
    simpa only [integral_Icc_eq_integral_Ioc] using hIcc
  simpa only [G, K] using hIoc

/-- The total horizontal error to a chosen vertical witness line is continuous in that line. -/
theorem continuous_horizontal_witness_error
    {a b c d : ℝ} {F : ℝ × ℝ → ℂ} (hF : Continuous F) :
    Continuous fun x0 => ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
      Complex.normSq (F (x, y) - F (x0, y)) := by
  let K : (ℝ × ℝ) → ℝ → ℝ := fun p x =>
    Complex.normSq (F (x, p.2) - F (p.1, p.2))
  have hK : Continuous (Function.uncurry K) := by
    change Continuous fun p : (ℝ × ℝ) × ℝ =>
      Complex.normSq (F (p.2, p.1.2) - F (p.1.1, p.1.2))
    exact Complex.continuous_normSq.comp
      ((hF.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))).sub
        (hF.comp ((continuous_fst.comp continuous_fst).prodMk
          (continuous_snd.comp continuous_fst))))
  have hInner : Continuous fun p : ℝ × ℝ => ∫ x in Set.Ioc a b, K p x := by
    have hIcc : Continuous fun p : ℝ × ℝ => ∫ x in Set.Icc a b, K p x := by
      exact continuous_parametric_integral_of_continuous hK isCompact_Icc
    simpa only [integral_Icc_eq_integral_Ioc] using hIcc
  let G : ℝ → ℝ → ℝ := fun x0 y => ∫ x in Set.Ioc a b, K (x0, y) x
  have hG : Continuous (Function.uncurry G) := by
    change Continuous fun p : ℝ × ℝ => ∫ x in Set.Ioc a b, K (p.1, p.2) x
    exact hInner
  have hIcc : Continuous (fun x0 => ∫ y in Set.Icc c d, G x0 y) := by
    exact continuous_parametric_integral_of_continuous hG isCompact_Icc
  have hIoc : Continuous (fun x0 => ∫ y in Set.Ioc c d, G x0 y) := by
    simpa only [integral_Icc_eq_integral_Ioc] using hIcc
  simpa only [G, K] using hIoc

/-- The vertical error of a chosen witness line is continuous in that line. -/
theorem continuous_vertical_witness_error
    {c d : ℝ} {F : ℝ × ℝ → ℂ} (hF : Continuous F) :
    Continuous fun x0 => ∫ y in Set.Ioc c d,
      Complex.normSq (F (x0, y) - verticalCellAverage c d F x0) := by
  have hC : Continuous (verticalCellAverage c d F) :=
    continuous_verticalCellAverage hF
  let K : ℝ → ℝ → ℝ := fun x0 y =>
    Complex.normSq (F (x0, y) - verticalCellAverage c d F x0)
  have hK : Continuous (Function.uncurry K) := by
    change Continuous fun p : ℝ × ℝ =>
      Complex.normSq (F (p.1, p.2) - verticalCellAverage c d F p.1)
    exact Complex.continuous_normSq.comp
      (hF.sub (hC.comp continuous_fst))
  have hIcc : Continuous (fun x0 => ∫ y in Set.Icc c d, K x0 y) := by
    exact continuous_parametric_integral_of_continuous hK isCompact_Icc
  have hIoc : Continuous (fun x0 => ∫ y in Set.Ioc c d, K x0 y) := by
    simpa only [integral_Icc_eq_integral_Ioc] using hIcc
  simpa only [K] using hIoc

/-- The horizontal two-witness average also bounds the same error with the
witness coordinate outermost, as required by common finite-family selection. -/
theorem horizontal_witness_integral_le
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {F Fx : ℝ × ℝ → ℂ} (hF : Continuous F) (hFx : Continuous Fx)
    (hderiv : ∀ x y : ℝ, HasDerivAt (fun t => F (t, y)) (Fx (x, y)) x) :
    (∫ x0 in Set.Ioc a b, ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
      Complex.normSq (F (x, y) - F (x0, y))) ≤
      4 * (b - a) * ((b - a) ^ 2 * ∫ y in Set.Ioc c d,
        ∫ x in Set.Ioc a b, Complex.normSq (Fx (x, y))) := by
  let W : ℝ → ℝ → ℝ := fun x0 y => ∫ x in Set.Ioc a b,
    Complex.normSq (F (x, y) - F (x0, y))
  have hW : Continuous (Function.uncurry W) := by
    let K : (ℝ × ℝ) → ℝ → ℝ := fun p x =>
      Complex.normSq (F (x, p.2) - F (p.1, p.2))
    have hK : Continuous (Function.uncurry K) := by
      change Continuous fun p : (ℝ × ℝ) × ℝ =>
        Complex.normSq (F (p.2, p.1.2) - F (p.1.1, p.1.2))
      exact Complex.continuous_normSq.comp
        ((hF.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))).sub
          (hF.comp ((continuous_fst.comp continuous_fst).prodMk
            (continuous_snd.comp continuous_fst))))
    have hInner : Continuous fun p : ℝ × ℝ => ∫ x in Set.Ioc a b, K p x := by
      have hIcc : Continuous fun p : ℝ × ℝ => ∫ x in Set.Icc a b, K p x := by
        exact continuous_parametric_integral_of_continuous hK isCompact_Icc
      simpa only [integral_Icc_eq_integral_Ioc] using hIcc
    change Continuous fun p : ℝ × ℝ => ∫ x in Set.Ioc a b, K p x
    exact hInner
  have hsubset : Set.Ioc a b ×ˢ Set.Ioc c d ⊆ Set.Icc a b ×ˢ Set.Icc c d := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨⟨hx.1.le, hx.2⟩, ⟨hy.1.le, hy.2⟩⟩
  have hIcc : IntegrableOn (Function.uncurry W)
      (Set.Icc a b ×ˢ Set.Icc c d) volume :=
    hW.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hWint : Integrable (Function.uncurry W)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc c d))) := by
    have hi : IntegrableOn (Function.uncurry W)
        (Set.Ioc a b ×ˢ Set.Ioc c d) volume := hIcc.mono_set hsubset
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hi
    exact hi
  have hswap : (∫ x0 in Set.Ioc a b, ∫ y in Set.Ioc c d, W x0 y) =
      ∫ y in Set.Ioc c d, ∫ x0 in Set.Ioc a b, W x0 y := by
    exact integral_integral_swap hWint
  have hbase := horizontal_witness_average_iterated_le hab hcd hF hFx hderiv
  calc
    (∫ x0 in Set.Ioc a b, ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
        Complex.normSq (F (x, y) - F (x0, y))) =
        ∫ y in Set.Ioc c d, ∫ x0 in Set.Ioc a b, ∫ x in Set.Ioc a b,
          Complex.normSq (F (x, y) - F (x0, y)) := by
      simpa only [W] using hswap
    _ ≤ 4 * (b - a) * ((b - a) ^ 2 * ∫ y in Set.Ioc c d,
        ∫ x in Set.Ioc a b, Complex.normSq (Fx (x, y))) := hbase

/-- A finite family of complex `C¹` fields has one common vertical witness line
whose componentwise vertical mean gives a simultaneous rectangle approximation. -/
theorem exists_rectangle_witness_line_finset
    {ι : Type*} [Fintype ι] {a b c d : ℝ} (hab : a < b) (hcd : c ≤ d)
    {F Fx Fy : ι → ℝ × ℝ → ℂ}
    (hF : ∀ i, Continuous (F i)) (hFx : ∀ i, Continuous (Fx i))
    (hFy : ∀ i, Continuous (Fy i))
    (hderivX : ∀ i x y, HasDerivAt (fun t => F i (t, y)) (Fx i (x, y)) x)
    (hderivY : ∀ i x y, HasDerivAt (fun t => F i (x, t)) (Fy i (x, y)) y) :
    ∃ x0 ∈ Set.Ioc a b,
      (∑ i, ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
        Complex.normSq (F i (x, y) - verticalCellAverage c d (F i) x0)) ≤
        8 * (b - a) ^ 2 * (∑ i, ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
          Complex.normSq (Fx i (x, y))) +
        2 * (d - c) ^ 2 * (∑ i, ∫ x in Set.Ioc a b, ∫ y in Set.Ioc c d,
          Complex.normSq (Fy i (x, y))) := by
  let E_x : ι → ℝ := fun i => ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
    Complex.normSq (Fx i (x, y))
  let E_y : ι → ℝ := fun i => ∫ x in Set.Ioc a b, ∫ y in Set.Ioc c d,
    Complex.normSq (Fy i (x, y))
  let Q : ι → ℝ → ℝ := fun i x0 => ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
    Complex.normSq (F i (x, y) - verticalCellAverage c d (F i) x0)
  let H : ι → ℝ → ℝ := fun i x0 => ∫ y in Set.Ioc c d, ∫ x in Set.Ioc a b,
    Complex.normSq (F i (x, y) - F i (x0, y))
  let V : ι → ℝ → ℝ := fun i x0 => ∫ y in Set.Ioc c d,
    Complex.normSq (F i (x0, y) - verticalCellAverage c d (F i) x0)
  let A : ℝ := 4 * (b - a) ^ 2 * ∑ i, E_x i
  let B : ℝ := (d - c) ^ 2 * ∑ i, E_y i
  have hQ : ∀ i, Continuous (Q i) := by
    intro i
    dsimp [Q]
    exact continuous_rectangle_error_to_vertical_witness (hF i)
  have hH : ∀ i, Continuous (H i) := by
    intro i
    dsimp [H]
    exact continuous_horizontal_witness_error (hF i)
  have hV : ∀ i, Continuous (V i) := by
    intro i
    dsimp [V]
    exact continuous_vertical_witness_error (hF i)
  have hpoint : ∀ i x0, Q i x0 ≤ 2 * H i x0 + 2 * (b - a) * V i x0 := by
    intro i x0
    dsimp [Q, H, V]
    exact rectangle_error_to_vertical_witness_le hab.le hcd (hF i) x0
  have hHbudget : (∑ i, ∫ x0 in Set.Ioc a b, H i x0) ≤ (b - a) * A := by
    calc
      (∑ i, ∫ x0 in Set.Ioc a b, H i x0) ≤
          ∑ i, 4 * (b - a) * ((b - a) ^ 2 * E_x i) := by
        apply Finset.sum_le_sum
        intro i _
        dsimp [H, E_x]
        exact horizontal_witness_integral_le hab.le hcd (hF i) (hFx i)
          (fun x y => hderivX i x y)
      _ = (b - a) * A := by
        dsimp [A]
        calc
          (∑ i, 4 * (b - a) * ((b - a) ^ 2 * E_x i)) =
              ∑ i, ((b - a) * (4 * (b - a) ^ 2)) * E_x i := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = ((b - a) * (4 * (b - a) ^ 2)) * ∑ i, E_x i := by
            rw [Finset.mul_sum]
          _ = (b - a) * (4 * (b - a) ^ 2 * ∑ i, E_x i) := by ring
  have hVbudget : (∑ i, ∫ x0 in Set.Ioc a b, V i x0) ≤ B := by
    calc
      (∑ i, ∫ x0 in Set.Ioc a b, V i x0) ≤
          ∑ i, (d - c) ^ 2 * E_y i := by
        apply Finset.sum_le_sum
        intro i _
        dsimp [V, E_y]
        exact vertical_cell_mean_iterated_le hab.le hcd (hF i) (hFy i)
          (fun x y => hderivY i x y)
      _ = B := by
        dsimp [B]
        rw [Finset.mul_sum]
  obtain ⟨x0, hx0, hx0bound⟩ := exists_common_witness_of_finite_budget
    (Q := Q) (H := H) (V := V) hab hQ hH hV hpoint hHbudget hVbudget
  refine ⟨x0, hx0, ?_⟩
  change (∑ i, Q i x0) ≤
    8 * (b - a) ^ 2 * (∑ i, E_x i) +
      2 * (d - c) ^ 2 * (∑ i, E_y i)
  calc
    (∑ i, Q i x0) ≤ 2 * A + 2 * B := hx0bound
    _ = 8 * (b - a) ^ 2 * (∑ i, E_x i) +
      2 * (d - c) ^ 2 * (∑ i, E_y i) := by
      dsimp [A, B]
      ring

end GaloisForLFunctions.HTGeometry
