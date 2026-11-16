import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateEquationOnProbes
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ThePairedReflectionPreservesArithmeticEnergy
import GaloisForLFunctions.RHTower.OddWeilFunctionRigidity
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.BoundedWeilEnergyUpgradesL1LimitsToStrongLimits
import GaloisForLFunctions.HTGeometry.RiemannZetaMeromorphic
import GaloisForLFunctions.RHTower.EvenSectorWeightGrowth
import GaloisForLFunctions.HTGeometry.LogWeightedPoisson

/-!
# The state equation is holomorphic in the probe exponent

Each term of the state equation on probes extends holomorphically in the exponent `p`:

* the Laplace transform `L F(p) = ∫ F(u) e^{pu} du` on `Re p > -b/2` whenever
  `∫ F² e^{-bu} < ∞` (AM–GM against the square moment);
* the Gamma pairing `Γ F(p) = (1/2π) ∫ ½(F̂(r)/(p - ir) + conj F̂(r)/(p + ir)) γ(r) dr` on
  `Re p > 0` (the Gamma energy of `F` and the logarithmic growth of `γ` dominate it);
* the prime tail `T F(p) = Σ Λ(n) n^{-½} n^{p} ∫_{u<-log n} F(u) e^{pu} du` on `Re p > 0`
  (the confinement mass bounds each tail by `e^{-4 log n}`).

The Euler factor is replaced by `ζ'/ζ(½ + p)`. The resulting function `stateEquation` agrees with the
real probe equation at real `p > 4`, where it vanishes.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric
open scoped ComplexConjugate

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### The Laplace transform -/

/-- AM–GM against a square moment: `|F| e^{cu} ≤ (F² e^{-bu} + e_{2c+b})/2` on the half-line. -/
theorem abs_mul_exp_le_of_support {F : ℝ → ℝ} (hsupp : ∀ u, 0 ≤ u → F u = 0) (b c u : ℝ) :
    |F u| * Real.exp (c * u) ≤ (F u ^ 2 * Real.exp (-(b * u)) + probe (2 * c + b) u) / 2 := by
  rcases lt_or_ge u 0 with hu | hu
  · rw [probe_of_neg hu]
    set X := |F u| * Real.exp (-(b * u) / 2) with hX
    set Y := Real.exp ((c + b / 2) * u) with hY
    have hXY : |F u| * Real.exp (c * u) = X * Y := by
      rw [hX, hY, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    have hX2 : F u ^ 2 * Real.exp (-(b * u)) = X ^ 2 := by
      have he : Real.exp (-(b * u)) = Real.exp (-(b * u) / 2) * Real.exp (-(b * u) / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [he, hX, mul_pow, sq_abs]
      ring
    have hY2 : Real.exp ((2 * c + b) * u) = Y ^ 2 := by
      rw [hY, sq, ← Real.exp_add]; congr 1; ring
    rw [hXY, hX2, hY2]
    nlinarith [sq_nonneg (X - Y)]
  · rw [hsupp u hu, probe_of_nonneg hu]
    simp

theorem integrable_abs_mul_exp_of_sq {F : ℝ → ℝ} (hFm : Measurable F)
    (hsupp : ∀ u, 0 ≤ u → F u = 0) {b c : ℝ}
    (hb : Integrable fun u => F u ^ 2 * Real.exp (-(b * u))) (hc : 0 < 2 * c + b) :
    Integrable fun u => |F u| * Real.exp (c * u) := by
  refine ((hb.add (integrable_probe hc)).div_const 2).mono'
    ((hFm.abs.mul (by fun_prop : Measurable fun u : ℝ => Real.exp (c * u))).aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact abs_mul_exp_le_of_support hsupp b c u

theorem norm_cexp_mul_ofReal (z : ℂ) (u : ℝ) : ‖cexp (z * u)‖ = Real.exp (z.re * u) := by
  rw [Complex.norm_exp]
  simp

/-- The Laplace transform of a half-line profile with `∫ F² e^{-bu} < ∞` is holomorphic on
`Re p > -b/2`. -/
theorem differentiableOn_laplace_of_sq {F : ℝ → ℝ} (hFm : Measurable F)
    (hsupp : ∀ u, 0 ≤ u → F u = 0) {b : ℝ}
    (hb : Integrable fun u => F u ^ 2 * Real.exp (-(b * u))) :
    DifferentiableOn ℂ (negativeHalfLineLaplace (cx F)) {p : ℂ | -(b / 2) < p.re} := by
  have hU : IsOpen {p : ℂ | -(b / 2) < p.re} := isOpen_lt continuous_const Complex.continuous_re
  refine differentiableOn_integral_of_locally_bounded (ν := volume)
    (F := fun (u : ℝ) (z : ℂ) => cexp (z * u) * cx F u) hU
    (fun u => (by fun_prop : Differentiable ℂ fun z : ℂ => cexp (z * u) * cx F u).differentiableOn)
    (fun z _ => ((by fun_prop : Continuous fun u : ℝ => cexp (z * u)).measurable.mul
      (Complex.measurable_ofReal.comp hFm)).aestronglyMeasurable) ?_
  intro z₀ hz₀
  have hz₀' : -(b / 2) < z₀.re := hz₀
  set r := (z₀.re + b / 2) / 2 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  refine ⟨r, hrpos, fun z hz => ?_, fun u => |F u| * Real.exp ((z₀.re - r) * u),
    integrable_abs_mul_exp_of_sq hFm hsupp hb (by rw [hr]; linarith), fun u z hz => ?_⟩
  · have hd := Complex.abs_re_le_norm (z - z₀)
    rw [mem_closedBall, dist_eq_norm] at hz
    have : |z.re - z₀.re| ≤ r := by simpa using hd.trans hz
    show -(b / 2) < z.re
    rw [hr] at this
    linarith [(abs_le.mp this).1]
  · have hd := Complex.abs_re_le_norm (z - z₀)
    rw [mem_closedBall, dist_eq_norm] at hz
    have hre : z₀.re - r ≤ z.re := by
      have : |z.re - z₀.re| ≤ r := by simpa using hd.trans hz
      linarith [(abs_le.mp this).1]
    rw [norm_mul, norm_cexp_mul_ofReal]
    rcases lt_or_ge u 0 with hu | hu
    · have he : Real.exp (z.re * u) ≤ Real.exp ((z₀.re - r) * u) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hn : ‖cx F u‖ = |F u| := by simp [cx]
      rw [hn, mul_comm]
      exact mul_le_mul_of_nonneg_left he (abs_nonneg _)
    · simp [cx, hsupp u hu]

/-! ### The Gamma pairing -/

/-- The holomorphic Gamma pairing of a profile with the probe of exponent `p`. -/
def stateGamma (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  1 / (2 * Real.pi) * ∫ r : ℝ, (paperFT (cx F) r / (p - I * r) +
    conj (paperFT (cx F) r) / (p + I * r)) / 2 * (EF.gammaBracket r : ℂ)

/-- A complex number with real part at least `c` and imaginary part at least `|r| - M` in
absolute value has norm at least `c/(c+M+1) · (1 + |r|)`. -/
theorem norm_ge_of_re_im {w : ℂ} {c M r : ℝ} (hc : 0 < c) (hM : 0 ≤ M) (hre : c ≤ |w.re|)
    (him : |r| - M ≤ |w.im|) : c / (c + M + 1) * (1 + |r|) ≤ ‖w‖ := by
  have h1 : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
  have h2 : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg hc.le (sub_nonneg.mpr (him.trans h2)),
    mul_nonneg (by linarith : (0 : ℝ) ≤ M + 1) (sub_nonneg.mpr (hre.trans h1))]

/-- `‖a/w‖ ≤ (‖a‖² + K (1+r²)⁻¹)/2` once `‖w‖ ≥ κ (1+|r|)` with `K = κ⁻²`. -/
theorem norm_div_le_of_lower {a w : ℂ} {κ r : ℝ} (hκ : 0 < κ) (hw : κ * (1 + |r|) ≤ ‖w‖) :
    ‖a / w‖ ≤ (‖a‖ ^ 2 + (κ ^ 2)⁻¹ * (1 + r ^ 2)⁻¹) / 2 := by
  have hwpos : 0 < ‖w‖ := lt_of_lt_of_le (by positivity) hw
  have hsq : κ ^ 2 * (1 + r ^ 2) ≤ ‖w‖ ^ 2 := by
    have h1 : κ ^ 2 * (1 + r ^ 2) ≤ (κ * (1 + |r|)) ^ 2 := by
      rw [mul_pow]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg κ)
      nlinarith [abs_nonneg r, sq_abs r]
    exact h1.trans (pow_le_pow_left₀ (by positivity) hw 2)
  have hinv : (‖w‖ ^ 2)⁻¹ ≤ (κ ^ 2)⁻¹ * (1 + r ^ 2)⁻¹ := by
    rw [← mul_inv]
    exact inv_anti₀ (by positivity) hsq
  rw [norm_div]
  have hamgm : ‖a‖ / ‖w‖ ≤ (‖a‖ ^ 2 + (‖w‖ ^ 2)⁻¹) / 2 := by
    have : ‖a‖ / ‖w‖ = ‖a‖ * ‖w‖⁻¹ := div_eq_mul_inv _ _
    rw [this, ← inv_pow]
    nlinarith [sq_nonneg (‖a‖ - ‖w‖⁻¹)]
  linarith

theorem continuous_paperFT_div {F : ℝ → ℝ} (hF : Integrable F) {p : ℂ} (hp : 0 < p.re)
    (s : ℂ) (hs : s = I ∨ s = -I) :
    Continuous fun r : ℝ => paperFT (cx F) r / (p - s * r) := by
  refine (continuous_paperFT_cx hF).div (by fun_prop) fun r h => ?_
  have := congrArg Complex.re h
  rcases hs with rfl | rfl <;> simp at this <;> linarith

/-- The Gamma pairing is holomorphic on `Re p > 0`. -/
theorem differentiableOn_stateGamma {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    DifferentiableOn ℂ (stateGamma F) {p : ℂ | 0 < p.re} := by
  have hU : IsOpen {p : ℂ | 0 < p.re} := isOpen_lt continuous_const Complex.continuous_re
  have hne : ∀ p : ℂ, 0 < p.re → ∀ r : ℝ, p - I * r ≠ 0 ∧ p + I * r ≠ 0 := by
    intro p hp r
    constructor <;> intro h <;> have := congrArg Complex.re h <;> simp at this <;> linarith
  refine DifferentiableOn.const_mul ?_ _
  refine differentiableOn_integral_of_locally_bounded (ν := volume)
    (F := fun (r : ℝ) (p : ℂ) => (paperFT (cx F) r / (p - I * r) +
      conj (paperFT (cx F) r) / (p + I * r)) / 2 * (EF.gammaBracket r : ℂ)) hU ?_ ?_ ?_
  · intro r p hp
    have h := hne p hp r
    refine DifferentiableAt.differentiableWithinAt ?_
    exact ((((differentiableAt_const _).div (differentiableAt_id.sub_const _) h.1).add
      ((differentiableAt_const _).div (differentiableAt_id.add_const _) h.2)).div_const _).mul_const _
  · intro p hp
    have h1 := continuous_paperFT_div hF.integrable hp I (Or.inl rfl)
    have h2 : Continuous fun r : ℝ => conj (paperFT (cx F) r) / (p + I * r) := by
      refine (Complex.continuous_conj.comp (continuous_paperFT_cx hF.integrable)).div
        (by fun_prop) fun r => (hne p hp r).2
    exact (((h1.add h2).div_const _).mul
      (Complex.continuous_ofReal.comp WeilHerglotz.continuous_gammaBracket)).aestronglyMeasurable
  · intro z₀ hz₀
    have hz₀' : 0 < z₀.re := hz₀
    set c := z₀.re / 2 with hc
    set M := |z₀.im| + c with hMdef
    have hcpos : 0 < c := by rw [hc]; linarith
    have hM : 0 ≤ M := by rw [hMdef]; positivity
    set κ := c / (c + M + 1) with hκ
    have hκpos : 0 < κ := by rw [hκ]; positivity
    refine ⟨c, hcpos, fun z hz => ?_, fun r => |EF.gammaBracket r| *
      ((‖paperFT (cx F) r‖ ^ 2 + (κ ^ 2)⁻¹ * (1 + r ^ 2)⁻¹) / 2), ?_, fun r z hz => ?_⟩
    · rw [mem_closedBall, dist_eq_norm] at hz
      have := (abs_le.mp ((Complex.abs_re_le_norm (z - z₀)).trans hz)).1
      show 0 < z.re
      simp at this
      linarith
    · have hA : Integrable fun r : ℝ => |EF.gammaBracket r| * ‖paperFT (cx F) r‖ ^ 2 :=
        hF.gamma.norm.congr (Eventually.of_forall fun r => by
          simp only [norm_mul, norm_pow, norm_norm, Real.norm_eq_abs]; ring)
      have hB : Integrable fun r : ℝ => |EF.gammaBracket r| * (1 + r ^ 2)⁻¹ := by
        have i1 := (integrable_inv_one_add_sq).const_mul |EvenSector.gammaLogConst|
        have i2 := HTGeometry.integrable_log_mul_inv_sq_add_sq (a := 1) one_pos
        refine (i1.add i2).mono'
          ((Continuous.mul (continuous_abs.comp WeilHerglotz.continuous_gammaBracket)
            (by fun_prop : Continuous fun r : ℝ => (1 + r ^ 2)⁻¹)).aestronglyMeasurable)
          (Eventually.of_forall fun r => ?_)
        have hg := EvenSector.abs_gammaBracket_le_log r
        have hl : 0 ≤ Real.log (2 + |r|) := Real.log_nonneg (by linarith [abs_nonneg r])
        have hi : 0 < (1 + r ^ 2)⁻¹ := by positivity
        rw [Real.norm_of_nonneg (by positivity), one_pow]
        simp only [Pi.add_apply]
        nlinarith [le_abs_self EvenSector.gammaLogConst]
      refine ((hA.add (hB.const_mul (κ ^ 2)⁻¹)).div_const 2).congr
        (Eventually.of_forall fun r => ?_)
      simp only [Pi.add_apply]
      ring
    · rw [mem_closedBall, dist_eq_norm] at hz
      have hre := (abs_le.mp ((Complex.abs_re_le_norm (z - z₀)).trans hz)).1
      have him := (abs_le.mp ((Complex.abs_im_le_norm (z - z₀)).trans hz))
      simp only [Complex.sub_re, Complex.sub_im] at hre him
      have hzre : c ≤ z.re := by rw [hc] at hre ⊢; linarith
      have hzim : |z.im| ≤ M := by
        rw [hMdef, abs_le]; constructor <;> linarith [neg_abs_le z₀.im, le_abs_self z₀.im]
      have hlow : ∀ s : ℝ, s = 1 ∨ s = -1 → κ * (1 + |r|) ≤ ‖z + (s : ℂ) * I * r‖ := by
        intro s hs
        apply norm_ge_of_re_im hcpos hM
        · rcases hs with rfl | rfl <;> simp <;> rw [abs_of_pos (by linarith)] <;> linarith
        · rcases hs with rfl | rfl <;> simp
          · have := abs_sub_abs_le_abs_sub r (-z.im); simp at this
            rw [abs_add_comm] at *; linarith [abs_add_le z.im r, abs_sub_abs_le_abs_sub r (-z.im)]
          · linarith [abs_sub_abs_le_abs_sub r z.im, abs_sub_comm z.im r]
      have h1 : κ * (1 + |r|) ≤ ‖z - I * r‖ := by
        have := hlow (-1) (Or.inr rfl); simpa [sub_eq_add_neg, mul_comm, mul_left_comm] using this
      have h2 : κ * (1 + |r|) ≤ ‖z + I * r‖ := by
        have := hlow 1 (Or.inl rfl); simpa [mul_comm, mul_left_comm] using this
      have b1 := norm_div_le_of_lower (a := paperFT (cx F) r) hκpos h1
      have b2 := norm_div_le_of_lower (a := conj (paperFT (cx F) r)) hκpos h2
      rw [Complex.norm_conj] at b2
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [norm_div, Complex.norm_two]
      have := norm_add_le (paperFT (cx F) r / (z - I * r)) (conj (paperFT (cx F) r) / (z + I * r))
      linarith

/-! ### The prime tail -/

/-- The holomorphic prime tail of a profile at the probe exponent `p`. -/
def stateTail (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  ∑' n : ℕ, (vonMangoldtAtom n : ℂ) *
    (cexp (p * Real.log n) * ∫ u in Iio (-Real.log n), (F u : ℂ) * cexp (p * u))

/-- The confinement mass bounds the mass of a profile beyond `-L`. -/
theorem setIntegral_abs_le_confinement {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {L : ℝ}
    (hL : 0 ≤ L) :
    (∫ u in Iio (-L), |F u|) ≤
      Real.exp (-(4 * L)) * ((∫ u, F u ^ 2 * Real.exp (-(8 * u))) + 1 / 8) / 2 := by
  have hW := hF.exponential
  have hE : IntegrableOn (fun u : ℝ => Real.exp (4 * L) * Real.exp (8 * u)) (Iio (-L)) :=
    ((integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 8) (-L)).mono_set
      Iio_subset_Iic_self).const_mul _
  have hpt : ∀ u ∈ Iio (-L), |F u| ≤ (Real.exp (-(4 * L)) * (F u ^ 2 * Real.exp (-(8 * u))) +
      Real.exp (4 * L) * Real.exp (8 * u)) / 2 := by
    intro u _
    set X := Real.exp (-(2 * L)) * |F u| * Real.exp (-(4 * u))
    set Y := Real.exp (2 * L) * Real.exp (4 * u)
    have hXY : |F u| = X * Y := by
      simp only [X, Y]
      have : Real.exp (-(2 * L)) * Real.exp (2 * L) * (Real.exp (-(4 * u)) * Real.exp (4 * u)) = 1 := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; simp
      nlinarith [this]
    have hX2 : Real.exp (-(4 * L)) * (F u ^ 2 * Real.exp (-(8 * u))) = X ^ 2 := by
      simp only [X, mul_pow, sq_abs, ← Real.exp_nat_mul]; ring_nf
    have hY2 : Real.exp (4 * L) * Real.exp (8 * u) = Y ^ 2 := by
      simp only [Y, mul_pow, ← Real.exp_nat_mul]; ring_nf
    rw [hXY, hX2, hY2]
    nlinarith [sq_nonneg (X - Y)]
  have hint : IntegrableOn (fun u => (Real.exp (-(4 * L)) * (F u ^ 2 * Real.exp (-(8 * u))) +
      Real.exp (4 * L) * Real.exp (8 * u)) / 2) (Iio (-L)) :=
    ((hW.integrableOn.const_mul _).add hE).div_const 2
  have habs : IntegrableOn (fun u => |F u|) (Iio (-L)) := hF.integrable.abs.integrableOn
  calc (∫ u in Iio (-L), |F u|)
      ≤ ∫ u in Iio (-L), (Real.exp (-(4 * L)) * (F u ^ 2 * Real.exp (-(8 * u))) +
          Real.exp (4 * L) * Real.exp (8 * u)) / 2 :=
        setIntegral_mono_on habs hint measurableSet_Iio hpt
    _ = (Real.exp (-(4 * L)) * (∫ u in Iio (-L), F u ^ 2 * Real.exp (-(8 * u))) +
          Real.exp (4 * L) * (Real.exp (8 * (-L)) / 8)) / 2 := by
        rw [integral_div, integral_add (hW.integrableOn.const_mul _) hE, integral_const_mul,
          integral_const_mul, ← integral_Iic_eq_integral_Iio, integral_exp_mul_Iic (by norm_num)]
    _ ≤ Real.exp (-(4 * L)) * ((∫ u, F u ^ 2 * Real.exp (-(8 * u))) + 1 / 8) / 2 := by
        have hle : (∫ u in Iio (-L), F u ^ 2 * Real.exp (-(8 * u))) ≤
            ∫ u, F u ^ 2 * Real.exp (-(8 * u)) :=
          setIntegral_le_integral hW (Eventually.of_forall fun u => by positivity)
        have he : Real.exp (4 * L) * (Real.exp (8 * (-L)) / 8) = Real.exp (-(4 * L)) / 8 := by
          rw [mul_div_assoc', ← Real.exp_add]; congr 2; ring
        rw [he]
        have := mul_le_mul_of_nonneg_left hle (Real.exp_pos (-(4 * L))).le
        linarith

/-- One term of the prime tail is bounded uniformly on `Re p ≥ 0`. -/
theorem norm_stateTail_term_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : 0 ≤ p.re) (n : ℕ) :
    ‖(vonMangoldtAtom n : ℂ) * (cexp (p * Real.log n) *
        ∫ u in Iio (-Real.log n), (F u : ℂ) * cexp (p * u))‖ ≤
      vonMangoldtAtom n * (Real.exp (-(4 * Real.log n)) *
        (((∫ u, F u ^ 2 * Real.exp (-(8 * u))) + 1 / 8) / 2)) := by
  set L := Real.log n with hLdef
  have hL : 0 ≤ L := Real.log_natCast_nonneg n
  have hatom : 0 ≤ vonMangoldtAtom n := by
    unfold vonMangoldtAtom; split_ifs
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    · exact le_rfl
  have hint : ‖∫ u in Iio (-L), (F u : ℂ) * cexp (p * u)‖ ≤
      Real.exp (-(p.re * L)) * ∫ u in Iio (-L), |F u| := by
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (hF.integrable.abs.integrableOn.const_mul _) ?_
    refine (ae_restrict_iff' measurableSet_Iio).mpr (Eventually.of_forall fun u hu => ?_)
    rw [norm_mul, norm_cexp_mul_ofReal, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by
      have : u < -L := hu; nlinarith)) (abs_nonneg _)
  have hexp : ‖cexp (p * L)‖ = Real.exp (p.re * L) := norm_cexp_mul_ofReal p L
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hatom, hexp]
  refine mul_le_mul_of_nonneg_left ?_ hatom
  calc Real.exp (p.re * L) * ‖∫ u in Iio (-L), (F u : ℂ) * cexp (p * u)‖
      ≤ Real.exp (p.re * L) * (Real.exp (-(p.re * L)) * ∫ u in Iio (-L), |F u|) :=
        mul_le_mul_of_nonneg_left hint (Real.exp_pos _).le
    _ = ∫ u in Iio (-L), |F u| := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    _ ≤ _ := setIntegral_abs_le_confinement hF hL

/-- The prime tail is holomorphic on `Re p > 0`. -/
theorem differentiableOn_stateTail {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    DifferentiableOn ℂ (stateTail F) {p : ℂ | 0 < p.re} := by
  have hU : IsOpen {p : ℂ | 0 < p.re} := isOpen_lt continuous_const Complex.continuous_re
  have hsum : Summable fun n : ℕ => vonMangoldtAtom n * (Real.exp (-(4 * Real.log n)) *
      (((∫ u, F u ^ 2 * Real.exp (-(8 * u))) + 1 / 8) / 2)) := by
    have h := (summable_vonMangoldt_div_rpow (σ := 1 / 2 + 4) (by norm_num)).mul_right
      (((∫ u, F u ^ 2 * Real.exp (-(8 * u))) + 1 / 8) / 2)
    refine h.congr fun n => ?_
    rw [← vonMangoldtAtom_mul_exp_eq]
    ring
  refine Complex.differentiableOn_tsum_of_summable_norm hsum (fun n => ?_) hU
    (fun n p hp => norm_stateTail_term_le hF (le_of_lt hp) n)
  refine DifferentiableOn.const_mul (DifferentiableOn.mul
    (by fun_prop : Differentiable ℂ fun p : ℂ => cexp (p * Real.log n)).differentiableOn ?_) _
  refine differentiableOn_integral_of_locally_bounded (ν := volume.restrict (Iio (-Real.log n)))
    (F := fun (u : ℝ) (p : ℂ) => (F u : ℂ) * cexp (p * u)) hU
    (fun u => (by fun_prop : Differentiable ℂ fun p : ℂ => (F u : ℂ) * cexp (p * u)).differentiableOn)
    (fun p _ => ((Complex.measurable_ofReal.comp hF.meas).mul
      (by fun_prop : Continuous fun u : ℝ => cexp (p * u)).measurable).aestronglyMeasurable) ?_
  intro z₀ hz₀
  have hz₀' : 0 < z₀.re := hz₀
  refine ⟨z₀.re / 2, by linarith, fun z hz => ?_, fun u => |F u|,
    hF.integrable.abs.integrableOn, fun u z hz => ?_⟩
  · rw [mem_closedBall, dist_eq_norm] at hz
    have := (abs_le.mp ((Complex.abs_re_le_norm (z - z₀)).trans hz)).1
    show 0 < z.re
    simp at this
    linarith
  · rw [mem_closedBall, dist_eq_norm] at hz
    have hre := (abs_le.mp ((Complex.abs_re_le_norm (z - z₀)).trans hz)).1
    simp only [Complex.sub_re] at hre
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cexp_mul_ofReal]
    rcases lt_or_ge u 0 with hu | hu
    · have : Real.exp (z.re * u) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      nlinarith [abs_nonneg (F u)]
    · simp [hF.support u hu]

/-! ### The extended state equation -/

/-- The state equation on probes, extended holomorphically in the exponent `p`. -/
def stateEquation (W₀ : ℝ) (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  criticalAliasCoefficient W₀ * negativeHalfLineLaplace (cx F) (p - 8) + stateGamma F p +
    negativeHalfLineLaplace (cx F) p * (deriv riemannZeta (1 / 2 + p) / riemannZeta (1 / 2 + p)) -
    stateTail F p +
    (coshHalfMoment F * (1 / (p + 1 / 2) + 1 / (p - 1 / 2)) -
      sinhHalfMoment F * (1 / (p + 1 / 2) - 1 / (p - 1 / 2)))

theorem stateGamma_ofReal (F : ℝ → ℝ) (p : ℝ) :
    stateGamma F p = ((1 / (2 * Real.pi) *
      ∫ r : ℝ, (paperFT (cx F) (r : ℂ) / ((p : ℂ) - I * r)).re * EF.gammaBracket r : ℝ) : ℂ) := by
  unfold stateGamma
  have hpt : ∀ r : ℝ, (paperFT (cx F) r / ((p : ℂ) - I * r) +
      conj (paperFT (cx F) r) / ((p : ℂ) + I * r)) / 2 * (EF.gammaBracket r : ℂ) =
      (((paperFT (cx F) (r : ℂ) / ((p : ℂ) - I * r)).re * EF.gammaBracket r : ℝ) : ℂ) := by
    intro r
    have hc : conj (paperFT (cx F) r) / ((p : ℂ) + I * r) =
        conj (paperFT (cx F) r / ((p : ℂ) - I * r)) := by
      rw [map_div₀]
      congr 1
      simp [Complex.conj_ofReal]
    rw [hc, Complex.add_conj]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_ofReal]
  push_cast
  ring

theorem stateTail_ofReal (F : ℝ → ℝ) (p : ℝ) : stateTail F p = (primeTail F p : ℂ) := by
  unfold stateTail primeTail
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  have hi : (∫ u in Iio (-Real.log n), (F u : ℂ) * cexp ((p : ℂ) * u)) =
      ((∫ u in Iio (-Real.log n), F u * Real.exp (p * u) : ℝ) : ℂ) := by
    rw [← integral_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    push_cast
    rfl
  rw [hi]
  push_cast
  rfl

/-- At real `p > 4` the extended state equation is the real one, so it vanishes. -/
theorem stateEquation_ofReal_eq_zero {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {p : ℝ} (hp : 4 < p) :
    stateEquation W₀ F p = 0 := by
  have he := criticalState_probeEquation hW hthreshold hF hp
  have hs : (1 : ℂ) / 2 + p = ((1 / 2 + p : ℝ) : ℂ) := by push_cast; ring
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := (1 : ℂ) / 2 + p) (by rw [hs, Complex.ofReal_re]; linarith)
  have hζ : deriv riemannZeta (1 / 2 + p) / riemannZeta (1 / 2 + p) =
      -((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (1 / 2 + p) : ℝ) : ℂ) := by
    rw [← LSeries_vonMangoldt_ofReal, ← hs, hL, neg_div, neg_neg]
  have h8 : (p : ℂ) - 8 = ((p - 8 : ℝ) : ℂ) := by push_cast; ring
  unfold stateEquation
  rw [hζ, h8, negativeHalfLineLaplace_ofReal, negativeHalfLineLaplace_ofReal, stateGamma_ofReal,
    stateTail_ofReal]
  have hc : (((0 : ℝ)) : ℂ) = 0 := by simp
  rw [← hc, ← he]
  push_cast
  ring

end GaloisForLFunctions.ExclusionOfTheCriticalState
