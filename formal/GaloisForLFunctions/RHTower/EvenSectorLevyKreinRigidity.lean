import GaloisForLFunctions.RHTower.WeilArchimedeanExactForm
import GaloisForLFunctions.RHTower.EvenSectorSmoothSourceScalarization
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# Pole-free EWU Lévy formula and L² autocorrelation increments

The translation-energy identity and Cauchy–Schwarz require only L² membership.
In particular, dyadic deficit bounds require no spectral second moment.
-/

open MeasureTheory Set Filter Topology Complex
open Zeta23
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.AutocorrelationKrein

open ArchimedeanAnomaly ArchimedeanExactForm

variable {f : ℝ → ℝ}

theorem memLp_shift (hf : MemLp f 2 volume) (x : ℝ) :
    MemLp (fun u => f (u + x)) 2 volume :=
  hf.comp_measurePreserving (measurePreserving_add_right volume x)

theorem integrable_mul_shift (hf : MemLp f 2 volume) (x : ℝ) :
    Integrable (fun u => f u * f (u + x)) :=
  integrable_mul_of_sq_integrable hf.1 (memLp_shift hf x).1
    hf.integrable_sq (memLp_shift hf x).integrable_sq

theorem autocorr_zero_eq (f : ℝ → ℝ) : autocorr f 0 = ∫ u, f u ^ 2 := by
  simp only [autocorr, add_zero, pow_two]

/-- Translation energy for arbitrary real L² sources. -/
theorem integral_sub_shift_sq (hf : MemLp f 2 volume) (x : ℝ) :
    (∫ u, (f u - f (u + x)) ^ 2) = 2 * (autocorr f 0 - autocorr f x) := by
  have he : (fun u => (f u - f (u + x)) ^ 2) =
      fun u => (f u ^ 2 + f (u + x) ^ 2) - 2 * (f u * f (u + x)) := by
    funext u; ring
  have hs : (∫ u, (f u ^ 2 + f (u + x) ^ 2) - 2 * (f u * f (u + x))) =
      (∫ u, f u ^ 2 + f (u + x) ^ 2) - ∫ u, 2 * (f u * f (u + x)) :=
    integral_sub (hf.integrable_sq.add (memLp_shift hf x).integrable_sq)
      ((integrable_mul_shift hf x).const_mul 2)
  have ha : (∫ u, f u ^ 2 + f (u + x) ^ 2) =
      (∫ u, f u ^ 2) + ∫ u, f (u + x) ^ 2 :=
    integral_add hf.integrable_sq (memLp_shift hf x).integrable_sq
  rw [he, hs, ha, integral_const_mul,
    integral_add_right_eq_self (μ := volume) (fun u : ℝ => f u ^ 2) x,
    autocorr_zero_eq, autocorr]
  ring

theorem deficit_nonneg (hf : MemLp f 2 volume) (x : ℝ) :
    0 ≤ autocorr f 0 - autocorr f x := by
  have h : 0 ≤ ∫ u : ℝ, (f u - f (u + x)) ^ 2 := integral_nonneg fun u => sq_nonneg _
  rw [integral_sub_shift_sq hf x] at h
  linarith

theorem integral_shift_sub_shift_sq (hf : MemLp f 2 volume) (x y : ℝ) :
    (∫ u, (f (u + x) - f (u + y)) ^ 2) =
      2 * (autocorr f 0 - autocorr f (x - y)) := by
  calc
    _ = ∫ u, (f (u + y) - f (u + y + (x - y))) ^ 2 := by
      congr 1; funext u
      rw [show u + y + (x - y) = u + x by ring]
      ring
    _ = ∫ u, (f u - f (u + (x - y))) ^ 2 :=
      integral_add_right_eq_self (μ := volume) (fun u : ℝ => (f u - f (u + (x - y))) ^ 2) y
    _ = _ := integral_sub_shift_sq hf _

/-- Krein's increment inequality, with no regularity or moment premise. -/
theorem increment_sq_le (hf : MemLp f 2 volume) (x y : ℝ) :
    |autocorr f x - autocorr f y| ^ 2 ≤
      2 * autocorr f 0 * (autocorr f 0 - autocorr f (x - y)) := by
  have hd := (memLp_shift hf x).sub (memLp_shift hf y)
  have h := sq_integral_mul_le hf.1 hd.1 hf.integrable_sq hd.integrable_sq
  have he : (∫ u, f u * (f (u + x) - f (u + y))) =
      autocorr f x - autocorr f y := by
    simp_rw [mul_sub]
    exact integral_sub (integrable_mul_shift hf x) (integrable_mul_shift hf y)
  change (∫ u, f u * (f (u + x) - f (u + y))) ^ 2 ≤
    (∫ u, f u ^ 2) * ∫ u, (f (u + x) - f (u + y)) ^ 2 at h
  rw [he, integral_shift_sub_shift_sq hf, ← autocorr_zero_eq] at h
  rw [sq_abs]
  nlinarith [h]

/-- Splitting a translation controls its deficit at every pair of summands. -/
theorem deficit_add_le (hf : MemLp f 2 volume) (x y : ℝ) :
    autocorr f 0 - autocorr f (x + y) ≤
      2 * (autocorr f 0 - autocorr f x) + 2 * (autocorr f 0 - autocorr f y) := by
  have h := integral_mono ((hf.sub (memLp_shift hf (x + y))).integrable_sq)
    ((((hf.sub (memLp_shift hf x)).integrable_sq).const_mul 2).add
      ((((memLp_shift hf x).sub (memLp_shift hf (x + y))).integrable_sq).const_mul 2))
    (fun u => show (f u - f (u + (x + y))) ^ 2 ≤
      2 * (f u - f (u + x)) ^ 2 + 2 * (f (u + x) - f (u + (x + y))) ^ 2 by
        nlinarith [sq_nonneg (f u - 2 * f (u + x) + f (u + (x + y)))])
  have ha : (∫ u, 2 * (f u - f (u + x)) ^ 2 +
      2 * (f (u + x) - f (u + (x + y))) ^ 2) =
      (∫ u, 2 * (f u - f (u + x)) ^ 2) +
        ∫ u, 2 * (f (u + x) - f (u + (x + y))) ^ 2 :=
    integral_add (((hf.sub (memLp_shift hf x)).integrable_sq).const_mul 2)
      ((((memLp_shift hf x).sub (memLp_shift hf (x + y))).integrable_sq).const_mul 2)
  change (∫ u, (f u - f (u + (x + y))) ^ 2) ≤
    ∫ u, 2 * (f u - f (u + x)) ^ 2 + 2 * (f (u + x) - f (u + (x + y))) ^ 2 at h
  rw [ha,
    integral_const_mul, integral_const_mul, integral_sub_shift_sq hf,
    integral_sub_shift_sq hf, integral_shift_sub_shift_sq hf,
    show x - (x + y) = -y by ring, autocorr_neg] at h
  linarith

/-- Doubling costs at most four times the translation deficit. -/
theorem deficit_double_le (hf : MemLp f 2 volume) (x : ℝ) :
    autocorr f 0 - autocorr f (2 * x) ≤ 4 * (autocorr f 0 - autocorr f x) := by
  have h := deficit_add_le hf x x
  rw [← two_mul] at h
  linarith

/-- The valid bound between dyadic points couples complementary shifts. -/
theorem complementary_deficit_lower_bound (g : Lp ℝ 2 (volume : Measure ℝ)) (L x : ℝ) :
    (autocorr g 0 - autocorr g L) / 2 ≤
      (autocorr g 0 - autocorr g x) + (autocorr g 0 - autocorr g (L - x)) := by
  have h := deficit_add_le (Lp.memLp g) x (L - x)
  rw [add_sub_cancel] at h
  linarith

/-- A bound at every dyadic submultiple, before imposing any blindness condition. -/
theorem deficit_dyadic_le (hf : MemLp f 2 volume) (L : ℝ) (m : ℕ) :
    autocorr f 0 - autocorr f L ≤
      (4 : ℝ) ^ m * (autocorr f 0 - autocorr f (L / (2 : ℝ) ^ m)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hd := deficit_double_le hf (L / (2 : ℝ) ^ (m + 1))
    have he : 2 * (L / (2 : ℝ) ^ (m + 1)) = L / (2 : ℝ) ^ m := by
      rw [pow_succ]; field_simp
    rw [he] at hd
    calc
      _ ≤ (4 : ℝ) ^ m * (autocorr f 0 - autocorr f (L / (2 : ℝ) ^ m)) := ih
      _ ≤ (4 : ℝ) ^ m * (4 * (autocorr f 0 - autocorr f (L / (2 : ℝ) ^ (m + 1)))) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
      _ = _ := by rw [pow_succ]; ring

/-- Unconditional L² formulation of the requested increment inequality. -/
theorem lp_increment_sq_le (g : Lp ℝ 2 (volume : Measure ℝ)) (x y : ℝ) :
    |autocorr g x - autocorr g y| ^ 2 ≤
      2 * autocorr g 0 * (autocorr g 0 - autocorr g (x - y)) :=
  increment_sq_le (Lp.memLp g) x y

/-- Identifies the real L² autocorrelation with the literal corpus Weil test. -/
theorem weilTest_eq (f : ℝ → ℝ) (x : ℝ) :
    EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) x = (autocorr f x : ℂ) := by
  have h := autocorr_eq_weilTest f (-x)
  simpa only [autocorr_neg, neg_neg] using h.symm

theorem weilTest_increment_sq_le (g : Lp ℝ 2 (volume : Measure ℝ)) (x y : ℝ) :
    ‖EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) x -
      EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) y‖ ^ 2 ≤
      2 * (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) 0).re *
        ((EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) 0).re -
          (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) (x - y)).re) := by
  simpa only [weilTest_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Complex.ofReal_re] using lp_increment_sq_le g x y

/-- Prime-2 blindness alone forces the dyadic lower bound. -/
theorem prime_two_dyadic_lower_bound (g : Lp ℝ 2 (volume : Measure ℝ))
    (hblind : autocorr g (Real.log 2) = 0) (m : ℕ) :
    (1 / (4 : ℝ) ^ m) * autocorr g 0 ≤
      autocorr g 0 - autocorr g (Real.log 2 / (2 : ℝ) ^ m) := by
  have h := deficit_dyadic_le (Lp.memLp g) (Real.log 2) m
  rw [hblind, sub_zero] at h
  rw [one_div, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
  simpa [mul_comm] using h

end RHTower.AutocorrelationKrein

namespace RHTower.EvenSector

open ArchimedeanAnomaly ArchimedeanExactForm

/-- The real-valued part of the existing EWU test domain. -/
def RealEvenPolarTestFn := {g : WeilEvenPolarTestFn // ∀ u, (g.1.1 u).im = 0}

namespace RealEvenPolarTestFn

def source (g : RealEvenPolarTestFn) (u : ℝ) : ℝ := (g.1.1.1 u).re

theorem source_eq (g : RealEvenPolarTestFn) :
    (fun u => (g.source u : ℂ)) = g.1.1.1 := by
  funext u
  apply Complex.ext
  · rfl
  · simpa using (g.2 u).symm

theorem contDiff_source (g : RealEvenPolarTestFn) : ContDiff ℝ 2 g.source :=
  Complex.reCLM.contDiff.comp g.1.1.2.1

theorem hasCompactSupport_source (g : RealEvenPolarTestFn) : HasCompactSupport g.source :=
  g.1.1.2.2.comp_left Complex.zero_re

theorem memLp_source (g : RealEvenPolarTestFn) : MemLp g.source 2 volume :=
  g.contDiff_source.continuous.memLp_of_hasCompactSupport g.hasCompactSupport_source

theorem autocorr_eq (g : RealEvenPolarTestFn) (x : ℝ) :
    autocorr g.source x = (EF.weilTest g.1.1.1 g.1.1.1 x).re := by
  have h := congrArg Complex.re (autocorr_eq_weilTest g.source (-x))
  simpa only [autocorr_neg, neg_neg, source_eq, Complex.ofReal_re] using h

/-- The actual Lévy integrand, with the exact sinh normalization. -/
def levyIntegrand (g : RealEvenPolarTestFn) (x : ℝ) : ℝ :=
  (autocorr g.source 0 - autocorr g.source x) * (Real.exp (x / 2) / Real.sinh x)

theorem levyIntegrand_nonneg (g : RealEvenPolarTestFn) (x : Set.Ioi (0 : ℝ)) :
    0 ≤ g.levyIntegrand x :=
  mul_nonneg (AutocorrelationKrein.deficit_nonneg g.memLp_source x)
    (div_nonneg (Real.exp_pos _).le (Real.sinh_pos_iff.mpr x.2).le)

/-- Finiteness is proved separately from the totalized Bochner integral identity. -/
theorem integrableOn_levyIntegrand (g : RealEvenPolarTestFn) :
    IntegrableOn g.levyIntegrand (Ioi 0) := by
  have hmeas : AEStronglyMeasurable g.levyIntegrand (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    exact (continuousOn_const.sub
      (continuous_autocorr g.contDiff_source g.hasCompactSupport_source).continuousOn).mul
        ((Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn.div
          Real.continuous_sinh.continuousOn
          (fun x hx => (Real.sinh_pos_iff.mpr hx).ne'))
  have he : (∫⁻ x in Ioi 0, ENNReal.ofReal
      (archLevyDensity x * ∫ u, (g.source u - g.source (u + x)) ^ 2)) =
      ∫⁻ x in Ioi 0, ENNReal.ofReal (g.levyIntegrand x) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only [levyIntegrand]
    rw [AutocorrelationKrein.integral_sub_shift_sq g.memLp_source,
      exp_half_div_sinh_eq hx]
    congr 1
    ring
  have hfin := WeilMarkovPole.lintegral_levy_ne_top g.contDiff_source g.hasCompactSupport_source
  rw [he] at hfin
  refine ⟨hmeas, ?_⟩
  rw [HasFiniteIntegral]
  refine lt_of_le_of_lt (le_of_eq ?_) hfin.lt_top
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro x hx
  exact Real.enorm_eq_ofReal (g.levyIntegrand_nonneg ⟨x, hx⟩)

/-- EWU's polar condition cancels the full cosh pole moment exactly. -/
theorem poleMoment_eq_zero (g : RealEvenPolarTestFn) :
    (∫ u, g.source u * Real.cosh (u / 2)) ^ 2 -
      (∫ u, g.source u * Real.sinh (u / 2)) ^ 2 = 0 := by
  have hp := g.1.2.2
  rw [← g.source_eq, WeilLevyPole.paperFT_ofReal_I_div_two] at hp
  have hz : (∫ u, g.source u * Real.exp (-u / 2)) = 0 := by
    exact_mod_cast hp
  rw [← integral_prod_cosh_eq_sq g.hasCompactSupport_source g.contDiff_source.continuous,
    WeilLevyPole.integral_prod_cosh_eq g.hasCompactSupport_source g.contDiff_source.continuous,
    hz, mul_zero]

/-- Exact pole-eliminated Lévy–sinh formula on every real EWU test. -/
theorem weilArchRe_eq_levy (g : RealEvenPolarTestFn) :
    WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) =
      EF.gammaBracket 0 * (EF.weilTest g.1.1.1 g.1.1.1 0).re +
        ∫ x in Ioi 0, ((EF.weilTest g.1.1.1 g.1.1.1 0).re -
          (EF.weilTest g.1.1.1 g.1.1.1 x).re) * (Real.exp (x / 2) / Real.sinh x) := by
  have h := weilArchRe_eq_autocorrelation_form g.contDiff_source g.hasCompactSupport_source
  rw [g.source_eq, g.poleMoment_eq_zero, mul_zero, zero_add] at h
  have he := integral_eq_lintegral_of_nonneg_ae
    ((ae_restrict_mem measurableSet_Ioi).mono (fun x hx => g.levyIntegrand_nonneg ⟨x, hx⟩))
    g.integrableOn_levyIntegrand.aestronglyMeasurable
  change (∫ x in Ioi 0, g.levyIntegrand x) = _ at he
  change _ = _ + (∫⁻ x in Ioi 0, ENNReal.ofReal (g.levyIntegrand x)).toReal at h
  rw [← he] at h
  simpa only [levyIntegrand, g.autocorr_eq] using h

theorem weilArchRe_integrand_nonneg (g : RealEvenPolarTestFn) (x : Set.Ioi (0 : ℝ)) :
    0 ≤ ((EF.weilTest g.1.1.1 g.1.1.1 0).re - (EF.weilTest g.1.1.1 g.1.1.1 x).re) *
      (Real.exp (x / 2) / Real.sinh x) := by
  simpa only [levyIntegrand, g.autocorr_eq] using g.levyIntegrand_nonneg x

theorem krein_increment (g : RealEvenPolarTestFn) (x y : ℝ) :
    |(EF.weilTest g.1.1.1 g.1.1.1 x).re - (EF.weilTest g.1.1.1 g.1.1.1 y).re| ^ 2 ≤
      2 * (EF.weilTest g.1.1.1 g.1.1.1 0).re *
        ((EF.weilTest g.1.1.1 g.1.1.1 0).re - (EF.weilTest g.1.1.1 g.1.1.1 (x - y)).re) := by
  simpa only [g.autocorr_eq] using AutocorrelationKrein.increment_sq_le g.memLp_source x y

theorem dyadic_deficit (g : RealEvenPolarTestFn) (L : ℝ) (m : ℕ) :
    (EF.weilTest g.1.1.1 g.1.1.1 0).re - (EF.weilTest g.1.1.1 g.1.1.1 L).re ≤
      (4 : ℝ) ^ m * ((EF.weilTest g.1.1.1 g.1.1.1 0).re -
        (EF.weilTest g.1.1.1 g.1.1.1 (L / (2 : ℝ) ^ m)).re) := by
  simpa only [g.autocorr_eq] using AutocorrelationKrein.deficit_dyadic_le g.memLp_source L m

theorem prime_two_dyadic_lower_bound (g : RealEvenPolarTestFn)
    (hblind : EF.weilTest g.1.1.1 g.1.1.1 (Real.log 2) = 0) (m : ℕ) :
    (1 / (4 : ℝ) ^ m) * (EF.weilTest g.1.1.1 g.1.1.1 0).re ≤
      (EF.weilTest g.1.1.1 g.1.1.1 0).re -
        (EF.weilTest g.1.1.1 g.1.1.1 (Real.log 2 / (2 : ℝ) ^ m)).re := by
  have h := g.dyadic_deficit (Real.log 2) m
  rw [hblind, Complex.zero_re, sub_zero] at h
  rw [one_div, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
  simpa only [mul_comm] using h

end RealEvenPolarTestFn

/-- Real-valued smooth EWU sources, retaining the original smooth test. -/
def RealSmoothEvenPolarTestFn := {g : SmoothEvenPolarTestFn // ∀ u, (g.1.1.1 u).im = 0}

def RealSmoothEvenPolarTestFn.toRealEvenPolar (g : RealSmoothEvenPolarTestFn) :
    RealEvenPolarTestFn := ⟨g.1.1, g.2⟩

theorem RealSmoothEvenPolarTestFn.weilArchRe_eq_levy (g : RealSmoothEvenPolarTestFn) :
    WeilOneSided.weilArchRe (EF.weilTest g.1.1.1.1 g.1.1.1.1) =
      EF.gammaBracket 0 * (EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re +
        ∫ x in Ioi 0, ((EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re -
          (EF.weilTest g.1.1.1.1 g.1.1.1.1 x).re) * (Real.exp (x / 2) / Real.sinh x) :=
  g.toRealEvenPolar.weilArchRe_eq_levy

end RHTower.EvenSector

namespace RHTower.AutocorrelationKrein

/-- Cosine is positive definite: its finite real Gram form is a sum of two squares. -/
theorem cosine_gram_nonneg (ω : ℝ) {n : ℕ} (c t : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * Real.cos (ω * (t i - t j)) := by
  have he : (∑ i, ∑ j, c i * c j * Real.cos (ω * (t i - t j))) =
      (∑ i, c i * Real.cos (ω * t i)) ^ 2 +
        (∑ i, c i * Real.sin (ω * t i)) ^ 2 := by
    simp only [mul_sub, Real.cos_sub, mul_add, Finset.sum_add_distrib, pow_two,
      Finset.sum_mul, Finset.mul_sum]
    apply congrArg₂ (fun a b : ℝ => a + b)
    all_goals
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
  rw [he]
  positivity

/-- A continuous positive-definite kernel blind at log 2 can return to its maximum
inside the interval. Thus positive-definiteness cannot justify the proposed interpolation.
This witness is a finite spectral measure, not a claim that cosine itself is an L² autocorrelation. -/
theorem exists_positiveDefinite_blind_interior_return :
    ∃ k : ℝ → ℝ, Continuous k ∧ k 0 = 1 ∧ k (Real.log 2) = 0 ∧
      (∀ (n : ℕ) (c t : Fin n → ℝ), 0 ≤ ∑ i, ∑ j, c i * c j * k (t i - t j)) ∧
      ∃ x ∈ Ioo (0 : ℝ) (Real.log 2), k 0 - k x = 0 := by
  let ω : ℝ := 5 * Real.pi / (2 * Real.log 2)
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : ω * Real.log 2 = Real.pi / 2 + 2 * Real.pi := by
    dsimp [ω]
    field_simp
    ring
  refine ⟨fun x => Real.cos (ω * x), by fun_prop, by simp, ?_,
    (fun n c t => cosine_gram_nonneg ω c t), 4 * Real.log 2 / 5,
    ⟨by positivity, by linarith⟩, ?_⟩
  · change Real.cos (ω * Real.log 2) = 0
    rw [he, Real.cos_add_two_pi, Real.cos_pi_div_two]
  · have hr : ω * (4 * Real.log 2 / 5) = 2 * Real.pi := by
      dsimp [ω]
      field_simp
      ring
    simp only [mul_zero, Real.cos_zero, hr, Real.cos_two_pi, sub_self]

end RHTower.AutocorrelationKrein
