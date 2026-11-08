import GaloisForLFunctions.ArithmeticPositiveDuality.PositiveTwoPrimeAnnihilators
import Mathlib.Analysis.MeanInequalities

/-!
# Accuracy of a positive annihilator forces growth to the left

The nonconstant mass of a positive Dirichlet polynomial is logarithmically
convex in the real argument. At a zero it is at least one. Interpolation therefore
turns small error on a right line into a quantitative lower bound on every line
to the left of the zero. A single monomial attains the interpolation inequality.
-/

noncomputable section
set_option autoImplicit false

open Complex Finset
open scoped NNReal

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

/-- The logarithm of the integer `2^(d 0) 3^(d 1)`. -/
def monomialLog (d : Fin 2 →₀ ℕ) : ℝ :=
  (d 0 : ℝ) * Real.log (primeBase 0) + (d 1 : ℝ) * Real.log (primeBase 1)

/-- The positive real mass of the nonconstant monomials. -/
def dirichletTailMass (P : MvPolynomial (Fin 2) ℝ≥0) (σ : ℝ) : ℝ :=
  ∑ d ∈ P.support.erase 0, ((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * σ)

private theorem monomial_exp (d : Fin 2 →₀ ℕ) (s : ℂ) :
    Complex.exp (-(Real.log (primeBase 0) : ℂ) * s) ^ d 0 *
      Complex.exp (-(Real.log (primeBase 1) : ℂ) * s) ^ d 1 =
        Complex.exp (-(monomialLog d : ℂ) * s) := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  dsimp only [monomialLog]
  push_cast
  ring

theorem dirichletEval_eq_frequency_sum (P : MvPolynomial (Fin 2) ℝ≥0) (s : ℂ) :
    dirichletEval s P = ∑ d ∈ P.support,
      (((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * s) := by
  change MvPolynomial.eval₂ _ _ P = _
  rw [MvPolynomial.eval₂_eq']
  simp only [Fin.prod_univ_two]
  apply Finset.sum_congr rfl
  intro d _
  rw [monomial_exp]
  rfl

theorem dirichletEval_eq_one_add_tail {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) (s : ℂ) :
    dirichletEval s P = 1 + ∑ d ∈ P.support.erase 0,
      (((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * s) := by
  classical
  have hc : P.coeff 0 = 1 := hP
  have hmem : (0 : Fin 2 →₀ ℕ) ∈ P.support := by
    rw [MvPolynomial.mem_support_iff, hc]
    exact one_ne_zero
  have h := Finset.sum_erase_add P.support
    (fun d => (((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * s)) hmem
  have h0 : (((P.coeff 0 : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog 0 : ℂ) * s) = 1 := by
    simp [monomialLog, hc]
  rw [h0, ← dirichletEval_eq_frequency_sum] at h
  exact h.symm.trans (add_comm _ _)

theorem dirichletTailMass_nonneg (P : MvPolynomial (Fin 2) ℝ≥0) (σ : ℝ) :
    0 ≤ dirichletTailMass P σ := by
  unfold dirichletTailMass
  exact Finset.sum_nonneg fun d _ => mul_nonneg (P.coeff d).coe_nonneg (Real.exp_pos _).le

/-- Cancellation of the constant term costs at least one in nonconstant positive mass. -/
theorem one_le_dirichletTailMass_of_zero {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {ρ : ℂ} (hz : dirichletEval ρ P = 0) :
    1 ≤ dirichletTailMass P ρ.re := by
  have he := dirichletEval_eq_one_add_tail hP ρ
  rw [hz] at he
  have hs : (∑ d ∈ P.support.erase 0,
      (((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ)) = -1 := by
    linear_combination -he
  calc
    1 = ‖∑ d ∈ P.support.erase 0,
        (((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ)‖ := by rw [hs]; simp
    _ ≤ ∑ d ∈ P.support.erase 0,
        ‖(((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ)‖ := norm_sum_le _ _
    _ = dirichletTailMass P ρ.re := by
      unfold dirichletTailMass
      apply Finset.sum_congr rfl
      intro d _
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (P.coeff d).coe_nonneg, Complex.norm_exp, Complex.mul_re,
        Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
        neg_zero, zero_mul, sub_zero]

theorem dirichletTailMass_pos_of_zero {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {ρ : ℂ} (hz : dirichletEval ρ P = 0) (σ : ℝ) :
    0 < dirichletTailMass P σ := by
  have hm := one_le_dirichletTailMass_of_zero hP hz
  have hS : (P.support.erase 0).Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty] at hn
    simp only [dirichletTailMass, hn, Finset.sum_empty] at hm
    norm_num at hm
  unfold dirichletTailMass
  apply Finset.sum_pos _ hS
  intro d hd
  have hc : (0 : ℝ) < ((P.coeff d : ℝ≥0) : ℝ) := by
    have hn := MvPolynomial.mem_support_iff.mp (Finset.mem_of_mem_erase hd)
    exact_mod_cast (pos_iff_ne_zero.mpr hn : 0 < P.coeff d)
  exact mul_pos hc (Real.exp_pos _)

private theorem monomialTerm_re (c L : ℝ) (ρ : ℂ) :
    ((c : ℂ) * Complex.exp (-(L : ℂ) * ρ)).re =
      c * Real.exp (-L * ρ.re) * Real.cos (L * ρ.im) := by
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.exp_re, Complex.neg_re, Complex.neg_im,
    Complex.mul_im, add_zero, neg_mul, Real.cos_neg, mul_assoc]

/-- The mass beyond one is exactly the positive defect of the cancelling phases. -/
theorem dirichletTailMass_sub_one_eq_phase_defect {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {ρ : ℂ} (hz : dirichletEval ρ P = 0) :
    dirichletTailMass P ρ.re - 1 =
      ∑ d ∈ P.support.erase 0, ((P.coeff d : ℝ≥0) : ℝ) *
        Real.exp (-monomialLog d * ρ.re) * (1 + Real.cos (monomialLog d * ρ.im)) := by
  have he := congrArg Complex.re (dirichletEval_eq_one_add_tail hP ρ)
  rw [hz, Complex.zero_re, Complex.add_re, Complex.one_re] at he
  change 0 = 1 + Complex.reAddGroupHom (∑ d ∈ P.support.erase 0,
    (((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ)) at he
  rw [map_sum] at he
  change 0 = 1 + ∑ d ∈ P.support.erase 0,
    ((((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ)).re at he
  simp_rw [monomialTerm_re] at he
  unfold dirichletTailMass
  simp_rw [mul_add, mul_one]
  rw [Finset.sum_add_distrib]
  linarith only [he]

/-- Minimal mass occurs exactly when every supported nonconstant phase has cosine minus one. -/
theorem dirichletTailMass_eq_one_iff_phases {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {ρ : ℂ} (hz : dirichletEval ρ P = 0) :
    dirichletTailMass P ρ.re = 1 ↔
      ∀ d ∈ P.support.erase 0, Real.cos (monomialLog d * ρ.im) = -1 := by
  have hdef := dirichletTailMass_sub_one_eq_phase_defect hP hz
  have hpos (d : Fin 2 →₀ ℕ) (hd : d ∈ P.support.erase 0) :
      0 < ((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * ρ.re) := by
    apply mul_pos _ (Real.exp_pos _)
    have hn := MvPolynomial.mem_support_iff.mp (Finset.mem_of_mem_erase hd)
    exact_mod_cast (pos_iff_ne_zero.mpr hn : 0 < P.coeff d)
  have hnonneg (d : Fin 2 →₀ ℕ) (hd : d ∈ P.support.erase 0) :
      0 ≤ ((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * ρ.re) *
        (1 + Real.cos (monomialLog d * ρ.im)) := by
    apply mul_nonneg (hpos d hd).le
    linarith only [Real.neg_one_le_cos (monomialLog d * ρ.im)]
  constructor
  · intro hm
    have hs : (∑ d ∈ P.support.erase 0, ((P.coeff d : ℝ≥0) : ℝ) *
        Real.exp (-monomialLog d * ρ.re) * (1 + Real.cos (monomialLog d * ρ.im))) = 0 := by
      rw [← hdef, hm, sub_self]
    intro d hd
    have ht := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hs d hd
    have hc := (mul_eq_zero.mp ht).resolve_left (hpos d hd).ne'
    linarith only [hc]
  · intro hphase
    have hs : (∑ d ∈ P.support.erase 0, ((P.coeff d : ℝ≥0) : ℝ) *
        Real.exp (-monomialLog d * ρ.re) * (1 + Real.cos (monomialLog d * ρ.im))) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      rw [hphase d hd]
      ring
    rw [hs] at hdef
    linarith only [hdef]

theorem dirichletEval_ofReal_eq_one_add_tail {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) (σ : ℝ) :
    dirichletEval (σ : ℂ) P = ((1 + dirichletTailMass P σ : ℝ) : ℂ) := by
  rw [dirichletEval_eq_one_add_tail hP, Complex.ofReal_add, Complex.ofReal_one]
  congr 1
  unfold dirichletTailMass
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  push_cast
  rfl

theorem norm_dirichletEval_real_error {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) (σ : ℝ) :
    ‖dirichletEval (σ : ℂ) P - 1‖ = dirichletTailMass P σ := by
  rw [dirichletEval_ofReal_eq_one_add_tail hP, Complex.ofReal_add, Complex.ofReal_one,
    add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (dirichletTailMass_nonneg P σ)]

private theorem sum_interpolate {ι : Type*} (S : Finset ι) (x y : ι → ℝ)
    (hx : ∀ i ∈ S, 0 ≤ x i) (hy : ∀ i ∈ S, 0 ≤ y i)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (∑ i ∈ S, (x i) ^ θ * (y i) ^ (1 - θ)) ≤
      (∑ i ∈ S, x i) ^ θ * (∑ i ∈ S, y i) ^ (1 - θ) := by
  have hθ : θ ≠ 0 := hθ0.ne'
  have hη : 1 - θ ≠ 0 := (sub_pos.mpr hθ1).ne'
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg S
    (f := fun i => (x i) ^ θ) (g := fun i => (y i) ^ (1 - θ))
    (Real.HolderConjugate.inv_one_sub_inv hθ0 hθ1)
    (fun i hi => Real.rpow_nonneg (hx i hi) _)
    (fun i hi => Real.rpow_nonneg (hy i hi) _)
  have hX : (∑ i ∈ S, ((x i) ^ θ) ^ θ⁻¹) = ∑ i ∈ S, x i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.rpow_mul (hx i hi), mul_inv_cancel₀ hθ, Real.rpow_one]
  have hY : (∑ i ∈ S, ((y i) ^ (1 - θ)) ^ (1 - θ)⁻¹) = ∑ i ∈ S, y i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.rpow_mul (hy i hi), mul_inv_cancel₀ hη, Real.rpow_one]
  simpa only [hX, hY, one_div, inv_inv] using h

private theorem exp_term_interpolate {c : ℝ} (hc : 0 < c) (L s t θ : ℝ) :
    c * Real.exp (-L * (θ * s + (1 - θ) * t)) =
      (c * Real.exp (-L * s)) ^ θ * (c * Real.exp (-L * t)) ^ (1 - θ) := by
  rw [Real.rpow_def_of_pos (mul_pos hc (Real.exp_pos _)),
    Real.rpow_def_of_pos (mul_pos hc (Real.exp_pos _)),
    Real.log_mul hc.ne' (Real.exp_pos _).ne',
    Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp, ← Real.exp_add]
  conv_lhs => rw [← Real.exp_log hc, ← Real.exp_add]
  congr 1
  ring

/-- The positive tail mass is multiplicatively convex on the real axis. -/
theorem dirichletTailMass_interpolate (P : MvPolynomial (Fin 2) ℝ≥0) (s t : ℝ)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    dirichletTailMass P (θ * s + (1 - θ) * t) ≤
      dirichletTailMass P s ^ θ * dirichletTailMass P t ^ (1 - θ) := by
  unfold dirichletTailMass
  calc
    _ = ∑ d ∈ P.support.erase 0,
        (((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * s)) ^ θ *
        (((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * t)) ^ (1 - θ) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hc : (0 : ℝ) < ((P.coeff d : ℝ≥0) : ℝ) := by
        have hn := MvPolynomial.mem_support_iff.mp (Finset.mem_of_mem_erase hd)
        exact_mod_cast (pos_iff_ne_zero.mpr hn : 0 < P.coeff d)
      exact exp_term_interpolate hc _ _ _ _
    _ ≤ _ := sum_interpolate _ _ _
      (fun d _ => mul_nonneg (P.coeff d).coe_nonneg (Real.exp_pos _).le)
      (fun d _ => mul_nonneg (P.coeff d).coe_nonneg (Real.exp_pos _).le) hθ0 hθ1

/-- A zero imposes an exact two-sided positive-mass constraint. -/
theorem root_forces_tail_sandwich {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {ρ : ℂ} (hz : dirichletEval ρ P = 0)
    {σlo σhi : ℝ} (hlo : σlo < ρ.re) (hhi : ρ.re < σhi) :
    1 ≤ dirichletTailMass P σhi ^ ((ρ.re - σlo) / (σhi - σlo)) *
      dirichletTailMass P σlo ^ ((σhi - ρ.re) / (σhi - σlo)) := by
  have hd : 0 < σhi - σlo := sub_pos.mpr (hlo.trans hhi)
  have hθ0 : 0 < (ρ.re - σlo) / (σhi - σlo) := div_pos (sub_pos.mpr hlo) hd
  have hθ1 : (ρ.re - σlo) / (σhi - σlo) < 1 := by
    apply (div_lt_one hd).mpr
    linarith only [hhi]
  have h := dirichletTailMass_interpolate P σhi σlo hθ0 hθ1
  have hη : 1 - (ρ.re - σlo) / (σhi - σlo) = (σhi - ρ.re) / (σhi - σlo) := by
    field_simp [hd.ne']
    ring
  have hβ : (ρ.re - σlo) / (σhi - σlo) * σhi +
      (1 - (ρ.re - σlo) / (σhi - σlo)) * σlo = ρ.re := by
    field_simp [hd.ne']
    ring
  rw [hβ, hη] at h
  exact (one_le_dirichletTailMass_of_zero hP hz).trans h

/-- Small positive mass on a right line forces a precise power of its reciprocal on the left. -/
theorem annihilator_accuracy_forces_left_growth {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {ρ : ℂ} (hz : dirichletEval ρ P = 0)
    {σlo σhi ε : ℝ} (hlo : σlo < ρ.re) (hhi : ρ.re < σhi)
    (hε : 0 < ε) (hacc : dirichletTailMass P σhi ≤ ε) :
    ε ^ (-((ρ.re - σlo) / (σhi - ρ.re))) ≤ dirichletTailMass P σlo := by
  have hR := dirichletTailMass_pos_of_zero hP hz σhi
  have hL := dirichletTailMass_pos_of_zero hP hz σlo
  have hd : 0 < σhi - σlo := sub_pos.mpr (hlo.trans hhi)
  have hs := root_forces_tail_sandwich hP hz hlo hhi
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1) hs
  rw [Real.log_one, Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hR, Real.log_rpow hL] at hlog
  have haccLog := Real.log_le_log hR hacc
  have hθ : 0 ≤ (ρ.re - σlo) / (σhi - σlo) :=
    div_nonneg (sub_pos.mpr hlo).le hd.le
  have hw := hlog.trans (add_le_add (mul_le_mul_of_nonneg_left haccLog hθ) le_rfl)
  have hscale' : 0 ≤ (ρ.re - σlo) * Real.log ε + (σhi - ρ.re) * Real.log (dirichletTailMass P σlo) := by
    calc
      0 = (σhi - σlo) * 0 := by ring
      _ ≤ (σhi - σlo) *
          ((ρ.re - σlo) / (σhi - σlo) * Real.log ε +
            (σhi - ρ.re) / (σhi - σlo) * Real.log (dirichletTailMass P σlo)) :=
        mul_le_mul_of_nonneg_left hw hd.le
      _ = _ := by field_simp [hd.ne']; ring
  have hb : -((ρ.re - σlo) * Real.log ε) / (σhi - ρ.re) ≤
      Real.log (dirichletTailMass P σlo) := by
    apply (div_le_iff₀ (sub_pos.mpr hhi)).mpr
    linarith only [hscale']
  rw [Real.rpow_def_of_pos hε, ← Real.exp_log hL]
  apply Real.exp_le_exp.mpr
  convert hb using 1 <;> ring

/-- Actual zeta zeros admit arbitrary positive finite annihilation accuracy, but every
such construction pays the corresponding power-law mass cost to the left of each zero. -/
theorem exists_xi_zero_annihilator_with_left_growth
    (F : Finset {ρ : ℂ // RHTower.xi ρ = 0})
    (m : {ρ : ℂ // RHTower.xi ρ = 0} → ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin 2) ℝ≥0, MvPolynomial.constantCoeff P = 1 ∧
      (∀ ρ ∈ F, dirichletEval (ρ : ℂ) P = 0 ∧
        (m ρ : ℕ∞) ≤ analyticOrderAt (fun s => dirichletEval s P) (ρ : ℂ)) ∧
      (∀ s : ℂ, 1 ≤ s.re → ‖dirichletEval s P - 1‖ < ε) ∧
      ∀ ρ ∈ F, ∀ σ : ℝ, σ < (ρ : ℂ).re →
        ε ^ (-(((ρ : ℂ).re - σ) / (1 - (ρ : ℂ).re))) ≤ dirichletTailMass P σ := by
  obtain ⟨P, hPc, hPz, hPa⟩ := exists_xi_zero_annihilator_with_multiplicities F m hε
  refine ⟨P, hPc, hPz, hPa, ?_⟩
  intro ρ hρ σ hσ
  have ha : dirichletTailMass P 1 ≤ ε := by
    rw [← norm_dirichletEval_real_error hPc]
    exact (hPa 1 (by norm_num)).le
  exact annihilator_accuracy_forces_left_growth hPc (hPz ρ hρ).1 hσ
    (RHTower.xi_zero_re_mem_open_unit ρ.property).2 hε ha

/-- The positive coefficient of the extremal binomial. -/
def sharpBinomialCoefficient (β : ℝ) : ℝ≥0 :=
  ⟨Real.exp (Real.log 2 * β), (Real.exp_pos _).le⟩

/-- A positive one-prime polynomial attaining the mass and interpolation bounds. -/
def sharpBinomial (β : ℝ) : MvPolynomial (Fin 2) ℝ≥0 :=
  1 + MvPolynomial.C (sharpBinomialCoefficient β) *
    MvPolynomial.X 0

/-- A zero of the extremal binomial on the prescribed vertical line. -/
def sharpBinomialRoot (β : ℝ) : ℂ :=
  (β : ℂ) + ((Real.pi / Real.log 2 : ℝ) : ℂ) * I

theorem sharpBinomial_constantCoeff (β : ℝ) :
    MvPolynomial.constantCoeff (sharpBinomial β) = 1 := by
  unfold sharpBinomial
  rw [map_add, map_one, map_mul]
  simp

theorem dirichletEval_sharpBinomial (β : ℝ) (s : ℂ) :
    dirichletEval s (sharpBinomial β) =
      1 + Complex.exp ((Real.log 2 : ℂ) * ((β : ℂ) - s)) := by
  unfold sharpBinomial
  rw [map_add, map_one, map_mul]
  simp only [dirichletEval, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
  change 1 + (Real.exp (Real.log 2 * β) : ℂ) *
    Complex.exp (-(Real.log 2 : ℂ) * s) = _
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem sharpBinomialRoot_re (β : ℝ) : (sharpBinomialRoot β).re = β := by
  simp only [sharpBinomialRoot, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero,
    add_zero]

theorem sharpBinomial_vanishes (β : ℝ) :
    dirichletEval (sharpBinomialRoot β) (sharpBinomial β) = 0 := by
  have hlog : (Real.log 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have harg : (Real.log 2 : ℂ) * ((β : ℂ) - sharpBinomialRoot β) =
      -((Real.pi : ℂ) * I) := by
    unfold sharpBinomialRoot
    push_cast
    field_simp [hlog]
    ring
  rw [dirichletEval_sharpBinomial, harg, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

theorem sharpBinomial_real_error (β σ : ℝ) :
    ‖dirichletEval (σ : ℂ) (sharpBinomial β) - 1‖ =
      Real.exp (Real.log 2 * (β - σ)) := by
  rw [dirichletEval_sharpBinomial, add_sub_cancel_left, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

theorem sharpBinomial_cost_equality (β σlo σhi : ℝ) (hhi : β < σhi) :
    Real.exp (Real.log 2 * (β - σhi)) ^ (-((β - σlo) / (σhi - β))) =
      Real.exp (Real.log 2 * (β - σlo)) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  field_simp [(sub_pos.mpr hhi).ne']
  ring

/-- The complete tail mass of the extremal binomial. -/
theorem dirichletTailMass_sharpBinomial (β σ : ℝ) :
    dirichletTailMass (sharpBinomial β) σ = Real.exp (Real.log 2 * (β - σ)) := by
  rw [← norm_dirichletEval_real_error (sharpBinomial_constantCoeff β)]
  exact sharpBinomial_real_error β σ

/-- The cancellation bound is attained at an actual zero of a positive Dirichlet polynomial. -/
theorem exists_positive_annihilator_of_unit_tail_mass (β : ℝ) :
    ∃ P : MvPolynomial (Fin 2) ℝ≥0, ∃ ρ : ℂ,
      MvPolynomial.constantCoeff P = 1 ∧ ρ.re = β ∧
      dirichletEval ρ P = 0 ∧ dirichletTailMass P β = 1 := by
  refine ⟨sharpBinomial β, sharpBinomialRoot β, sharpBinomial_constantCoeff β,
    sharpBinomialRoot_re β, sharpBinomial_vanishes β, ?_⟩
  rw [dirichletTailMass_sharpBinomial, sub_self, mul_zero, Real.exp_zero]

/-- The exponent in the left-growth bound is exact for the extremal binomial. -/
theorem sharpBinomial_attains_left_growth (β σlo σhi : ℝ) (hhi : β < σhi) :
    dirichletTailMass (sharpBinomial β) σhi ^ (-((β - σlo) / (σhi - β))) =
      dirichletTailMass (sharpBinomial β) σlo := by
  rw [dirichletTailMass_sharpBinomial, dirichletTailMass_sharpBinomial]
  exact sharpBinomial_cost_equality β σlo σhi hhi

#print axioms one_le_dirichletTailMass_of_zero
#print axioms dirichletTailMass_eq_one_iff_phases
#print axioms root_forces_tail_sandwich
#print axioms annihilator_accuracy_forces_left_growth
#print axioms exists_xi_zero_annihilator_with_left_growth
#print axioms exists_positive_annihilator_of_unit_tail_mass
#print axioms sharpBinomial_attains_left_growth

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator
