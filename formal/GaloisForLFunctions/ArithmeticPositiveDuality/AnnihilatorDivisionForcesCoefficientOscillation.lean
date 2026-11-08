import GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilatorAccuracyForcesLeftGrowth
import GaloisForLFunctions.HTGeometry.PiGeometricSeries
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# Dividing by a positive annihilator forces both coefficient signs to grow

The canonical two-prime coefficients of the formal quotient by a normalized positive
polynomial have arbitrarily large excursions of both signs below every right-hand zero.
Positivity turns either one-sided envelope into absolute convergence; the convolution
identity then contradicts the zero. No analytic continuation of the quotient is assumed.
-/

noncomputable section
set_option autoImplicit false
open Complex Finset
open scoped NNReal

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

private def geometricNumerator : MvPowerSeries (Fin 2) ℝ := fun _ => 1

/-- Formal two-prime coefficient series of `ζ/P`, restricted to the semigroup generated
by two and three. The all-one numerator is the formal product of the two geometric series. -/
def annihilatorQuotient (P : MvPolynomial (Fin 2) ℝ≥0) : MvPowerSeries (Fin 2) ℝ :=
  (MvPolynomial.map NNReal.toRealHom P : MvPowerSeries (Fin 2) ℝ)⁻¹ *
    geometricNumerator

/-- The canonical real coefficient at `2^(d 0) 3^(d 1)`. -/
def annihilatorQuotientCoeff (P : MvPolynomial (Fin 2) ℝ≥0) (d : Fin 2 →₀ ℕ) : ℝ :=
  MvPowerSeries.coeff d (annihilatorQuotient P)

private theorem quotient_mul (P : MvPolynomial (Fin 2) ℝ≥0)
    (hP : MvPolynomial.constantCoeff P = 1) :
    (MvPolynomial.map NNReal.toRealHom P : MvPowerSeries (Fin 2) ℝ) *
      annihilatorQuotient P = ((fun _ : Fin 2 →₀ ℕ => (1 : ℝ)) : MvPowerSeries (Fin 2) ℝ) := by
  have hc : MvPowerSeries.constantCoeff
      (MvPolynomial.map NNReal.toRealHom P : MvPowerSeries (Fin 2) ℝ) ≠ 0 := by
    change ((P.coeff 0 : ℝ≥0) : ℝ) ≠ 0
    change P.coeff 0 = 1 at hP
    rw [hP]
    exact one_ne_zero
  rw [annihilatorQuotient, ← mul_assoc, MvPowerSeries.mul_inv_cancel _ hc, one_mul]
  rfl

private theorem frequency_add (d e : Fin 2 →₀ ℕ) :
    monomialLog (d + e) = monomialLog d + monomialLog e := by
  simp only [monomialLog, Finsupp.add_apply, Nat.cast_add]
  ring

private theorem frequency_nonneg (d : Fin 2 →₀ ℕ) : 0 ≤ monomialLog d := by
  unfold monomialLog
  apply add_nonneg <;> apply mul_nonneg (Nat.cast_nonneg _)
  · exact Real.log_nonneg (by norm_num [primeBase])
  · exact Real.log_nonneg (by norm_num [primeBase])

private theorem frequency_mono {d e : Fin 2 →₀ ℕ} (h : d ≤ e) :
    monomialLog d ≤ monomialLog e := by
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (h 0))
      (Real.log_nonneg (by norm_num [primeBase]))
  · exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (h 1))
      (Real.log_nonneg (by norm_num [primeBase]))

private def primeNome (s : ℂ) (i : Fin 2) : ℂ :=
  Complex.exp (-(Real.log (primeBase i) : ℂ) * s)

private theorem frequency_exp (d : Fin 2 →₀ ℕ) (s : ℂ) :
    (∏ i, primeNome s i ^ d i) = Complex.exp (-(monomialLog d : ℂ) * s) := by
  rw [Fin.prod_univ_two]
  unfold primeNome
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  dsimp only [monomialLog]
  push_cast
  ring

private theorem primeNome_contracts {s : ℂ} (hs : 0 < s.re) (i : Fin 2) :
    ‖primeNome s i‖ < 1 := by
  rw [primeNome, Complex.norm_exp, Real.exp_lt_one_iff]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (Real.log_pos (by
    fin_cases i <;> norm_num [primeBase]))) hs

private theorem frequency_geometric {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun d : Fin 2 →₀ ℕ => Complex.exp (-(monomialLog d : ℂ) * s))
      (∏ i : Fin 2, (1 - primeNome s i)⁻¹) := by
  have h := (Finsupp.equivFunOnFinite (α := Fin 2) (M := ℕ)).hasSum_iff.mpr
    (HTGeometry.hasSum_pi_geometric (primeNome s) (primeNome_contracts hs))
  exact h.congr_fun fun d => (frequency_exp d s).symm

private theorem frequency_geometric_norm {s : ℂ} (hs : 0 < s.re) :
    Summable (fun d : Fin 2 →₀ ℕ => ‖Complex.exp (-(monomialLog d : ℂ) * s)‖) := by
  have h := (Finsupp.equivFunOnFinite (α := Fin 2) (M := ℕ)).summable_iff.mpr
    (HTGeometry.summable_norm_pi_geometric (primeNome s) (primeNome_contracts hs))
  exact h.congr fun d => congrArg norm (frequency_exp d s)

private theorem frequency_geometric_sum_ne_zero {s : ℂ} (hs : 0 < s.re) :
    (∑' d : Fin 2 →₀ ℕ, Complex.exp (-(monomialLog d : ℂ) * s)) ≠ 0 := by
  rw [(frequency_geometric hs).tsum_eq]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply inv_ne_zero
  apply sub_ne_zero.mpr
  intro h
  have hc := primeNome_contracts hs i
  rw [← h, norm_one] at hc
  exact lt_irrefl _ hc

private theorem coeff_polynomial_mul (Q : MvPolynomial (Fin 2) ℝ)
    (B : MvPowerSeries (Fin 2) ℝ) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d ((Q : MvPowerSeries (Fin 2) ℝ) * B) =
      ∑ e ∈ Q.support, if e ≤ d then Q.coeff e * MvPowerSeries.coeff (d - e) B else 0 := by
  classical
  conv_lhs => rw [Q.as_sum]
  change MvPowerSeries.coeff d
    (MvPolynomial.coeToMvPowerSeries.ringHom (∑ e ∈ Q.support,
      MvPolynomial.monomial e (Q.coeff e)) * B) = _
  simp only [map_sum, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
    MvPolynomial.coe_monomial, Finset.sum_mul, MvPowerSeries.coeff_monomial_mul]

private theorem quotient_recurrence (P : MvPolynomial (Fin 2) ℝ≥0)
    (hP : MvPolynomial.constantCoeff P = 1) (d : Fin 2 →₀ ℕ) :
    annihilatorQuotientCoeff P d +
      (∑ e ∈ (MvPolynomial.map NNReal.toRealHom P).support.erase 0,
        if e ≤ d then ((P.coeff e : ℝ≥0) : ℝ) * annihilatorQuotientCoeff P (d-e) else 0) = 1 := by
  classical
  let Q := MvPolynomial.map NNReal.toRealHom P
  have h0 : Q.coeff 0 = 1 := by
    change P.coeff 0 = 1 at hP
    simp only [Q, MvPolynomial.coeff_map, hP, map_one]
  have hm : (0 : Fin 2 →₀ ℕ) ∈ Q.support := by
    rw [MvPolynomial.mem_support_iff, h0]
    exact one_ne_zero
  have hc := congrArg (MvPowerSeries.coeff d) (quotient_mul P hP)
  rw [coeff_polynomial_mul] at hc
  have he := Finset.sum_erase_add Q.support
    (fun e => if e ≤ d then Q.coeff e * MvPowerSeries.coeff (d-e) (annihilatorQuotient P) else 0) hm
  simp only [h0, zero_le, if_true, tsub_zero, one_mul] at he
  rw [← he] at hc
  simpa only [MvPowerSeries.coeff_apply, Q, MvPolynomial.coeff_map,
    NNReal.coe_toRealHom, annihilatorQuotientCoeff, add_comm] using hc

/-- Either one-sided exponential envelope forces an absolute envelope for the quotient. -/
private theorem absolute_envelope_of_one_sided
    (P : MvPolynomial (Fin 2) ℝ≥0) (hP : MvPolynomial.constantCoeff P = 1)
    {α C : ℝ} (hα : 0 ≤ α) (hC : 0 < C)
    (hbound : (∀ d, annihilatorQuotientCoeff P d ≤ C * Real.exp (α * monomialLog d)) ∨
      (∀ d, -(C * Real.exp (α * monomialLog d)) ≤ annihilatorQuotientCoeff P d)) :
    ∃ K : ℝ, 0 < K ∧ ∀ d, |annihilatorQuotientCoeff P d| ≤
      K * Real.exp (α * monomialLog d) := by
  classical
  let S := (MvPolynomial.map NNReal.toRealHom P).support.erase 0
  let A : ℝ := ∑ e ∈ S, ((P.coeff e : ℝ≥0) : ℝ)
  have hA : 0 ≤ A := Finset.sum_nonneg fun e _ => (P.coeff e).coe_nonneg
  refine ⟨1 + C + C * A, by positivity, fun d => ?_⟩
  let W : ℝ := Real.exp (α * monomialLog d)
  have hW : 1 ≤ W := Real.one_le_exp (mul_nonneg hα (frequency_nonneg d))
  have hW0 : 0 ≤ W := (Real.exp_pos _).le
  have hshift (e : Fin 2 →₀ ℕ) :
      Real.exp (α * monomialLog (d-e)) ≤ W :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (frequency_mono (tsub_le_self : d-e ≤ d)) hα)
  have hsum := quotient_recurrence P hP d
  change annihilatorQuotientCoeff P d +
    (∑ e ∈ S, if e ≤ d then ((P.coeff e : ℝ≥0) : ℝ) *
      annihilatorQuotientCoeff P (d-e) else 0) = 1 at hsum
  have hscale : (∑ e ∈ S, ((P.coeff e : ℝ≥0) : ℝ) * (C * W)) = C * A * W := by
    rw [← Finset.sum_mul]
    dsimp only [A]
    ring
  rcases hbound with hu | hl
  · have ht : (∑ e ∈ S, if e ≤ d then ((P.coeff e : ℝ≥0) : ℝ) *
        annihilatorQuotientCoeff P (d-e) else 0) ≤ C * A * W := by
      rw [← hscale]
      apply Finset.sum_le_sum
      intro e _
      split_ifs with he
      · exact mul_le_mul_of_nonneg_left
          ((hu _).trans (mul_le_mul_of_nonneg_left (hshift e) hC.le)) (P.coeff e).coe_nonneg
      · positivity
    apply abs_le.mpr
    have hd := hu d
    change annihilatorQuotientCoeff P d ≤ C * W at hd
    constructor <;> nlinarith only [hsum, ht, hd, hW, hC, hA, hW0, mul_nonneg hC.le hA, mul_nonneg hC.le hW0,
      mul_nonneg (mul_nonneg hC.le hA) hW0]
  · have ht : -(C * A * W) ≤ (∑ e ∈ S, if e ≤ d then ((P.coeff e : ℝ≥0) : ℝ) *
        annihilatorQuotientCoeff P (d-e) else 0) := by
      rw [← hscale, ← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro e _
      split_ifs with he
      · have hv := (hl (d-e))
        have hw := mul_le_mul_of_nonneg_left (hshift e) hC.le
        have hb : -(C * W) ≤ annihilatorQuotientCoeff P (d-e) := by linarith only [hv, hw]
        simpa only [mul_neg] using mul_le_mul_of_nonneg_left hb (P.coeff e).coe_nonneg
      · exact neg_nonpos.mpr (mul_nonneg (P.coeff e).coe_nonneg (mul_nonneg hC.le hW0))
    apply abs_le.mpr
    have hd := hl d
    change -(C * W) ≤ annihilatorQuotientCoeff P d at hd
    constructor <;> nlinarith only [hsum, ht, hd, hW, hC, hA, hW0, mul_nonneg hC.le hA, mul_nonneg hC.le hW0,
      mul_nonneg (mul_nonneg hC.le hA) hW0]

private theorem weighted_quotient_summable (P : MvPolynomial (Fin 2) ℝ≥0)
    {α K : ℝ} (hK : ∀ d, |annihilatorQuotientCoeff P d| ≤ K * Real.exp (α * monomialLog d))
    {s : ℂ} (hs : α < s.re) :
    Summable (fun d : Fin 2 →₀ ℕ => ‖(annihilatorQuotientCoeff P d : ℂ) *
      Complex.exp (-(monomialLog d : ℂ) * s)‖) := by
  have hg := frequency_geometric_norm (s := s - (α : ℂ)) (by simpa using sub_pos.mpr hs)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hg.mul_left K)
  intro d
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
  calc
    |annihilatorQuotientCoeff P d| * Real.exp (-monomialLog d * s.re)
      ≤ (K * Real.exp (α * monomialLog d)) * Real.exp (-monomialLog d * s.re) :=
        mul_le_mul_of_nonneg_right (hK d) (Real.exp_pos _).le
    _ = K * ‖Complex.exp (-(monomialLog d : ℂ) * (s - (α : ℂ)))‖ := by
      rw [mul_assoc, ← Real.exp_add, Complex.norm_exp]
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im, neg_zero, zero_mul, sub_zero, Complex.sub_re]
      congr 2
      ring

private theorem quotient_evaluation (P : MvPolynomial (Fin 2) ℝ≥0)
    (hP : MvPolynomial.constantCoeff P = 1) (s : ℂ)
    (hb : Summable (fun d : Fin 2 →₀ ℕ => ‖(annihilatorQuotientCoeff P d : ℂ) *
      Complex.exp (-(monomialLog d : ℂ) * s)‖)) :
    dirichletEval s P * (∑' d : Fin 2 →₀ ℕ, (annihilatorQuotientCoeff P d : ℂ) *
      Complex.exp (-(monomialLog d : ℂ) * s)) =
        ∑' d : Fin 2 →₀ ℕ, Complex.exp (-(monomialLog d : ℂ) * s) := by
  classical
  let a := fun d : Fin 2 →₀ ℕ => (((P.coeff d : ℝ≥0) : ℝ) : ℂ) *
    Complex.exp (-(monomialLog d : ℂ) * s)
  let b := fun d : Fin 2 →₀ ℕ => (annihilatorQuotientCoeff P d : ℂ) *
    Complex.exp (-(monomialLog d : ℂ) * s)
  have ha0 {d : Fin 2 →₀ ℕ} (hd : d ∉ P.support) : a d = 0 := by
    simp only [a, MvPolynomial.notMem_support_iff.mp hd, NNReal.coe_zero, Complex.ofReal_zero,
      zero_mul]
  have ha : Summable (fun d => ‖a d‖) := summable_of_ne_finset_zero (s := P.support)
    (fun d hd => by rw [ha0 hd, norm_zero])
  have hsum : (∑' d, a d) = dirichletEval s P := by
    rw [tsum_eq_sum (s := P.support) (fun d hd => ha0 hd), dirichletEval_eq_frequency_sum]
  rw [← hsum]
  change (∑' d, a d) * (∑' d, b d) = _
  have hconv := Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
    (f := a) (g := b) ha.of_norm hb.of_norm
    (summable_mul_of_summable_norm (f := a) (g := b) ha hb)
  rw [hconv]
  apply tsum_congr
  intro d
  have hc := congrArg (MvPowerSeries.coeff d) (quotient_mul P hP)
  rw [MvPowerSeries.coeff_mul] at hc
  simp only [MvPowerSeries.coeff_apply] at hc
  have hcc := congrArg Complex.ofReal hc
  push_cast at hcc
  calc
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal d, a p.1 * b p.2) =
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal d, (((P.coeff p.1 : ℝ≥0) : ℝ) : ℂ) *
          (annihilatorQuotientCoeff P p.2 : ℂ)) * Complex.exp (-(monomialLog d : ℂ) * s) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      have hp' : p.1 + p.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      dsimp only [a, b]
      rw [show (-(monomialLog d : ℂ) * s) =
          -(monomialLog p.1 : ℂ) * s + -(monomialLog p.2 : ℂ) * s by
        rw [← hp', frequency_add, Complex.ofReal_add]; ring, Complex.exp_add]
      ring
    _ = _ := by rw [show (∑ p ∈ Finset.HasAntidiagonal.antidiagonal d,
          (((P.coeff p.1 : ℝ≥0) : ℝ) : ℂ) * (annihilatorQuotientCoeff P p.2 : ℂ)) = 1
        from hcc, one_mul]

/-- Even at a zero's own real part, the absolute weighted quotient mass diverges. -/
theorem quotient_absolute_mass_diverges_at_zero
    (P : MvPolynomial (Fin 2) ℝ≥0) (hP : MvPolynomial.constantCoeff P = 1)
    {ρ : ℂ} (hρ : 0 < ρ.re) (hz : dirichletEval ρ P = 0) :
    ¬ Summable (fun d : Fin 2 →₀ ℕ => |annihilatorQuotientCoeff P d| *
      Real.exp (-monomialLog d * ρ.re)) := by
  intro h
  have hb : Summable (fun d : Fin 2 →₀ ℕ => ‖(annihilatorQuotientCoeff P d : ℂ) *
      Complex.exp (-(monomialLog d : ℂ) * ρ)‖) := by
    apply h.congr
    intro d
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
      Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
  have he := quotient_evaluation P hP ρ hb
  rw [hz, zero_mul] at he
  exact frequency_geometric_sum_ne_zero hρ he.symm

/-- A right-hand zero makes both signs of the canonical quotient coefficients exceed
any exponential envelope with smaller nonnegative exponent. -/
theorem quotient_coefficients_have_two_sided_exponential_excursions
    (P : MvPolynomial (Fin 2) ℝ≥0) (hP : MvPolynomial.constantCoeff P = 1)
    {ρ : ℂ} (hz : dirichletEval ρ P = 0) {α : ℝ} (hα : 0 ≤ α) (hαρ : α < ρ.re)
    (C : ℝ) (hC : 0 < C) :
    (∃ d : Fin 2 →₀ ℕ, C * Real.exp (α * monomialLog d) < annihilatorQuotientCoeff P d) ∧
    (∃ d : Fin 2 →₀ ℕ, annihilatorQuotientCoeff P d < -(C * Real.exp (α * monomialLog d))) := by
  have impossible (hb : (∀ d, annihilatorQuotientCoeff P d ≤ C * Real.exp (α * monomialLog d)) ∨
      (∀ d, -(C * Real.exp (α * monomialLog d)) ≤ annihilatorQuotientCoeff P d)) : False := by
    obtain ⟨K, _, hK⟩ := absolute_envelope_of_one_sided P hP hα hC hb
    have he := quotient_evaluation P hP ρ (weighted_quotient_summable P hK hαρ)
    rw [hz, zero_mul] at he
    exact frequency_geometric_sum_ne_zero (lt_of_le_of_lt hα hαρ) he.symm
  constructor
  · by_contra! h
    exact impossible (Or.inl h)
  · by_contra! h
    exact impossible (Or.inr h)

/-- Both exponential excursions escape every prescribed finite coefficient set. -/
theorem quotient_coefficient_excursions_escape_finite_sets
    (P : MvPolynomial (Fin 2) ℝ≥0) (hP : MvPolynomial.constantCoeff P = 1)
    {ρ : ℂ} (hz : dirichletEval ρ P = 0) {α : ℝ} (hα : 0 ≤ α) (hαρ : α < ρ.re)
    (C : ℝ) (hC : 0 < C) (S : Finset (Fin 2 →₀ ℕ)) :
    (∃ d ∉ S, C * Real.exp (α * monomialLog d) < annihilatorQuotientCoeff P d) ∧
    (∃ d ∉ S, annihilatorQuotientCoeff P d < -(C * Real.exp (α * monomialLog d))) := by
  classical
  let A : ℝ := ∑ d ∈ S, |annihilatorQuotientCoeff P d|
  have hA : 0 ≤ A := Finset.sum_nonneg fun d _ => abs_nonneg _
  have hK : 0 < C + 1 + A := by linarith only [hC, hA]
  obtain ⟨⟨d, hd⟩, ⟨e, he⟩⟩ :=
    quotient_coefficients_have_two_sided_exponential_excursions P hP hz hα hαρ (C + 1 + A) hK
  have hw (d : Fin 2 →₀ ℕ) : 1 ≤ Real.exp (α * monomialLog d) :=
    Real.one_le_exp (mul_nonneg hα (frequency_nonneg d))
  have hc (d : Fin 2 →₀ ℕ) : C * Real.exp (α * monomialLog d) ≤
      (C + 1 + A) * Real.exp (α * monomialLog d) :=
    mul_le_mul_of_nonneg_right (by linarith only [hA]) (Real.exp_pos _).le
  have habs {d : Fin 2 →₀ ℕ} (hd : d ∈ S) : |annihilatorQuotientCoeff P d| ≤ A :=
    Finset.single_le_sum (f := fun d => |annihilatorQuotientCoeff P d|)
      (fun x _ => abs_nonneg _) hd
  have hl (d : Fin 2 →₀ ℕ) : A < (C + 1 + A) * Real.exp (α * monomialLog d) := by
    have hh := mul_le_mul_of_nonneg_left (hw d) hK.le
    nlinarith only [hh, hC]
  constructor
  · refine ⟨d, ?_, (hc d).trans_lt hd⟩
    intro hmem
    have hh := (le_abs_self (annihilatorQuotientCoeff P d)).trans (habs hmem)
    linarith only [hh, hl d, hd]
  · refine ⟨e, ?_, he.trans_le (neg_le_neg (hc e))⟩
    intro hmem
    have hh := (neg_abs_le (annihilatorQuotientCoeff P e))
    have ha := habs hmem
    linarith only [hh, ha, hl e, he]

#print axioms quotient_absolute_mass_diverges_at_zero
#print axioms quotient_coefficients_have_two_sided_exponential_excursions
#print axioms quotient_coefficient_excursions_escape_finite_sets

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator
