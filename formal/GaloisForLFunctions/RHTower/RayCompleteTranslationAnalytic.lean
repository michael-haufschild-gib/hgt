import GaloisForLFunctions.RHTower.GeneralizedDirichletSeriesInjectivity
import GaloisForLFunctions.RHTower.RationalExponentialDecay
import GaloisForLFunctions.RHTower.RayCompleteTranslationFaithful

/-!
# Analytic realization of ray-complete translation faithfulness

`RayCompleteTranslationFaithful` proves the character/Vandermonde core.  This file supplies the
previously missing analytic bridge: finite translations of an absolutely convergent generalized
Dirichlet series have the expected character-twisted coefficients; a rational output must vanish
because the series decays exponentially; generalized-Dirichlet uniqueness then forces every
translation character to vanish.
-/

open Complex Filter Topology Asymptotics

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The literal action of a finite translation-algebra element on a function. -/
def finiteTranslationAction (P : AddMonoidAlgebra ℂ ℂ) (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  ∑ h ∈ P.coeff.support, P.coeff h * f (s + h)

/-- A convenient common right-half-plane threshold for every shift in a finite operator. -/
def finiteTranslationThreshold (P : AddMonoidAlgebra ℂ ℂ) (sigma : ℝ) : ℝ :=
  sigma + ∑ h ∈ P.coeff.support, |h.re|

lemma finiteTranslationThreshold_le_re_add
    (P : AddMonoidAlgebra ℂ ℂ) (sigma x : ℝ) (hx : finiteTranslationThreshold P sigma ≤ x)
    {h : ℂ} (hh : h ∈ P.coeff.support) :
    sigma ≤ ((x : ℂ) + h).re := by
  have habs : |h.re| ≤ ∑ u ∈ P.coeff.support, |u.re| := by
    exact Finset.single_le_sum (fun u hu => abs_nonneg u.re) hh
  rw [Complex.add_re, Complex.ofReal_re]
  dsimp [finiteTranslationThreshold] at hx
  have hneg : -h.re ≤ |h.re| := neg_le_abs _
  linarith

private lemma summable_generalizedDirichletTerm_of_re_ge
    {mu : ℕ → ℝ} (hmu0 : ∀ n, 0 < mu n) {a : ℕ → ℂ} {sigma : ℝ}
    (ha : Summable fun n => ‖a n‖ * Real.exp (-mu n * sigma))
    {s : ℂ} (hs : sigma ≤ s.re) :
    Summable (fun n => a n * Complex.exp (-(mu n : ℂ) * s)) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ ha
  intro n
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
  have hle : -mu n * s.re ≤ -mu n * sigma := by
    nlinarith [hmu0 n]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (norm_nonneg _)

/-- The coefficient obtained by applying a finite translation operator to a generalized
Dirichlet series. -/
def translatedGeneralizedCoefficient
    (P : AddMonoidAlgebra ℂ ℂ) (mu : ℕ → ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n * translationChar (mu n) P

private lemma translatedCoefficient_weighted_eq_sum
    (P : AddMonoidAlgebra ℂ ℂ) (mu : ℕ → ℝ) (a : ℕ → ℂ) (x : ℝ) (n : ℕ) :
    translatedGeneralizedCoefficient P mu a n *
        Complex.exp (-(mu n : ℂ) * (x : ℂ)) =
      ∑ h ∈ P.coeff.support, P.coeff h *
        (a n * Complex.exp (-(mu n : ℂ) *
          ((x : ℂ) + h))) := by
  rw [translatedGeneralizedCoefficient, translationChar_apply]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h hh
  have hexp :
      -(mu n : ℂ) * ((x : ℂ) + h) =
        (-(mu n : ℂ) * h) + (-(mu n : ℂ) * (x : ℂ)) := by
    ring
  rw [hexp, Complex.exp_add]
  ring

/-- The character-twisted coefficient sequence is absolutely summable on the common shifted
half-plane. -/
theorem summable_translatedGeneralizedCoefficient
    {mu : ℕ → ℝ} (hmu : StrictMono mu) (hmu0 : 0 < mu 0)
    {a : ℕ → ℂ} {sigma : ℝ}
    (ha : Summable fun n => ‖a n‖ * Real.exp (-mu n * sigma))
    (P : AddMonoidAlgebra ℂ ℂ) :
    Summable (fun n => ‖translatedGeneralizedCoefficient P mu a n‖ *
      Real.exp (-mu n * finiteTranslationThreshold P sigma)) := by
  have hmu_pos (n : ℕ) : 0 < mu n :=
    hmu0.trans_le (hmu.monotone (Nat.zero_le n))
  have hshift (h : ℂ) (hh : h ∈ P.coeff.support) :
      Summable (fun n => P.coeff h * (a n * Complex.exp (-(mu n : ℂ) *
        ((finiteTranslationThreshold P sigma : ℂ) + h)))) := by
    apply Summable.mul_left
    exact summable_generalizedDirichletTerm_of_re_ge hmu_pos ha
      (finiteTranslationThreshold_le_re_add P sigma _ le_rfl hh)
  have hsum : Summable (fun n => ∑ h ∈ P.coeff.support, P.coeff h *
      (a n * Complex.exp (-(mu n : ℂ) *
        ((finiteTranslationThreshold P sigma : ℂ) + h)))) :=
    summable_sum fun h hh => hshift h hh
  have hweighted : Summable (fun n => translatedGeneralizedCoefficient P mu a n *
      Complex.exp (-(mu n : ℂ) * (finiteTranslationThreshold P sigma : ℂ))) :=
    hsum.congr fun n =>
      (translatedCoefficient_weighted_eq_sum P mu a
        (finiteTranslationThreshold P sigma) n).symm
  simpa [norm_mul, Complex.norm_exp] using hweighted.norm

/-- Finite translation acts termwise by the expected exponential character on every sufficiently
far-right point. -/
theorem finiteTranslationAction_generalizedDirichletSeries
    {mu : ℕ → ℝ} (hmu : StrictMono mu) (hmu0 : 0 < mu 0)
    {a : ℕ → ℂ} {sigma : ℝ}
    (ha : Summable fun n => ‖a n‖ * Real.exp (-mu n * sigma))
    (P : AddMonoidAlgebra ℂ ℂ) {x : ℝ}
    (hx : finiteTranslationThreshold P sigma ≤ x) :
    finiteTranslationAction P (generalizedDirichletSeries mu a) x =
      generalizedDirichletSeries mu (translatedGeneralizedCoefficient P mu a) x := by
  have hmu_pos (n : ℕ) : 0 < mu n :=
    hmu0.trans_le (hmu.monotone (Nat.zero_le n))
  have hsummable (h : ℂ) (hh : h ∈ P.coeff.support) :
      Summable (fun n => P.coeff h * (a n * Complex.exp (-(mu n : ℂ) * ((x : ℂ) + h)))) := by
    apply Summable.mul_left
    exact summable_generalizedDirichletTerm_of_re_ge hmu_pos ha
      (finiteTranslationThreshold_le_re_add P sigma x hx hh)
  rw [finiteTranslationAction, generalizedDirichletSeries]
  simp_rw [generalizedDirichletSeries, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum hsummable]
  apply tsum_congr
  intro n
  exact (translatedCoefficient_weighted_eq_sum P mu a x n).symm

/-- **Literal analytic ray-complete faithfulness.**  Suppose an absolutely convergent generalized
Dirichlet carrier contains, with nonzero coefficient, every positive multiple of each ray in an
infinite pairwise-incommensurable family.  If a finite translation operator sends that carrier to a
rational function on a right half-plane, then the operator is zero.

The proof supplies both analytic implications omitted by the character-only formulation:
exponential decay forces the rational output to vanish, and generalized-Dirichlet uniqueness then
forces every ray character of the operator to vanish. -/
theorem rayComplete_translation_rational_forces_zero
    {ι : Type*} [Infinite ι]
    {mu : ℕ → ℝ} (hmu : StrictMono mu) (hmu0 : 0 < mu 0)
    {a : ℕ → ℂ} {sigma : ℝ}
    (ha : Summable fun n => ‖a n‖ * Real.exp (-mu n * sigma))
    (l : ι → ℝ) (hpos : ∀ p, 0 < l p)
    (hirr : ∀ p q, p ≠ q → Irrational (l p / l q))
    (hoccurs : ∀ (p : ι) (m : ℕ), 1 ≤ m →
      ∃ n : ℕ, mu n = (m : ℝ) * l p ∧ a n ≠ 0)
    (P : AddMonoidAlgebra ℂ ℂ) (R : RatFunc ℂ)
    (hRat : ∀ x : ℝ, finiteTranslationThreshold P sigma ≤ x →
      finiteTranslationAction P (generalizedDirichletSeries mu a) x =
        RatFunc.eval (RingHom.id ℂ) (x : ℂ) R) :
    P = 0 := by
  let tau : ℝ := finiteTranslationThreshold P sigma
  let b : ℕ → ℂ := translatedGeneralizedCoefficient P mu a
  have hb : Summable (fun n => ‖b n‖ * Real.exp (-mu n * tau)) := by
    simpa [b, tau] using summable_translatedGeneralizedCoefficient hmu hmu0 ha P
  let S : ℝ := ∑' n, ‖b n‖ * Real.exp (-mu n * tau)
  let C : ℝ := S * Real.exp (mu 0 * tau)
  have hS : 0 ≤ S := by
    exact tsum_nonneg fun n => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hC : 0 ≤ C := mul_nonneg hS (Real.exp_pos _).le
  have hbound : ∀ᶠ x : ℝ in atTop,
      ‖R.num.eval (x : ℂ) / R.denom.eval (x : ℂ)‖ ≤
        C * Real.exp (-mu 0 * x) := by
    filter_upwards [eventually_ge_atTop tau] with x hx
    have haction := finiteTranslationAction_generalizedDirichletSeries hmu hmu0 ha P hx
    have hdecay := norm_generalizedDirichletSeries_real_le hmu.monotone hmu0 hb hx
    have hratEval :
        R.num.eval (x : ℂ) / R.denom.eval (x : ℂ) =
          finiteTranslationAction P (generalizedDirichletSeries mu a) x := by
      rw [hRat x hx]
      simp only [RatFunc.eval, Polynomial.eval₂_id]
    have hdecay' :
        ‖generalizedDirichletSeries mu (translatedGeneralizedCoefficient P mu a) x‖ ≤
          S * Real.exp (-mu 0 * (x - tau)) := by
      simpa only [b, S] using hdecay
    have hsplit : Real.exp (-mu 0 * (x - tau)) =
        Real.exp (mu 0 * tau) * Real.exp (-mu 0 * x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hratEval, haction]
    calc
      ‖generalizedDirichletSeries mu (translatedGeneralizedCoefficient P mu a) ↑x‖ ≤
          S * Real.exp (-mu 0 * (x - tau)) := hdecay'
      _ = C * Real.exp (-mu 0 * x) := by rw [hsplit]; simp only [C]; ring
  have hnum : R.num = 0 :=
    complexPolynomial_eq_zero_of_div_exponential_bound
      (RatFunc.denom_ne_zero R) hmu0 hC hbound
  have hR : R = 0 := RatFunc.num_eq_zero_iff.mp hnum
  have hseriesZero :
      (fun x : ℝ => generalizedDirichletSeries mu b x) =ᶠ[atTop] 0 := by
    filter_upwards [eventually_ge_atTop tau] with x hx
    calc
      generalizedDirichletSeries mu b x =
          finiteTranslationAction P (generalizedDirichletSeries mu a) x :=
        (finiteTranslationAction_generalizedDirichletSeries hmu hmu0 ha P hx).symm
      _ = RatFunc.eval (RingHom.id ℂ) (x : ℂ) R := hRat x hx
      _ = 0 := by simp [hR]
  have hcoeff : ∀ n, b n = 0 :=
    generalizedDirichletSeries_coeff_eq_zero_of_absolutelySummable_at
      hmu hmu0 hb hseriesZero
  apply translationChar_moments_eq_zero l hpos hirr P
  intro p m hm
  obtain ⟨n, hfreq, hane⟩ := hoccurs p m hm
  have hn := hcoeff n
  simp only [b, translatedGeneralizedCoefficient] at hn
  rw [hfreq] at hn
  exact (mul_eq_zero.mp hn).resolve_left hane

/-- A finite translation operator rationalizes a generalized Dirichlet carrier when its action
agrees with one rational function on the common right half-plane. -/
def RationalizesGeneralizedDirichletCarrier
    (mu : ℕ → ℝ) (a : ℕ → ℂ) (sigma : ℝ)
    (P : AddMonoidAlgebra ℂ ℂ) : Prop :=
  ∃ R : RatFunc ℂ, ∀ x : ℝ, finiteTranslationThreshold P sigma ≤ x →
    finiteTranslationAction P (generalizedDirichletSeries mu a) x =
      RatFunc.eval (RingHom.id ℂ) (x : ℂ) R

/-- Exact analytic-constraint classification: for a ray-complete carrier, the rationalizing set is
the singleton zero operator.  This is the literal `I_an(F) = 0`, rather than the character-kernel
proxy. -/
theorem rationalizesGeneralizedDirichletCarrier_iff_eq_zero
    {ι : Type*} [Infinite ι]
    {mu : ℕ → ℝ} (hmu : StrictMono mu) (hmu0 : 0 < mu 0)
    {a : ℕ → ℂ} {sigma : ℝ}
    (ha : Summable fun n => ‖a n‖ * Real.exp (-mu n * sigma))
    (l : ι → ℝ) (hpos : ∀ p, 0 < l p)
    (hirr : ∀ p q, p ≠ q → Irrational (l p / l q))
    (hoccurs : ∀ (p : ι) (m : ℕ), 1 ≤ m →
      ∃ n : ℕ, mu n = (m : ℝ) * l p ∧ a n ≠ 0)
    (P : AddMonoidAlgebra ℂ ℂ) :
    RationalizesGeneralizedDirichletCarrier mu a sigma P ↔ P = 0 := by
  constructor
  · rintro ⟨R, hR⟩
    exact rayComplete_translation_rational_forces_zero
      hmu hmu0 ha l hpos hirr hoccurs P R hR
  · rintro rfl
    refine ⟨0, ?_⟩
    intro x hx
    rw [finiteTranslationAction, RatFunc.eval_zero]
    apply Finset.sum_eq_zero
    intro h hh
    exact mul_eq_zero.mpr (Or.inl rfl)

end GaloisForLFunctions.RHTower
