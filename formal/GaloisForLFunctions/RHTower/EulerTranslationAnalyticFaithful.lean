import GaloisForLFunctions.RHTower.RayCompletePoincareFlatness
import GaloisForLFunctions.RHTower.EulerNormalizedTraceHankelFarRight

/-!
# Literal analytic translation faithfulness of the Euler derivative tower

We enumerate all integers `n ≥ 2` by `n + 2`.  The frequencies `log (n+2)` are strictly
increasing and the von-Mangoldt coefficient is nonzero at every prime power.  Logarithmic weights
give every derivative of the Euler logarithmic-derivative carrier.  The general analytic theorem
therefore applies at every derivative order.
-/

open Complex Filter Topology LSeries

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Increasing positive frequencies enumerating the ordinary Dirichlet monomials from `2`
onwards. -/
def eulerGeneralizedFrequency (n : ℕ) : ℝ := Real.log (((n + 2 : ℕ) : ℝ))

/-- Coefficients of the `k`-th derivative of the Euler logarithmic-derivative carrier, with the
irrelevant zero terms at `0` and `1` omitted. -/
def eulerGeneralizedCoefficient (k n : ℕ) : ℂ :=
  (-1 : ℂ) ^ k * RHTower.vonMangoldtLogCoeff k (n + 2)

theorem eulerGeneralizedFrequency_strictMono : StrictMono eulerGeneralizedFrequency := by
  intro n m hnm
  apply Real.strictMonoOn_log
  · exact Set.mem_Ioi.mpr (by positivity)
  · exact Set.mem_Ioi.mpr (by positivity)
  · exact_mod_cast Nat.add_lt_add_right hnm 2

theorem eulerGeneralizedFrequency_zero_pos : 0 < eulerGeneralizedFrequency 0 := by
  simpa [eulerGeneralizedFrequency] using Real.log_pos (by norm_num : (1 : ℝ) < 2)

private theorem eulerLogCoeff_absolutelySummable
    (k : ℕ) {sigma : ℝ} (hsigma : 1 < sigma) :
    LSeriesSummable (LSeries.logMul^[k]
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) (sigma : ℂ) := by
  let beta : ℝ := (1 + sigma) / 2
  have hbeta1 : 1 < beta := by dsimp [beta]; linarith
  have hbetasigma : beta < sigma := by dsimp [beta]; linarith
  have hbase := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (beta : ℂ)) (by simpa using hbeta1)
  apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
  rw [LSeries.absicssaOfAbsConv_logPowMul]
  exact hbase.abscissaOfAbsConv_le.trans_lt (by simpa using hbetasigma)

/-- Absolute convergence of every derivative coefficient sequence on every half-plane
`sigma > 1`. -/
theorem summable_eulerGeneralizedCoefficient
    (k : ℕ) {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun n => ‖eulerGeneralizedCoefficient k n‖ *
      Real.exp (-eulerGeneralizedFrequency n * sigma)) := by
  have hs := summable_norm_iff.mpr (eulerLogCoeff_absolutelySummable k hsigma)
  have htail : Summable (fun n =>
      ‖LSeries.term (LSeries.logMul^[k]
        (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))) (sigma : ℂ) (n + 2)‖) :=
    hs.comp_injective (fun a b h => by omega)
  refine htail.congr (fun n => ?_)
  rw [LSeries.norm_term_eq, if_neg (by omega : n + 2 ≠ 0)]
  have hpos : (0 : ℝ) < (n + 2 : ℕ) := by positivity
  have hexp : Real.exp (-eulerGeneralizedFrequency n * sigma) =
      ((n + 2 : ℕ) : ℝ) ^ (-sigma) := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast hpos)]
    simp only [eulerGeneralizedFrequency]
    congr 1
    ring
  rw [eulerGeneralizedCoefficient, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, hexp, Real.rpow_neg (by positivity : (0 : ℝ) ≤ (n + 2 : ℕ)), div_eq_mul_inv]
  rfl

/-- Every positive multiple of every prime-log ray occurs with a nonzero coefficient at every
derivative order. -/
theorem eulerGeneralizedCoefficient_ray_complete
    (k : ℕ) (p : Nat.Primes) (m : ℕ) (hm : 1 ≤ m) :
    ∃ n : ℕ,
      eulerGeneralizedFrequency n = (m : ℝ) * Real.log (p : ℕ) ∧
      eulerGeneralizedCoefficient k n ≠ 0 := by
  have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
  have hpow2 : 2 ≤ (p : ℕ) ^ m :=
    hp2.trans (Nat.le_pow (by omega : 0 < m))
  refine ⟨(p : ℕ) ^ m - 2, ?_, ?_⟩
  · rw [eulerGeneralizedFrequency, Nat.sub_add_cancel hpow2]
    rw [Nat.cast_pow, Real.log_pow]
  · rw [eulerGeneralizedCoefficient, RHTower.vonMangoldtLogCoeff_apply,
      Nat.sub_add_cancel hpow2, ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime p.2]
    apply mul_ne_zero
    · exact pow_ne_zero _ (by norm_num)
    · apply mul_ne_zero
      · apply pow_ne_zero
        rw [← Complex.natCast_log]
        exact Complex.ofReal_ne_zero.mpr
          (Real.log_pos (by exact_mod_cast (show 1 < (p : ℕ) ^ m by omega))).ne'
      · exact Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast p.2.one_lt)).ne'

/-- Literal Euler flat-tower law: no nonzero finite complex translation combination sends the
`k`-th von-Mangoldt/logarithmic derivative carrier to a rational function. -/
theorem eulerDerivative_rationalizes_iff_eq_zero
    (k : ℕ) {sigma : ℝ} (hsigma : 1 < sigma)
    (P : AddMonoidAlgebra ℂ ℂ) :
    RationalizesGeneralizedDirichletCarrier
      eulerGeneralizedFrequency (eulerGeneralizedCoefficient k) sigma P ↔ P = 0 := by
  apply rationalizesGeneralizedDirichletCarrier_iff_eq_zero
    eulerGeneralizedFrequency_strictMono eulerGeneralizedFrequency_zero_pos
    (summable_eulerGeneralizedCoefficient k hsigma)
    (fun p : Nat.Primes => Real.log (p : ℕ))
  · intro p
    exact Real.log_pos (by exact_mod_cast p.2.one_lt)
  · intro p q hpq
    exact irrational_log_ratio q.2 p.2 (fun h => hpq (Subtype.ext h.symm))
  · intro p m hm
    exact eulerGeneralizedCoefficient_ray_complete k p m hm

/-- Every Euler derivative carrier and each of its finite translations has zero inverse-power
Poincare shadow. -/
theorem eulerDerivativeTranslation_hasZeroInversePowerPoincareShadow
    (k : ℕ) {sigma : ℝ} (hsigma : 1 < sigma)
    (P : AddMonoidAlgebra ℂ ℂ) :
    HasZeroInversePowerPoincareShadow (fun x : ℝ =>
      finiteTranslationAction P
        (generalizedDirichletSeries eulerGeneralizedFrequency
          (eulerGeneralizedCoefficient k)) x) :=
  finiteTranslationAction_hasZeroInversePowerPoincareShadow
    eulerGeneralizedFrequency_strictMono eulerGeneralizedFrequency_zero_pos
    (summable_eulerGeneralizedCoefficient k hsigma) P

private theorem eulerGeneralizedTerm_eq_lSeriesTerm
    (k n : ℕ) (s : ℂ) :
    eulerGeneralizedCoefficient k n *
        Complex.exp (-(eulerGeneralizedFrequency n : ℂ) * s) =
      (-1 : ℂ) ^ k * LSeries.term
        (LSeries.logMul^[k] (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)))
        s (n + 2) := by
  have hn0 : ((n + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
  have hlog : Complex.log (((n + 2 : ℕ) : ℂ)) =
      ((Real.log ((n + 2 : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.natCast_log]
  rw [eulerGeneralizedCoefficient, eulerGeneralizedFrequency,
    LSeries.term_of_ne_zero (by omega : n + 2 ≠ 0),
    Complex.cpow_def_of_ne_zero hn0, hlog, div_eq_mul_inv, ← Complex.exp_neg]
  rw [RHTower.vonMangoldtLogCoeff]
  ring

/-- The shifted generalized series is exactly the logarithmically weighted von-Mangoldt L-series. -/
theorem eulerGeneralizedDirichletSeries_eq_weightedLSeries
    (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    generalizedDirichletSeries eulerGeneralizedFrequency
        (eulerGeneralizedCoefficient k) s =
      (-1 : ℂ) ^ k *
        LSeries (LSeries.logMul^[k]
          (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s := by
  let beta : ℝ := (1 + s.re) / 2
  have hbeta1 : 1 < beta := by dsimp [beta]; linarith
  have hbetas : beta < s.re := by dsimp [beta]; linarith
  have hbase := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (beta : ℂ)) (by simpa using hbeta1)
  have habs : LSeries.abscissaOfAbsConv
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) < s.re :=
    hbase.abscissaOfAbsConv_le.trans_lt (by exact_mod_cast hbetas)
  have hsum : LSeriesSummable
      (LSeries.logMul^[k] (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s := by
    apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
    rw [LSeries.absicssaOfAbsConv_logPowMul]
    exact habs
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have hhead : ∑ n ∈ Finset.range 2,
      LSeries.term (LSeries.logMul^[k]
        (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))) s n = 0 := by
    simp [Finset.sum_range_succ, LSeries.term_def,
      show (LSeries.logMul^[k] (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))) 1 = 0 by
        exact RHTower.vonMangoldtLogCoeff_one k]
  rw [generalizedDirichletSeries, LSeries, ← hsplit, hhead, zero_add, ← tsum_mul_left]
  apply tsum_congr
  intro n
  exact eulerGeneralizedTerm_eq_lSeriesTerm k n s

/-- The generalized carrier used in the analytic proof is the literal `k`-th derivative of the
von-Mangoldt L-series throughout `Re s > 1`. -/
theorem eulerGeneralizedDirichletSeries_eq_iteratedDeriv
    (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    generalizedDirichletSeries eulerGeneralizedFrequency
        (eulerGeneralizedCoefficient k) s =
      iteratedDeriv k
        (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s := by
  let beta : ℝ := (1 + s.re) / 2
  have hbeta1 : 1 < beta := by dsimp [beta]; linarith
  have hbetas : beta < s.re := by dsimp [beta]; linarith
  have hbase := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (beta : ℂ)) (by simpa using hbeta1)
  have habs : LSeries.abscissaOfAbsConv
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) < s.re :=
    hbase.abscissaOfAbsConv_le.trans_lt (by exact_mod_cast hbetas)
  rw [LSeries_iteratedDeriv k habs]
  exact eulerGeneralizedDirichletSeries_eq_weightedLSeries k hs

/-- Literal Euler derivative rationalization, stated directly for the iterated derivative of the
von-Mangoldt L-series rather than for its generalized-series presentation. -/
theorem eulerLSeriesDerivative_rationalizes_iff_eq_zero
    (k : ℕ) {sigma : ℝ} (hsigma : 1 < sigma)
    (P : AddMonoidAlgebra ℂ ℂ) :
    (∃ R : RatFunc ℂ, ∀ x : ℝ, finiteTranslationThreshold P sigma ≤ x →
      finiteTranslationAction P
          (iteratedDeriv k
            (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)))) x =
        RatFunc.eval (RingHom.id ℂ) (x : ℂ) R) ↔ P = 0 := by
  constructor
  · rintro ⟨R, hR⟩
    apply (eulerDerivative_rationalizes_iff_eq_zero k hsigma P).mp
    refine ⟨R, ?_⟩
    intro x hx
    rw [← hR x hx]
    apply Finset.sum_congr rfl
    intro h hh
    congr 1
    apply eulerGeneralizedDirichletSeries_eq_iteratedDeriv
    exact hsigma.trans_le (finiteTranslationThreshold_le_re_add P sigma x hx hh)
  · rintro rfl
    refine ⟨0, ?_⟩
    intro x hx
    rw [finiteTranslationAction, RatFunc.eval_zero]
    apply Finset.sum_eq_zero
    intro h hh
    exact mul_eq_zero.mpr (Or.inl rfl)

/-- The canonical Euler logarithmic-derivative carrier `E = -ζ'/ζ`. -/
def eulerLogDerivative (s : ℂ) : ℂ :=
  -deriv riemannZeta s / riemannZeta s

/-- On `Re s > 1`, every derivative of the canonical `-ζ'/ζ` carrier is the corresponding
derivative of its von-Mangoldt L-series. -/
theorem iteratedDeriv_eulerLogDerivative_eq_vonMangoldtLSeries
    (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv k eulerLogDerivative s =
      iteratedDeriv k
        (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s := by
  have hopen : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hev : eulerLogDerivative =ᶠ[nhds s]
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact (zeta_logDeriv_frequencies_weld hz).1
  exact hev.iteratedDeriv_eq k

/-- Canonical Euler flat-tower law `(23)`: for every derivative order, the analytic translation
constraint set of `E^(k)` is exactly the zero operator. -/
theorem eulerLogDerivative_iterated_rationalizes_iff_eq_zero
    (k : ℕ) {sigma : ℝ} (hsigma : 1 < sigma)
    (P : AddMonoidAlgebra ℂ ℂ) :
    (∃ R : RatFunc ℂ, ∀ x : ℝ, finiteTranslationThreshold P sigma ≤ x →
      finiteTranslationAction P (iteratedDeriv k eulerLogDerivative) x =
        RatFunc.eval (RingHom.id ℂ) (x : ℂ) R) ↔ P = 0 := by
  constructor
  · rintro ⟨R, hR⟩
    apply (eulerLSeriesDerivative_rationalizes_iff_eq_zero k hsigma P).mp
    refine ⟨R, ?_⟩
    intro x hx
    rw [← hR x hx]
    apply Finset.sum_congr rfl
    intro h hh
    congr 1
    exact (iteratedDeriv_eulerLogDerivative_eq_vonMangoldtLSeries k
      (hsigma.trans_le (finiteTranslationThreshold_le_re_add P sigma x hx hh))).symm
  · rintro rfl
    refine ⟨0, ?_⟩
    intro x hx
    rw [finiteTranslationAction, RatFunc.eval_zero]
    apply Finset.sum_eq_zero
    intro h hh
    exact mul_eq_zero.mpr (Or.inl rfl)

end GaloisForLFunctions.RHTower
