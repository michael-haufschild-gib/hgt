import GaloisForLFunctions.BiScaleUncertainty.AnnularCorrelationTransport
import Mathlib.NumberTheory.Chebyshev
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Signed prime–polar coupling through the Chebyshev discrepancy

Finite logarithmic windows retain every von Mangoldt atom and both branches of
the polar density. Annular correlation transport supplies a continuous derivative
for every compact continuous source. Exact Stieltjes summation then identifies
the signed pairing with Chebyshev work, including both endpoints, up to an
explicit local Krein transport cost.
-/
open MeasureTheory Set
open scoped BigOperators CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

def cutoff (N : ℕ) : ℝ := Real.log (N + 2 : ℕ)
def step (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (N+2), if Real.log (n : ℝ) ≤ x then ArithmeticFunction.vonMangoldt n else 0

theorem step_eq (N : ℕ) {x : ℝ} (hx : x ≤ cutoff N) :
    step N x = Chebyshev.psi (Real.exp x) := by
  have hfloor : ⌊Real.exp x⌋₊ ≤ N+2 := by
    apply Nat.floor_le_of_le
    have he := Real.exp_le_exp.mpr hx
    rw [cutoff, Real.exp_log (by positivity)] at he
    exact he
  unfold step Chebyshev.psi
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hn, _⟩, hx⟩
      exact ⟨hn, (Nat.le_floor_iff (Real.exp_pos x).le).mpr
        ((Real.log_le_iff_le_exp (by exact_mod_cast (show 0 < n from hn))).mp hx)⟩
    · rintro ⟨hn, hx⟩
      refine ⟨⟨hn, hx.trans hfloor⟩, ?_⟩
      exact (Real.log_le_iff_le_exp (by exact_mod_cast hn)).mpr
        ((Nat.le_floor_iff (Real.exp_pos x).le).mp hx)
  · intro _ _; rfl


theorem cutoff_nonneg (N : ℕ) : 0 ≤ cutoff N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N+2 by omega))

theorem node_bounds (N n : ℕ) (hn : n ∈ Finset.Icc 1 (N+2)) :
    0 ≤ Real.log (n : ℝ) ∧ Real.log (n : ℝ) ≤ cutoff N := by
  have hn' := Finset.mem_Icc.mp hn
  exact ⟨Real.log_nonneg (by exact_mod_cast hn'.1),
    Real.log_le_log (by exact_mod_cast (show 0 < n from hn'.1)) (by exact_mod_cast hn'.2)⟩

private theorem integrable_mul_step (q : ℝ → ℝ) (hq : Continuous q) (N : ℕ) :
    IntegrableOn (fun x => q x * step N x) (Icc 0 (cutoff N)) := by
  simp only [step, Finset.mul_sum]
  apply integrable_finsetSum
  intro n _
  have hi := (hq.mul_const (ArithmeticFunction.vonMangoldt n)).integrableOn_Icc
    (μ := volume) (a := (0 : ℝ)) (b := cutoff N)
  apply (Integrable.indicator hi (s := Ici (Real.log (n : ℝ))) measurableSet_Ici).congr
  filter_upwards [] with x
  by_cases hx : Real.log (n : ℝ) ≤ x <;> simp [Set.indicator, hx]

private theorem integral_mul_step (g q : ℝ → ℝ) (hq : Continuous q)
    (hg : ∀ x, HasDerivAt g (q x) x) (N : ℕ) :
    (∫ x in Icc 0 (cutoff N), q x * step N x) =
      ∑ n ∈ Finset.Icc 1 (N+2),
        (g (cutoff N) - g (Real.log n)) * ArithmeticFunction.vonMangoldt n := by
  simp only [step, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    have ht := node_bounds N n hn
    have heq : (fun x => q x * (if Real.log (n : ℝ) ≤ x then
        ArithmeticFunction.vonMangoldt n else 0)) =
        (Ici (Real.log n)).indicator (fun x => q x * ArithmeticFunction.vonMangoldt n) := by
      funext x
      by_cases hx : Real.log (n : ℝ) ≤ x <;> simp [hx, Set.indicator]
    rw [heq, setIntegral_indicator measurableSet_Ici]
    have hs : Icc (0 : ℝ) (cutoff N) ∩ Ici (Real.log n) = Icc (Real.log n) (cutoff N) := by
      ext x
      simp only [mem_inter_iff, mem_Icc, mem_Ici]
      constructor
      · rintro ⟨⟨_, hL⟩, ht⟩; exact ⟨ht, hL⟩
      · rintro ⟨hx, hL⟩; exact ⟨⟨ht.1.trans hx, hL⟩, hx⟩
    rw [hs, integral_mul_const, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ht.2,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hg x)
        (hq.intervalIntegrable _ _)]
  · intro n _
    have hi := (hq.mul_const (ArithmeticFunction.vonMangoldt n)).integrableOn_Icc
      (μ := volume) (a := (0 : ℝ)) (b := cutoff N)
    apply (Integrable.indicator hi (s := Ici (Real.log (n : ℝ))) measurableSet_Ici).congr
    filter_upwards [] with x
    by_cases hx : Real.log (n : ℝ) ≤ x <;> simp [Set.indicator, hx]


def logError (x : ℝ) : ℝ := Chebyshev.psi (Real.exp x) - Real.exp x

theorem integrable_mul_logError (q : ℝ → ℝ) (hq : Continuous q) (N : ℕ) :
    IntegrableOn (fun x => q x * logError x) (Icc 0 (cutoff N)) := by
  have hi := (integrable_mul_step q hq N).sub
    ((hq.mul Real.continuous_exp).integrableOn_Icc (μ := volume))
  apply hi.congr_fun _ measurableSet_Icc
  intro x hx
  dsimp only [Pi.mul_apply, Pi.sub_apply]
  rw [step_eq N hx.2]
  simp only [logError, mul_sub]

private theorem abel_error (g q : ℝ → ℝ) (hq : Continuous q)
    (hg : ∀ x, HasDerivAt g (q x) x) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 (N+2), g (Real.log n) * ArithmeticFunction.vonMangoldt n) -
        (∫ x in Icc 0 (cutoff N), g x * Real.exp x) =
      g 0 + g (cutoff N) * logError (cutoff N) -
        ∫ x in Icc 0 (cutoff N), q x * logError x := by
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
  have hi := integral_mul_step g q hq hg N
  have hc := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := cutoff N) hgc.continuousOn Real.continuous_exp.continuousOn
    (fun x _ => hg x) (fun x _ => Real.hasDerivAt_exp x)
    (hq.intervalIntegrable _ _) (Real.continuous_exp.intervalIntegrable _ _)
  rw [intervalIntegral.integral_of_le (cutoff_nonneg N),
    intervalIntegral.integral_of_le (cutoff_nonneg N), Real.exp_zero, mul_one] at hc
  rw [← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc] at hc
  have hstep : step N (cutoff N) = ∑ n ∈ Finset.Icc 1 (N+2),
      ArithmeticFunction.vonMangoldt n := by
    apply Finset.sum_congr rfl
    intro n hn
    exact if_pos (node_bounds N n hn).2
  have he : (∫ x in Icc 0 (cutoff N), q x * logError x) =
      (∫ x in Icc 0 (cutoff N), q x * step N x) -
      ∫ x in Icc 0 (cutoff N), q x * Real.exp x := by
    have hqe : IntegrableOn (fun x => q x * Real.exp x) (Icc 0 (cutoff N)) :=
      (hq.mul Real.continuous_exp).integrableOn_Icc
    rw [← integral_sub (integrable_mul_step q hq N) hqe]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    dsimp only
    rw [step_eq N hx.2]
    simp only [logError, mul_sub]
  rw [he, logError, ← step_eq N le_rfl, hstep]
  simp_rw [sub_mul] at hi
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hi
  linarith only [hi, hc]


/-- The critical von Mangoldt atom weight, retaining its actual arithmetic value. -/
def primeWeight (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n / Real.sqrt n

/-- The full positive polar density, including both exponential branches. -/
def polarDensity (x : ℝ) : ℝ := 2 * Real.cosh (x / 2)

def pairing (N : ℕ) (h : ℝ → ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 (N+2), primeWeight n * h (Real.log n)) -
    ∫ x in Icc 0 (cutoff N), polarDensity x * h x

def mass (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 (N+2), primeWeight n) +
    ∫ x in Icc 0 (cutoff N), polarDensity x

theorem primeWeight_nonneg (n : ℕ) : 0 ≤ primeWeight n :=
  div_nonneg (ArithmeticFunction.vonMangoldt_nonneg) (Real.sqrt_nonneg _)

theorem polarDensity_nonneg (x : ℝ) : 0 ≤ polarDensity x :=
  mul_nonneg (by norm_num) (Real.cosh_pos _).le

theorem continuous_polarDensity : Continuous polarDensity := by unfold polarDensity; fun_prop

theorem mass_nonneg (N : ℕ) : 0 ≤ mass N :=
  add_nonneg (Finset.sum_nonneg fun n _ => primeWeight_nonneg n)
    (integral_nonneg fun x => polarDensity_nonneg x)

private theorem exp_neg_log_half (n : ℕ) (hn : 0 < n) :
    Real.exp (-Real.log (n : ℝ) / 2) = (Real.sqrt n)⁻¹ := by
  rw [neg_div, Real.exp_neg, exp_half_log_eq_sqrt (by exact_mod_cast hn)]

private theorem pairing_eq_error (H V : ℝ → ℝ) (hH : Continuous H) (hV : Continuous V)
    (hd : ∀ x, HasDerivAt H (V x) x) (N : ℕ) :
    pairing N H = H 0 + Real.exp (-cutoff N / 2) * H (cutoff N) * logError (cutoff N) -
      (∫ x in Icc 0 (cutoff N),
        (Real.exp (-x / 2) * (V x - H x / 2)) * logError x) -
      ∫ x in Icc 0 (cutoff N), Real.exp (-x / 2) * H x := by
  let g := fun x => Real.exp (-x / 2) * H x
  let q := fun x => Real.exp (-x / 2) * (V x - H x / 2)
  have hgc : Continuous g := by dsimp [g]; fun_prop
  have hqc : Continuous q := by dsimp [q]; fun_prop
  have hgd (x : ℝ) : HasDerivAt g (q x) x := by
    dsimp [g, q]
    convert (((hasDerivAt_id x).neg.div_const 2).exp.mul (hd x)) using 1 <;>
      first | rfl | (simp only [Pi.neg_apply, id_eq]; ring)
  have hab := abel_error g q hqc hgd N
  have hs : (∑ n ∈ Finset.Icc 1 (N+2), g (Real.log n) * ArithmeticFunction.vonMangoldt n) =
      ∑ n ∈ Finset.Icc 1 (N+2), primeWeight n * H (Real.log n) := by
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [g, primeWeight]
    rw [exp_neg_log_half n (Finset.mem_Icc.mp hn).1]
    ring
  have hp : (∫ x in Icc 0 (cutoff N), polarDensity x * H x) =
      (∫ x in Icc 0 (cutoff N), g x * Real.exp x) +
      ∫ x in Icc 0 (cutoff N), Real.exp (-x / 2) * H x := by
    have hgexp : IntegrableOn (fun x => g x * Real.exp x) (Icc 0 (cutoff N)) :=
      (hgc.mul Real.continuous_exp).integrableOn_Icc
    have hneg : IntegrableOn (fun x => Real.exp (-x / 2) * H x) (Icc 0 (cutoff N)) :=
      hgc.integrableOn_Icc
    rw [← integral_add hgexp hneg]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    have he : Real.exp (-x / 2) * Real.exp x = Real.exp (x / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp [g, polarDensity]
    rw [Real.cosh_eq]
    rw [show -(x / 2) = -x / 2 by ring]
    nlinarith only [congrArg (fun z : ℝ => z * H x) he]
  rw [hs] at hab
  dsimp [g, q] at hab
  simp only [neg_zero, zero_div, Real.exp_zero, one_mul] at hab
  unfold pairing
  rw [hp]
  linarith only [hab]

/-- Exact Chebyshev transport for the constructed differentiable correlation average. -/
theorem pairing_correlationAverage_eq (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    pairing N (correlationAverage f a b) =
      correlationAverage f a b 0 +
        Real.exp (-cutoff N / 2) * correlationAverage f a b (cutoff N) * logError (cutoff N) -
      (∫ x in Icc 0 (cutoff N),
        (Real.exp (-x / 2) * (correlationAverageSlope f a b x - correlationAverage f a b x / 2)) *
          logError x) -
      ∫ x in Icc 0 (cutoff N), Real.exp (-x / 2) * correlationAverage f a b x :=
  pairing_eq_error _ _ (continuous_correlationAverage f a b)
    (continuous_correlationAverageSlope f a b) (hasDerivAt_correlationAverage f a b) N


private theorem abs_pairing_sub_le (H K : ℝ → ℝ) (hH : Continuous H) (hK : Continuous K)
    (B : ℝ) (hb : ∀ x, |H x - K x| ≤ B) (N : ℕ) :
    |pairing N H - pairing N K| ≤ mass N * B := by
  have hiH : IntegrableOn (fun x => polarDensity x * H x) (Icc 0 (cutoff N)) :=
    (continuous_polarDensity.mul hH).integrableOn_Icc
  have hiK : IntegrableOn (fun x => polarDensity x * K x) (Icc 0 (cutoff N)) :=
    (continuous_polarDensity.mul hK).integrableOn_Icc
  have he : pairing N H - pairing N K =
      (∑ n ∈ Finset.Icc 1 (N+2), primeWeight n * (H (Real.log n) - K (Real.log n))) -
      ∫ x in Icc 0 (cutoff N), polarDensity x * (H x - K x) := by
    simp only [pairing, mul_sub, Finset.sum_sub_distrib, integral_sub hiH hiK]
    ring
  have hs : |∑ n ∈ Finset.Icc 1 (N+2), primeWeight n * (H (Real.log n) - K (Real.log n))| ≤
      (∑ n ∈ Finset.Icc 1 (N+2), primeWeight n) * B := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 (N+2), |primeWeight n * (H (Real.log n) - K (Real.log n))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 (N+2), primeWeight n * B := by
        apply Finset.sum_le_sum
        intro n _
        rw [abs_mul, abs_of_nonneg (primeWeight_nonneg n)]
        exact mul_le_mul_of_nonneg_left (hb _) (primeWeight_nonneg n)
      _ = _ := (Finset.sum_mul ..).symm
  have hi : |∫ x in Icc 0 (cutoff N), polarDensity x * (H x - K x)| ≤
      (∫ x in Icc 0 (cutoff N), polarDensity x) * B := by
    have hmajor : IntegrableOn (fun x => polarDensity x * B) (Icc 0 (cutoff N)) :=
      (continuous_polarDensity.mul_const B).integrableOn_Icc
    have hi := norm_integral_le_of_norm_le (f := fun x => polarDensity x * (H x - K x)) hmajor
      (Filter.Eventually.of_forall fun x => ?_)
    · simpa only [Real.norm_eq_abs, integral_mul_const] using hi
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (polarDensity_nonneg x)]
      exact mul_le_mul_of_nonneg_left (hb x) (polarDensity_nonneg x)
  rw [he]
  calc
    _ ≤ |∑ n ∈ Finset.Icc 1 (N+2), primeWeight n * (H (Real.log n) - K (Real.log n))| +
        |∫ x in Icc 0 (cutoff N), polarDensity x * (H x - K x)| := abs_sub _ _
    _ ≤ _ := by dsimp [mass]; nlinarith only [hs, hi]

/-- Explicit Chebyshev work, with both finite-window boundary contributions and polar shadow. -/
def chebyshevWork (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) : ℝ :=
  correlationAverage f a b 0 +
    Real.exp (-cutoff N / 2) * correlationAverage f a b (cutoff N) * logError (cutoff N) -
  (∫ x in Icc 0 (cutoff N),
    (Real.exp (-x / 2) * (correlationAverageSlope f a b x - correlationAverage f a b x / 2)) *
      logError x) -
  ∫ x in Icc 0 (cutoff N), Real.exp (-x / 2) * correlationAverage f a b x

/-- Direct signed prime–polar coupling for every compact continuous source. -/
theorem abs_pairing_sub_chebyshevWork_le (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    |pairing N (autocorr f) - chebyshevWork f a b N| ≤
      mass N * correlationTransportCost f a b := by
  have he : pairing N (correlationAverage f a b) = chebyshevWork f a b N :=
    pairing_correlationAverage_eq f a b N
  rw [← he]
  apply abs_pairing_sub_le _ _ (continuous_autocorr_compact f)
    (continuous_correlationAverage f a b)
  intro x
  rw [abs_sub_comm]
  exact abs_correlationAverage_sub_le f a b x

/-- The direct coupling paid by local Lévy energy and the linearly vanishing reciprocal weight. -/
theorem abs_pairing_sub_chebyshevWork_le_levy (f : C_c(ℝ, ℝ)) (a b c : ℝ) (N : ℕ) :
    |pairing N (autocorr f) - chebyshevWork f a b N| ≤
      mass N * (Real.exp c * (∫ y in Real.exp a..Real.exp a + Real.exp b,
        (autocorr f 0 - autocorr f y) * archLevySinhWeight y) +
      autocorr f 0 / (2 * Real.exp c * Real.exp b ^ 2) *
        ∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) :=
  (abs_pairing_sub_chebyshevWork_le f a b N).trans
    (mul_le_mul_of_nonneg_left (correlationTransportCost_le_levy f a b c) (mass_nonneg N))

/-- The pairing is literally the truncation of the requested prime and polar measures. -/
theorem pairing_eq_literal (N : ℕ) (h : ℝ → ℝ) :
    pairing N h =
      (∑ n ∈ Finset.Icc 2 (N+2), ArithmeticFunction.vonMangoldt n / Real.sqrt n * h (Real.log n)) -
      ∫ x in Icc 0 (Real.log (N+2 : ℕ)), 2 * Real.cosh (x / 2) * h x := by
  unfold pairing cutoff polarDensity primeWeight
  congr 1
  symm
  apply Finset.sum_subset
  · intro n hn
    have hn := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, hn.2⟩
  · intro n hn hnot
    have hn' : n = 1 := by
      simp only [Finset.mem_Icc] at hn hnot
      omega
    simp [hn']

end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
