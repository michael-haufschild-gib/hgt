import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeKernelNegativeDefinite
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeScaleCoupling

/-!
# Finite-scale negativity of the critical prime channel

A translated critical pattern is the coefficient combination of the single-scale critical sources
at scales `n+j+1`, so its actual von Mangoldt prime energy is the quadratic form of a symmetric
finite-scale prime matrix

  `M_n(i,j) = Σ_r Λ(r)/√r · (X_n(i,j;log r) + X_n(j,i;log r))/2`,

built from the cross correlations of single-scale sources. Polarizing the translated prime limit
shows that `M_n` converges entrywise to the Toeplitz scale-coupling matrix
`(4/π⁴) κ(|i-j|)`. Since the limiting form is negative definite with constant `4/(7000π⁴)`,
on every finite support the actual prime energy is negative definite with half that constant
for all scales beyond a threshold depending only on the support, uniformly in the coefficients.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-- The critical source of the single scale `q+1` with unit coefficient. -/
def criticalScaleSource (q : ℕ) : ℝ → ℝ := criticalFactorialSource {q} (fun _ => 1)

/-- A critical pattern source is the coefficient combination of its single-scale sources. -/
theorem criticalFactorialSource_eq_sum (T : Finset ℕ) (c : ℕ → ℝ) (x : ℝ) :
    criticalFactorialSource T c x = ∑ q ∈ T, c q * criticalScaleSource q x := by
  unfold criticalScaleSource criticalFactorialSource
  by_cases hx : x ∈ Iic (0 : ℝ)
  · simp only [Set.indicator_of_mem hx, factorialPhaseCombination, Finset.sum_singleton, one_mul,
      Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  · simp [Set.indicator_of_notMem hx]

/-- Single-scale critical sources are dominated by the envelope `2 e^{x/2}` on `x ≤ 0`. -/
theorem abs_criticalScaleSource_le (q : ℕ) (x : ℝ) :
    |criticalScaleSource q x| ≤ (Iic (0 : ℝ)).indicator (fun x => 2 * Real.exp (x / 2)) x := by
  unfold criticalScaleSource criticalFactorialSource
  by_cases hx : x ∈ Iic (0 : ℝ)
  · simp only [Set.indicator_of_mem hx, factorialPhaseCombination, Finset.sum_singleton,
      Complex.ofReal_one, one_mul, Complex.ofReal_re]
    rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_factorialPhaseProfile_le _ _) (Real.exp_pos _).le
  · simp [Set.indicator_of_notMem hx]

/-- Single-scale critical sources are measurable. -/
theorem measurable_criticalScaleSource (q : ℕ) : Measurable (criticalScaleSource q) := by
  unfold criticalScaleSource criticalFactorialSource
  refine Measurable.indicator ?_ measurableSet_Iic
  have := continuous_factorialPhaseCombination {q} (fun _ => ((1 : ℝ) : ℂ))
  exact (by fun_prop : Continuous fun x : ℝ => Real.exp (x / 2) *
    (factorialPhaseCombination {q} (fun _ => ((1 : ℝ) : ℂ)) (Real.exp (-x))).re).measurable

/-- Cross products of single-scale critical sources at nonnegative shifts are integrable. -/
theorem integrable_criticalScaleSource_mul (p q : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Integrable fun x => criticalScaleSource p x * criticalScaleSource q (x - t) := by
  have hdom : Integrable ((Iic (0 : ℝ)).indicator fun x => 4 * Real.exp x) := by
    rw [integrable_indicator_iff measurableSet_Iic]
    exact (integrableOn_exp_Iic 0).const_mul 4
  refine hdom.mono' ((measurable_criticalScaleSource p).mul
    ((measurable_criticalScaleSource q).comp (measurable_id.sub_const t))).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := abs_criticalScaleSource_le p x
  have h2 := abs_criticalScaleSource_le q (x - t)
  by_cases hx : x ∈ Iic (0 : ℝ)
  · have hxt : x - t ∈ Iic (0 : ℝ) := by simp only [mem_Iic] at hx ⊢; linarith
    rw [Set.indicator_of_mem hx] at h1 ⊢
    rw [Set.indicator_of_mem hxt] at h2
    have : Real.exp (x / 2) * Real.exp ((x - t) / 2) ≤ Real.exp x := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    calc |criticalScaleSource p x| * |criticalScaleSource q (x - t)| ≤
        (2 * Real.exp (x / 2)) * (2 * Real.exp ((x - t) / 2)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ ≤ 4 * Real.exp x := by nlinarith
  · rw [Set.indicator_of_notMem hx] at h1 ⊢
    have : |criticalScaleSource p x| = 0 := le_antisymm h1 (abs_nonneg _)
    rw [this, zero_mul]

/-- The von Mangoldt prime weight `Λ(r)/√r` of the critical prime channel. -/
private def critPrimeWeight (r : ℕ) : ℝ :=
  if 2 ≤ r then (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt (r : ℝ) else 0

/-- Cross correlation of the single-scale critical sources of scales `p+1` and `q+1` at shift `t`. -/
def criticalScaleCrossCorrelation (p q : ℕ) (t : ℝ) : ℝ :=
  ∫ x, criticalScaleSource p x * criticalScaleSource q (x - t)

/-- Cross correlation of two translated single-scale sources at the logarithm of `r`. -/
private def critCross (n i j r : ℕ) : ℝ := criticalScaleCrossCorrelation (n+i) (n+j) (Real.log r)

/-- A translated critical pattern is the coefficient combination of its single-scale sources. -/
theorem criticalFactorialSource_translated_eq_sum (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    criticalFactorialSource (S.image (fun j => n+j)) (fun q => b (q-n)) x =
      ∑ j ∈ S, b j * criticalScaleSource (n+j) x := by
  classical
  rw [criticalFactorialSource_eq_sum, Finset.sum_image (fun i _ j _ h => Nat.add_left_cancel h)]
  simp only [Nat.add_sub_cancel_left]

/-- **Bilinear expansion of translated autocorrelations** at every nonnegative shift. -/
theorem criticalFactorialSource_translated_correlation_eq_sum (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ x, criticalFactorialSource (S.image (fun j => n+j)) (fun q => b (q-n)) x *
      criticalFactorialSource (S.image (fun j => n+j)) (fun q => b (q-n)) (x - t) =
      ∑ i ∈ S, ∑ j ∈ S, b i * b j * criticalScaleCrossCorrelation (n+i) (n+j) t := by
  simp_rw [criticalFactorialSource_translated_eq_sum, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((integrable_criticalScaleSource_mul (n+i) (n+j) ht).const_mul (b i * b j)).congr
      (Eventually.of_forall fun x => by ring)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ =>
    ((integrable_criticalScaleSource_mul (n+i) (n+j) ht).const_mul (b i * b j)).congr
      (Eventually.of_forall fun x => by ring)]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold criticalScaleCrossCorrelation
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun x => by ring)

private theorem summable_critPrime_pattern (T : Finset ℕ) (c : ℕ → ℝ) :
    Summable fun r : ℕ => critPrimeWeight r *
      ∫ x, criticalFactorialSource T c x * criticalFactorialSource T c (x - Real.log r) :=
  (summable_criticalFactorialSource_prime T c).of_abs

private theorem summable_critCross_sym (n i j : ℕ) :
    Summable fun r : ℕ => critPrimeWeight r * ((critCross n i j r + critCross n j i r) / 2) := by
  have hii := summable_critPrime_pattern {n+i} (fun _ => 1)
  have hjj := summable_critPrime_pattern {n+j} (fun _ => 1)
  have hpair := summable_critPrime_pattern {n+i, n+j}
    (fun q => if q = n+i then 1 else if q = n+j then 1 else 0)
  by_cases hij : i = j
  · subst hij
    refine hii.congr fun r => ?_
    simp only [criticalFactorialSource_eq_sum, Finset.sum_singleton, one_mul, critCross,
      criticalScaleCrossCorrelation]
    unfold criticalScaleSource; ring
  · have hne : n+i ≠ n+j := by omega
    have heq (r : ℕ) : critPrimeWeight r * ((critCross n i j r + critCross n j i r) / 2) =
        (critPrimeWeight r * (∫ x, criticalFactorialSource {n+i, n+j}
          (fun q => if q = n+i then 1 else if q = n+j then 1 else 0) x *
          criticalFactorialSource {n+i, n+j}
            (fun q => if q = n+i then 1 else if q = n+j then 1 else 0) (x - Real.log r)) -
        critPrimeWeight r * (∫ x, criticalFactorialSource {n+i} (fun _ => 1) x *
          criticalFactorialSource {n+i} (fun _ => 1) (x - Real.log r)) -
        critPrimeWeight r * (∫ x, criticalFactorialSource {n+j} (fun _ => 1) x *
          criticalFactorialSource {n+j} (fun _ => 1) (x - Real.log r))) / 2 := by
      have ht := Real.log_natCast_nonneg r
      simp only [criticalFactorialSource_eq_sum, Finset.sum_singleton, one_mul,
        Finset.sum_pair hne, if_neg hne.symm, if_neg hne, critCross, criticalScaleCrossCorrelation, ite_true]
      have h1 := integrable_criticalScaleSource_mul (n+i) (n+i) ht
      have h2 := integrable_criticalScaleSource_mul (n+i) (n+j) ht
      have h3 := integrable_criticalScaleSource_mul (n+j) (n+i) ht
      have h4 := integrable_criticalScaleSource_mul (n+j) (n+j) ht
      set f1 := fun x => criticalScaleSource (n+i) x * criticalScaleSource (n+i) (x - Real.log r)
      set f2 := fun x => criticalScaleSource (n+i) x * criticalScaleSource (n+j) (x - Real.log r)
      set f3 := fun x => criticalScaleSource (n+j) x * criticalScaleSource (n+i) (x - Real.log r)
      set f4 := fun x => criticalScaleSource (n+j) x * criticalScaleSource (n+j) (x - Real.log r)
      have e12 : ∫ x, (f1 x + f2 x) = (∫ x, f1 x) + ∫ x, f2 x := integral_add h1 h2
      have e34 : ∫ x, (f3 x + f4 x) = (∫ x, f3 x) + ∫ x, f4 x := integral_add h3 h4
      have e : ∫ x, ((f1 x + f2 x) + (f3 x + f4 x)) = (∫ x, (f1 x + f2 x)) + ∫ x, (f3 x + f4 x) :=
        integral_add (h1.add h2) (h3.add h4)
      have hexp : ∫ x, (criticalScaleSource (n+i) x + criticalScaleSource (n+j) x) *
          (criticalScaleSource (n+i) (x - Real.log r) + criticalScaleSource (n+j) (x - Real.log r)) =
          (∫ x, f1 x) + (∫ x, f2 x) + (∫ x, f3 x) + ∫ x, f4 x := by
        rw [show (fun x => (criticalScaleSource (n+i) x + criticalScaleSource (n+j) x) *
          (criticalScaleSource (n+i) (x - Real.log r) + criticalScaleSource (n+j) (x - Real.log r))) =
          fun x => ((f1 x + f2 x) + (f3 x + f4 x)) by funext x; simp only [f1, f2, f3, f4]; ring,
          e, e12, e34]
        ring
      rw [hexp]
      ring
    exact (((hpair.sub hii).sub hjj).div_const 2).congr fun r => (heq r).symm

/-- The symmetric matrix of the actual critical prime channel on a translated support. -/
def criticalTranslatedPrimeMatrix (n i j : ℕ) : ℝ :=
  ∑' r : ℕ, critPrimeWeight r * ((critCross n i j r + critCross n j i r) / 2)

/-- The translated prime matrix is symmetric. -/
theorem criticalTranslatedPrimeMatrix_symm (n i j : ℕ) :
    criticalTranslatedPrimeMatrix n i j = criticalTranslatedPrimeMatrix n j i := by
  unfold criticalTranslatedPrimeMatrix
  exact tsum_congr fun r => by ring

/-- **Bilinear structure.** The actual critical prime energy of a translated pattern is the
quadratic form of the translated prime matrix. -/
theorem factorialCriticalTranslatedPrimeEnergy_eq_matrix (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) :
    factorialCriticalTranslatedPrimeEnergy S b n =
      ∑ i ∈ S, ∑ j ∈ S, b i * b j * criticalTranslatedPrimeMatrix n i j := by
  unfold factorialCriticalTranslatedPrimeEnergy
  have hterm (r : ℕ) : (if 2 ≤ r then (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt (r : ℝ) else 0) *
      ∫ x, criticalFactorialSource (S.image (fun j => n+j)) (fun q => b (q-n)) x *
        criticalFactorialSource (S.image (fun j => n+j)) (fun q => b (q-n)) (x - Real.log r) =
      ∑ i ∈ S, ∑ j ∈ S, b i * b j * (critPrimeWeight r * ((critCross n i j r + critCross n j i r) / 2)) := by
    rw [criticalFactorialSource_translated_correlation_eq_sum S b n (Real.log_natCast_nonneg r)]
    change critPrimeWeight r * _ = _
    have hsym : ∑ i ∈ S, ∑ j ∈ S, b i * b j * critCross n i j r =
        ∑ i ∈ S, ∑ j ∈ S, b i * b j * ((critCross n i j r + critCross n j i r) / 2) := by
      have hswap : ∑ i ∈ S, ∑ j ∈ S, b i * b j * critCross n j i r =
          ∑ i ∈ S, ∑ j ∈ S, b i * b j * critCross n i j r := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      have : ∑ i ∈ S, ∑ j ∈ S, b i * b j * ((critCross n i j r + critCross n j i r) / 2) =
          (∑ i ∈ S, ∑ j ∈ S, b i * b j * critCross n i j r +
            ∑ i ∈ S, ∑ j ∈ S, b i * b j * critCross n j i r) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [this, hswap]; ring
    rw [show (∑ i ∈ S, ∑ j ∈ S, b i * b j * criticalScaleCrossCorrelation (n+i) (n+j) (Real.log r)) =
      ∑ i ∈ S, ∑ j ∈ S, b i * b j * critCross n i j r from rfl, hsym, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [tsum_congr hterm, Summable.tsum_finsetSum fun i _ =>
    summable_sum fun j _ => (summable_critCross_sym n i j).mul_left _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Summable.tsum_finsetSum fun j _ => (summable_critCross_sym n i j).mul_left _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tsum_mul_left]
  rfl

private theorem energy_singleton (n i : ℕ) :
    factorialCriticalTranslatedPrimeEnergy {i} (fun _ => 1) n = criticalTranslatedPrimeMatrix n i i := by
  rw [factorialCriticalTranslatedPrimeEnergy_eq_matrix]; simp

private theorem energy_pair (n : ℕ) {i j : ℕ} (hij : i ≠ j) :
    factorialCriticalTranslatedPrimeEnergy {i, j} (fun _ => 1) n =
      criticalTranslatedPrimeMatrix n i i + criticalTranslatedPrimeMatrix n j j +
        2 * criticalTranslatedPrimeMatrix n i j := by
  rw [factorialCriticalTranslatedPrimeEnergy_eq_matrix]
  simp only [Finset.sum_pair hij, one_mul]
  rw [criticalTranslatedPrimeMatrix_symm n j i]; ring

private theorem limit_singleton (i : ℕ) :
    factorialCriticalTranslatedPrimeLimit {i} (fun _ => 1) =
      (4 / Real.pi ^ 4) * factorialCriticalPrimeCoupling 0 := by
  rw [factorialCriticalTranslatedPrimeLimit_eq_coupling]; simp

private theorem limit_pair {i j : ℕ} (hij : i ≠ j) :
    factorialCriticalTranslatedPrimeLimit {i, j} (fun _ => 1) =
      (4 / Real.pi ^ 4) * (2 * factorialCriticalPrimeCoupling 0 +
        2 * factorialCriticalPrimeCoupling ((i : ℤ) - j).natAbs) := by
  rw [factorialCriticalTranslatedPrimeLimit_eq_coupling]
  have hs : ((j : ℤ) - i).natAbs = ((i : ℤ) - j).natAbs := by omega
  simp only [Finset.sum_pair hij, one_mul, sub_self, Int.natAbs_zero, hs]
  ring

/-- **Toeplitz limit of the actual prime Gram matrix.** At every pair of offsets the finite-scale
prime matrix of the translated critical sources converges to the scale coupling coefficient of
the offset difference. -/
theorem tendsto_criticalTranslatedPrimeMatrix (i j : ℕ) :
    Tendsto (fun n => criticalTranslatedPrimeMatrix n i j) atTop
      (𝓝 ((4 / Real.pi ^ 4) * factorialCriticalPrimeCoupling ((i : ℤ) - j).natAbs)) := by
  have hsing (k : ℕ) := factorialCriticalTranslatedPrimeEnergy_tendsto {k} (fun _ => 1)
  rcases eq_or_ne i j with rfl | hij
  · have h := hsing i
    rw [limit_singleton] at h
    exact (h.congr fun n => energy_singleton n i).trans (le_of_eq (by simp))
  · have h := ((factorialCriticalTranslatedPrimeEnergy_tendsto {i, j} (fun _ => 1)).sub
      ((hsing i).add (hsing j))).div_const 2
    rw [limit_pair hij, limit_singleton, limit_singleton] at h
    refine h.congr' (Eventually.of_forall fun n => ?_) |>.trans (le_of_eq (by congr 1; ring))
    simp only [energy_pair n hij, energy_singleton]; ring

/-- **Uniform finite-scale negativity of the actual prime channel.** On every finite support the
actual critical prime energy of translated patterns is, beyond a threshold scale depending only
on the support, negative definite with half the limiting constant, uniformly in the coefficients. -/
theorem eventually_factorialCriticalTranslatedPrimeEnergy_le (S : Finset ℕ) :
    ∀ᶠ n in atTop, ∀ b : ℕ → ℝ,
      factorialCriticalTranslatedPrimeEnergy S b n ≤ -(2 / (7000 * Real.pi ^ 4)) * ∑ j ∈ S, b j ^ 2 := by
  set c : ℝ := 4 / (7000 * Real.pi ^ 4)
  have hc : 0 < c := by positivity
  set δ : ℝ := c / (2 * (S.card + 1))
  have hδ : 0 < δ := by positivity
  set L : ℕ → ℕ → ℝ := fun i j => (4 / Real.pi ^ 4) * factorialCriticalPrimeCoupling ((i : ℤ) - j).natAbs
  have hev : ∀ᶠ n in atTop, ∀ i ∈ S, ∀ j ∈ S, |criticalTranslatedPrimeMatrix n i j - L i j| < δ := by
    rw [Filter.eventually_all_finset]
    intro i _
    rw [Filter.eventually_all_finset]
    intro j _
    exact (Metric.tendsto_nhds.mp (tendsto_criticalTranslatedPrimeMatrix i j)) δ hδ
  filter_upwards [hev] with n hn b
  have hP := factorialCriticalTranslatedPrimeLimit_le_neg_energy S b
  rw [factorialCriticalTranslatedPrimeLimit_eq_coupling] at hP
  have hsplit : factorialCriticalTranslatedPrimeEnergy S b n =
      (4 / Real.pi ^ 4) * ∑ i ∈ S, ∑ j ∈ S, b i * b j * factorialCriticalPrimeCoupling ((i : ℤ) - j).natAbs +
      ∑ i ∈ S, ∑ j ∈ S, b i * b j * (criticalTranslatedPrimeMatrix n i j - L i j) := by
    rw [factorialCriticalTranslatedPrimeEnergy_eq_matrix, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp only [L]; ring
  have herr : ∑ i ∈ S, ∑ j ∈ S, b i * b j * (criticalTranslatedPrimeMatrix n i j - L i j) ≤
      δ * (S.card * ∑ j ∈ S, b j ^ 2) := by
    calc _ ≤ ∑ i ∈ S, ∑ j ∈ S, |b i| * |b j| * δ := by
          refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
          calc b i * b j * (criticalTranslatedPrimeMatrix n i j - L i j) ≤
              |b i * b j * (criticalTranslatedPrimeMatrix n i j - L i j)| := le_abs_self _
            _ = |b i| * |b j| * |criticalTranslatedPrimeMatrix n i j - L i j| := by rw [abs_mul, abs_mul]
            _ ≤ |b i| * |b j| * δ :=
                mul_le_mul_of_nonneg_left (hn i hi j hj).le (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = δ * (∑ i ∈ S, |b i|) ^ 2 := by
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ δ * (S.card * ∑ j ∈ S, b j ^ 2) := by
          gcongr
          simpa only [sq_abs] using (sq_sum_le_card_mul_sum_sq (s := S) (f := fun i => |b i|))
  have hE : 0 ≤ ∑ j ∈ S, b j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hδS : δ * S.card ≤ c / 2 := by
    simp only [δ]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [(Nat.cast_nonneg S.card : (0:ℝ) ≤ S.card)]
  have hc2 : -(2 / (7000 * Real.pi ^ 4)) = -c + c / 2 := by simp only [c]; ring
  rw [hsplit, hc2]
  have hP' : (4 / Real.pi ^ 4) * ∑ i ∈ S, ∑ j ∈ S, b i * b j * factorialCriticalPrimeCoupling ((i : ℤ) - j).natAbs ≤
      -c * ∑ j ∈ S, b j ^ 2 := by simpa [c] using hP
  nlinarith [mul_le_mul_of_nonneg_right hδS hE]

end GaloisForLFunctions.ArithmeticPositivityTheory
