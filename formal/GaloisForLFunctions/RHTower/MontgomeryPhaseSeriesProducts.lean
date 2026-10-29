import GaloisForLFunctions.RHTower.Sieve.DirichletMeanValueSharp
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Linearity

/-!
# Phase series: products and mean values

For coefficients `a : ℕ → ℂ` with `a 0 = 0` and `Σ |a_n| < ∞`, the phase series
`K[a](t) = Σ_n a_n e^{−it log n}` is the L-series of `a` on the imaginary axis (`phaseSeries`).

* **Products** (`phaseSeries_mul`): `K[a] K[b] = K[a ⍟ b]` with the Dirichlet convolution, and
  `a ⍟ b` is again absolutely summable (`summable_norm_convolution`).
* **Mean value** (`integral_normSq_phaseSeries_sub_le`): if also `Σ n |a_n|² < ∞`, then
  `|∫_0^T |K[a]|² − T Σ |a_n|²| ≤ 104 Σ n |a_n|²`. The truncations are Dirichlet polynomials, for
  which this is the sharp Montgomery–Vaughan theorem, and their tails are uniformly small.
* **Bilinear mean value** (`norm_integral_phaseSeries_mul_conj_sub_le`), by polarization:
  `|∫_0^T K[a] conj K[b] − T Σ a_n conj b_n| ≤ 208 (Σ n |a_n|² + Σ n |b_n|²)`.
-/

open Complex MeasureTheory Filter Topology
open scoped ComplexConjugate LSeries.notation

noncomputable section

namespace RHTower.PhaseSeries

/-- The phase series `K[a](t) = Σ_n a_n e^{−it log n}`: the L-series of `a` at `s = it`. -/
def phaseSeries (a : ℕ → ℂ) (t : ℝ) : ℂ := LSeries a ((t : ℂ) * I)

/-- `n^{−it} = e^{−it log n}` for `n ≠ 0`. -/
theorem natCast_cpow_neg_mul_I {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    (n : ℂ) ^ (-((t : ℂ) * I)) = Complex.exp (-(((t * Real.log n : ℝ) : ℂ) * I)) := by
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn), ← Complex.natCast_log]
  congr 1; push_cast; ring

theorem norm_exp_neg_phase (θ : ℝ) : ‖Complex.exp (-((θ : ℂ) * I))‖ = 1 := by
  rw [← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]

theorem term_eq {a : ℕ → ℂ} (ha0 : a 0 = 0) (t : ℝ) (n : ℕ) :
    LSeries.term a ((t : ℂ) * I) n = a n * Complex.exp (-(((t * Real.log n : ℝ) : ℂ) * I)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [ha0]
  · rw [LSeries.term_def₀ ha0, natCast_cpow_neg_mul_I hn]

theorem norm_term {a : ℕ → ℂ} (ha0 : a 0 = 0) (t : ℝ) (n : ℕ) :
    ‖LSeries.term a ((t : ℂ) * I) n‖ = ‖a n‖ := by
  rw [term_eq ha0, norm_mul, norm_exp_neg_phase, mul_one]

theorem lseriesSummable {a : ℕ → ℂ} (ha0 : a 0 = 0) (ha : Summable fun n => ‖a n‖) (t : ℝ) :
    LSeriesSummable a ((t : ℂ) * I) :=
  Summable.of_norm (ha.congr fun n => (norm_term ha0 t n).symm)

theorem phaseSeries_eq_tsum {a : ℕ → ℂ} (ha0 : a 0 = 0) (t : ℝ) :
    phaseSeries a t = ∑' n, a n * Complex.exp (-(((t * Real.log n : ℝ) : ℂ) * I)) := by
  rw [phaseSeries, LSeries]; simp_rw [term_eq ha0]

/-- **Products are Dirichlet convolutions**: `K[a] K[b] = K[a ⍟ b]`. -/
theorem phaseSeries_mul {a b : ℕ → ℂ} (ha0 : a 0 = 0) (hb0 : b 0 = 0)
    (ha : Summable fun n => ‖a n‖) (hb : Summable fun n => ‖b n‖) (t : ℝ) :
    phaseSeries a t * phaseSeries b t = phaseSeries (a ⍟ b) t :=
  (LSeries_convolution' (lseriesSummable ha0 ha t) (lseriesSummable hb0 hb t)).symm

theorem norm_convolution_le (a b : ℕ → ℂ) (n : ℕ) :
    ‖(a ⍟ b) n‖ ≤ ∑ p ∈ n.divisorsAntidiagonal, ‖a p.1‖ * ‖b p.2‖ := by
  rw [LSeries.convolution_def]
  exact (norm_sum_le _ _).trans (le_of_eq (by simp_rw [norm_mul]))

theorem convolution_zero (a b : ℕ → ℂ) : (a ⍟ b) 0 = 0 := LSeries.convolution_map_zero a b

/-- The convolution of absolutely summable coefficients is absolutely summable. -/
theorem summable_norm_convolution {a b : ℕ → ℂ} (ha0 : a 0 = 0) (hb0 : b 0 = 0)
    (ha : Summable fun n => ‖a n‖) (hb : Summable fun n => ‖b n‖) :
    Summable fun n => ‖(a ⍟ b) n‖ := by
  set A : ℕ → ℂ := fun n => ((‖a n‖ : ℝ) : ℂ)
  set B : ℕ → ℂ := fun n => ((‖b n‖ : ℝ) : ℂ)
  have hA0 : A 0 = 0 := by simp [A, ha0]
  have hB0 : B 0 = 0 := by simp [B, hb0]
  have hA : Summable fun n => ‖A n‖ := by simpa [A] using ha
  have hB : Summable fun n => ‖B n‖ := by simpa [B] using hb
  have hS := LSeriesSummable.convolution (lseriesSummable hA0 hA 0) (lseriesSummable hB0 hB 0)
  have hS' : Summable fun n => (A ⍟ B) n := by
    refine hS.congr fun n => ?_
    rw [term_eq (convolution_zero A B)]; simp
  have hR : Summable fun n : ℕ => ∑ p ∈ n.divisorsAntidiagonal, ‖a p.1‖ * ‖b p.2‖ := by
    refine Complex.summable_ofReal.mp (hS'.congr fun n => ?_)
    rw [LSeries.convolution_def]; push_cast; rfl
  exact hR.of_nonneg_of_le (fun n => norm_nonneg _) (norm_convolution_le a b)

/-! ### Truncations and continuity -/

/-- The truncation `Σ_{n<N} a_n e^{−it log n}`. -/
def partialSum (a : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, a n * Complex.exp (-(((t * Real.log n : ℝ) : ℂ) * I))

theorem continuous_phaseSeries {a : ℕ → ℂ} (ha0 : a 0 = 0) (ha : Summable fun n => ‖a n‖) :
    Continuous (phaseSeries a) := by
  have e : phaseSeries a = fun t => ∑' n, a n * Complex.exp (-(((t * Real.log n : ℝ) : ℂ) * I)) :=
    funext (phaseSeries_eq_tsum ha0)
  rw [e]
  refine continuous_tsum (fun n => by fun_prop) ha fun n t => ?_
  rw [norm_mul, norm_exp_neg_phase, mul_one]

theorem continuous_partialSum (a : ℕ → ℂ) (N : ℕ) : Continuous (partialSum a N) := by
  unfold partialSum; fun_prop

theorem norm_partialSum_le {a : ℕ → ℂ} (ha : Summable fun n => ‖a n‖) (N : ℕ) (t : ℝ) :
    ‖partialSum a N t‖ ≤ ∑' n, ‖a n‖ := by
  refine (norm_sum_le _ _).trans ?_
  refine le_of_eq_of_le (Finset.sum_congr rfl fun n _ => ?_) (ha.sum_le_tsum _ fun n _ =>
    norm_nonneg _)
  rw [norm_mul, norm_exp_neg_phase, mul_one]

theorem norm_phaseSeries_sub_partialSum_le {a : ℕ → ℂ} (ha0 : a 0 = 0)
    (ha : Summable fun n => ‖a n‖) (N : ℕ) (t : ℝ) :
    ‖phaseSeries a t - partialSum a N t‖ ≤ ∑' k, ‖a (k + N)‖ := by
  have hfn : ∀ n : ℕ, ‖a n * Complex.exp (-(((t * Real.log n : ℝ) : ℂ) * I))‖ = ‖a n‖ :=
    fun n => by rw [norm_mul, norm_exp_neg_phase, mul_one]
  have hs : Summable fun n : ℕ => a n * Complex.exp (-(((t * Real.log n : ℝ) : ℂ) * I)) :=
    Summable.of_norm (ha.congr fun n => (hfn n).symm)
  have h1 : phaseSeries a t - partialSum a N t =
      ∑' k : ℕ, a (k + N) * Complex.exp (-(((t * Real.log ((k + N : ℕ) : ℝ) : ℝ) : ℂ) * I)) := by
    rw [phaseSeries_eq_tsum ha0, ← hs.sum_add_tsum_nat_add N, partialSum, add_sub_cancel_left]
  rw [h1]
  have hs' : Summable fun k : ℕ =>
      ‖a (k + N) * Complex.exp (-(((t * Real.log ((k + N : ℕ) : ℝ) : ℝ) : ℂ) * I))‖ :=
    ((summable_nat_add_iff N).mpr ha).congr fun k => (hfn (k + N)).symm
  refine (norm_tsum_le_tsum_norm hs').trans (le_of_eq ?_)
  exact tsum_congr fun k => hfn (k + N)

/-! ### The mean value theorem -/

theorem conj_partialSum_succ {a : ℕ → ℂ} (ha0 : a 0 = 0) (N : ℕ) (t : ℝ) :
    conj (partialSum a (N + 1) t) = Sieve.dirPoly N (fun m : Fin N => conj (a ((m : ℕ) + 1))) t := by
  rw [partialSum, Finset.sum_range_succ', Sieve.dirPoly, Fin.sum_univ_eq_sum_range
    (fun m => conj (a (m + 1)) * Complex.exp (((t * Real.log (((m : ℕ) : ℝ) + 1) : ℝ) : ℂ) * I)) N]
  simp only [ha0, zero_mul, add_zero, map_sum, map_mul, ← Complex.exp_conj, map_neg,
    Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_neg]
  refine Finset.sum_congr rfl fun m _ => ?_
  push_cast; rfl

theorem sum_fin_normSq_eq {a : ℕ → ℂ} (ha0 : a 0 = 0) (N : ℕ) :
    ∑ m : Fin N, ‖conj (a ((m : ℕ) + 1))‖ ^ (2 : ℕ) = ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun m => ‖conj (a (m + 1))‖ ^ (2 : ℕ)) N, Finset.sum_range_succ',
    ha0, norm_zero]
  simp

theorem sum_fin_mul_normSq_eq {a : ℕ → ℂ} (ha0 : a 0 = 0) (N : ℕ) :
    ∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖conj (a ((m : ℕ) + 1))‖ ^ (2 : ℕ) =
      ∑ n ∈ Finset.range (N + 1), (n : ℝ) * ‖a n‖ ^ 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun m => ((m : ℝ) + 1) * ‖conj (a (m + 1))‖ ^ (2 : ℕ)) N,
    Finset.sum_range_succ', ha0, norm_zero]
  simp

/-- The sharp mean value theorem for the truncation. -/
theorem integral_normSq_partialSum_sub_le {a : ℕ → ℂ} (ha0 : a 0 = 0) (N : ℕ) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖partialSum a (N + 1) t‖ ^ 2)
        - T * ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2|
      ≤ 104 * ∑ n ∈ Finset.range (N + 1), (n : ℝ) * ‖a n‖ ^ 2 := by
  have h := Sieve.dirichlet_meanValue_sharp N (fun m : Fin N => conj (a ((m : ℕ) + 1))) T
  rw [sum_fin_normSq_eq ha0, sum_fin_mul_normSq_eq ha0] at h
  have e : (fun t => ‖partialSum a (N + 1) t‖ ^ 2) =
      fun t => ‖Sieve.dirPoly N (fun m : Fin N => conj (a ((m : ℕ) + 1))) t‖ ^ (2 : ℕ) := by
    funext t; rw [← conj_partialSum_succ ha0, RCLike.norm_conj]
  rw [e]; exact h

theorem abs_normSq_add_sub_normSq_le' (u v : ℂ) :
    |‖u + v‖ ^ 2 - ‖u‖ ^ 2| ≤ ‖v‖ * (2 * ‖u‖ + ‖v‖) := by
  have h1 : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le u v
  have h2 : ‖u‖ ≤ ‖u + v‖ + ‖v‖ := by
    calc ‖u‖ = ‖(u + v) + -v‖ := by ring_nf
      _ ≤ ‖u + v‖ + ‖-v‖ := norm_add_le _ _
      _ = ‖u + v‖ + ‖v‖ := by rw [norm_neg]
  have h0 := norm_nonneg (u + v)
  have h0' := norm_nonneg u
  have h0'' := norm_nonneg v
  rw [abs_le]; constructor <;> nlinarith

/-- `|∫_0^T |K[a]|² − ∫_0^T |K_N[a]|²| ≤ T τ_N (2 A + τ_N)`. -/
theorem abs_integral_normSq_sub_partialSum_le {a : ℕ → ℂ} (ha0 : a 0 = 0)
    (ha : Summable fun n => ‖a n‖) {T : ℝ} (hT : 0 ≤ T) (N : ℕ) :
    |(∫ t in (0 : ℝ)..T, ‖phaseSeries a t‖ ^ 2) - ∫ t in (0 : ℝ)..T, ‖partialSum a N t‖ ^ 2|
      ≤ T * ((∑' k, ‖a (k + N)‖) * (2 * ∑' n, ‖a n‖ + ∑' k, ‖a (k + N)‖)) := by
  have hc : Continuous fun t => ‖phaseSeries a t‖ ^ 2 :=
    (continuous_phaseSeries ha0 ha).norm.pow 2
  have hcN : Continuous fun t => ‖partialSum a N t‖ ^ 2 := (continuous_partialSum a N).norm.pow 2
  rw [← intervalIntegral.integral_sub (hc.intervalIntegrable _ _) (hcN.intervalIntegrable _ _)]
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) T, ‖‖phaseSeries a t‖ ^ 2 - ‖partialSum a N t‖ ^ 2‖
      ≤ (∑' k, ‖a (k + N)‖) * (2 * ∑' n, ‖a n‖ + ∑' k, ‖a (k + N)‖) := by
    intro t _
    rw [Real.norm_eq_abs]
    have hkey := abs_normSq_add_sub_normSq_le' (partialSum a N t)
      (phaseSeries a t - partialSum a N t)
    rw [add_sub_cancel] at hkey
    refine hkey.trans ?_
    have h1 := norm_phaseSeries_sub_partialSum_le ha0 ha N t
    have h2 := norm_partialSum_le ha N t
    have h0 := norm_nonneg (phaseSeries a t - partialSum a N t)
    have h3 : 0 ≤ ∑' k, ‖a (k + N)‖ := tsum_nonneg fun _ => norm_nonneg _
    exact mul_le_mul h1 (by linarith) (by positivity) h3
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hT] at this
  linarith

theorem summable_normSq_of_mul {a : ℕ → ℂ} (ha0 : a 0 = 0)
    (hna : Summable fun n : ℕ => (n : ℝ) * ‖a n‖ ^ 2) : Summable fun n => ‖a n‖ ^ 2 := by
  refine hna.of_nonneg_of_le (fun n => by positivity) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ha0]
  · exact le_mul_of_one_le_left (by positivity) (by exact_mod_cast hn)

/-- **The mean value theorem for phase series.** -/
theorem integral_normSq_phaseSeries_sub_le {a : ℕ → ℂ} (ha0 : a 0 = 0)
    (ha : Summable fun n => ‖a n‖) (hna : Summable fun n : ℕ => (n : ℝ) * ‖a n‖ ^ 2)
    {T : ℝ} (hT : 0 ≤ T) :
    |(∫ t in (0 : ℝ)..T, ‖phaseSeries a t‖ ^ 2) - T * ∑' n, ‖a n‖ ^ 2|
      ≤ 104 * ∑' n : ℕ, (n : ℝ) * ‖a n‖ ^ 2 := by
  have hsq := summable_normSq_of_mul ha0 hna
  set τ : ℕ → ℝ := fun N => ∑' k, ‖a (k + N)‖
  have hstep : ∀ N : ℕ,
      |(∫ t in (0 : ℝ)..T, ‖phaseSeries a t‖ ^ 2) - T * ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2|
        ≤ T * (τ (N + 1) * (2 * ∑' n, ‖a n‖ + τ (N + 1)))
          + 104 * ∑ n ∈ Finset.range (N + 1), (n : ℝ) * ‖a n‖ ^ 2 := by
    intro N
    have h1 := abs_integral_normSq_sub_partialSum_le ha0 ha hT (N + 1)
    have h2 := integral_normSq_partialSum_sub_le ha0 N T
    calc _ ≤ |(∫ t in (0 : ℝ)..T, ‖phaseSeries a t‖ ^ 2)
            - ∫ t in (0 : ℝ)..T, ‖partialSum a (N + 1) t‖ ^ 2|
          + |(∫ t in (0 : ℝ)..T, ‖partialSum a (N + 1) t‖ ^ 2)
            - T * ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add h1 h2
  have hτ : Tendsto (fun N : ℕ => τ (N + 1)) atTop (nhds 0) :=
    (tendsto_sum_nat_add fun n => ‖a n‖).comp (Filter.tendsto_add_atTop_nat 1)
  have hL : Tendsto (fun N : ℕ => |(∫ t in (0 : ℝ)..T, ‖phaseSeries a t‖ ^ 2)
      - T * ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2|) atTop
      (nhds |(∫ t in (0 : ℝ)..T, ‖phaseSeries a t‖ ^ 2) - T * ∑' n, ‖a n‖ ^ 2|) :=
    (tendsto_const_nhds.sub (tendsto_const_nhds.mul
      (hsq.tendsto_sum_tsum_nat.comp (Filter.tendsto_add_atTop_nat 1)))).abs
  have hR : Tendsto (fun N : ℕ => T * (τ (N + 1) * (2 * ∑' n, ‖a n‖ + τ (N + 1)))
      + 104 * ∑ n ∈ Finset.range (N + 1), (n : ℝ) * ‖a n‖ ^ 2) atTop
      (nhds (T * (0 * (2 * ∑' n, ‖a n‖ + 0)) + 104 * ∑' n : ℕ, (n : ℝ) * ‖a n‖ ^ 2)) :=
    (tendsto_const_nhds.mul (hτ.mul (tendsto_const_nhds.add hτ))).add
      (tendsto_const_nhds.mul (hna.tendsto_sum_tsum_nat.comp (Filter.tendsto_add_atTop_nat 1)))
  have := le_of_tendsto_of_tendsto' hL hR hstep
  simpa using this

/-! ### The bilinear mean value theorem -/

/-- **Polarization**: `u v̄ = ¼ (|u+v|² − |u−v|² + i|u+iv|² − i|u−iv|²)`. -/
theorem mul_conj_eq_polarization (u v : ℂ) :
    u * conj v = 1 / 4 * (((‖u + v‖ ^ 2 : ℝ) : ℂ) - ((‖u + -1 * v‖ ^ 2 : ℝ) : ℂ) +
      I * ((‖u + I * v‖ ^ 2 : ℝ) : ℂ) - I * ((‖u + -I * v‖ ^ 2 : ℝ) : ℂ)) := by
  have key : ∀ w : ℂ, ((‖w‖ ^ 2 : ℝ) : ℂ) = w * conj w := fun w => by
    rw [Complex.sq_norm, Complex.mul_conj]
  rw [key, key, key, key]
  simp only [map_add, map_mul, map_neg, map_one, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem phaseSeries_add_smul {a b : ℕ → ℂ} (ha0 : a 0 = 0) (hb0 : b 0 = 0)
    (ha : Summable fun n => ‖a n‖) (hb : Summable fun n => ‖b n‖) (ε : ℂ) (t : ℝ) :
    phaseSeries (a + ε • b) t = phaseSeries a t + ε * phaseSeries b t := by
  rw [phaseSeries, LSeries_add (lseriesSummable ha0 ha t)
    ((lseriesSummable hb0 hb t).smul ε), LSeries_smul]
  rfl

/-- The hypotheses of the mean value theorem pass to `a + ε b`, `|ε| = 1`, with
`Σ n |a + εb|² ≤ 2 Σ n |a|² + 2 Σ n |b|²`. -/
theorem hyp_add_smul {a b : ℕ → ℂ} (ha0 : a 0 = 0) (hb0 : b 0 = 0)
    (ha : Summable fun n => ‖a n‖) (hb : Summable fun n => ‖b n‖)
    (hna : Summable fun n : ℕ => (n : ℝ) * ‖a n‖ ^ 2)
    (hnb : Summable fun n : ℕ => (n : ℝ) * ‖b n‖ ^ 2) {ε : ℂ} (hε : ‖ε‖ = 1) :
    (a + ε • b) 0 = 0 ∧ (Summable fun n => ‖(a + ε • b) n‖) ∧
      (Summable fun n : ℕ => (n : ℝ) * ‖(a + ε • b) n‖ ^ 2) ∧
      ∑' n : ℕ, (n : ℝ) * ‖(a + ε • b) n‖ ^ 2 ≤
        2 * ∑' n : ℕ, (n : ℝ) * ‖a n‖ ^ 2 + 2 * ∑' n : ℕ, (n : ℝ) * ‖b n‖ ^ 2 := by
  have hpt : ∀ n, ‖(a + ε • b) n‖ ^ 2 ≤ 2 * ‖a n‖ ^ 2 + 2 * ‖b n‖ ^ 2 := fun n => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h := norm_add_le (a n) (ε * b n)
    rw [norm_mul, hε, one_mul] at h
    nlinarith [norm_nonneg (a n + ε * b n), norm_nonneg (a n), norm_nonneg (b n),
      sq_nonneg (‖a n‖ - ‖b n‖)]
  have hpt' : ∀ n : ℕ, (n : ℝ) * ‖(a + ε • b) n‖ ^ 2 ≤
      2 * ((n : ℝ) * ‖a n‖ ^ 2) + 2 * ((n : ℝ) * ‖b n‖ ^ 2) := fun n => by
    nlinarith [hpt n, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hS : Summable fun n : ℕ => 2 * ((n : ℝ) * ‖a n‖ ^ 2) + 2 * ((n : ℝ) * ‖b n‖ ^ 2) :=
    (hna.mul_left 2).add (hnb.mul_left 2)
  refine ⟨by simp [ha0, hb0], ?_, ?_, ?_⟩
  · refine (ha.add hb).of_nonneg_of_le (fun n => norm_nonneg _) fun n => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, hε, one_mul]
  · exact hS.of_nonneg_of_le (fun n => by positivity) hpt'
  · refine (Summable.tsum_le_tsum hpt' (hS.of_nonneg_of_le (fun n => by positivity) hpt') hS).trans
      (le_of_eq ?_)
    rw [(hna.mul_left 2).tsum_add (hnb.mul_left 2), tsum_mul_left, tsum_mul_left]

/-- **The bilinear mean value theorem.**
`|∫_0^T K[a] conj K[b] − T Σ a_n conj b_n| ≤ 208 (Σ n|a_n|² + Σ n|b_n|²)`. -/
theorem norm_integral_phaseSeries_mul_conj_sub_le {a b : ℕ → ℂ} (ha0 : a 0 = 0) (hb0 : b 0 = 0)
    (ha : Summable fun n => ‖a n‖) (hb : Summable fun n => ‖b n‖)
    (hna : Summable fun n : ℕ => (n : ℝ) * ‖a n‖ ^ 2)
    (hnb : Summable fun n : ℕ => (n : ℝ) * ‖b n‖ ^ 2) {T : ℝ} (hT : 0 ≤ T) :
    ‖(∫ t in (0 : ℝ)..T, phaseSeries a t * conj (phaseSeries b t)) - T * ∑' n, a n * conj (b n)‖
      ≤ 208 * (∑' n : ℕ, (n : ℝ) * ‖a n‖ ^ 2 + ∑' n : ℕ, (n : ℝ) * ‖b n‖ ^ 2) := by
  set A := ∑' n : ℕ, (n : ℝ) * ‖a n‖ ^ 2
  set B := ∑' n : ℕ, (n : ℝ) * ‖b n‖ ^ 2
  -- the four polarization coefficients and their mean-value defects
  have hD : ∀ ε : ℂ, ‖ε‖ = 1 →
      |(∫ t in (0 : ℝ)..T, ‖phaseSeries (a + ε • b) t‖ ^ 2) - T * ∑' n, ‖(a + ε • b) n‖ ^ 2|
        ≤ 208 * (A + B) := fun ε hε => by
    obtain ⟨h0, h1, h2, h3⟩ := hyp_add_smul ha0 hb0 ha hb hna hnb hε
    refine (integral_normSq_phaseSeries_sub_le h0 h1 h2 hT).trans ?_
    linarith
  have hsq : ∀ ε : ℂ, ‖ε‖ = 1 → Summable fun n => ‖(a + ε • b) n‖ ^ 2 := fun ε hε => by
    obtain ⟨h0, -, h2, -⟩ := hyp_add_smul ha0 hb0 ha hb hna hnb hε
    exact summable_normSq_of_mul h0 h2
  have hcont : ∀ ε : ℂ, ‖ε‖ = 1 →
      Continuous fun t => ((‖phaseSeries (a + ε • b) t‖ ^ 2 : ℝ) : ℂ) := fun ε hε => by
    obtain ⟨h0, h1, -, -⟩ := hyp_add_smul ha0 hb0 ha hb hna hnb hε
    exact Complex.continuous_ofReal.comp ((continuous_phaseSeries h0 h1).norm.pow 2)
  have h1 : ‖(1 : ℂ)‖ = 1 := norm_one
  have hm1 : ‖(-1 : ℂ)‖ = 1 := by simp
  have hI : ‖I‖ = 1 := Complex.norm_I
  have hmI : ‖-I‖ = 1 := by rw [norm_neg, Complex.norm_I]
  -- polarization of the integrand and of the coefficient sum
  have hint : (∫ t in (0 : ℝ)..T, phaseSeries a t * conj (phaseSeries b t)) =
      1 / 4 * ((((∫ t in (0 : ℝ)..T, ‖phaseSeries (a + (1 : ℂ) • b) t‖ ^ 2) : ℝ) : ℂ)
        - (((∫ t in (0 : ℝ)..T, ‖phaseSeries (a + (-1 : ℂ) • b) t‖ ^ 2) : ℝ) : ℂ)
        + I * (((∫ t in (0 : ℝ)..T, ‖phaseSeries (a + I • b) t‖ ^ 2) : ℝ) : ℂ)
        - I * (((∫ t in (0 : ℝ)..T, ‖phaseSeries (a + (-I) • b) t‖ ^ 2) : ℝ) : ℂ)) := by
    have hpt : ∀ t, phaseSeries a t * conj (phaseSeries b t) =
        1 / 4 * (((‖phaseSeries (a + (1 : ℂ) • b) t‖ ^ 2 : ℝ) : ℂ)
          - ((‖phaseSeries (a + (-1 : ℂ) • b) t‖ ^ 2 : ℝ) : ℂ)
          + I * ((‖phaseSeries (a + I • b) t‖ ^ 2 : ℝ) : ℂ)
          - I * ((‖phaseSeries (a + (-I) • b) t‖ ^ 2 : ℝ) : ℂ)) := fun t => by
      rw [phaseSeries_add_smul ha0 hb0 ha hb, phaseSeries_add_smul ha0 hb0 ha hb,
        phaseSeries_add_smul ha0 hb0 ha hb, phaseSeries_add_smul ha0 hb0 ha hb,
        mul_conj_eq_polarization]
      simp only [one_mul, neg_mul]
    simp_rw [hpt]
    have i1 : IntervalIntegrable (fun t => ((‖phaseSeries (a + (1 : ℂ) • b) t‖ ^ 2 : ℝ) : ℂ))
        volume 0 T := (hcont 1 h1).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun t => ((‖phaseSeries (a + (-1 : ℂ) • b) t‖ ^ 2 : ℝ) : ℂ))
        volume 0 T := (hcont (-1) hm1).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun t => I * ((‖phaseSeries (a + I • b) t‖ ^ 2 : ℝ) : ℂ))
        volume 0 T := ((hcont I hI).const_mul I).intervalIntegrable _ _
    have i4 : IntervalIntegrable (fun t => I * ((‖phaseSeries (a + (-I) • b) t‖ ^ 2 : ℝ) : ℂ))
        volume 0 T := ((hcont (-I) hmI).const_mul I).intervalIntegrable _ _
    have i12 : IntervalIntegrable (fun t => ((‖phaseSeries (a + (1 : ℂ) • b) t‖ ^ 2 : ℝ) : ℂ) -
        ((‖phaseSeries (a + (-1 : ℂ) • b) t‖ ^ 2 : ℝ) : ℂ)) volume 0 T := i1.sub i2
    have i123 : IntervalIntegrable (fun t => ((‖phaseSeries (a + (1 : ℂ) • b) t‖ ^ 2 : ℝ) : ℂ) -
        ((‖phaseSeries (a + (-1 : ℂ) • b) t‖ ^ 2 : ℝ) : ℂ) +
        I * ((‖phaseSeries (a + I • b) t‖ ^ 2 : ℝ) : ℂ)) volume 0 T := i12.add i3
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub i123 i4,
      intervalIntegral.integral_add i12 i3, intervalIntegral.integral_sub i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  have hsum : ∑' n, a n * conj (b n) =
      1 / 4 * (((∑' n, ‖(a + (1 : ℂ) • b) n‖ ^ 2 : ℝ) : ℂ)
        - ((∑' n, ‖(a + (-1 : ℂ) • b) n‖ ^ 2 : ℝ) : ℂ)
        + I * ((∑' n, ‖(a + I • b) n‖ ^ 2 : ℝ) : ℂ)
        - I * ((∑' n, ‖(a + (-I) • b) n‖ ^ 2 : ℝ) : ℂ)) := by
    have hc : ∀ ε : ℂ, ‖ε‖ = 1 → Summable fun n => ((‖(a + ε • b) n‖ ^ 2 : ℝ) : ℂ) :=
      fun ε hε => Complex.summable_ofReal.mpr (hsq ε hε)
    have hpt : ∀ n, a n * conj (b n) =
        1 / 4 * (((‖(a + (1 : ℂ) • b) n‖ ^ 2 : ℝ) : ℂ) - ((‖(a + (-1 : ℂ) • b) n‖ ^ 2 : ℝ) : ℂ)
          + I * ((‖(a + I • b) n‖ ^ 2 : ℝ) : ℂ) - I * ((‖(a + (-I) • b) n‖ ^ 2 : ℝ) : ℂ)) :=
      fun n => by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul]
        exact mul_conj_eq_polarization (a n) (b n)
    simp_rw [hpt]
    have c12 : Summable fun n => ((‖(a + (1 : ℂ) • b) n‖ ^ 2 : ℝ) : ℂ) -
        ((‖(a + (-1 : ℂ) • b) n‖ ^ 2 : ℝ) : ℂ) := (hc 1 h1).sub (hc (-1) hm1)
    have c3 : Summable fun n => I * ((‖(a + I • b) n‖ ^ 2 : ℝ) : ℂ) := (hc I hI).mul_left I
    have c4 : Summable fun n => I * ((‖(a + (-I) • b) n‖ ^ 2 : ℝ) : ℂ) := (hc (-I) hmI).mul_left I
    have c123 : Summable fun n => ((‖(a + (1 : ℂ) • b) n‖ ^ 2 : ℝ) : ℂ) -
        ((‖(a + (-1 : ℂ) • b) n‖ ^ 2 : ℝ) : ℂ) + I * ((‖(a + I • b) n‖ ^ 2 : ℝ) : ℂ) := c12.add c3
    rw [tsum_mul_left, c123.tsum_sub c4, c12.tsum_add c3, (hc 1 h1).tsum_sub (hc (-1) hm1),
      tsum_mul_left, tsum_mul_left, Complex.ofReal_tsum, Complex.ofReal_tsum,
      Complex.ofReal_tsum, Complex.ofReal_tsum]
  rw [hint, hsum]
  set D : ℂ → ℝ := fun ε =>
    (∫ t in (0 : ℝ)..T, ‖phaseSeries (a + ε • b) t‖ ^ 2) - T * ∑' n, ‖(a + ε • b) n‖ ^ 2
  have e : 1 / 4 * ((((∫ t in (0 : ℝ)..T, ‖phaseSeries (a + (1 : ℂ) • b) t‖ ^ 2) : ℝ) : ℂ)
        - (((∫ t in (0 : ℝ)..T, ‖phaseSeries (a + (-1 : ℂ) • b) t‖ ^ 2) : ℝ) : ℂ)
        + I * (((∫ t in (0 : ℝ)..T, ‖phaseSeries (a + I • b) t‖ ^ 2) : ℝ) : ℂ)
        - I * (((∫ t in (0 : ℝ)..T, ‖phaseSeries (a + (-I) • b) t‖ ^ 2) : ℝ) : ℂ))
      - T * (1 / 4 * (((∑' n, ‖(a + (1 : ℂ) • b) n‖ ^ 2 : ℝ) : ℂ)
        - ((∑' n, ‖(a + (-1 : ℂ) • b) n‖ ^ 2 : ℝ) : ℂ)
        + I * ((∑' n, ‖(a + I • b) n‖ ^ 2 : ℝ) : ℂ)
        - I * ((∑' n, ‖(a + (-I) • b) n‖ ^ 2 : ℝ) : ℂ)))
      = 1 / 4 * (((D 1 : ℝ) : ℂ) - ((D (-1) : ℝ) : ℂ) + I * ((D I : ℝ) : ℂ) - I * ((D (-I) : ℝ) : ℂ)) := by
    simp only [D]; push_cast; ring
  rw [e, norm_mul]
  have hq : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
  rw [hq]
  have hsub : ‖((D 1 : ℝ) : ℂ) - ((D (-1) : ℝ) : ℂ) + I * ((D I : ℝ) : ℂ) - I * ((D (-I) : ℝ) : ℂ)‖
      ≤ |D 1| + |D (-1)| + |D I| + |D (-I)| := by
    refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (le_of_eq (by rw [Complex.norm_real, Complex.norm_real]; rfl)))
      (le_of_eq (by rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real]; rfl))))
      (le_of_eq (by rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real]; rfl)))
  have := hD 1 h1
  have := hD (-1) hm1
  have := hD I hI
  have := hD (-I) hmI
  calc 1 / 4 * ‖((D 1 : ℝ) : ℂ) - ((D (-1) : ℝ) : ℂ) + I * ((D I : ℝ) : ℂ) - I * ((D (-I) : ℝ) : ℂ)‖
      ≤ 1 / 4 * (|D 1| + |D (-1)| + |D I| + |D (-I)|) := by gcongr
    _ ≤ 208 * (A + B) := by simp only [D] at *; linarith

end RHTower.PhaseSeries
