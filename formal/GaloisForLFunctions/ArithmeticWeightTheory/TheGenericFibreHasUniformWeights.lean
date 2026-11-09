import GaloisForLFunctions.ArithmeticCorrelationGeometry.MultiplicativeObservationIsGaugeInvariant
import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheConditionalMomentsOfTheTail
import Mathlib.NumberTheory.Chebyshev
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# The generic fibre has uniform weights

Deligne's purity argument bounds the weight of a sheaf `F` by the moments of its traces at all
tensor powers `F^{⊗2k}`, uniformly in `k`; the uniformity comes from the coinvariants of a big
geometric monodromy, whose weight is known. Over `ℤ` the virtual motive of the zeros has no
geometric monodromy. The gauge torus supplies one: twisting by `χ_x` is a geometric direction,
and Haar orthogonality of twists is big monodromy.

**The family.** For a window `g` with `|g| ≤ 1` and a radius `R ≥ 0` the fibre `x` of the gauge
family has the twisted window traces (`fibreTrace`)

  `T_x(u) = e^{−u/2} Σ_{p ≤ e^{u+R}} log p · g(log p − u) · χ_x(p)`,

and its tensor moments at the primes are `Σ_{p ≤ N} log p · |T_x(log p)|^{2k}` (`fibreMoment`).
At the trivial point `x = 0` these are the prime counts of `ζ` in the windows of the degrees.

**Big monodromy** (`integral_norm_twistSum_pow_le`). For a source supported on primes,
`∫ |Σ_p a_p χ_x(p)|^{2k} dx ≤ k! (Σ_p |a_p|²)^k`: the coinvariants of the `2k`-th tensor power are
the multiplicative pairings, at most `k!` per monomial, of weight zero. With Chebyshev's bound the
coinvariants of the window traces are `≤ k! (log 4 · e^R · (u + R))^k`
(`integral_norm_fibreTrace_pow_le`): logarithmic in the degree, uniformly in the fibre.

**Theorem** (`ae_fibreMoment_le`, milestone M2 of the field). For Haar-almost every fibre, every
`k` and every `ε > 0`, `Σ_{p ≤ N} log p · |T_x(log p)|^{2k} ≤ C N^{1+ε}`: the generic fibre
satisfies the uniform-weights conjecture with exponent `A = 0⁺`, and its traces are `p^{o(1)}`
(`ae_norm_fibreTrace_le`), which is Deligne's conclusion.

**Proof.** Markov at the dyadic degrees `N = 2^j` against the coinvariant bound gives exceptional
sets of measure `≪_k (j + 1)^k 2^{−jε}`, summable in `j`; Borel–Cantelli and monotonicity in `N`
give the bound for every `N`, and countably many `(k, ε)` are intersected. The trace bound is one
term of the `k`-th moment, with `k ≥ 1/ε`.
-/

open MeasureTheory Finset Real Filter Topology
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.ArithmeticWeightTheory

open ArithmeticCorrelationGeometry

/-! ### Big monodromy of the gauge family -/

/-- Products of twisted polynomials are twisted polynomials on the products. -/
theorem twistSum_mul_twistSum {A B : Finset ℕ} (hA : ∀ m ∈ A, m ≠ 0) (hB : ∀ n ∈ B, n ≠ 0)
    (r b : ℕ → ℂ) (x : GaugeTorus) :
    twistSum A r x * twistSum B b x =
      twistSum (TailArithmeticOfThePrimeOrbit.mulSupport A B)
        (TailArithmeticOfThePrimeOrbit.convCoeff A B r b) x := by
  classical
  unfold twistSum TailArithmeticOfThePrimeOrbit.convCoeff TailArithmeticOfThePrimeOrbit.mulSupport
  rw [Finset.sum_mul_sum, ← Finset.sum_product',
    ← Finset.sum_fiberwise_of_maps_to (g := fun y : ℕ × ℕ => y.1 * y.2)
      (t := (A ×ˢ B).image fun y => y.1 * y.2) (fun y hy => Finset.mem_image_of_mem _ hy)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun y hy => ?_
  obtain ⟨hy, hq⟩ := Finset.mem_filter.mp hy
  obtain ⟨hy1, hy2⟩ := Finset.mem_product.mp hy
  rw [← hq, twist_mul x (hA _ hy1) (hB _ hy2)]
  ring

/-- The `k`-th power of a twisted polynomial, with the convolution coefficients of `B^k`. -/
theorem twistSum_pow_eq {B : Finset ℕ} (hB : ∀ n ∈ B, n ≠ 0) (b : ℕ → ℂ) (x : GaugeTorus) :
    ∀ k, twistSum B b x ^ k = twistSum (TailArithmeticOfThePrimeOrbit.powSupport B k)
      (TailArithmeticOfThePrimeOrbit.powCoeff B b k) x
  | 0 => by
    simp [twistSum, TailArithmeticOfThePrimeOrbit.powSupport, TailArithmeticOfThePrimeOrbit.powCoeff]
  | k + 1 => by
    rw [pow_succ, twistSum_pow_eq hB b x k,
      twistSum_mul_twistSum (TailArithmeticOfThePrimeOrbit.powSupport_ne_zero hB k) hB]
    rfl

/-- **Big monodromy.** The `2k`-th gauge moment of a prime-supported source is at most
`k! (Σ_p |a_p|²)^k`: the coinvariants are the multiplicative pairings. -/
theorem integral_norm_twistSum_pow_le {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) (b : ℕ → ℂ)
    (k : ℕ) :
    ∫ x, ‖twistSum B b x‖ ^ (2 * k) ∂gaugeHaar ≤ k.factorial * (∑ p ∈ B, ‖b p‖ ^ 2) ^ k := by
  have hB0 : ∀ n ∈ B, n ≠ 0 := fun n hn => (hB n hn).ne_zero
  have h : ∀ x, ‖twistSum B b x‖ ^ (2 * k) = ‖twistSum (TailArithmeticOfThePrimeOrbit.powSupport B k)
      (TailArithmeticOfThePrimeOrbit.powCoeff B b k) x‖ ^ 2 := by
    intro x
    rw [← twistSum_pow_eq hB0, norm_pow, ← pow_mul, mul_comm]
  simp_rw [h]
  rw [integral_normSq_twistSum (TailArithmeticOfThePrimeOrbit.powSupport_ne_zero hB0 k)]
  exact TailArithmeticOfThePrimeOrbit.powNorm_le hB b k

/-! ### The twisted window traces -/

/-- The primes of the window of `u` with radius `R`: `p ≤ e^{u+R}`. -/
def windowPrimes (R u : ℝ) : Finset ℕ := Nat.primesLE ⌊Real.exp (u + R)⌋₊

/-- The weight of the prime `p` in the window trace at `u`: `e^{−u/2} log p · g(log p − u)`. -/
def windowWeight (g : ℝ → ℝ) (u : ℝ) (p : ℕ) : ℂ :=
  ((Real.exp (-(u / 2)) * Real.log p * g (Real.log p - u) : ℝ) : ℂ)

/-- **The twisted window trace** of the fibre `x` at `u`. -/
def fibreTrace (g : ℝ → ℝ) (R u : ℝ) (x : GaugeTorus) : ℂ :=
  twistSum (windowPrimes R u) (windowWeight g u) x

/-- **The tensor moment** `Σ_{p ≤ N} log p · |T_x(log p)|^{2k}` of the fibre `x`. -/
def fibreMoment (g : ℝ → ℝ) (R : ℝ) (k N : ℕ) (x : GaugeTorus) : ℝ :=
  ∑ p ∈ Nat.primesLE N, Real.log p * ‖fibreTrace g R (Real.log p) x‖ ^ (2 * k)

theorem continuous_fibreTrace (g : ℝ → ℝ) (R u : ℝ) : Continuous (fibreTrace g R u) :=
  continuous_twistSum _ _

theorem continuous_fibreMoment (g : ℝ → ℝ) (R : ℝ) (k N : ℕ) :
    Continuous (fibreMoment g R k N) :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul ((continuous_fibreTrace _ _ _).norm.pow _)

theorem fibreMoment_nonneg (g : ℝ → ℝ) (R : ℝ) (k N : ℕ) (x : GaugeTorus) :
    0 ≤ fibreMoment g R k N x :=
  Finset.sum_nonneg fun p hp => mul_nonneg
    (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le)) (by positivity)

/-- The moments grow with the number of primes. -/
theorem fibreMoment_mono (g : ℝ → ℝ) (R : ℝ) (k : ℕ) (x : GaugeTorus) :
    Monotone fun N => fibreMoment g R k N x := by
  intro M N hMN
  refine Finset.sum_le_sum_of_subset_of_nonneg (Nat.primesLE_mono hMN) fun p hp _ => ?_
  exact mul_nonneg
    (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le)) (by positivity)

theorem integrable_fibreMoment (g : ℝ → ℝ) (R : ℝ) (k N : ℕ) :
    Integrable (fibreMoment g R k N) gaugeHaar :=
  (continuous_fibreMoment g R k N).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- **The variance of a window trace** is logarithmic in the degree (Chebyshev). -/
theorem sum_norm_windowWeight_sq_le {g : ℝ → ℝ} (hg : ∀ v, |g v| ≤ 1) {R u : ℝ}
    (hu : 0 ≤ u + R) :
    ∑ p ∈ windowPrimes R u, ‖windowWeight g u p‖ ^ 2 ≤ Real.log 4 * Real.exp R * (u + R) := by
  have hterm : ∀ p ∈ windowPrimes R u,
      ‖windowWeight g u p‖ ^ 2 ≤ Real.exp (-u) * (u + R) * Real.log p := by
    intro p hp
    obtain ⟨hpN, hpp⟩ := Nat.mem_primesLE.mp hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    have hlog0 : 0 ≤ Real.log p := Real.log_nonneg hp1
    have hpe : (p : ℝ) ≤ Real.exp (u + R) :=
      (Nat.cast_le.mpr hpN).trans (Nat.floor_le (Real.exp_pos _).le)
    have hlogle : Real.log p ≤ u + R := by
      calc Real.log p ≤ Real.log (Real.exp (u + R)) := Real.log_le_log (by linarith) hpe
        _ = u + R := Real.log_exp _
    have hg2 : g (Real.log p - u) ^ 2 ≤ 1 := by
      have h := hg (Real.log p - u)
      rw [← sq_abs]
      nlinarith [abs_nonneg (g (Real.log p - u))]
    have hexp : Real.exp (-(u / 2)) ^ 2 = Real.exp (-u) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [windowWeight, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, mul_pow, hexp]
    have he : 0 < Real.exp (-u) := Real.exp_pos _
    calc Real.exp (-u) * Real.log p ^ 2 * g (Real.log p - u) ^ 2
        ≤ Real.exp (-u) * Real.log p ^ 2 * 1 := by gcongr
      _ ≤ Real.exp (-u) * (u + R) * Real.log p := by
        have : Real.log p ^ 2 ≤ (u + R) * Real.log p := by nlinarith
        nlinarith
  have hθ := Chebyshev.theta_le_log4_mul_x (Real.exp_pos (u + R)).le
  rw [Chebyshev.theta_eq_sum_primesLE] at hθ
  calc ∑ p ∈ windowPrimes R u, ‖windowWeight g u p‖ ^ 2
      ≤ ∑ p ∈ windowPrimes R u, Real.exp (-u) * (u + R) * Real.log p := Finset.sum_le_sum hterm
    _ = Real.exp (-u) * (u + R) * ∑ p ∈ windowPrimes R u, Real.log p := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-u) * (u + R) * (Real.log 4 * Real.exp (u + R)) := by
        exact mul_le_mul_of_nonneg_left hθ (mul_nonneg (Real.exp_pos _).le hu)
    _ = Real.log 4 * Real.exp R * (u + R) := by
        rw [Real.exp_add, Real.exp_neg]
        field_simp

/-- **The coinvariants of the window traces.** Uniformly in the degree and the fibre,
`∫ |T_x(u)|^{2k} dx ≤ k! (log 4 · e^R · (u + R))^k`. -/
theorem integral_norm_fibreTrace_pow_le {g : ℝ → ℝ} (hg : ∀ v, |g v| ≤ 1) {R u : ℝ}
    (hu : 0 ≤ u + R) (k : ℕ) :
    ∫ x, ‖fibreTrace g R u x‖ ^ (2 * k) ∂gaugeHaar ≤
      k.factorial * (Real.log 4 * Real.exp R * (u + R)) ^ k := by
  refine (integral_norm_twistSum_pow_le (fun p hp => (Nat.mem_primesLE.mp hp).2) _ k).trans ?_
  gcongr
  exact sum_norm_windowWeight_sq_le hg hu

/-- The mean tensor moment of the family: `≤ log 4 · N · k! (log 4 · e^R · (log N + R))^k`. -/
theorem integral_fibreMoment_le {g : ℝ → ℝ} (hg : ∀ v, |g v| ≤ 1) {R : ℝ} (hR : 0 ≤ R)
    (k N : ℕ) :
    ∫ x, fibreMoment g R k N x ∂gaugeHaar ≤
      Real.log 4 * N * (k.factorial * (Real.log 4 * Real.exp R * (Real.log N + R)) ^ k) := by
  have hint : ∀ p : ℕ, Integrable (fun x => ‖fibreTrace g R (Real.log p) x‖ ^ (2 * k)) gaugeHaar :=
    fun p => ((continuous_fibreTrace g R _).norm.pow _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold fibreMoment
  rw [integral_finsetSum _ fun p _ => (hint p).const_mul _]
  simp_rw [integral_const_mul]
  have hθ := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg (α := ℝ) N)
  rw [Chebyshev.theta_eq_sum_primesLE_log] at hθ
  calc ∑ p ∈ Nat.primesLE N, Real.log p * ∫ x, ‖fibreTrace g R (Real.log p) x‖ ^ (2 * k) ∂gaugeHaar
      ≤ ∑ p ∈ Nat.primesLE N, Real.log p *
          (k.factorial * (Real.log 4 * Real.exp R * (Real.log N + R)) ^ k) := by
        refine Finset.sum_le_sum fun p hp => ?_
        obtain ⟨hpN, hpp⟩ := Nat.mem_primesLE.mp hp
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
        have hlog0 : 0 ≤ Real.log p := Real.log_nonneg hp1
        have hlogN : Real.log p ≤ Real.log N :=
          Real.log_le_log (by linarith) (by exact_mod_cast hpN)
        refine mul_le_mul_of_nonneg_left ((integral_norm_fibreTrace_pow_le hg (by linarith) k).trans ?_)
          hlog0
        gcongr
    _ = (∑ p ∈ Nat.primesLE N, Real.log p) *
          (k.factorial * (Real.log 4 * Real.exp R * (Real.log N + R)) ^ k) := by
        rw [Finset.sum_mul]
    _ ≤ Real.log 4 * N * (k.factorial * (Real.log 4 * Real.exp R * (Real.log N + R)) ^ k) := by
        have h0 : 0 ≤ Real.log N + R := by
          rcases Nat.eq_zero_or_pos N with h | h
          · simp [h, hR]
          · have : (1 : ℝ) ≤ N := by exact_mod_cast h
            linarith [Real.log_nonneg this]
        gcongr

/-! ### Borel–Cantelli at the dyadic degrees -/

/-- At the dyadic degree `2^j` the exceptional set of the moment bound `2^{j(1+ε)}`. -/
def dyadicExceptional (g : ℝ → ℝ) (R : ℝ) (k : ℕ) (ε : ℝ) (j : ℕ) : Set GaugeTorus :=
  {x | (2 : ℝ) ^ ((j : ℝ) * (1 + ε)) ≤ fibreMoment g R k (2 ^ j) x}

theorem measureReal_dyadicExceptional_le {g : ℝ → ℝ} (hg : ∀ v, |g v| ≤ 1) {R : ℝ} (hR : 0 ≤ R)
    (k : ℕ) {ε : ℝ} (j : ℕ) :
    gaugeHaar.real (dyadicExceptional g R k ε j) ≤
      Real.log 4 * k.factorial * (Real.log 4 * Real.exp R * (1 + R)) ^ k *
        (((j : ℝ) + 1) ^ k * ((2 : ℝ) ^ (-ε)) ^ j) := by
  set L := Real.log 4 * Real.exp R with hLdef
  have hL : 0 ≤ L := by positivity
  set c : ℝ := (2 : ℝ) ^ ((j : ℝ) * (1 + ε)) with hcdef
  have hc : 0 < c := by positivity
  have hM := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fibreMoment_nonneg g R k (2 ^ j)))
    (integrable_fibreMoment g R k (2 ^ j)) c
  have hE := integral_fibreMoment_le hg hR k (2 ^ j)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogj : Real.log ((2 ^ j : ℕ) : ℝ) = j * Real.log 2 := by
    push_cast; rw [Real.log_pow]
  have hlog : Real.log ((2 ^ j : ℕ) : ℝ) + R ≤ (1 + R) * ((j : ℝ) + 1) := by
    rw [hlogj]
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9; linarith
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  have h0 : 0 ≤ Real.log ((2 ^ j : ℕ) : ℝ) + R := by
    rw [hlogj]; positivity
  have hsplit : c = (2 : ℝ) ^ j * ((2 : ℝ) ^ ε) ^ j := by
    rw [hcdef, show (j : ℝ) * (1 + ε) = (j : ℝ) + ε * j by ring, Real.rpow_add (by norm_num),
      Real.rpow_natCast, Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have hneg : ((2 : ℝ) ^ (-ε)) ^ j * ((2 : ℝ) ^ ε) ^ j = 1 := by
    rw [← mul_pow, ← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero, one_pow]
  have hpow : (L * (Real.log ((2 ^ j : ℕ) : ℝ) + R)) ^ k ≤ (L * ((1 + R) * ((j : ℝ) + 1))) ^ k :=
    pow_le_pow_left₀ (mul_nonneg hL h0) (mul_le_mul_of_nonneg_left hlog hL) k
  have hE' : ∫ x, fibreMoment g R k (2 ^ j) x ∂gaugeHaar ≤
      c * (Real.log 4 * k.factorial * (L * (1 + R)) ^ k *
        (((j : ℝ) + 1) ^ k * ((2 : ℝ) ^ (-ε)) ^ j)) := by
    refine hE.trans ?_
    calc Real.log 4 * ((2 ^ j : ℕ) : ℝ) * (k.factorial * (L * (Real.log ((2 ^ j : ℕ) : ℝ) + R)) ^ k)
        ≤ Real.log 4 * ((2 ^ j : ℕ) : ℝ) * (k.factorial * (L * ((1 + R) * ((j : ℝ) + 1))) ^ k) := by
          gcongr
      _ = Real.log 4 * k.factorial * (L * (1 + R)) ^ k * ((j : ℝ) + 1) ^ k * (2 : ℝ) ^ j * 1 := by
          rw [show L * ((1 + R) * ((j : ℝ) + 1)) = (L * (1 + R)) * ((j : ℝ) + 1) by ring, mul_pow]
          push_cast; ring
      _ = Real.log 4 * k.factorial * (L * (1 + R)) ^ k * ((j : ℝ) + 1) ^ k * (2 : ℝ) ^ j *
            (((2 : ℝ) ^ (-ε)) ^ j * ((2 : ℝ) ^ ε) ^ j) := by rw [hneg]
      _ = c * (Real.log 4 * k.factorial * (L * (1 + R)) ^ k *
            (((j : ℝ) + 1) ^ k * ((2 : ℝ) ^ (-ε)) ^ j)) := by rw [hsplit]; ring
  exact le_of_mul_le_mul_left (hM.trans hE') hc

theorem summable_poly_mul_geometric (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable fun j : ℕ => ((j : ℝ) + 1) ^ k * r ^ j := by
  have hs : Summable fun n : ℕ => (n : ℝ) ^ k * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one k (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0])
  have hs1 := (summable_nat_add_iff 1).mpr hs
  rcases hr0.eq_or_lt with h | h
  · subst h
    refine summable_of_ne_finset_zero (s := {0}) fun j hj => ?_
    have : j ≠ 0 := by simpa using hj
    simp [zero_pow this]
  · have := hs1.mul_left r⁻¹
    refine this.congr fun j => ?_
    push_cast
    rw [pow_succ]
    field_simp

/-- **Borel–Cantelli at the dyadic degrees.** For Haar-a.e. fibre the moment at `2^j` is
eventually below `2^{j(1+ε)}`. -/
theorem ae_eventually_fibreMoment_dyadic_lt {g : ℝ → ℝ} (hg : ∀ v, |g v| ≤ 1) {R : ℝ}
    (hR : 0 ≤ R) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂gaugeHaar, ∀ᶠ j : ℕ in atTop,
      fibreMoment g R k (2 ^ j) x < (2 : ℝ) ^ ((j : ℝ) * (1 + ε)) := by
  set A : ℝ := Real.log 4 * k.factorial * (Real.log 4 * Real.exp R * (1 + R)) ^ k
  have hA : 0 ≤ A := by positivity
  have hr0 : 0 ≤ (2 : ℝ) ^ (-ε) := by positivity
  have hr1 : (2 : ℝ) ^ (-ε) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hsum : Summable fun j : ℕ => A * (((j : ℝ) + 1) ^ k * ((2 : ℝ) ^ (-ε)) ^ j) :=
    (summable_poly_mul_geometric k hr0 hr1).mul_left A
  have hfin : (∑' j, gaugeHaar (dyadicExceptional g R k ε j)) ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' j : ℕ,
      A * (((j : ℝ) + 1) ^ k * ((2 : ℝ) ^ (-ε)) ^ j))) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsum]
    refine ENNReal.tsum_le_tsum fun j => ?_
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (measureReal_dyadicExceptional_le hg hR k j)
  filter_upwards [ae_eventually_notMem hfin] with x hx
  refine hx.mono fun j hj => ?_
  simpa [dyadicExceptional, not_le] using hj

/-! ### The generic fibre -/

/-- A dyadic bound for all `j ≥ J` gives a polynomial bound at every degree. -/
theorem fibreMoment_le_of_dyadic {g : ℝ → ℝ} {R : ℝ} {k : ℕ} {ε : ℝ} (hε : 0 < ε)
    {x : GaugeTorus} {J : ℕ}
    (hJ : ∀ j, J ≤ j → fibreMoment g R k (2 ^ j) x < (2 : ℝ) ^ ((j : ℝ) * (1 + ε))) :
    ∃ C : ℝ, ∀ N : ℕ, fibreMoment g R k N x ≤ C * ((N : ℝ) + 1) ^ (1 + ε) := by
  set C₁ := fibreMoment g R k (2 ^ J) x
  refine ⟨max C₁ ((2 : ℝ) ^ (1 + ε)), fun N => ?_⟩
  have hN1 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ (1 + ε) :=
    Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) N]) (by linarith)
  have hC₁ : 0 ≤ C₁ := fibreMoment_nonneg g R k _ x
  by_cases hNJ : N ≤ 2 ^ J
  · calc fibreMoment g R k N x ≤ C₁ := fibreMoment_mono g R k x hNJ
      _ ≤ max C₁ ((2 : ℝ) ^ (1 + ε)) := le_max_left _ _
      _ ≤ max C₁ ((2 : ℝ) ^ (1 + ε)) * ((N : ℝ) + 1) ^ (1 + ε) :=
          le_mul_of_one_le_right (hC₁.trans (le_max_left _ _)) hN1
  · push Not at hNJ
    set j := Nat.clog 2 N
    have hN2 : 1 < N := lt_of_le_of_lt (Nat.one_le_two_pow) hNJ
    have hNj : N ≤ 2 ^ j := Nat.le_pow_clog (by norm_num) N
    have hJj : J ≤ j := by
      by_contra h
      push Not at h
      have : 2 ^ j ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) h.le
      omega
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · rw [h, pow_zero] at hNj; omega
      · exact h
    have hpred : 2 ^ (j - 1) < N := by
      have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hN2
      simpa [Nat.pred_eq_sub_one] using this
    have h2j : ((2 : ℝ) ^ j) ≤ 2 * ((N : ℝ) + 1) := by
      have : 2 ^ j = 2 * 2 ^ (j - 1) := by
        rw [← pow_succ']; congr 1; omega
      have h' : (2 : ℝ) ^ j = 2 * (2 : ℝ) ^ (j - 1) := by exact_mod_cast this
      have h'' : ((2 : ℝ) ^ (j - 1)) ≤ N := by exact_mod_cast hpred.le
      rw [h']; linarith
    calc fibreMoment g R k N x ≤ fibreMoment g R k (2 ^ j) x := fibreMoment_mono g R k x hNj
      _ ≤ (2 : ℝ) ^ ((j : ℝ) * (1 + ε)) := (hJ j hJj).le
      _ = ((2 : ℝ) ^ j) ^ (1 + ε) := by
          rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
      _ ≤ (2 * ((N : ℝ) + 1)) ^ (1 + ε) := by
          gcongr
      _ = (2 : ℝ) ^ (1 + ε) * ((N : ℝ) + 1) ^ (1 + ε) :=
          Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ max C₁ ((2 : ℝ) ^ (1 + ε)) * ((N : ℝ) + 1) ^ (1 + ε) := by
          gcongr
          exact le_max_right _ _

/-- **The generic fibre has uniform weights** (milestone M2). For Haar-almost every fibre of the
gauge family, every tensor power `k` and every `ε > 0` there is `C` with
`Σ_{p ≤ N} log p · |T_x(log p)|^{2k} ≤ C (N + 1)^{1+ε}` for all `N`. -/
theorem ae_fibreMoment_le {g : ℝ → ℝ} (hg : ∀ v, |g v| ≤ 1) {R : ℝ} (hR : 0 ≤ R) :
    ∀ᵐ x ∂gaugeHaar, ∀ k : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, ∀ N : ℕ, fibreMoment g R k N x ≤ C * ((N : ℝ) + 1) ^ (1 + ε) := by
  have h : ∀ᵐ x ∂gaugeHaar, ∀ k m : ℕ, ∀ᶠ j : ℕ in atTop,
      fibreMoment g R k (2 ^ j) x < (2 : ℝ) ^ ((j : ℝ) * (1 + 1 / ((m : ℝ) + 1))) := by
    rw [ae_all_iff]; intro k
    rw [ae_all_iff]; intro m
    exact ae_eventually_fibreMoment_dyadic_lt hg hR k (by positivity)
  filter_upwards [h] with x hx k ε hε
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε)
  have hm' : 1 / ((m : ℝ) + 1) ≤ ε := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hm
    linarith
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp (hx k m)
  obtain ⟨C, hC⟩ := fibreMoment_le_of_dyadic (ε := 1 / ((m : ℝ) + 1)) (by positivity)
    (fun j hj => hJ j hj)
  refine ⟨max C 0, fun N => (hC N).trans ?_⟩
  have h1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  calc C * ((N : ℝ) + 1) ^ (1 + 1 / ((m : ℝ) + 1))
      ≤ max C 0 * ((N : ℝ) + 1) ^ (1 + 1 / ((m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * ((N : ℝ) + 1) ^ (1 + ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 (by linarith))
          (le_max_right _ _)

/-- **Deligne's conclusion at the generic fibre.** For Haar-almost every fibre the window traces
at the primes are `p^{o(1)}`. -/
theorem ae_norm_fibreTrace_le {g : ℝ → ℝ} (hg : ∀ v, |g v| ≤ 1) {R : ℝ} (hR : 0 ≤ R) :
    ∀ᵐ x ∂gaugeHaar, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ p : ℕ, p.Prime →
      ‖fibreTrace g R (Real.log p) x‖ ≤ C * (p : ℝ) ^ ε := by
  filter_upwards [ae_fibreMoment_le hg hR] with x hx ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  have hk0 : 0 < k := by
    have : (0 : ℝ) < k := lt_trans (by positivity) hk
    exact_mod_cast this
  obtain ⟨C, hC⟩ := hx k 1 one_pos
  set D : ℝ := max C 0 * 4 / Real.log 2
  have hD : 0 ≤ D := by
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    positivity
  refine ⟨D ^ (((2 * k : ℕ) : ℝ)⁻¹), fun p hp => ?_⟩
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hlog2 : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set a := ‖fibreTrace g R (Real.log p) x‖
  have ha : 0 ≤ a := norm_nonneg _
  -- one term of the `k`-th moment at `N = p`
  have hone : Real.log p * a ^ (2 * k) ≤ fibreMoment g R k p x := by
    have hmem : p ∈ Nat.primesLE p := Nat.mem_primesLE.mpr ⟨le_rfl, hp⟩
    refine Finset.single_le_sum (f := fun q : ℕ => Real.log q *
      ‖fibreTrace g R (Real.log q) x‖ ^ (2 * k)) (fun q hq => mul_nonneg
        (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hq).2.one_lt.le))
        (by positivity)) hmem
  have hsq : ((p : ℝ) + 1) ^ (1 + (1 : ℝ)) ≤ 4 * (p : ℝ) ^ (2 : ℕ) := by
    rw [show (1 + (1 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith
  have hpow : a ^ (2 * k) ≤ D * (p : ℝ) ^ (2 : ℕ) := by
    have h1 : Real.log 2 * a ^ (2 * k) ≤ max C 0 * (4 * (p : ℝ) ^ (2 : ℕ)) := by
      calc Real.log 2 * a ^ (2 * k) ≤ Real.log p * a ^ (2 * k) := by gcongr
        _ ≤ fibreMoment g R k p x := hone
        _ ≤ C * ((p : ℝ) + 1) ^ (1 + (1 : ℝ)) := hC p
        _ ≤ max C 0 * ((p : ℝ) + 1) ^ (1 + (1 : ℝ)) := by gcongr; exact le_max_left _ _
        _ ≤ max C 0 * (4 * (p : ℝ) ^ (2 : ℕ)) := by gcongr
    rw [show D * (p : ℝ) ^ (2 : ℕ) = max C 0 * (4 * (p : ℝ) ^ (2 : ℕ)) / Real.log 2 by
      simp only [D]; ring]
    rw [le_div_iff₀ hlog2pos]
    linarith
  -- take the `2k`-th root
  have h2k : (2 * k : ℕ) ≠ 0 := by omega
  have hroot : a ≤ (D * (p : ℝ) ^ (2 : ℕ)) ^ (((2 * k : ℕ) : ℝ)⁻¹) := by
    have h := Real.rpow_le_rpow (pow_nonneg ha _) hpow (inv_nonneg.mpr (Nat.cast_nonneg (2 * k)))
    rwa [Real.pow_rpow_inv_natCast ha h2k] at h
  have hexp : (2 : ℝ) * (((2 * k : ℕ) : ℝ)⁻¹) ≤ ε := by
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
    rw [div_lt_iff₀ hε] at hk
    push_cast
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (two_ne_zero), one_mul, inv_le_iff_one_le_mul₀ hk']
    linarith
  calc a ≤ (D * (p : ℝ) ^ (2 : ℕ)) ^ (((2 * k : ℕ) : ℝ)⁻¹) := hroot
    _ = D ^ (((2 * k : ℕ) : ℝ)⁻¹) * (p : ℝ) ^ ((2 : ℝ) * (((2 * k : ℕ) : ℝ)⁻¹)) := by
        rw [Real.mul_rpow hD (by positivity), show ((p : ℝ) ^ (2 : ℕ)) = (p : ℝ) ^ ((2 : ℕ) : ℝ) from
          (Real.rpow_natCast _ _).symm, ← Real.rpow_mul hp0.le]
        norm_num
    _ ≤ D ^ (((2 * k : ℕ) : ℝ)⁻¹) * (p : ℝ) ^ ε := by
        gcongr
        exact_mod_cast hp.one_lt.le

end GaloisForLFunctions.ArithmeticWeightTheory
