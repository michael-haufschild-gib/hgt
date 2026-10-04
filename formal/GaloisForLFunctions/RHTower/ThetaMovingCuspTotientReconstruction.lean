import GaloisForLFunctions.RHTower.ThetaMovingCuspDualSource
import GaloisForLFunctions.RHTower.ThetaMovingCuspSignedTotientInverse
import GaloisForLFunctions.RHTower.ThetaOneSidedBernsteinGauge
import GaloisForLFunctions.RHTower.Sieve.SquarefreeDivisorProduct

/-!
# Moving-cusp reflection: signed-totient atoms and positive totient reconstruction

Log-shift series compose by Dirichlet convolution of their weights.  Writing the completed theta
source over its seed atom `h(u) = e^{u/2} H(e^u)`, `k(u) = Σ_n n^{−1/2} h(u + log n)`, the cofinal
dual source becomes

```text
R_∞(u) = Σ_m A(m) m^{−1/2} h(u + log m),       A(m) = Σ_{e|m} μ(e)e = ∏_{p|m}(1 − p),   (4)
h(u)   = Σ_n φ(n) n^{−1/2} R_∞(u + log n),     A ⋆ φ = δ.                              (4a)
```

At a finite stage, `R_S(u) = Σ_m A_S(m) m^{−1/2} h(u + log m)` with
`A_S(m) = ∏_{p∈S, p|m}(1 − p)`, and the positive totient operator gives
`T_φ R_S(u) = Σ_{(m,P)=1} √m h(u + log m)` (4b), which tends to `h` locally uniformly along every
prime exhaustion.  Since `φ ≥ 0` and `h < 0` on a far negative ray, `R_∞` cannot be nonnegative.
-/

open MeasureTheory Set Filter Topology ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace RHTower

noncomputable section

/-! ## Composition of log-shift series -/

/-- Multiplicative (Dirichlet) convolution of weights. -/
def mulConvWeight (a b : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ p ∈ m.divisorsAntidiagonal, a p.1 * b p.2

theorem polyBoundedWeight_dirichletWeight {K L : ℕ} {a b : ℕ → ℝ} (ha : PolyBoundedWeight K a)
    (hb : PolyBoundedWeight L b) : PolyBoundedWeight (K + L + 1) (mulConvWeight a b) := by
  intro m
  rw [mulConvWeight]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ p ∈ m.divisorsAntidiagonal, |a p.1 * b p.2|
      ≤ ∑ p ∈ m.divisorsAntidiagonal, (m : ℝ) ^ (K + L) := by
        refine Finset.sum_le_sum fun p hp => ?_
        obtain ⟨hpm, hm0⟩ := Nat.mem_divisorsAntidiagonal.1 hp
        have h1 : (p.1 : ℝ) ≤ m := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) ⟨p.2, hpm.symm⟩
        have h2 : (p.2 : ℝ) ≤ m := by
          exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) ⟨p.1, by rw [← hpm]; ring⟩
        rw [abs_mul, pow_add]
        exact mul_le_mul ((ha _).trans (pow_le_pow_left₀ (Nat.cast_nonneg _) h1 K))
          ((hb _).trans (pow_le_pow_left₀ (Nat.cast_nonneg _) h2 L)) (abs_nonneg _) (by positivity)
    _ = (m.divisorsAntidiagonal.card : ℝ) * (m : ℝ) ^ (K + L) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (m : ℝ) * (m : ℝ) ^ (K + L) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [← Nat.map_div_right_divisors, Finset.card_map]
        exact_mod_cast Nat.card_divisors_le_self m
    _ = (m : ℝ) ^ (K + L + 1) := by ring

/-- A nonnegative double series vanishing on the axes is summable once its multiplicative fibre
sums are. -/
theorem summable_of_divisorsAntidiagonal_nonneg {F : ℕ × ℕ → ℝ} (hF : ∀ p, 0 ≤ F p)
    (h0 : ∀ p : ℕ × ℕ, (p.1 = 0 ∨ p.2 = 0) → F p = 0)
    (hs : Summable fun m : ℕ => ∑ p ∈ m.divisorsAntidiagonal, F p) : Summable F := by
  classical
  refine summable_of_sum_le hF (c := ∑' m : ℕ, ∑ p ∈ m.divisorsAntidiagonal, F p) fun s => ?_
  set g : ℕ × ℕ → ℕ := fun p => p.1 * p.2
  rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image g) (g := g)
    (fun p hp => Finset.mem_image_of_mem g hp)]
  refine le_trans ?_ (Summable.sum_le_tsum (s.image g)
    (fun m _ => Finset.sum_nonneg fun p _ => hF p) hs)
  refine Finset.sum_le_sum fun m _ => ?_
  calc ∑ p ∈ s with g p = m, F p
      = ∑ p ∈ (s.filter fun p => g p = m) with p ∈ m.divisorsAntidiagonal, F p := by
        refine (Finset.sum_filter_of_ne fun p hp hne => ?_).symm
        rw [Finset.mem_filter] at hp
        refine Nat.mem_divisorsAntidiagonal.2 ⟨hp.2, fun hm => hne ?_⟩
        exact h0 p (mul_eq_zero.1 (hp.2.trans hm))
    _ ≤ ∑ p ∈ m.divisorsAntidiagonal, F p :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => (Finset.mem_filter.1 hp).2)
          fun p _ _ => hF p

/-- **Composition of log-shift series.**  `Σ_e a_e Σ_n b_n f(u + log e + log n)
= Σ_m (a ⋆ b)(m) f(u + log m)`, with absolute convergence. -/
theorem GaussianLogTail.logShiftSeries_logShiftSeries {f : ℝ → ℝ} (hf : GaussianLogTail f)
    {K L : ℕ} {a b : ℕ → ℝ} (ha : PolyBoundedWeight K a) (hb : PolyBoundedWeight L b)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) (u : ℝ) :
    logShiftSeries a (logShiftSeries b f) u = logShiftSeries (mulConvWeight a b) f u := by
  set F : ℕ × ℕ → ℝ := fun p => a p.1 * b p.2 * f (u + Real.log ((p.1 * p.2 : ℕ) : ℝ))
  have hF0 : ∀ p : ℕ × ℕ, (p.1 = 0 ∨ p.2 = 0) → F p = 0 := by
    rintro p (h | h) <;> simp [F, h, ha0, hb0]
  have hmaj : Summable fun m : ℕ => (m : ℝ) ^ (K + L + 1) * |f (u + Real.log m)| := by
    have h := (hf.summable (K := K + L + 1) (a := fun m => (m : ℝ) ^ (K + L + 1))
      (fun m => by rw [abs_of_nonneg (by positivity)]) u).abs
    refine h.congr fun m => ?_
    rw [abs_mul, abs_of_nonneg (by positivity)]
  have hFs : Summable F := by
    refine Summable.of_abs (summable_of_divisorsAntidiagonal_nonneg (fun p => abs_nonneg _)
      (fun p hp => by rw [hF0 p hp, abs_zero]) ?_)
    refine Summable.of_nonneg_of_le (fun m => Finset.sum_nonneg fun p _ => abs_nonneg _)
      (fun m => ?_) hmaj
    calc ∑ p ∈ m.divisorsAntidiagonal, |F p|
        = ∑ p ∈ m.divisorsAntidiagonal, |a p.1 * b p.2| * |f (u + Real.log m)| := by
          refine Finset.sum_congr rfl fun p hp => ?_
          simp only [F, abs_mul]
          rw [(Nat.mem_divisorsAntidiagonal.1 hp).1]
      _ = (∑ p ∈ m.divisorsAntidiagonal, |a p.1 * b p.2|) * |f (u + Real.log m)| :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ (m : ℝ) ^ (K + L + 1) * |f (u + Real.log m)| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          have := polyBoundedWeight_dirichletWeight (fun n => abs_abs (a n) ▸ ha n)
            (fun n => abs_abs (b n) ▸ hb n) m
          rw [mulConvWeight] at this
          refine le_trans (le_of_eq ?_) (le_trans (le_abs_self _) this)
          exact Finset.sum_congr rfl fun p _ => by rw [abs_mul]
  have hrow : ∀ e : ℕ, a e * logShiftSeries b f (u + Real.log e) = ∑' n, F (e, n) := by
    intro e
    rw [logShiftSeries, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [F]
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp [ha0]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hb0]
    rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity), add_assoc]
    ring
  rw [logShiftSeries, tsum_congr hrow, ← hFs.tsum_prod' hFs.prod_factor,
    ← (hasSum_divisorsAntidiagonal_regroup hFs hF0).tsum_eq, logShiftSeries]
  refine tsum_congr fun m => ?_
  rw [mulConvWeight, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  simp only [F]
  rw [(Nat.mem_divisorsAntidiagonal.1 hp).1]

/-! ## The seed atom -/

/-- The seed atom `h(u) = e^{u/2} H(e^u)` in logarithmic coordinates. -/
def thetaSeedAtom (u : ℝ) : ℝ := thetaCuspSourceTerm u 1

theorem thetaSeedAtom_eq (u : ℝ) :
    thetaSeedAtom u = 2 * Real.pi * Real.exp (u / 2) *
      (2 * Real.pi * Real.exp (4 * u) - 3 * Real.exp (2 * u)) * Real.exp (-Real.pi * Real.exp (2 * u)) := by
  rw [thetaSeedAtom, thetaCuspSourceTerm, thetaCuspSeed, Nat.cast_one, one_mul]
  have h4 : Real.exp u ^ 4 = Real.exp (4 * u) := by rw [← Real.exp_nat_mul]; norm_num
  have h2 : Real.exp u ^ 2 = Real.exp (2 * u) := by rw [← Real.exp_nat_mul]; norm_num
  rw [h4, h2]; ring

theorem abs_thetaSeedAtom_le (u : ℝ) :
    |thetaSeedAtom u| ≤ 2 * Real.pi * Real.exp (u / 2) *
      ((2 * Real.pi + 3) * max (Real.exp (4 * u)) (Real.exp (2 * u))) *
        Real.exp (-Real.pi * Real.exp (2 * u)) := by
  rw [thetaSeedAtom_eq, abs_mul, abs_mul, abs_of_pos (Real.exp_pos (-Real.pi * Real.exp (2 * u))),
    abs_of_pos (show 0 < 2 * Real.pi * Real.exp (u / 2) by positivity)]
  gcongr
  have h4 := le_max_left (Real.exp (4 * u)) (Real.exp (2 * u))
  have h2 := le_max_right (Real.exp (4 * u)) (Real.exp (2 * u))
  rw [abs_le]; constructor <;> nlinarith [Real.pi_pos, Real.exp_pos (2 * u), Real.exp_pos (4 * u)]

theorem gaussianLogTail_thetaSeedAtom : GaussianLogTail thetaSeedAtom := by
  set c : ℝ := 2 * Real.pi * (2 * Real.pi + 3)
  have hc : 0 < c := by positivity
  have hpos : ∀ u, 0 ≤ u → |thetaSeedAtom u| ≤ c * Real.exp ((5 : ℕ) * u) *
      Real.exp (-Real.pi * Real.exp (2 * u)) := by
    intro u hu
    refine (abs_thetaSeedAtom_le u).trans ?_
    rw [max_eq_left (Real.exp_le_exp.2 (by linarith))]
    have h5 : Real.exp (u / 2) * Real.exp (4 * u) ≤ Real.exp ((5 : ℕ) * u) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by push_cast; linarith)
    calc 2 * Real.pi * Real.exp (u / 2) * ((2 * Real.pi + 3) * Real.exp (4 * u)) *
          Real.exp (-Real.pi * Real.exp (2 * u))
        = c * (Real.exp (u / 2) * Real.exp (4 * u)) * Real.exp (-Real.pi * Real.exp (2 * u)) := by
          simp only [c]; ring
      _ ≤ _ := by gcongr
  refine ⟨⟨c * Real.exp (((5 : ℕ) : ℝ) ^ 2 / (8 * Real.pi)) + c, by positivity, fun u => ?_⟩,
    ⟨c, 5, hc.le, hpos⟩⟩
  rcases le_total 0 u with hu | hu
  · refine (hpos u hu).trans ?_
    have := exp_mul_exp_neg_le ((5 : ℕ) : ℝ) u hu
    nlinarith
  · refine (abs_thetaSeedAtom_le u).trans ?_
    have e1 : Real.exp (u / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have e2 : max (Real.exp (4 * u)) (Real.exp (2 * u)) ≤ 1 :=
      max_le (Real.exp_le_one_iff.2 (by linarith)) (Real.exp_le_one_iff.2 (by linarith))
    have e3 : Real.exp (-Real.pi * Real.exp (2 * u)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, Real.exp_pos (2 * u)])
    calc 2 * Real.pi * Real.exp (u / 2) * ((2 * Real.pi + 3) * max (Real.exp (4 * u)) (Real.exp (2 * u))) *
          Real.exp (-Real.pi * Real.exp (2 * u))
        ≤ 2 * Real.pi * 1 * ((2 * Real.pi + 3) * 1) * 1 := by gcongr
      _ = c := by simp only [c]; ring
      _ ≤ _ := by have := Real.exp_pos (((5 : ℕ) : ℝ) ^ 2 / (8 * Real.pi)); nlinarith

/-- The atom weights `n^{−1/2}` (zero at `n = 0`). -/
def invSqrtWeight (n : ℕ) : ℝ := (n : ℝ) ^ (-(1 / 2 : ℝ))

theorem invSqrtWeight_zero : invSqrtWeight 0 = 0 := by
  simp [invSqrtWeight]

theorem polyBoundedWeight_invSqrtWeight : PolyBoundedWeight 0 invSqrtWeight := by
  intro n
  rw [pow_zero, invSqrtWeight, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]; norm_num
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by norm_num)

/-- The completed source is the log-shift series of its seed atom. -/
theorem thetaCuspFullSource_eq_logShiftSeries :
    thetaCuspFullSource = logShiftSeries invSqrtWeight thetaSeedAtom := by
  funext u
  rw [thetaCuspFullSource, logShiftSeries]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [invSqrtWeight_zero, thetaCuspSourceTerm, thetaCuspSeed]
  · rw [invSqrtWeight, thetaSeedAtom, rpow_neg_half_mul_thetaCuspSourceTerm_add_log hn, mul_one]

/-- The signed-totient atom weights `A(m) m^{−1/2}`. -/
def signedTotientAtomWeight (m : ℕ) : ℝ := signedTotientAF m * invSqrtWeight m

theorem abs_signedTotientAF_le (m : ℕ) : |signedTotientAF m| ≤ (m : ℝ) ^ 2 := by
  rw [signedTotientAF_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ a ∈ m.divisors, |((μ a : ℤ) : ℝ) * (a : ℝ)| ≤ ∑ a ∈ m.divisors, (m : ℝ) := by
        refine Finset.sum_le_sum fun a ha => ?_
        rw [abs_mul, Nat.abs_cast]
        have hμ : |((μ a : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have ham : (a : ℝ) ≤ m := by exact_mod_cast Nat.divisor_le ha
        nlinarith [abs_nonneg ((μ a : ℤ) : ℝ), (Nat.cast_nonneg a : (0:ℝ) ≤ a)]
    _ = (m.divisors.card : ℝ) * m := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (m : ℝ) * m := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.card_divisors_le_self m)
          (Nat.cast_nonneg _)
    _ = (m : ℝ) ^ 2 := by ring

theorem polyBoundedWeight_signedTotientAtomWeight : PolyBoundedWeight 2 signedTotientAtomWeight := by
  intro m
  rw [signedTotientAtomWeight, abs_mul]
  have h1 := polyBoundedWeight_invSqrtWeight m
  rw [pow_zero] at h1
  calc |signedTotientAF m| * |invSqrtWeight m| ≤ (m : ℝ) ^ 2 * 1 :=
        mul_le_mul (abs_signedTotientAF_le m) h1 (abs_nonneg _) (by positivity)
    _ = (m : ℝ) ^ 2 := mul_one _

theorem sqrt_mul_invSqrt_eq {e n : ℕ} :
    (e : ℝ) ^ (1 / 2 : ℝ) * invSqrtWeight n = (e : ℝ) * invSqrtWeight (e * n) := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hsplit : (e : ℝ) ^ (1 / 2 : ℝ) = (e : ℝ) * (e : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_one_add' heR.le (by norm_num)]; norm_num
  rw [invSqrtWeight, invSqrtWeight, Nat.cast_mul, Real.mul_rpow heR.le (Nat.cast_nonneg _), hsplit]
  ring

theorem dirichletWeight_movingCuspLimitWeight_invSqrtWeight (m : ℕ) :
    mulConvWeight movingCuspLimitWeight invSqrtWeight m = signedTotientAtomWeight m := by
  rw [mulConvWeight, signedTotientAtomWeight, signedTotientAF_apply, Finset.sum_mul,
    ← Nat.sum_divisorsAntidiagonal (f := fun a b => ((μ a : ℤ) : ℝ) * (a : ℝ) * invSqrtWeight m)]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [movingCuspLimitWeight, mul_assoc, sqrt_mul_invSqrt_eq, (Nat.mem_divisorsAntidiagonal.1 hp).1,
    mul_assoc]

/-- **(4) Signed-totient atom expansion.**  `R_∞(u) = Σ_m A(m) m^{−1/2} h(u + log m)`. -/
theorem movingCuspDualLimit_eq_signedTotientAtoms :
    movingCuspDualLimit = logShiftSeries signedTotientAtomWeight thetaSeedAtom := by
  funext u
  rw [movingCuspDualLimit, thetaCuspFullSource_eq_logShiftSeries,
    gaussianLogTail_thetaSeedAtom.logShiftSeries_logShiftSeries
      polyBoundedWeight_movingCuspLimitWeight polyBoundedWeight_invSqrtWeight
      (by simp [movingCuspLimitWeight]) invSqrtWeight_zero]
  congr 1
  funext m
  exact dirichletWeight_movingCuspLimitWeight_invSqrtWeight m

/-- **(4)** in atom form: `R_∞(u) = Σ_m A(m) a_m(u)`, with `a_m(u) = m^{−1/2} h(u + log m)`. -/
theorem movingCuspDualLimit_eq_tsum_signedTotientAF_mul_atom (u : ℝ) :
    movingCuspDualLimit u = ∑' m : ℕ, signedTotientAF m * thetaCuspSourceTerm u m := by
  rw [movingCuspDualLimit_eq_signedTotientAtoms, logShiftSeries]
  refine tsum_congr fun m => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [signedTotientAtomWeight, invSqrtWeight_zero]
  · rw [signedTotientAtomWeight, mul_assoc, invSqrtWeight, thetaSeedAtom,
      rpow_neg_half_mul_thetaCuspSourceTerm_add_log hm, mul_one]

theorem signedTotientAF_isMultiplicative : signedTotientAF.IsMultiplicative := by
  rw [signedTotientAF, weightedMobiusAF]
  exact (isMultiplicative_moebius.intCast.pmul isMultiplicative_id.natCast).mul
    isMultiplicative_zeta.natCast

/-- **(4)** `A(m) = ∏_{p|m}(1 − p)`. -/
theorem signedTotientAF_eq_prod_primeFactors {m : ℕ} (hm : m ≠ 0) :
    signedTotientAF m = ∏ p ∈ m.primeFactors, (1 - (p : ℝ)) := by
  have h := (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers signedTotientAF
    signedTotientAF_isMultiplicative (prodPrimeFactors fun p => 1 - (p : ℝ))
    (ArithmeticFunction.IsMultiplicative.prodPrimeFactors _)).2 fun p i hp => by
      rw [signedTotientAF_apply]
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp
      rw [prodPrimeFactors_apply (pow_ne_zero _ hp.ne_zero), Nat.primeFactors_prime_pow hi.ne' hp,
        Finset.prod_singleton, Nat.sum_divisors_prime_pow hp]
      rw [Finset.sum_range_succ', Finset.sum_eq_single 0]
      · simp [ArithmeticFunction.moebius_apply_prime hp]; ring
      · intro j _ hj
        rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
        simp
      · intro h; simp at h; omega
  rw [h, prodPrimeFactors_apply hm]

/-! ## Positive totient reconstruction -/

/-- The positive totient weights `φ(n) n^{−1/2}`. -/
def totientAtomWeight (n : ℕ) : ℝ := eulerTotientAF n * invSqrtWeight n

theorem abs_eulerTotientAF_le (n : ℕ) : |eulerTotientAF n| ≤ (n : ℝ) ^ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [eulerTotientAF_apply n hn, abs_of_nonneg (Nat.cast_nonneg _), pow_one]
  exact_mod_cast Nat.totient_le n

theorem polyBoundedWeight_totientAtomWeight : PolyBoundedWeight 1 totientAtomWeight := by
  intro n
  rw [totientAtomWeight, abs_mul]
  have h1 := polyBoundedWeight_invSqrtWeight n
  rw [pow_zero] at h1
  calc |eulerTotientAF n| * |invSqrtWeight n| ≤ (n : ℝ) ^ 1 * 1 :=
        mul_le_mul (abs_eulerTotientAF_le n) h1 (abs_nonneg _) (by positivity)
    _ = (n : ℝ) ^ 1 := mul_one _

theorem invSqrtWeight_mul {e n : ℕ} : invSqrtWeight e * invSqrtWeight n = invSqrtWeight (e * n) := by
  rw [invSqrtWeight, invSqrtWeight, invSqrtWeight, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

theorem dirichletWeight_atomWeights (f g : ArithmeticFunction ℝ) (m : ℕ) :
    mulConvWeight (fun n => f n * invSqrtWeight n) (fun n => g n * invSqrtWeight n) m =
      (f * g) m * invSqrtWeight m := by
  rw [mulConvWeight, mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← (Nat.mem_divisorsAntidiagonal.1 hp).1, ← invSqrtWeight_mul]
  ring

/-- **(4a) Positive totient reconstruction.**  `h(u) = Σ_n φ(n) n^{−1/2} R_∞(u + log n)`. -/
theorem thetaSeedAtom_eq_totient_reconstruction (u : ℝ) :
    thetaSeedAtom u = logShiftSeries totientAtomWeight movingCuspDualLimit u := by
  rw [movingCuspDualLimit_eq_signedTotientAtoms,
    gaussianLogTail_thetaSeedAtom.logShiftSeries_logShiftSeries polyBoundedWeight_totientAtomWeight
      polyBoundedWeight_signedTotientAtomWeight (by simp [totientAtomWeight, invSqrtWeight_zero])
      (by simp [signedTotientAtomWeight, invSqrtWeight_zero])]
  have hw : mulConvWeight totientAtomWeight signedTotientAtomWeight =
      fun m => if m = 1 then 1 else 0 := by
    funext m
    rw [show totientAtomWeight = fun n => eulerTotientAF n * invSqrtWeight n from rfl,
      show signedTotientAtomWeight = fun n => signedTotientAF n * invSqrtWeight n from rfl,
      dirichletWeight_atomWeights, mul_comm eulerTotientAF, signedTotientAF_mul_eulerTotientAF]
    by_cases hm : m = 1
    · subst hm; simp [invSqrtWeight]
    · simp [hm]
  rw [hw, logShiftSeries, tsum_eq_single 1]
  · simp
  · intro n hn; simp [hn]

theorem thetaSeedAtom_neg_of_le {u : ℝ} (hu : u ≤ -1) : thetaSeedAtom u < 0 := by
  rw [thetaSeedAtom_eq]
  have h1 : Real.exp (2 * u) ≤ Real.exp (-2) := Real.exp_le_exp.2 (by linarith)
  have h2 : Real.exp (-2) < 1 / 4 := by
    have := Real.exp_one_gt_d9
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 2) (by norm_num), show (2:ℝ) = 1 + 1 by norm_num,
      Real.exp_add]
    nlinarith
  have h4 : Real.exp (4 * u) = Real.exp (2 * u) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
  have he := Real.exp_pos (2 * u)
  have hneg : 2 * Real.pi * Real.exp (4 * u) - 3 * Real.exp (2 * u) < 0 := by
    rw [h4]; nlinarith [Real.pi_lt_four]
  have hpos : 0 < 2 * Real.pi * Real.exp (u / 2) := by positivity
  have := mul_neg_of_pos_of_neg hpos hneg
  exact mul_neg_of_neg_of_pos this (Real.exp_pos _)

/-- **Second proof of the sign obstruction.**  `φ ≥ 0` while the seed is negative on the far
negative ray, so `R_∞ ≥ 0` would contradict (4a). -/
theorem not_forall_movingCuspDualLimit_nonneg' : ¬ ∀ u, 0 ≤ movingCuspDualLimit u := by
  intro h
  have hrec := thetaSeedAtom_eq_totient_reconstruction (-1)
  have hnn : 0 ≤ logShiftSeries totientAtomWeight movingCuspDualLimit (-1) :=
    tsum_nonneg fun n => mul_nonneg (mul_nonneg (by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [eulerTotientAF_apply n hn]; positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (h _)
  linarith [thetaSeedAtom_neg_of_le (le_refl (-1 : ℝ))]

/-! ## The finite stage (4b) -/

/-- The divisors of `m` that divide `P = ∏S` are the divisors of `∏_{p∈S, p|m} p`. -/
theorem divisors_filter_dvd_prod_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {m : ℕ} (hm : m ≠ 0) :
    m.divisors.filter (· ∣ ∏ p ∈ S, p) = (∏ p ∈ S.filter (· ∣ m), p).divisors := by
  ext e
  have hsP : (∏ p ∈ S.filter (· ∣ m), p) ∣ ∏ p ∈ S, p :=
    Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
  have hsm : (∏ p ∈ S.filter (· ∣ m), p) ∣ m :=
    Finset.prod_primes_dvd m (fun p hp => (hS p (Finset.mem_filter.1 hp).1).prime)
      (fun p hp => (Finset.mem_filter.1 hp).2)
  have hs0 : (∏ p ∈ S.filter (· ∣ m), p) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p hp => (hS p (Finset.mem_filter.1 hp).1).ne_zero
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hem, -⟩, heP⟩
    refine ⟨?_, hs0⟩
    have hsq : Squarefree e := Squarefree.squarefree_of_dvd heP (Sieve.prodDistinctPrimes_squarefree S hS)
    rw [← Nat.prod_primeFactors_of_squarefree hsq]
    refine Finset.prod_dvd_prod_of_subset _ _ _ fun p hp => Finset.mem_filter.2 ⟨?_, ?_⟩
    · obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_of_mem_primeFactors hp).prime
        (fun q => q)).1 ((Nat.dvd_of_mem_primeFactors hp).trans heP)
      rwa [(Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hp) (hS q hq)).1 hpq]
    · exact (Nat.dvd_of_mem_primeFactors hp).trans hem
  · rintro ⟨hes, -⟩
    exact ⟨⟨hes.trans hsm, hm⟩, hes.trans hsP⟩

/-- The finite signed-totient coefficient `A_S(m) = Σ_{e|m, e|P} μ(e) e`. -/
def finiteSignedTotient (S : Finset ℕ) (m : ℕ) : ℝ :=
  ∑ e ∈ m.divisors with e ∣ ∏ p ∈ S, p, ((μ e : ℤ) : ℝ) * (e : ℝ)

/-- **(4b)** `A_S(m) = ∏_{p∈S, p|m}(1 − p)`. -/
theorem finiteSignedTotient_eq_prod {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {m : ℕ} (hm : m ≠ 0) :
    finiteSignedTotient S m = ∏ p ∈ S.filter (· ∣ m), (1 - (p : ℝ)) := by
  have hs : ∀ p ∈ S.filter (· ∣ m), p.Prime := fun p hp => hS p (Finset.mem_filter.1 hp).1
  rw [finiteSignedTotient, divisors_filter_dvd_prod_primes hS hm, Sieve.sum_divisors_prod_primes_eq hs,
    show (∏ p ∈ S.filter (· ∣ m), (1 - (p : ℝ))) = ∏ p ∈ S.filter (· ∣ m), (-(p : ℝ) + 1) from
      Finset.prod_congr rfl fun p _ => by ring, Finset.prod_add]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hTp : ∀ p ∈ T, p.Prime := fun p hp => hs p (Finset.mem_powerset.1 hT hp)
  rw [moebius_prod_of_primes hTp, Finset.prod_neg, Finset.prod_const_one, mul_one]
  push_cast
  ring

theorem dirichletWeight_movingCuspWeight_invSqrtWeight (S : Finset ℕ) (m : ℕ) :
    mulConvWeight (movingCuspWeight S) invSqrtWeight m = finiteSignedTotient S m * invSqrtWeight m := by
  rw [mulConvWeight, finiteSignedTotient, Finset.sum_filter, Finset.sum_mul,
    ← Nat.sum_divisorsAntidiagonal (f := fun a b => (if a ∣ ∏ p ∈ S, p then
      ((μ a : ℤ) : ℝ) * (a : ℝ) else 0) * invSqrtWeight m)]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [movingCuspWeight]
  split_ifs
  · rw [mul_assoc, sqrt_mul_invSqrt_eq, (Nat.mem_divisorsAntidiagonal.1 hp).1, mul_assoc]
  · simp

theorem abs_finiteSignedTotient_le (S : Finset ℕ) (m : ℕ) : |finiteSignedTotient S m| ≤ (m : ℝ) ^ 2 := by
  rw [finiteSignedTotient]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ a ∈ m.divisors with a ∣ ∏ p ∈ S, p, |((μ a : ℤ) : ℝ) * (a : ℝ)|
      ≤ ∑ a ∈ m.divisors, |((μ a : ℤ) : ℝ) * (a : ℝ)| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => abs_nonneg _
    _ ≤ ∑ a ∈ m.divisors, (m : ℝ) := by
        refine Finset.sum_le_sum fun a ha => ?_
        rw [abs_mul, Nat.abs_cast]
        have hμ : |((μ a : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have ham : (a : ℝ) ≤ m := by exact_mod_cast Nat.divisor_le ha
        nlinarith [abs_nonneg ((μ a : ℤ) : ℝ), (Nat.cast_nonneg a : (0:ℝ) ≤ a)]
    _ = (m.divisors.card : ℝ) * m := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (m : ℝ) * m := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.card_divisors_le_self m)
          (Nat.cast_nonneg _)
    _ = (m : ℝ) ^ 2 := by ring

theorem polyBoundedWeight_finiteSignedTotientAtom (S : Finset ℕ) :
    PolyBoundedWeight 2 (fun m => finiteSignedTotient S m * invSqrtWeight m) := by
  intro m
  rw [abs_mul]
  have h1 := polyBoundedWeight_invSqrtWeight m
  rw [pow_zero] at h1
  calc |finiteSignedTotient S m| * |invSqrtWeight m| ≤ (m : ℝ) ^ 2 * 1 :=
        mul_le_mul (abs_finiteSignedTotient_le S m) h1 (abs_nonneg _) (by positivity)
    _ = (m : ℝ) ^ 2 := mul_one _

/-- **(4b)** `R_S(u) = Σ_m A_S(m) m^{−1/2} h(u + log m)`. -/
theorem movingCuspSource_eq_finiteSignedTotientAtoms {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    movingCuspSource S thetaCuspFullSource =
      logShiftSeries (fun m => finiteSignedTotient S m * invSqrtWeight m) thetaSeedAtom := by
  funext u
  rw [movingCuspSource_eq_logShiftSeries hS, thetaCuspFullSource_eq_logShiftSeries,
    gaussianLogTail_thetaSeedAtom.logShiftSeries_logShiftSeries (polyBoundedWeight_movingCuspWeight S)
      polyBoundedWeight_invSqrtWeight (by simp [movingCuspWeight]) invSqrtWeight_zero]
  congr 1
  funext m
  exact dirichletWeight_movingCuspWeight_invSqrtWeight S m

/-- The finite signed-totient arithmetic function. -/
def finiteSignedTotientAF (S : Finset ℕ) : ArithmeticFunction ℝ :=
  ⟨finiteSignedTotient S, by simp [finiteSignedTotient]⟩

/-- The `P`-restricted Möbius function. -/
def restrictedMoebiusAF (S : Finset ℕ) : ArithmeticFunction ℝ :=
  ⟨fun e => if e ∣ ∏ p ∈ S, p then ((μ e : ℤ) : ℝ) else 0, by simp⟩

theorem finiteSignedTotientAF_eq (S : Finset ℕ) :
    finiteSignedTotientAF S = ((restrictedMoebiusAF S).pmul ArithmeticFunction.id) * ζ := by
  ext m
  rw [coe_mul_zeta_apply]
  change finiteSignedTotient S m = _
  rw [finiteSignedTotient, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [pmul_apply, restrictedMoebiusAF, ArithmeticFunction.coe_mk, natCoe_apply, id_apply]
  split_ifs <;> simp

/-- **(4b) arithmetic.**  `(φ ⋆ A_S)(m) = m · 1_{(m,P)=1}`. -/
theorem eulerTotientAF_mul_finiteSignedTotientAF {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {m : ℕ}
    (hm : m ≠ 0) :
    (eulerTotientAF * finiteSignedTotientAF S) m = if ∀ p ∈ S, ¬ p ∣ m then (m : ℝ) else 0 := by
  have h1 : eulerTotientAF * finiteSignedTotientAF S =
      ((ζ : ArithmeticFunction ℝ) * restrictedMoebiusAF S).pmul ArithmeticFunction.id := by
    rw [finiteSignedTotientAF_eq, eulerTotientAF, ← pmul_id_mul, zeta_pmul]
    calc (μ : ArithmeticFunction ℝ) * ArithmeticFunction.id *
          ((restrictedMoebiusAF S).pmul ArithmeticFunction.id * ζ)
        = ((μ : ArithmeticFunction ℝ) * ζ) * (ArithmeticFunction.id *
            (restrictedMoebiusAF S).pmul ArithmeticFunction.id) := by ac_rfl
      _ = _ := by
          rw [coe_moebius_mul_coe_zeta, one_mul]
  rw [h1, pmul_apply, coe_zeta_mul_apply, natCoe_apply, id_apply]
  have hsum : ∑ i ∈ m.divisors, restrictedMoebiusAF S i =
      ∑ e ∈ (∏ p ∈ S.filter (· ∣ m), p).divisors, ((μ e : ℤ) : ℝ) := by
    rw [← divisors_filter_dvd_prod_primes hS hm, Finset.sum_filter]
    rfl
  have hone := congrArg (fun f : ArithmeticFunction ℝ => f (∏ p ∈ S.filter (· ∣ m), p))
    (coe_zeta_mul_coe_moebius (R := ℝ))
  simp only [coe_zeta_mul_apply, intCoe_apply, one_apply] at hone
  rw [hsum, hone]
  have hiff : (∏ p ∈ S.filter (· ∣ m), p) = 1 ↔ ∀ p ∈ S, ¬ p ∣ m := by
    rw [Finset.prod_eq_one_iff_of_one_le' (fun p hp => (hS p (Finset.mem_filter.1 hp).1).one_lt.le)]
    constructor
    · intro h p hp hpm
      exact (hS p hp).one_lt.ne' (h p (Finset.mem_filter.2 ⟨hp, hpm⟩))
    · intro h p hp
      exact absurd (Finset.mem_filter.1 hp).2 (h p (Finset.mem_filter.1 hp).1)
  by_cases hc : ∀ p ∈ S, ¬ p ∣ m
  · rw [if_pos (hiff.2 hc), if_pos hc, one_mul]
  · rw [if_neg (mt hiff.1 hc), if_neg hc, zero_mul]

/-- The coprime atom weights `√m · 1_{(m,P)=1}`. -/
def coprimeSqrtWeight (S : Finset ℕ) (m : ℕ) : ℝ :=
  if ∀ p ∈ S, ¬ p ∣ m then (m : ℝ) ^ (1 / 2 : ℝ) else 0

/-- **(4b) Finite totient reconstruction.**  `T_φ R_S(u) = Σ_{(m,P)=1} √m h(u + log m)`. -/
theorem logShiftSeries_totient_movingCuspSource {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (u : ℝ) :
    logShiftSeries totientAtomWeight (movingCuspSource S thetaCuspFullSource) u =
      logShiftSeries (coprimeSqrtWeight S) thetaSeedAtom u := by
  rw [movingCuspSource_eq_finiteSignedTotientAtoms hS,
    gaussianLogTail_thetaSeedAtom.logShiftSeries_logShiftSeries polyBoundedWeight_totientAtomWeight
      (polyBoundedWeight_finiteSignedTotientAtom S) (by simp [totientAtomWeight, invSqrtWeight_zero])
      (by simp [invSqrtWeight_zero])]
  congr 1
  funext m
  rw [show totientAtomWeight = fun n => eulerTotientAF n * invSqrtWeight n from rfl,
    show (fun m => finiteSignedTotient S m * invSqrtWeight m) =
      fun m => finiteSignedTotientAF S m * invSqrtWeight m from rfl, dirichletWeight_atomWeights]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [coprimeSqrtWeight, invSqrtWeight_zero]
  rw [eulerTotientAF_mul_finiteSignedTotientAF hS hm.ne', coprimeSqrtWeight]
  split_ifs
  · rw [invSqrtWeight, ← Real.rpow_one_add' (Nat.cast_nonneg _) (by norm_num)]
    · norm_num
  · simp

theorem polyBoundedWeight_coprimeSqrtWeight (S : Finset ℕ) : PolyBoundedWeight 1 (coprimeSqrtWeight S) := by
  intro m
  rw [coprimeSqrtWeight]
  split_ifs
  · rw [abs_of_nonneg (by positivity), pow_one]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · exact Real.rpow_le_self_of_one_le (by exact_mod_cast hm) (by norm_num)
  · simp

theorem PrimeExhaustion.tendsto_coprimeSqrtWeight {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S)
    (m : ℕ) : Tendsto (fun N => coprimeSqrtWeight (S N) m) atTop
      (𝓝 (if m = 1 then 1 else 0)) := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · simp [coprimeSqrtWeight]
    · refine tendsto_const_nhds.congr fun N => ?_
      rw [coprimeSqrtWeight, if_pos fun p hp hpd => (hS.prime N p hp).one_lt.ne'
        (Nat.dvd_one.1 hpd)]
      simp
  · rw [if_neg (by omega)]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hS.eventually_not_coprime hm] with N hN
    rw [coprimeSqrtWeight, if_neg hN]

/-- **(4b) limit.**  `T_φ R_{S_N} → h` uniformly on compact windows along every prime exhaustion. -/
theorem PrimeExhaustion.tendstoUniformlyOn_totient_movingCuspSource {S : ℕ → Finset ℕ}
    (hS : PrimeExhaustion S) (lo hi : ℝ) :
    TendstoUniformlyOn (fun N => logShiftSeries totientAtomWeight (movingCuspSource (S N) thetaCuspFullSource))
      thetaSeedAtom atTop (Icc lo hi) := by
  have hfun : (fun N => logShiftSeries totientAtomWeight (movingCuspSource (S N) thetaCuspFullSource)) =
      fun N => logShiftSeries (coprimeSqrtWeight (S N)) thetaSeedAtom := by
    funext N u
    exact logShiftSeries_totient_movingCuspSource (hS.prime N) u
  have hlim : logShiftSeries (fun m => if m = 1 then (1 : ℝ) else 0) thetaSeedAtom = thetaSeedAtom := by
    funext u
    rw [logShiftSeries, tsum_eq_single 1]
    · simp
    · intro n hn; simp [hn]
  rw [hfun]
  have h := gaussianLogTail_thetaSeedAtom.tendstoUniformlyOn_logShiftSeries
    (fun N => polyBoundedWeight_coprimeSqrtWeight _)
    (fun m => by split_ifs <;> simp [*]) hS.tendsto_coprimeSqrtWeight lo hi
  rwa [hlim] at h

end

end RHTower
