import GaloisForLFunctions.RHTower.ZetaSquareMobiusDetilting
import GaloisForLFunctions.RHTower.WeilZetaSquareMobiusRigidity

/-!
# Uniqueness of Weil-positive completions in the absolutely convergent finite-type class

Let `lam = Λ ⋆ a + μ ⋆ f + v` with `a, f, v` absolutely convergent past `½`
(`Σ (|a(n)| + |f(n)| + |v(n)|) n^{-1/2+δ} < ∞`), `f(1) = v(0) = v(1) = 0`. If `lam` is full-cone
Weil-positive, then `a = δ₁`, `f = 0` and `v = 0` (`eq_delta_and_eq_zero_of_weilPositiveFull_abs`).
Within this class a Weil-positive system exists iff RH (`exists_weilPositive_abs_iff`).

After `a = δ₁` (`eq_delta_of_weilPositiveFull`), the `|ζ|²`-weighted boundary inequality reads
`Re V(1/2+it) |ζ|² + Re(F conj ζ) ≤ 0` on the line, with `V` the Dirichlet series of `v`. We average
against `ω_L |M_P|² |1 + c a^{-it}|²`, where `P` is the set of primes `≤ K` and `c = v(a)`.

* The `V`-term is of order `L log L`. By de-tilting (`exists_abs_momentP_sub_le`), its leading
  coefficient is `Σ_n v(n) n^{-1/2} ((1+c²) T_P(n,1) + c (T_P(na,1) + T_P(n,a)))`.
* The `F`-term is `O(L √log L)`.

Evaluating `T_P` (`gval_self`, `gval_eq_zero`, `abs_gval_le`) gives
`v(a)² a^{-1/2} ≤ C Σ_{n > K} |v(n)|/n`. Hence `v = 0` by induction on `a`, then `f = 0` by the
sign rigidity against `ζ`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
open RHTower.WeilSpectral RHTower.WeilHerglotz RHTower.WeilFiniteType RHTower.WeilInfiniteDilation

namespace RHTower.WeilZetaSquare

open RHTower.ZetaNotch

/-! ## Evaluation at the primes up to `K` -/

/-- The primes `≤ K`. -/
def primesUpTo (K : ℕ) : Finset ℕ := (Finset.range (K + 1)).filter Nat.Prime

theorem mem_primesUpTo {K p : ℕ} : p ∈ primesUpTo K ↔ p ≤ K ∧ p.Prime := by
  simp [primesUpTo]

theorem primesUpTo_prime {K : ℕ} : ∀ p ∈ primesUpTo K, p.Prime := fun _ hp =>
  (mem_primesUpTo.mp hp).2

/-- An integer `2 ≤ n ≤ K` has a prime factor in `primesUpTo K` where it differs from `1`. -/
theorem exists_mem_factorization_ne_one {K n : ℕ} (hn2 : 2 ≤ n) (hnK : n ≤ K) {m : ℕ} (hm : m ≠ 0)
    (hnm : n ∣ m) : ∃ p ∈ primesUpTo K, m.factorization p ≠ (1 : ℕ).factorization p := by
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
  refine ⟨p, mem_primesUpTo.mpr ⟨(Nat.le_of_dvd (by omega) hpn).trans hnK, hp⟩, ?_⟩
  rw [Nat.factorization_one, Finsupp.zero_apply]
  exact (hp.factorization_pos_of_dvd hm (hpn.trans hnm)).ne'

theorem closedT_eq_zero_of_dvd {K n m : ℕ} (hn2 : 2 ≤ n) (hnK : n ≤ K) (hm : m ≠ 0) (hnm : n ∣ m) :
    closedT (primesUpTo K) m 1 = 0 := by
  classical
  obtain ⟨p, hp, hne⟩ := exists_mem_factorization_ne_one hn2 hnK hm hnm
  rw [closedT, if_neg (fun h => hne (h p hp)), mul_zero]

/-- Integers `≤ K` agreeing at all primes `≤ K` are equal. -/
theorem eq_of_factorization_primesUpTo {K n a : ℕ} (hn : n ≠ 0) (ha : a ≠ 0) (hnK : n ≤ K) (haK : a ≤ K)
    (h : ∀ p ∈ primesUpTo K, n.factorization p = a.factorization p) : n = a := by
  refine Nat.eq_of_factorization_eq hn ha fun p => ?_
  by_cases hp : p.Prime
  · by_cases hpK : p ≤ K
    · exact h p (mem_primesUpTo.mpr ⟨hpK, hp⟩)
    · push Not at hpK
      rw [Nat.factorization_eq_zero_of_not_dvd (fun hd => by
          have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd; omega),
        Nat.factorization_eq_zero_of_not_dvd (fun hd => by
          have := Nat.le_of_dvd (Nat.pos_of_ne_zero ha) hd; omega)]
  · rw [Nat.factorization_eq_zero_of_not_prime n hp, Nat.factorization_eq_zero_of_not_prime a hp]

/-- `(1+c²) T_P(n,1) + c (T_P(na,1) + T_P(n,a))`. -/
def gval (P : Finset ℕ) (c : ℝ) (a n : ℕ) : ℝ :=
  (1 + c ^ 2) * closedT P n 1 + c * (closedT P (n * a) 1 + closedT P n a)

/-- At `n = a` the de-tilted coefficient is `c Π_{p ≤ K}(1 − 1/p)`. -/
theorem gval_self {K a : ℕ} (ha2 : 2 ≤ a) (haK : a ≤ K) (c : ℝ) :
    gval (primesUpTo K) c a a = c * kpMass (primesUpTo K) := by
  classical
  have ha0 : a ≠ 0 := by omega
  unfold gval
  rw [closedT_eq_zero_of_dvd ha2 haK ha0 dvd_rfl,
    closedT_eq_zero_of_dvd ha2 haK (mul_ne_zero ha0 ha0) (dvd_mul_left a a), closedT,
    if_pos (fun _ _ => rfl), kpCorr_self ha0]
  ring

/-- For `2 ≤ n ≤ K`, `n ≠ a`, the de-tilted coefficient vanishes. -/
theorem gval_eq_zero {K a n : ℕ} (ha2 : 2 ≤ a) (haK : a ≤ K) (hn2 : 2 ≤ n) (hnK : n ≤ K) (hna : n ≠ a)
    (c : ℝ) : gval (primesUpTo K) c a n = 0 := by
  classical
  have ha0 : a ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  unfold gval
  rw [closedT_eq_zero_of_dvd hn2 hnK hn0 dvd_rfl,
    closedT_eq_zero_of_dvd ha2 haK (mul_ne_zero hn0 ha0) (dvd_mul_left a n), closedT,
    if_neg (fun h => hna (eq_of_factorization_primesUpTo hn0 ha0 hnK haK h))]
  ring

theorem abs_closedT_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (u w : ℕ) :
    |closedT P u w| ≤ kpMass P * kpCorr u w := by
  classical
  have hm := (kpMass_pos hP).le
  unfold closedT
  split_ifs
  · rw [abs_of_nonneg (mul_nonneg hm (kpCorr_nonneg u w))]
  · simp only [mul_zero, abs_zero]; exact mul_nonneg hm (kpCorr_nonneg u w)

/-- `|gval(n)| ≤ Π(1 − 1/p) (1 + c² + |c|(1 + √a)) n^{-1/2}`. -/
theorem abs_gval_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {a n : ℕ} (ha : a ≠ 0) (hn : n ≠ 0)
    (c : ℝ) :
    |gval P c a n| ≤ kpMass P * (1 + c ^ 2 + |c| * (1 + Real.sqrt a)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hm := (kpMass_pos hP).le
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnpow : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hn0.le _
  have h1 : |closedT P n 1| ≤ kpMass P * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
    (abs_closedT_le P hP n 1).trans (by rw [kpCorr_one_right])
  have h2 : |closedT P (n * a) 1| ≤ kpMass P * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    refine (abs_closedT_le P hP (n * a) 1).trans ?_
    rw [kpCorr_one_right]
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hn0 ?_ (by norm_num)) hm
    have : (1 : ℝ) ≤ a := by exact_mod_cast Nat.pos_of_ne_zero ha
    push_cast; nlinarith
  have h3 : |closedT P n a| ≤ kpMass P * (Real.sqrt a * (n : ℝ) ^ (-(1 / 2 : ℝ))) :=
    (abs_closedT_le P hP n a).trans (mul_le_mul_of_nonneg_left (kpCorr_le hn ha) hm)
  unfold gval
  calc |(1 + c ^ 2) * closedT P n 1 + c * (closedT P (n * a) 1 + closedT P n a)|
      ≤ (1 + c ^ 2) * |closedT P n 1| + |c| * (|closedT P (n * a) 1| + |closedT P n a|) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_pos (by positivity)]
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
    _ ≤ (1 + c ^ 2) * (kpMass P * (n : ℝ) ^ (-(1 / 2 : ℝ))) + |c| * (kpMass P * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
          kpMass P * (Real.sqrt a * (n : ℝ) ^ (-(1 / 2 : ℝ)))) := by gcongr
    _ = kpMass P * (1 + c ^ 2 + |c| * (1 + Real.sqrt a)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by ring

/-! ## The averaging weight -/

/-- `|1 + c a^{-it}|² = 1 + c² + 2c cos(t log a)`. -/
def rotWeight (c : ℝ) (a : ℕ) (t : ℝ) : ℝ := 1 + c ^ 2 + 2 * c * Real.cos (Real.log a * t)

theorem rotWeight_nonneg (c : ℝ) (a : ℕ) (t : ℝ) : 0 ≤ rotWeight c a t := by
  unfold rotWeight
  nlinarith [sq_nonneg (c + Real.cos (Real.log a * t)), sq_nonneg (Real.sin (Real.log a * t)),
    Real.sin_sq_add_cos_sq (Real.log a * t)]

theorem rotWeight_le (c : ℝ) (a : ℕ) (t : ℝ) : rotWeight c a t ≤ (1 + |c|) ^ 2 := by
  unfold rotWeight
  have h1 := Real.cos_le_one (Real.log a * t)
  have h2 := Real.neg_one_le_cos (Real.log a * t)
  have h3 : 2 * c * Real.cos (Real.log a * t) ≤ 2 * |c| := by
    have : |2 * c * Real.cos (Real.log a * t)| ≤ 2 * |c| := by
      rw [abs_mul, abs_mul, abs_two]
      have := Real.abs_cos_le_one (Real.log a * t)
      nlinarith [abs_nonneg c]
    exact (le_abs_self _).trans this
  nlinarith [sq_abs c, abs_nonneg c]

theorem continuous_rotWeight (c : ℝ) (a : ℕ) : Continuous (rotWeight c a) := by
  unfold rotWeight; fun_prop

/-- `|1 + c a^{-it}|² cos(t log n)` splits into three frequencies. -/
theorem rotWeight_mul_cos (c : ℝ) {a n : ℕ} (ha : a ≠ 0) (hn : n ≠ 0) (t : ℝ) :
    rotWeight c a t * Real.cos (Real.log n * t) =
      (1 + c ^ 2) * Real.cos ((Real.log n - Real.log (1 : ℕ)) * t) +
        c * (Real.cos ((Real.log (n * a : ℕ) - Real.log (1 : ℕ)) * t) +
          Real.cos ((Real.log n - Real.log a) * t)) := by
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  push_cast
  rw [Real.log_one, sub_zero, sub_zero, Real.log_mul hn0 ha0,
    show (Real.log n + Real.log a) * t = Real.log n * t + Real.log a * t by ring,
    show (Real.log n - Real.log a) * t = Real.log n * t - Real.log a * t by ring,
    Real.cos_add, Real.cos_sub]
  unfold rotWeight
  ring

/-- `(1+c²) M_P(n,1) + c (M_P(na,1) + M_P(n,a))`. -/
def mval (P : Finset ℕ) (L c : ℝ) (a n : ℕ) : ℝ :=
  (1 + c ^ 2) * momentP P L n 1 + c * (momentP P L (n * a) 1 + momentP P L n a)

theorem integral_weighted_cos_eq (P : Finset ℕ) {L : ℝ} (hL : 0 < L) (c : ℝ) {a n : ℕ} (ha : a ≠ 0)
    (hn : n ≠ 0) :
    ∫ t, win L t * zsq t * mollWeight P t * rotWeight c a t * Real.cos (Real.log n * t) =
      mval P L c a n := by
  have hpt : ∀ t, win L t * zsq t * mollWeight P t * rotWeight c a t * Real.cos (Real.log n * t) =
      (1 + c ^ 2) * (win L t * zsq t * mollWeight P t * Real.cos ((Real.log n - Real.log (1 : ℕ)) * t)) +
        c * (win L t * zsq t * mollWeight P t * Real.cos ((Real.log (n * a : ℕ) - Real.log (1 : ℕ)) * t) +
          win L t * zsq t * mollWeight P t * Real.cos ((Real.log n - Real.log a) * t)) := by
    intro t
    calc _ = win L t * zsq t * mollWeight P t * (rotWeight c a t * Real.cos (Real.log n * t)) := by ring
      _ = _ := by rw [rotWeight_mul_cos c ha hn t]; ring
  simp_rw [hpt]
  have i1 := integrable_momentP_integrand P hL (Real.log n - Real.log (1 : ℕ))
  have i2 := integrable_momentP_integrand P hL (Real.log (n * a : ℕ) - Real.log (1 : ℕ))
  have i3 := integrable_momentP_integrand P hL (Real.log n - Real.log a)
  have i23 : Integrable fun t =>
      win L t * zsq t * mollWeight P t * Real.cos ((Real.log (n * a : ℕ) - Real.log (1 : ℕ)) * t) +
        win L t * zsq t * mollWeight P t * Real.cos ((Real.log n - Real.log a) * t) := i2.add i3
  rw [integral_add (i1.const_mul _) (i23.const_mul _), integral_const_mul, integral_const_mul,
    integral_add i2 i3]
  rfl

theorem abs_momentP_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {L : ℝ} (hL : 0 < L) (u w : ℕ) :
    |momentP P L u w| ≤ 4 ^ P.card * momentRe L 0 := by
  rw [momentRe_zero_eq, ← integral_const_mul]
  have hint : Integrable fun t => 4 ^ P.card * (win L t * zsq t) :=
    ((integrable_win_mul hL continuous_zsq).const_mul _)
  have h := norm_integral_le_of_norm_le (μ := volume)
    (f := fun t => win L t * zsq t * mollWeight P t * Real.cos ((Real.log u - Real.log w) * t)) hint
    (Eventually.of_forall fun t => by
      have hw0 := blockWindow_nonneg L (2 * L) (L / 2) t
      have hz := zsq_nonneg t
      have hm0 := mollWeight_nonneg hP t
      have hm1 := mollWeight_le hP t
      have hc := Real.abs_cos_le_one ((Real.log u - Real.log w) * t)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hw0, abs_of_nonneg hz,
        abs_of_nonneg hm0]
      have hwz : 0 ≤ win L t * zsq t := mul_nonneg hw0 hz
      calc win L t * zsq t * mollWeight P t * |Real.cos ((Real.log u - Real.log w) * t)|
          ≤ win L t * zsq t * 4 ^ P.card * 1 := by gcongr
        _ = 4 ^ P.card * (win L t * zsq t) := by ring)
  rw [Real.norm_eq_abs] at h
  exact h

theorem abs_mval_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {L : ℝ} (hL : 0 < L) (c : ℝ) (a n : ℕ) :
    |mval P L c a n| ≤ (1 + c ^ 2 + 2 * |c|) * (4 ^ P.card * momentRe L 0) := by
  have h1 := abs_momentP_le P hP hL n 1
  have h2 := abs_momentP_le P hP hL (n * a) 1
  have h3 := abs_momentP_le P hP hL n a
  unfold mval
  calc |(1 + c ^ 2) * momentP P L n 1 + c * (momentP P L (n * a) 1 + momentP P L n a)|
      ≤ (1 + c ^ 2) * |momentP P L n 1| + |c| * (|momentP P L (n * a) 1| + |momentP P L n a|) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_pos (by positivity)]
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
    _ ≤ (1 + c ^ 2) * (4 ^ P.card * momentRe L 0) +
          |c| * (4 ^ P.card * momentRe L 0 + 4 ^ P.card * momentRe L 0) := by gcongr
    _ = (1 + c ^ 2 + 2 * |c|) * (4 ^ P.card * momentRe L 0) := by ring

/-! ## The averaged inequality -/

theorem integral_win_le {L : ℝ} (hL : 0 < L) : ∫ t, win L t ≤ 2 * L := by
  have h := integral_win_mul_eq hL (fun _ => (1 : ℝ))
  simp only [mul_one] at h
  rw [h]
  have := intervalIntegral.integral_mono_on (μ := volume) (a := L / 2) (b := 5 * L / 2)
    (f := win L) (g := fun _ => (1 : ℝ)) (by linarith)
    ((contDiff_blockWindow L (2 * L) (L / 2)).continuous.intervalIntegrable _ _)
    intervalIntegrable_const (fun t _ => blockWindow_le_one L (2 * L) (L / 2) t)
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at this
  linarith

/-- `∫ ω_L |ζ| ≤ (1 + C₀) L √(log L)`. -/
theorem integral_win_norm_zeta_le {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hmom0 : ∀ {L : ℝ}, 16 ≤ L → momentRe L 0 ≤ C₀ * L * Real.log L) {L : ℝ} (hL : 16 ≤ L) :
    ∫ t, win L t * ‖riemannZeta (linePt t)‖ ≤ (1 + C₀) * (L * Real.sqrt (Real.log L)) := by
  have hL0 : 0 < L := by linarith
  have hlog : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hL0]
    have := Real.exp_one_lt_d9
    linarith
  set lam := Real.sqrt (Real.log L) with hlam
  have hlampos : 0 < lam := Real.sqrt_pos.mpr (by linarith)
  have hlamsq : lam ^ 2 = Real.log L := Real.sq_sqrt (by linarith)
  have hpt : ∀ t, win L t * ‖riemannZeta (linePt t)‖ ≤ lam / 2 * win L t + 1 / (2 * lam) * (win L t * zsq t) := by
    intro t
    have hw0 := blockWindow_nonneg L (2 * L) (L / 2) t
    have hz : zsq t = ‖riemannZeta (linePt t)‖ ^ 2 := by unfold zsq; rw [Complex.normSq_eq_norm_sq]
    set x := ‖riemannZeta (linePt t)‖
    have hx : x ≤ lam / 2 + 1 / (2 * lam) * zsq t := by
      rw [hz, show lam / 2 + 1 / (2 * lam) * x ^ 2 = (lam ^ 2 + x ^ 2) / (2 * lam) by field_simp,
        le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (x - lam)]
    calc win L t * x ≤ win L t * (lam / 2 + 1 / (2 * lam) * zsq t) := mul_le_mul_of_nonneg_left hx hw0
      _ = lam / 2 * win L t + 1 / (2 * lam) * (win L t * zsq t) := by ring
  have i1 : Integrable fun t => win L t * ‖riemannZeta (linePt t)‖ :=
    integrable_win_mul hL0 continuous_zeta_line.norm
  have i2 : Integrable (win L) := by
    have := integrable_win_mul hL0 (g := fun _ => (1 : ℝ)) continuous_const
    simpa using this
  have i3 : Integrable fun t => win L t * zsq t := integrable_win_mul hL0 continuous_zsq
  have hmono : ∫ t, win L t * ‖riemannZeta (linePt t)‖ ≤
      ∫ t, (lam / 2 * win L t + 1 / (2 * lam) * (win L t * zsq t)) :=
    integral_mono i1 ((i2.const_mul _).add (i3.const_mul _)) hpt
  rw [integral_add (i2.const_mul _) (i3.const_mul _), integral_const_mul, integral_const_mul,
    ← momentRe_zero_eq] at hmono
  have h2 := integral_win_le hL0
  have h3 := hmom0 hL
  calc ∫ t, win L t * ‖riemannZeta (linePt t)‖
      ≤ lam / 2 * (∫ t, win L t) + 1 / (2 * lam) * momentRe L 0 := hmono
    _ ≤ lam / 2 * (2 * L) + 1 / (2 * lam) * (C₀ * L * Real.log L) := by gcongr
    _ = L * lam + C₀ / 2 * (L * lam) := by
        rw [← hlamsq]; field_simp
    _ ≤ (1 + C₀) * (L * lam) := by nlinarith [mul_pos hL0 hlampos]

/-! ## The critical-line series under `Σ |f(n)|/√n < ∞` -/

theorem abs_div_sqrt_eq (f : ℕ → ℝ) (n : ℕ) :
    |f n| / Real.sqrt n = |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.rpow_neg hn0.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]

theorem dilSeries_line_eq_tsum (f : ℕ → ℝ) (t : ℝ) :
    dilSeries f (linePt t) = ∑' n, critDirPoly {n} f t := by
  rw [show linePt t = (1 / 2 : ℂ) + t * I by simp [linePt]]
  exact ZetaUniformMoment.LSeries_line_eq_tsum f t

theorem norm_dilSeries_line_le_of_summable {f : ℕ → ℝ}
    (hfs : Summable fun n => |f n| / Real.sqrt n) (t : ℝ) :
    ‖dilSeries f (linePt t)‖ ≤ ∑' n, |f n| / Real.sqrt n := by
  have hb : ∀ n, ‖critDirPoly {n} f t‖ ≤ |f n| / Real.sqrt n := fun n => by
    rw [ZetaUniformMoment.norm_critDirPoly_singleton, abs_div_sqrt_eq]
  rw [dilSeries_line_eq_tsum]
  exact (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb hfs)).trans
    (Summable.tsum_le_tsum hb (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb hfs) hfs)

theorem continuous_dilSeries_line_of_summable {f : ℕ → ℝ}
    (hfs : Summable fun n => |f n| / Real.sqrt n) :
    Continuous fun t : ℝ => dilSeries f (linePt t) := by
  have hs : Summable fun n : ℕ => |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
    hfs.congr fun n => abs_div_sqrt_eq f n
  have := ZetaUniformMoment.continuous_LSeries_line hs
  refine this.congr fun t => ?_
  rw [show linePt t = (1 / 2 : ℂ) + t * I by simp [linePt]]

theorem re_dilSeries_line_of_summable {v : ℕ → ℝ} (hvs : Summable fun n => |v n| / Real.sqrt n)
    (t : ℝ) :
    (dilSeries v (linePt t)).re = ∑' n, v n / Real.sqrt n * Real.cos (Real.log n * t) := by
  have hsum : Summable fun n => critDirPoly {n} v t :=
    Summable.of_norm_bounded hvs fun n => by
      rw [ZetaUniformMoment.norm_critDirPoly_singleton, abs_div_sqrt_eq]
  rw [dilSeries_line_eq_tsum, Complex.re_tsum hsum]
  refine tsum_congr fun n => ?_
  rw [ZetaUniformMoment.critDirPoly_singleton,
    show -((Real.log n : ℝ) : ℂ) * t * I = ((-(Real.log n) * t : ℝ) : ℂ) * I by push_cast; ring,
    ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re,
    show -Real.log n * t = -(Real.log n * t) by ring, Real.cos_neg]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.rpow_neg hn0.le, ← Real.sqrt_eq_rpow]
    ring

/-- **The averaged inequality at leading order.** If `Re V |ζ|² + Re(F conj ζ) ≤ 0` on the line
(`t ≥ 8`), with `V, F` absolutely convergent past `½`, then for every finite set `P` of primes,
`c ∈ ℝ` and `a ≥ 1`: `Σ_n v(n) n^{-1/2} gval_P(c, a, n) ≤ 0`. -/
theorem tsum_gval_nonpos {v f : ℕ → ℝ} (hs : Summable fun n => |v n| / Real.sqrt n)
    (hfs : Summable fun n => |f n| / Real.sqrt n)
    (h : ∀ t : ℝ, 8 ≤ t → (dilSeries v (linePt t)).re * zsq t +
      (dilSeries f (linePt t) * conj (riemannZeta (linePt t))).re ≤ 0)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (c : ℝ) {a : ℕ} (ha : a ≠ 0) :
    ∑' n, v n / Real.sqrt n * gval P c a n ≤ 0 := by
  obtain ⟨C₀, hC₀, hmom0⟩ := exists_momentRe_zero_le
  obtain ⟨CP, hCP, hmainP⟩ := exists_abs_momentP_sub_le P hP
  set SF := ∑' n, |f n| / Real.sqrt n with hSFdef
  have hSF : ∀ t, ‖dilSeries f (linePt t)‖ ≤ SF := norm_dilSeries_line_le_of_summable hfs
  have hSF0 : 0 ≤ SF := (norm_nonneg _).trans (hSF 0)
  set B : ℝ := 4 ^ P.card * (1 + |c|) ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast Nat.pos_of_ne_zero ha
  have hcontV : Continuous fun t : ℝ => (dilSeries v (linePt t)).re :=
    Complex.continuous_re.comp (continuous_dilSeries_line_of_summable hs)
  have hcontF : Continuous fun t : ℝ =>
      (dilSeries f (linePt t) * conj (riemannZeta (linePt t))).re :=
    Complex.continuous_re.comp ((continuous_dilSeries_line_of_summable hfs).mul
      (Complex.continuous_conj.comp continuous_zeta_line))
  have hwt : ∀ t, 0 ≤ mollWeight P t * rotWeight c a t :=
    fun t => mul_nonneg (mollWeight_nonneg hP t) (rotWeight_nonneg c a t)
  have hwtB : ∀ t, mollWeight P t * rotWeight c a t ≤ B := fun t =>
    mul_le_mul (mollWeight_le hP t) (rotWeight_le c a t) (rotWeight_nonneg c a t) (by positivity)
  -- the two integrals
  set Ifun : ℝ → ℝ := fun L => ∫ t, win L t *
    (zsq t * mollWeight P t * rotWeight c a t * (dilSeries v (linePt t)).re) with hIdef
  set Jfun : ℝ → ℝ := fun L => ∫ t, win L t *
    (mollWeight P t * rotWeight c a t * (dilSeries f (linePt t) * conj (riemannZeta (linePt t))).re)
    with hJdef
  have hIJ : ∀ L : ℝ, 16 ≤ L → Ifun L + Jfun L ≤ 0 := by
    intro L hL
    have hL0 : 0 < L := by linarith
    have i1 : Integrable fun t => win L t *
        (zsq t * mollWeight P t * rotWeight c a t * (dilSeries v (linePt t)).re) :=
      integrable_win_mul hL0 (((continuous_zsq.mul (continuous_mollWeight P)).mul
        (continuous_rotWeight c a)).mul hcontV)
    have i2 : Integrable fun t => win L t * (mollWeight P t * rotWeight c a t *
        (dilSeries f (linePt t) * conj (riemannZeta (linePt t))).re) :=
      integrable_win_mul hL0 (((continuous_mollWeight P).mul (continuous_rotWeight c a)).mul hcontF)
    simp only [hIdef, hJdef]
    rw [← integral_add i1 i2]
    refine integral_nonpos fun t => ?_
    by_cases ht : t ∈ Icc (L / 2) (5 * L / 2)
    · have h8 : 8 ≤ t := by linarith [ht.1]
      have hw0 := blockWindow_nonneg L (2 * L) (L / 2) t
      have key := h t h8
      have e : win L t * (zsq t * mollWeight P t * rotWeight c a t * (dilSeries v (linePt t)).re) +
          win L t * (mollWeight P t * rotWeight c a t *
            (dilSeries f (linePt t) * conj (riemannZeta (linePt t))).re) =
          (win L t * (mollWeight P t * rotWeight c a t)) *
            ((dilSeries v (linePt t)).re * zsq t +
              (dilSeries f (linePt t) * conj (riemannZeta (linePt t))).re) := by ring
      rw [Pi.zero_apply, e]
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hw0 (hwt t)) key
    · rw [Pi.zero_apply, win_eq_zero hL0 ht]; simp
  have hI : ∀ L : ℝ, 16 ≤ L → Ifun L = ∑' n, v n / Real.sqrt n * mval P L c a n := by
    intro L hL
    have hL0 : 0 < L := by linarith
    set Fn : ℕ → ℝ → ℝ := fun n t => win L t * (zsq t * mollWeight P t * rotWeight c a t *
      (v n / Real.sqrt n * Real.cos (Real.log n * t))) with hFn
    have hpt : ∀ t, win L t * (zsq t * mollWeight P t * rotWeight c a t * (dilSeries v (linePt t)).re) =
        ∑' n, Fn n t := by
      intro t
      rw [re_dilSeries_line_of_summable hs t, tsum_mul_left, tsum_mul_left]
    have hFint : ∀ n, Integrable (Fn n) := fun n => integrable_win_mul hL0
      (((continuous_zsq.mul (continuous_mollWeight P)).mul (continuous_rotWeight c a)).mul
        (continuous_const.mul (by fun_prop)))
    have hFnorm : ∀ n, ∫ t, ‖Fn n t‖ ≤ |v n| / Real.sqrt n * (B * momentRe L 0) := by
      intro n
      rw [momentRe_zero_eq, ← integral_const_mul, ← integral_const_mul]
      refine integral_mono (hFint n).norm
        (((integrable_win_mul hL0 continuous_zsq).const_mul _).const_mul _) fun t => ?_
      have hw0 := blockWindow_nonneg L (2 * L) (L / 2) t
      have hz := zsq_nonneg t
      have hc := Real.abs_cos_le_one (Real.log n * t)
      have e : Fn n t = (win L t * zsq t) * (mollWeight P t * rotWeight c a t) * (v n / Real.sqrt n) *
          Real.cos (Real.log n * t) := by simp only [hFn]; ring
      rw [Real.norm_eq_abs, e, abs_mul, abs_mul, abs_mul, abs_of_nonneg (mul_nonneg hw0 hz),
        abs_of_nonneg (hwt t), abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
      have hvn : 0 ≤ |v n| / Real.sqrt n := by positivity
      calc win L t * zsq t * (mollWeight P t * rotWeight c a t) * (|v n| / Real.sqrt n) *
            |Real.cos (Real.log n * t)|
          ≤ win L t * zsq t * B * (|v n| / Real.sqrt n) * 1 := by
            gcongr
            · exact hwtB t
        _ = |v n| / Real.sqrt n * (B * (win L t * zsq t)) := by ring
    have hsum : Summable fun n => ∫ t, ‖Fn n t‖ :=
      Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _) hFnorm
        (hs.mul_right _)
    simp only [hIdef]
    rw [show (fun t => win L t * (zsq t * mollWeight P t * rotWeight c a t * (dilSeries v (linePt t)).re)) =
      fun t => ∑' n, Fn n t from funext hpt, ← integral_tsum_of_summable_integral_norm hFint hsum]
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hFn]
    · rw [← integral_weighted_cos_eq P hL0 c ha hn.ne', ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [hFn]
      ring
  have hJ : ∀ L : ℝ, 16 ≤ L → |Jfun L| ≤ B * SF * ((1 + C₀) * (L * Real.sqrt (Real.log L))) := by
    intro L hL
    have hL0 : 0 < L := by linarith
    have hint : Integrable fun t => B * SF * (win L t * ‖riemannZeta (linePt t)‖) :=
      (integrable_win_mul hL0 continuous_zeta_line.norm).const_mul _
    have h1 := norm_integral_le_of_norm_le (μ := volume)
      (f := fun t => win L t * (mollWeight P t * rotWeight c a t *
        (dilSeries f (linePt t) * conj (riemannZeta (linePt t))).re)) hint
      (Eventually.of_forall fun t => by
        have hw0 := blockWindow_nonneg L (2 * L) (L / 2) t
        have hre : |(dilSeries f (linePt t) * conj (riemannZeta (linePt t))).re| ≤
            SF * ‖riemannZeta (linePt t)‖ := by
          refine (Complex.abs_re_le_norm _).trans ?_
          rw [norm_mul, Complex.norm_conj]
          exact mul_le_mul_of_nonneg_right (hSF t) (norm_nonneg _)
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw0, abs_of_nonneg (hwt t)]
        calc win L t * (mollWeight P t * rotWeight c a t *
              |(dilSeries f (linePt t) * conj (riemannZeta (linePt t))).re|)
            ≤ win L t * (B * (SF * ‖riemannZeta (linePt t)‖)) := by
              gcongr
              · exact hwtB t
          _ = B * SF * (win L t * ‖riemannZeta (linePt t)‖) := by ring)
    rw [Real.norm_eq_abs, integral_const_mul] at h1
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_left (integral_win_norm_zeta_le hC₀ hmom0 hL) (by positivity)
  -- limits
  set W : ℝ → ℝ := fun L => (logWindow L).re with hWdef
  have hWge : ∀ L : ℝ, 16 ≤ L → L * Real.log L ≤ W L := fun L hL =>
    WeilFiniteSupport.re_logWindow_ge (by linarith)
  have hWpos : ∀ L : ℝ, 16 ≤ L → 0 < W L := fun L hL => lt_of_lt_of_le
    (mul_pos (by linarith) (Real.log_pos (by linarith))) (hWge L hL)
  have hlogtop : Tendsto (fun L : ℝ => Real.log L) atTop atTop := Real.tendsto_log_atTop
  have hsqrttop : Tendsto (fun L : ℝ => Real.sqrt (Real.log L)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hlogtop
  -- J / W → 0
  have hJlim : Tendsto (fun L => Jfun L / W L) atTop (𝓝 0) := by
    have hbound : Tendsto (fun L : ℝ => B * SF * (1 + C₀) / Real.sqrt (Real.log L)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hsqrttop
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun L => norm_nonneg _) ?_ hbound
    filter_upwards [eventually_ge_atTop (16 : ℝ)] with L hL
    have hL0 : 0 < L := by linarith
    have hlog1 : 0 < Real.log L := Real.log_pos (by linarith)
    have hsq : 0 < Real.sqrt (Real.log L) := Real.sqrt_pos.mpr hlog1
    have hsq2 : Real.sqrt (Real.log L) * Real.sqrt (Real.log L) = Real.log L :=
      Real.mul_self_sqrt hlog1.le
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hWpos L hL), div_le_div_iff₀ (hWpos L hL) hsq]
    calc |Jfun L| * Real.sqrt (Real.log L)
        ≤ B * SF * ((1 + C₀) * (L * Real.sqrt (Real.log L))) * Real.sqrt (Real.log L) := by
          gcongr; exact hJ L hL
      _ = B * SF * (1 + C₀) * (L * (Real.sqrt (Real.log L) * Real.sqrt (Real.log L))) := by ring
      _ = B * SF * (1 + C₀) * (L * Real.log L) := by rw [hsq2]
      _ ≤ B * SF * (1 + C₀) * W L := by gcongr; exact hWge L hL
  -- I / W → Γ
  set Γ := ∑' n, v n / Real.sqrt n * gval P c a n with hΓ
  have hIlim : Tendsto (fun L => Ifun L / W L) atTop (𝓝 Γ) := by
    set K₁ := (1 + c ^ 2 + 2 * |c|) * (4 ^ P.card * C₀) with hK₁
    have hdom : Summable fun n => |v n| / Real.sqrt n * K₁ := hs.mul_right _
    have hrw : ∀ᶠ L : ℝ in atTop, Ifun L / W L = ∑' n, v n / Real.sqrt n * (mval P L c a n / W L) := by
      filter_upwards [eventually_ge_atTop (16 : ℝ)] with L hL
      rw [hI L hL, ← tsum_div_const]
      refine tsum_congr fun n => ?_
      ring
    refine Tendsto.congr' (EventuallyEq.symm hrw) ?_
    refine tendsto_tsum_of_dominated_convergence hdom (fun n => ?_) ?_
    · -- pointwise
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      refine Tendsto.const_mul _ ?_
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      set Kn := CP * ((1 + c ^ 2) * n + |c| * (n * a + n * a)) with hKn
      have hbound : Tendsto (fun L : ℝ => Kn / Real.log L) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hlogtop
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun L => norm_nonneg _) ?_ hbound
      filter_upwards [eventually_ge_atTop (16 : ℝ)] with L hL
      have hL0 : 0 < L := by linarith
      have hlog1 : 0 < Real.log L := Real.log_pos (by linarith)
      have hW0 := hWpos L hL
      have e1 := hmainP hL hn one_pos
      have e2 := hmainP hL (Nat.mul_pos hn (Nat.pos_of_ne_zero ha)) one_pos
      have e3 := hmainP hL hn (Nat.pos_of_ne_zero ha)
      push_cast at e1 e2 e3
      have hdiff : |mval P L c a n - gval P c a n * W L| ≤ Kn * L := by
        have : mval P L c a n - gval P c a n * W L =
            (1 + c ^ 2) * (momentP P L n 1 - closedT P n 1 * W L) +
              c * ((momentP P L (n * a) 1 - closedT P (n * a) 1 * W L) +
                (momentP P L n a - closedT P n a * W L)) := by
          unfold mval gval; ring
        rw [this]
        calc |(1 + c ^ 2) * (momentP P L n 1 - closedT P n 1 * W L) +
              c * ((momentP P L (n * a) 1 - closedT P (n * a) 1 * W L) +
                (momentP P L n a - closedT P n a * W L))|
            ≤ (1 + c ^ 2) * |momentP P L n 1 - closedT P n 1 * W L| +
                |c| * (|momentP P L (n * a) 1 - closedT P (n * a) 1 * W L| +
                  |momentP P L n a - closedT P n a * W L|) := by
              refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
              · rw [abs_mul, abs_of_pos (by positivity)]
              · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
          _ ≤ (1 + c ^ 2) * (CP * ((n : ℝ) * 1) * L) +
                |c| * (CP * ((n : ℝ) * a * 1) * L + CP * ((n : ℝ) * a) * L) := by
              gcongr
          _ = Kn * L := by rw [hKn]; ring
      rw [Real.norm_eq_abs, show mval P L c a n / W L - gval P c a n =
        (mval P L c a n - gval P c a n * W L) / W L by field_simp, abs_div, abs_of_pos hW0,
        div_le_div_iff₀ hW0 hlog1]
      calc |mval P L c a n - gval P c a n * W L| * Real.log L ≤ Kn * L * Real.log L := by gcongr
        _ = Kn * (L * Real.log L) := by ring
        _ ≤ Kn * W L := by
            have hKn0 : 0 ≤ Kn := by positivity
            gcongr; exact hWge L hL
    · -- domination
      filter_upwards [eventually_ge_atTop (16 : ℝ)] with L hL n
      have hL0 : 0 < L := by linarith
      have hW0 := hWpos L hL
      have hm := abs_mval_le P hP hL0 c a n
      have hmom := hmom0 hL
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg (Real.sqrt_nonneg _), abs_div,
        abs_of_pos hW0]
      have hvn : 0 ≤ |v n| / Real.sqrt n := by positivity
      refine mul_le_mul_of_nonneg_left ?_ hvn
      rw [div_le_iff₀ hW0]
      calc |mval P L c a n| ≤ (1 + c ^ 2 + 2 * |c|) * (4 ^ P.card * momentRe L 0) := hm
        _ ≤ (1 + c ^ 2 + 2 * |c|) * (4 ^ P.card * (C₀ * L * Real.log L)) := by gcongr
        _ = K₁ * (L * Real.log L) := by rw [hK₁]; ring
        _ ≤ K₁ * W L := by
            have : 0 ≤ K₁ := by positivity
            gcongr; exact hWge L hL
  -- conclude
  have hsumlim : Tendsto (fun L => Ifun L / W L + Jfun L / W L) atTop (𝓝 (Γ + 0)) :=
    hIlim.add hJlim
  rw [add_zero] at hsumlim
  refine le_of_tendsto hsumlim ?_
  filter_upwards [eventually_ge_atTop (16 : ℝ)] with L hL
  rw [← add_div]
  exact div_nonpos_of_nonpos_of_nonneg (hIJ L hL) (hWpos L hL).le

/-! ## Rigidity of the regular part -/

theorem summable_abs_div_nat {v : ℕ → ℝ} (hs : Summable fun n => |v n| / Real.sqrt n) :
    Summable fun n : ℕ => |v n| / n := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hsn : Real.sqrt n ≤ n := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ n by linarith), Real.sqrt_nonneg (n : ℝ)]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (Real.sqrt_pos.mpr (by linarith)) hsn

theorem div_sqrt_mul_rpow {n : ℕ} (hn : n ≠ 0) (x : ℝ) :
    x / Real.sqrt n * (n : ℝ) ^ (-(1 / 2 : ℝ)) = x / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hs : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  have hs0 : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  rw [Real.rpow_neg hn0.le, ← Real.sqrt_eq_rpow]
  calc x / Real.sqrt n * (Real.sqrt n)⁻¹ = x / (Real.sqrt n * Real.sqrt n) := by field_simp
    _ = x / n := by rw [hs]

/-- **Regular-part rigidity.** If `Re V(1/2+it) |ζ|² + Re(F conj ζ) ≤ 0` for all `t ≥ 8`, where `V` and
`F` are the Dirichlet series of `v, f` with `Σ |v(n)|/√n < ∞`, `Σ |f(n)|/√n < ∞` and `v(1) = 0`, then
`v(n) = 0` for every `n ≥ 1`. -/
theorem eq_zero_of_re_regular_le_of_summable {v f : ℕ → ℝ} (hs : Summable fun n => |v n| / Real.sqrt n)
    (hv1 : v 1 = 0) (hfs : Summable fun n => |f n| / Real.sqrt n)
    (h : ∀ t : ℝ, 8 ≤ t → (dilSeries v (linePt t)).re * zsq t +
      (dilSeries f (linePt t) * conj (riemannZeta (linePt t))).re ≤ 0) :
    ∀ n, 1 ≤ n → v n = 0 := by
  have hsn := summable_abs_div_nat hs
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro ha
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  · have : a = 1 := by omega
    subst this; exact hv1
  have ha0 : a ≠ 0 := by omega
  set c := v a with hc
  set C₀ := 1 + c ^ 2 + |c| * (1 + Real.sqrt a) with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  have hsqa : 0 < Real.sqrt a := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero ha0)
  have hbound : ∀ K : ℕ, a ≤ K → c * c / Real.sqrt a ≤ C₀ * ZetaUniformMoment.tailSum v K := by
    intro K hK
    set P := primesUpTo K
    have hP : ∀ p ∈ P, p.Prime := primesUpTo_prime
    have hm := kpMass_pos hP
    have hΓ := tsum_gval_nonpos hs hfs h P hP c ha0
    set v₀ : ℝ := c / Real.sqrt a * (c * kpMass P) with hv₀
    set e : ℕ → ℝ := fun n => v n / Real.sqrt n * gval P c a n - if n = a then v₀ else 0 with he
    set b : ℕ → ℝ := fun n => kpMass P * C₀ * (if K < n then |v n| / n else 0) with hb
    have hbsum : Summable b := by
      refine Summable.mul_left _ ?_
      refine Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => ?_) hsn
      split_ifs
      · exact le_rfl
      · positivity
    have heb : ∀ n, |e n| ≤ b n := by
      intro n
      simp only [he, hb]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [if_neg (by omega)]; simp
      rcases lt_trichotomy n a with hna | rfl | hna
      · rw [if_neg (by omega), ih n hna hn]
        simp only [zero_div, zero_mul, sub_zero, abs_zero]
        split_ifs <;> positivity
      · rw [if_pos rfl, gval_self ha2 hK c, hv₀, ← hc, sub_self, abs_zero]
        split_ifs <;> positivity
      · rw [if_neg (by omega), sub_zero]
        by_cases hnK : n ≤ K
        · rw [gval_eq_zero ha2 hK (by omega) hnK (by omega) c, mul_zero, abs_zero]
          split_ifs <;> positivity
        · push Not at hnK
          rw [if_pos hnK, abs_mul, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
          have hg := abs_gval_le P hP ha0 (by omega) c (n := n)
          have hvn : 0 ≤ |v n| / Real.sqrt n := by positivity
          calc |v n| / Real.sqrt n * |gval P c a n|
              ≤ |v n| / Real.sqrt n * (kpMass P * C₀ * (n : ℝ) ^ (-(1 / 2 : ℝ))) :=
                mul_le_mul_of_nonneg_left hg hvn
            _ = kpMass P * C₀ * (|v n| / Real.sqrt n * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by ring
            _ = kpMass P * C₀ * (|v n| / n) := by rw [div_sqrt_mul_rpow (by omega)]
    have hesum : Summable e := Summable.of_norm_bounded hbsum (fun n => by
      rw [Real.norm_eq_abs]; exact heb n)
    have hite : Summable fun n : ℕ => if n = a then v₀ else 0 :=
      summable_of_ne_finset_zero (s := {a}) fun n hn => by rw [if_neg (by simpa using hn)]
    have hvt : (∑' n : ℕ, if n = a then v₀ else 0) = v₀ := by
      rw [tsum_eq_single a]
      · simp
      · intro n hn; simp [hn]
    have hsplit : (∑' n, v n / Real.sqrt n * gval P c a n) = (∑' n, e n) + v₀ := by
      rw [← hvt, ← Summable.tsum_add hesum hite]
      refine tsum_congr fun n => ?_
      simp only [he]
      ring
    have hetail : |∑' n, e n| ≤ kpMass P * C₀ * ZetaUniformMoment.tailSum v K := by
      calc |∑' n, e n| ≤ ∑' n, |e n| := by
            rw [← Real.norm_eq_abs]
            refine (norm_tsum_le_tsum_norm hesum.norm).trans (le_of_eq ?_)
            simp [Real.norm_eq_abs]
        _ ≤ ∑' n, b n := Summable.tsum_le_tsum heb hesum.abs hbsum
        _ = kpMass P * C₀ * ZetaUniformMoment.tailSum v K := by
            rw [tsum_mul_left]; rfl
    have hv₀le : v₀ ≤ kpMass P * C₀ * ZetaUniformMoment.tailSum v K := by
      have := neg_abs_le (∑' n, e n)
      linarith
    have : c * c / Real.sqrt a * kpMass P ≤ C₀ * ZetaUniformMoment.tailSum v K * kpMass P := by
      calc c * c / Real.sqrt a * kpMass P = v₀ := by rw [hv₀]; ring
        _ ≤ kpMass P * C₀ * ZetaUniformMoment.tailSum v K := hv₀le
        _ = C₀ * ZetaUniformMoment.tailSum v K * kpMass P := by ring
    exact le_of_mul_le_mul_right this hm
  have htail := ZetaUniformMoment.tendsto_tailSum hsn
  have hlim : Tendsto (fun K => C₀ * ZetaUniformMoment.tailSum v K) atTop (𝓝 0) := by
    simpa using htail.const_mul C₀
  have h0 : c * c / Real.sqrt a ≤ 0 := ge_of_tendsto hlim ((eventually_ge_atTop a).mono hbound)
  have hcc : c * c ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have := div_pos hcon hsqa
    linarith
  exact mul_self_eq_zero.mp (le_antisymm hcc (mul_self_nonneg c))

/-- **Regular-part rigidity**, absolutely convergent case. -/
theorem eq_zero_of_re_regular_le {v f : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hv : LSeriesSummable (fun n => (v n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hv1 : v 1 = 0)
    (hf : LSeriesSummable (fun n => (f n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ))
    (h : ∀ t : ℝ, 8 ≤ t → (dilSeries v (linePt t)).re * zsq t +
      (dilSeries f (linePt t) * conj (riemannZeta (linePt t))).re ≤ 0) :
    ∀ n, 1 ≤ n → v n = 0 :=
  eq_zero_of_re_regular_le_of_summable (summable_a_div hδ hv) hv1 (summable_a_div hδ hf) h

/-! ## Uniqueness in the absolutely convergent finite-type class -/

theorem regularPart_of_lSeriesSummable {v : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hv : LSeriesSummable (fun n => (v n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hv0 : v 0 = 0) (hv1 : v 1 = 0) :
    RegularPart v (dilSeries v) where
  zero := hv0
  one := hv1
  summable := fun s hs => summable_of_le_re hv (by simp; linarith)
  series := fun _ _ => rfl
  holo := ⟨δ, hδ, differentiableOn_dilSeries hv⟩
  growth := fun _ => ⟨∑' n, ‖LSeries.term (fun n => (v n : ℂ)) (1 / 2) n‖, 0, fun s hs _ => by
    rw [pow_zero, mul_one]; exact norm_dilSeries_le hv hδ hs⟩

/-- **Uniqueness in the absolutely convergent finite-type class.** If `Λ ⋆ a + μ ⋆ f + v` is
full-cone Weil-positive, with `a, f, v` absolutely convergent past `½`, `f(1) = 0` and
`v(0) = v(1) = 0`, then `a = δ₁`, `f = 0` and `v = 0`. -/
theorem eq_delta_and_eq_zero_of_weilPositiveFull_abs {a f v : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ))
    (hf : LSeriesSummable (fun n => (f n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hf1 : f 1 = 0)
    (hv : LSeriesSummable (fun n => (v n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hv0 : v 0 = 0) (hv1 : v 1 = 0)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) :
    a 1 = 1 ∧ (∀ n, 2 ≤ n → a n = 0) ∧ (∀ n, 1 ≤ n → f n = 0) ∧ ∀ n, v n = 0 := by
  have hreg := regularPart_of_lSeriesSummable hδ hv hv0 hv1
  obtain ⟨h1, h2⟩ := eq_delta_of_weilPositiveFull hδ ha hf hf1 hreg hW (norm_dilSeries_line_le hv hδ)
  have hvz : ∀ n, 1 ≤ n → v n = 0 := by
    refine eq_zero_of_re_regular_le hδ hv hv1 hf fun t _ => ?_
    have hb := re_boundary_ge hδ ha hf hf1 hreg hW t
    rw [dilSeries_eq_one h1 h2, sub_self, zero_mul, zero_mul, Complex.zero_re] at hb
    exact hb
  have hv' : ∀ n, v n = 0 := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact hv0
    · exact hvz n hn
  have hseq : finiteTypeSeq a f v = finiteTypeSeq a f (fun _ => 0) := by
    funext n; unfold finiteTypeSeq; rw [hv' n]
  rw [hseq] at hW
  obtain ⟨-, -, hf0⟩ := eq_delta_and_eq_zero_of_weilPositiveFull_mobius hδ ha hf hf1 hW
  exact ⟨h1, h2, hf0, hv'⟩

/-- **Within the absolutely convergent finite-type class, a Weil-positive system exists iff RH.** -/
theorem exists_weilPositive_abs_iff :
    (∃ (a f v : ℕ → ℝ) (δ : ℝ), 0 < δ ∧
      LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ) ∧
      LSeriesSummable (fun n => (f n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ) ∧ f 1 = 0 ∧
      LSeriesSummable (fun n => (v n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ) ∧ v 0 = 0 ∧ v 1 = 0 ∧
      WeilPositiveFull (finiteTypeSeq a f v)) ↔ RiemannHypothesis := by
  rw [← exists_weilPositive_mobius_iff]
  constructor
  · rintro ⟨a, f, v, δ, hδ, ha, hf, hf1, hv, hv0, hv1, hW⟩
    obtain ⟨-, -, -, hv'⟩ := eq_delta_and_eq_zero_of_weilPositiveFull_abs hδ ha hf hf1 hv hv0 hv1 hW
    have hseq : finiteTypeSeq a f v = finiteTypeSeq a f (fun _ => 0) := by
      funext n; unfold finiteTypeSeq; rw [hv' n]
    exact ⟨a, f, δ, hδ, ha, hf, hf1, hseq ▸ hW⟩
  · rintro ⟨a, f, δ, hδ, ha, hf, hf1, hW⟩
    refine ⟨a, f, fun _ => 0, δ, hδ, ha, hf, hf1, ?_, rfl, rfl, hW⟩
    refine summable_of_ne_finset_zero (s := ∅) fun n _ => ?_
    simp [LSeries.term]

end RHTower.WeilZetaSquare
