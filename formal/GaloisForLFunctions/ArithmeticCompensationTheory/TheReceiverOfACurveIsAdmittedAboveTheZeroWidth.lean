import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The receiver of a curve is admitted above the zero width

Over `F_q[T]` the damped centred source is constant and admission is free
(`ArithmeticContinuationAndCriticalEnergy.fqUniformlyAdmitsOn`). A curve model with Frobenius
eigenvalues `αᵢ` is the first calibration where the source is not degenerate. Its degree
generating functions are

`Z(u) = P(u)/((1 − u)(1 − qu))`,  `P(u) = Πᵢ (1 − αᵢu)`,

`Z` counting effective divisors by degree and `1/Z` giving the degree sums of the Möbius function
(`curveZ_mul_curveZinv`). The damped source at degree horizon `n` is the prefix of
`Z(u)·(1/Z)(q^{−ε}u)`, centred by the density `δ_ε = Σ_k μ_ε(k) q^{−k}` times the divisor count
(`curveCentredPrefix`), and the receiver energy weights degree `n` by `q^{−n}`, the norm weight of
the `≍ qⁿ` divisors of that degree (`curveReceiverEnergy`).

* `exists_curveReceiverEnergy_le`: if every eigenvalue has modulus at most `λ√q` and
  `λ < q^ε`, the receiver energy is bounded uniformly in the horizon: **the curve receiver is
  admitted at every damping above the zero width `log_q λ`**;
* `exists_curveReceiverEnergy_le_of_weil`: on the Weil circle, `λ = 1`, at every `ε > 0`.

The mechanism is the one the number-field programme names. The centring removes the pole of `Z` at
`u = 1/q` exactly: `(1 − qu)^{−1}(R − δ)` has coefficients `−qⁿ Σ_{j>n} b_j q^{−j}`
(`coeff_geomSeries_mul_eq_neg_tail`), which leaves the growth `(λ√q q^{−ε})ⁿ` of the zeros, and
the norm weight `q^{−n}` turns it into `(λ q^{−ε})^{2n}`. Admission is the zero width, with a
nonzero budget: unlike `F_q[T]`, the centred source of a curve moves. Weil's bound is the defining
property of the model class; nothing is claimed about point counts of actual curves.
-/

open PowerSeries Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

variable {m : ℕ}

/-! ## The curve model -/

/-- The geometric series `1/(1 − cu) = Σ cⁿuⁿ`. -/
def geomSeries (c : ℂ) : PowerSeries ℂ := mk fun n => c ^ n

/-- `P(u) = Πᵢ (1 − αᵢ u)`. -/
def curveP (α : Fin m → ℂ) : PowerSeries ℂ := ∏ i, (1 - C (α i) * X)

/-- `1/P(u) = Πᵢ 1/(1 − αᵢ u)`. -/
def curvePinv (α : Fin m → ℂ) : PowerSeries ℂ := ∏ i, geomSeries (α i)

/-- The divisor generating function `Z(u) = P(u)/((1 − u)(1 − qu))`. -/
def curveZ (q : ℕ) (α : Fin m → ℂ) : PowerSeries ℂ := curveP α * geomSeries 1 * geomSeries q

/-- The Möbius generating function `1/Z(u) = (1 − u)(1 − qu)/P(u)`. -/
def curveZinv (q : ℕ) (α : Fin m → ℂ) : PowerSeries ℂ :=
  (1 - C 1 * X) * (1 - C (q : ℂ) * X) * curvePinv α

/-- The damped Möbius generating function `(1/Z)(q^{−ε}u)`. -/
def curveDampedZinv (q : ℕ) (α : Fin m → ℂ) (ε : ℝ) : PowerSeries ℂ :=
  rescale (((q : ℝ) ^ (-ε) : ℝ) : ℂ) (curveZinv q α)

/-- The density `δ_ε = Σ_k μ_ε(k) q^{−k}`, the value `1/ζ_C(1 + ε)`. -/
def curveDensity (q : ℕ) (α : Fin m → ℂ) (ε : ℝ) : ℂ :=
  ∑' k, coeff k (curveDampedZinv q α ε) / (q : ℂ) ^ k

/-- The centred damped source at degree horizon `n`: the prefix of `Z(u)(1/Z)(q^{−ε}u)` minus the
density times the number of effective divisors of degree at most `n`. -/
def curveCentredPrefix (q : ℕ) (α : Fin m → ℂ) (ε : ℝ) (n : ℕ) : ℂ :=
  coeff n (geomSeries 1 * (curveZ q α * curveDampedZinv q α ε)) -
    curveDensity q α ε * coeff n (geomSeries 1 * curveZ q α)

/-- The receiver energy of the curve model, degree `n` weighted by `q^{−n}`. -/
def curveReceiverEnergy (q : ℕ) (α : Fin m → ℂ) (ε : ℝ) (D : ℕ) : ℝ :=
  ∑ n ∈ range (D + 1), ‖curveCentredPrefix q α ε n‖ ^ 2 / (q : ℝ) ^ n

theorem one_sub_mul_geomSeries (c : ℂ) : (1 - C c * X) * geomSeries c = 1 := by
  have he : (1 - C c * X) * geomSeries c = geomSeries c - C c * (X * geomSeries c) := by ring
  ext n
  rw [he, map_sub, coeff_C_mul, coeff_one]
  rcases n with _ | n
  · simp [geomSeries]
  · rw [coeff_succ_X_mul]
    simp [geomSeries, pow_succ]
    ring

/-- **Möbius inversion of the model.** `Z(u) · (1/Z)(u) = 1`. -/
theorem curveZ_mul_curveZinv (q : ℕ) (α : Fin m → ℂ) : curveZ q α * curveZinv q α = 1 := by
  have hP : curveP α * curvePinv α = 1 := by
    rw [curveP, curvePinv, ← prod_mul_distrib]
    exact prod_eq_one fun i _ => one_sub_mul_geomSeries (α i)
  have h1 := one_sub_mul_geomSeries 1
  have hq := one_sub_mul_geomSeries (q : ℂ)
  calc curveZ q α * curveZinv q α
      = (curveP α * curvePinv α) * ((1 - C 1 * X) * geomSeries 1) *
          ((1 - C (q : ℂ) * X) * geomSeries q) := by
        rw [curveZ, curveZinv]; ring
    _ = 1 := by rw [hP, h1, hq]; ring

/-! ## Coefficient bounds -/

/-- A product of series with `‖coeff_n‖ ≤ tⁿ` has `‖coeff_n‖ ≤ (n + 1)^{#s} tⁿ`. -/
theorem norm_coeff_prod_le {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℂ) {t : ℝ}
    (ht : 0 ≤ t) (hf : ∀ i ∈ s, ∀ n, ‖coeff n (f i)‖ ≤ t ^ n) (n : ℕ) :
    ‖coeff n (∏ i ∈ s, f i)‖ ≤ ((n : ℝ) + 1) ^ s.card * t ^ n := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty =>
      rw [prod_empty, coeff_one, card_empty, pow_zero, one_mul]
      split_ifs with h
      · subst h; simp
      · simp only [norm_zero]; positivity
  | insert a s ha ih =>
      have hfa := hf a (mem_insert_self a s)
      have hfs : ∀ i ∈ s, ∀ n, ‖coeff n (f i)‖ ≤ t ^ n := fun i hi => hf i (mem_insert_of_mem hi)
      rw [prod_insert ha, coeff_mul, card_insert_of_notMem ha]
      calc ‖∑ p ∈ antidiagonal n, coeff p.1 (f a) * coeff p.2 (∏ i ∈ s, f i)‖
          ≤ ∑ p ∈ antidiagonal n, t ^ p.1 * (((p.2 : ℝ) + 1) ^ s.card * t ^ p.2) := by
            refine (norm_sum_le _ _).trans (sum_le_sum fun p _ => ?_)
            rw [norm_mul]
            exact mul_le_mul (hfa p.1) (ih hfs p.2) (norm_nonneg _) (pow_nonneg ht _)
        _ ≤ ∑ _p ∈ antidiagonal n, ((n : ℝ) + 1) ^ s.card * t ^ n := by
            refine sum_le_sum fun p hp => ?_
            have hpn := mem_antidiagonal.mp hp
            have h2 : ((p.2 : ℝ) + 1) ≤ (n : ℝ) + 1 := by
              have : p.2 ≤ n := by omega
              exact_mod_cast Nat.add_le_add_right this 1
            calc t ^ p.1 * (((p.2 : ℝ) + 1) ^ s.card * t ^ p.2)
                = ((p.2 : ℝ) + 1) ^ s.card * t ^ (p.1 + p.2) := by rw [pow_add]; ring
              _ ≤ ((n : ℝ) + 1) ^ s.card * t ^ n := by
                  rw [hpn]
                  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h2 _)
                    (pow_nonneg ht _)
        _ = ((n : ℝ) + 1) ^ (s.card + 1) * t ^ n := by
            rw [sum_const, Nat.card_antidiagonal, nsmul_eq_mul, pow_succ]
            push_cast; ring

/-- `P(u)` is a polynomial of degree at most `m`. -/
theorem coeff_curveP_eq_zero (α : Fin m → ℂ) {n : ℕ} (hn : m < n) : coeff n (curveP α) = 0 := by
  classical
  have key : ∀ (s : Finset (Fin m)) (n : ℕ), s.card < n →
      coeff n (∏ i ∈ s, (1 - C (α i) * X)) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro n hn
        rw [prod_empty, coeff_one, if_neg (by simp at hn; omega)]
    | insert a s ha ih =>
        intro n hn
        rw [card_insert_of_notMem ha] at hn
        rw [prod_insert ha, coeff_mul]
        refine sum_eq_zero fun p hp => ?_
        have hpn := mem_antidiagonal.mp hp
        by_cases h1 : p.1 ≤ 1
        · rw [ih p.2 (by omega), mul_zero]
        · have : coeff p.1 (1 - C (α a) * X) = 0 := by
            rw [map_sub, coeff_one, coeff_C_mul, coeff_X, if_neg (by omega), if_neg (by omega)]
            simp
          rw [this, zero_mul]
  simpa [curveP] using key univ n (by simpa using hn)

/-- The coefficients of `P(u)` are at most `(n + 1)^m tⁿ` when every `|αᵢ| ≤ t`, `t ≥ 1`. -/
theorem norm_coeff_curveP_le (α : Fin m → ℂ) {t : ℝ} (ht : 1 ≤ t) (hα : ∀ i, ‖α i‖ ≤ t) (n : ℕ) :
    ‖coeff n (curveP α)‖ ≤ ((n : ℝ) + 1) ^ m * t ^ n := by
  have h := norm_coeff_prod_le univ (fun i => 1 - C (α i) * X) (by linarith) (t := t)
    (fun i _ k => by
      rw [map_sub, coeff_one, coeff_C_mul, coeff_X]
      rcases k with _ | _ | k
      · simp
      · simpa using hα i
      · simp only [if_neg (by omega : k + 2 ≠ 0), if_neg (by omega : k + 2 ≠ 1)]
        simp only [mul_zero, sub_zero, norm_zero]; positivity) n
  simpa [curveP] using h

/-- The coefficients of `1/P(u)` are at most `(n + 1)^m tⁿ` when every `|αᵢ| ≤ t`. -/
theorem norm_coeff_curvePinv_le (α : Fin m → ℂ) {t : ℝ} (ht : 0 ≤ t) (hα : ∀ i, ‖α i‖ ≤ t)
    (n : ℕ) : ‖coeff n (curvePinv α)‖ ≤ ((n : ℝ) + 1) ^ m * t ^ n := by
  have h := norm_coeff_prod_le univ (fun i => geomSeries (α i)) ht
    (fun i _ k => by
      rw [geomSeries, coeff_mk, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hα i) k) n
  simpa [curvePinv] using h

/-- Multiplying by `1 − cu` costs the factor `1 + c` in a bound `K (k + 1)^m tᵏ`, `t ≥ 1`. -/
theorem norm_coeff_one_sub_mul_le {F : PowerSeries ℂ} {K t c : ℝ} (hK : 0 ≤ K) (ht : 1 ≤ t)
    (hc : 0 ≤ c) (hF : ∀ k, ‖coeff k F‖ ≤ K * ((k : ℝ) + 1) ^ m * t ^ k) (k : ℕ) :
    ‖coeff k ((1 - C (c : ℂ) * X) * F)‖ ≤ (1 + c) * K * ((k : ℝ) + 1) ^ m * t ^ k := by
  have he : (1 - C (c : ℂ) * X) * F = F - C (c : ℂ) * (X * F) := by ring
  rw [he, map_sub, coeff_C_mul]
  rcases k with _ | k
  · rw [coeff_zero_X_mul, mul_zero, sub_zero]
    have := hF 0
    nlinarith [mul_nonneg hc (mul_nonneg hK (by positivity : (0 : ℝ) ≤ ((0 : ℕ) + 1 : ℝ) ^ m))]
  · rw [coeff_succ_X_mul]
    have h1 := hF (k + 1)
    have h2 := hF k
    have hk : ((k : ℝ) + 1) ^ m ≤ (((k + 1 : ℕ) : ℝ) + 1) ^ m :=
      pow_le_pow_left₀ (by positivity) (by push_cast; linarith) m
    have htk : t ^ k ≤ t ^ (k + 1) := pow_le_pow_right₀ ht (by omega)
    calc ‖coeff (k + 1) F - (c : ℂ) * coeff k F‖ ≤ ‖coeff (k + 1) F‖ + c * ‖coeff k F‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
      _ ≤ K * (((k + 1 : ℕ) : ℝ) + 1) ^ m * t ^ (k + 1) +
            c * (K * (((k + 1 : ℕ) : ℝ) + 1) ^ m * t ^ (k + 1)) := by
          refine add_le_add h1 (mul_le_mul_of_nonneg_left (h2.trans ?_) hc)
          exact mul_le_mul (mul_le_mul_of_nonneg_left hk hK) htk (by positivity) (by positivity)
      _ = (1 + c) * K * (((k + 1 : ℕ) : ℝ) + 1) ^ m * t ^ (k + 1) := by ring

/-- `Σ_n (n + j)^k rⁿ` converges for `0 < r < 1`. -/
theorem summable_add_pow_mul_geometric (k j : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable fun n : ℕ => ((n : ℝ) + j) ^ k * r ^ n := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one k (r := r)
    (by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1)
  have h2 := ((summable_nat_add_iff j).mpr hs).mul_left (r ^ j)⁻¹
  refine h2.congr fun n => ?_
  push_cast
  rw [pow_add]
  field_simp

/-! ## The polar cancellation -/

/-- **The centring removes the pole at `u = 1/q`.** If `Σ_j b_j q^{−j} = 0`, the coefficients of
`(1 − qu)^{−1} B(u)` are `−qⁿ Σ_{j>n} b_j q^{−j}`. -/
theorem coeff_geomSeries_mul_eq_neg_tail {q : ℕ} (hq : 1 ≤ q) {B : PowerSeries ℂ}
    (hs : Summable fun j => coeff j B / (q : ℂ) ^ j) (h0 : ∑' j, coeff j B / (q : ℂ) ^ j = 0)
    (n : ℕ) :
    coeff n (geomSeries q * B) =
      -((q : ℂ) ^ n * ∑' i, coeff (i + (n + 1)) B / (q : ℂ) ^ (i + (n + 1))) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hsplit := hs.sum_add_tsum_nat_add (n + 1)
  rw [h0] at hsplit
  have hhead : coeff n (geomSeries q * B) =
      (q : ℂ) ^ n * ∑ j ∈ range (n + 1), coeff j B / (q : ℂ) ^ j := by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum,
      ← sum_range_reflect]
    refine sum_congr rfl fun j hj => ?_
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    simp only [geomSeries, coeff_mk]
    rw [show n - (n + 1 - 1 - j) = j by omega, show n + 1 - 1 - j = n - j by omega]
    rw [show (q : ℂ) ^ n = (q : ℂ) ^ (n - j) * (q : ℂ) ^ j by
      rw [← pow_add, Nat.sub_add_cancel hjn]]
    field_simp
  rw [hhead, eq_neg_iff_add_eq_zero, ← mul_add, hsplit, mul_zero]

/-! ## Admission above the zero width -/

/-- **The curve receiver is admitted above the zero width.** If every Frobenius eigenvalue has
modulus at most `λ√q`, `λ ≥ 1`, then at every damping with `λ < q^ε` the receiver energy is bounded
uniformly in the degree horizon. -/
theorem exists_curveReceiverEnergy_le {q : ℕ} (hq : 2 ≤ q) {α : Fin m → ℂ} {lam : ℝ}
    (hlam : 1 ≤ lam) (hα : ∀ i, ‖α i‖ ≤ lam * Real.sqrt q) {ε : ℝ}
    (hlamε : lam < (q : ℝ) ^ ε) :
    ∃ B : ℝ, ∀ D, curveReceiverEnergy q α ε D ≤ B := by
  -- the scales: `t = λ√q`, the damped zero growth `ρ = t q^{−ε}`, and the tail ratio `x = ρ/q`
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  set s := Real.sqrt q
  have hs1 : 1 ≤ s := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hss : s * s = q := Real.mul_self_sqrt hq0.le
  set t := lam * s
  have ht1 : 1 ≤ t := by nlinarith
  set ρ₀ := (q : ℝ) ^ (-ε)
  have hρ₀ : 0 < ρ₀ := Real.rpow_pos_of_pos hq0 _
  have hlamρ : lam * ρ₀ < 1 := by
    have : (q : ℝ) ^ (-ε) * (q : ℝ) ^ ε = 1 := by
      rw [← Real.rpow_add hq0, neg_add_cancel, Real.rpow_zero]
    simp only [ρ₀]
    nlinarith [Real.rpow_pos_of_pos hq0 (-ε)]
  set ρ := t * ρ₀
  have hρ0 : 0 < ρ := by positivity
  set x := ρ / q
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by
    rw [div_lt_one hq0]
    calc ρ = lam * ρ₀ * s := by simp only [ρ, t]; ring
      _ < 1 * s := mul_lt_mul_of_pos_right hlamρ (by positivity)
      _ ≤ s * s := by nlinarith
      _ = q := hss
  set M := max 1 ρ
  have hM1 : 1 ≤ M := le_max_left _ _
  set r := M ^ 2 / q
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by
    rw [div_lt_one hq0]
    rcases le_total ρ 1 with h | h
    · have hM : M = 1 := max_eq_left h
      rw [hM]; linarith
    · have hM : M = ρ := max_eq_right h
      rw [hM]
      calc ρ ^ 2 = (lam * ρ₀) ^ 2 * (s * s) := by simp only [ρ, t]; ring
        _ < 1 * (s * s) := by
            refine mul_lt_mul_of_pos_right ?_ (by positivity)
            nlinarith [mul_pos (by linarith : (0 : ℝ) < lam) hρ₀]
        _ = q := by rw [one_mul, hss]
  -- coefficient bounds for `1/P`, `1/Z` and its damping
  have hα' : ∀ i, ‖α i‖ ≤ t := hα
  have hPinv : ∀ k, ‖coeff k (curvePinv α)‖ ≤ 1 * ((k : ℝ) + 1) ^ m * t ^ k := fun k => by
    rw [one_mul]; exact norm_coeff_curvePinv_le α (by linarith) hα' k
  set KR : ℝ := (1 + (q : ℝ)) * ((1 + 1) * 1)
  have hKR : 0 ≤ KR := by positivity
  have hZinv : ∀ k, ‖coeff k (curveZinv q α)‖ ≤ KR * ((k : ℝ) + 1) ^ m * t ^ k := by
    intro k
    have h1 : ∀ k, ‖coeff k ((1 - C ((1 : ℝ) : ℂ) * X) * curvePinv α)‖ ≤
        (1 + 1) * 1 * ((k : ℝ) + 1) ^ m * t ^ k :=
      norm_coeff_one_sub_mul_le zero_le_one ht1 zero_le_one hPinv
    have h2 := norm_coeff_one_sub_mul_le (by positivity) ht1 (Nat.cast_nonneg q) h1 k
    have he : curveZinv q α = (1 - C (((q : ℕ) : ℝ) : ℂ) * X) *
        ((1 - C ((1 : ℝ) : ℂ) * X) * curvePinv α) := by
      rw [curveZinv]; push_cast; ring
    rw [he]
    simpa [KR, mul_assoc] using h2
  have hR : ∀ k, ‖coeff k (curveDampedZinv q α ε)‖ ≤ KR * ((k : ℝ) + 1) ^ m * ρ ^ k := by
    intro k
    rw [curveDampedZinv, coeff_rescale, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hρ₀.le]
    calc ρ₀ ^ k * ‖coeff k (curveZinv q α)‖ ≤ ρ₀ ^ k * (KR * ((k : ℝ) + 1) ^ m * t ^ k) :=
          mul_le_mul_of_nonneg_left (hZinv k) (by positivity)
      _ = KR * ((k : ℝ) + 1) ^ m * ρ ^ k := by simp only [ρ]; rw [mul_pow]; ring
  -- the density series and the polar cancellation
  set R := curveDampedZinv q α ε
  set δ := curveDensity q α ε
  have hqk : ∀ k : ℕ, ‖(q : ℂ) ^ k‖ = (q : ℝ) ^ k := fun k => by
    rw [norm_pow, Complex.norm_natCast]
  have hRsum : Summable fun k => coeff k R / (q : ℂ) ^ k := by
    refine Summable.of_norm_bounded ((summable_add_pow_mul_geometric m 1 hx0 hx1).mul_left KR)
      fun k => ?_
    rw [norm_div, hqk, div_le_iff₀ (by positivity)]
    calc ‖coeff k R‖ ≤ KR * ((k : ℝ) + 1) ^ m * ρ ^ k := hR k
      _ = KR * (((k : ℝ) + ((1 : ℕ) : ℝ)) ^ m * x ^ k) * (q : ℝ) ^ k := by
          simp only [x]; rw [div_pow]; field_simp; push_cast; ring
  set Bs := R - C δ
  have hBcoeff : ∀ j, 1 ≤ j → coeff j Bs = coeff j R := fun j hj => by
    simp only [Bs, map_sub, coeff_C, if_neg (show j ≠ 0 by omega), sub_zero]
  have hBsum : Summable fun j => coeff j Bs / (q : ℂ) ^ j := by
    have he : (fun j => coeff j Bs / (q : ℂ) ^ j) =
        fun j => coeff j R / (q : ℂ) ^ j - (if j = 0 then δ else 0) := by
      funext j
      simp only [Bs, map_sub, coeff_C]
      split_ifs with h
      · subst h; simp
      · simp
    rw [he]
    exact hRsum.sub (summable_of_ne_finset_zero (s := {0}) fun j hj => by
      simp only [mem_singleton] at hj; simp [hj])
  have hB0 : ∑' j, coeff j Bs / (q : ℂ) ^ j = 0 := by
    have he : (fun j => coeff j Bs / (q : ℂ) ^ j) =
        fun j => coeff j R / (q : ℂ) ^ j - (if j = 0 then δ else 0) := by
      funext j
      simp only [Bs, map_sub, coeff_C]
      split_ifs with h
      · subst h; simp
      · simp
    rw [he, Summable.tsum_sub hRsum (summable_of_ne_finset_zero (s := {0}) fun j hj => by
      simp only [mem_singleton] at hj; simp [hj]), tsum_ite_eq]
    simp [δ, curveDensity, R]
  set Sx := ∑' i : ℕ, ((i : ℝ) + ((1 : ℕ) : ℝ)) ^ m * x ^ i
  have hSx : 0 ≤ Sx := tsum_nonneg fun i => by positivity
  set K1 := KR * Sx * x
  have hK1 : 0 ≤ K1 := by positivity
  have hC : ∀ n, ‖coeff n (geomSeries q * Bs)‖ ≤ K1 * ((n : ℝ) + 2) ^ m * ρ ^ n := by
    intro n
    rw [coeff_geomSeries_mul_eq_neg_tail (by omega) hBsum hB0 n, norm_neg, norm_mul, hqk]
    have htail : ‖∑' i, coeff (i + (n + 1)) Bs / (q : ℂ) ^ (i + (n + 1))‖ ≤
        KR * ((n : ℝ) + 2) ^ m * x ^ (n + 1) * Sx := by
      have hbd : ∀ i, ‖coeff (i + (n + 1)) Bs / (q : ℂ) ^ (i + (n + 1))‖ ≤
          KR * ((n : ℝ) + 2) ^ m * x ^ (n + 1) * (((i : ℝ) + ((1 : ℕ) : ℝ)) ^ m * x ^ i) := by
        intro i
        rw [hBcoeff _ (by omega), norm_div, hqk, div_le_iff₀ (by positivity)]
        have hpow : (((i + (n + 1) : ℕ) : ℝ) + 1) ^ m ≤ ((n : ℝ) + 2) ^ m * ((i : ℝ) + 1) ^ m := by
          rw [← mul_pow]
          refine pow_le_pow_left₀ (by positivity) ?_ m
          push_cast
          nlinarith [Nat.cast_nonneg (α := ℝ) i, Nat.cast_nonneg (α := ℝ) n]
        calc ‖coeff (i + (n + 1)) R‖ ≤ KR * (((i + (n + 1) : ℕ) : ℝ) + 1) ^ m * ρ ^ (i + (n + 1)) :=
              hR _
          _ ≤ KR * (((n : ℝ) + 2) ^ m * ((i : ℝ) + 1) ^ m) * ρ ^ (i + (n + 1)) := by gcongr
          _ = KR * ((n : ℝ) + 2) ^ m * x ^ (n + 1) *
                (((i : ℝ) + ((1 : ℕ) : ℝ)) ^ m * x ^ i) * (q : ℝ) ^ (i + (n + 1)) := by
              simp only [x]; rw [div_pow, div_pow, pow_add (q : ℝ)]; field_simp; push_cast
              rw [pow_add]; ring
      have hsum := (summable_add_pow_mul_geometric m 1 hx0 hx1).mul_left
        (KR * ((n : ℝ) + 2) ^ m * x ^ (n + 1))
      have hnorm := Summable.of_nonneg_of_le (fun i => norm_nonneg _) hbd hsum
      refine (norm_tsum_le_tsum_norm hnorm).trans ?_
      rw [← tsum_mul_left]
      exact hnorm.tsum_le_tsum hbd hsum
    calc (q : ℝ) ^ n * ‖∑' i, coeff (i + (n + 1)) Bs / (q : ℂ) ^ (i + (n + 1))‖
        ≤ (q : ℝ) ^ n * (KR * ((n : ℝ) + 2) ^ m * x ^ (n + 1) * Sx) :=
          mul_le_mul_of_nonneg_left htail (by positivity)
      _ = K1 * ((n : ℝ) + 2) ^ m * ρ ^ n := by
          simp only [K1, x]; rw [div_pow, pow_succ]; field_simp; ring
  -- convolution with `P`, of degree at most `m`
  set c₀ := max 1 ρ⁻¹
  set K2 := ((m : ℝ) + 1) * (((m : ℝ) + 1) ^ m * t ^ m) * (K1 * c₀ ^ m)
  have hK2 : 0 ≤ K2 := by positivity
  have hPC : ∀ n, ‖coeff n (curveP α * (geomSeries q * Bs))‖ ≤ K2 * ((n : ℝ) + 2) ^ m * M ^ n := by
    intro n
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have hterm : ∀ k ∈ range (n + 1), ‖coeff k (curveP α) * coeff (n - k) (geomSeries q * Bs)‖ ≤
        if k ≤ m then ((m : ℝ) + 1) ^ m * t ^ m * (K1 * c₀ ^ m * ((n : ℝ) + 2) ^ m * M ^ n)
        else 0 := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
      split_ifs with hkm
      · rw [norm_mul]
        refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
        · refine (norm_coeff_curveP_le α ht1 hα' k).trans ?_
          have hkm' : (k : ℝ) + 1 ≤ (m : ℝ) + 1 := by
            have : (k : ℝ) ≤ m := by exact_mod_cast hkm
            linarith
          exact mul_le_mul (pow_le_pow_left₀ (by positivity) hkm' m) (pow_le_pow_right₀ ht1 hkm)
            (by positivity) (by positivity)
        · refine (hC (n - k)).trans ?_
          have h1 : (((n - k : ℕ) : ℝ) + 2) ^ m ≤ ((n : ℝ) + 2) ^ m :=
            pow_le_pow_left₀ (by positivity) (by
              have : ((n - k : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n k
              linarith) m
          have h2 : ρ ^ (n - k) ≤ c₀ ^ m * M ^ n := by
            rcases le_total ρ 1 with hρ1 | hρ1
            · -- `ρ^{n−k} ≤ ρ^{−k} ≤ ρ^{−m}`
              have hρk : ρ ^ (n - k) * ρ ^ k ≤ 1 := by
                rw [← pow_add, Nat.sub_add_cancel hkn]; exact pow_le_one₀ hρ0.le hρ1
              have hinv1 : 1 ≤ ρ⁻¹ := (one_le_inv₀ hρ0).mpr hρ1
              have hinv : ρ⁻¹ ^ k ≤ c₀ ^ m :=
                (pow_le_pow_right₀ hinv1 hkm).trans
                  (pow_le_pow_left₀ (by positivity) (le_max_right _ _) m)
              have hM : M ^ n = 1 := by
                have : M = 1 := max_eq_left hρ1
                rw [this, one_pow]
              rw [hM, mul_one]
              calc ρ ^ (n - k) = ρ ^ (n - k) * ρ ^ k * ρ⁻¹ ^ k := by
                    rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hρ0.ne', one_pow, mul_one]
                _ ≤ 1 * c₀ ^ m := mul_le_mul hρk hinv (by positivity) zero_le_one
                _ = c₀ ^ m := one_mul _
            · have hM : M = ρ := max_eq_right hρ1
              rw [hM]
              have hc : 1 ≤ c₀ ^ m := one_le_pow₀ (le_max_left _ _)
              calc ρ ^ (n - k) ≤ ρ ^ n := pow_le_pow_right₀ hρ1 (Nat.sub_le n k)
                _ ≤ c₀ ^ m * ρ ^ n := le_mul_of_one_le_left (by positivity) hc
          calc K1 * (((n - k : ℕ) : ℝ) + 2) ^ m * ρ ^ (n - k)
              ≤ K1 * ((n : ℝ) + 2) ^ m * (c₀ ^ m * M ^ n) :=
                mul_le_mul (mul_le_mul_of_nonneg_left h1 hK1) h2 (by positivity) (by positivity)
            _ = K1 * c₀ ^ m * ((n : ℝ) + 2) ^ m * M ^ n := by ring
      · rw [coeff_curveP_eq_zero α (by omega), zero_mul, norm_zero]
    refine (norm_sum_le _ _).trans ((sum_le_sum hterm).trans ?_)
    rw [← sum_filter]
    calc ∑ k ∈ (range (n + 1)).filter (· ≤ m),
          ((m : ℝ) + 1) ^ m * t ^ m * (K1 * c₀ ^ m * ((n : ℝ) + 2) ^ m * M ^ n)
        ≤ ∑ k ∈ range (m + 1),
          ((m : ℝ) + 1) ^ m * t ^ m * (K1 * c₀ ^ m * ((n : ℝ) + 2) ^ m * M ^ n) :=
          sum_le_sum_of_subset_of_nonneg (fun k hk => by
            simp only [mem_filter, mem_range] at hk ⊢; omega) (fun _ _ _ => by positivity)
      _ = K2 * ((n : ℝ) + 2) ^ m * M ^ n := by
          rw [sum_const, card_range, nsmul_eq_mul]; simp only [K2]; push_cast; ring
  -- two partial sums
  have hpartial : ∀ (F : PowerSeries ℂ) (K : ℝ) (j : ℕ), 0 ≤ K →
      (∀ n, ‖coeff n F‖ ≤ K * ((n : ℝ) + 2) ^ j * M ^ n) →
      ∀ n, ‖coeff n (geomSeries 1 * F)‖ ≤ K * ((n : ℝ) + 2) ^ (j + 1) * M ^ n := by
    intro F K j hK hF n
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have hterm : ∀ k ∈ range (n + 1), ‖coeff k (geomSeries 1) * coeff (n - k) F‖ ≤
        K * ((n : ℝ) + 2) ^ j * M ^ n := by
      intro k hk
      simp only [geomSeries, coeff_mk, one_pow, one_mul]
      refine (hF (n - k)).trans ?_
      have h1 : (((n - k : ℕ) : ℝ) + 2) ^ j ≤ ((n : ℝ) + 2) ^ j :=
        pow_le_pow_left₀ (by positivity) (by
          have : ((n - k : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n k
          linarith) j
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hK)
        (pow_le_pow_right₀ hM1 (Nat.sub_le n k)) (by positivity) (by positivity)
    refine (norm_sum_le _ _).trans ((sum_le_sum hterm).trans ?_)
    rw [sum_const, card_range, nsmul_eq_mul, pow_succ]
    have : ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 2 := by push_cast; linarith
    calc ((n + 1 : ℕ) : ℝ) * (K * ((n : ℝ) + 2) ^ j * M ^ n)
        ≤ ((n : ℝ) + 2) * (K * ((n : ℝ) + 2) ^ j * M ^ n) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = K * (((n : ℝ) + 2) ^ j * ((n : ℝ) + 2)) * M ^ n := by ring
  have hA1 := hpartial _ K2 m hK2 hPC
  have hA2 := hpartial _ K2 (m + 1) hK2 hA1
  have hAeq : ∀ n, curveCentredPrefix q α ε n =
      coeff n (geomSeries 1 * (geomSeries 1 * (curveP α * (geomSeries q * Bs)))) := by
    intro n
    rw [curveCentredPrefix, ← coeff_C_mul, ← map_sub]
    congr 1
    simp only [Bs, curveZ, R, δ]
    ring
  -- the energy
  set G : ℕ → ℝ := fun n => K2 ^ 2 * (((n : ℝ) + 2) ^ (2 * (m + 2)) * r ^ n)
  have hG : Summable G := (summable_add_pow_mul_geometric (2 * (m + 2)) 2 hr0 hr1).mul_left _
  refine ⟨∑' n, G n, fun D => ?_⟩
  refine le_trans ?_ (hG.sum_le_tsum (range (D + 1)) (fun n _ => by positivity))
  refine sum_le_sum fun n _ => ?_
  rw [hAeq, div_le_iff₀ (by positivity)]
  have hn := hA2 n
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  calc ‖coeff n (geomSeries 1 * (geomSeries 1 * (curveP α * (geomSeries q * Bs))))‖ ^ 2
      ≤ (K2 * ((n : ℝ) + 2) ^ (m + 1 + 1) * M ^ n) ^ 2 := hsq
    _ = G n * (q : ℝ) ^ n := by
        simp only [G, r]
        rw [div_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
        field_simp
        ring

/-- **On the Weil circle the curve receiver is admitted at every positive damping.** -/
theorem exists_curveReceiverEnergy_le_of_weil {q : ℕ} (hq : 2 ≤ q) {α : Fin m → ℂ}
    (hα : ∀ i, ‖α i‖ ≤ Real.sqrt q) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, ∀ D, curveReceiverEnergy q α ε D ≤ B :=
  exists_curveReceiverEnergy_le hq le_rfl (fun i => by rw [one_mul]; exact hα i)
    (Real.one_lt_rpow (by exact_mod_cast (show 1 < q by omega)) hε)

end GaloisForLFunctions.ArithmeticCompensationTheory
