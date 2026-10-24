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
* `exists_curveReceiverEnergy_le_of_weil`: on the Weil circle, `λ = 1`, at every `ε > 0`;
* `not_exists_curveReceiverEnergy_le_single`: conversely, for one eigenvalue `a = λ√q` with
  `q^ε < λ < q^{1/2+ε}`, `a ≠ q`, the receiver energy is unbounded — the source grows like
  `(a q^{−ε})ⁿ`, faster than the norm weight allows;
* `coeff_curveAnnihilatorFilter_mul_curveCentredSeries`: for any number `m` of complex eigenvalues,
  multiplying the centred prefix series by the finite polynomial filter
  `Q_i(u) = (1 − u)²(1 − qu) Π_{j ≠ i}(1 − α_j q^{−ε}u)` of degree `m + 2` annihilates all other
  Frobenius modes, the poles at `1` and `1/q`, and the density term above degree `2m + 1`, leaving
  the exact pure geometric mode `curveEigenvalueResidue q α ε i · (α_i q^{−ε})ᴺ` at every degree
  `N ≥ 2m + 2`;
* `exists_pos_mul_pow_le_curveReceiverEnergy`, `not_exists_curveReceiverEnergy_le`: hence if any
  eigenvalue `α_i` lies below the damping threshold (`√q q^ε < ‖α_i‖`), is not a pole (`α_i ≠ 1, q`)
  and is not shadowed by another zero (`∀ j, α_j ≠ α_i q^{−ε}`), the cumulative receiver energy
  grows exponentially at rate `(‖α_i‖ q^{−ε}/√q)^{2D}` for all `D ≥ 2m + 2` and admission fails —
  oscillating multi-eigenvalue terms cannot cancel across a block of length `m + 3`;
* `curveReceiverEnergy_admitted_iff_of_equimodular`, `weil_iff_cofinal_curveReceiverEnergy`: on an
  equimodular family `‖α_j‖ = λ√q` admission at `ε > 0` holds iff `λ < q^ε` (for `λ ≠ q^ε`), and
  for an arbitrary tuple `α : Fin m → ℂ` with `α_i ≠ q` **cofinal admission as `ε ↓ 0` holds if
  and only if the Weil bound `∀ i, ‖α_i‖ ≤ √q` holds**.

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

/-- The centred source is the double prefix of `P(u)(1 − qu)^{−1}(R(u) − δ)`. -/
theorem curveCentredPrefix_eq (q : ℕ) (α : Fin m → ℂ) (ε : ℝ) (n : ℕ) :
    curveCentredPrefix q α ε n = coeff n (geomSeries 1 * (geomSeries 1 * (curveP α *
      (geomSeries q * (curveDampedZinv q α ε - C (curveDensity q α ε)))))) := by
  rw [curveCentredPrefix, ← coeff_C_mul, ← map_sub]
  congr 1
  simp only [curveZ]
  ring

/-- A prefix is a product with `1/(1 − u)`. -/
theorem coeff_geomSeries_one_mul (F : PowerSeries ℂ) (n : ℕ) :
    coeff n (geomSeries 1 * F) = ∑ j ∈ range (n + 1), coeff j F := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [geomSeries, coeff_mk, one_pow, one_mul]
  exact sum_range_reflect (fun j => coeff j F) (n + 1)

/-- The damped Möbius coefficients are at most `2(1 + q)(k + 1)^m (t q^{−ε})^k`. -/
theorem norm_coeff_curveDampedZinv_le (q : ℕ) {α : Fin m → ℂ} {t : ℝ} (ht : 1 ≤ t)
    (hα : ∀ i, ‖α i‖ ≤ t) (ε : ℝ) (k : ℕ) :
    ‖coeff k (curveDampedZinv q α ε)‖ ≤
      2 * (1 + (q : ℝ)) * ((k : ℝ) + 1) ^ m * (t * (q : ℝ) ^ (-ε)) ^ k := by
  have hPinv : ∀ k, ‖coeff k (curvePinv α)‖ ≤ 1 * ((k : ℝ) + 1) ^ m * t ^ k := fun k => by
    rw [one_mul]; exact norm_coeff_curvePinv_le α (by linarith) hα k
  have h1 : ∀ k, ‖coeff k ((1 - C ((1 : ℝ) : ℂ) * X) * curvePinv α)‖ ≤
      (1 + 1) * 1 * ((k : ℝ) + 1) ^ m * t ^ k :=
    norm_coeff_one_sub_mul_le zero_le_one ht zero_le_one hPinv
  have h2 := norm_coeff_one_sub_mul_le (by positivity) ht (Nat.cast_nonneg q) h1 k
  have he : curveZinv q α = (1 - C (((q : ℕ) : ℝ) : ℂ) * X) *
      ((1 - C ((1 : ℝ) : ℂ) * X) * curvePinv α) := by
    rw [curveZinv]; push_cast; ring
  have hρ₀ : 0 ≤ (q : ℝ) ^ (-ε) := Real.rpow_nonneg (Nat.cast_nonneg q) _
  rw [curveDampedZinv, coeff_rescale, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hρ₀, he]
  calc ((q : ℝ) ^ (-ε)) ^ k * ‖coeff k ((1 - C (((q : ℕ) : ℝ) : ℂ) * X) *
        ((1 - C ((1 : ℝ) : ℂ) * X) * curvePinv α))‖
      ≤ ((q : ℝ) ^ (-ε)) ^ k * ((1 + (q : ℝ)) * ((1 + 1) * 1) * ((k : ℝ) + 1) ^ m * t ^ k) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 * (1 + (q : ℝ)) * ((k : ℝ) + 1) ^ m * (t * (q : ℝ) ^ (-ε)) ^ k := by
        rw [mul_pow]; ring

/-- **The density series converges and the centred series vanishes at `u = 1/q`**, as soon as the
damped zero growth `t q^{−ε}` is below `q`. -/
theorem summable_and_tsum_curveCentredSeries {q : ℕ} (hq : 2 ≤ q) {α : Fin m → ℂ} {t : ℝ}
    (ht : 1 ≤ t) (hα : ∀ i, ‖α i‖ ≤ t) {ε : ℝ} (hx : t * (q : ℝ) ^ (-ε) < q) :
    Summable (fun j => coeff j (curveDampedZinv q α ε - C (curveDensity q α ε)) / (q : ℂ) ^ j) ∧
      ∑' j, coeff j (curveDampedZinv q α ε - C (curveDensity q α ε)) / (q : ℂ) ^ j = 0 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  set x := t * (q : ℝ) ^ (-ε) / q
  have hx0 : 0 < x := by
    have := Real.rpow_pos_of_pos hq0 (-ε); positivity
  have hx1 : x < 1 := by rw [div_lt_one hq0]; exact hx
  have hqk : ∀ k : ℕ, ‖(q : ℂ) ^ k‖ = (q : ℝ) ^ k := fun k => by
    rw [norm_pow, Complex.norm_natCast]
  have hRsum : Summable fun k => coeff k (curveDampedZinv q α ε) / (q : ℂ) ^ k := by
    refine Summable.of_norm_bounded
      ((summable_add_pow_mul_geometric m 1 hx0 hx1).mul_left (2 * (1 + (q : ℝ)))) fun k => ?_
    rw [norm_div, hqk, div_le_iff₀ (by positivity)]
    refine (norm_coeff_curveDampedZinv_le q ht hα ε k).trans (le_of_eq ?_)
    simp only [x]; rw [div_pow]; field_simp; push_cast; ring
  have hfin : Summable fun j : ℕ => (if j = 0 then curveDensity q α ε else 0) :=
    summable_of_ne_finset_zero (s := {0}) fun j hj => by
      simp only [mem_singleton] at hj; simp [hj]
  have he : (fun j => coeff j (curveDampedZinv q α ε - C (curveDensity q α ε)) / (q : ℂ) ^ j) =
      fun j => coeff j (curveDampedZinv q α ε) / (q : ℂ) ^ j -
        (if j = 0 then curveDensity q α ε else 0) := by
    funext j
    simp only [map_sub, coeff_C]
    split_ifs with h
    · subst h; simp
    · simp
  refine ⟨he ▸ hRsum.sub hfin, ?_⟩
  rw [he, Summable.tsum_sub hRsum hfin, tsum_ite_eq]
  simp [curveDensity]

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
  -- coefficient bounds and the polar cancellation
  have hα' : ∀ i, ‖α i‖ ≤ t := hα
  set KR : ℝ := 2 * (1 + (q : ℝ))
  have hKR : 0 ≤ KR := by positivity
  have hR : ∀ k, ‖coeff k (curveDampedZinv q α ε)‖ ≤ KR * ((k : ℝ) + 1) ^ m * ρ ^ k :=
    norm_coeff_curveDampedZinv_le q ht1 hα' ε
  set R := curveDampedZinv q α ε
  set δ := curveDensity q α ε
  have hqk : ∀ k : ℕ, ‖(q : ℂ) ^ k‖ = (q : ℝ) ^ k := fun k => by
    rw [norm_pow, Complex.norm_natCast]
  set Bs := R - C δ
  have hBcoeff : ∀ j, 1 ≤ j → coeff j Bs = coeff j R := fun j hj => by
    simp only [Bs, map_sub, coeff_C, if_neg (show j ≠ 0 by omega), sub_zero]
  have hρq : t * (q : ℝ) ^ (-ε) < q := by
    have := (div_lt_one hq0).mp hx1; exact this
  obtain ⟨hBsum, hB0⟩ := summable_and_tsum_curveCentredSeries hq ht1 hα' hρq
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
      coeff n (geomSeries 1 * (geomSeries 1 * (curveP α * (geomSeries q * Bs)))) :=
    curveCentredPrefix_eq q α ε
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

/-! ## Below the zero width admission fails -/

/-- For one eigenvalue `a`, the Möbius coefficients beyond degree one are `aʲ(a − 1)(a − q)`. -/
theorem coeff_curveZinv_single (q : ℕ) (a : ℂ) (j : ℕ) :
    coeff (j + 2) (curveZinv q (fun _ : Fin 1 => a)) = a ^ j * (a - 1) * (a - q) := by
  have hP : curvePinv (fun _ : Fin 1 => a) = geomSeries a := by
    simp [curvePinv]
  have he : curveZinv q (fun _ : Fin 1 => a) = geomSeries a - X * geomSeries a -
      C (q : ℂ) * (X * geomSeries a) + C (q : ℂ) * (X * (X * geomSeries a)) := by
    rw [curveZinv, hP, map_one]; ring
  rw [he, map_add, map_sub, map_sub, coeff_C_mul, coeff_C_mul, coeff_succ_X_mul,
    coeff_succ_X_mul, coeff_succ_X_mul]
  simp only [geomSeries, coeff_mk]
  ring

/-- **Below the zero width the curve receiver is not admitted.** For a single eigenvalue
`a = λ√q` with `q^ε < λ < q^{1/2+ε}` and `a ≠ q`, the receiver energy is unbounded: the
coefficients of the source grow like `(a q^{−ε})ⁿ`, faster than the norm weight `q^{n/2}`.
Together with `exists_curveReceiverEnergy_le`, admission at `ε` is decided by the zero width. -/
theorem not_exists_curveReceiverEnergy_le_single {q : ℕ} (hq : 2 ≤ q) {a ε : ℝ} (hε : 0 < ε)
    (ha : Real.sqrt q * (q : ℝ) ^ ε < a) (haq : a < (q : ℝ) ^ (1 + ε)) (haq' : a ≠ q) :
    ¬ ∃ B : ℝ, ∀ D, curveReceiverEnergy q (fun _ : Fin 1 => (a : ℂ)) ε D ≤ B := by
  rintro ⟨B, hB⟩
  set α : Fin 1 → ℂ := fun _ => (a : ℂ)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  set s := Real.sqrt q
  have hs1 : 1 < s := Real.lt_sqrt_of_sq_lt (by norm_num; linarith)
  have hss : s * s = q := Real.mul_self_sqrt hq0.le
  set ρ₀ := (q : ℝ) ^ (-ε)
  have hρ₀ : 0 < ρ₀ := Real.rpow_pos_of_pos hq0 _
  have hρ₀1 : ρ₀ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  have hqε : (q : ℝ) ^ ε * ρ₀ = 1 := by
    rw [← Real.rpow_add hq0, add_neg_cancel, Real.rpow_zero]
  have hqε0 : 0 < (q : ℝ) ^ ε := Real.rpow_pos_of_pos hq0 _
  have ha1 : 1 < a := by nlinarith [Real.one_le_rpow hq1.le hε.le]
  set ρ := a * ρ₀
  have hρs : s < ρ := by
    have := mul_lt_mul_of_pos_right ha hρ₀
    rw [mul_assoc, hqε, mul_one] at this; exact this
  have hρ0 : 0 < ρ := by linarith
  have hρq : ρ < q := by
    have h := mul_lt_mul_of_pos_right haq hρ₀
    rw [Real.rpow_add hq0, Real.rpow_one, mul_assoc, hqε, mul_one] at h; exact h
  set y := ρ / q
  have hy0 : 0 < y := by positivity
  have hy1 : y < 1 := by rw [div_lt_one hq0]; exact hρq
  -- the coefficients of `(1 − qu)^{−1}(R − δ)` are `K ρⁿ` from degree one on
  set κ : ℝ := (a - 1) * (a - q) / a ^ 2
  set K : ℝ := -(κ * y / (1 - y))
  have hκ : κ ≠ 0 := by
    have : a - (q : ℝ) ≠ 0 := sub_ne_zero.mpr haq'
    have : a - 1 ≠ 0 := by linarith
    positivity
  have hK : K ≠ 0 := by
    have : 1 - y ≠ 0 := by linarith
    simp only [K, neg_ne_zero]; positivity
  have hα : ∀ i, ‖α i‖ ≤ a := fun i => by
    simp only [α, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < a),
      le_refl]
  obtain ⟨hBsum, hB0⟩ := summable_and_tsum_curveCentredSeries hq ha1.le hα hρq
  set Bs := curveDampedZinv q α ε - C (curveDensity q α ε)
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast (by linarith : a ≠ 0)
  have hBj : ∀ j, coeff (j + 2) Bs = ((κ * ρ ^ (j + 2) : ℝ) : ℂ) := by
    intro j
    have hz := coeff_curveZinv_single q (a : ℂ) j
    have hcoef : coeff (j + 2) Bs = ((ρ₀ ^ (j + 2) : ℝ) : ℂ) * coeff (j + 2) (curveZinv q α) := by
      simp only [Bs, map_sub, coeff_C, if_neg (show j + 2 ≠ 0 by omega), sub_zero,
        curveDampedZinv, coeff_rescale]
      push_cast; rfl
    rw [hcoef, hz]
    simp only [κ, ρ]
    push_cast
    field_simp
    ring
  have hreal : ∀ n : ℕ, -((q : ℝ) ^ n * (κ * y ^ (n + 1) * (1 - y)⁻¹)) = K * ρ ^ n := by
    intro n
    simp only [K, y]
    rw [div_pow, pow_succ]
    have h1 : (1 : ℝ) - ρ / q ≠ 0 := by linarith
    field_simp
    ring
  have hc : ∀ n, 1 ≤ n → coeff n (geomSeries q * Bs) = ((K * ρ ^ n : ℝ) : ℂ) := by
    intro n hn
    rw [coeff_geomSeries_mul_eq_neg_tail (by omega) hBsum hB0 n]
    have hterm : ∀ i, coeff (i + (n + 1)) Bs / (q : ℂ) ^ (i + (n + 1)) =
        ((κ * y ^ (n + 1) : ℝ) : ℂ) * (y : ℂ) ^ i := by
      intro i
      obtain ⟨k, hk⟩ : ∃ k, i + (n + 1) = k + 2 := ⟨i + n - 1, by omega⟩
      rw [hk, hBj, ← hk]
      have hr : κ * ρ ^ (i + (n + 1)) / (q : ℝ) ^ (i + (n + 1)) = κ * y ^ (n + 1) * y ^ i := by
        simp only [y]
        rw [div_pow, div_pow, pow_add ρ i, pow_add (q : ℝ) i]
        field_simp
      have hq0' : (q : ℂ) ^ (i + (n + 1)) = (((q : ℝ) ^ (i + (n + 1)) : ℝ) : ℂ) := by push_cast; rfl
      rw [hq0', ← Complex.ofReal_div, hr]
      push_cast; ring
    have hy : ‖(y : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hy0.le]; exact hy1
    rw [tsum_congr hterm, tsum_mul_left, tsum_geometric_of_norm_lt_one hy, ← hreal n]
    push_cast
    ring
  -- after `P(u) = 1 − au` the coefficients are `L ρ^{n−1}` from degree two on
  set L : ℝ := K * (ρ - a)
  have hL : L ≠ 0 := by
    have : ρ - a ≠ 0 := by
      have : ρ - a = a * (ρ₀ - 1) := by simp only [ρ]; ring
      rw [this]; exact mul_ne_zero (by linarith) (by linarith)
    exact mul_ne_zero hK this
  set Dser := curveP α * (geomSeries q * Bs)
  have hPα : curveP α = 1 - C (a : ℂ) * X := by simp [curveP, α]
  have hd : ∀ j, coeff (j + 2) Dser = ((L * ρ ^ (j + 1) : ℝ) : ℂ) := by
    intro j
    have he : Dser = geomSeries q * Bs - C (a : ℂ) * (X * (geomSeries q * Bs)) := by
      simp only [Dser, hPα]; ring
    rw [he, map_sub, coeff_C_mul, coeff_succ_X_mul, hc (j + 2) (by omega), hc (j + 1) (by omega)]
    simp only [L]
    push_cast
    ring
  -- the double prefix grows like `|L| ρ^{n−1}`
  set C₀ := ‖coeff 0 Dser‖ + ‖coeff 1 Dser‖
  have hA : ∀ n : ℕ, 2 ≤ n →
      |L| * ρ ^ (n - 1) - ((n : ℝ) + 1) * C₀ ≤ ‖curveCentredPrefix q α ε n‖ := by
    intro n hn
    rw [curveCentredPrefix_eq, coeff_geomSeries_one_mul]
    simp only [coeff_geomSeries_one_mul]
    -- split each coefficient into its geometric part and its first two terms
    set g : ℕ → ℝ := fun j => if 2 ≤ j then L * ρ ^ (j - 1) else 0
    set h : ℕ → ℂ := fun j => if 2 ≤ j then 0 else coeff j Dser
    have hsplit : ∀ j, coeff j Dser = (g j : ℂ) + h j := by
      intro j
      simp only [g, h]
      split_ifs with hj
      · obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
        rw [hd k, show k + 2 - 1 = k + 1 by omega]; simp
      · simp
    have hsum : (∑ k ∈ range (n + 1), ∑ j ∈ range (k + 1), coeff j Dser) =
        ((∑ k ∈ range (n + 1), ∑ j ∈ range (k + 1), g j : ℝ) : ℂ) +
          ∑ k ∈ range (n + 1), ∑ j ∈ range (k + 1), h j := by
      simp only [hsplit, sum_add_distrib]; push_cast; ring
    have hh : ‖∑ k ∈ range (n + 1), ∑ j ∈ range (k + 1), h j‖ ≤ ((n : ℝ) + 1) * C₀ := by
      have hk : ∀ k, ‖∑ j ∈ range (k + 1), h j‖ ≤ C₀ := by
        intro k
        refine (norm_sum_le _ _).trans ?_
        have hle : ∀ j ∈ range (k + 1), ‖h j‖ ≤ if j < 2 then ‖coeff j Dser‖ else 0 := by
          intro j _
          simp only [h]
          split_ifs <;> first | omega | simp
        refine (sum_le_sum hle).trans ?_
        rw [← sum_filter]
        calc ∑ j ∈ (range (k + 1)).filter (· < 2), ‖coeff j Dser‖
            ≤ ∑ j ∈ range 2, ‖coeff j Dser‖ :=
              sum_le_sum_of_subset_of_nonneg (fun j hj => by
                simp only [mem_filter, mem_range] at hj ⊢; omega) (fun _ _ _ => norm_nonneg _)
          _ = C₀ := by simp [C₀, sum_range_succ]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ k ∈ range (n + 1), ‖∑ j ∈ range (k + 1), h j‖ ≤ ∑ _k ∈ range (n + 1), C₀ :=
            sum_le_sum fun k _ => hk k
        _ = ((n : ℝ) + 1) * C₀ := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
    have hg0 : ∀ j, 0 ≤ g j * L := by
      intro j; simp only [g]; split_ifs
      · nlinarith [mul_self_nonneg L, pow_pos hρ0 (j - 1)]
      · simp
    set W := ∑ k ∈ range (n + 1), ∑ j ∈ range (k + 1), g j
    have hWL : L ^ 2 * ρ ^ (n - 1) ≤ W * L := by
      have hnn : ∀ k ∈ range (n + 1), 0 ≤ (∑ j ∈ range (k + 1), g j) * L := fun k _ => by
        rw [sum_mul]; exact sum_nonneg fun j _ => hg0 j
      calc L ^ 2 * ρ ^ (n - 1) = g n * L := by simp only [g, if_pos hn]; ring
        _ ≤ (∑ j ∈ range (n + 1), g j) * L := by
            rw [sum_mul]
            exact single_le_sum (fun j _ => hg0 j) (mem_range.mpr (by omega))
        _ ≤ ∑ k ∈ range (n + 1), (∑ j ∈ range (k + 1), g j) * L :=
            single_le_sum hnn (mem_range.mpr (by omega))
        _ = W * L := by rw [sum_mul]
    have hLW : |L| * ρ ^ (n - 1) ≤ |W| := by
      have hL0 : 0 < |L| := abs_pos.mpr hL
      have h1 : W * L ≤ |W| * |L| := by rw [← abs_mul]; exact le_abs_self _
      have h2 : |L| * (|L| * ρ ^ (n - 1)) ≤ |L| * |W| :=
        calc |L| * (|L| * ρ ^ (n - 1)) = L ^ 2 * ρ ^ (n - 1) := by rw [← sq_abs L]; ring
          _ ≤ W * L := hWL
          _ ≤ |W| * |L| := h1
          _ = |L| * |W| := mul_comm _ _
      exact le_of_mul_le_mul_left h2 hL0
    rw [hsum]
    have h3 := norm_sub_le ((W : ℂ) + ∑ k ∈ range (n + 1), ∑ j ∈ range (k + 1), h j)
      (∑ k ∈ range (n + 1), ∑ j ∈ range (k + 1), h j)
    rw [add_sub_cancel_right, Complex.norm_real, Real.norm_eq_abs] at h3
    linarith
  -- the bounded energy caps every term: `‖A(n)‖ ≤ √B qⁿᐟ²`
  have hB0' : 0 ≤ B := (sum_nonneg fun n _ => by positivity).trans (hB 0)
  have hcap : ∀ n, ‖curveCentredPrefix q α ε n‖ ≤ Real.sqrt B * s ^ n := by
    intro n
    have hterm : ‖curveCentredPrefix q α ε n‖ ^ 2 / (q : ℝ) ^ n ≤ B :=
      (single_le_sum (f := fun k => ‖curveCentredPrefix q α ε k‖ ^ 2 / (q : ℝ) ^ k)
        (fun k _ => by positivity) (mem_range.mpr (Nat.lt_succ_self n))).trans (hB n)
    rw [div_le_iff₀ (by positivity)] at hterm
    have hsn : s ^ n * s ^ n = (q : ℝ) ^ n := by rw [← mul_pow, hss]
    have hsq : ‖curveCentredPrefix q α ε n‖ ^ 2 ≤ (Real.sqrt B * s ^ n) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hB0', sq (s ^ n), hsn]; exact hterm
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  -- but `ρ > √q`: the ratio `(ρ/s)ⁿ` diverges while `(n + 1)/sⁿ → 0`
  have hdiv : Tendsto (fun n : ℕ => |L| / ρ * (ρ / s) ^ n - C₀ * (((n : ℝ) + 1) * (1 / s) ^ n))
      atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => (ρ / s) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt ((one_lt_div (by linarith)).mpr hρs)
    have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * (1 / s) ^ n) atTop (𝓝 0) := by
      have hr : |1 / s| < 1 := by
        rw [abs_of_pos (by positivity), div_lt_one (by linarith)]; exact hs1
      have h3 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hr
      have h4 := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / s)
        ((div_lt_one (by linarith)).mpr hs1)
      have h5 := h3.add h4
      rw [add_zero] at h5
      exact h5.congr fun n => by simp only [pow_one]; ring
    have h6 := (h1.const_mul_atTop (by positivity : 0 < |L| / ρ)).atTop_add (h2.const_mul (-C₀))
    exact h6.congr fun n => by ring
  obtain ⟨n, hn⟩ := ((hdiv.eventually (eventually_gt_atTop (Real.sqrt B))).and
    (eventually_ge_atTop 2)).exists
  have hlow := hA n hn.2
  have hup := hcap n
  have hsn : 0 < s ^ n := pow_pos (by linarith) n
  have key : |L| / ρ * (ρ / s) ^ n - C₀ * (((n : ℝ) + 1) * (1 / s) ^ n) ≤ Real.sqrt B := by
    have e : |L| / ρ * (ρ / s) ^ n - C₀ * (((n : ℝ) + 1) * (1 / s) ^ n) =
        (|L| * ρ ^ (n - 1) - ((n : ℝ) + 1) * C₀) / s ^ n := by
      rw [div_pow, div_pow, one_pow, show ρ ^ n = ρ ^ (n - 1) * ρ by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]]
      field_simp
    rw [e, div_le_iff₀ hsn]
    linarith
  linarith [hn.1]

/-! ## Multi-eigenvalue non-cancellation and the annihilator filter law

For several complex eigenvalues `α₀, …, α_{m−1}` the coefficients of `1/P(q^{−ε}u)` are sums of
oscillating modes `Σᵢ cᵢ (αᵢ q^{−ε})ⁿ` that can cancel at isolated degrees. Across a window of
length `m + 3`, however, no cancellation can occur: multiplying the centred prefix generating series
by the finite polynomial filter

`Qᵢ(u) = (1 − u)²(1 − qu) Π_{j ≠ i} (1 − αⱼ q^{−ε} u)`

of degree `m + 2` annihilates all other Frobenius modes, the poles at `1` and `1/q`, and the
density polynomial above degree `2m + 1`, isolating the single geometric mode `(αᵢ q^{−ε})ᴺ` at
every degree `N ≥ 2m + 2`. -/

/-- The generating series of the centred damped prefixes `curveCentredPrefix q α ε n`. -/
def curveCentredSeries (q : ℕ) (α : Fin m → ℂ) (ε : ℝ) : PowerSeries ℂ :=
  geomSeries 1 * (geomSeries 1 * (curveP α *
    (geomSeries q * (curveDampedZinv q α ε - C (curveDensity q α ε)))))

theorem coeff_curveCentredSeries (q : ℕ) (α : Fin m → ℂ) (ε : ℝ) (n : ℕ) :
    coeff n (curveCentredSeries q α ε) = curveCentredPrefix q α ε n :=
  (curveCentredPrefix_eq q α ε n).symm

/-- The polynomial filter of degree `m + 2` that annihilates the poles at `1` and `1/q` and all
damped Frobenius eigenvalues except `α i`. -/
def curveAnnihilatorFilter (q : ℕ) (α : Fin m → ℂ) (ε : ℝ) (i : Fin m) : PowerSeries ℂ :=
  (∏ j ∈ univ.erase i, (1 - C ((((q : ℝ) ^ (-ε) : ℝ) : ℂ) * α j) * X)) *
    (1 - C 1 * X) * (1 - C 1 * X) * (1 - C (q : ℂ) * X)

/-- The filtered series including the polynomial density term of degree `< 2m`. -/
def curveFilteredSeries (q : ℕ) (α : Fin m → ℂ) (ε : ℝ) (i : Fin m) : PowerSeries ℂ :=
  curveAnnihilatorFilter q α ε i * curveCentredSeries q α ε +
    C (curveDensity q α ε) *
      (∏ j ∈ univ.erase i, (1 - C ((((q : ℝ) ^ (-ε) : ℝ) : ℂ) * α j) * X)) * curveP α

/-- The characteristic numerator `P(u)(1 − q^{−ε}u)(1 − q^{1−ε}u)` of degree `m + 2`. -/
def curveCharacteristicNumerator (q : ℕ) (α : Fin m → ℂ) (ε : ℝ) : PowerSeries ℂ :=
  curveP α * (1 - C (((q : ℝ) ^ (-ε) : ℝ) : ℂ) * X) *
    (1 - C ((((q : ℝ) ^ (-ε) : ℝ) : ℂ) * q) * X)

/-- The amplitude of the isolated geometric mode `(q^{−ε} αᵢ)ᴺ` after annihilator filtering:
`(Πⱼ (1 − αⱼ / (q^{−ε} αᵢ))) (1 − 1/αᵢ) (1 − q/αᵢ)`. -/
def curveEigenvalueResidue (q : ℕ) (α : Fin m → ℂ) (ε : ℝ) (i : Fin m) : ℂ :=
  (∏ j : Fin m, (1 - α j * ((((q : ℝ) ^ (-ε) : ℝ) : ℂ) * α i)⁻¹)) *
    (1 - (((q : ℝ) ^ (-ε) : ℝ) : ℂ) * ((((q : ℝ) ^ (-ε) : ℝ) : ℂ) * α i)⁻¹) *
    (1 - ((((q : ℝ) ^ (-ε) : ℝ) : ℂ) * q) * ((((q : ℝ) ^ (-ε) : ℝ) : ℂ) * α i)⁻¹)

theorem rescale_one_sub_C_mul_X (a c : ℂ) :
    rescale a (1 - C c * X) = 1 - C (a * c) * X := by
  ext n
  rw [coeff_rescale, map_sub, map_sub, coeff_one, coeff_C_mul, coeff_C_mul, coeff_X]
  rcases n with _ | _ | n <;> simp [mul_comm a c]

theorem rescale_curveP (a : ℂ) (α : Fin m → ℂ) :
    rescale a (curveP α) = curveP (fun i => a * α i) := by
  simp only [curveP, map_prod, rescale_one_sub_C_mul_X]

theorem curveP_mul_curveZinv (q : ℕ) (α : Fin m → ℂ) :
    curveP α * curveZinv q α = (1 - C 1 * X) * (1 - C (q : ℂ) * X) := by
  have hP : curveP α * curvePinv α = 1 := by
    rw [curveP, curvePinv, ← prod_mul_distrib]
    exact prod_eq_one fun i _ => one_sub_mul_geomSeries (α i)
  calc curveP α * curveZinv q α
      = (1 - C 1 * X) * (1 - C (q : ℂ) * X) * (curveP α * curvePinv α) := by
        rw [curveZinv]; ring
    _ = (1 - C 1 * X) * (1 - C (q : ℂ) * X) := by rw [hP, mul_one]

theorem curveP_rescale_mul_curveDampedZinv (q : ℕ) (α : Fin m → ℂ) (ε : ℝ) :
    curveP (fun i => (((q : ℝ) ^ (-ε) : ℝ) : ℂ) * α i) * curveDampedZinv q α ε =
      (1 - C (((q : ℝ) ^ (-ε) : ℝ) : ℂ) * X) *
        (1 - C ((((q : ℝ) ^ (-ε) : ℝ) : ℂ) * q) * X) := by
  set ρ₀ : ℂ := (((q : ℝ) ^ (-ε) : ℝ) : ℂ)
  have h := congr_arg (rescale ρ₀) (curveP_mul_curveZinv q α)
  rw [map_mul, map_mul, rescale_curveP, rescale_one_sub_C_mul_X, rescale_one_sub_C_mul_X,
    mul_one] at h
  exact h

/-- **The exact polynomial annihilator identity.** Multiplying the filtered series by
`1 − q^{−ε} αᵢ u` leaves the polynomial `P(u)(1 − q^{−ε}u)(1 − q^{1−ε}u)`. -/
theorem one_sub_mul_curveFilteredSeries (q : ℕ) (α : Fin m → ℂ) (ε : ℝ) (i : Fin m) :
    (1 - C ((((q : ℝ) ^ (-ε) : ℝ) : ℂ) * α i) * X) * curveFilteredSeries q α ε i =
      curveCharacteristicNumerator q α ε := by
  set ρ₀ : ℂ := (((q : ℝ) ^ (-ε) : ℝ) : ℂ)
  have h1 := one_sub_mul_geomSeries 1
  have hq := one_sub_mul_geomSeries (q : ℂ)
  have hclear : (1 - C 1 * X) * (1 - C 1 * X) * (1 - C (q : ℂ) * X) * curveCentredSeries q α ε +
      C (curveDensity q α ε) * curveP α = curveP α * curveDampedZinv q α ε := by
    calc (1 - C 1 * X) * (1 - C 1 * X) * (1 - C (q : ℂ) * X) * curveCentredSeries q α ε +
          C (curveDensity q α ε) * curveP α
        = ((1 - C 1 * X) * geomSeries 1) * ((1 - C 1 * X) * geomSeries 1) *
            ((1 - C (q : ℂ) * X) * geomSeries q) *
            (curveP α * (curveDampedZinv q α ε - C (curveDensity q α ε))) +
          C (curveDensity q α ε) * curveP α := by
          rw [curveCentredSeries]; ring
      _ = curveP α * curveDampedZinv q α ε := by
          rw [h1, hq]; ring
  have hsplit : (1 - C (ρ₀ * α i) * X) *
      (∏ j ∈ univ.erase i, (1 - C (ρ₀ * α j) * X)) = curveP (fun j => ρ₀ * α j) :=
    mul_prod_erase univ (fun j => 1 - C (ρ₀ * α j) * X) (mem_univ i)
  calc (1 - C (ρ₀ * α i) * X) * curveFilteredSeries q α ε i
      = ((1 - C (ρ₀ * α i) * X) * ∏ j ∈ univ.erase i, (1 - C (ρ₀ * α j) * X)) *
          ((1 - C 1 * X) * (1 - C 1 * X) * (1 - C (q : ℂ) * X) * curveCentredSeries q α ε +
            C (curveDensity q α ε) * curveP α) := by
        rw [curveFilteredSeries, curveAnnihilatorFilter]; ring
    _ = curveP α * (curveP (fun j => ρ₀ * α j) * curveDampedZinv q α ε) := by
        rw [hsplit, hclear]; ring
    _ = curveCharacteristicNumerator q α ε := by
        rw [curveP_rescale_mul_curveDampedZinv, curveCharacteristicNumerator]; ring

/-- **Telescoping evaluation of `(1 − βX) G(X)`.** When `β z = 1`, the partial sums of
`((1 − βX) G)(z)` telescope to `g_N z^N`. -/
theorem sum_range_coeff_one_sub_mul (G : PowerSeries ℂ) {β z : ℂ} (hβz : β * z = 1) (N : ℕ) :
    (∑ n ∈ range (N + 1), coeff n ((1 - C β * X) * G) * z ^ n) = coeff N G * z ^ N := by
  have he : (1 - C β * X) * G = G - C β * (X * G) := by ring
  induction N with
  | zero =>
      rw [range_one, sum_singleton, he, map_sub, coeff_C_mul, coeff_zero_X_mul]
      simp
  | succ N ih =>
      rw [sum_range_succ, ih, he, map_sub, coeff_C_mul, coeff_succ_X_mul]
      calc coeff N G * z ^ N + (coeff (N + 1) G - β * coeff N G) * z ^ (N + 1)
          = coeff (N + 1) G * z ^ (N + 1) + coeff N G * z ^ N * (1 - β * z) := by
            rw [pow_succ]; ring
        _ = coeff (N + 1) G * z ^ (N + 1) := by rw [hβz, sub_self, mul_zero, add_zero]

theorem coeff_one_sub_mul_eq_zero {F : PowerSeries ℂ} {d : ℕ}
    (hF : ∀ n, d < n → coeff n F = 0) (c : ℂ) {n : ℕ} (hn : d + 1 < n) :
    coeff n ((1 - C c * X) * F) = 0 := by
  have he : (1 - C c * X) * F = F - C c * (X * F) := by ring
  rw [he, map_sub, coeff_C_mul]
  rcases n with _ | n
  · omega
  · rw [coeff_succ_X_mul, hF (n + 1) (by omega), hF n (by omega), mul_zero, sub_zero]

theorem sum_range_coeff_one_sub_mul_of_eq_zero {F : PowerSeries ℂ} {d : ℕ}
    (hF : ∀ n, d < n → coeff n F = 0) (c z : ℂ) :
    (∑ n ∈ range (d + 2), coeff n ((1 - C c * X) * F) * z ^ n) =
      (1 - c * z) * ∑ n ∈ range (d + 1), coeff n F * z ^ n := by
  have he : (1 - C c * X) * F = F - C c * (X * F) := by ring
  simp only [he, map_sub, coeff_C_mul, sub_mul, sum_sub_distrib]
  have h1 : (∑ n ∈ range (d + 2), coeff n F * z ^ n) =
      ∑ n ∈ range (d + 1), coeff n F * z ^ n := by
    rw [sum_range_succ, hF (d + 1) (by omega), zero_mul, add_zero]
  have h2 : (∑ n ∈ range (d + 2), c * coeff n (X * F) * z ^ n) =
      c * z * ∑ n ∈ range (d + 1), coeff n F * z ^ n := by
    rw [sum_range_succ' _ (d + 1), coeff_zero_X_mul, mul_zero, zero_mul, add_zero, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [coeff_succ_X_mul, pow_succ]
    ring
  rw [h1, h2]
  ring

theorem coeff_prod_one_sub_eq_zero {ι : Type*} (s : Finset ι) (f : ι → ℂ) {n : ℕ}
    (hn : s.card < n) : coeff n (∏ j ∈ s, (1 - C (f j) * X)) = 0 := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty =>
      rw [prod_empty, coeff_one, if_neg (by simp at hn; omega)]
  | insert a s ha ih =>
      rw [card_insert_of_notMem ha] at hn
      rw [prod_insert ha]
      exact coeff_one_sub_mul_eq_zero (fun k hk => ih hk) (f a) hn

theorem sum_range_coeff_prod_one_sub {ι : Type*} (s : Finset ι) (f : ι → ℂ) (z : ℂ) :
    (∑ n ∈ range (s.card + 1), coeff n (∏ j ∈ s, (1 - C (f j) * X)) * z ^ n) =
      ∏ j ∈ s, (1 - f j * z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [card_insert_of_notMem ha, prod_insert ha, prod_insert ha]
      rw [sum_range_coeff_one_sub_mul_of_eq_zero (fun k hk => coeff_prod_one_sub_eq_zero s f hk)
        (f a) z, ih]

theorem coeff_curveCharacteristicNumerator_eq_zero (q : ℕ) (α : Fin m → ℂ) (ε : ℝ) {n : ℕ}
    (hn : m + 2 < n) : coeff n (curveCharacteristicNumerator q α ε) = 0 := by
  set ρ₀ : ℂ := (((q : ℝ) ^ (-ε) : ℝ) : ℂ)
  have he : curveCharacteristicNumerator q α ε =
      (1 - C (ρ₀ * q) * X) * ((1 - C ρ₀ * X) * curveP α) := by
    rw [curveCharacteristicNumerator]; ring
  have h1 : ∀ k, m + 1 < k → coeff k ((1 - C ρ₀ * X) * curveP α) = 0 :=
    fun k hk => coeff_one_sub_mul_eq_zero (fun j hj => coeff_curveP_eq_zero α hj) ρ₀ hk
  rw [he]
  exact coeff_one_sub_mul_eq_zero h1 (ρ₀ * q) hn

theorem sum_range_coeff_curveCharacteristicNumerator (q : ℕ) (α : Fin m → ℂ) (ε : ℝ) (z : ℂ)
    {N : ℕ} (hN : m + 2 ≤ N) :
    (∑ n ∈ range (N + 1), coeff n (curveCharacteristicNumerator q α ε) * z ^ n) =
      (∏ j : Fin m, (1 - α j * z)) * (1 - (((q : ℝ) ^ (-ε) : ℝ) : ℂ) * z) *
        (1 - ((((q : ℝ) ^ (-ε) : ℝ) : ℂ) * q) * z) := by
  set ρ₀ : ℂ := (((q : ℝ) ^ (-ε) : ℝ) : ℂ)
  have hsub : (∑ n ∈ range (N + 1), coeff n (curveCharacteristicNumerator q α ε) * z ^ n) =
      ∑ n ∈ range (m + 3), coeff n (curveCharacteristicNumerator q α ε) * z ^ n := by
    refine (sum_subset (range_mono (by omega)) fun n _ hn => ?_).symm
    rw [coeff_curveCharacteristicNumerator_eq_zero q α ε (by simp at hn; omega), zero_mul]
  have he : curveCharacteristicNumerator q α ε =
      (1 - C (ρ₀ * q) * X) * ((1 - C ρ₀ * X) * curveP α) := by
    rw [curveCharacteristicNumerator]; ring
  have h1 : ∀ k, m + 1 < k → coeff k ((1 - C ρ₀ * X) * curveP α) = 0 :=
    fun k hk => coeff_one_sub_mul_eq_zero (fun j hj => coeff_curveP_eq_zero α hj) ρ₀ hk
  have h0 : ∀ k, m < k → coeff k (curveP α) = 0 := fun k hk => coeff_curveP_eq_zero α hk
  have hP : (∑ n ∈ range (m + 1), coeff n (curveP α) * z ^ n) = ∏ j : Fin m, (1 - α j * z) := by
    simpa [curveP, card_univ, Fintype.card_fin] using
      sum_range_coeff_prod_one_sub (univ : Finset (Fin m)) α z
  rw [hsub, he, show m + 3 = (m + 1) + 2 by omega,
    sum_range_coeff_one_sub_mul_of_eq_zero h1 (ρ₀ * q) z,
    show m + 1 + 1 = m + 2 by omega,
    sum_range_coeff_one_sub_mul_of_eq_zero h0 ρ₀ z, hP]
  ring

theorem coeff_mul_eq_zero_of_gt {F G : PowerSeries ℂ} {d₁ d₂ n : ℕ}
    (hF : ∀ k, d₁ < k → coeff k F = 0) (hG : ∀ k, d₂ < k → coeff k G = 0)
    (hn : d₁ + d₂ < n) : coeff n (F * G) = 0 := by
  rw [coeff_mul]
  refine sum_eq_zero fun p hp => ?_
  have hpn := mem_antidiagonal.mp hp
  by_cases h1 : d₁ < p.1
  · rw [hF p.1 h1, zero_mul]
  · rw [hG p.2 (by omega), mul_zero]

/-- Above degree `2m − 1` the polynomial density term of `curveFilteredSeries` vanishes. -/
theorem coeff_curveFilteredSeries_eq_annihilator (q : ℕ) (α : Fin m → ℂ) (ε : ℝ) (i : Fin m)
    {N : ℕ} (hN : 2 * m ≤ N) :
    coeff N (curveFilteredSeries q α ε i) =
      coeff N (curveAnnihilatorFilter q α ε i * curveCentredSeries q α ε) := by
  have hm : 1 ≤ m := Fin.pos i
  set ρ₀ : ℂ := (((q : ℝ) ^ (-ε) : ℝ) : ℂ)
  set P₁ := ∏ j ∈ univ.erase i, (1 - C (ρ₀ * α j) * X)
  have hcard : (univ.erase i).card = m - 1 := by
    rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
  have hP₁ : ∀ k, m - 1 < k → coeff k P₁ = 0 := by
    intro k hk
    exact coeff_prod_one_sub_eq_zero (univ.erase i) (fun j => ρ₀ * α j) (by omega)
  have hP₂ : ∀ k, m < k → coeff k (curveP α) = 0 := fun k hk => coeff_curveP_eq_zero α hk
  have hprod : coeff N (P₁ * curveP α) = 0 :=
    coeff_mul_eq_zero_of_gt hP₁ hP₂ (by omega)
  rw [curveFilteredSeries, map_add, mul_assoc (C (curveDensity q α ε)), coeff_C_mul, hprod,
    mul_zero, add_zero]

/-- **The Annihilator Filter Law.** For every eigenvalue `αᵢ ≠ 0` and every degree `N ≥ 2m + 2`,
the `N`-th coefficient of the annihilator-filtered centred source is the exact pure geometric
mode `curveEigenvalueResidue q α ε i · (q^{−ε} αᵢ)ᴺ`. -/
theorem coeff_curveAnnihilatorFilter_mul_curveCentredSeries {q : ℕ} (hq : 1 ≤ q)
    (α : Fin m → ℂ) (ε : ℝ) {i : Fin m} (hαi : α i ≠ 0) {N : ℕ} (hN : 2 * m + 2 ≤ N) :
    coeff N (curveAnnihilatorFilter q α ε i * curveCentredSeries q α ε) =
      curveEigenvalueResidue q α ε i * ((((q : ℝ) ^ (-ε) : ℝ) : ℂ) * α i) ^ N := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set ρ₀ : ℂ := (((q : ℝ) ^ (-ε) : ℝ) : ℂ)
  have hρ₀ : ρ₀ ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hq0 (-ε)).ne'
  set β : ℂ := ρ₀ * α i
  have hβ : β ≠ 0 := mul_ne_zero hρ₀ hαi
  set z : ℂ := β⁻¹
  have hβz : β * z = 1 := mul_inv_cancel₀ hβ
  rw [← coeff_curveFilteredSeries_eq_annihilator q α ε i (by omega)]
  have htel := sum_range_coeff_one_sub_mul (curveFilteredSeries q α ε i) hβz N
  rw [one_sub_mul_curveFilteredSeries,
    sum_range_coeff_curveCharacteristicNumerator q α ε z (by omega)] at htel
  have hres : (∏ j : Fin m, (1 - α j * z)) * (1 - ρ₀ * z) * (1 - (ρ₀ * q) * z) =
      curveEigenvalueResidue q α ε i := rfl
  rw [hres] at htel
  calc coeff N (curveFilteredSeries q α ε i)
      = (coeff N (curveFilteredSeries q α ε i) * z ^ N) * β ^ N := by
        rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hβ, one_pow, mul_one]
    _ = curveEigenvalueResidue q α ε i * β ^ N := by rw [← htel]

/-- **Exact characterization of mode vanishing.** For `q ≥ 1` and `αᵢ ≠ 0`, the isolated mode
amplitude `curveEigenvalueResidue q α ε i` vanishes if and only if `αᵢ` is shadowed by some
eigenvalue `αⱼ = q^{−ε} αᵢ` or `αᵢ ∈ {1, q}`. -/
theorem curveEigenvalueResidue_eq_zero_iff {q : ℕ} (hq : 1 ≤ q) (α : Fin m → ℂ) (ε : ℝ)
    {i : Fin m} (hαi : α i ≠ 0) :
    curveEigenvalueResidue q α ε i = 0 ↔
      (∃ j : Fin m, α j = (((q : ℝ) ^ (-ε) : ℝ) : ℂ) * α i) ∨ α i = 1 ∨ α i = q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set ρ₀ : ℂ := (((q : ℝ) ^ (-ε) : ℝ) : ℂ)
  have hρ₀ : ρ₀ ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hq0 (-ε)).ne'
  set β : ℂ := ρ₀ * α i
  have hβ : β ≠ 0 := mul_ne_zero hρ₀ hαi
  rw [curveEigenvalueResidue, mul_eq_zero, mul_eq_zero, prod_eq_zero_iff]
  have h1 : (∃ a ∈ (univ : Finset (Fin m)), 1 - α a * β⁻¹ = 0) ↔ ∃ j : Fin m, α j = β := by
    constructor
    · rintro ⟨j, _, hj⟩
      refine ⟨j, ?_⟩
      have := sub_eq_zero.mp hj
      calc α j = (α j * β⁻¹) * β := by rw [mul_assoc, inv_mul_cancel₀ hβ, mul_one]
        _ = 1 * β := by rw [← this]
        _ = β := one_mul β
    · rintro ⟨j, hj⟩
      refine ⟨j, mem_univ j, ?_⟩
      rw [hj, mul_inv_cancel₀ hβ, sub_self]
  have h2 : 1 - ρ₀ * β⁻¹ = 0 ↔ α i = 1 := by
    have he : ρ₀ * β⁻¹ = (α i)⁻¹ := by
      simp only [β, mul_inv_rev]
      rw [← mul_assoc, mul_comm ρ₀, mul_assoc, mul_inv_cancel₀ hρ₀, mul_one]
    rw [he, sub_eq_zero, eq_comm, inv_eq_one]
  have h3 : 1 - (ρ₀ * (q : ℂ)) * β⁻¹ = 0 ↔ α i = q := by
    have he : (ρ₀ * (q : ℂ)) * β⁻¹ = (q : ℂ) * (α i)⁻¹ := by
      simp only [β, mul_inv_rev]
      calc (ρ₀ * (q : ℂ)) * ((α i)⁻¹ * ρ₀⁻¹) = (q : ℂ) * (α i)⁻¹ * (ρ₀ * ρ₀⁻¹) := by ring
        _ = (q : ℂ) * (α i)⁻¹ := by rw [mul_inv_cancel₀ hρ₀, mul_one]
    rw [he, sub_eq_zero, eq_comm, mul_inv_eq_one₀ hαi, eq_comm]
  rw [h1, h2, h3, or_assoc]

theorem curveEigenvalueResidue_ne_zero {q : ℕ} (hq : 1 ≤ q) {α : Fin m → ℂ} {ε : ℝ} {i : Fin m}
    (hαi : α i ≠ 0) (h1 : α i ≠ 1) (hq' : α i ≠ q)
    (hsh : ∀ j, α j ≠ (((q : ℝ) ^ (-ε) : ℝ) : ℂ) * α i) :
    curveEigenvalueResidue q α ε i ≠ 0 := by
  rw [Ne, curveEigenvalueResidue_eq_zero_iff hq α ε hαi]
  push Not
  exact ⟨hsh, h1, hq'⟩

/-- **Shadowing annihilates the isolated mode.** When some eigenvalue `αⱼ` equals the damped
eigenvalue `q^{−ε} αᵢ` (`αᵢ ≠ 0`), the `i`-th annihilator-filtered centred source vanishes at
every degree `N ≥ 2m + 2`. -/
theorem coeff_curveAnnihilatorFilter_mul_eq_zero_of_shadow {q : ℕ} (hq : 1 ≤ q)
    (α : Fin m → ℂ) (ε : ℝ) {i j : Fin m} (hαi : α i ≠ 0)
    (hsh : α j = (((q : ℝ) ^ (-ε) : ℝ) : ℂ) * α i) {N : ℕ} (hN : 2 * m + 2 ≤ N) :
    coeff N (curveAnnihilatorFilter q α ε i * curveCentredSeries q α ε) = 0 := by
  rw [coeff_curveAnnihilatorFilter_mul_curveCentredSeries hq α ε hαi hN,
    (curveEigenvalueResidue_eq_zero_iff hq α ε hαi).mpr (Or.inl ⟨j, hsh⟩), zero_mul]

/-! ## Filter norm bounds and exponential blow-up below the zero width -/

/-- The norm amplification factor of `curveAnnihilatorFilter`. -/
def curveFilterConstant (q : ℕ) (α : Fin m → ℂ) (ε : ℝ) (i : Fin m) : ℝ :=
  (∏ j ∈ univ.erase i, (1 + ‖(((q : ℝ) ^ (-ε) : ℝ) : ℂ) * α j‖)) * 4 * (1 + q)

theorem curveFilterConstant_pos (q : ℕ) (α : Fin m → ℂ) (ε : ℝ) (i : Fin m) :
    0 < curveFilterConstant q α ε i := by
  rw [curveFilterConstant]
  refine mul_pos (mul_pos (prod_pos fun j _ => ?_) (by norm_num)) (by positivity)
  linarith [norm_nonneg ((((q : ℝ) ^ (-ε) : ℝ) : ℂ) * α j)]

theorem norm_coeff_one_sub_mul_le_of_le {G : PowerSeries ℂ} {K s : ℝ} (hK : 0 ≤ K) (hs : 1 ≤ s)
    {N : ℕ} (hG : ∀ n ≤ N, ‖coeff n G‖ ≤ K * s ^ n) (c : ℂ) {n : ℕ} (hn : n ≤ N) :
    ‖coeff n ((1 - C c * X) * G)‖ ≤ (1 + ‖c‖) * K * s ^ n := by
  have he : (1 - C c * X) * G = G - C c * (X * G) := by ring
  rw [he, map_sub, coeff_C_mul]
  rcases n with _ | n
  · rw [coeff_zero_X_mul, mul_zero, sub_zero, pow_zero, mul_one]
    have h0 := hG 0 hn
    rw [pow_zero, mul_one] at h0
    nlinarith [norm_nonneg c]
  · rw [coeff_succ_X_mul]
    have h1 := hG (n + 1) hn
    have h2 := hG n (by omega)
    have hsn : s ^ n ≤ s ^ (n + 1) := pow_le_pow_right₀ hs (by omega)
    calc ‖coeff (n + 1) G - c * coeff n G‖
        ≤ ‖coeff (n + 1) G‖ + ‖c‖ * ‖coeff n G‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ K * s ^ (n + 1) + ‖c‖ * (K * s ^ n) :=
          add_le_add h1 (mul_le_mul_of_nonneg_left h2 (norm_nonneg c))
      _ ≤ K * s ^ (n + 1) + ‖c‖ * (K * s ^ (n + 1)) := by gcongr
      _ = (1 + ‖c‖) * K * s ^ (n + 1) := by ring

theorem norm_coeff_prod_one_sub_mul_le_of_le {ι : Type*} (S : Finset ι) (f : ι → ℂ)
    {G : PowerSeries ℂ} {K s : ℝ} (hK : 0 ≤ K) (hs : 1 ≤ s) {N : ℕ}
    (hG : ∀ n ≤ N, ‖coeff n G‖ ≤ K * s ^ n) {n : ℕ} (hn : n ≤ N) :
    ‖coeff n ((∏ j ∈ S, (1 - C (f j) * X)) * G)‖ ≤
      (∏ j ∈ S, (1 + ‖f j‖)) * K * s ^ n := by
  classical
  induction S using Finset.induction_on generalizing G K n with
  | empty =>
      rw [prod_empty, prod_empty, one_mul, one_mul]
      exact hG n hn
  | insert a S ha ih =>
      rw [prod_insert ha, prod_insert ha, mul_assoc]
      have hS : ∀ k ≤ N, ‖coeff k ((∏ j ∈ S, (1 - C (f j) * X)) * G)‖ ≤
          (∏ j ∈ S, (1 + ‖f j‖)) * K * s ^ k :=
        fun k hk => ih hK hG hk
      have hK' : 0 ≤ (∏ j ∈ S, (1 + ‖f j‖)) * K :=
        mul_nonneg (prod_nonneg fun j _ => by linarith [norm_nonneg (f j)]) hK
      have hstep := norm_coeff_one_sub_mul_le_of_le hK' hs hS (f a) hn
      linarith

theorem norm_curveCentredPrefix_le_sqrt_energy {q : ℕ} (hq : 1 ≤ q) (α : Fin m → ℂ) (ε : ℝ)
    {N n : ℕ} (hn : n ≤ N) :
    ‖curveCentredPrefix q α ε n‖ ≤
      Real.sqrt (curveReceiverEnergy q α ε N) * Real.sqrt q ^ n := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set s := Real.sqrt q
  have hss : s * s = q := Real.mul_self_sqrt hq0.le
  have hE0 : 0 ≤ curveReceiverEnergy q α ε N :=
    sum_nonneg fun k _ => by positivity
  have hterm : ‖curveCentredPrefix q α ε n‖ ^ 2 / (q : ℝ) ^ n ≤ curveReceiverEnergy q α ε N :=
    single_le_sum (f := fun k => ‖curveCentredPrefix q α ε k‖ ^ 2 / (q : ℝ) ^ k)
      (fun k _ => by positivity) (mem_range.mpr (by omega))
  rw [div_le_iff₀ (by positivity)] at hterm
  have hsn : s ^ n * s ^ n = (q : ℝ) ^ n := by rw [← mul_pow, hss]
  have hsq : ‖curveCentredPrefix q α ε n‖ ^ 2 ≤
      (Real.sqrt (curveReceiverEnergy q α ε N) * s ^ n) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hE0, sq (s ^ n), hsn]; exact hterm
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

theorem norm_coeff_curveAnnihilatorFilter_mul_le {q : ℕ} (hq : 1 ≤ q) (α : Fin m → ℂ) (ε : ℝ)
    (i : Fin m) (N : ℕ) :
    ‖coeff N (curveAnnihilatorFilter q α ε i * curveCentredSeries q α ε)‖ ≤
      curveFilterConstant q α ε i * Real.sqrt (curveReceiverEnergy q α ε N) *
        Real.sqrt q ^ N := by
  set s := Real.sqrt q
  have hs : 1 ≤ s := Real.le_sqrt_of_sq_le (by norm_num; exact_mod_cast hq)
  set K := Real.sqrt (curveReceiverEnergy q α ε N)
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hA : ∀ n ≤ N, ‖coeff n (curveCentredSeries q α ε)‖ ≤ K * s ^ n := fun n hn => by
    rw [coeff_curveCentredSeries]
    exact norm_curveCentredPrefix_le_sqrt_energy hq α ε hn
  have h1 : ∀ n ≤ N, ‖coeff n ((1 - C (q : ℂ) * X) * curveCentredSeries q α ε)‖ ≤
      (1 + (q : ℝ)) * K * s ^ n := fun n hn => by
    simpa [Complex.norm_natCast] using norm_coeff_one_sub_mul_le_of_le hK hs hA (q : ℂ) hn
  have h2 : ∀ n ≤ N, ‖coeff n ((1 - C 1 * X) * ((1 - C (q : ℂ) * X) * curveCentredSeries q α ε))‖ ≤
      2 * ((1 + (q : ℝ)) * K) * s ^ n := fun n hn => by
    simpa [one_add_one_eq_two] using
      norm_coeff_one_sub_mul_le_of_le (by positivity) hs h1 1 hn
  have h3 : ∀ n ≤ N, ‖coeff n ((1 - C 1 * X) *
      ((1 - C 1 * X) * ((1 - C (q : ℂ) * X) * curveCentredSeries q α ε)))‖ ≤
      2 * (2 * ((1 + (q : ℝ)) * K)) * s ^ n := fun n hn => by
    simpa [one_add_one_eq_two] using
      norm_coeff_one_sub_mul_le_of_le (by positivity) hs h2 1 hn
  have h4 := norm_coeff_prod_one_sub_mul_le_of_le (univ.erase i)
    (fun j => (((q : ℝ) ^ (-ε) : ℝ) : ℂ) * α j) (by positivity) hs h3 le_rfl
  have he : ((∏ j ∈ univ.erase i, (1 - C ((((q : ℝ) ^ (-ε) : ℝ) : ℂ) * α j) * X)) *
      ((1 - C 1 * X) * ((1 - C 1 * X) * ((1 - C (q : ℂ) * X) * curveCentredSeries q α ε)))) =
      curveAnnihilatorFilter q α ε i * curveCentredSeries q α ε := by
    rw [curveAnnihilatorFilter]; ring
  rw [he] at h4
  refine h4.trans (le_of_eq ?_)
  rw [curveFilterConstant]
  ring

/-- **Quantitative lower bound on the curve receiver energy.** At every degree horizon
`D ≥ 2m + 2`, the cumulative receiver energy dominates the `i`-th geometric mode. -/
theorem curveEigenvalueResidue_sq_le_curveReceiverEnergy {q : ℕ} (hq : 1 ≤ q)
    (α : Fin m → ℂ) (ε : ℝ) {i : Fin m} (hαi : α i ≠ 0) {D : ℕ} (hD : 2 * m + 2 ≤ D) :
    (‖curveEigenvalueResidue q α ε i‖ / curveFilterConstant q α ε i) ^ 2 *
        ((‖α i‖ * (q : ℝ) ^ (-ε)) ^ 2 / q) ^ D ≤
      curveReceiverEnergy q α ε D := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hρ0 : 0 ≤ (q : ℝ) ^ (-ε) := Real.rpow_nonneg hq0.le _
  have hC : 0 < curveFilterConstant q α ε i := curveFilterConstant_pos q α ε i
  have hE0 : 0 ≤ curveReceiverEnergy q α ε D := sum_nonneg fun k _ => by positivity
  have hbd := norm_coeff_curveAnnihilatorFilter_mul_le hq α ε i D
  rw [coeff_curveAnnihilatorFilter_mul_curveCentredSeries hq α ε hαi hD, norm_mul, norm_pow,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0] at hbd
  have hsq0 := pow_le_pow_left₀ (by positivity) hbd 2
  have hsD : (Real.sqrt q ^ D) ^ 2 = (q : ℝ) ^ D := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hq0.le]
  have hsq : ‖curveEigenvalueResidue q α ε i‖ ^ 2 * ((‖α i‖ * (q : ℝ) ^ (-ε)) ^ 2) ^ D ≤
      curveFilterConstant q α ε i ^ 2 * curveReceiverEnergy q α ε D * (q : ℝ) ^ D := by
    calc ‖curveEigenvalueResidue q α ε i‖ ^ 2 * ((‖α i‖ * (q : ℝ) ^ (-ε)) ^ 2) ^ D
        = (‖curveEigenvalueResidue q α ε i‖ * ((q : ℝ) ^ (-ε) * ‖α i‖) ^ D) ^ 2 := by
          rw [mul_comm ‖α i‖, ← pow_mul, mul_comm 2 D, pow_mul]; ring
      _ ≤ (curveFilterConstant q α ε i * Real.sqrt (curveReceiverEnergy q α ε D) *
            Real.sqrt q ^ D) ^ 2 := hsq0
      _ = curveFilterConstant q α ε i ^ 2 * curveReceiverEnergy q α ε D * (q : ℝ) ^ D := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hE0, hsD]
  rw [div_pow, div_pow, div_mul_div_comm, div_le_iff₀ (by positivity)]
  calc ‖curveEigenvalueResidue q α ε i‖ ^ 2 * ((‖α i‖ * (q : ℝ) ^ (-ε)) ^ 2) ^ D
      ≤ curveFilterConstant q α ε i ^ 2 * curveReceiverEnergy q α ε D * (q : ℝ) ^ D := hsq
    _ = curveReceiverEnergy q α ε D * (curveFilterConstant q α ε i ^ 2 * (q : ℝ) ^ D) := by ring

/-- **Exponential growth of the curve receiver below the zero width.** For any `m` and any complex
eigenvalues `α : Fin m → ℂ`, if some `αᵢ` has `αᵢ ≠ 0, 1, q` and is not shadowed
(`∀ j, αⱼ ≠ q^{−ε} αᵢ`), there is `c > 0` with
`curveReceiverEnergy q α ε D ≥ c ((‖αᵢ‖ q^{−ε})² / q)^D` for all `D ≥ 2m + 2`. -/
theorem exists_pos_mul_pow_le_curveReceiverEnergy {q : ℕ} (hq : 1 ≤ q) {α : Fin m → ℂ} {ε : ℝ}
    {i : Fin m} (hαi : α i ≠ 0) (h1 : α i ≠ 1) (hq' : α i ≠ q)
    (hsh : ∀ j, α j ≠ (((q : ℝ) ^ (-ε) : ℝ) : ℂ) * α i) :
    ∃ c > 0, ∀ D, 2 * m + 2 ≤ D →
      c * ((‖α i‖ * (q : ℝ) ^ (-ε)) ^ 2 / q) ^ D ≤ curveReceiverEnergy q α ε D := by
  have hres := curveEigenvalueResidue_ne_zero hq hαi h1 hq' hsh
  have hC := curveFilterConstant_pos q α ε i
  refine ⟨(‖curveEigenvalueResidue q α ε i‖ / curveFilterConstant q α ε i) ^ 2,
    pow_pos (div_pos (norm_pos_iff.mpr hres) hC) 2, fun D hD => ?_⟩
  exact curveEigenvalueResidue_sq_le_curveReceiverEnergy hq α ε hαi hD

/-- **Below the zero width the curve receiver is not admitted (multi-eigenvalue theorem).**
For any number `m` of complex eigenvalues `α : Fin m → ℂ`, if some eigenvalue `αᵢ` satisfies
`√q q^ε < ‖αᵢ‖`, `αᵢ ≠ 1`, `αᵢ ≠ q`, and `∀ j, αⱼ ≠ q^{−ε} αᵢ`, the receiver energy is
unbounded. -/
theorem not_exists_curveReceiverEnergy_le {q : ℕ} (hq : 2 ≤ q) {α : Fin m → ℂ} {ε : ℝ}
    {i : Fin m} (hαi : Real.sqrt q * (q : ℝ) ^ ε < ‖α i‖) (h1 : α i ≠ 1) (hq' : α i ≠ q)
    (hsh : ∀ j, α j ≠ (((q : ℝ) ^ (-ε) : ℝ) : ℂ) * α i) :
    ¬ ∃ B : ℝ, ∀ D, curveReceiverEnergy q α ε D ≤ B := by
  rintro ⟨B, hB⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hs0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hρ0 : 0 < (q : ℝ) ^ (-ε) := Real.rpow_pos_of_pos hq0 (-ε)
  have hα0 : α i ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hαi
    linarith [mul_pos hs0 (Real.rpow_pos_of_pos hq0 ε)]
  obtain ⟨c, hc, hlow⟩ := exists_pos_mul_pow_le_curveReceiverEnergy (by omega) hα0 h1 hq' hsh
  have hgt : Real.sqrt q < ‖α i‖ * (q : ℝ) ^ (-ε) := by
    have h := mul_lt_mul_of_pos_right hαi hρ0
    rwa [mul_assoc, ← Real.rpow_add hq0, add_neg_cancel, Real.rpow_zero, mul_one] at h
  set r := (‖α i‖ * (q : ℝ) ^ (-ε)) ^ 2 / q
  have hr1 : 1 < r := by
    rw [one_lt_div hq0]
    calc (q : ℝ) = Real.sqrt q ^ 2 := (Real.sq_sqrt hq0.le).symm
      _ < (‖α i‖ * (q : ℝ) ^ (-ε)) ^ 2 := pow_lt_pow_left₀ hgt hs0.le two_ne_zero
  have hdiv : Tendsto (fun D : ℕ => c * r ^ D) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hr1).const_mul_atTop hc
  obtain ⟨D, hDB, hDm⟩ := ((hdiv.eventually (eventually_gt_atTop B)).and
    (eventually_ge_atTop (2 * m + 2))).exists
  linarith [hlow D hDm, hB D]

/-- **Equimodular failure below the zero width.** When all eigenvalues have modulus `λ√q` and
`q^ε < λ` (`ε > 0`), no eigenvalue can shadow another, so admission fails as soon as `m ≥ 1` and
some `αᵢ ≠ q`. -/
theorem not_exists_curveReceiverEnergy_le_of_equimodular {q : ℕ} (hq : 2 ≤ q) {α : Fin m → ℂ}
    {lam ε : ℝ} (hε : 0 < ε) (hlam : (q : ℝ) ^ ε < lam)
    (hα : ∀ j, ‖α j‖ = lam * Real.sqrt q) {i : Fin m} (hq' : α i ≠ q) :
    ¬ ∃ B : ℝ, ∀ D, curveReceiverEnergy q α ε D ≤ B := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hs1 : 1 < Real.sqrt q := Real.lt_sqrt_of_sq_lt (by norm_num; linarith)
  have hs0 : 0 < Real.sqrt q := by linarith
  have hqε1 : 1 < (q : ℝ) ^ ε := Real.one_lt_rpow hq1 hε
  have hρ1 : (q : ℝ) ^ (-ε) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  have hρ0 : 0 < (q : ℝ) ^ (-ε) := Real.rpow_pos_of_pos (by linarith) (-ε)
  have hαi_gt : Real.sqrt q * (q : ℝ) ^ ε < ‖α i‖ := by
    rw [hα i, mul_comm (Real.sqrt q)]
    exact mul_lt_mul_of_pos_right hlam hs0
  have h1 : α i ≠ 1 := by
    intro h
    have : ‖α i‖ = 1 := by rw [h, norm_one]
    nlinarith
  have hsh : ∀ j, α j ≠ (((q : ℝ) ^ (-ε) : ℝ) : ℂ) * α i := by
    intro j hj
    have hn := congr_arg norm hj
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0.le, hα j, hα i] at hn
    have hpos : 0 < lam * Real.sqrt q := by nlinarith
    nlinarith
  exact not_exists_curveReceiverEnergy_le hq hαi_gt h1 hq' hsh

/-- **Exact zero-width threshold for equimodular curve models.** For `m ≥ 1` eigenvalues of
modulus `λ√q` (`λ ≥ 1`, `αⱼ ≠ q`) and any `ε > 0` with `λ ≠ q^ε`, the curve receiver is admitted
at `ε` if and only if `λ < q^ε`. -/
theorem curveReceiverEnergy_admitted_iff_of_equimodular {q : ℕ} (hq : 2 ≤ q) {α : Fin m → ℂ}
    {lam ε : ℝ} (hlam : 1 ≤ lam) (hε : 0 < ε) (hne : lam ≠ (q : ℝ) ^ ε)
    (hα : ∀ j, ‖α j‖ = lam * Real.sqrt q) (i : Fin m) (hq' : α i ≠ q) :
    (∃ B : ℝ, ∀ D, curveReceiverEnergy q α ε D ≤ B) ↔ lam < (q : ℝ) ^ ε := by
  constructor
  · intro hB
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hlt
    · exact False.elim (not_exists_curveReceiverEnergy_le_of_equimodular hq hε hgt hα hq' hB)
  · intro hlt
    exact exists_curveReceiverEnergy_le hq hlam (fun j => (hα j).le) hlt

/-- **No eigenvalue in the shadow strip `(√q, √q q^ε]` implies blow-up below the zero width.**
If some eigenvalue exceeds `√q q^ε` (`ε > 0`), no eigenvalue lies in `(√q, √q q^ε]`, and
`∀ j, αⱼ ≠ q`, the curve receiver is not admitted at `ε`: the minimal supercritical eigenvalue
cannot be shadowed. -/
theorem not_exists_curveReceiverEnergy_le_of_no_strip {q : ℕ} (hq : 2 ≤ q) {α : Fin m → ℂ}
    {ε : ℝ} (hε : 0 < ε) (hex : ∃ i, Real.sqrt q * (q : ℝ) ^ ε < ‖α i‖)
    (hstrip : ∀ j, Real.sqrt q < ‖α j‖ → Real.sqrt q * (q : ℝ) ^ ε < ‖α j‖)
    (hq' : ∀ j, α j ≠ q) :
    ¬ ∃ B : ℝ, ∀ D, curveReceiverEnergy q α ε D ≤ B := by
  classical
  obtain ⟨i₁, hi₁⟩ := hex
  set U := univ.filter (fun j : Fin m => Real.sqrt q * (q : ℝ) ^ ε < ‖α j‖)
  have hne : U.Nonempty := ⟨i₁, mem_filter.mpr ⟨mem_univ i₁, hi₁⟩⟩
  obtain ⟨i₀, hi₀U, hmin⟩ := exists_min_image U (fun j => ‖α j‖) hne
  have hi₀ : Real.sqrt q * (q : ℝ) ^ ε < ‖α i₀‖ := (mem_filter.mp hi₀U).2
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hs1 : 1 < Real.sqrt q := Real.lt_sqrt_of_sq_lt (by norm_num; linarith)
  have hqε1 : 1 < (q : ℝ) ^ ε := Real.one_lt_rpow hq1 hε
  have hρ0 : 0 < (q : ℝ) ^ (-ε) := Real.rpow_pos_of_pos (by linarith) (-ε)
  have hρ1 : (q : ℝ) ^ (-ε) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  have h1 : α i₀ ≠ 1 := by
    intro h
    have : ‖α i₀‖ = 1 := by rw [h, norm_one]
    nlinarith
  have hsh : ∀ j, α j ≠ (((q : ℝ) ^ (-ε) : ℝ) : ℂ) * α i₀ := by
    intro j hj
    have hn := congr_arg norm hj
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0.le] at hn
    have hj_gt : Real.sqrt q < ‖α j‖ := by
      have hmul := mul_lt_mul_of_pos_right hi₀ hρ0
      rw [mul_assoc, ← Real.rpow_add (by linarith), add_neg_cancel, Real.rpow_zero, mul_one,
        mul_comm] at hmul
      linarith
    have hjU : j ∈ U := mem_filter.mpr ⟨mem_univ j, hstrip j hj_gt⟩
    have hle := hmin j hjU
    nlinarith
  exact not_exists_curveReceiverEnergy_le hq hi₀ h1 (hq' i₀) hsh

/-- **The Weil bound is equivalent to cofinal admission of the curve receiver.**
For any `q ≥ 2` and any tuple of complex eigenvalues `α : Fin m → ℂ` with `∀ i, α i ≠ q`,
every eigenvalue satisfies the Weil bound `‖α i‖ ≤ √q` if and only if `curveReceiverEnergy q α ε`
is admitted at arbitrarily small positive dampings `ε ↓ 0`. -/
theorem weil_iff_cofinal_curveReceiverEnergy {q : ℕ} (hq : 2 ≤ q) {α : Fin m → ℂ}
    (hq' : ∀ i, α i ≠ q) :
    (∀ i, ‖α i‖ ≤ Real.sqrt q) ↔
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
        ∃ B : ℝ, ∀ D, curveReceiverEnergy q α ε D ≤ B := by
  constructor
  · intro hweil δ hδ
    refine ⟨δ / 2, by linarith, by linarith, ?_⟩
    exact exists_curveReceiverEnergy_le_of_weil hq hweil (by linarith)
  · intro hcof
    classical
    by_contra hnot
    push Not at hnot
    obtain ⟨i₁, hi₁⟩ := hnot
    set U := univ.filter (fun j : Fin m => Real.sqrt q < ‖α j‖)
    have hne : U.Nonempty := ⟨i₁, mem_filter.mpr ⟨mem_univ i₁, hi₁⟩⟩
    obtain ⟨i₀, hi₀U, hmin⟩ := exists_min_image U (fun j => ‖α j‖) hne
    have hi₀ : Real.sqrt q < ‖α i₀‖ := (mem_filter.mp hi₀U).2
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hcont : Continuous (fun ε : ℝ => Real.sqrt q * Real.exp (Real.log q * ε)) :=
      continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have hlim : Tendsto (fun ε : ℝ => Real.sqrt q * (q : ℝ) ^ ε) (𝓝 0) (𝓝 (Real.sqrt q)) := by
      have h0 : (fun ε : ℝ => Real.sqrt q * (q : ℝ) ^ ε) =
          fun ε : ℝ => Real.sqrt q * Real.exp (Real.log q * ε) := by
        ext ε; rw [Real.rpow_def_of_pos hq0]
      rw [h0]
      simpa using hcont.tendsto 0
    obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.mp
      (hlim.eventually (eventually_lt_nhds hi₀))
    obtain ⟨ε, hε0, hεδ, hB⟩ := hcof δ hδ0
    have hε_lt : Real.sqrt q * (q : ℝ) ^ ε < ‖α i₀‖ :=
      hδ (by rw [Real.dist_eq, sub_zero, abs_of_pos hε0]; exact hεδ)
    have hstrip : ∀ j, Real.sqrt q < ‖α j‖ → Real.sqrt q * (q : ℝ) ^ ε < ‖α j‖ :=
      fun j hj => hε_lt.trans_le (hmin j (mem_filter.mpr ⟨mem_univ j, hj⟩))
    exact not_exists_curveReceiverEnergy_le_of_no_strip hq hε0 ⟨i₀, hε_lt⟩ hstrip hq' hB

end GaloisForLFunctions.ArithmeticCompensationTheory


