import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheAnomalyCostsHalfALogarithm

/-!
# The torsion counterterm is at most two logarithms

Normalize the charges by the orbit size, `z_n = √φ(n) y_n` (`normalizedCharge`), so that the self-mass
is `|z|²`. Off the diagonal the torsion pairing then has the kernel `K(m, mt) = Λ(t) √(φ(m)/φ(mt))`,
and Weil's kernel is `P(m, mt) = Λ(t)/√t`. Since `φ(m)φ(t) ≤ φ(mt) ≤ t φ(m)`,

  `P(m, mt) ≤ K(m, mt) ≤ P(m, mt) + e(t)`,   `e(t) = Λ(t)(φ(t)^{−1/2} − t^{−1/2})` (`heckeExcess`).

* **The excess is summable** (`heckeExcess_prime_pow_le`, `sum_heckeExcess_le`): `e` lives on prime
  powers, `e(p^k) ≤ (log p/(p − 1)) p^{−k/2}`, so one prime contributes at most `32 p^{−5/4}` and
  `Σ_{t ≤ N} e(t) ≤ C_e` uniformly in `N`.
* **The torsion pairing is Weil's form up to a bounded operator** (`heckePair_le`, `offDiag_le`):
  `y_m y_n I(m, n) ≤ z_m z_n P(m, n) + ½(z_m² + z_n²)(e(m, n) + e(n, m))` off the diagonal.
* **The torsion counterterm is at most `2 log N + C`** (`renormalizesAt_two_log`): the diagonal
  `c(n) ≤ log n` costs `log N`, Weil's form the covariant `log N + log 4 + 4`, the excess `2C_e`.
* **The window** (`torsionCounterterm_window`, `anomaly_cost_window`): the minimal torsion
  counterterm lies in `[(3/2) log N − C₁, 2 log N + C₂]`; the anomaly costs between `½ log N − C` and
  `log N + C` over the covariant counterterm.

AES's Schur test with weights `1/n` pays the diagonal and the two directions of the Hecke tower
separately (`4 log N`). Comparing with Weil's kernel instead pays the tower once, at the covariant
rate. The continuum model's constant `e/(e − 1)` lies inside the window.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

/-! ### The Hecke excess -/

/-- The **Hecke excess** `e(t) = Λ(t)(φ(t)^{−1/2} − t^{−1/2})`: how far the normalized torsion kernel
can exceed Weil's kernel on a Hecke step of degree `t`. -/
def heckeExcess (t : ℕ) : ℝ := Λ t * (1 / Real.sqrt (Nat.totient t) - 1 / Real.sqrt t)

theorem heckeExcess_nonneg (t : ℕ) : 0 ≤ heckeExcess t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [heckeExcess]
  have hφ : (0 : ℝ) < Nat.totient t := by exact_mod_cast Nat.totient_pos.mpr ht
  refine mul_nonneg vonMangoldt_nonneg (sub_nonneg.mpr ?_)
  exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hφ)
    (Real.sqrt_le_sqrt (by exact_mod_cast Nat.totient_le t))

theorem heckeExcess_one : heckeExcess 1 = 0 := by simp [heckeExcess]

/-- `1/√F − 1/√T ≤ (T − F)/(√T F)` for `0 < F ≤ T`. -/
theorem inv_sqrt_sub_inv_sqrt_le {F T : ℝ} (hF : 0 < F) (hFT : F ≤ T) :
    1 / Real.sqrt F - 1 / Real.sqrt T ≤ (T - F) / (Real.sqrt T * F) := by
  have hT : 0 < T := hF.trans_le hFT
  obtain ⟨a, ha0, rfl⟩ : ∃ a, 0 < a ∧ T = a ^ 2 :=
    ⟨Real.sqrt T, Real.sqrt_pos.mpr hT, (Real.sq_sqrt hT.le).symm⟩
  obtain ⟨b, hb0, rfl⟩ : ∃ b, 0 < b ∧ F = b ^ 2 :=
    ⟨Real.sqrt F, Real.sqrt_pos.mpr hF, (Real.sq_sqrt hF.le).symm⟩
  have hba : b ≤ a := by nlinarith
  rw [Real.sqrt_sq ha0.le, Real.sqrt_sq hb0.le, div_sub_div _ _ hb0.ne' ha0.ne',
    div_le_div_iff₀ (by positivity) (by positivity)]
  -- the difference is `a² b (a − b) ≥ 0`
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hba) ha0.le) ha0.le) hb0.le]

/-- **The excess on prime powers**: `e(p^k) ≤ (log p/(p − 1))/√(p^k)`. -/
theorem heckeExcess_prime_pow_le {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    heckeExcess (p ^ k) ≤ Real.log p / ((p : ℝ) - 1) / Real.sqrt ((p ^ k : ℕ) : ℝ) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
  have hΛ : Λ (p ^ (j + 1)) = Real.log p := by
    rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]
  have hF : (Nat.totient (p ^ (j + 1)) : ℝ) = (p : ℝ) ^ j * ((p : ℝ) - 1) := by
    rw [Nat.totient_prime_pow_succ hp, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_le,
      Nat.cast_one]
  have hT : ((p ^ (j + 1) : ℕ) : ℝ) = (p : ℝ) ^ j * p := by push_cast; ring
  have hpj : (0 : ℝ) < (p : ℝ) ^ j := by positivity
  have hFpos : (0 : ℝ) < (Nat.totient (p ^ (j + 1)) : ℝ) := by
    rw [hF]; exact mul_pos hpj (by linarith)
  have hFT : (Nat.totient (p ^ (j + 1)) : ℝ) ≤ ((p ^ (j + 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.totient_le _
  have hs : Real.sqrt ((p ^ (j + 1) : ℕ) : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (hFpos.trans_le hFT)).ne'
  have h := inv_sqrt_sub_inv_sqrt_le hFpos hFT
  rw [heckeExcess, hΛ]
  calc Real.log p * (1 / Real.sqrt (Nat.totient (p ^ (j + 1)) : ℝ) -
        1 / Real.sqrt ((p ^ (j + 1) : ℕ) : ℝ))
      ≤ Real.log p * ((((p ^ (j + 1) : ℕ) : ℝ) - Nat.totient (p ^ (j + 1))) /
          (Real.sqrt ((p ^ (j + 1) : ℕ) : ℝ) * Nat.totient (p ^ (j + 1)))) :=
        mul_le_mul_of_nonneg_left h (Real.log_nonneg hp1.le)
    _ = Real.log p / ((p : ℝ) - 1) / Real.sqrt ((p ^ (j + 1) : ℕ) : ℝ) := by
        rw [hF]
        nth_rewrite 1 [hT]
        field_simp
        ring

/-- **One prime pays a constant**: `Σ_{1 ≤ k ≤ K} e(p^k) ≤ (log p/(p − 1))/(√p − 1)`. -/
theorem sum_heckeExcess_prime_pow_le {p : ℕ} (hp : p.Prime) (K : ℕ) :
    ∑ k ∈ Icc 1 K, heckeExcess (p ^ k) ≤ Real.log p / ((p : ℝ) - 1) / (Real.sqrt p - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hs1 : 1 < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one hp1
  have hc : 0 ≤ Real.log p / ((p : ℝ) - 1) :=
    div_nonneg (Real.log_nonneg hp1.le) (by linarith)
  set r := 1 / Real.sqrt p with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one (by linarith)]; exact hs1
  -- `√(p^k) = (√p)^k`
  have hsqrt : ∀ k : ℕ, Real.sqrt ((p ^ k : ℕ) : ℝ) = Real.sqrt p ^ k := by
    intro k
    have h : ((p ^ k : ℕ) : ℝ) = (Real.sqrt p ^ k) ^ 2 := by
      rw [← pow_mul, show k * 2 = 2 * k by ring, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _),
        Nat.cast_pow]
    rw [h, Real.sqrt_sq (by positivity)]
  calc ∑ k ∈ Icc 1 K, heckeExcess (p ^ k)
      ≤ ∑ k ∈ Icc 1 K, Real.log p / ((p : ℝ) - 1) * r ^ k := by
        refine sum_le_sum fun k hk => (heckeExcess_prime_pow_le hp (mem_Icc.mp hk).1).trans ?_
        rw [hsqrt, hr, one_div_pow, mul_one_div]
    _ = Real.log p / ((p : ℝ) - 1) * ∑ k ∈ Ico 1 (K + 1), r ^ k := by
        rw [← mul_sum, Finset.Ico_add_one_right_eq_Icc]
    _ ≤ Real.log p / ((p : ℝ) - 1) * (r ^ 1 / (1 - r)) :=
        mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hr0 hr1) hc
    _ = Real.log p / ((p : ℝ) - 1) / (Real.sqrt p - 1) := by
        have : Real.sqrt p - 1 ≠ 0 := by linarith
        have : Real.sqrt p ≠ 0 := by linarith
        rw [hr]
        field_simp

/-- `(log p/(p − 1))/(√p − 1) ≤ 32 p^{−5/4}` for `p ≥ 2`. -/
theorem log_div_sqrt_sub_le {p : ℕ} (hp : 2 ≤ p) :
    Real.log p / ((p : ℝ) - 1) / (Real.sqrt p - 1) ≤ 32 * ((p : ℝ) ^ ((5 : ℝ) / 4))⁻¹ := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  -- write everything in `s = p^{1/4}`
  set s := (p : ℝ) ^ ((1 : ℝ) / 4) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hp0 _
  have hs4 : s ^ 4 = p := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num
  have hs5 : (p : ℝ) ^ ((5 : ℝ) / 4) = s ^ 5 := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num
  have hsq : Real.sqrt p = s ^ 2 := by
    rw [← hs4, show s ^ 4 = (s ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hlog : Real.log p ≤ 4 * s := by
    have h := Real.log_le_rpow_div hp0.le (show (0 : ℝ) < 1 / 4 by norm_num)
    rw [← hs] at h
    linarith [show s / (1 / 4) = 4 * s by ring]
  have hD1 : s ^ 4 / 2 ≤ (p : ℝ) - 1 := by rw [hs4]; linarith
  have hs2 : 4 / 3 ≤ s ^ 2 := by nlinarith
  have hD2 : s ^ 2 / 4 ≤ s ^ 2 - 1 := by linarith
  rw [hsq, hs5]
  calc Real.log p / ((p : ℝ) - 1) / (s ^ 2 - 1)
      ≤ 4 * s / (s ^ 4 / 2) / (s ^ 2 / 4) :=
        div_le_div₀ (by positivity) (div_le_div₀ (by positivity) hlog (by positivity) hD1)
          (by positivity) hD2
    _ = 32 * (s ^ 5)⁻¹ := by field_simp; ring

/-- The constant `C_e = Σ_n 32 n^{−5/4}` bounding the total Hecke excess. -/
def excessConstant : ℝ := ∑' n : ℕ, 32 * ((n : ℝ) ^ ((5 : ℝ) / 4))⁻¹

theorem summable_excess : Summable fun n : ℕ => 32 * ((n : ℝ) ^ ((5 : ℝ) / 4))⁻¹ :=
  (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 32

theorem excessConstant_nonneg : 0 ≤ excessConstant :=
  tsum_nonneg fun n => by positivity

/-- **The Hecke excess is summable**: `Σ_{t ≤ N} e(t) ≤ C_e` for every `N`. -/
theorem sum_heckeExcess_le (N : ℕ) : ∑ t ∈ Icc 1 N, heckeExcess t ≤ excessConstant := by
  classical
  set P := (Icc 1 N).filter Nat.Prime
  -- the excess lives on prime powers
  have h1 : ∑ t ∈ Icc 1 N, heckeExcess t =
      ∑ t ∈ (Icc 1 N).filter IsPrimePow, heckeExcess t := by
    refine (sum_filter_of_ne fun t _ ht => ?_).symm
    rw [← vonMangoldt_ne_zero_iff]
    intro h
    exact ht (by simp [heckeExcess, h])
  -- prime powers `≤ N` are the images `p^k` of primes `p ≤ N` and exponents `1 ≤ k ≤ N`
  have hsub : (Icc 1 N).filter IsPrimePow ⊆ (P ×ˢ Icc 1 N).image (fun q => q.1 ^ q.2) := by
    intro t ht
    obtain ⟨htN, hpp⟩ := mem_filter.mp ht
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    have hle := (mem_Icc.mp htN).2
    refine mem_image.mpr ⟨(p, k), mem_product.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.one_le,
      (Nat.le_self_pow hk.ne' p).trans hle⟩, hp⟩, mem_Icc.mpr ⟨hk, ?_⟩⟩, rfl⟩
    exact (Nat.lt_pow_self hp.one_lt).le.trans hle
  have hinj : ∀ q ∈ P ×ˢ Icc 1 N, ∀ q' ∈ P ×ˢ Icc 1 N, q.1 ^ q.2 = q'.1 ^ q'.2 → q = q' := by
    rintro ⟨p, k⟩ hq ⟨p', k'⟩ hq' h
    simp only [mem_product, mem_filter, mem_Icc, P] at hq hq'
    have hp := hq.1.2
    have hp' := hq'.1.2
    have hpp' : p = p' := by
      have hdvd : p ∣ p' ^ k' := h ▸ dvd_pow_self p (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hp hp').mp (hp.dvd_of_dvd_pow hdvd)
    subst hpp'
    exact Prod.ext rfl (Nat.pow_right_injective hp.two_le h)
  rw [h1]
  calc ∑ t ∈ (Icc 1 N).filter IsPrimePow, heckeExcess t
      ≤ ∑ t ∈ (P ×ˢ Icc 1 N).image (fun q => q.1 ^ q.2), heckeExcess t :=
        sum_le_sum_of_subset_of_nonneg hsub fun t _ _ => heckeExcess_nonneg t
    _ = ∑ p ∈ P, ∑ k ∈ Icc 1 N, heckeExcess (p ^ k) := by
        rw [sum_image hinj, sum_product]
    _ ≤ ∑ p ∈ P, 32 * ((p : ℝ) ^ ((5 : ℝ) / 4))⁻¹ := sum_le_sum fun p hp =>
        (sum_heckeExcess_prime_pow_le (mem_filter.mp hp).2 N).trans
          (log_div_sqrt_sub_le (mem_filter.mp hp).2.two_le)
    _ ≤ excessConstant := summable_excess.sum_le_tsum _ fun n _ => by positivity

/-! ### The torsion kernel against Weil's kernel -/

/-- The charges normalized by the orbit size, `z_n = √φ(n) y_n`: the self-mass is `|z|²`. -/
def normalizedCharge (y : ℕ → ℝ) (n : ℕ) : ℝ := Real.sqrt (Nat.totient n) * y n

theorem normalizedCharge_sq (y : ℕ → ℝ) (n : ℕ) :
    normalizedCharge y n ^ 2 = (Nat.totient n : ℝ) * y n ^ 2 := by
  rw [normalizedCharge, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

theorem selfMass_eq (N : ℕ) (y : ℕ → ℝ) :
    selfMass N y = ∑ n ∈ Icc 1 N, normalizedCharge y n ^ 2 :=
  sum_congr rfl fun n _ => (normalizedCharge_sq y n).symm

/-- `φ(m)/√(φ(m)φ(mt)) ≤ 1/√φ(t)`, by super-multiplicativity `φ(m)φ(t) ≤ φ(mt)`. -/
theorem normalizedIntersection_le {m t : ℕ} (hm : 0 < m) (ht : 0 < t) :
    (Nat.totient m : ℝ) / Real.sqrt ((Nat.totient m : ℝ) * Nat.totient (m * t)) ≤
      1 / Real.sqrt (Nat.totient t) := by
  have hφm : (0 : ℝ) < Nat.totient m := by exact_mod_cast Nat.totient_pos.mpr hm
  have hφt : (0 : ℝ) < Nat.totient t := by exact_mod_cast Nat.totient_pos.mpr ht
  have hφmt : (0 : ℝ) < Nat.totient (m * t) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos hm ht)
  rw [div_sqrt_mul_eq hφm hφmt, ← Real.sqrt_one, ← Real.sqrt_div' _ hφt.le]
  refine Real.sqrt_le_sqrt ?_
  rw [div_le_div_iff₀ hφmt hφt, one_mul]
  exact_mod_cast Nat.totient_super_multiplicative m t

/-- **On a Hecke pair the torsion kernel is Weil's kernel plus at most the excess**:
`y_m y_{mt} I(m, mt) ≤ z_m z_{mt} Λ(t)/√t + ½(z_m² + z_{mt}²) e(t)`. -/
theorem heckePair_le (y : ℕ → ℝ) {m t : ℕ} (hm : 0 < m) (ht : 1 < t) :
    y m * y (m * t) * orbitIntersection m (m * t) ≤
      normalizedCharge y m * normalizedCharge y (m * t) * (Λ t / Real.sqrt t) +
        (normalizedCharge y m ^ 2 + normalizedCharge y (m * t) ^ 2) / 2 * heckeExcess t := by
  have ht0 : 0 < t := by omega
  have hφm : (0 : ℝ) < Nat.totient m := by exact_mod_cast Nat.totient_pos.mpr hm
  have hφn : (0 : ℝ) < Nat.totient (m * t) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos hm ht0)
  have hlo := inv_sqrt_le_normalizedIntersection hm ht0
  have hhi := normalizedIntersection_le hm ht0
  -- `y_m y_{mt} φ(m) = z_m z_{mt} · φ(m)/√(φ(m)φ(mt))`
  have hid : y m * y (m * t) * (Nat.totient m : ℝ) =
      normalizedCharge y m * normalizedCharge y (m * t) *
        ((Nat.totient m : ℝ) / Real.sqrt ((Nat.totient m : ℝ) * Nat.totient (m * t))) := by
    have h1 : Real.sqrt (Nat.totient m : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hφm).ne'
    have h2 : Real.sqrt (Nat.totient (m * t) : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hφn).ne'
    rw [normalizedCharge, normalizedCharge, Real.sqrt_mul hφm.le]
    field_simp
  set A := (Nat.totient m : ℝ) / Real.sqrt ((Nat.totient m : ℝ) * Nat.totient (m * t))
  set a := normalizedCharge y m
  set b := normalizedCharge y (m * t)
  have hΛ : 0 ≤ Λ t := vonMangoldt_nonneg
  have hc0 : 0 ≤ Λ t * (A - 1 / Real.sqrt t) := mul_nonneg hΛ (by linarith)
  have hc1 : Λ t * (A - 1 / Real.sqrt t) ≤ heckeExcess t :=
    mul_le_mul_of_nonneg_left (by linarith) hΛ
  have hab : a * b * (Λ t * (A - 1 / Real.sqrt t)) ≤
      (a ^ 2 + b ^ 2) / 2 * (Λ t * (A - 1 / Real.sqrt t)) := by
    nlinarith [mul_nonneg (sq_nonneg (a - b)) hc0]
  have hab2 : (a ^ 2 + b ^ 2) / 2 * (Λ t * (A - 1 / Real.sqrt t)) ≤
      (a ^ 2 + b ^ 2) / 2 * heckeExcess t :=
    mul_le_mul_of_nonneg_left hc1 (by positivity)
  rw [orbitIntersection_hecke hm ht]
  calc y m * y (m * t) * ((Nat.totient m : ℝ) * Λ t)
      = a * b * (Λ t / Real.sqrt t) + a * b * (Λ t * (A - 1 / Real.sqrt t)) := by
        rw [← mul_assoc, hid]; ring
    _ ≤ _ := by linarith

/-- The excess of the Hecke step from `m` up to `n`: `e(n/m)` when `m ∣ n`, else `0`. -/
def upExcess (m n : ℕ) : ℝ := if m ∣ n then heckeExcess (n / m) else 0

theorem upExcess_self {m : ℕ} (hm : 0 < m) : upExcess m m = 0 := by
  rw [upExcess, if_pos dvd_rfl, Nat.div_self hm, heckeExcess_one]

/-- **Off the diagonal the torsion pairing is Weil's form plus the excess**:
`y_m y_n I(m, n) ≤ z_m z_n P(m, n) + ½(z_m² + z_n²)(e(m, n) + e(n, m))`. -/
theorem offDiag_le (y : ℕ → ℝ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    y m * y n * orbitIntersection m n ≤
      normalizedCharge y m * normalizedCharge y n * weilPrimeKernel m n +
        (normalizedCharge y m ^ 2 + normalizedCharge y n ^ 2) / 2 *
          (upExcess m n + upExcess n m) := by
  -- the case `m ∣ n`
  have key : ∀ {a b : ℕ}, 0 < a → 0 < b → a ≠ b → a ∣ b →
      y a * y b * orbitIntersection a b ≤
        normalizedCharge y a * normalizedCharge y b * weilPrimeKernel a b +
          (normalizedCharge y a ^ 2 + normalizedCharge y b ^ 2) / 2 *
            (upExcess a b + upExcess b a) := by
    intro a b ha hb hab hdvd
    obtain ⟨t, rfl⟩ := hdvd
    have ht0 : t ≠ 0 := fun h => by simp [h] at hb
    have ht1 : t ≠ 1 := fun h => hab (by simp [h])
    have ht : 1 < t := by omega
    have hba : ¬ a * t ∣ a := fun h => hab (Nat.dvd_antisymm (dvd_mul_right a t) h)
    have hP : weilPrimeKernel a (a * t) = Λ t / Real.sqrt t := by
      rw [weilPrimeKernel, if_pos ⟨dvd_mul_right a t, hab⟩, Nat.mul_div_cancel_left t ha]
    have hU1 : upExcess a (a * t) = heckeExcess t := by
      rw [upExcess, if_pos (dvd_mul_right a t), Nat.mul_div_cancel_left t ha]
    have hU2 : upExcess (a * t) a = 0 := by rw [upExcess, if_neg hba]
    rw [hP, hU1, hU2, add_zero]
    exact heckePair_le y ha ht
  by_cases h1 : m ∣ n
  · exact key hm hn hmn h1
  · by_cases h2 : n ∣ m
    · have h := key hn hm (Ne.symm hmn) h2
      rw [ArithmeticElectrostatics.orbitIntersection_comm n m, weilPrimeKernel_comm n m] at h
      linarith
    · simp [orbitIntersection_eq hm hn hmn, weilPrimeKernel, upExcess, h1, h2]

/-- **Schur test for the excess with constant weights**: each row of `e(m, n) + e(n, m)` is at
most `2C_e`. -/
theorem sum_excess_le (N : ℕ) (z : ℕ → ℝ) :
    ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (z m ^ 2 + z n ^ 2) / 2 * (upExcess m n + upExcess n m) ≤
      2 * excessConstant * ∑ n ∈ Icc 1 N, z n ^ 2 := by
  set S := Icc 1 N
  -- the rows: up the tower `Σ_{t ≤ N/m} e(t)`, down the tower `Σ_{d ∣ m} e(d)`
  have hup : ∀ m ∈ S, ∑ n ∈ S, upExcess m n ≤ excessConstant := by
    intro m hm
    have hm0 := (mem_Icc.mp hm).1
    have h : ∑ n ∈ S, upExcess m n = ∑ t ∈ Icc 1 (N / m), heckeExcess t := by
      simp only [S, upExcess]
      rw [← sum_filter, filter_dvd_Icc_eq_image hm0,
        sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hm0 h]
      exact sum_congr rfl fun t _ => by rw [Nat.mul_div_cancel_left t hm0]
    rw [h]
    exact (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl (Nat.div_le_self N m))
      fun t _ _ => heckeExcess_nonneg t).trans (sum_heckeExcess_le N)
  have hdown : ∀ m ∈ S, ∑ n ∈ S, upExcess n m ≤ excessConstant := by
    intro m hm
    have hm0 := (mem_Icc.mp hm).1
    have hmN := (mem_Icc.mp hm).2
    have h : ∑ n ∈ S, upExcess n m = ∑ d ∈ m.divisors, heckeExcess d := by
      simp only [S, upExcess]
      rw [← sum_filter, filter_Icc_dvd_eq_divisors hm0 hmN, Nat.sum_div_divisors]
    rw [h]
    refine (sum_le_sum_of_subset_of_nonneg (fun d hd => ?_)
      fun t _ _ => heckeExcess_nonneg t).trans (sum_heckeExcess_le N)
    have hd' := Nat.mem_divisors.mp hd
    exact mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hd'.1 hm0, (Nat.le_of_dvd hm0 hd'.1).trans hmN⟩
  -- symmetrize: `Σ Σ z_n² s(m, n) = Σ Σ z_m² s(m, n)` for the symmetric `s`
  have hsym : ∑ m ∈ S, ∑ n ∈ S, z n ^ 2 * (upExcess m n + upExcess n m) =
      ∑ m ∈ S, ∑ n ∈ S, z m ^ 2 * (upExcess m n + upExcess n m) := by
    rw [sum_comm]
    exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by rw [add_comm (upExcess n m)]
  have hsplit : ∑ m ∈ S, ∑ n ∈ S, (z m ^ 2 + z n ^ 2) / 2 * (upExcess m n + upExcess n m) =
      (∑ m ∈ S, ∑ n ∈ S, z m ^ 2 * (upExcess m n + upExcess n m) +
        ∑ m ∈ S, ∑ n ∈ S, z n ^ 2 * (upExcess m n + upExcess n m)) / 2 := by
    rw [← sum_add_distrib, sum_div]
    refine sum_congr rfl fun m _ => ?_
    rw [← sum_add_distrib, sum_div]
    exact sum_congr rfl fun n _ => by ring
  rw [hsplit, hsym, add_self_div_two, mul_sum]
  refine sum_le_sum fun m hm => ?_
  rw [← mul_sum, mul_comm (2 * excessConstant)]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  rw [sum_add_distrib]
  linarith [hup m hm, hdown m hm]

/-! ### The torsion counterterm -/

/-- **The torsion counterterm is at most `2 log N + C`**: `κ = 2 log N + log 4 + 4 + 2C_e`
renormalizes the torsion pairing on the orders `≤ N`. -/
theorem renormalizesAt_two_log (N : ℕ) :
    RenormalizesAt N (2 * Real.log N + (Real.log 4 + 4 + 2 * excessConstant)) := by
  intro y
  set z := normalizedCharge y
  set S := Icc 1 N
  -- the pointwise bound: diagonal, Weil's kernel, excess
  have hpt : ∀ m ∈ S, ∀ n ∈ S, y m * y n * orbitIntersection m n ≤
      (if m = n then Real.log N * z m ^ 2 else 0) + z m * z n * weilPrimeKernel m n +
        (z m ^ 2 + z n ^ 2) / 2 * (upExcess m n + upExcess n m) := by
    intro m hm n hn
    have hm0 := (mem_Icc.mp hm).1
    by_cases hmn : m = n
    · subst hmn
      simp only [↓reduceIte, weilPrimeKernel_self, upExcess_self hm0, mul_zero, add_zero]
      rw [normalizedCharge_sq]
      have hlog : Real.log m ≤ Real.log N := Real.log_le_log (by exact_mod_cast hm0)
        (by exact_mod_cast (mem_Icc.mp hm).2)
      have hI := (orbitIntersection_self_le hm0).trans
        (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (Nat.totient m)))
      nlinarith [mul_le_mul_of_nonneg_left hI (sq_nonneg (y m))]
    · rw [if_neg hmn, zero_add]
      exact offDiag_le y hm0 (mem_Icc.mp hn).1 hmn
  have hdiag : ∑ m ∈ S, ∑ n ∈ S, (if m = n then Real.log N * z m ^ 2 else 0) =
      Real.log N * ∑ n ∈ S, z n ^ 2 := by
    rw [mul_sum]
    exact sum_congr rfl fun m hm => by rw [sum_ite_eq, if_pos hm]
  have hW : ∑ m ∈ S, ∑ n ∈ S, z m * z n * weilPrimeKernel m n ≤
      (Real.log N + (Real.log 4 + 4)) * ∑ n ∈ S, z n ^ 2 := atomicWeilForm_le_log N z
  have hE := sum_excess_le N z
  rw [torsionPairing, selfMass_eq]
  refine (sum_le_sum fun m hm => sum_le_sum fun n hn => hpt m hm n hn).trans ?_
  simp only [sum_add_distrib]
  rw [hdiag]
  linarith

/-- **The torsion window.** On the orders `≤ N` the minimal torsion counterterm lies between
`(3/2) log N − C₁` and `2 log N + C₂`. -/
theorem torsionCounterterm_window {N : ℕ} (hN : 1 ≤ N) :
    RenormalizesAt N (2 * Real.log N + (Real.log 4 + 4 + 2 * excessConstant)) ∧
      ∀ κ, RenormalizesAt N κ →
        3 / 2 * Real.log N - (Real.log 8 + 4 + tameConstant + 3 / 2) ≤ κ :=
  ⟨renormalizesAt_two_log N, fun _ hκ => torsionCounterterm_ge hN hκ⟩

/-- **The anomaly costs between half a logarithm and one logarithm** over the covariant
counterterm `log N + log 4 + 4`. -/
theorem anomaly_cost_window {N : ℕ} (hN : 1 ≤ N) :
    RenormalizesAt N ((Real.log N + (Real.log 4 + 4)) + (Real.log N + 2 * excessConstant)) ∧
      ∀ κ, RenormalizesAt N κ → (Real.log N + (Real.log 4 + 4)) + (1 / 2 * Real.log N -
        (Real.log 8 + Real.log 4 + 8 + tameConstant + 3 / 2)) ≤ κ := by
  refine ⟨?_, fun _ hκ => (anomaly_cost hN hκ).2⟩
  have h := renormalizesAt_two_log N
  convert h using 1
  ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
