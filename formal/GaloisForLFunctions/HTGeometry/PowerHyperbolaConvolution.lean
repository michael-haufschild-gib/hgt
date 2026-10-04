import Mathlib

/-!
# Power-twisted partial sums and the hyperbola method for `A ⋆ ℕ^{1/β}`

Let `c : ℕ → ℝ`, `c(0) = 0`, with counting function `A(t) = Σ_{k ≤ t} c(k)` (`countFn`) satisfying
`|A(t) − a t| ≤ C t^γ` for `t ≥ 1`.

**Partial summation** (`abs_sum_rpow_mul_sub_le`).  For `0 ≤ γ < p`, `p ≠ 1`,

`Σ_{k ≤ Y} c(k) k^{−p} = a Y^{1−p}/(1 − p) + Z_p + O(Y^{γ−p})`,
`Z_p = a p/(p − 1) + p ∫_1^∞ (A(t) − a t) t^{−p−1} dt` (`abelConst`).

This is Abel summation against `t^{−p}`; the tail of the convergent integral is `O(Y^{γ−p})`.

**Hyperbola** (`abs_hyperbolaCount_sub_le`).  For `0 < γ < β < 1` and `|c| ≤ 1`, the count
`N(x) = Σ_{m ≤ x^β} A(x m^{−1/β})` of pairs `(n, m)` with `n m^{1/β} ≤ x`, weighted by `c(n)`,
satisfies

`N(x) = a Z₁ x + Z_β x^β + O(x^{β/(1 + β − γ)})`,

where `Z₁ = Σ_m m^{−1/β}` is the partial-summation constant of `1` at exponent `1/β`.  Split at
`m = U^β`, `U = x^{(1−γ)/(1+β−γ)}`: the small `m` use the expansion of `A`, the large `m` are
counted along `n ≤ x/U` with the expansion of `Σ c(n) n^{−β}`; the three `x U^{β−1}` terms
cancel.
-/

open Finset MeasureTheory Set Real Filter

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PowerHyperbola

/-- The counting function `A(t) = Σ_{k ≤ t} c(k)`. -/
def countFn (c : ℕ → ℝ) (t : ℝ) : ℝ := ∑ k ∈ Icc 0 ⌊t⌋₊, c k

/-- The constant of the partial summation `Σ_{k ≤ Y} c(k) k^{−p}`. -/
def abelConst (c : ℕ → ℝ) (a p : ℝ) : ℝ :=
  a * p / (p - 1) + p * ∫ t in Ioi (1 : ℝ), (countFn c t - a * t) * t ^ (-p - 1)

theorem measurable_countFn (c : ℕ → ℝ) : Measurable (countFn c) :=
  (measurable_from_nat (f := fun n : ℕ => ∑ k ∈ Icc 0 n, c k)).comp Nat.measurable_floor

theorem countFn_of_lt_one (c : ℕ → ℝ) (hc0 : c 0 = 0) {t : ℝ} (ht : t < 1) : countFn c t = 0 := by
  rw [countFn, Nat.floor_eq_zero.mpr ht]; simp [hc0]

/-- The error of the counting function is integrable against `t^{−p−1}` on `(1, ∞)`. -/
theorem integrableOn_countFn_sub_mul_rpow (c : ℕ → ℝ) {a C γ p : ℝ} (hγp : γ < p)
    (hA : ∀ t : ℝ, 1 ≤ t → |countFn c t - a * t| ≤ C * t ^ γ) {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun t => (countFn c t - a * t) * t ^ (-p - 1)) (Ioi Y) := by
  have hY0 : 0 < Y := by linarith
  refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (a := γ - p - 1) (by linarith) hY0).const_mul
    C) ?_ ?_
  · exact (((measurable_countFn c).sub (measurable_const.mul measurable_id)).mul
      (measurable_id.pow_const _)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 ≤ t := by have : Y < t := ht; linarith
    have ht0 : 0 < t := by linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    calc |countFn c t - a * t| * t ^ (-p - 1) ≤ C * t ^ γ * t ^ (-p - 1) :=
          mul_le_mul_of_nonneg_right (hA t ht1) (by positivity)
      _ = C * t ^ (γ - p - 1) := by
          rw [mul_assoc, ← Real.rpow_add ht0]; ring_nf

/-- The tail of the error integral is `O(Y^{γ−p})`. -/
theorem abs_integral_Ioi_le (c : ℕ → ℝ) {a C γ p : ℝ} (hγp : γ < p)
    (hA : ∀ t : ℝ, 1 ≤ t → |countFn c t - a * t| ≤ C * t ^ γ) {Y : ℝ} (hY : 1 ≤ Y) :
    |∫ t in Ioi Y, (countFn c t - a * t) * t ^ (-p - 1)| ≤ C / (p - γ) * Y ^ (γ - p) := by
  have hY0 : 0 < Y := by linarith
  have hb : IntegrableOn (fun t : ℝ => C * t ^ (γ - p - 1)) (Ioi Y) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hY0).const_mul C
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hb ?_).trans (le_of_eq ?_)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 ≤ t := by have : Y < t := ht; linarith
    have ht0 : 0 < t := by linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    calc |countFn c t - a * t| * t ^ (-p - 1) ≤ C * t ^ γ * t ^ (-p - 1) :=
          mul_le_mul_of_nonneg_right (hA t ht1) (by positivity)
      _ = C * t ^ (γ - p - 1) := by
          rw [mul_assoc, ← Real.rpow_add ht0]; ring_nf
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hY0]
    have : γ - p - 1 + 1 = γ - p := by ring
    rw [this, show -Y ^ (γ - p) / (γ - p) = Y ^ (γ - p) / (p - γ) by
      rw [neg_div, ← div_neg, neg_sub]]
    ring

/-- **Partial summation against `k^{−p}`.** -/
theorem abs_sum_rpow_mul_sub_le (c : ℕ → ℝ) (hc0 : c 0 = 0) {a C γ p : ℝ} (hγp : γ < p)
    (hp0 : 0 < p) (hp1 : p ≠ 1)
    (hA : ∀ t : ℝ, 1 ≤ t → |countFn c t - a * t| ≤ C * t ^ γ) {Y : ℝ} (hY : 1 ≤ Y) :
    |∑ k ∈ Icc 0 ⌊Y⌋₊, (k : ℝ) ^ (-p) * c k - a * Y ^ (1 - p) / (1 - p) - abelConst c a p| ≤
      C * (1 + p / (p - γ)) * Y ^ (γ - p) := by
  have hY0 : 0 < Y := by linarith
  set E : ℝ → ℝ := fun t => countFn c t - a * t with hE
  have hderiv : ∀ t : ℝ, 0 < t → HasDerivAt (fun t : ℝ => t ^ (-p)) (-p * t ^ (-p - 1)) t :=
    fun t ht => Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have hdiff : ∀ t ∈ Icc (1 : ℝ) Y, DifferentiableAt ℝ (fun t : ℝ => t ^ (-p)) t :=
    fun t ht => (hderiv t (by linarith [ht.1])).differentiableAt
  have hderiv_eq : EqOn (deriv fun t : ℝ => t ^ (-p)) (fun t => -p * t ^ (-p - 1)) (Icc 1 Y) :=
    fun t ht => (hderiv t (by linarith [ht.1])).deriv
  have hint_deriv : IntegrableOn (deriv fun t : ℝ => t ^ (-p)) (Icc 1 Y) := by
    have hcont : ContinuousOn (fun t : ℝ => -p * t ^ (-p - 1)) (Icc 1 Y) :=
      continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id
        (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le one_pos ht.1))))
    exact (hcont.integrableOn_Icc).congr_fun hderiv_eq.symm measurableSet_Icc
  have habel : ∑ k ∈ Icc 0 ⌊Y⌋₊, (k : ℝ) ^ (-p) * c k = Y ^ (-p) * countFn c Y -
      ∫ t in Ioc 1 Y, deriv (fun t : ℝ => t ^ (-p)) t * countFn c t :=
    sum_mul_eq_sub_integral_mul₀ c hc0 Y hdiff hint_deriv
  -- rewrite the Abel integral
  have hI : ∫ t in Ioc 1 Y, deriv (fun t : ℝ => t ^ (-p)) t * countFn c t =
      -p * (a * ((Y ^ (1 - p) - 1) / (1 - p)) + ∫ t in Ioc 1 Y, E t * t ^ (-p - 1)) := by
    have h1 : ∫ t in Ioc 1 Y, deriv (fun t : ℝ => t ^ (-p)) t * countFn c t =
        ∫ t in Ioc 1 Y, -p * (a * t ^ (-p) + E t * t ^ (-p - 1)) := by
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      have ht0 : 0 < t := by linarith [ht.1]
      rw [hderiv_eq (Ioc_subset_Icc_self ht), hE]
      have : t ^ (-p - 1) * t = t ^ (-p) := by
        rw [← Real.rpow_add_one ht0.ne']; ring_nf
      linear_combination (-p * a) * this
    have hpow : IntegrableOn (fun t : ℝ => t ^ (-p)) (Ioc 1 Y) := by
      refine (ContinuousOn.integrableOn_Icc (ContinuousOn.rpow_const continuousOn_id
        (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le one_pos ht.1))))).mono_set Ioc_subset_Icc_self
    have hEi : IntegrableOn (fun t => E t * t ^ (-p - 1)) (Ioc 1 Y) := by
      have := integrableOn_countFn_sub_mul_rpow c hγp hA (le_refl 1)
      exact this.mono_set (fun t ht => ht.1)
    rw [h1, integral_const_mul, integral_add (hpow.const_mul a) hEi, integral_const_mul,
      ← intervalIntegral.integral_of_le hY, integral_rpow (Or.inr ⟨by
        intro h; apply hp1; linarith, by
        rw [Set.uIcc_of_le hY]; intro h; linarith [h.1]⟩)]
    rw [show -p + 1 = 1 - p by ring, Real.one_rpow]
  -- split the error integral
  have hsplit : ∫ t in Ioc 1 Y, E t * t ^ (-p - 1) =
      (∫ t in Ioi 1, E t * t ^ (-p - 1)) - ∫ t in Ioi Y, E t * t ^ (-p - 1) := by
    have hu := setIntegral_union (μ := volume) (f := fun t => E t * t ^ (-p - 1))
      (Ioc_disjoint_Ioi_same (a := (1 : ℝ)) (b := Y)) measurableSet_Ioi
      ((integrableOn_countFn_sub_mul_rpow c hγp hA (le_refl 1)).mono_set (fun t ht => ht.1))
      (integrableOn_countFn_sub_mul_rpow c hγp hA hY)
    rw [Ioc_union_Ioi_eq_Ioi hY] at hu
    linarith
  have htail := abs_integral_Ioi_le c hγp hA hY
  have hEY := hA Y hY
  rw [habel, hI, hsplit]
  unfold abelConst
  set I₁ := ∫ t in Ioi 1, E t * t ^ (-p - 1)
  set IY := ∫ t in Ioi Y, E t * t ^ (-p - 1)
  have hYp : Y ^ (-p) * Y = Y ^ (1 - p) := by
    rw [← Real.rpow_add_one hY0.ne']; ring_nf
  have hp1' : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  have hp1'' : p - 1 ≠ 0 := sub_ne_zero.mpr hp1
  have hkey : Y ^ (-p) * countFn c Y - -p * (a * ((Y ^ (1 - p) - 1) / (1 - p)) + (I₁ - IY)) -
      a * Y ^ (1 - p) / (1 - p) - (a * p / (p - 1) + p * I₁) = Y ^ (-p) * E Y - p * IY := by
    rw [hE]; simp only
    rw [show Y ^ (-p) * (countFn c Y - a * Y) = Y ^ (-p) * countFn c Y - a * (Y ^ (-p) * Y) by
      ring, hYp]
    field_simp
    ring
  rw [hkey]
  have hYγ : Y ^ (-p) * Y ^ γ = Y ^ (γ - p) := by
    rw [← Real.rpow_add hY0]; ring_nf
  calc |Y ^ (-p) * E Y - p * IY| ≤ |Y ^ (-p) * E Y| + |p * IY| := abs_sub _ _
    _ ≤ Y ^ (-p) * (C * Y ^ γ) + p * (C / (p - γ) * Y ^ (γ - p)) := by
        rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hY0 _), abs_of_pos hp0]
        gcongr
    _ = C * (1 + p / (p - γ)) * Y ^ (γ - p) := by
        rw [show Y ^ (-p) * (C * Y ^ γ) = C * (Y ^ (-p) * Y ^ γ) by ring, hYγ]
        have : p - γ ≠ 0 := by linarith
        field_simp

/-! ## The hyperbola method -/

/-- The indicator of the positive integers. -/
def oneSeq (n : ℕ) : ℝ := if n = 0 then 0 else 1

theorem oneSeq_zero : oneSeq 0 = 0 := by simp [oneSeq]

theorem sum_Icc_zero_oneSeq (n : ℕ) : ∑ k ∈ Icc 0 n, oneSeq k = n := by
  induction n with
  | zero => simp [oneSeq]
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (Nat.zero_le _), ih]
      simp [oneSeq]

theorem abs_countFn_oneSeq_sub_le {t : ℝ} (ht : 1 ≤ t) :
    |countFn oneSeq t - 1 * t| ≤ 1 * t ^ (0 : ℝ) := by
  rw [countFn, sum_Icc_zero_oneSeq, Real.rpow_zero, one_mul, one_mul, abs_le]
  have h1 := Nat.lt_floor_add_one t
  have h2 := Nat.floor_le (by linarith : (0 : ℝ) ≤ t)
  constructor <;> linarith

/-- Sums over `1 ≤ k ≤ n` as sums over `0 ≤ k ≤ n` when the `k = 0` term vanishes. -/
theorem sum_Icc_one_eq (f : ℕ → ℝ) (hf : f 0 = 0) (n : ℕ) :
    ∑ k ∈ Icc 1 n, f k = ∑ k ∈ Icc 0 n, f k := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons, hf, zero_add]
  rfl

theorem sum_Icc_one_rpow_eq (q : ℝ) (n : ℕ) :
    ∑ m ∈ Icc 1 n, (m : ℝ) ^ (-q) = ∑ k ∈ Icc 0 n, (k : ℝ) ^ (-q) * oneSeq k := by
  rw [← sum_Icc_one_eq _ (by simp [oneSeq]) n]
  refine Finset.sum_congr rfl fun m hm => ?_
  have : m ≠ 0 := by have := (Finset.mem_Icc.mp hm).1; omega
  simp [oneSeq, this]

/-- The hyperbola count `N(x) = Σ_{1 ≤ m ≤ x^β} A(x m^{−1/β})`. -/
def hyperbolaCount (c : ℕ → ℝ) (β x : ℝ) : ℝ :=
  ∑ m ∈ Icc 1 ⌊x ^ β⌋₊, countFn c (x * (m : ℝ) ^ (-(1 / β)))

/-- For `m, n ≥ 1`: `n ≤ x m^{−1/β}` iff `m ≤ (x/n)^β`. -/
theorem le_mul_rpow_iff {β x : ℝ} (hβ : 0 < β) (hx : 0 ≤ x) {m n : ℝ} (hm : 0 < m) (hn : 0 < n) :
    n ≤ x * m ^ (-(1 / β)) ↔ m ≤ (x / n) ^ β := by
  have hmp : 0 < m ^ (1 / β) := Real.rpow_pos_of_pos hm _
  rw [Real.rpow_neg hm.le, ← div_eq_mul_inv, le_div_iff₀ hmp, mul_comm, ← le_div_iff₀ hn]
  rw [← Real.rpow_le_rpow_iff (Real.rpow_nonneg hm.le _) (div_nonneg hx hn.le) hβ,
    ← Real.rpow_mul hm.le, one_div, inv_mul_cancel₀ hβ.ne', Real.rpow_one]

/-- **The large-`m` part of the hyperbola**, counted along `n`. -/
theorem sum_Ioc_countFn_eq (c : ℕ → ℝ) (hc0 : c 0 = 0) {β x U : ℝ} (hβ : 0 < β) (hx : 1 ≤ x)
    (hU : 1 ≤ U) :
    ∑ m ∈ Ioc ⌊U ^ β⌋₊ ⌊x ^ β⌋₊, countFn c (x * (m : ℝ) ^ (-(1 / β))) =
      ∑ n ∈ Icc 1 ⌊x / U⌋₊, c n * ((⌊(x / n) ^ β⌋₊ : ℝ) - ⌊U ^ β⌋₊) := by
  have hx0 : 0 < x := by linarith
  have hU0 : 0 < U := by linarith
  have hM1 : 1 ≤ U ^ β := Real.one_le_rpow hU hβ.le
  -- drop the `n = 0` terms
  have h1 : ∀ m ∈ Finset.Ioc ⌊U ^ β⌋₊ ⌊x ^ β⌋₊, countFn c (x * (m : ℝ) ^ (-(1 / β))) =
      ∑ n ∈ Icc 1 ⌊x * (m : ℝ) ^ (-(1 / β))⌋₊, c n := fun m _ =>
    (sum_Icc_one_eq c hc0 _).symm
  rw [Finset.sum_congr rfl h1]
  have hswap := Finset.sum_comm' (s := Finset.Ioc ⌊U ^ β⌋₊ ⌊x ^ β⌋₊)
    (t := fun m : ℕ => Finset.Icc 1 ⌊x * (m : ℝ) ^ (-(1 / β))⌋₊) (t' := Finset.Icc 1 ⌊x / U⌋₊)
    (s' := fun n : ℕ => Finset.Ioc ⌊U ^ β⌋₊ ⌊(x / n) ^ β⌋₊) (f := fun _ n => c n) ?_
  · rw [hswap]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnY : (n : ℝ) ≤ x / U := by
      have := (Finset.mem_Icc.mp hn).2
      exact (Nat.le_floor_iff (by positivity)).mp this
    have hMle : ⌊U ^ β⌋₊ ≤ ⌊(x / n) ^ β⌋₊ := by
      apply Nat.floor_le_floor
      apply Real.rpow_le_rpow hU0.le _ hβ.le
      rw [le_div_iff₀ hn0]; rw [le_div_iff₀ hU0] at hnY; linarith
    rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.cast_sub hMle]
    ring
  · intro m n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hm1, hm2⟩, hn1, hn2⟩
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm1)
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hnx : (n : ℝ) ≤ x * (m : ℝ) ^ (-(1 / β)) :=
        (Nat.le_floor_iff (by positivity)).mp hn2
      have hmM : U ^ β < m := by
        have := Nat.lt_floor_add_one (U ^ β)
        have h' : ((⌊U ^ β⌋₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm1
        push_cast at h'; linarith
      refine ⟨⟨hm1, Nat.le_floor ((le_mul_rpow_iff hβ hx0.le hm0 hn0).mp hnx)⟩, hn1, ?_⟩
      apply Nat.le_floor
      -- `n ≤ x m^{−1/β} < x (U^β)^{−1/β} = x/U`
      have hlt : (m : ℝ) ^ (-(1 / β)) < (U ^ β) ^ (-(1 / β)) :=
        Real.rpow_lt_rpow_of_neg (by positivity) hmM (by
          have : 0 < 1 / β := by positivity
          linarith)
      rw [← Real.rpow_mul hU0.le, show β * -(1 / β) = -1 by field_simp, Real.rpow_neg_one] at hlt
      rw [div_eq_mul_inv]
      nlinarith
    · rintro ⟨⟨hm1, hm2⟩, hn1, hn2⟩
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm1)
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hmx : (m : ℝ) ≤ (x / n) ^ β := (Nat.le_floor_iff (by positivity)).mp hm2
      refine ⟨⟨hm1, Nat.le_floor ?_⟩, hn1, Nat.le_floor ((le_mul_rpow_iff hβ hx0.le hm0 hn0).mpr hmx)⟩
      refine hmx.trans (Real.rpow_le_rpow (by positivity) ?_ hβ.le)
      rw [div_le_iff₀ hn0]
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      nlinarith

/-- The small-`m` part of the hyperbola: `A(x m^{−1/β}) = a x m^{−1/β} + O(x^γ m^{−γ/β})`. -/
theorem abs_sum_Icc_countFn_sub_le (c : ℕ → ℝ) {a C γ β : ℝ} (hβ0 : 0 < β)
    (hA : ∀ t : ℝ, 1 ≤ t → |countFn c t - a * t| ≤ C * t ^ γ) {x M : ℝ} (hx0 : 0 < x)
    (hM1 : 1 ≤ M) (hxM : 1 ≤ x * M ^ (-(1 / β))) :
    |∑ m ∈ Finset.Icc 1 ⌊M⌋₊, countFn c (x * (m : ℝ) ^ (-(1 / β))) -
        a * x * ∑ m ∈ Finset.Icc 1 ⌊M⌋₊, (m : ℝ) ^ (-(1 / β))| ≤
      C * x ^ γ * ∑ m ∈ Finset.Icc 1 ⌊M⌋₊, (m : ℝ) ^ (-(γ / β)) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hm0 : (0 : ℝ) < m := by linarith
  have hmM : (m : ℝ) ≤ M := (Nat.le_floor_iff (by linarith)).mp (Finset.mem_Icc.mp hm).2
  have harg : 1 ≤ x * (m : ℝ) ^ (-(1 / β)) := by
    have h1 : M ^ (-(1 / β)) ≤ (m : ℝ) ^ (-(1 / β)) :=
      Real.rpow_le_rpow_of_nonpos hm0 hmM (by rw [neg_nonpos]; positivity)
    calc (1 : ℝ) ≤ x * M ^ (-(1 / β)) := hxM
      _ ≤ x * (m : ℝ) ^ (-(1 / β)) := by gcongr
  have hE := hA _ harg
  have hpow : (x * (m : ℝ) ^ (-(1 / β))) ^ γ = x ^ γ * (m : ℝ) ^ (-(γ / β)) := by
    rw [Real.mul_rpow hx0.le (by positivity), ← Real.rpow_mul hm0.le]
    congr 2; ring
  rw [hpow] at hE
  calc |countFn c (x * (m : ℝ) ^ (-(1 / β))) - a * x * (m : ℝ) ^ (-(1 / β))|
      = |countFn c (x * (m : ℝ) ^ (-(1 / β))) - a * (x * (m : ℝ) ^ (-(1 / β)))| := by ring_nf
    _ ≤ C * (x ^ γ * (m : ℝ) ^ (-(γ / β))) := hE
    _ = C * x ^ γ * (m : ℝ) ^ (-(γ / β)) := by ring

/-- The large-`m` part of the hyperbola: `x^β Σ_{n ≤ x/U} c(n) n^{−β} − U^β A(x/U) + O(x/U)`. -/
theorem abs_sum_Ioc_countFn_sub_le (c : ℕ → ℝ) (hc0 : c 0 = 0) (hc : ∀ n, |c n| ≤ 1) {β x U : ℝ}
    (hβ : 0 < β) (hx : 1 ≤ x) (hU : 1 ≤ U) :
    |∑ m ∈ Finset.Ioc ⌊U ^ β⌋₊ ⌊x ^ β⌋₊, countFn c (x * (m : ℝ) ^ (-(1 / β))) -
        (x ^ β * ∑ k ∈ Finset.Icc 0 ⌊x / U⌋₊, (k : ℝ) ^ (-β) * c k -
          U ^ β * countFn c (x / U))| ≤ x / U := by
  have hx0 : 0 < x := by linarith
  have hU0 : 0 < U := by linarith
  rw [sum_Ioc_countFn_eq c hc0 hβ hx hU]
  have hexp : x ^ β * ∑ k ∈ Finset.Icc 0 ⌊x / U⌋₊, (k : ℝ) ^ (-β) * c k -
      U ^ β * countFn c (x / U) =
      ∑ n ∈ Finset.Icc 1 ⌊x / U⌋₊, c n * ((x / n) ^ β - U ^ β) := by
    rw [countFn, ← sum_Icc_one_eq (fun k => (k : ℝ) ^ (-β) * c k) (by simp [hc0]),
      ← sum_Icc_one_eq c hc0, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by
      have := (Finset.mem_Icc.mp hn).1; exact_mod_cast this
    rw [Real.div_rpow hx0.le hn0.le, Real.rpow_neg hn0.le]
    ring
  rw [hexp, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hY : (0 : ℝ) ≤ x / U := by positivity
  calc ∑ n ∈ Finset.Icc 1 ⌊x / U⌋₊,
        |c n * ((⌊(x / n) ^ β⌋₊ : ℝ) - ⌊U ^ β⌋₊) - c n * ((x / n) ^ β - U ^ β)|
      ≤ ∑ n ∈ Finset.Icc 1 ⌊x / U⌋₊, (1 : ℝ) := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [← mul_sub, abs_mul]
        have hfl1 := Nat.floor_le (by positivity : (0 : ℝ) ≤ (x / n) ^ β)
        have hfl2 := Nat.lt_floor_add_one ((x / n) ^ β)
        have hfl3 := Nat.floor_le (by positivity : (0 : ℝ) ≤ U ^ β)
        have hfl4 := Nat.lt_floor_add_one (U ^ β)
        have hd : |((⌊(x / n) ^ β⌋₊ : ℝ) - ⌊U ^ β⌋₊) - ((x / n) ^ β - U ^ β)| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith
        calc |c n| * |((⌊(x / n) ^ β⌋₊ : ℝ) - ⌊U ^ β⌋₊) - ((x / n) ^ β - U ^ β)| ≤ 1 * 1 :=
              mul_le_mul (hc n) hd (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    _ = ⌊x / U⌋₊ := by simp
    _ ≤ x / U := Nat.floor_le hY

theorem hyperbolaCount_eq_add (c : ℕ → ℝ) {β x M : ℝ} (hM1 : 1 ≤ M) (hMx : M ≤ x ^ β) :
    hyperbolaCount c β x =
      (∑ m ∈ Finset.Icc 1 ⌊M⌋₊, countFn c (x * (m : ℝ) ^ (-(1 / β)))) +
        ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊x ^ β⌋₊, countFn c (x * (m : ℝ) ^ (-(1 / β))) := by
  have hMfl : 1 ≤ ⌊M⌋₊ := Nat.le_floor (by exact_mod_cast hM1)
  have hMfl' : ⌊M⌋₊ ≤ ⌊x ^ β⌋₊ := Nat.floor_le_floor hMx
  rw [hyperbolaCount, ← Finset.sum_union]
  · congr 1
    ext m
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  · rw [Finset.disjoint_left]
    intro m h1 h2
    rw [Finset.mem_Icc] at h1; rw [Finset.mem_Ioc] at h2; omega

/-- The three `x U^{β−1}` terms of the hyperbola cancel. -/
theorem hyperbola_cancel {a β x U : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hx0 : 0 < x) (hU0 : 0 < U) :
    a * x * ((U ^ β) ^ (1 - 1 / β) / (1 - 1 / β)) +
        x ^ β * (a * (x / U) ^ (1 - β) / (1 - β)) - U ^ β * (a * (x / U)) = 0 := by
  have h1 : (U ^ β) ^ (1 - 1 / β) = U ^ (β - 1) := by
    rw [← Real.rpow_mul hU0.le]; congr 1; field_simp
  have h2 : x ^ β * (x / U) ^ (1 - β) = x * U ^ (β - 1) := by
    rw [Real.div_rpow hx0.le hU0.le, ← mul_div_assoc, ← Real.rpow_add hx0,
      show β + (1 - β) = 1 by ring, Real.rpow_one, div_eq_mul_inv, ← Real.rpow_neg hU0.le]
    ring_nf
  have h3 : U ^ β * (x / U) = x * U ^ (β - 1) := by
    rw [Real.rpow_sub_one hU0.ne']; field_simp
  have h2' : x ^ β * (a * (x / U) ^ (1 - β) / (1 - β)) = a * (x * U ^ (β - 1)) / (1 - β) := by
    rw [← h2]; ring
  have h3' : U ^ β * (a * (x / U)) = a * (x * U ^ (β - 1)) := by rw [← h3]; ring
  rw [h1, h2', h3']
  have hb1 : 1 - β ≠ 0 := by intro h; linarith
  have hb3 : -1 + β ≠ 0 := by intro h; linarith
  have hb4 : β - 1 ≠ 0 := by intro h; linarith
  field_simp
  ring

/-- The exponent bookkeeping of the hyperbola at `U = x^{(1−γ)/(1+β−γ)}`. -/
theorem hyperbola_rpow_facts {β γ x : ℝ} (hγ0 : 0 < γ) (hγβ : γ < β) (hβ1 : β < 1) (hx : 1 ≤ x) :
    let U := x ^ ((1 - γ) / (1 + β - γ))
    let e := β / (1 + β - γ)
    1 ≤ U ∧ U ≤ x ∧ x / U = x ^ e ∧ x ^ γ * (U ^ β) ^ (1 - γ / β) = x ^ e ∧
      x ^ β * (x / U) ^ (γ - β) = x ^ e ∧ U ^ β * (x / U) ^ γ = x ^ e ∧ x ^ γ ≤ x ^ e ∧
      x * (U ^ β) ^ (-(1 / β)) = x ^ e := by
  intro U e
  have hβ0 : 0 < β := by linarith
  have hx0 : 0 < x := by linarith
  have hden : 0 < 1 + β - γ := by linarith
  set l : ℝ := (1 - γ) / (1 + β - γ) with hl
  have hl0 : 0 ≤ l := div_nonneg (by linarith) hden.le
  have hl1 : l ≤ 1 := by rw [hl, div_le_one hden]; linarith
  have hle : 1 - l = e := by simp only [e]; rw [hl]; field_simp; ring
  have hU1 : 1 ≤ U := Real.one_le_rpow hx hl0
  have hU0 : 0 < U := by linarith
  have hUx : U ≤ x := by
    calc U = x ^ l := rfl
      _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hl1
      _ = x := Real.rpow_one x
  have hYe : x / U = x ^ e := by
    simp only [U]; rw [← hle, Real.rpow_sub hx0, Real.rpow_one]
  have hUl : ∀ r : ℝ, U ^ r = x ^ (l * r) := fun r => by
    simp only [U]; rw [← Real.rpow_mul hx0.le]
  have hγe : x ^ γ * U ^ (β - γ) = x ^ e := by
    rw [hUl, ← Real.rpow_add hx0]; congr 1
    simp only [e]; rw [hl]; field_simp; ring
  refine ⟨hU1, hUx, hYe, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Real.rpow_mul hU0.le, show β * (1 - γ / β) = β - γ by field_simp, hγe]
  · rw [Real.div_rpow hx0.le hU0.le, ← mul_div_assoc, ← Real.rpow_add hx0,
      show β + (γ - β) = γ by ring, div_eq_mul_inv, ← Real.rpow_neg hU0.le,
      show -(γ - β) = β - γ by ring, hγe]
  · rw [Real.div_rpow hx0.le hU0.le, mul_div_assoc', mul_comm, mul_div_assoc,
      ← Real.rpow_sub hU0, hγe]
  · apply Real.rpow_le_rpow_of_exponent_le hx
    simp only [e]; rw [le_div_iff₀ hden]; nlinarith
  · rw [← Real.rpow_mul hU0.le, show β * -(1 / β) = -1 by field_simp, Real.rpow_neg_one,
      ← div_eq_mul_inv, hYe]

/-- The linear bookkeeping of the hyperbola. -/
theorem hyperbola_assemble {SI SII Sp Sβ AY Z₁ Z a x xβ M Y P Q B1 B2 B3 B4 B5 : ℝ}
    (hI : |SI - a * x * Sp| ≤ B1) (hb1 : |a * x * (Sp - P - Z₁)| ≤ B2)
    (hII : |SII - (xβ * Sβ - M * AY)| ≤ B3) (hb2 : |xβ * (Sβ - Q - Z)| ≤ B4)
    (hb3 : |M * (AY - a * Y)| ≤ B5) (hcancel : a * x * P + xβ * Q - M * (a * Y) = 0) :
    |SI + SII - a * Z₁ * x - Z * xβ| ≤ B1 + B2 + B3 + B4 + B5 := by
  have hid : SI + SII - a * Z₁ * x - Z * xβ =
      (SI - a * x * Sp) + a * x * (Sp - P - Z₁) + (SII - (xβ * Sβ - M * AY)) +
        xβ * (Sβ - Q - Z) - M * (AY - a * Y) + (a * x * P + xβ * Q - M * (a * Y)) := by ring
  rw [hid, hcancel, add_zero]
  have e1 := abs_le.mp hI
  have e2 := abs_le.mp hb1
  have e3 := abs_le.mp hII
  have e4 := abs_le.mp hb2
  have e5 := abs_le.mp hb3
  rw [abs_le]
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2]

/-- The hyperbola estimate at a fixed splitting point `U`. -/
theorem abs_hyperbolaCount_sub_le_of (c : ℕ → ℝ) (hc0 : c 0 = 0) (hc : ∀ n, |c n| ≤ 1)
    {a C γ β : ℝ} (hγ0 : 0 < γ) (hγβ : γ < β) (hβ1 : β < 1) (hC : 0 ≤ C)
    (hA : ∀ t : ℝ, 1 ≤ t → |countFn c t - a * t| ≤ C * t ^ γ) {x U xe : ℝ} (hx : 1 ≤ x)
    (hU1 : 1 ≤ U) (hUx : U ≤ x) (hYe : x / U = xe) (hqe : x ^ γ * (U ^ β) ^ (1 - γ / β) = xe)
    (hβe : x ^ β * (x / U) ^ (γ - β) = xe) (hMYe : U ^ β * (x / U) ^ γ = xe) (hγe : x ^ γ ≤ xe)
    (hxMe : x * (U ^ β) ^ (-(1 / β)) = xe) :
    |hyperbolaCount c β x - a * abelConst oneSeq 1 (1 / β) * x - abelConst c a β * x ^ β| ≤
      (|a| * (1 * (1 + 1 / β / (1 / β - 0))) +
        C * (1 / (1 - γ / β) + |abelConst oneSeq 1 (γ / β)| + 1 * (1 + γ / β / (γ / β - 0))) +
        C * (1 + β / (β - γ)) + C + 1) * xe := by
  have hβ0 : 0 < β := by linarith
  have hp1 : 1 < 1 / β := by rw [lt_div_iff₀ hβ0]; linarith
  have hq0 : 0 < γ / β := by positivity
  have hq1 : γ / β < 1 := by rw [div_lt_one hβ0]; exact hγβ
  have hA1 : ∀ t : ℝ, 1 ≤ t → |countFn oneSeq t - 1 * t| ≤ 1 * t ^ (0 : ℝ) :=
    fun t ht => abs_countFn_oneSeq_sub_le ht
  have hx0 : 0 < x := by linarith
  have hU0 : 0 < U := by linarith
  have hM1 : 1 ≤ U ^ β := Real.one_le_rpow hU1 hβ0.le
  have hMx : U ^ β ≤ x ^ β := Real.rpow_le_rpow hU0.le hUx hβ0.le
  have hY1 : 1 ≤ x / U := by rw [le_div_iff₀ hU0]; linarith
  have hxe1 : 1 ≤ xe := by rw [← hYe]; exact hY1
  have hxM : 1 ≤ x * (U ^ β) ^ (-(1 / β)) := by rw [hxMe]; exact hxe1
  have hKp0 : (0 : ℝ) ≤ 1 * (1 + 1 / β / (1 / β - 0)) := by
    rw [sub_zero, div_self (by positivity)]; norm_num
  have hKq0 : (0 : ℝ) ≤ 1 * (1 + γ / β / (γ / β - 0)) := by
    rw [sub_zero, div_self (by positivity)]; norm_num
  rw [hyperbolaCount_eq_add c hM1 hMx]
  have hI := abs_sum_Icc_countFn_sub_le c hβ0 hA hx0 hM1 hxM
  have hII := abs_sum_Ioc_countFn_sub_le c hc0 hc hβ0 hx hU1
  have hSp := abs_sum_rpow_mul_sub_le oneSeq oneSeq_zero (a := 1) (C := 1) (γ := 0) (p := 1 / β)
    (by linarith) (by linarith) (ne_of_gt hp1) hA1 hM1
  have hSq := abs_sum_rpow_mul_sub_le oneSeq oneSeq_zero (a := 1) (C := 1) (γ := 0) (p := γ / β)
    hq0 hq0 (ne_of_lt hq1) hA1 hM1
  have hSβ := abs_sum_rpow_mul_sub_le c hc0 hγβ hβ0 (ne_of_lt hβ1) hA hY1
  have hAY := hA (x / U) hY1
  rw [← sum_Icc_one_rpow_eq] at hSp hSq
  have hcancel := hyperbola_cancel (a := a) hβ0 hβ1 hx0 hU0
  -- the second part, `|a x (S_p − main − Z₁)| ≤ |a| K_p x^e`
  have hMp : x * (U ^ β) ^ (0 - 1 / β) = xe := by rw [zero_sub]; exact hxMe
  have hb1 : |a * x * (∑ m ∈ Finset.Icc 1 ⌊U ^ β⌋₊, (m : ℝ) ^ (-(1 / β)) -
      1 * (U ^ β) ^ (1 - 1 / β) / (1 - 1 / β) - abelConst oneSeq 1 (1 / β))| ≤
      |a| * (1 * (1 + 1 / β / (1 / β - 0))) * xe := by
    rw [abs_mul, abs_mul, abs_of_pos hx0, ← hMp]
    calc |a| * x * |∑ m ∈ Finset.Icc 1 ⌊U ^ β⌋₊, (m : ℝ) ^ (-(1 / β)) -
          1 * (U ^ β) ^ (1 - 1 / β) / (1 - 1 / β) - abelConst oneSeq 1 (1 / β)|
        ≤ |a| * x * (1 * (1 + 1 / β / (1 / β - 0)) * (U ^ β) ^ (0 - 1 / β)) := by gcongr
      _ = _ := by ring
  have hb2 : |x ^ β * (∑ k ∈ Finset.Icc 0 ⌊x / U⌋₊, (k : ℝ) ^ (-β) * c k -
      a * (x / U) ^ (1 - β) / (1 - β) - abelConst c a β)| ≤ C * (1 + β / (β - γ)) * xe := by
    rw [abs_mul, abs_of_nonneg (by positivity), ← hβe]
    calc x ^ β * |∑ k ∈ Finset.Icc 0 ⌊x / U⌋₊, (k : ℝ) ^ (-β) * c k -
          a * (x / U) ^ (1 - β) / (1 - β) - abelConst c a β|
        ≤ x ^ β * (C * (1 + β / (β - γ)) * (x / U) ^ (γ - β)) := by gcongr
      _ = _ := by ring
  have hb3 : |U ^ β * (countFn c (x / U) - a * (x / U))| ≤ C * xe := by
    rw [abs_mul, abs_of_nonneg (by linarith), ← hMYe]
    calc U ^ β * |countFn c (x / U) - a * (x / U)| ≤ U ^ β * (C * (x / U) ^ γ) := by gcongr
      _ = _ := by ring
  have hb4 : C * x ^ γ * ∑ m ∈ Finset.Icc 1 ⌊U ^ β⌋₊, (m : ℝ) ^ (-(γ / β)) ≤
      C * (1 / (1 - γ / β) + |abelConst oneSeq 1 (γ / β)| + 1 * (1 + γ / β / (γ / β - 0))) * xe := by
    have hq1' : 0 < 1 - γ / β := by linarith
    have hMq : (U ^ β) ^ (0 - γ / β) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hM1 (by linarith)
    have hS := (abs_le.mp hSq).2
    rw [one_mul] at hS
    have hKq : 1 * (1 + γ / β / (γ / β - 0)) * (U ^ β) ^ (0 - γ / β) ≤
        1 * (1 + γ / β / (γ / β - 0)) := mul_le_of_le_one_right hKq0 hMq
    have hZq := le_abs_self (abelConst oneSeq 1 (γ / β))
    have hSq_le : ∑ m ∈ Finset.Icc 1 ⌊U ^ β⌋₊, (m : ℝ) ^ (-(γ / β)) ≤
        (U ^ β) ^ (1 - γ / β) / (1 - γ / β) + |abelConst oneSeq 1 (γ / β)| +
          1 * (1 + γ / β / (γ / β - 0)) := by linarith
    have hxγ0 : 0 ≤ x ^ γ := by positivity
    have hK0 : 0 ≤ |abelConst oneSeq 1 (γ / β)| + 1 * (1 + γ / β / (γ / β - 0)) := by positivity
    calc C * x ^ γ * ∑ m ∈ Finset.Icc 1 ⌊U ^ β⌋₊, (m : ℝ) ^ (-(γ / β))
        ≤ C * x ^ γ * ((U ^ β) ^ (1 - γ / β) / (1 - γ / β) + |abelConst oneSeq 1 (γ / β)| +
          1 * (1 + γ / β / (γ / β - 0))) := by gcongr
      _ = C * ((x ^ γ * (U ^ β) ^ (1 - γ / β)) / (1 - γ / β) +
          (|abelConst oneSeq 1 (γ / β)| + 1 * (1 + γ / β / (γ / β - 0))) * x ^ γ) := by ring
      _ ≤ C * (xe / (1 - γ / β) +
          (|abelConst oneSeq 1 (γ / β)| + 1 * (1 + γ / β / (γ / β - 0))) * xe) := by
          rw [hqe]; gcongr
      _ = _ := by ring
  have hb5 : x / U ≤ 1 * xe := by rw [one_mul, hYe]
  have h := hyperbola_assemble (hI.trans hb4) hb1 (hII.trans hb5) hb2 hb3
    (by linear_combination hcancel)
  refine h.trans (le_of_eq ?_)
  ring

/-- **The hyperbola method.**  If `|A(t) − a t| ≤ C t^γ` with `0 < γ < β < 1` and `|c| ≤ 1`, then
`N(x) = a Z₁ x + Z_β x^β + O(x^{β/(1+β−γ)})`. -/
theorem abs_hyperbolaCount_sub_le (c : ℕ → ℝ) (hc0 : c 0 = 0) (hc : ∀ n, |c n| ≤ 1)
    {a C γ β : ℝ} (hγ0 : 0 < γ) (hγβ : γ < β) (hβ1 : β < 1) (hC : 0 ≤ C)
    (hA : ∀ t : ℝ, 1 ≤ t → |countFn c t - a * t| ≤ C * t ^ γ) :
    ∃ K : ℝ, ∀ x : ℝ, 1 ≤ x →
      |hyperbolaCount c β x - a * abelConst oneSeq 1 (1 / β) * x - abelConst c a β * x ^ β| ≤
        K * x ^ (β / (1 + β - γ)) := by
  refine ⟨|a| * (1 * (1 + 1 / β / (1 / β - 0))) +
    C * (1 / (1 - γ / β) + |abelConst oneSeq 1 (γ / β)| + 1 * (1 + γ / β / (γ / β - 0))) +
    C * (1 + β / (β - γ)) + C + 1, fun x hx => ?_⟩
  obtain ⟨hU1, hUx, hYe, hqe, hβe, hMYe, hγe, hxMe⟩ := hyperbola_rpow_facts hγ0 hγβ hβ1 hx
  exact abs_hyperbolaCount_sub_le_of c hc0 hc hγ0 hγβ hβ1 hC hA hx hU1 hUx hYe hqe hβe hMYe hγe
    hxMe

end GaloisForLFunctions.HTGeometry.PowerHyperbola
