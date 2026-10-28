import GaloisForLFunctions.ArtinMertens.TheIdealCountHasAPowerSavingErrorTerm
import GaloisForLFunctions.RHTower.Sieve.ZetaTruncated

/-!
# Mertens' theorem for prime ideals with a bounded error

For a number field `K`, `A_K(x) = Σ_{N𝔭^k ≤ x} log N𝔭/N𝔭^k = log x + O(1)`
(`exists_abs_primeMertens_sub_log_le`).

* **Abel summation** (`sum_Icc_mul_eq_abel`, `sum_mul_le_of_count_le`, `sum_mul_log_ge_of_count`):
  weights whose counting function is at most `Bm` sum against a nonincreasing `f ≥ 0` to at most
  `B Σ_{m ≤ x} f(m)`, and against `log` to at least `(total weight)·log x − Bx`.
* **The hyperbola identity** `L(x) = Σ_{N𝔞 ≤ x} log N𝔞 = Σ_{N𝔭^k ≤ x} log N𝔭 · I(⌊x/N𝔭^k⌋)`: with
  Weber's `|I(t) − ct| ≤ B t^σ`, `σ = 1 − 1/(n+1)`, the right side is `c x A_K(x) + O(ψ_K(x)) +
  O(x^σ S(x))`, `S(x) = Σ log N𝔭 (N𝔭^k)^{−σ} ≤ D Σ_{m ≤ x} m^{−σ} = O(x^{1−σ})` (Chebyshev), so
  `c x A_K(x) + O(x)`; the left side is `I(x) log x − O(x) = c x log x + O(x)`.
-/

noncomputable section

open Finset NumberField Ideal Filter Topology Module
open scoped Classical

namespace GaloisForLFunctions.ArtinMertens

/-- **Abel summation**: `Σ_{m=1}^N a_m g_m = A_N g_N + Σ_{m=1}^{N−1} A_m (g_m − g_{m+1})` with
`A_m = Σ_{k=1}^m a_k`. -/
theorem sum_Icc_mul_eq_abel (a g : ℕ → ℝ) (N : ℕ) :
    ∑ m ∈ Icc 1 N, a m * g m = (∑ k ∈ Icc 1 N, a k) * g N +
      ∑ m ∈ Ico 1 N, (∑ k ∈ Icc 1 m, a k) * (g m - g (m + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), ih, sum_Icc_succ_top (by omega)]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · rw [sum_Ico_succ_top hN]
      ring

/-- Grouping a weighted sum by the values of `q ∈ [1, x]`. -/
theorem sum_eq_sum_Icc_fiber {β : Type*} (s : Finset β) (q : β → ℕ) (v : β → ℝ) (f : ℕ → ℝ)
    {x : ℕ} (hq : ∀ b ∈ s, q b ∈ Icc 1 x) :
    ∑ b ∈ s, v b * f (q b) = ∑ m ∈ Icc 1 x, (∑ b ∈ s.filter (fun b => q b = m), v b) * f m := by
  rw [← sum_fiberwise_of_maps_to hq]
  refine sum_congr rfl fun m _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun b hb => ?_
  rw [(mem_filter.mp hb).2]

/-- The partial sums of the grouped weights are the counting function. -/
theorem sum_Icc_fiber_eq {β : Type*} (s : Finset β) (q : β → ℕ) (v : β → ℝ)
    (hq1 : ∀ b ∈ s, 1 ≤ q b) (m : ℕ) :
    ∑ k ∈ Icc 1 m, ∑ b ∈ s.filter (fun b => q b = k), v b =
      ∑ b ∈ s.filter (fun b => q b ≤ m), v b := by
  rw [← sum_fiberwise_of_maps_to (s := s.filter fun b => q b ≤ m) (t := Icc 1 m) (g := q)
    (fun b hb => by
      rw [mem_filter] at hb
      exact mem_Icc.mpr ⟨hq1 b hb.1, hb.2⟩)]
  refine sum_congr rfl fun k hk => ?_
  rw [filter_filter]
  refine sum_congr (filter_congr fun b _ => ?_) fun _ _ => rfl
  constructor
  · intro h
    exact ⟨h ▸ (mem_Icc.mp hk).2, h⟩
  · exact fun h => h.2

/-- **Majorization**: weights `v` with counting function `Σ_{q(b) ≤ m} v_b ≤ Bm` sum against a
nonincreasing nonnegative `f` to at most `B Σ_{m ≤ x} f(m)`. -/
theorem sum_mul_le_of_count_le {β : Type*} (s : Finset β) (q : β → ℕ) (v : β → ℝ) {x : ℕ}
    (hq : ∀ b ∈ s, q b ∈ Icc 1 x) {f : ℕ → ℝ} (hf : ∀ m, 1 ≤ m → f (m + 1) ≤ f m)
    (hf0 : ∀ m, 1 ≤ m → 0 ≤ f m) {B : ℝ}
    (hcount : ∀ m, ∑ b ∈ s.filter (fun b => q b ≤ m), v b ≤ B * m) :
    ∑ b ∈ s, v b * f (q b) ≤ B * ∑ m ∈ Icc 1 x, f m := by
  have hq1 : ∀ b ∈ s, 1 ≤ q b := fun b hb => (mem_Icc.mp (hq b hb)).1
  have hA : ∀ m, ∑ k ∈ Icc 1 m, ∑ b ∈ s.filter (fun b => q b = k), v b ≤ m * B := fun m =>
    ((sum_Icc_fiber_eq s q v hq1 m).trans_le (hcount m)).trans_eq (mul_comm _ _)
  have hB := sum_Icc_mul_eq_abel (fun _ => B) f x
  simp only [sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul] at hB
  rw [sum_eq_sum_Icc_fiber s q v f hq, sum_Icc_mul_eq_abel, mul_sum, hB]
  refine add_le_add ?_ (sum_le_sum fun m hm => ?_)
  · rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · exact mul_le_mul_of_nonneg_right (hA x) (hf0 x hx)
  · exact mul_le_mul_of_nonneg_right (hA m) (sub_nonneg.mpr (hf m (mem_Ico.mp hm).1))

/-- **The logarithmic side**: nonnegative weights with counting function `≤ Bm` have
`Σ v_b log q(b) ≥ (Σ v_b) log x − Bx`. -/
theorem sum_mul_log_ge_of_count {β : Type*} (s : Finset β) (q : β → ℕ) (v : β → ℝ) {x : ℕ}
    (hq : ∀ b ∈ s, q b ∈ Icc 1 x) (hv : ∀ b ∈ s, 0 ≤ v b) {B : ℝ}
    (hcount : ∀ m, ∑ b ∈ s.filter (fun b => q b ≤ m), v b ≤ B * m) :
    (∑ b ∈ s, v b) * Real.log x - B * x ≤ ∑ b ∈ s, v b * Real.log (q b) := by
  have hq1 : ∀ b ∈ s, 1 ≤ q b := fun b hb => (mem_Icc.mp (hq b hb)).1
  have hA : ∀ m, ∑ k ∈ Icc 1 m, ∑ b ∈ s.filter (fun b => q b = k), v b ≤ B * m := fun m =>
    (sum_Icc_fiber_eq s q v hq1 m).trans_le (hcount m)
  have hA0 : ∀ m, 0 ≤ ∑ k ∈ Icc 1 m, ∑ b ∈ s.filter (fun b => q b = k), v b := fun m => by
    rw [sum_Icc_fiber_eq s q v hq1 m]
    exact sum_nonneg fun b hb => hv b (mem_filter.mp hb).1
  have hB0 : 0 ≤ B := by simpa using (hA0 1).trans (hA 1)
  have htot : ∑ k ∈ Icc 1 x, ∑ b ∈ s.filter (fun b => q b = k), v b = ∑ b ∈ s, v b := by
    rw [sum_Icc_fiber_eq s q v hq1 x, filter_true_of_mem fun b hb => (mem_Icc.mp (hq b hb)).2]
  rw [sum_eq_sum_Icc_fiber s q v (fun m => Real.log m) hq, sum_Icc_mul_eq_abel, htot]
  -- each Abel term is at least `−B`, since `log(m+1) − log m ≤ 1/m`
  have hterm : ∀ m ∈ Ico 1 x, -B ≤ (∑ k ∈ Icc 1 m, ∑ b ∈ s.filter (fun b => q b = k), v b) *
      (Real.log m - Real.log (m + 1 : ℕ)) := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (mem_Ico.mp hm).1
    have hm0 : (0 : ℝ) < m := by linarith
    have hlog : Real.log ((m + 1 : ℕ) : ℝ) - Real.log m ≤ 1 / m := by
      rw [← Real.log_div (by positivity) hm0.ne']
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((m + 1 : ℕ) : ℝ) / m by positivity)
      have : ((m + 1 : ℕ) : ℝ) / m - 1 = 1 / m := by
        push_cast
        field_simp
        ring
      linarith
    have h1 := mul_le_mul_of_nonneg_left hlog (hA0 m)
    have h2 : (∑ k ∈ Icc 1 m, ∑ b ∈ s.filter (fun b => q b = k), v b) * (1 / m) ≤ B := by
      rw [mul_one_div, div_le_iff₀ hm0]
      exact hA m
    have hlogm : 0 ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log m := by
      rw [sub_nonneg]
      exact Real.log_le_log hm0 (by push_cast; linarith)
    nlinarith
  have hsum := sum_le_sum hterm
  rw [sum_const, Nat.card_Ico, nsmul_eq_mul] at hsum
  have hcard : ((x - 1 : ℕ) : ℝ) ≤ x := by exact_mod_cast Nat.sub_le x 1
  have : -(B * x) ≤ ((x - 1 : ℕ) : ℝ) * -B := by nlinarith
  linarith

variable {K : Type*} [Field K] [NumberField K]

local notation "n" => finrank ℚ K

/-- The prime powers up to `x` with norm `≤ m` lie among those up to `m`. -/
theorem filter_primePowersLe_subset (x m : ℕ) :
    (primePowersLe K x).filter (fun pk => absNorm pk.1 ^ pk.2 ≤ m) ⊆ primePowersLe K m := by
  intro pk hpk
  rw [mem_filter, mem_primePowersLe] at hpk
  rw [mem_primePowersLe]
  exact ⟨hpk.1.1, hpk.1.2.1, hpk.1.2.2.1, hpk.2⟩

theorem mem_Icc_absNorm_pow {x : ℕ} {pk : Ideal (𝓞 K) × ℕ} (hpk : pk ∈ primePowersLe K x) :
    absNorm pk.1 ^ pk.2 ∈ Icc 1 x := by
  rw [mem_primePowersLe] at hpk
  have h2 := two_le_absNorm_of_isPrime hpk.1 hpk.2.1
  have hpos : 0 < absNorm pk.1 ^ pk.2 := pow_pos (by omega) _
  exact mem_Icc.mpr ⟨hpos, hpk.2.2.2⟩

/-- **The weighted prime sum**: `Σ_{N𝔭^k ≤ x} log N𝔭 (N𝔭^k)^{−σ} ≤ D Σ_{m ≤ x} m^{−σ}`. -/
theorem sum_log_mul_rpow_neg_le {σ : ℝ} (hσ : 0 ≤ σ) (x : ℕ) :
    ∑ pk ∈ primePowersLe K x, Real.log (absNorm pk.1) * (((absNorm pk.1 ^ pk.2 : ℕ) : ℝ) ^ (-σ)) ≤
      (finrank ℤ (𝓞 K) : ℝ) ^ 2 * (Real.log 4 + 4) * ∑ m ∈ Icc 1 x, (m : ℝ) ^ (-σ) := by
  refine sum_mul_le_of_count_le (primePowersLe K x) (fun pk => absNorm pk.1 ^ pk.2)
    (fun pk => Real.log (absNorm pk.1)) (fun pk hpk => mem_Icc_absNorm_pow hpk)
    (f := fun m => (m : ℝ) ^ (-σ)) (fun m hm => ?_) (fun m _ => by positivity) (fun m => ?_)
  · exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hm) (by push_cast; linarith)
      (by linarith)
  · calc ∑ pk ∈ (primePowersLe K x).filter (fun pk => absNorm pk.1 ^ pk.2 ≤ m),
          Real.log (absNorm pk.1)
        ≤ ∑ pk ∈ primePowersLe K m, Real.log (absNorm pk.1) :=
          sum_le_sum_of_subset_of_nonneg (filter_primePowersLe_subset x m)
            fun pk _ _ => log_absNorm_nonneg _
      _ ≤ (finrank ℤ (𝓞 K) : ℝ) ^ 2 * ((Real.log 4 + 4) * m) := sum_primePowersLe_log_le m
      _ = _ := by ring

/-- The ideal counting function is at most linear: `I_K(m) ≤ B' m` with `B' = c_K + B`. -/
theorem idealCount_le_of_weber {c B σ : ℝ} (hB : 0 ≤ B) (hσ1 : σ ≤ 1)
    (hup : ∀ t : ℕ, idealCount K t ≤ c * t + B * (t : ℝ) ^ σ) (m : ℕ) :
    idealCount K m ≤ (c + B) * m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [idealCount_zero, Nat.cast_zero, mul_zero]
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have := Real.rpow_le_rpow_of_exponent_le hm1 hσ1
    rw [Real.rpow_one] at this
    nlinarith [hup m]

/-- **Mertens' theorem for prime ideals with a bounded error**: `A_K(x) = log x + O(1)`. -/
theorem exists_abs_primeMertens_sub_log_le :
    ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x → |primeMertens K x - Real.log x| ≤ C := by
  obtain ⟨B₀, hB₀⟩ := exists_abs_idealCount_sub_le (K := K)
  have hc := dedekindZeta_residue_pos K
  set c := dedekindZeta_residue K with hcdef
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast finrank_pos
  set δ : ℝ := ((n : ℝ) + 1)⁻¹ with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 2 := by
    rw [hδdef, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  set σ : ℝ := 1 - δ with hσdef
  have hσ0 : 0 ≤ σ := by linarith
  have hσ1 : σ < 1 := by linarith
  have hB₀0 : 0 ≤ B₀ := by
    have := hB₀ 1 le_rfl
    simp only [Nat.cast_one, Real.one_rpow, mul_one] at this
    exact (abs_nonneg _).trans this
  -- Weber with exponent `σ` for all `t`
  have hexp : 1 - (n : ℝ)⁻¹ ≤ σ := by
    rw [hσdef, hδdef]
    have : ((n : ℝ) + 1)⁻¹ ≤ (n : ℝ)⁻¹ := inv_anti₀ (by positivity) (by linarith)
    linarith
  have hW : ∀ t : ℕ, |idealCount K t - c * t| ≤ B₀ * (t : ℝ) ^ σ := by
    intro t
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · rw [idealCount_zero, Nat.cast_zero, mul_zero, sub_zero, abs_zero,
        Real.zero_rpow (by linarith), mul_zero]
    · have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
      exact (hB₀ t ht).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le ht1 hexp) hB₀0)
  have hup : ∀ t : ℕ, idealCount K t ≤ c * t + B₀ * (t : ℝ) ^ σ := fun t => by
    have := (abs_le.mp (hW t)).2
    linarith
  have hlow : ∀ t : ℕ, c * t - B₀ * (t : ℝ) ^ σ ≤ idealCount K t := fun t => by
    have := (abs_le.mp (hW t)).1
    linarith
  set D : ℝ := (finrank ℤ (𝓞 K) : ℝ) ^ 2 * (Real.log 4 + 4) with hDdef
  have hD : 0 ≤ D := mul_nonneg (by positivity)
    (add_nonneg (Real.log_nonneg (by norm_num)) (by norm_num))
  refine ⟨(B₀ / δ + c * D + B₀ * D * (2 + 1 / δ) + (c + B₀)) / c, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (by omega : 1 ≤ x)
  -- `x^σ log x ≤ x/δ` and `x^σ · x^δ = x`
  have hxσδ : (x : ℝ) ^ σ * (x : ℝ) ^ δ = x := by
    rw [← Real.rpow_add hx0, hσdef, sub_add_cancel, Real.rpow_one]
  have hlogx : (x : ℝ) ^ σ * Real.log x ≤ x / δ := by
    have h := Real.log_le_rpow_div hx0.le hδ0
    calc (x : ℝ) ^ σ * Real.log x ≤ (x : ℝ) ^ σ * ((x : ℝ) ^ δ / δ) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = x / δ := by rw [mul_div_assoc', hxσδ]
  -- `S(x) = Σ log N𝔭 (N𝔭^k)^{−σ} ≤ D (2 + 1/δ) x^δ`
  have hS : ∑ pk ∈ primePowersLe K x, Real.log (absNorm pk.1) *
      (((absNorm pk.1 ^ pk.2 : ℕ) : ℝ) ^ (-σ)) ≤ D * ((2 + 1 / δ) * (x : ℝ) ^ δ) := by
    refine (sum_log_mul_rpow_neg_le hσ0 x).trans (mul_le_mul_of_nonneg_left ?_ hD)
    have hσpos : 0 < σ := by linarith
    have h := RHTower.Sieve.sum_rpow_neg_le_of_lt_one hσpos hσ1 hx
    have hxδ : (1 : ℝ) ≤ (x : ℝ) ^ δ := Real.one_le_rpow hx1 hδ0.le
    have hxneg : (x : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    rw [show 1 - σ = δ by rw [hσdef]; ring] at h
    have hδinv : 0 < 1 / δ := by positivity
    calc ∑ m ∈ Icc 1 x, (m : ℝ) ^ (-σ) ≤ 1 + ((x : ℝ) ^ δ - 1) / δ + (x : ℝ) ^ (-σ) := h
      _ ≤ 2 + (x : ℝ) ^ δ / δ := by
          have : ((x : ℝ) ^ δ - 1) / δ ≤ (x : ℝ) ^ δ / δ :=
            div_le_div_of_nonneg_right (by linarith) hδ0.le
          linarith
      _ ≤ (2 + 1 / δ) * (x : ℝ) ^ δ := by
          rw [add_mul, div_eq_mul_one_div ((x : ℝ) ^ δ) δ, mul_comm ((x : ℝ) ^ δ) (1 / δ)]
          nlinarith
  have hψ : primeChebyshev K x ≤ D * x := (primeChebyshev_le x).trans_eq (by rw [hDdef]; ring)
  -- the hyperbola identity, term by term
  have hid := sum_log_absNorm_idealsLe_eq (K := K) x
  have hterm : ∀ pk ∈ primePowersLe K x,
      c * x * (Real.log (absNorm pk.1) / (absNorm pk.1 ^ pk.2 : ℕ)) - c * Real.log (absNorm pk.1) -
        B₀ * (x : ℝ) ^ σ * (Real.log (absNorm pk.1) * (((absNorm pk.1 ^ pk.2 : ℕ) : ℝ) ^ (-σ))) ≤
        Real.log (absNorm pk.1) * ((idealsLe K (x / absNorm pk.1 ^ pk.2)).card : ℝ) ∧
      Real.log (absNorm pk.1) * ((idealsLe K (x / absNorm pk.1 ^ pk.2)).card : ℝ) ≤
        c * x * (Real.log (absNorm pk.1) / (absNorm pk.1 ^ pk.2 : ℕ)) +
          B₀ * (x : ℝ) ^ σ * (Real.log (absNorm pk.1) *
            (((absNorm pk.1 ^ pk.2 : ℕ) : ℝ) ^ (-σ))) := by
    intro pk hpk
    have hq := (mem_Icc.mp (mem_Icc_absNorm_pow hpk)).1
    have hq0 : (0 : ℝ) < (absNorm pk.1 ^ pk.2 : ℕ) := by exact_mod_cast hq
    set q : ℕ := absNorm pk.1 ^ pk.2
    set w := Real.log (absNorm pk.1)
    have hw : 0 ≤ w := log_absNorm_nonneg _
    have ht : ((x / q : ℕ) : ℝ) ≤ (x : ℝ) / q := Nat.cast_div_le
    have ht' := RHTower.Mertens.cast_div_lt x q hq
    have hrp : ((x / q : ℕ) : ℝ) ^ σ ≤ (x : ℝ) ^ σ * (q : ℝ) ^ (-σ) := by
      rw [Real.rpow_neg hq0.le, ← div_eq_mul_inv, ← Real.div_rpow hx0.le hq0.le]
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) ht hσ0
    have hxq : (x : ℝ) * (w / q) = w * ((x : ℝ) / q) := by ring
    change c * x * (w / q) - c * w - B₀ * (x : ℝ) ^ σ * (w * (q : ℝ) ^ (-σ)) ≤
        w * idealCount K (x / q) ∧
      w * idealCount K (x / q) ≤ c * x * (w / q) + B₀ * (x : ℝ) ^ σ * (w * (q : ℝ) ^ (-σ))
    constructor
    · have h1 := hlow (x / q)
      have h2 : c * ((x : ℝ) / q - 1) - B₀ * ((x : ℝ) ^ σ * (q : ℝ) ^ (-σ)) ≤
          idealCount K (x / q) := by
        have : c * ((x : ℝ) / q - 1) ≤ c * ((x / q : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left (by linarith) hc.le
        have : B₀ * ((x / q : ℕ) : ℝ) ^ σ ≤ B₀ * ((x : ℝ) ^ σ * (q : ℝ) ^ (-σ)) :=
          mul_le_mul_of_nonneg_left hrp hB₀0
        linarith
      have := mul_le_mul_of_nonneg_left h2 hw
      nlinarith
    · have h1 := hup (x / q)
      have h2 : idealCount K (x / q) ≤ c * ((x : ℝ) / q) +
          B₀ * ((x : ℝ) ^ σ * (q : ℝ) ^ (-σ)) := by
        have : c * ((x / q : ℕ) : ℝ) ≤ c * ((x : ℝ) / q) := mul_le_mul_of_nonneg_left ht hc.le
        have : B₀ * ((x / q : ℕ) : ℝ) ^ σ ≤ B₀ * ((x : ℝ) ^ σ * (q : ℝ) ^ (-σ)) :=
          mul_le_mul_of_nonneg_left hrp hB₀0
        linarith
      have := mul_le_mul_of_nonneg_left h2 hw
      nlinarith
  have hsumL := sum_le_sum fun pk hpk => (hterm pk hpk).1
  have hsumU := sum_le_sum fun pk hpk => (hterm pk hpk).2
  rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum, ← hid] at hsumL
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← hid] at hsumU
  change c * x * primeMertens K x - c * primeChebyshev K x - _ ≤ _ at hsumL
  change _ ≤ c * x * primeMertens K x + _ at hsumU
  -- the logarithmic side `L(x) = Σ_{N𝔞 ≤ x} log N𝔞`
  have hLup := sum_log_absNorm_idealsLe_le (K := K) x
  have hLlow : idealCount K x * Real.log x - (c + B₀) * x ≤
      ∑ I ∈ idealsLe K x, Real.log (absNorm I) := by
    have h := sum_mul_log_ge_of_count (idealsLe K x) (fun I => absNorm I) (fun _ => (1 : ℝ))
      (x := x) (fun I hI => by
        rw [mem_idealsLe] at hI
        exact mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr fun h => hI.1 (absNorm_eq_zero_iff.mp h),
          hI.2⟩)
      (fun _ _ => zero_le_one) (B := c + B₀) (fun m => ?_)
    · simp only [one_mul, sum_const, nsmul_eq_mul, mul_one] at h
      exact h
    · simp only [sum_const, nsmul_eq_mul, mul_one]
      calc (((idealsLe K x).filter fun I => absNorm I ≤ m).card : ℝ) ≤ idealCount K m := by
            refine Nat.cast_le.mpr (card_le_card fun I hI => ?_)
            rw [mem_filter, mem_idealsLe] at hI
            exact mem_idealsLe.mpr ⟨hI.1.1, hI.2⟩
        _ ≤ (c + B₀) * m := idealCount_le_of_weber hB₀0 hσ1.le hup m
  have hIx := hup x
  have hIx' := hlow x
  have hS' : B₀ * (x : ℝ) ^ σ * ∑ pk ∈ primePowersLe K x, Real.log (absNorm pk.1) *
      (((absNorm pk.1 ^ pk.2 : ℕ) : ℝ) ^ (-σ)) ≤ B₀ * D * (2 + 1 / δ) * x := by
    calc _ ≤ B₀ * (x : ℝ) ^ σ * (D * ((2 + 1 / δ) * (x : ℝ) ^ δ)) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = B₀ * D * (2 + 1 / δ) * ((x : ℝ) ^ σ * (x : ℝ) ^ δ) := by ring
      _ = B₀ * D * (2 + 1 / δ) * x := by rw [hxσδ]
  have hlogx' : B₀ * ((x : ℝ) ^ σ * Real.log x) ≤ B₀ * (x / δ) :=
    mul_le_mul_of_nonneg_left hlogx hB₀0
  have hIlog : idealCount K x * Real.log x ≤ (c * x + B₀ * (x : ℝ) ^ σ) * Real.log x :=
    mul_le_mul_of_nonneg_right hIx (Real.log_nonneg hx1)
  have hIlog' : (c * x - B₀ * (x : ℝ) ^ σ) * Real.log x ≤ idealCount K x * Real.log x :=
    mul_le_mul_of_nonneg_right hIx' (Real.log_nonneg hx1)
  have hcψ : c * primeChebyshev K x ≤ c * (D * x) := mul_le_mul_of_nonneg_left hψ hc.le
  -- `c x |A_K(x) − log x| ≤ x K₀`
  have hcx : 0 < c * x := mul_pos hc hx0
  have hcB : 0 ≤ (x : ℝ) * (c + B₀) := mul_nonneg hx0.le (add_nonneg hc.le hB₀0)
  have hcD : 0 ≤ c * D * x := mul_nonneg (mul_nonneg hc.le hD) hx0.le
  have hU : c * x * (primeMertens K x - Real.log x) ≤
      x * (B₀ / δ + c * D + B₀ * D * (2 + 1 / δ) + (c + B₀)) := by
    have : B₀ * ((x : ℝ) / δ) = x * (B₀ / δ) := by ring
    linarith
  have hLo : -(x * (B₀ / δ + c * D + B₀ * D * (2 + 1 / δ) + (c + B₀))) ≤
      c * x * (primeMertens K x - Real.log x) := by
    have : B₀ * ((x : ℝ) / δ) = x * (B₀ / δ) := by ring
    linarith
  have habs := abs_le.mpr ⟨hLo, hU⟩
  rw [abs_mul, abs_of_pos hcx] at habs
  rw [le_div_iff₀ hc]
  have h : |primeMertens K x - Real.log x| * c * x ≤
      (B₀ / δ + c * D + B₀ * D * (2 + 1 / δ) + (c + B₀)) * x := by
    linarith
  exact le_of_mul_le_mul_right h hx0

end GaloisForLFunctions.ArtinMertens
