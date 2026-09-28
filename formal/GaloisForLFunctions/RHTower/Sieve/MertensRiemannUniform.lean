import GaloisForLFunctions.RHTower.Sieve.MertensSecondSharp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Uniform Mertens–Riemann sums

For `0 < a₀ ≤ l ≤ r ≤ b₀` and a function `g` bounded by `M` and `L`-Lipschitz on `[l, r]`,

`∑_{y^l < p ≤ y^r} g(log p / log y) / p = ∫_l^r g(α)/α dα + o(1)`

uniformly in `l, r, g`.  The proof partitions `[l, r]` into `K` equal cells, uses Mertens' second
theorem with its `O(1/log N)` error on each cell (`Sieve.abs_mertensS_sub_logLog_sub_const_le`),
and pays `LΔ` for freezing `g` on a cell.
-/

namespace RHTower.Sieve

open Real Filter Topology Finset

noncomputable section

/-- The prime sum `∑_{y^l < p ≤ y^r} g(log p / log y)/p`. -/
def primeScaleSum (y l r : ℝ) (g : ℝ → ℝ) : ℝ :=
  ∑ p ∈ (Finset.Ioc ⌊y ^ l⌋₊ ⌊y ^ r⌋₊).filter Nat.Prime, g (log p / log y) / p

theorem sum_Ioc_prime_inv_eq_mertensS_sub {N M : ℕ} (h : N ≤ M) :
    ∑ p ∈ (Finset.Ioc N M).filter Nat.Prime, 1 / (p : ℝ) = mertensS M - mertensS N := by
  unfold mertensS
  rw [Nat.primesLE_eq_filter_range, Nat.primesLE_eq_filter_range, eq_sub_iff_add_eq,
    ← Finset.sum_union]
  · congr 1
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
    constructor
    · rintro (⟨⟨h1, h2⟩, hp⟩ | ⟨h1, hp⟩) <;> exact ⟨by omega, hp⟩
    · rintro ⟨h1, hp⟩
      by_cases hpN : p ≤ N
      · exact Or.inr ⟨by omega, hp⟩
      · exact Or.inl ⟨⟨by omega, by omega⟩, hp⟩
  · rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hp hp'
    omega

/-- The Mertens error numerator. -/
def mertensSecondErrorConst : ℝ := 2 * mertensFirstConst + 1 / 2

theorem mertensSecondErrorConst_nonneg : 0 ≤ mertensSecondErrorConst := by
  unfold mertensSecondErrorConst; have := mertensFirstConst_nonneg; linarith

/-- `log log ⌊y^γ⌋` is within `2 log 2/(γ log y)` of `log (γ log y)` once `y^γ ≥ 4`. -/
theorem abs_log_log_floor_rpow_sub_le {y γ : ℝ} (hy : 1 < y) (hγ : 0 < γ) (h4 : 4 ≤ y ^ γ) :
    |log (log (⌊y ^ γ⌋₊ : ℝ)) - log (γ * log y)| ≤ 2 * log 2 / (γ * log y) := by
  have hly : 0 < log y := Real.log_pos hy
  have hv : 0 < γ * log y := mul_pos hγ hly
  have hpos : (0 : ℝ) < y ^ γ := by linarith
  have hfl1 : (⌊y ^ γ⌋₊ : ℝ) ≤ y ^ γ := Nat.floor_le hpos.le
  have hfl2 : y ^ γ / 2 ≤ (⌊y ^ γ⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (y ^ γ); linarith
  have hN0 : (0 : ℝ) < ⌊y ^ γ⌋₊ := by linarith
  have hlogrpow : log (y ^ γ) = γ * log y := Real.log_rpow (by linarith) γ
  have hu1 : log (⌊y ^ γ⌋₊ : ℝ) ≤ γ * log y := by
    rw [← hlogrpow]; exact Real.log_le_log hN0 hfl1
  have hu2 : γ * log y - log 2 ≤ log (⌊y ^ γ⌋₊ : ℝ) := by
    have := Real.log_le_log (by positivity) hfl2
    rw [Real.log_div hpos.ne' (by norm_num), hlogrpow] at this
    exact this
  have h2 : 2 * log 2 ≤ γ * log y := by
    have := Real.log_le_log (by norm_num) h4
    rw [hlogrpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at this
    push_cast at this; linarith
  have hu0 : γ * log y / 2 ≤ log (⌊y ^ γ⌋₊ : ℝ) := by linarith
  have hupos : 0 < log (⌊y ^ γ⌋₊ : ℝ) := by linarith
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (Real.log_le_log hupos hu1)),
    ← Real.log_div hv.ne' hupos.ne']
  have hq : 1 ≤ γ * log y / log (⌊y ^ γ⌋₊ : ℝ) := by rw [le_div_iff₀ hupos]; linarith
  calc log (γ * log y / log (⌊y ^ γ⌋₊ : ℝ))
      ≤ γ * log y / log (⌊y ^ γ⌋₊ : ℝ) - 1 := Real.log_le_sub_one_of_pos (by linarith)
    _ = (γ * log y - log (⌊y ^ γ⌋₊ : ℝ)) / log (⌊y ^ γ⌋₊ : ℝ) := by field_simp
    _ ≤ log 2 / (γ * log y / 2) :=
        div_le_div₀ (by positivity) (by linarith) (by positivity) hu0
    _ = 2 * log 2 / (γ * log y) := by field_simp

/-- Mertens' second theorem on `(y^α, y^β]`, uniformly for `a₀ ≤ α ≤ β` once `y^{a₀} ≥ 4`. -/
theorem abs_sum_prime_inv_rpow_sub_log_le {a₀ α β y : ℝ} (ha₀ : 0 < a₀) (hy : 1 < y)
    (hy4 : 4 ≤ y ^ a₀) (hα : a₀ ≤ α) (hαβ : α ≤ β) :
    |∑ p ∈ (Finset.Ioc ⌊y ^ α⌋₊ ⌊y ^ β⌋₊).filter Nat.Prime, 1 / (p : ℝ) - log (β / α)|
      ≤ (4 * mertensSecondErrorConst + 4) / (a₀ * log y) := by
  have hly : 0 < log y := Real.log_pos hy
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < β := by linarith
  have h4α : 4 ≤ y ^ α := hy4.trans (Real.rpow_le_rpow_of_exponent_le hy.le hα)
  have h4β : 4 ≤ y ^ β := h4α.trans (Real.rpow_le_rpow_of_exponent_le hy.le hαβ)
  have hNαβ : ⌊y ^ α⌋₊ ≤ ⌊y ^ β⌋₊ := Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hy.le hαβ)
  have hN2 : ∀ γ : ℝ, 4 ≤ y ^ γ → 2 ≤ ⌊y ^ γ⌋₊ := fun γ h =>
    Nat.le_floor (by push_cast; linarith)
  rw [sum_Ioc_prime_inv_eq_mertensS_sub hNαβ]
  have hMα := abs_mertensS_sub_logLog_sub_const_le (hN2 α h4α)
  have hMβ := abs_mertensS_sub_logLog_sub_const_le (hN2 β h4β)
  have hLα := abs_log_log_floor_rpow_sub_le hy hα0 h4α
  have hLβ := abs_log_log_floor_rpow_sub_le hy hβ0 h4β
  have hlogN : ∀ γ, 0 < γ → 4 ≤ y ^ γ → γ * log y / 2 ≤ log (⌊y ^ γ⌋₊ : ℝ) := by
    intro γ hγ h4
    have hpos : (0 : ℝ) < y ^ γ := by linarith
    have hfl2 : y ^ γ / 2 ≤ (⌊y ^ γ⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one (y ^ γ); linarith
    have hlogrpow : log (y ^ γ) = γ * log y := Real.log_rpow (by linarith) γ
    have hu2 : γ * log y - log 2 ≤ log (⌊y ^ γ⌋₊ : ℝ) := by
      have := Real.log_le_log (by positivity) hfl2
      rw [Real.log_div hpos.ne' (by norm_num), hlogrpow] at this
      exact this
    have h2 : 2 * log 2 ≤ γ * log y := by
      have := Real.log_le_log (by norm_num) h4
      rw [hlogrpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at this
      push_cast at this; linarith
    linarith
  have hC := mertensSecondErrorConst_nonneg
  have hEα : mertensSecondErrorConst / log (⌊y ^ α⌋₊ : ℝ) ≤ 2 * mertensSecondErrorConst / (a₀ * log y) := by
    have h1 := hlogN α hα0 h4α
    have h2 : a₀ * log y / 2 ≤ α * log y / 2 := by
      have := mul_le_mul_of_nonneg_right hα hly.le; linarith
    rw [show 2 * mertensSecondErrorConst / (a₀ * log y) = mertensSecondErrorConst / (a₀ * log y / 2) by
      field_simp]
    exact div_le_div_of_nonneg_left hC (by positivity) (h2.trans h1)
  have hEβ : mertensSecondErrorConst / log (⌊y ^ β⌋₊ : ℝ) ≤ 2 * mertensSecondErrorConst / (a₀ * log y) := by
    have h1 := hlogN β hβ0 h4β
    have h2 : a₀ * log y / 2 ≤ β * log y / 2 := by
      have := mul_le_mul_of_nonneg_right (hα.trans hαβ) hly.le; linarith
    rw [show 2 * mertensSecondErrorConst / (a₀ * log y) = mertensSecondErrorConst / (a₀ * log y / 2) by
      field_simp]
    exact div_le_div_of_nonneg_left hC (by positivity) (h2.trans h1)
  have hTα : 2 * log 2 / (α * log y) ≤ 2 / (a₀ * log y) := by
    apply div_le_div₀ (by norm_num) (by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]) (by positivity)
    exact mul_le_mul_of_nonneg_right hα hly.le
  have hTβ : 2 * log 2 / (β * log y) ≤ 2 / (a₀ * log y) := by
    apply div_le_div₀ (by norm_num) (by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]) (by positivity)
    exact mul_le_mul_of_nonneg_right (hα.trans hαβ) hly.le
  have hlogq : log (β / α) = log (β * log y) - log (α * log y) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1; field_simp
  unfold mertensSecondErrorConst at hMα hMβ hEα hEβ ⊢
  unfold logLog at hMα hMβ
  rw [hlogq]
  have e : (4 * (2 * mertensFirstConst + 1 / 2) + 4) / (a₀ * log y)
      = 2 * (2 * mertensFirstConst + 1 / 2) / (a₀ * log y)
        + 2 * (2 * mertensFirstConst + 1 / 2) / (a₀ * log y)
        + 2 / (a₀ * log y) + 2 / (a₀ * log y) := by ring
  rw [e]
  rw [abs_le] at hMα hMβ hLα hLβ ⊢
  constructor <;> linarith [hMα.1, hMα.2, hMβ.1, hMβ.2, hLα.1, hLα.2, hLβ.1, hLβ.2]

theorem sum_range_sum_Ioc_eq {f : ℕ → ℝ} {N : ℕ → ℕ} (hN : Monotone N) (K : ℕ) :
    ∑ j ∈ Finset.range K, ∑ p ∈ Finset.Ioc (N j) (N (j + 1)), f p =
      ∑ p ∈ Finset.Ioc (N 0) (N K), f p := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Ioc_consecutive _ (hN (Nat.zero_le K))
      (hN (Nat.le_succ K))]

/-- The partition error of a Mertens–Riemann sum with `K` equal cells. -/
theorem abs_primeScaleSum_sub_integral_le {a₀ M L y l r : ℝ} {g : ℝ → ℝ} (K : ℕ) (hK : 0 < K)
    (ha₀ : 0 < a₀) (hy : 1 < y) (hy4 : 4 ≤ y ^ a₀) (hl : a₀ ≤ l) (hlr : l ≤ r)
    (hM : ∀ α ∈ Set.Icc l r, |g α| ≤ M)
    (hL : ∀ α ∈ Set.Icc l r, ∀ β ∈ Set.Icc l r, |g α - g β| ≤ L * |α - β|) (hL0 : 0 ≤ L) :
    |primeScaleSum y l r g - (∫ α in l..r, g α / α)| ≤
      2 * L * ((r - l) / K) * log (r / l)
        + (L * ((r - l) / K) + M) * K * ((4 * mertensSecondErrorConst + 4) / (a₀ * log y)) := by
  set Δ := (r - l) / K with hΔ
  set e := (4 * mertensSecondErrorConst + 4) / (a₀ * log y) with he
  have hly : 0 < log y := Real.log_pos hy
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hΔ0 : 0 ≤ Δ := div_nonneg (by linarith) hK0.le
  have hl0 : 0 < l := by linarith
  set α : ℕ → ℝ := fun j => l + j * Δ with hα
  have hαmono : Monotone α := fun i j hij => by
    simp only [hα]; have : (i : ℝ) ≤ j := by exact_mod_cast hij
    nlinarith
  have hαK : α K = r := by simp only [hα, hΔ]; field_simp; ring
  have hα0 : α 0 = l := by simp [hα]
  have hαl : ∀ j, l ≤ α j := fun j => by rw [← hα0]; exact hαmono (Nat.zero_le j)
  have hαr : ∀ j, j ≤ K → α j ≤ r := fun j hj => by rw [← hαK]; exact hαmono hj
  have hαsucc : ∀ j, α (j + 1) - α j = Δ := fun j => by simp only [hα]; push_cast; ring
  have hMg : 0 ≤ M := (abs_nonneg _).trans (hM l ⟨le_rfl, hlr⟩)
  have he0 : 0 ≤ e := div_nonneg (by linarith [mertensSecondErrorConst_nonneg]) (by positivity)
  set N : ℕ → ℕ := fun j => ⌊y ^ α j⌋₊ with hN
  have hNmono : Monotone N := fun i j hij =>
    Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hy.le (hαmono hij))
  -- the prime sum splits over cells
  have hsum : primeScaleSum y l r g = ∑ j ∈ Finset.range K,
      ∑ p ∈ (Finset.Ioc (N j) (N (j + 1))).filter Nat.Prime, g (log p / log y) / p := by
    unfold primeScaleSum
    simp_rw [Finset.sum_filter]
    rw [sum_range_sum_Ioc_eq hNmono K]
    simp only [hN, hα0, hαK]
  -- the integral splits over cells
  have hgc : ContinuousOn (fun a => g a / a) (Set.Icc l r) := by
    have hgcont : ContinuousOn g (Set.Icc l r) := by
      intro a ha
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      by_cases hL0' : L = 0
      · refine ⟨1, one_pos, fun b hb _ => ?_⟩
        have := hL b hb a ha
        rw [hL0', zero_mul] at this
        rw [Real.dist_eq]; linarith [abs_nonneg (g b - g a)]
      · have hLpos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hL0')
        refine ⟨ε / L, div_pos hε hLpos, fun b hb hdist => ?_⟩
        rw [Real.dist_eq] at hdist ⊢
        calc |g b - g a| ≤ L * |b - a| := hL b hb a ha
          _ < L * (ε / L) := by gcongr
          _ = ε := by field_simp
    exact hgcont.div continuousOn_id (fun a ha => (hl0.trans_le ha.1).ne')
  have hint : ∫ a in l..r, g a / a = ∑ j ∈ Finset.range K, ∫ a in α j..α (j + 1), g a / a := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (fun j hj =>
      (hgc.mono (Set.Icc_subset_Icc (hαl j) (hαr (j + 1) (by omega)))).intervalIntegrable_of_Icc
        (hαmono (Nat.le_succ j))), hα0, hαK]
  rw [hsum, hint, ← Finset.sum_sub_distrib]
  -- the per-cell estimate
  have hcell : ∀ j ∈ Finset.range K,
      |∑ p ∈ (Finset.Ioc (N j) (N (j + 1))).filter Nat.Prime, g (log p / log y) / p
        - (∫ a in α j..α (j + 1), g a / a)|
        ≤ L * Δ * (2 * log (α (j + 1) / α j) + e) + M * e := by
    intro j hj
    have hj' : j + 1 ≤ K := Finset.mem_range.mp hj
    have hαj0 : 0 < α j := hl0.trans_le (hαl j)
    have hαjj : α j ≤ α (j + 1) := hαmono (Nat.le_succ j)
    have hmem : ∀ p ∈ (Finset.Ioc (N j) (N (j + 1))).filter Nat.Prime,
        log p / log y ∈ Set.Icc (α j) (α (j + 1)) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Ioc, hN] at hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.Prime.pos hp.2
      constructor
      · rw [le_div_iff₀ hly]
        have h1 : y ^ α j < p := by
          have := Nat.lt_floor_add_one (y ^ α j)
          have h2 : ((⌊y ^ α j⌋₊ : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast hp.1.1
          linarith
        have := Real.log_lt_log (by positivity) h1
        rw [Real.log_rpow (by linarith)] at this
        linarith
      · rw [div_le_iff₀ hly]
        have h1 : (p : ℝ) ≤ y ^ α (j + 1) :=
          (Nat.cast_le.mpr hp.1.2).trans (Nat.floor_le (by positivity))
        have := Real.log_le_log hp0 h1
        rwa [Real.log_rpow (by linarith)] at this
    set S := ∑ p ∈ (Finset.Ioc (N j) (N (j + 1))).filter Nat.Prime, 1 / (p : ℝ) with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg (fun p _ => by positivity)
    have hmert := abs_sum_prime_inv_rpow_sub_log_le ha₀ hy hy4 (hl.trans (hαl j)) hαjj
    rw [← hS] at hmert
    have hA : |∑ p ∈ (Finset.Ioc (N j) (N (j + 1))).filter Nat.Prime, g (log p / log y) / p
        - g (α j) * S| ≤ L * Δ * S := by
      rw [hS, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun p hp => ?_))
      have hp0 : (0 : ℝ) < p := by
        simp only [Finset.mem_filter] at hp; exact_mod_cast Nat.Prime.pos hp.2
      have hm := hmem p hp
      have hgl := hL (log p / log y) ⟨(hαl j).trans hm.1, hm.2.trans (hαr (j + 1) hj')⟩
        (α j) ⟨hαl j, (hαjj).trans (hαr (j + 1) hj')⟩
      have hd : |log p / log y - α j| ≤ Δ := by
        rw [abs_le]; constructor <;> linarith [hm.1, hm.2, hαsucc j]
      rw [show g (log p / log y) / p - g (α j) * (1 / p) = (g (log p / log y) - g (α j)) / p by ring,
        abs_div, abs_of_pos hp0, show L * Δ * (1 / (p : ℝ)) = L * Δ / p by ring]
      exact div_le_div_of_nonneg_right (hgl.trans (mul_le_mul_of_nonneg_left hd hL0)) hp0.le
    have hB : |(∫ a in α j..α (j + 1), g a / a) - g (α j) * log (α (j + 1) / α j)|
        ≤ L * Δ * log (α (j + 1) / α j) := by
      have hlogint : ∫ a in α j..α (j + 1), g (α j) / a = g (α j) * log (α (j + 1) / α j) := by
        rw [show (fun a => g (α j) / a) = fun a => g (α j) * a⁻¹ by ext a; ring,
          intervalIntegral.integral_const_mul, integral_inv_of_pos hαj0 (hαj0.trans_le hαjj)]
      have hcj : ContinuousOn (fun a => g a / a) (Set.Icc (α j) (α (j + 1))) :=
        hgc.mono (Set.Icc_subset_Icc (hαl j) (hαr (j + 1) hj'))
      have i1 : IntervalIntegrable (fun a => g a / a) MeasureTheory.volume (α j) (α (j + 1)) :=
        hcj.intervalIntegrable_of_Icc hαjj
      have i2 : IntervalIntegrable (fun a => g (α j) / a) MeasureTheory.volume (α j) (α (j + 1)) :=
        (show ContinuousOn (fun a => g (α j) / a) (Set.Icc (α j) (α (j + 1))) from
          continuousOn_const.div continuousOn_id (fun a ha =>
            (hαj0.trans_le ha.1).ne')).intervalIntegrable_of_Icc hαjj
      rw [← hlogint, ← intervalIntegral.integral_sub i1 i2]
      calc |∫ a in α j..α (j + 1), (g a / a - g (α j) / a)|
          ≤ ∫ a in α j..α (j + 1), L * Δ / a := by
            refine intervalIntegral.abs_integral_le_integral_abs hαjj |>.trans
              (intervalIntegral.integral_mono_on hαjj ?_ ?_ ?_)
            · exact ((hcj.sub (continuousOn_const.div continuousOn_id (fun a ha =>
                (hαj0.trans_le ha.1).ne'))).abs).intervalIntegrable_of_Icc hαjj
            · exact (continuousOn_const.div continuousOn_id (fun a ha =>
                (hαj0.trans_le ha.1).ne')).intervalIntegrable_of_Icc hαjj
            · intro a ha
              have ha0 : 0 < a := hαj0.trans_le ha.1
              have hgl := hL a ⟨(hαl j).trans ha.1, ha.2.trans (hαr (j + 1) hj')⟩
                (α j) ⟨hαl j, hαjj.trans (hαr (j + 1) hj')⟩
              have hd : |a - α j| ≤ Δ := by
                rw [abs_le]; constructor <;> linarith [ha.1, ha.2, hαsucc j]
              rw [show g a / a - g (α j) / a = (g a - g (α j)) / a by ring, abs_div,
                abs_of_pos ha0]
              exact div_le_div_of_nonneg_right (hgl.trans (mul_le_mul_of_nonneg_left hd hL0))
                ha0.le
        _ = L * Δ * log (α (j + 1) / α j) := by
            rw [show (fun a => L * Δ / a) = fun a => (L * Δ) * a⁻¹ by ext a; ring,
              intervalIntegral.integral_const_mul, integral_inv_of_pos hαj0 (hαj0.trans_le hαjj)]
    have hgj : |g (α j)| ≤ M := hM (α j) ⟨hαl j, hαjj.trans (hαr (j + 1) hj')⟩
    have hSle : S ≤ log (α (j + 1) / α j) + e := by
      have := (abs_le.mp hmert).2; linarith
    have hge : |g (α j) * S - g (α j) * log (α (j + 1) / α j)| ≤ M * e := by
      rw [← mul_sub, abs_mul]
      exact mul_le_mul hgj hmert (abs_nonneg _) hMg
    have hLS : L * Δ * S ≤ L * Δ * (log (α (j + 1) / α j) + e) :=
      mul_le_mul_of_nonneg_left hSle (mul_nonneg hL0 hΔ0)
    have := abs_sub_le (∑ p ∈ (Finset.Ioc (N j) (N (j + 1))).filter Nat.Prime,
      g (log p / log y) / p) (g (α j) * S) (∫ a in α j..α (j + 1), g a / a)
    have := abs_sub_le (g (α j) * S) (g (α j) * log (α (j + 1) / α j))
      (∫ a in α j..α (j + 1), g a / a)
    rw [abs_sub_comm (g (α j) * log (α (j + 1) / α j))] at this
    nlinarith
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hcell).trans ?_)
  have hlogsum : ∑ j ∈ Finset.range K, log (α (j + 1) / α j) = log (r / l) := by
    have : ∀ j ∈ Finset.range K, log (α (j + 1) / α j) = log (α (j + 1)) - log (α j) :=
      fun j _ => Real.log_div (hl0.trans_le (hαl (j + 1))).ne' (hl0.trans_le (hαl j)).ne'
    rw [Finset.sum_congr rfl this, Finset.sum_range_sub (fun j => log (α j)), hαK, hα0,
      Real.log_div (by linarith) hl0.ne']
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
    hlogsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  nlinarith [mul_nonneg hL0 hΔ0, he0, hMg, hK0.le]

/-- **Uniform Mertens–Riemann sums.**  For fixed `0 < a₀`, `b₀`, `M`, `L ≥ 0` and `η > 0`,
eventually in `y`, every `g` bounded by `M` and `L`-Lipschitz on `[l, r] ⊂ [a₀, b₀]` satisfies
`|∑_{y^l < p ≤ y^r} g(log p/log y)/p - ∫_l^r g(α)/α dα| ≤ η`. -/
theorem eventually_abs_primeScaleSum_sub_integral_le {a₀ b₀ M L η : ℝ} (ha₀ : 0 < a₀)
    (hη : 0 < η) (hL0 : 0 ≤ L) :
    ∀ᶠ y : ℝ in atTop, ∀ l r : ℝ, a₀ ≤ l → l ≤ r → r ≤ b₀ → ∀ g : ℝ → ℝ,
      (∀ α ∈ Set.Icc l r, |g α| ≤ M) →
      (∀ α ∈ Set.Icc l r, ∀ β ∈ Set.Icc l r, |g α - g β| ≤ L * |α - β|) →
      |primeScaleSum y l r g - (∫ α in l..r, g α / α)| ≤ η := by
  set D := max (b₀ - a₀) 0 with hD
  set Λ := max (log (b₀ / a₀)) 0 with hΛ
  obtain ⟨K, hK⟩ := exists_nat_gt (4 * L * D * Λ / η)
  set K' := K + 1 with hK'
  have hK'0 : (0 : ℝ) < K' := by positivity
  have hfirst : 2 * L * (D / K') * Λ ≤ η / 2 := by
    have hKgt : 4 * L * D * Λ / η < K' := by push_cast [hK']; linarith
    rw [div_lt_iff₀ hη] at hKgt
    have hD0 : 0 ≤ D := le_max_right _ _
    have hΛ0 : 0 ≤ Λ := le_max_right _ _
    rw [show 2 * L * (D / K') * Λ = (2 * L * D * Λ) / K' by ring, div_le_iff₀ hK'0]
    nlinarith
  set E := 4 * mertensSecondErrorConst + 4 with hE
  have hE0 : 0 ≤ E := by have := mertensSecondErrorConst_nonneg; linarith
  set C := (L * (D / K') + max M 0) * K' * E / a₀ with hC
  have hC0 : 0 ≤ C := by
    have : 0 ≤ L * (D / K') := mul_nonneg hL0 (div_nonneg (le_max_right _ _) hK'0.le)
    have : 0 ≤ max M 0 := le_max_right _ _
    positivity
  have hlog : ∀ᶠ y : ℝ in atTop, 2 * C / η ≤ log y :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  have h4 : ∀ᶠ y : ℝ in atTop, 4 ≤ y ^ a₀ :=
    (tendsto_rpow_atTop ha₀).eventually_ge_atTop 4
  filter_upwards [hlog, h4, eventually_gt_atTop (1 : ℝ)] with y hly hy4 hy1
  intro l r hl hlr hr g hM hLg
  have hly0 : 0 < log y := Real.log_pos hy1
  have hbound := abs_primeScaleSum_sub_integral_le (a₀ := a₀) (M := max M 0) K' (by omega) ha₀ hy1
    hy4 hl hlr (fun α hα => (hM α hα).trans (le_max_left _ _)) hLg hL0
  refine hbound.trans ?_
  have hl0 : 0 < l := ha₀.trans_le hl
  have hΔ : (r - l) / K' ≤ D / K' :=
    div_le_div_of_nonneg_right ((by linarith : r - l ≤ b₀ - a₀).trans (le_max_left _ _)) hK'0.le
  have hΔ0 : 0 ≤ (r - l) / K' := div_nonneg (by linarith) hK'0.le
  have hlogrl : log (r / l) ≤ Λ := by
    refine (Real.log_le_log (div_pos (hl0.trans_le hlr) hl0) ?_).trans (le_max_left _ _)
    exact div_le_div₀ (by linarith) hr ha₀ hl
  have hlogrl0 : 0 ≤ log (r / l) := Real.log_nonneg (by rw [le_div_iff₀ hl0]; linarith)
  have hsecond : (L * ((r - l) / K') + max M 0) * K' * (E / (a₀ * log y)) ≤ η / 2 := by
    have h1 : (L * ((r - l) / K') + max M 0) * K' * (E / (a₀ * log y)) ≤ C / log y := by
      have hLΔ : L * ((r - l) / K') ≤ L * (D / K') := mul_le_mul_of_nonneg_left hΔ hL0
      have hmul : (L * ((r - l) / K') + max M 0) * K' * E / a₀
          ≤ (L * (D / K') + max M 0) * K' * E / a₀ := by
        apply div_le_div_of_nonneg_right _ ha₀.le
        apply mul_le_mul_of_nonneg_right _ hE0
        exact mul_le_mul_of_nonneg_right (by linarith) hK'0.le
      calc (L * ((r - l) / K') + max M 0) * K' * (E / (a₀ * log y))
          = (L * ((r - l) / K') + max M 0) * K' * E / a₀ / log y := by
            field_simp
        _ ≤ C / log y := div_le_div_of_nonneg_right hmul hly0.le
    refine h1.trans ?_
    rw [div_le_iff₀ hly0]
    rw [div_le_iff₀ hη] at hly
    linarith
  have hfirst' : 2 * L * ((r - l) / K') * log (r / l) ≤ η / 2 := by
    refine le_trans ?_ hfirst
    have := mul_le_mul hΔ hlogrl hlogrl0 (div_nonneg (le_max_right _ _) hK'0.le)
    nlinarith
  linarith

end

end RHTower.Sieve
