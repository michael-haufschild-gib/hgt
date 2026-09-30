import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Counting near-resonant pairs for a multiplicative twist

For a twist `h/k` (`h, k ≥ 1`) and a pair `(M, N)` of positive integers, the pair is *near-resonant
at scale `δ`* if `Nk ≠ Mh` and `|log(N/M) − log(h/k)| < δ`, with `0 < δ ≤ 1/4`. Then:

* `N ≥ Mh/(2k)`, so `(MN)^{−1/2} ≤ √(2k/h)/M`;
* `1 ≤ |Nk − Mh| ≤ 2δ Mh`, so for fixed `M` there are at most `4δ Mh` such `N` (the map
  `N ↦ Nk − Mh` is injective into the nonzero integers of modulus at most `2δMh`).

With the weight `(MN)^{−1/2} min(1, L/(MN))` the near-resonant mass is therefore at most
`4δ √(2hk) Σ_M min(1, 2kL/(M²h))`. Since `Σ_M min(1, a/M²) ≤ 3√a` and `≤ 2a`, it is at most
`24 δ k √L` (`tsum_nearRes_le`), independent of the twist height `h`, and at most
`16 δ k L √(2k/h)` (`tsum_nearRes_le'`).
-/

noncomputable section

namespace RHTower.ZetaNotch

open Finset

/-! ## The one-dimensional sum `Σ_M min(1, a/M²)` -/

theorem summable_min_one_div_sq (a : ℝ) :
    Summable (fun M : ℕ => min 1 (a / ((M : ℝ) + 1) ^ 2)) := by
  have hs : Summable (fun M : ℕ => |a| / ((M : ℝ) + 1) ^ 2) := by
    have h := (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).comp_injective
      (add_left_injective 1)
    refine (h.mul_left |a|).congr fun M => ?_
    simp [div_eq_mul_inv]
  refine Summable.of_norm_bounded hs fun M => ?_
  rw [Real.norm_eq_abs]
  have hM : (0 : ℝ) < ((M : ℝ) + 1) ^ 2 := by positivity
  rcases le_total 0 (min 1 (a / ((M : ℝ) + 1) ^ 2)) with h | h
  · rw [abs_of_nonneg h]
    exact (min_le_right _ _).trans (div_le_div_of_nonneg_right (le_abs_self a) hM.le)
  · rw [abs_of_nonpos h]
    have : min 1 (a / ((M : ℝ) + 1) ^ 2) = a / ((M : ℝ) + 1) ^ 2 := by
      apply min_eq_right
      by_contra hc
      push Not at hc
      linarith [min_eq_left hc.le]
    rw [this, ← neg_div]
    exact div_le_div_of_nonneg_right (neg_le_abs a) hM.le

theorem tsum_inv_sq_le_two : ∑' M : ℕ, (((M : ℝ) + 1) ^ 2)⁻¹ ≤ 2 := by
  have hs : Summable (fun M : ℕ => (((M : ℝ) + 1) ^ 2)⁻¹) := by
    have h := (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).comp_injective
      (add_left_injective 1)
    simpa [Function.comp_def] using h
  refine Real.tsum_le_of_sum_range_le (fun M => by positivity) fun n => ?_
  have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (n + 1)
  have heq : ∑ M ∈ range n, (((M : ℝ) + 1) ^ 2)⁻¹ = ∑ i ∈ Ioo 0 (n + 1), ((i : ℝ) ^ 2)⁻¹ := by
    rw [range_eq_Ico]
    have := sum_Ico_add' (fun i : ℕ => ((i : ℝ) ^ 2)⁻¹) 0 n 1
    simp only [Nat.cast_add, Nat.cast_one, zero_add] at this
    rw [this]
    rfl
  rw [heq]
  refine h.trans ?_
  norm_num

/-- `Σ_{M ≥ 1} min(1, a/M²) ≤ 2a`. -/
theorem tsum_min_one_div_sq_le_two_mul {a : ℝ} (ha : 0 ≤ a) :
    ∑' M : ℕ, min 1 (a / ((M : ℝ) + 1) ^ 2) ≤ 2 * a := by
  have hs : Summable (fun M : ℕ => a * (((M : ℝ) + 1) ^ 2)⁻¹) := by
    have h := (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).comp_injective
      (add_left_injective 1)
    exact (by simpa [Function.comp_def] using h : Summable (fun M : ℕ => (((M : ℝ) + 1) ^ 2)⁻¹)).mul_left a
  calc ∑' M : ℕ, min 1 (a / ((M : ℝ) + 1) ^ 2) ≤ ∑' M : ℕ, a * (((M : ℝ) + 1) ^ 2)⁻¹ :=
        (summable_min_one_div_sq a).tsum_le_tsum (fun M => (min_le_right _ _).trans
          (le_of_eq (div_eq_mul_inv _ _))) hs
    _ = a * ∑' M : ℕ, (((M : ℝ) + 1) ^ 2)⁻¹ := tsum_mul_left
    _ ≤ a * 2 := mul_le_mul_of_nonneg_left tsum_inv_sq_le_two ha
    _ = 2 * a := by ring

/-- `Σ_{M ≥ 1} min(1, a/M²) ≤ 3√a`. -/
theorem tsum_min_one_div_sq_le_three_sqrt {a : ℝ} (ha : 0 ≤ a) :
    ∑' M : ℕ, min 1 (a / ((M : ℝ) + 1) ^ 2) ≤ 3 * Real.sqrt a := by
  rcases le_or_gt a 1 with ha1 | ha1
  · refine (tsum_min_one_div_sq_le_two_mul ha).trans ?_
    have : a ≤ Real.sqrt a := by
      have hs1 : Real.sqrt a ≤ 1 := Real.sqrt_le_one.mpr ha1
      have hs0 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
      calc a = Real.sqrt a * Real.sqrt a := (Real.mul_self_sqrt ha).symm
        _ ≤ Real.sqrt a * 1 := mul_le_mul_of_nonneg_left hs1 hs0
        _ = Real.sqrt a := mul_one _
    linarith [Real.sqrt_nonneg a]
  · set J : ℕ := ⌊Real.sqrt a⌋₊ with hJ
    have hsa : 1 < Real.sqrt a := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) ha1
    have hJ1 : 1 ≤ J := Nat.le_floor (by exact_mod_cast hsa.le)
    have hJle : (J : ℝ) ≤ Real.sqrt a := Nat.floor_le (Real.sqrt_nonneg a)
    have hJlt : Real.sqrt a < J + 1 := Nat.lt_floor_add_one _
    have hs := summable_min_one_div_sq a
    rw [← hs.sum_add_tsum_nat_add J]
    have hhead : ∑ M ∈ range J, min (1 : ℝ) (a / ((M : ℝ) + 1) ^ 2) ≤ (J : ℝ) := by
      calc ∑ M ∈ range J, min 1 (a / ((M : ℝ) + 1) ^ 2) ≤ ∑ M ∈ range J, (1 : ℝ) :=
            sum_le_sum fun M _ => min_le_left _ _
        _ = J := by simp
    have htail : ∑' M : ℕ, min 1 (a / (((M + J : ℕ) : ℝ) + 1) ^ 2) ≤ 2 * Real.sqrt a := by
      have hs2 : Summable (fun M : ℕ => a * ((((M + J : ℕ) : ℝ) + 1) ^ 2)⁻¹) := by
        have h := (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).comp_injective
          (add_left_injective (J + 1))
        refine (h.mul_left a).congr fun M => ?_
        simp only [Function.comp_apply]
        push_cast
        ring_nf
      calc ∑' M : ℕ, min 1 (a / (((M + J : ℕ) : ℝ) + 1) ^ 2)
          ≤ ∑' M : ℕ, a * ((((M + J : ℕ) : ℝ) + 1) ^ 2)⁻¹ :=
            (hs.comp_injective (add_left_injective J)).tsum_le_tsum
              (fun M => (min_le_right _ _).trans (le_of_eq (div_eq_mul_inv _ _))) hs2
        _ = a * ∑' M : ℕ, ((((M + J : ℕ) : ℝ) + 1) ^ 2)⁻¹ := tsum_mul_left
        _ ≤ a * (1 / J) := by
            apply mul_le_mul_of_nonneg_left _ ha
            refine Real.tsum_le_of_sum_range_le (fun M => by positivity) fun n => ?_
            have h := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := J) (n := J + n) (by omega) (by omega)
            have heq : ∑ M ∈ range n, ((((M + J : ℕ) : ℝ) + 1) ^ 2)⁻¹ =
                ∑ i ∈ Ioc J (J + n), ((i : ℝ) ^ 2)⁻¹ := by
              rw [range_eq_Ico]
              have := sum_Ico_add' (fun i : ℕ => ((i : ℝ) ^ 2)⁻¹) 0 n (J + 1)
              simp only [zero_add] at this
              rw [show Ioc J (J + n) = Ico (J + 1) (J + n + 1) by
                ext i; simp only [mem_Ioc, mem_Ico]; omega]
              rw [show J + n + 1 = n + (J + 1) by omega, ← this]
              refine sum_congr rfl fun M _ => ?_
              push_cast
              ring_nf
            rw [heq]
            refine h.trans ?_
            have : 0 ≤ (((J + n : ℕ) : ℝ))⁻¹ := by positivity
            rw [one_div]
            linarith
        _ ≤ 2 * Real.sqrt a := by
            have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ1
            rw [mul_one_div, div_le_iff₀ hJ0]
            have hsq : a = Real.sqrt a * Real.sqrt a := (Real.mul_self_sqrt ha).symm
            have hJ2 : Real.sqrt a ≤ 2 * J := by
              have : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
              linarith
            calc a = Real.sqrt a * Real.sqrt a := hsq
              _ ≤ Real.sqrt a * (2 * J) := mul_le_mul_of_nonneg_left hJ2 (Real.sqrt_nonneg a)
              _ = 2 * Real.sqrt a * J := by ring
    have hhead' : (J : ℝ) ≤ Real.sqrt a := hJle
    linarith

/-! ## Near-resonant pairs -/

/-- Near-resonance of the pair `(M, N) = (p.1+1, p.2+1)` with the twist `h/k` at scale `δ`. -/
def nearRes (h k : ℕ) (δ : ℝ) (p : ℕ × ℕ) : Prop :=
  (p.2 + 1) * k ≠ (p.1 + 1) * h ∧
    |Real.log (((p.2 : ℝ) + 1) / ((p.1 : ℝ) + 1)) - Real.log ((h : ℝ) / k)| < δ

instance (h k : ℕ) (δ : ℝ) (p : ℕ × ℕ) : Decidable (nearRes h k δ p) := Classical.dec _

/-- The pair weight `(MN)^{−1/2} min(1, L/(MN))`. -/
def pairWeight (L : ℝ) (p : ℕ × ℕ) : ℝ :=
  (Real.sqrt (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1)))⁻¹ *
    min 1 (L / (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1)))

theorem pairWeight_nonneg {L : ℝ} (hL : 0 ≤ L) (p : ℕ × ℕ) : 0 ≤ pairWeight L p := by
  unfold pairWeight
  apply mul_nonneg (by positivity)
  exact le_min zero_le_one (by positivity)

/-- The consequences of near-resonance: `N ≥ Mh/(2k)` and `1 ≤ |Nk − Mh| ≤ 2δ Mh`. -/
theorem nearRes_bounds {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) {δ : ℝ} (hδ1 : δ ≤ 1 / 4)
    {p : ℕ × ℕ} (hp : nearRes h k δ p) :
    ((p.1 : ℝ) + 1) * h / (2 * k) ≤ (p.2 : ℝ) + 1 ∧
      1 ≤ |((p.2 : ℝ) + 1) * k - ((p.1 : ℝ) + 1) * h| ∧
      |((p.2 : ℝ) + 1) * k - ((p.1 : ℝ) + 1) * h| ≤ 2 * δ * (((p.1 : ℝ) + 1) * h) := by
  obtain ⟨hne, hlog⟩ := hp
  set M : ℝ := (p.1 : ℝ) + 1 with hM
  set N : ℝ := (p.2 : ℝ) + 1 with hN
  have hM0 : 0 < M := by positivity
  have hN0 : 0 < N := by positivity
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hMh : 0 < M * h := by positivity
  have hNk : 0 < N * k := by positivity
  -- the logarithmic closeness gives the ratio window
  have hratio : Real.log (N * k / (M * h)) = Real.log (N / M) - Real.log (h / k) := by
    rw [show N * k / (M * h) = (N / M) / (h / k) by field_simp,
      Real.log_div (by positivity) (by positivity)]
  have habs : |Real.log (N * k / (M * h))| < δ := by rw [hratio]; exact hlog
  have hlo : Real.exp (-δ) < N * k / (M * h) := by
    have := (abs_lt.mp habs).1
    rw [← Real.exp_lt_exp, Real.exp_log (by positivity)] at this
    exact this
  have hhi : N * k / (M * h) < Real.exp δ := by
    have := (abs_lt.mp habs).2
    rw [← Real.exp_lt_exp, Real.exp_log (by positivity)] at this
    exact this
  have hexp1 : Real.exp δ ≤ 1 + 2 * δ := by
    have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (le_of_lt hlog)
    have := Real.exp_bound' (x := δ) hδ0 (by linarith) (n := 1) (by norm_num)
    simp at this
    nlinarith [Real.add_one_le_exp δ]
  have hexp2 : 1 - 2 * δ ≤ Real.exp (-δ) := by
    have := Real.add_one_le_exp (-δ)
    linarith
  have hlo' : (1 - 2 * δ) * (M * h) < N * k := by
    have := lt_of_le_of_lt hexp2 hlo
    rwa [lt_div_iff₀ hMh] at this
  have hhi' : N * k < (1 + 2 * δ) * (M * h) := by
    have := lt_of_lt_of_le hhi hexp1
    rwa [div_lt_iff₀ hMh] at this
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hδ1 hMh.le]
  · have hne' : ((p.2 + 1) * k : ℤ) ≠ ((p.1 + 1) * h : ℤ) := by exact_mod_cast hne
    have hint : ((p.2 + 1) * k : ℤ) - ((p.1 + 1) * h : ℤ) ≠ 0 := sub_ne_zero.mpr hne'
    have h1 : (1 : ℤ) ≤ |((p.2 + 1) * k : ℤ) - ((p.1 + 1) * h : ℤ)| := Int.one_le_abs hint
    have h2 : ((|((p.2 + 1) * k : ℤ) - ((p.1 + 1) * h : ℤ)| : ℤ) : ℝ) = |N * k - M * h| := by
      push_cast
      rfl
    rw [← h2]
    exact_mod_cast h1
  · rw [abs_le]
    constructor <;> nlinarith

/-- A near-resonant `N` is at most `2Mh`. -/
theorem nearRes_snd_lt {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) {δ : ℝ} (hδ1 : δ ≤ 1 / 4) {a b : ℕ}
    (hn : nearRes h k δ (a, b)) : b < 2 * (a + 1) * h := by
  obtain ⟨_, _, hub⟩ := nearRes_bounds hh hk hδ1 hn
  simp only at hub
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hn.2.le
  have hN : ((b : ℝ) + 1) * k ≤ 2 * (((a : ℝ) + 1) * h) := by
    have := (abs_le.mp hub).2
    have hMh : (0 : ℝ) ≤ ((a : ℝ) + 1) * h := by positivity
    nlinarith
  have hNnat : (b + 1) * k ≤ 2 * ((a + 1) * h) := by exact_mod_cast hN
  have hk' : b + 1 ≤ (b + 1) * k := Nat.le_mul_of_pos_right _ hk
  have e2 : 2 * (a + 1) * h = 2 * ((a + 1) * h) := by ring
  omega

/-- **Near-resonant mass, row by row.** For fixed `M`, the near-resonant `N` contribute at most
`4δ √(2hk) min(1, 2kL/(hM²))`. -/
theorem tsum_row_nearRes_le {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) {δ L : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 4) (hL : 0 < L) (a : ℕ) :
    ∑' b : ℕ, (if nearRes h k δ (a, b) then pairWeight L (a, b) else 0) ≤
      4 * δ * Real.sqrt (2 * h * k) *
        min 1 (2 * k * L / (h * ((a : ℝ) + 1) ^ 2)) := by
  set M : ℝ := (a : ℝ) + 1 with hM
  have hM0 : 0 < M := by positivity
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  -- the uniform bound on each near-resonant term
  set W : ℝ := Real.sqrt (2 * k / h) / M * min 1 (2 * k * L / (h * M ^ 2)) with hW
  have hterm : ∀ b, nearRes h k δ (a, b) → pairWeight L (a, b) ≤ W := by
    intro b hb
    obtain ⟨hNge, _, _⟩ := nearRes_bounds hh hk hδ1 hb
    simp only at hNge
    set N : ℝ := (b : ℝ) + 1
    have hN0 : 0 < N := by positivity
    have hMN : M * h / (2 * k) * M ≤ M * N := by nlinarith
    have hMNpos : 0 < M * h / (2 * k) * M := by positivity
    unfold pairWeight
    simp only
    apply mul_le_mul _ _ (le_min zero_le_one (by positivity)) (by positivity)
    · rw [show Real.sqrt (2 * k / h) / M = (Real.sqrt (M * h / (2 * k) * M))⁻¹ by
        rw [show M * h / (2 * k) * M = (h / (2 * k)) * M ^ 2 by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq hM0.le, mul_inv, ← Real.sqrt_inv, inv_div]
        ring]
      exact inv_anti₀ (Real.sqrt_pos.mpr hMNpos) (Real.sqrt_le_sqrt hMN)
    · apply min_le_min_left
      have hMhN : M * h ≤ 2 * k * N := by
        have := hNge
        rw [div_le_iff₀ (by positivity)] at this
        rw [hM]
        linarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have e1 : ((a : ℝ) + 1) * ((b : ℝ) + 1) = M * N := rfl
      rw [e1]
      nlinarith [mul_le_mul_of_nonneg_left hMhN (by positivity : (0 : ℝ) ≤ L * M)]
  -- the near-resonant set is finite: `N ≤ 2Mh`
  set Nmax : ℕ := 2 * (a + 1) * h with hNmax
  have hsupp : ∀ b ∉ Finset.range Nmax,
      (if nearRes h k δ (a, b) then pairWeight L (a, b) else 0) = 0 := by
    intro b hb
    rw [if_neg]
    intro hnear
    exact hb (Finset.mem_range.mpr (nearRes_snd_lt hh hk hδ1 hnear))
  rw [tsum_eq_sum (s := Finset.range Nmax) hsupp]
  -- bound each term by `W` on the near-resonant filter
  have hsum : ∑ b ∈ Finset.range Nmax, (if nearRes h k δ (a, b) then pairWeight L (a, b) else 0) ≤
      ∑ b ∈ (Finset.range Nmax).filter (fun b => nearRes h k δ (a, b)), W := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun b _ => ?_
    split_ifs with hb
    · exact hterm b hb
    · exact le_refl _
  refine hsum.trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  -- the card bound
  set R : ℕ := ⌊2 * δ * (M * h)⌋₊ with hR
  have hcard : ((Finset.range Nmax).filter (fun b => nearRes h k δ (a, b))).card ≤ 2 * R := by
    have hinj : Set.InjOn (fun b : ℕ => (((b + 1) * k : ℕ) : ℤ) - (((a + 1) * h : ℕ) : ℤ))
        ((Finset.range Nmax).filter (fun b => nearRes h k δ (a, b))) := by
      intro b₁ _ b₂ _ heq
      simp only at heq
      have : (b₁ + 1) * k = (b₂ + 1) * k := by exact_mod_cast (by linarith : (((b₁ + 1) * k : ℕ) : ℤ) =
        (((b₂ + 1) * k : ℕ) : ℤ))
      have := Nat.eq_of_mul_eq_mul_right hk this
      omega
    have hmaps : ∀ b ∈ (Finset.range Nmax).filter (fun b => nearRes h k δ (a, b)),
        (fun b : ℕ => (((b + 1) * k : ℕ) : ℤ) - (((a + 1) * h : ℕ) : ℤ)) b ∈
          (Finset.Icc (-(R : ℤ)) R).erase 0 := by
      intro b hb
      rw [Finset.mem_filter] at hb
      obtain ⟨_, hlow, hup⟩ := nearRes_bounds hh hk hδ1 hb.2
      simp only at hlow hup
      set r : ℤ := (((b + 1) * k : ℕ) : ℤ) - (((a + 1) * h : ℕ) : ℤ) with hr
      have hrR : ((r : ℤ) : ℝ) = ((b : ℝ) + 1) * k - ((a : ℝ) + 1) * h := by
        rw [hr]; push_cast; ring
      rw [Finset.mem_erase, Finset.mem_Icc]
      show r ≠ 0 ∧ -(R : ℤ) ≤ r ∧ r ≤ R
      have habs : |(r : ℝ)| ≤ 2 * δ * (M * h) := by rw [hrR]; exact hup
      have habs1 : 1 ≤ |(r : ℝ)| := by rw [hrR]; exact hlow
      have hrabs : |r| ≤ R := by
        have h1 : ((|r| : ℤ) : ℝ) ≤ 2 * δ * (M * h) := by push_cast; exact habs
        have h2 : (|r| : ℤ) ≤ ⌊2 * δ * (M * h)⌋ := Int.le_floor.mpr h1
        have h3 : (⌊2 * δ * (M * h)⌋ : ℤ) = (⌊2 * δ * (M * h)⌋₊ : ℤ) := by
          rw [Int.natCast_floor_eq_floor (by positivity)]
        rw [h3] at h2
        exact h2
      refine ⟨?_, ?_, ?_⟩
      · intro hr0
        rw [hr0] at habs1
        norm_num at habs1
      · have := neg_abs_le r
        linarith
      · exact (le_abs_self r).trans hrabs
    have h := Finset.card_le_card_of_injOn _ hmaps hinj
    refine h.trans ?_
    rw [Finset.card_erase_of_mem (by simp), Int.card_Icc]
    omega
  have hRle : (R : ℝ) ≤ 2 * δ * (M * h) := Nat.floor_le (by positivity)
  have hW0 : 0 ≤ W := by
    rw [hW]
    apply mul_nonneg (by positivity)
    exact le_min zero_le_one (by positivity)
  calc (((Finset.range Nmax).filter (fun b => nearRes h k δ (a, b))).card : ℝ) * W
      ≤ (2 * R : ℝ) * W := by
        apply mul_le_mul_of_nonneg_right _ hW0
        exact_mod_cast hcard
    _ ≤ (2 * (2 * δ * (M * h))) * W := by gcongr
    _ = 4 * δ * Real.sqrt (2 * h * k) * min 1 (2 * k * L / (h * M ^ 2)) := by
        rw [hW]
        have hsq : Real.sqrt (2 * k / h) * h = Real.sqrt (2 * h * k) := by
          rw [show 2 * (h : ℝ) * k = (2 * k / h) * h ^ 2 by field_simp,
            Real.sqrt_mul (by positivity), Real.sqrt_sq hh0.le]
        rw [← hsq]
        field_simp
        norm_num

/-- Each row of the near-resonant weight has finite support. -/
theorem summable_row_nearRes {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) {δ : ℝ} (hδ1 : δ ≤ 1 / 4)
    (L : ℝ) (a : ℕ) :
    Summable (fun b : ℕ => if nearRes h k δ (a, b) then pairWeight L (a, b) else 0) := by
  refine summable_of_ne_finset_zero (s := Finset.range (2 * (a + 1) * h)) fun b hb => ?_
  rw [if_neg]
  intro hn
  exact hb (Finset.mem_range.mpr (nearRes_snd_lt hh hk hδ1 hn))

theorem summable_nearRes {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) {δ L : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 4) (hL : 0 < L) :
    Summable (fun p : ℕ × ℕ => if nearRes h k δ p then pairWeight L p else 0) := by
  have hnn : 0 ≤ (fun p : ℕ × ℕ => if nearRes h k δ p then pairWeight L p else 0) := fun p => by
    simp only [Pi.zero_apply]
    split_ifs
    · exact pairWeight_nonneg hL.le p
    · exact le_refl _
  refine (summable_prod_of_nonneg hnn).mpr ⟨summable_row_nearRes hh hk hδ1 L, ?_⟩
  refine Summable.of_nonneg_of_le (fun a => tsum_nonneg fun b => hnn (a, b))
    (fun a => tsum_row_nearRes_le hh hk hδ0 hδ1 hL a) ?_
  refine ((summable_min_one_div_sq (2 * k * L / h)).mul_left
    (4 * δ * Real.sqrt (2 * h * k))).congr fun a => ?_
  rw [div_div]

/-- The near-resonant mass as a sum of row sums. -/
theorem tsum_nearRes_le_rows {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) {δ L : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 4) (hL : 0 < L) :
    ∑' p : ℕ × ℕ, (if nearRes h k δ p then pairWeight L p else 0) ≤
      4 * δ * Real.sqrt (2 * h * k) * ∑' a : ℕ, min 1 (2 * k * L / h / ((a : ℝ) + 1) ^ 2) := by
  rw [(summable_nearRes hh hk hδ0 hδ1 hL).tsum_prod' (summable_row_nearRes hh hk hδ1 L),
    ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun a => ?_) ?_ ((summable_min_one_div_sq _).mul_left _)
  · refine (tsum_row_nearRes_le hh hk hδ0 hδ1 hL a).trans (le_of_eq ?_)
    rw [div_div]
  · exact ((summable_prod_of_nonneg fun p => by
      simp only [Pi.zero_apply]
      split_ifs
      · exact pairWeight_nonneg hL.le p
      · exact le_refl _).mp (summable_nearRes hh hk hδ0 hδ1 hL)).2

/-- **Near-resonant mass, uniform in the twist height.** -/
theorem tsum_nearRes_le {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) {δ L : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 4) (hL : 0 < L) :
    ∑' p : ℕ × ℕ, (if nearRes h k δ p then pairWeight L p else 0) ≤ 24 * δ * k * Real.sqrt L := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  refine (tsum_nearRes_le_rows hh hk hδ0 hδ1 hL).trans ?_
  have ha : 0 ≤ 2 * k * L / h := by positivity
  calc 4 * δ * Real.sqrt (2 * h * k) * ∑' a : ℕ, min 1 (2 * k * L / h / ((a : ℝ) + 1) ^ 2)
      ≤ 4 * δ * Real.sqrt (2 * h * k) * (3 * Real.sqrt (2 * k * L / h)) := by
        gcongr
        exact tsum_min_one_div_sq_le_three_sqrt ha
    _ = 12 * δ * Real.sqrt (2 * h * k * (2 * k * L / h)) := by
        rw [Real.sqrt_mul (show (0 : ℝ) ≤ 2 * h * k by positivity) (2 * k * L / h)]
        ring
    _ = 24 * δ * k * Real.sqrt L := by
        rw [show 2 * (h : ℝ) * k * (2 * k * L / h) = (2 * k) ^ 2 * L by field_simp,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
        ring

/-- **Near-resonant mass, decaying in the twist height.** -/
theorem tsum_nearRes_le' {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) {δ L : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 4) (hL : 0 < L) :
    ∑' p : ℕ × ℕ, (if nearRes h k δ p then pairWeight L p else 0) ≤
      16 * δ * k * L * Real.sqrt (2 * k / h) := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  refine (tsum_nearRes_le_rows hh hk hδ0 hδ1 hL).trans ?_
  have ha : 0 ≤ 2 * k * L / h := by positivity
  calc 4 * δ * Real.sqrt (2 * h * k) * ∑' a : ℕ, min 1 (2 * k * L / h / ((a : ℝ) + 1) ^ 2)
      ≤ 4 * δ * Real.sqrt (2 * h * k) * (2 * (2 * k * L / h)) := by
        gcongr
        exact tsum_min_one_div_sq_le_two_mul ha
    _ = 16 * δ * k * L * (Real.sqrt (2 * h * k) / h) := by ring
    _ = 16 * δ * k * L * Real.sqrt (2 * k / h) := by
        congr 1
        rw [show 2 * (h : ℝ) * k = (2 * k / h) * h ^ 2 by field_simp,
          Real.sqrt_mul (by positivity), Real.sqrt_sq hh0.le]
        field_simp

/-- Near-resonance is symmetric under exchanging the pair and inverting the twist. -/
theorem nearRes_swap {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) {δ : ℝ} (p : ℕ × ℕ) :
    nearRes k h δ p.swap ↔ nearRes h k δ p := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  unfold nearRes
  simp only [Prod.fst_swap, Prod.snd_swap]
  have hp1 : ((p.1 : ℝ) + 1) ≠ 0 := by positivity
  have hp2 : ((p.2 : ℝ) + 1) ≠ 0 := by positivity
  have hlog : Real.log (((p.1 : ℝ) + 1) / ((p.2 : ℝ) + 1)) - Real.log ((k : ℝ) / h) =
      -(Real.log (((p.2 : ℝ) + 1) / ((p.1 : ℝ) + 1)) - Real.log ((h : ℝ) / k)) := by
    rw [Real.log_div hp1 hp2, Real.log_div hp2 hp1, Real.log_div hk0.ne' hh0.ne',
      Real.log_div hh0.ne' hk0.ne']
    ring
  rw [hlog, abs_neg]
  constructor
  · rintro ⟨hne, hlt⟩
    exact ⟨fun he => hne he.symm, hlt⟩
  · rintro ⟨hne, hlt⟩
    exact ⟨fun he => hne he.symm, hlt⟩

theorem pairWeight_swap (L : ℝ) (p : ℕ × ℕ) : pairWeight L p.swap = pairWeight L p := by
  unfold pairWeight
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [mul_comm ((p.2 : ℝ) + 1)]

/-- The near-resonant mass for the inverted twist, in swapped coordinates. -/
theorem tsum_nearRes_swap_eq {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) (δ L : ℝ) :
    ∑' p : ℕ × ℕ, (if nearRes k h δ p then pairWeight L p else 0) =
      ∑' p : ℕ × ℕ, (if nearRes h k δ p then pairWeight L p else 0) := by
  rw [← (Equiv.prodComm ℕ ℕ).tsum_eq]
  congr 1
  ext p
  simp only [Equiv.prodComm_apply]
  rw [if_congr (nearRes_swap hh hk p) (pairWeight_swap L p) rfl]

end RHTower.ZetaNotch
