import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartIsEulersConstant
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonCountertermIsATensorProduct

/-!
# The finite part is the tower form

On uniform profiles the finite part of the horizon renormalization is the scalar `−2γ`
(`TheFinitePartIsEulersConstant`). On the `p`-adic valuation classes it is a matrix, and this file
computes it: the local tower form of `p` (AIT `TheTowerFormOfAPrime`), shifted by a local Euler
constant.

* **The local Mertens sum** (`tendsto_pPowerMertensSum`, `tendsto_unitMertensSum_sub_log`): the
  powers of `p` contribute `Σ_k log p/p^k → log p/(p − 1)`, so
  `A_{p'}(y) = Σ_{t ≤ y, p ∤ t} Λ(t)/t = log y − γ_p + o(1)` with the **local Euler constant**
  `γ_p = γ + log p/(p − 1)`.
* **Class masses** (`tendsto_unitHarmonic_sub`, `tendsto_classMass_sub`):
  `|w_j^{(M)}|² = δ_j (log M − j log p + γ_p) + o(1)`.
* **The rows inside a class are exact** (`sum_divisors_dvd_vonMangoldt_eq`, `classRow_self_eq`): for
  `v_p(m) = j`, `classRow_j(m) = A_{p'}(⌊M/m⌋) + log m − j log p`.
* **The rows across classes are one prime power** (`classRow_of_lt`,
  `primeBilinear_classPole_cross_eq`): for `j < j'` and `v_p(m) = j'`, `classRow_j(m) = log p`
  exactly, so `⟨w_{j'}, P w_j⟩ = log p |w_{j'}|²`.
* **The finite part inside a class** (`exists_abs_classGram_self_finitePart_le`):
  `⟨w_j^{(M)}, P w_j^{(M)}⟩ = δ_j^{−1} |w_j|⁴ − 2γ_p |w_j|² + o(|w_j|²)`.
* **The finite part on the classes** (`exists_abs_atomicWeilForm_classCombination_finitePart_le`): for
  `x = Σ_{j ≤ J} a_j w_j^{(M)}`,

      P_M(x) = Σ_j δ_j^{−1} ℓ_j(x)² − 2γ_p Σ_j a_j² |w_j|² + log p Σ_{j ≠ j'} a_j a_{j'} |w_{max(j, j')}|² + o(·).

In the normalized coordinates `b_j = a_j |w_j|` the coupling `|w_{max}|²/(|w_j| |w_{j'}|)` tends to
`√(δ_{max}/δ_{min}) = p^{−|j − j'|/2}` (`classDensity_add`): the finite part is
`−2γ_p · 1 + log p (K_{p^{−1/2}} − 1)`, the tower form of `p` with the local Euler constant on the
diagonal. Summed over all classes the tower couplings give back `2 Σ_j j δ_j log p = 2 log p/(p − 1)`,
which cancels the local Euler shift: the uniform finite part `−2γ` is recovered. The finite part of
the horizon renormalization is the local Hodge index structure of AIT, carried by the torsion orbits
of `μ_{p^∞}`.
-/

noncomputable section

open Filter Topology Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

local notation "γ" => Real.eulerMascheroniConstant

variable {p : ℕ}

/-! ### The local Mertens sum -/

/-- The local Euler constant `γ_p = γ + log p/(p − 1)`. -/
def localEuler (p : ℕ) : ℝ := γ + Real.log p / ((p : ℝ) - 1)

/-- The contribution of the powers of `p` to Mertens' sum: `Σ_{t ≤ y, p ∣ t} Λ(t)/t`. -/
def pPowerMertensSum (p y : ℕ) : ℝ := ∑ t ∈ Icc 1 y, (if p ∣ t then Λ t / t else 0)

/-- The Mertens sum over the units of `p`: `A_{p'}(y) = Σ_{t ≤ y, p ∤ t} Λ(t)/t`. -/
def unitMertensSum (p y : ℕ) : ℝ := ∑ t ∈ Icc 1 y, (if p ∣ t then 0 else Λ t / t)

theorem unitMertensSum_eq (p y : ℕ) : unitMertensSum p y = mertensSum y - pPowerMertensSum p y := by
  rw [unitMertensSum, mertensSum, pPowerMertensSum, ← sum_sub_distrib]
  exact sum_congr rfl fun t _ => by split_ifs <;> ring

/-- The first `K` powers of `p` give `(log p/(p − 1))(1 − p^{−K})`. -/
theorem pPowerMertensSum_ge (hp : p.Prime) {K y : ℕ} (hK : p ^ K ≤ y) :
    Real.log p / ((p : ℝ) - 1) * (1 - (1 / (p : ℝ)) ^ K) ≤ pPowerMertensSum p y := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp1.le
  have hinj : Set.InjOn (fun k => p ^ (k + 1)) (range K : Set ℕ) := fun a _ b _ h =>
    by simpa using Nat.pow_right_injective hp.two_le h
  have hsub : (range K).image (fun k => p ^ (k + 1)) ⊆ Icc 1 y := by
    intro t ht
    obtain ⟨k, hk, rfl⟩ := mem_image.mp ht
    refine mem_Icc.mpr ⟨Nat.one_le_pow _ _ hp.pos, ?_⟩
    exact (Nat.pow_le_pow_right hp.pos (by simpa using hk)).trans hK
  have hgeo : ∀ K' : ℕ, ∑ k ∈ range K', Real.log p / (p : ℝ) ^ (k + 1) =
      Real.log p / ((p : ℝ) - 1) * (1 - (1 / (p : ℝ)) ^ K') := by
    intro K'
    induction K' with
    | zero => simp
    | succ K' ih =>
      rw [Finset.sum_range_succ, ih]
      have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp
      ring
  calc Real.log p / ((p : ℝ) - 1) * (1 - (1 / (p : ℝ)) ^ K)
      = ∑ k ∈ range K, Real.log p / (p : ℝ) ^ (k + 1) := (hgeo K).symm
    _ = ∑ t ∈ (range K).image (fun k => p ^ (k + 1)), (if p ∣ t then Λ t / t else 0) := by
        rw [sum_image hinj]
        refine sum_congr rfl fun k _ => ?_
        rw [if_pos (dvd_pow_self p (Nat.succ_ne_zero k)), vonMangoldt_prime_pow hp (by omega)]
        push_cast; rfl
    _ ≤ pPowerMertensSum p y :=
        sum_le_sum_of_subset_of_nonneg hsub fun t _ _ => by
          split_ifs
          · exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
          · exact le_rfl

/-- **The powers of `p` sum to `log p/(p − 1)`.** -/
theorem tendsto_pPowerMertensSum (hp : p.Prime) :
    Tendsto (pPowerMertensSum p) atTop (𝓝 (Real.log p / ((p : ℝ) - 1))) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp1.le
  set L := Real.log p / ((p : ℝ) - 1)
  have hL : 0 ≤ L := div_nonneg hlogp (by linarith)
  rw [Metric.tendsto_atTop]
  intro η hη
  -- `(1/p)^K → 0`
  have hr0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hr1 : (1 : ℝ) / p < 1 := by rw [div_lt_one (by linarith)]; exact hp1
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show 0 < η / (L + 1) by positivity) hr1
  refine ⟨p ^ K, fun y hy => ?_⟩
  have hlow := pPowerMertensSum_ge hp hy
  have hup : pPowerMertensSum p y ≤ L := sum_dvd_vonMangoldt_div_le hp _
  rw [Real.dist_eq, abs_lt]
  have hpow : 0 ≤ (1 / (p : ℝ)) ^ K := by positivity
  have h1 : L * (1 / (p : ℝ)) ^ K < η := by
    calc L * (1 / (p : ℝ)) ^ K ≤ (L + 1) * (1 / (p : ℝ)) ^ K :=
          mul_le_mul_of_nonneg_right (by linarith) hpow
      _ < (L + 1) * (η / (L + 1)) := mul_lt_mul_of_pos_left hK (by linarith)
      _ = η := by field_simp
  constructor <;> nlinarith

/-- **The local Mertens theorem**: `A_{p'}(y) − log y → −γ_p`. -/
theorem tendsto_unitMertensSum_sub_log (hp : p.Prime) :
    Tendsto (fun y : ℕ => unitMertensSum p y - Real.log y) atTop (𝓝 (-localEuler p)) := by
  have h := tendsto_mertensSum_sub_log.sub (tendsto_pPowerMertensSum hp)
  have hlim : -localEuler p = -γ - Real.log p / ((p : ℝ) - 1) := by unfold localEuler; ring
  rw [hlim]
  refine h.congr fun y => ?_
  rw [unitMertensSum_eq]; ring

/-! ### Class masses -/

/-- `log ⌊X/d⌋ − log X + log d → 0` as `X → ∞`. -/
theorem tendsto_log_div_sub (d : ℕ) (hd : 0 < d) :
    Tendsto (fun X : ℕ => Real.log ((X / d : ℕ) : ℝ) - Real.log X + Real.log d) atTop (𝓝 0) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  -- the ratio `d ⌊X/d⌋ / X` lies in `((X − d)/X, 1]`
  have hratio : Tendsto (fun X : ℕ => (d : ℝ) * ((X / d : ℕ) : ℝ) / X) atTop (𝓝 1) := by
    have hlow : Tendsto (fun X : ℕ => 1 - (d : ℝ) / X) atTop (𝓝 1) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (d : ℝ)).const_sub 1
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with X hX
      have hX' : (0 : ℝ) < X := by exact_mod_cast hX
      have hlt := RHTower.Mertens.cast_div_lt X d hd
      rw [div_lt_iff₀ hd'] at hlt
      rw [show (1 : ℝ) - d / X = (X - d) / X by field_simp]
      exact div_le_div_of_nonneg_right (by nlinarith) hX'.le
    · filter_upwards [eventually_gt_atTop 0] with X hX
      have hX' : (0 : ℝ) < X := by exact_mod_cast hX
      rw [div_le_one hX']
      have := (Nat.cast_div_le (α := ℝ) (m := X) (n := d))
      rw [le_div_iff₀ hd'] at this
      linarith
  have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  rw [Real.log_one] at hlog
  refine hlog.congr' ?_
  filter_upwards [eventually_ge_atTop d] with X hX
  have hq : 1 ≤ X / d := (Nat.le_div_iff_mul_le hd).mpr (by linarith)
  have hX' : (0 : ℝ) < X := by exact_mod_cast hd.trans_le hX
  simp only [Function.comp]
  rw [Real.log_div (by positivity) hX'.ne', Real.log_mul hd'.ne' (by positivity)]
  ring

/-- **Units below `X`**: `Σ_{k ≤ X, p ∤ k} 1/k − (1 − 1/p) log X → (1 − 1/p)γ + log p/p`. -/
theorem tendsto_unitHarmonic_sub (hp : p.Prime) :
    Tendsto (fun X : ℕ => unitHarmonic p X - (1 - 1 / (p : ℝ)) * Real.log X) atTop
      (𝓝 ((1 - 1 / (p : ℝ)) * γ + Real.log p / p)) := by
  have h1 := tendsto_harmonicSum_sub_log
  have hdiv : Tendsto (fun X : ℕ => X / p) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨b * p, fun X hX =>
      (Nat.le_div_iff_mul_le hp.pos).mpr hX⟩
  have h2 := h1.comp hdiv
  have h3 := tendsto_log_div_sub p hp.pos
  have h := (h1.sub ((h2.add h3).div_const (p : ℝ))).add_const (Real.log p / p)
  have hlim : (1 - 1 / (p : ℝ)) * γ + Real.log p / p = γ - (γ + 0) / p + Real.log p / p := by ring
  rw [hlim]
  refine h.congr fun X => ?_
  simp only [Function.comp, unitHarmonic_eq hp]
  ring

/-- **Class masses**: `|w_j^{(M)}|² − δ_j (log M − j log p + γ_p) → 0`. -/
theorem tendsto_classMass_sub (hp : p.Prime) (j : ℕ) :
    Tendsto (fun M : ℕ => classMass p j M -
      classDensity p j * (Real.log M - j * Real.log p + localEuler p)) atTop (𝓝 0) := by
  have hpj : 0 < p ^ j := pow_pos hp.pos j
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hdiv : Tendsto (fun M : ℕ => M / p ^ j) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨b * p ^ j, fun M hM =>
      (Nat.le_div_iff_mul_le hpj).mpr hM⟩
  have hU := (tendsto_unitHarmonic_sub hp).comp hdiv
  have hlog := tendsto_log_div_sub (p ^ j) hpj
  -- `classMass = U(⌊M/p^j⌋)/p^j`
  have h := ((hU.add ((tendsto_const_nhds (x := (1 - 1 / (p : ℝ)))).mul hlog)).div_const
    ((p : ℝ) ^ j))
  have hlim : ((1 - 1 / (p : ℝ)) * γ + Real.log p / p + (1 - 1 / (p : ℝ)) * 0) / (p : ℝ) ^ j -
      classDensity p j * localEuler p = 0 := by
    unfold classDensity localEuler
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  have h' := h.sub_const (classDensity p j * localEuler p)
  rw [hlim] at h'
  refine h'.congr' (Eventually.of_forall fun M => ?_)
  simp only [Function.comp, classMass_eq_unitHarmonic hp, classDensity]
  rw [Nat.cast_pow, Real.log_pow]
  have hp0 : (p : ℝ) ^ j ≠ 0 := by positivity
  field_simp
  ring

/-! ### The rows -/

/-- **The `p`-atoms dividing `m`, exactly**: `Σ_{t ∣ m, p ∣ t} Λ(t) = v_p(m) log p`. -/
theorem sum_divisors_dvd_vonMangoldt_eq (hp : p.Prime) {m : ℕ} (hm : m ≠ 0) :
    ∑ t ∈ m.divisors, (if p ∣ t then Λ t else 0) = m.factorization p * Real.log p := by
  refine le_antisymm (sum_divisors_dvd_vonMangoldt_le hp hm) ?_
  set v := m.factorization p
  have hinj : Set.InjOn (fun k => p ^ (k + 1)) (range v : Set ℕ) := fun a _ b _ h =>
    by simpa using Nat.pow_right_injective hp.two_le h
  have hsub : (range v).image (fun k => p ^ (k + 1)) ⊆ m.divisors := by
    intro t ht
    obtain ⟨k, hk, rfl⟩ := mem_image.mp ht
    rw [Nat.mem_divisors]
    exact ⟨(hp.pow_dvd_iff_le_factorization hm).mpr (by simpa using hk), hm⟩
  calc (v : ℝ) * Real.log p = ∑ k ∈ range v, Real.log p := by
        rw [sum_const, card_range, nsmul_eq_mul]
    _ = ∑ t ∈ (range v).image (fun k => p ^ (k + 1)), (if p ∣ t then Λ t else 0) := by
        rw [sum_image hinj]
        refine sum_congr rfl fun k _ => ?_
        rw [if_pos (dvd_pow_self p (Nat.succ_ne_zero k)), vonMangoldt_prime_pow hp (by omega)]
    _ ≤ ∑ t ∈ m.divisors, (if p ∣ t then Λ t else 0) :=
        sum_le_sum_of_subset_of_nonneg hsub fun t _ _ => by
          split_ifs
          · exact vonMangoldt_nonneg
          · exact le_rfl

/-- `v_p(mt) = v_p(m)` iff `p ∤ t`, for `m, t ≠ 0`. -/
theorem factorization_mul_eq_iff (hp : p.Prime) {m t : ℕ} (hm : m ≠ 0) (ht : t ≠ 0) :
    (m * t).factorization p = m.factorization p ↔ ¬ p ∣ t := by
  rw [Nat.factorization_mul hm ht, Finsupp.add_apply, hp.dvd_iff_one_le_factorization ht]
  omega

/-- The up-tower term of a class row: `n = mt` stays in the class iff `p ∤ t`. -/
theorem classRow_up_term (hp : p.Prime) {j m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hv : m.factorization p = j) :
    (if n.factorization p = j then (if m ∣ n ∧ m ≠ n then Λ (n / m) / ((n / m : ℕ) : ℝ) else 0)
      else 0) =
      if m ∣ n then (if p ∣ n / m then 0 else Λ (n / m) / ((n / m : ℕ) : ℝ)) else 0 := by
  by_cases hmn : m ∣ n
  · obtain ⟨t, rfl⟩ := hmn
    have ht : t ≠ 0 := by rintro rfl; simp at hn
    rw [if_pos (dvd_mul_right m t), Nat.mul_div_cancel_left t hm]
    by_cases ht1 : t = 1
    · subst ht1; simp
    · have hne : m ≠ m * t := fun h => ht1 (Nat.eq_of_mul_eq_mul_left hm (by rw [← h, mul_one]))
      have hiff : (m * t).factorization p = j ↔ ¬ p ∣ t := by
        rw [← hv]; exact factorization_mul_eq_iff hp hm.ne' ht
      by_cases hpt : p ∣ t
      · rw [if_neg (fun h => (hiff.mp h) hpt), if_pos hpt]
      · rw [if_pos (hiff.mpr hpt), if_neg hpt, if_pos ⟨dvd_mul_right m t, hne⟩]
  · rw [if_neg hmn]
    split_ifs with h1 h2
    · exact absurd h2.1 hmn
    · rfl
    · rfl

/-- The down-tower term of a class row: `n = m/t` stays in the class iff `p ∤ t`. -/
theorem classRow_down_term (hp : p.Prime) {j m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hv : m.factorization p = j) :
    (if n.factorization p = j then (if n ∣ m ∧ n ≠ m then Λ (m / n) else 0) else 0) =
      if n ∣ m then (if p ∣ m / n then 0 else Λ (m / n)) else 0 := by
  by_cases hnm : n ∣ m
  · obtain ⟨t, ht⟩ := hnm
    have ht0 : t ≠ 0 := by rintro rfl; rw [mul_zero] at ht; omega
    have hmn : m / n = t := by rw [ht, Nat.mul_div_cancel_left t hn]
    have hdvd : n ∣ m := ⟨t, ht⟩
    rw [if_pos hdvd, hmn]
    by_cases ht1 : t = 1
    · subst ht1
      rw [mul_one] at ht
      subst ht
      simp
    · have hne : n ≠ m := fun h => ht1 (Nat.eq_of_mul_eq_mul_left hn (by rw [← ht, h, mul_one]))
      have hiff : n.factorization p = j ↔ ¬ p ∣ t := by
        rw [← hv, ht, eq_comm]; exact factorization_mul_eq_iff hp hn.ne' ht0
      by_cases hpt : p ∣ t
      · rw [if_neg (fun h => (hiff.mp h) hpt), if_pos hpt]
      · rw [if_pos (hiff.mpr hpt), if_neg hpt, if_pos ⟨hdvd, hne⟩]
  · rw [if_neg hnm]
    split_ifs with h1 h2
    · exact absurd h2.1 hnm
    · rfl
    · rfl

/-- **The row inside a class is exact**: for `v_p(m) = j` and `m ≤ M`,
`classRow_j(m) = A_{p'}(⌊M/m⌋) + log m − j log p`. -/
theorem classRow_self_eq (hp : p.Prime) {j M m : ℕ} (hm : 0 < m) (hmM : m ≤ M)
    (hv : m.factorization p = j) :
    classRow p j M m = unitMertensSum p (M / m) + Real.log m - j * Real.log p := by
  have hsplit : ∀ n ∈ Icc 1 M, (if n.factorization p = j then
      weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n) else 0) =
      (if m ∣ n then (if p ∣ n / m then 0 else Λ (n / m) / ((n / m : ℕ) : ℝ)) else 0) +
        (if n ∣ m then (if p ∣ m / n then 0 else Λ (m / n)) else 0) := by
    intro n hn
    have hn0 := pos_of_mem_Icc' hn
    rw [← classRow_up_term hp hm hn0 hv, ← classRow_down_term hp hm hn0 hv,
      weilPrimeKernel_mul_sqrt_ratio hm hn0]
    split_ifs <;> ring
  unfold classRow
  rw [sum_congr rfl hsplit, sum_add_distrib]
  -- up: the units of `p` up to `M/m`
  have hup : ∑ n ∈ Icc 1 M, (if m ∣ n then (if p ∣ n / m then 0 else
      Λ (n / m) / ((n / m : ℕ) : ℝ)) else 0) = unitMertensSum p (M / m) := by
    rw [show (∑ n ∈ Icc 1 M, if m ∣ n then (if p ∣ n / m then 0 else
        Λ (n / m) / ((n / m : ℕ) : ℝ)) else 0) = ∑ n ∈ (Icc 1 M).filter (m ∣ ·),
          (if p ∣ n / m then 0 else Λ (n / m) / ((n / m : ℕ) : ℝ)) from (sum_filter _ _).symm,
      filter_dvd_Icc_eq_image hm, sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hm h,
      unitMertensSum]
    exact sum_congr rfl fun t _ => by rw [Nat.mul_div_cancel_left t hm]
  -- down: the divisors of `m` prime to `p`
  have hdown : ∑ n ∈ Icc 1 M, (if n ∣ m then (if p ∣ m / n then 0 else Λ (m / n)) else 0) =
      Real.log m - j * Real.log p := by
    rw [show (∑ n ∈ Icc 1 M, if n ∣ m then (if p ∣ m / n then 0 else Λ (m / n)) else 0) =
        ∑ n ∈ (Icc 1 M).filter (· ∣ m), (if p ∣ m / n then 0 else Λ (m / n)) from
          (sum_filter _ _).symm, filter_Icc_dvd_eq_divisors hm hmM,
      Nat.sum_div_divisors m (fun t => if p ∣ t then 0 else Λ t)]
    have h1 := sum_divisors_dvd_vonMangoldt_eq hp hm.ne'
    rw [hv] at h1
    have h3 : ∑ t ∈ m.divisors, (if p ∣ t then (0 : ℝ) else Λ t) =
        ∑ t ∈ m.divisors, Λ t - ∑ t ∈ m.divisors, (if p ∣ t then Λ t else 0) := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun t _ => by split_ifs <;> ring
    rw [h3, h1, vonMangoldt_sum]
  rw [hup, hdown]
  ring

/-- **The row across classes is one prime power**: for `j < v_p(m)`, `classRow_j(m) = log p`. -/
theorem classRow_of_lt (hp : p.Prime) {j M m : ℕ} (hm : 0 < m) (hmM : m ≤ M)
    (hj : j < m.factorization p) : classRow p j M m = Real.log p := by
  set k := m.factorization p - j
  have hk : 1 ≤ k := by omega
  have hpk : p ^ k ∣ m := (hp.pow_dvd_iff_le_factorization hm.ne').mpr (by omega)
  set n₀ := m / p ^ k
  have hn₀ : n₀ * p ^ k = m := Nat.div_mul_cancel hpk
  have hn₀0 : 0 < n₀ := Nat.div_pos (Nat.le_of_dvd hm hpk) (pow_pos hp.pos k)
  have hn₀v : n₀.factorization p = j := by
    have h := congrArg (fun x => x.factorization p) hn₀
    simp only [Nat.factorization_mul hn₀0.ne' (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
      hp.factorization_pow, Finsupp.single_eq_same] at h
    omega
  have hn₀M : n₀ ∈ Icc 1 M := mem_Icc.mpr ⟨hn₀0, (Nat.div_le_self m _).trans hmM⟩
  unfold classRow
  rw [← sum_erase_add _ _ hn₀M, if_pos hn₀v]
  -- the term `n₀ = m/p^k` carries `Λ(p^k) = log p`; every other term vanishes
  have hterm : weilPrimeKernel m n₀ * Real.sqrt ((m : ℝ) / n₀) = Real.log p := by
    rw [weilPrimeKernel_mul_sqrt_ratio hm hn₀0]
    have hdvd : n₀ ∣ m := ⟨p ^ k, hn₀.symm⟩
    have hne : n₀ ≠ m := by
      intro h
      have : n₀ * p ^ k = n₀ * 1 := by rw [hn₀, h, mul_one]
      have := Nat.eq_of_mul_eq_mul_left hn₀0 this
      exact absurd this (Nat.one_lt_pow (by omega) hp.one_lt).ne'
    have hnd : ¬ (m ∣ n₀ ∧ m ≠ n₀) := fun h =>
      hne (Nat.dvd_antisymm hdvd h.1)
    rw [if_neg hnd, zero_add, if_pos ⟨hdvd, hne⟩]
    rw [show m / n₀ = p ^ k by
      rw [← hn₀, Nat.mul_div_cancel_left _ hn₀0]]
    exact vonMangoldt_prime_pow hp hk
  rw [hterm]
  have hrest : ∑ n ∈ (Icc 1 M).erase n₀, (if n.factorization p = j then
      weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n) else 0) = 0 := by
    refine sum_eq_zero fun n hn => ?_
    have hn0 : 0 < n := pos_of_mem_Icc' (mem_of_mem_erase hn)
    have hnn : n ≠ n₀ := ne_of_mem_erase hn
    split_ifs with hv
    · rw [weilPrimeKernel_mul_sqrt_ratio hm hn0]
      have hup : ¬ (m ∣ n ∧ m ≠ n) := by
        rintro ⟨⟨t, rfl⟩, -⟩
        have ht : t ≠ 0 := by rintro rfl; simp at hn0
        rw [Nat.factorization_mul hm.ne' ht, Finsupp.add_apply] at hv
        omega
      have hdown : ¬ (n ∣ m ∧ n ≠ m) ∨ Λ (m / n) = 0 := by
        by_cases hd : n ∣ m ∧ n ≠ m
        · right
          obtain ⟨t, ht⟩ := hd.1
          have ht0 : t ≠ 0 := by rintro rfl; simp at ht; omega
          have hmn : m / n = t := by rw [ht, Nat.mul_div_cancel_left t hn0]
          rw [hmn]
          by_contra hΛ
          have hvt : t.factorization p = k := by
            have h := congrArg (fun x => x.factorization p) ht
            simp only [Nat.factorization_mul hn0.ne' ht0, Finsupp.add_apply] at h
            omega
          have hpt : p ∣ t := (hp.dvd_iff_one_le_factorization ht0).mpr (by omega)
          obtain ⟨k', hk', htk⟩ := eq_pow_of_dvd_of_vonMangoldt_ne_zero hp hpt hΛ
          rw [htk, hp.factorization_pow, Finsupp.single_eq_same] at hvt
          apply hnn
          rw [htk, hvt] at ht
          rw [← hn₀] at ht
          exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos k) ht.symm
        · left; exact hd
      rw [if_neg hup, zero_add]
      rcases hdown with h | h
      · rw [if_neg h]
      · split_ifs <;> simp [h]
    · rfl
  rw [hrest, zero_add]

/-- **The cross-class Gram is exact**: for `j < j'`, `⟨w_{j'}^{(M)}, P w_j^{(M)}⟩ = log p |w_{j'}^{(M)}|²`. -/
theorem primeBilinear_classPole_cross_eq (hp : p.Prime) {j j' : ℕ} (hjj : j < j') (M : ℕ) :
    primeBilinear M (classPole p j' M) (classPole p j M) = Real.log p * classMass p j' M := by
  rw [primeBilinear_classPole_eq, classMass, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  split_ifs with hv
  · rw [classRow_of_lt hp (pos_of_mem_Icc' hm) (mem_Icc.mp hm).2 (by rw [hv]; exact hjj)]
    ring
  · simp

/-! ### The finite part inside a class -/

/-- **The finite part inside a class.** For every `η > 0` there is `C` with
`|⟨w_j^{(M)}, P w_j^{(M)}⟩ − δ_j^{−1} |w_j|⁴ + 2γ_p |w_j|²| ≤ η |w_j|² + C` for all `M`. -/
theorem exists_abs_classGram_self_finitePart_le (hp : p.Prime) (j : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, ∀ M : ℕ,
      |primeBilinear M (classPole p j M) (classPole p j M) -
          classMass p j M ^ 2 / classDensity p j + 2 * localEuler p * classMass p j M| ≤
        η * classMass p j M + C := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hδ := classDensity_pos hp j
  -- the local Mertens sum at precision `η/4`, the class mass at precision `η δ_j/4`
  obtain ⟨Y₁, hY₁⟩ := (Metric.tendsto_atTop.mp (tendsto_unitMertensSum_sub_log hp)) (η / 4)
    (by positivity)
  obtain ⟨M₀, hM₀⟩ := (Metric.tendsto_atTop.mp (tendsto_classMass_sub hp j)) (η * classDensity p j / 4)
    (div_pos (mul_pos hη hδ) (by norm_num))
  set Y : ℕ := max Y₁ (⌈4 / η⌉₊ + 1)
  -- a uniform bound for `|A_{p'}(y) − log y + γ_p|`
  set Ce : ℝ := Real.log 4 + 4 + Real.log p / ((p : ℝ) - 1) + |localEuler p|
  -- a uniform bound for `|δ_j^{-1}|w_j^{(M)}|² − (log M − j log p + γ_p)|` below `M₀`
  set B₀ : ℝ := ∑ M ∈ range (M₀ + 1), |classMass p j M / classDensity p j -
    (Real.log M - j * Real.log p + localEuler p)|
  refine ⟨(Ce + Real.log 2) * Y + (1 + Real.log M₀) * B₀, fun M => ?_⟩
  set m := classMass p j M
  have hm0 : 0 ≤ m := classMass_nonneg p j M
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlp : 0 ≤ Real.log p / ((p : ℝ) - 1) := div_nonneg (Real.log_nonneg hp1.le) (by linarith)
  -- the Gram through rows
  have hG : primeBilinear M (classPole p j M) (classPole p j M) =
      ∑ n ∈ Icc 1 M, (if n.factorization p = j then
        (unitMertensSum p (M / n) + Real.log n - j * Real.log p) / n else 0) := by
    rw [primeBilinear_classPole_eq]
    refine sum_congr rfl fun n hn => ?_
    split_ifs with hv
    · rw [classRow_self_eq hp (pos_of_mem_Icc' hn) (mem_Icc.mp hn).2 hv]
    · rfl
  -- `row = (log M − γ_p − j log p) + (e(⌊M/n⌋) − r_n)`
  set e : ℕ → ℝ := fun y => unitMertensSum p y - Real.log y + localEuler p
  set r : ℕ → ℝ := fun n => Real.log M - Real.log ((M / n : ℕ) : ℝ) - Real.log n
  have hrow : ∀ n ∈ Icc 1 M, (if n.factorization p = j then
      (unitMertensSum p (M / n) + Real.log n - j * Real.log p) / n else 0) =
      (Real.log M - localEuler p - j * Real.log p) * (if n.factorization p = j then 1 / (n : ℝ)
        else 0) + (if n.factorization p = j then (e (M / n) - r n) / n else 0) := by
    intro n _
    split_ifs
    · simp only [e, r]; ring
    · ring
  rw [hG, sum_congr rfl hrow, sum_add_distrib, ← mul_sum]
  -- the error term, as in `TheFinitePartIsEulersConstant`
  have herr : |∑ n ∈ Icc 1 M, (if n.factorization p = j then (e (M / n) - r n) / n else 0)| ≤
      η / 2 * m + (Ce + Real.log 2) * Y := by
    have hpt : ∀ n ∈ Icc 1 M, |(if n.factorization p = j then (e (M / n) - r n) / n else 0)| ≤
        η / 2 * (if n.factorization p = j then 1 / (n : ℝ) else 0) +
          (if M / n < Y then (Ce + Real.log 2) * (1 / (n : ℝ)) else 0) := by
      intro n hn
      have hn0 : 0 < n := pos_of_mem_Icc' hn
      have hnM := (mem_Icc.mp hn).2
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
      split_ifs with hv hY hY
      · -- small quotient: crude bound
        have hq : 1 ≤ M / n := (Nat.le_div_iff_mul_le hn0).mpr (by linarith)
        obtain ⟨hr0, hr1⟩ := roundoff_le hn0 hnM
        have hr2 : r n ≤ Real.log 2 := by
          have := log_le_log_div_add_log hn0 hnM; simp only [r]; linarith
        have hmert := RHTower.Mertens.mertens_first (M / n) hq
        have hpp := sum_dvd_vonMangoldt_div_le hp (Icc 1 (M / n))
        have hpp0 : 0 ≤ pPowerMertensSum p (M / n) := sum_nonneg fun t _ => by
          split_ifs
          · exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
          · exact le_rfl
        have hel : |e (M / n) - r n| ≤ Ce + Real.log 2 := by
          have he' : e (M / n) = (mertensSum (M / n) - Real.log ((M / n : ℕ) : ℝ)) -
              pPowerMertensSum p (M / n) + localEuler p := by
            simp only [e]; rw [unitMertensSum_eq]; ring
          have hr0' : 0 ≤ r n := hr0
          rw [he']
          have hm' : |mertensSum (M / n) - Real.log ((M / n : ℕ) : ℝ)| ≤ Real.log 4 + 4 := hmert
          have hpp' : pPowerMertensSum p (M / n) ≤ Real.log p / ((p : ℝ) - 1) := hpp
          simp only [Ce]
          rw [abs_le] at hm' ⊢
          have := abs_le.mp (le_refl |localEuler p|)
          have h1 := neg_abs_le (localEuler p)
          have h2 := le_abs_self (localEuler p)
          constructor <;> linarith
        rw [abs_div, abs_of_pos hn', div_eq_mul_one_div]
        have : 0 ≤ η / 2 * (1 / (n : ℝ)) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hel (by positivity : (0 : ℝ) ≤ 1 / n)]
      · -- large quotient: both terms are small
        push Not at hY
        have hYq : Y₁ ≤ M / n := (le_max_left _ _).trans hY
        obtain ⟨hr0, hr1⟩ := roundoff_le hn0 hnM
        have he : |e (M / n)| ≤ η / 4 := by
          have := (hY₁ (M / n) hYq).le
          rw [Real.dist_eq] at this
          simpa [e, sub_neg_eq_add, add_comm, add_left_comm, add_assoc] using this
        have hqY : (⌈4 / η⌉₊ + 1 : ℕ) ≤ M / n := (le_max_right _ _).trans hY
        have hinv : 1 / ((M / n : ℕ) : ℝ) ≤ η / 4 := by
          have h1 : (4 / η : ℝ) < ((M / n : ℕ) : ℝ) := by
            have := Nat.le_ceil (4 / η)
            have h2 : ((⌈4 / η⌉₊ + 1 : ℕ) : ℝ) ≤ ((M / n : ℕ) : ℝ) := by exact_mod_cast hqY
            push_cast at h2
            linarith
          rw [div_le_iff₀ (by positivity)]
          rw [div_lt_iff₀ hη] at h1
          linarith
        have hel : |e (M / n) - r n| ≤ η / 2 := by
          have hr0' : 0 ≤ r n := hr0
          have hr1' : r n ≤ 1 / ((M / n : ℕ) : ℝ) := hr1
          rw [abs_le] at he ⊢; constructor <;> linarith
        rw [abs_div, abs_of_pos hn', div_eq_mul_one_div, add_zero]
        exact mul_le_mul_of_nonneg_right hel (by positivity)
      · rw [abs_zero]; positivity
      · rw [abs_zero, mul_zero, add_zero]
    have hsmall : ∑ n ∈ Icc 1 M, (if M / n < Y then (Ce + Real.log 2) * (1 / (n : ℝ)) else 0) ≤
        (Ce + Real.log 2) * Y := by
      have hCe : 0 ≤ Ce := by simp only [Ce]; positivity
      rcases Nat.eq_zero_or_pos M with rfl | hMpos
      · simp; positivity
      have hterm : ∀ n ∈ Icc 1 M, (if M / n < Y then (Ce + Real.log 2) * (1 / (n : ℝ)) else 0) ≤
          (Ce + Real.log 2) * ((Y : ℝ) / M) := by
        intro n hn
        have hn0 : 0 < n := pos_of_mem_Icc' hn
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
        have hM' : (0 : ℝ) < M := by exact_mod_cast hMpos
        split_ifs with hY
        · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hlt := RHTower.Mertens.cast_div_lt M n hn0
          have hYr : ((M / n : ℕ) : ℝ) + 1 ≤ Y := by exact_mod_cast hY
          rw [div_lt_iff₀ hn'] at hlt
          rw [div_le_div_iff₀ hn' hM']
          nlinarith
        · positivity
      calc ∑ n ∈ Icc 1 M, (if M / n < Y then (Ce + Real.log 2) * (1 / (n : ℝ)) else 0)
          ≤ ∑ n ∈ Icc 1 M, (Ce + Real.log 2) * ((Y : ℝ) / M) := sum_le_sum hterm
        _ = (Ce + Real.log 2) * Y := by
            rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
            have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hMpos.ne'
            push_cast
            field_simp
    calc |∑ n ∈ Icc 1 M, (if n.factorization p = j then (e (M / n) - r n) / n else 0)|
        ≤ ∑ n ∈ Icc 1 M, |(if n.factorization p = j then (e (M / n) - r n) / n else 0)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Icc 1 M, (η / 2 * (if n.factorization p = j then 1 / (n : ℝ) else 0) +
            (if M / n < Y then (Ce + Real.log 2) * (1 / (n : ℝ)) else 0)) := sum_le_sum hpt
      _ = η / 2 * m + ∑ n ∈ Icc 1 M,
            (if M / n < Y then (Ce + Real.log 2) * (1 / (n : ℝ)) else 0) := by
          rw [sum_add_distrib, ← mul_sum]; rfl
      _ ≤ η / 2 * m + (Ce + Real.log 2) * Y := by linarith
  -- the class mass against its asymptotics
  have hmass : |m / classDensity p j - (Real.log M - j * Real.log p + localEuler p)| * m ≤
      η / 4 * m + (1 + Real.log M₀) * B₀ := by
    by_cases hMM₀ : M₀ ≤ M
    · have h := hM₀ M hMM₀
      rw [Real.dist_eq, sub_zero] at h
      have h' : |m / classDensity p j - (Real.log M - j * Real.log p + localEuler p)| ≤ η / 4 := by
        rw [show m / classDensity p j - (Real.log M - j * Real.log p + localEuler p) =
          (m - classDensity p j * (Real.log M - j * Real.log p + localEuler p)) / classDensity p j by
            field_simp, abs_div, abs_of_pos hδ, div_le_iff₀ hδ]
        linarith
      have hB₀ : 0 ≤ B₀ := sum_nonneg fun _ _ => abs_nonneg _
      have : 0 ≤ 1 + Real.log M₀ := by have := Real.log_natCast_nonneg M₀; linarith
      nlinarith [mul_le_mul_of_nonneg_right h' hm0]
    · push Not at hMM₀
      have hmem : M ∈ range (M₀ + 1) := mem_range.mpr (by omega)
      have h1 : |m / classDensity p j - (Real.log M - j * Real.log p + localEuler p)| ≤ B₀ :=
        single_le_sum (f := fun M => |classMass p j M / classDensity p j -
          (Real.log M - j * Real.log p + localEuler p)|) (fun _ _ => abs_nonneg _) hmem
      have h2 : m ≤ 1 + Real.log M₀ :=
        (classMass_le_harmonicSum p j M).trans ((harmonicSum_mono hMM₀.le).trans (harmonicSum_le M₀))
      have hB₀ : 0 ≤ B₀ := sum_nonneg fun _ _ => abs_nonneg _
      nlinarith [mul_le_mul h1 h2 hm0 hB₀, abs_nonneg (m / classDensity p j -
        (Real.log M - j * Real.log p + localEuler p))]
  -- assemble: `G − m²/δ + 2γ_p m = (stuff) · m + error`
  have hident : (Real.log M - localEuler p - j * Real.log p) * m +
      ∑ n ∈ Icc 1 M, (if n.factorization p = j then (e (M / n) - r n) / n else 0) -
        m ^ 2 / classDensity p j + 2 * localEuler p * m =
      ∑ n ∈ Icc 1 M, (if n.factorization p = j then (e (M / n) - r n) / n else 0) -
        (m / classDensity p j - (Real.log M - j * Real.log p + localEuler p)) * m := by
    field_simp
    ring
  have hsum : ∑ n ∈ Icc 1 M, (if n.factorization p = j then 1 / (n : ℝ) else 0) = m := rfl
  rw [hsum, hident]
  calc |∑ n ∈ Icc 1 M, (if n.factorization p = j then (e (M / n) - r n) / n else 0) -
        (m / classDensity p j - (Real.log M - j * Real.log p + localEuler p)) * m|
      ≤ |∑ n ∈ Icc 1 M, (if n.factorization p = j then (e (M / n) - r n) / n else 0)| +
          |m / classDensity p j - (Real.log M - j * Real.log p + localEuler p)| * m := by
        refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
        rw [abs_mul, abs_of_nonneg hm0]
    _ ≤ (η / 2 * m + (Ce + Real.log 2) * Y) + (η / 4 * m + (1 + Real.log M₀) * B₀) :=
        add_le_add herr hmass
    _ ≤ η * m + ((Ce + Real.log 2) * Y + (1 + Real.log M₀) * B₀) := by nlinarith

/-! ### The finite part on the classes -/

/-- The densities descend by the degree: `δ_{j+k} = δ_j/p^k`. -/
theorem classDensity_add (p j k : ℕ) : classDensity p (j + k) = classDensity p j / (p : ℝ) ^ k := by
  unfold classDensity
  rw [pow_add, div_div]

/-- **The finite part on the classes is the tower form.** For every `η > 0` there is `C` such that for
every `M` and every class combination `x = Σ_{j ≤ J} a_j w_j^{(M)}`, with `m_j = |w_j^{(M)}|²`,
`|P_M(x) − Σ_j δ_j^{−1} (a_j m_j)² + 2γ_p Σ_j a_j² m_j − log p Σ_{j ≠ j'} a_j a_{j'} m_{max(j, j')}|
≤ Σ_j a_j² (η m_j + C)`. -/
theorem exists_abs_atomicWeilForm_classCombination_finitePart_le (hp : p.Prime) (J : ℕ) {η : ℝ}
    (hη : 0 < η) :
    ∃ C : ℝ, ∀ (M : ℕ) (a : Fin (J + 1) → ℝ),
      |atomicWeilForm M (fun n => ∑ j : Fin (J + 1), a j * classPole p j M n) -
          ∑ j : Fin (J + 1), (a j * classMass p j M) ^ 2 / classDensity p j +
          2 * localEuler p * ∑ j : Fin (J + 1), a j ^ 2 * classMass p j M -
          Real.log p * ∑ j : Fin (J + 1), ∑ j' : Fin (J + 1),
            (if j = j' then 0 else a j * a j' * classMass p (max (j : ℕ) j') M)| ≤
        ∑ j : Fin (J + 1), a j ^ 2 * (η * classMass p j M + C) := by
  choose C hC using fun j : Fin (J + 1) => exists_abs_classGram_self_finitePart_le hp j hη
  refine ⟨∑ j, |C j|, fun M a => ?_⟩
  set G : Fin (J + 1) → Fin (J + 1) → ℝ := fun j j' =>
    primeBilinear M (classPole p j M) (classPole p j' M)
  have hexp : atomicWeilForm M (fun n => ∑ j : Fin (J + 1), a j * classPole p j M n) =
      ∑ j, ∑ j', a j * a j' * G j j' := by
    have hL : ∀ y, primeBilinear M (fun n => ∑ j : Fin (J + 1), a j * classPole p j M n) y =
        ∑ j, a j * primeBilinear M (classPole p j M) y := fun y =>
      primeBilinear_sum_left M a (fun j => classPole p j M) y
    rw [atomicWeilForm_eq_primeBilinear, hL]
    refine sum_congr rfl fun j _ => ?_
    rw [primeBilinear_comm, hL, mul_sum]
    refine sum_congr rfl fun j' _ => ?_
    simp only [G]
    rw [primeBilinear_comm]
    ring
  -- off the diagonal the Gram is exact
  have hcross : ∀ j j' : Fin (J + 1), j ≠ j' →
      G j j' = Real.log p * classMass p (max (j : ℕ) j') M := by
    intro j j' hne
    have hne' : (j : ℕ) ≠ j' := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hne' with h | h
    · simp only [G]
      rw [primeBilinear_comm, primeBilinear_classPole_cross_eq hp h, max_eq_right h.le]
    · simp only [G]
      rw [primeBilinear_classPole_cross_eq hp h, max_eq_left h.le]
  have hident : atomicWeilForm M (fun n => ∑ j : Fin (J + 1), a j * classPole p j M n) -
      ∑ j : Fin (J + 1), (a j * classMass p j M) ^ 2 / classDensity p j +
      2 * localEuler p * ∑ j : Fin (J + 1), a j ^ 2 * classMass p j M -
      Real.log p * ∑ j : Fin (J + 1), ∑ j' : Fin (J + 1),
        (if j = j' then 0 else a j * a j' * classMass p (max (j : ℕ) j') M) =
      ∑ j : Fin (J + 1), a j ^ 2 * (G j j - classMass p j M ^ 2 / classDensity p j +
        2 * localEuler p * classMass p j M) := by
    rw [hexp, mul_sum, mul_sum]
    simp only [mul_sum]
    rw [← sum_sub_distrib, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [← sum_erase_add _ _ (mem_univ j), ← sum_erase_add _ _ (mem_univ j), if_pos rfl]
    have hoff : ∑ j' ∈ univ.erase j, a j * a j' * G j j' =
        ∑ j' ∈ univ.erase j, Real.log p * (if j = j' then 0 else
          a j * a j' * classMass p (max (j : ℕ) j') M) := by
      refine sum_congr rfl fun j' hj' => ?_
      have hne : j ≠ j' := fun h => (mem_erase.mp hj').1 h.symm
      rw [if_neg hne, hcross j j' hne]
      ring
    rw [hoff]
    field_simp
    ring
  rw [hident]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  refine mul_le_mul_of_nonneg_left ((hC j M).trans ?_) (sq_nonneg _)
  have : C j ≤ ∑ j, |C j| := (le_abs_self _).trans
    (single_le_sum (f := fun j => |C j|) (fun _ _ => abs_nonneg _) (mem_univ j))
  linarith

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
