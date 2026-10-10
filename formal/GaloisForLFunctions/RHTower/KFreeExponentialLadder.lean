import GaloisForLFunctions.RHTower.KFreeExponentialCascade
import GaloisForLFunctions.RHTower.MobiusMertensAbscissaLittlewood
import GaloisForLFunctions.RHTower.FareyDiscrepancyOmega

/-!
# The quasi-RH ladder for `k`-free counts

With `A_k(t) = Σ_m μ(m)/(e^{m^k t} - 1)` (the exponentially weighted count of `k`-free numbers) and
`c_k = Σ_m μ(m)/m^k`:

**Theorem** (`zeroFree_strip_iff_kFree`). For every `k ≥ 2`,
`ζ(s) ≠ 0 on Re s > 1 - 1/k  ⟺  ∀ ε > 0, |A_k(t) - c_k/t| = O(t^{-(k-1)/k² - ε})` on `(0, 1]`.

A zero-free strip of width `1/k` is therefore exactly a power saving of `1/k²` (over the trivial
exponent `1/k`) in the smoothed `k`-free count. At `k = 2` this is RH and the squarefree law.

* **Forward transfer** (`abs_kProfile_sub_le_of_mertens`). If `|M(N)| ≤ B (N+1)^θ` with
  `0 ≤ θ ≤ 1`, then `|A_k(t) - c_k/t| ≤ C t^{-β}` for every `β ≤ 1` with `θ < kβ`. The proof writes
  `A_k(t) - c_k/t = Σ_m μ(m) h(m^k t)` and sums by parts twice, using that `h` is increasing with
  `|h(u)| ≤ u^{-β}`.
* **Converse.** The dilation law and the cascade `z ↦ 1 - z/k`
  (`riemannZeta_ne_zero_of_kBound`).
-/

open Filter Topology MeasureTheory Set Complex
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace RHTower.KFreeExponential

noncomputable section

open RHTower.SquarefreeExponential

/-- **Forward transfer** for the Möbius–kernel series at the `k`-th powers. -/
theorem abs_tsum_moebius_kernelH_pow_le {k : ℕ} (hk : 2 ≤ k) {θ β B : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hθβ : θ < k * β) (hβ1 : β ≤ 1) (hB : 0 ≤ B)
    (hM : ∀ n : ℕ, |mertensFunctionReal n| ≤ B * ((n : ℝ) + 1) ^ θ)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |∑' m : ℕ, (μ m : ℝ) * kernelH ((m : ℝ) ^ k * t)| ≤
      B * (4 + ∑' j : ℕ, ((j : ℝ) + 2) ^ (θ - 1 - k * β)) * t ^ (-β) := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hβ0 : 0 ≤ β := by nlinarith
  set p : ℝ := θ - 1 - k * β with hp
  have hZs : Summable fun j : ℕ => ((j : ℝ) + 2) ^ p := by
    have h := (Real.summable_nat_rpow (p := p)).mpr (by rw [hp]; linarith)
    have h2 := (summable_nat_add_iff 2).mpr h
    refine h2.congr fun j => ?_
    push_cast; ring_nf
  set Z : ℝ := ∑' j : ℕ, ((j : ℝ) + 2) ^ p with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg fun j => Real.rpow_nonneg (by positivity) _
  have htβ : 1 ≤ t ^ (-β) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (by linarith)
  set G : ℕ → ℝ := fun j => kernelH (((j : ℝ) + 1) ^ k * t) with hG
  have hGpos : ∀ j : ℕ, 0 < ((j : ℝ) + 1) ^ k * t := fun j => by positivity
  have hGmono : ∀ j : ℕ, G j ≤ G (j + 1) := by
    intro j
    refine monotoneOn_kernelH (hGpos j) (hGpos (j + 1)) ?_
    push_cast
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have : ((j : ℝ) + 1) ^ k ≤ ((j : ℝ) + 1 + 1) ^ k :=
      pow_le_pow_left₀ (by linarith) (by linarith) k
    exact mul_le_mul_of_nonneg_right this ht.le
  have hGabs : ∀ j : ℕ, |G j| ≤ ((j : ℝ) + 1) ^ (-(k * β)) * t ^ (-β) := by
    intro j
    have h := abs_kernelH_le_rpow (hGpos j) hβ0 hβ1
    have e : (((j : ℝ) + 1) ^ k * t) ^ (-β) = ((j : ℝ) + 1) ^ (-(k * β)) * t ^ (-β) := by
      rw [Real.mul_rpow (by positivity) ht.le,
        show ((j : ℝ) + 1) ^ k = ((j : ℝ) + 1) ^ ((k : ℕ) : ℝ) by rw [Real.rpow_natCast],
        ← Real.rpow_mul (by positivity)]
      congr 2
      ring
    exact h.trans (le_of_eq e)
  have hGle : ∀ j : ℕ, G j ≤ 0 := fun j => kernelH_nonpos (hGpos j)
  -- summability
  have hsum : Summable fun m : ℕ => (μ m : ℝ) * kernelH ((m : ℝ) ^ k * t) := by
    refine Summable.of_norm_bounded ((summable_inv_pow hk).div_const t) fun m => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [kernelH, zero_pow (show k ≠ 0 by omega)]
    · have hmt : 0 < (m : ℝ) ^ k * t := by positivity
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |(μ m : ℝ)| * |kernelH ((m : ℝ) ^ k * t)| ≤ 1 * (1 / ((m : ℝ) ^ k * t)) :=
            mul_le_mul (abs_moebius_real_le m) (abs_kernelH_le_inv hmt) (abs_nonneg _) zero_le_one
        _ = 1 / (m : ℝ) ^ k / t := by rw [one_mul, div_div]
  set S : ℕ → ℝ := fun n => ∑ j ∈ Finset.range n, (μ (j + 1) : ℝ) * G j with hS
  have hSlim : Tendsto S atTop (𝓝 (∑' m : ℕ, (μ m : ℝ) * kernelH ((m : ℝ) ^ k * t))) := by
    have h := hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    refine h.congr fun n => ?_
    simp only [Function.comp_apply, hS, hG]
    rw [Finset.sum_range_succ']
    simp
  have hbound : ∀ n : ℕ, |S n| ≤ B * (4 + Z) * t ^ (-β) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [hS, Finset.range_zero, Finset.sum_empty, abs_zero]
      have : 0 ≤ 4 + Z := by linarith
      positivity
    have hparts := Finset.sum_range_by_parts G (fun j => (μ (j + 1) : ℝ)) n
    simp only [smul_eq_mul] at hparts
    have hS' : S n = G (n - 1) * mertensFunctionReal n -
        ∑ j ∈ Finset.range (n - 1), (G (j + 1) - G j) * mertensFunctionReal (j + 1) := by
      rw [hS]
      simp only
      rw [show (∑ j ∈ Finset.range n, (μ (j + 1) : ℝ) * G j) =
          ∑ j ∈ Finset.range n, G j * (μ (j + 1) : ℝ) from
        Finset.sum_congr rfl fun j _ => mul_comm _ _, hparts, sum_range_moebius_succ_eq]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [sum_range_moebius_succ_eq]
      push_cast
      rfl
    have hbd : |G (n - 1) * mertensFunctionReal n| ≤ 2 * B * t ^ (-β) := by
      have hn1 : ((n - 1 : ℕ) : ℝ) + 1 = n := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [abs_mul]
      have h1 := hGabs (n - 1)
      rw [hn1] at h1
      have h2 := hM n
      have hpow : ((n : ℝ) + 1) ^ θ ≤ 2 * (n : ℝ) ^ θ := by
        calc ((n : ℝ) + 1) ^ θ ≤ (2 * n) ^ θ :=
              Real.rpow_le_rpow (by positivity) (by linarith) hθ0
          _ = 2 ^ θ * (n : ℝ) ^ θ := Real.mul_rpow (by norm_num) (by positivity)
          _ ≤ 2 * (n : ℝ) ^ θ := by
              gcongr
              calc (2 : ℝ) ^ θ ≤ 2 ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1
                _ = 2 := Real.rpow_one 2
      have hcomb : (n : ℝ) ^ (-(k * β)) * (n : ℝ) ^ θ ≤ 1 := by
        rw [← Real.rpow_add (by positivity)]
        exact Real.rpow_le_one_of_one_le_of_nonpos hnR (by linarith)
      calc |G (n - 1)| * |mertensFunctionReal n|
          ≤ ((n : ℝ) ^ (-(k * β)) * t ^ (-β)) * (B * ((n : ℝ) + 1) ^ θ) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ ≤ ((n : ℝ) ^ (-(k * β)) * t ^ (-β)) * (B * (2 * (n : ℝ) ^ θ)) := by gcongr
        _ = 2 * B * t ^ (-β) * ((n : ℝ) ^ (-(k * β)) * (n : ℝ) ^ θ) := by ring
        _ ≤ 2 * B * t ^ (-β) * 1 := by gcongr
        _ = 2 * B * t ^ (-β) := mul_one _
    set q : ℕ := n - 1 with hq
    have hinner : |∑ j ∈ Finset.range q, (G (j + 1) - G j) * mertensFunctionReal (j + 1)| ≤
        B * ∑ j ∈ Finset.range q, ((j : ℝ) + 2) ^ θ * (G (j + 1) - G j) := by
      rw [Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hGmono j))]
      have h := hM (j + 1)
      push_cast at h
      rw [show (j : ℝ) + 1 + 1 = (j : ℝ) + 2 by ring] at h
      calc (G (j + 1) - G j) * |mertensFunctionReal (j + 1)|
          ≤ (G (j + 1) - G j) * (B * ((j : ℝ) + 2) ^ θ) := by
            gcongr
            · exact sub_nonneg.mpr (hGmono j)
        _ = B * (((j : ℝ) + 2) ^ θ * (G (j + 1) - G j)) := by ring
    have hsecond : ∑ j ∈ Finset.range q, ((j : ℝ) + 2) ^ θ * (G (j + 1) - G j) ≤
        2 + Z * t ^ (-β) := by
      rw [sum_range_mul_sub_eq (fun j : ℕ => ((j : ℝ) + 2) ^ θ) G q]
      have h1 : ((q : ℝ) + 2) ^ θ * G q ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (hGle q)
      have h2 : -(((0 : ℕ) : ℝ) + 2) ^ θ * G 0 ≤ 2 := by
        push_cast
        have hG0' : |G 0| ≤ 1 := by
          have hu : G 0 = kernelH t := by simp [hG]
          rw [hu, abs_of_nonpos (kernelH_nonpos ht)]
          linarith [neg_one_le_kernelH ht]
        have h2θ : (2 : ℝ) ^ θ ≤ 2 := by
          calc (2 : ℝ) ^ θ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1
            _ = 2 := Real.rpow_one 2
        have hp2 : 0 ≤ (2 : ℝ) ^ θ := by positivity
        simp only [zero_add]
        nlinarith [abs_le.mp hG0', hGle 0]
      have h3 : -∑ j ∈ Finset.range q,
          ((((j + 1 : ℕ) : ℝ) + 2) ^ θ - ((j : ℝ) + 2) ^ θ) * G (j + 1) ≤ Z * t ^ (-β) := by
        rw [← Finset.sum_neg_distrib]
        calc ∑ j ∈ Finset.range q,
              -(((((j + 1 : ℕ) : ℝ) + 2) ^ θ - ((j : ℝ) + 2) ^ θ) * G (j + 1))
            ≤ ∑ j ∈ Finset.range q, ((j : ℝ) + 2) ^ p * t ^ (-β) := by
              refine Finset.sum_le_sum fun j _ => ?_
              have hj2 : (1 : ℝ) ≤ (j : ℝ) + 2 := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
              have hd := rpow_add_one_sub_rpow_le hj2 hθ0 hθ1
              have hGj := hGabs (j + 1)
              push_cast at hGj ⊢
              rw [show (j : ℝ) + 1 + 1 = (j : ℝ) + 2 by ring] at hGj
              rw [show (j : ℝ) + 1 + 2 = (j : ℝ) + 2 + 1 by ring]
              have hGneg : -G (j + 1) ≤ ((j : ℝ) + 2) ^ (-(k * β)) * t ^ (-β) := by
                linarith [neg_abs_le (G (j + 1)), abs_le.mp hGj]
              calc -((((j : ℝ) + 2 + 1) ^ θ - ((j : ℝ) + 2) ^ θ) * G (j + 1))
                  = (((j : ℝ) + 2 + 1) ^ θ - ((j : ℝ) + 2) ^ θ) * (-G (j + 1)) := by ring
                _ ≤ ((j : ℝ) + 2) ^ (θ - 1) * (((j : ℝ) + 2) ^ (-(k * β)) * t ^ (-β)) :=
                    mul_le_mul hd hGneg (by linarith [hGle (j + 1)]) (by positivity)
                _ = ((j : ℝ) + 2) ^ p * t ^ (-β) := by
                    rw [← mul_assoc, ← Real.rpow_add (by positivity), hp]
                    ring_nf
          _ = (∑ j ∈ Finset.range q, ((j : ℝ) + 2) ^ p) * t ^ (-β) := by rw [Finset.sum_mul]
          _ ≤ Z * t ^ (-β) := by
              gcongr
              exact hZs.sum_le_tsum _ fun j _ => Real.rpow_nonneg (by positivity) _
      linarith
    rw [hS']
    calc |G (n - 1) * mertensFunctionReal n -
          ∑ j ∈ Finset.range q, (G (j + 1) - G j) * mertensFunctionReal (j + 1)|
        ≤ |G (n - 1) * mertensFunctionReal n| +
            |∑ j ∈ Finset.range q, (G (j + 1) - G j) * mertensFunctionReal (j + 1)| :=
          abs_sub _ _
      _ ≤ 2 * B * t ^ (-β) + B * (2 + Z * t ^ (-β)) := by
          gcongr
          exact hinner.trans (mul_le_mul_of_nonneg_left hsecond hB)
      _ ≤ B * (4 + Z) * t ^ (-β) := by nlinarith
  exact le_of_tendsto hSlim.abs (Eventually.of_forall hbound)

/-- **Forward transfer.** -/
theorem abs_kProfile_sub_le_of_mertens {k : ℕ} (hk : 2 ≤ k) {θ β B : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hθβ : θ < k * β) (hβ1 : β ≤ 1) (hB : 0 ≤ B)
    (hM : ∀ n : ℕ, |mertensFunctionReal n| ≤ B * ((n : ℝ) + 1) ^ θ) :
    ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, |kProfile k t - kDensity k / t| ≤ C * t ^ (-β) :=
  ⟨_, fun t ht => by
    rw [kProfile_sub_eq_tsum hk ht.1]
    exact abs_tsum_moebius_kernelH_pow_le hk hθ0 hθ1 hθβ hβ1 hB hM ht.1 ht.2⟩

/-- **The quasi-RH ladder.** -/
theorem zeroFree_strip_iff_kFree {k : ℕ} (hk : 2 ≤ k) :
    (∀ s : ℂ, 1 - 1 / (k : ℝ) < s.re → riemannZeta s ≠ 0) ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1,
        |kProfile k t - kDensity k / t| ≤ C * t ^ (-(((k : ℝ) - 1) / (k : ℝ) ^ 2 + ε)) := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  constructor
  · intro hzf ε hε
    set δ : ℝ := min ε (1 / (2 * k)) with hδ
    have hδ0 : 0 < δ := lt_min hε (by positivity)
    have hδε : δ ≤ ε := min_le_left _ _
    have hδk : δ ≤ 1 / (2 * k) := min_le_right _ _
    have hδ1 : δ ≤ 1 / 4 := hδk.trans (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
    have hinvk : 1 / (k : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hk0 (by norm_num)]; linarith
    have hinvpos : 0 < 1 / (k : ℝ) := by positivity
    have hΘ : (1 / 2 : ℝ) ≤ 1 - 1 / k := by linarith
    have hΘ1 : 1 - 1 / (k : ℝ) ≤ 1 := by linarith
    obtain ⟨B, hB, hMB⟩ := mobiusMertens_subpower_of_zeroFree hΘ hΘ1 hzf (δ / 2) (by linarith)
    have hM : ∀ n : ℕ, |mertensFunctionReal n| ≤ B * ((n : ℝ) + 1) ^ (1 - 1 / k + δ / 2) :=
      fun n => by rw [← norm_mobiusMertensPartialSum_eq_abs_mertensFunctionReal]; exact hMB n
    have hkinv : (k : ℝ) * (1 / (2 * k)) = 1 / 2 := by field_simp
    have hθ1 : 1 - 1 / (k : ℝ) + δ / 2 ≤ 1 := by
      have : δ / 2 ≤ 1 / (2 * k) := by linarith [hδk, (by positivity : (0 : ℝ) < 1 / (2 * k))]
      have h2 : 1 / (2 * (k : ℝ)) ≤ 1 / k := by
        rw [div_le_div_iff₀ (by positivity) hk0]; linarith
      linarith
    have hβ : (1 - 1 / (k : ℝ) + δ / 2) < k * (((k : ℝ) - 1) / (k : ℝ) ^ 2 + δ) := by
      have e : (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ) ^ 2) = 1 - 1 / k := by field_simp
      rw [mul_add, e]
      nlinarith
    have hβ1 : ((k : ℝ) - 1) / (k : ℝ) ^ 2 + δ ≤ 1 := by
      have : ((k : ℝ) - 1) / (k : ℝ) ^ 2 ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      linarith
    obtain ⟨C, hC⟩ := abs_kProfile_sub_le_of_mertens hk (θ := 1 - 1 / k + δ / 2)
      (β := ((k : ℝ) - 1) / (k : ℝ) ^ 2 + δ) (by linarith) hθ1 hβ hβ1 hB hM
    refine ⟨|C|, fun t ht => ?_⟩
    calc |kProfile k t - kDensity k / t| ≤ C * t ^ (-(((k : ℝ) - 1) / (k : ℝ) ^ 2 + δ)) := hC t ht
      _ ≤ |C| * t ^ (-(((k : ℝ) - 1) / (k : ℝ) ^ 2 + δ)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg ht.1.le _)
      _ ≤ |C| * t ^ (-(((k : ℝ) - 1) / (k : ℝ) ^ 2 + ε)) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 (by linarith)) (abs_nonneg C)
  · intro hB s hs hz
    have hs1 : s.re < 1 := by
      by_contra h
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
    set ε : ℝ := min ((s.re - (1 - 1 / k)) / (2 * k)) ((1 - s.re) / (2 * (k : ℝ) ^ 2)) with hε
    have hgap : 0 < s.re - (1 - 1 / k) := by linarith
    have hgap2 : 0 < 1 - s.re := by linarith
    have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
    have hε1 : ε ≤ (s.re - (1 - 1 / k)) / (2 * k) := min_le_left _ _
    have hε2 : ε ≤ (1 - s.re) / (2 * (k : ℝ) ^ 2) := min_le_right _ _
    obtain ⟨C, hC⟩ := hB ε hε0
    set α : ℝ := ((k : ℝ) - 1) / (k : ℝ) ^ 2 + ε with hα
    have hkα : (k : ℝ) * α = 1 - 1 / k + k * ε := by
      rw [hα, mul_add]
      congr 1
      field_simp
    have hα0 : 0 ≤ α := by
      have : 0 ≤ ((k : ℝ) - 1) / (k : ℝ) ^ 2 := div_nonneg (by linarith) (by positivity)
      linarith
    have hα1 : α ≤ 1 := by
      have h1 : ((k : ℝ) - 1) / (k : ℝ) ^ 2 ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      have h2 : ε ≤ 1 / 2 := by
        refine hε2.trans ?_
        have hinvk : 1 / (k : ℝ) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ hk0 (by norm_num)]; linarith
        have hspos : 0 < s.re := by linarith
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    have hkε1 : (k : ℝ) * ε ≤ (s.re - (1 - 1 / k)) / 2 := by
      have := mul_le_mul_of_nonneg_left hε1 hk0.le
      rwa [show (k : ℝ) * ((s.re - (1 - 1 / k)) / (2 * k)) = (s.re - (1 - 1 / k)) / 2 by
        field_simp] at this
    have hkε2 : (k : ℝ) * ε * k ≤ (1 - s.re) / 2 := by
      have := mul_le_mul_of_nonneg_left hε2 (by positivity : (0 : ℝ) ≤ k * k)
      rw [show (k : ℝ) * k * ((1 - s.re) / (2 * (k : ℝ) ^ 2)) = (1 - s.re) / 2 by
        field_simp] at this
      linarith [this]
    refine riemannZeta_ne_zero_of_kBound hk hα0 hα1 hC ?_ ?_ hz
    · rw [hkα]; linarith
    · rw [hkα]
      have : s.re / k < 1 / k - k * ε := by
        rw [div_lt_iff₀ hk0]
        have e : (1 / (k : ℝ) - k * ε) * k = 1 - k * ε * k := by field_simp
        rw [e]
        linarith
      linarith

end

end RHTower.KFreeExponential
