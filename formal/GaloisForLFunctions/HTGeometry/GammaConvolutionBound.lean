import GaloisForLFunctions.HTGeometry.GammaRealShiftProfile

/-!
# The convolution of a gamma profile is concentrated at its endpoints

A Cauchy product of two series with the profile `Γ(1 + s k)` produces, at index `n`, the sum

```text
∑_{i=1}^{n-1} Γ(1 + s i) Γ(1 + s (n − i)) .
```

Log-convexity of `Γ` makes `i ↦ log Γ(1+s i) + log Γ(1+s(n−i))` convex, so on any subinterval the
sum is largest at the endpoints.  Applied at depth `1` it bounds every term by the first one;
applied at a fixed depth `p` it bounds the whole middle block by `Γ(1+s p) Γ(1+s(n−p))`, which is
smaller than the first term by a factor `n^{−s(p−1)}`.  Choosing `p` with `s(p−1) > 1` makes that
factor beat the number of terms, so the entire sum is a **bounded multiple of its first term**.

The geometric factor of a full profile `Γ(1+sk) β^k` cancels between the two sides, so the estimate
is a statement about `Γ` alone.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **Log-convexity bound.**  On the block `[p, n−p]` the pair product is largest at the ends. -/
theorem gammaPair_le_endpoint {s : ℝ} (hs : 0 < s) {p i n : ℕ}
    (hpi : p ≤ i) (hin : i + p ≤ n) :
    Real.Gamma (1 + s * (i : ℝ)) * Real.Gamma (1 + s * ((n - i : ℕ) : ℝ))
      ≤ Real.Gamma (1 + s * (p : ℝ)) * Real.Gamma (1 + s * ((n - p : ℕ) : ℝ)) := by
  have hpn : p ≤ n := by omega
  have hinn : i ≤ n := by omega
  have hcastI : ((n - i : ℕ) : ℝ) = (n : ℝ) - (i : ℝ) := by rw [Nat.cast_sub hinn]
  have hcastP : ((n - p : ℕ) : ℝ) = (n : ℝ) - (p : ℝ) := by rw [Nat.cast_sub hpn]
  have hPI : ((p : ℕ) : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_le.mpr hpi
  have hIN : ((i : ℕ) : ℝ) + ((p : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hin
  rw [hcastI, hcastP]
  set P : ℝ := (p : ℝ) with hP
  set I : ℝ := (i : ℝ) with hI
  set N : ℝ := (n : ℝ) with hN
  have hx : (0 : ℝ) < 1 + s * P := by
    have h : (0 : ℝ) ≤ s * P := mul_nonneg hs.le (Nat.cast_nonneg p)
    linarith
  have hy : (0 : ℝ) < 1 + s * (N - P) := by
    have h1 : (0 : ℝ) ≤ N - P := by linarith
    have h : (0 : ℝ) ≤ s * (N - P) := mul_nonneg hs.le h1
    linarith
  rcases eq_or_lt_of_le hPI with hEq | hlt
  · rw [← hEq]
  rcases eq_or_lt_of_le (by linarith : I ≤ N - P) with hEq2 | hlt2
  · have hNI : N - I = P := by rw [hEq2]; ring
    rw [hNI, hEq2]
    exact le_of_eq (mul_comm _ _)
  · have hden : (0 : ℝ) < N - 2 * P := by linarith
    have hdenne : N - 2 * P ≠ 0 := ne_of_gt hden
    set α : ℝ := (N - P - I) / (N - 2 * P) with hα
    set β : ℝ := (I - P) / (N - 2 * P) with hβ
    have hαpos : 0 < α := by
      rw [hα]
      exact div_pos (by linarith) hden
    have hβpos : 0 < β := by
      rw [hβ]
      exact div_pos (by linarith) hden
    have hab : α + β = 1 := by
      rw [hα, hβ, ← add_div, div_eq_one_iff_eq hdenne]
      ring
    have harg1 : α * (1 + s * P) + β * (1 + s * (N - P)) = 1 + s * I := by
      rw [hα, hβ, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hdenne]
      ring
    have harg2 : β * (1 + s * P) + α * (1 + s * (N - P)) = 1 + s * (N - I) := by
      rw [hα, hβ, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hdenne]
      ring
    have h1 := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hx hy hαpos hβpos hab
    have h2 := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hx hy hβpos hαpos
      (by linarith : β + α = 1)
    rw [harg1] at h1
    rw [harg2] at h2
    have hGx : (0 : ℝ) < Real.Gamma (1 + s * P) := Real.Gamma_pos_of_pos hx
    have hGy : (0 : ℝ) < Real.Gamma (1 + s * (N - P)) := Real.Gamma_pos_of_pos hy
    have hGI : (0 : ℝ) < Real.Gamma (1 + s * (N - I)) := by
      refine Real.Gamma_pos_of_pos ?_
      have h1' : (0 : ℝ) ≤ N - I := by linarith
      have : (0 : ℝ) ≤ s * (N - I) := mul_nonneg hs.le h1'
      linarith
    have hprod : Real.Gamma (1 + s * P) ^ α * Real.Gamma (1 + s * (N - P)) ^ β *
        (Real.Gamma (1 + s * P) ^ β * Real.Gamma (1 + s * (N - P)) ^ α)
        = Real.Gamma (1 + s * P) * Real.Gamma (1 + s * (N - P)) := by
      rw [show Real.Gamma (1 + s * P) ^ α * Real.Gamma (1 + s * (N - P)) ^ β *
          (Real.Gamma (1 + s * P) ^ β * Real.Gamma (1 + s * (N - P)) ^ α)
          = (Real.Gamma (1 + s * P) ^ α * Real.Gamma (1 + s * P) ^ β) *
            (Real.Gamma (1 + s * (N - P)) ^ β * Real.Gamma (1 + s * (N - P)) ^ α) by ring,
        ← Real.rpow_add hGx, ← Real.rpow_add hGy, hab, show β + α = (1 : ℝ) by linarith,
        Real.rpow_one, Real.rpow_one]
    calc Real.Gamma (1 + s * I) * Real.Gamma (1 + s * (N - I))
        ≤ (Real.Gamma (1 + s * P) ^ α * Real.Gamma (1 + s * (N - P)) ^ β) *
          (Real.Gamma (1 + s * P) ^ β * Real.Gamma (1 + s * (N - P)) ^ α) :=
          mul_le_mul h1 h2 hGI.le (by positivity)
      _ = Real.Gamma (1 + s * P) * Real.Gamma (1 + s * (N - P)) := hprod

/-! ### The full convolution sum -/

set_option maxHeartbeats 1600000 in
/-- **The convolution sum of a gamma profile is a bounded multiple of its first term.** -/
theorem exists_gammaConvolution_bound {s : ℝ} (hs : 0 < s) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      ∑ i ∈ Finset.Ico 1 n,
          Real.Gamma (1 + s * (i : ℝ)) * Real.Gamma (1 + s * ((n - i : ℕ) : ℝ))
        ≤ K * (Real.Gamma (1 + s * (1 : ℝ)) * Real.Gamma (1 + s * ((n - 1 : ℕ) : ℝ))) := by
  classical
  set p : ℕ := ⌈(2 : ℝ) / s⌉₊ + 2 with hpdef
  have hp2 : 2 ≤ p := by omega
  have hpR : ((p : ℝ) - 1) = (⌈(2 : ℝ) / s⌉₊ : ℝ) + 1 := by
    rw [hpdef]; push_cast; ring
  have hsp : 2 ≤ s * ((p : ℝ) - 1) := by
    have h1 : (2 : ℝ) / s ≤ (⌈(2 : ℝ) / s⌉₊ : ℝ) := Nat.le_ceil _
    rw [hpR]
    have h2 : (2 : ℝ) / s ≤ (⌈(2 : ℝ) / s⌉₊ : ℝ) + 1 := by linarith
    have h3 : s * ((2 : ℝ) / s) ≤ s * ((⌈(2 : ℝ) / s⌉₊ : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left h2 hs.le
    have h4 : s * ((2 : ℝ) / s) = 2 := by field_simp
    linarith
  set M : ℕ := ⌈s * ((p : ℝ) - 1)⌉₊ + 1 with hMdef
  have hMgt : s * ((p : ℝ) - 1) < (M : ℝ) := by
    have h1 : s * ((p : ℝ) - 1) ≤ (⌈s * ((p : ℝ) - 1)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((M : ℕ) : ℝ) = (⌈s * ((p : ℝ) - 1)⌉₊ : ℝ) + 1 := by
      rw [hMdef]; push_cast; ring
    rw [h2]
    linarith
  have hG1 : (0 : ℝ) < Real.Gamma (1 + s * (1 : ℝ)) := by
    refine Real.Gamma_pos_of_pos ?_
    nlinarith
  have hGp : (0 : ℝ) < Real.Gamma (1 + s * (p : ℝ)) := by
    refine Real.Gamma_pos_of_pos ?_
    have : (0 : ℝ) ≤ s * (p : ℝ) := mul_nonneg hs.le (Nat.cast_nonneg p)
    linarith
  set N : ℕ := max (2 * p) (max (⌈(2 * ((s : ℝ) + (M : ℝ)) + 2) / s⌉₊ + 1)
    (⌈4 * Real.Gamma (1 + s * (p : ℝ)) / (s ^ 2 * Real.Gamma (1 + s * (1 : ℝ)))⌉₊ + 1)) with hNdef
  refine ⟨2 * (p : ℝ) + 1, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn2p : 2 * p ≤ n := le_trans (le_max_left _ _) hn
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hcastn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hcastnp : ((n - p : ℕ) : ℝ) = (n : ℝ) - (p : ℝ) := by
    rw [Nat.cast_sub (by omega : p ≤ n)]
  -- the linear lower bound on the shifted argument
  have hlin : (s / 2) * (n : ℝ) ≤ 1 + s * ((n : ℝ) - 1) - (M : ℝ) := by
    have h1 : (2 * ((s : ℝ) + (M : ℝ)) + 2) / s ≤ ((⌈(2 * ((s : ℝ) + (M : ℝ)) + 2) / s⌉₊ : ℕ) : ℝ) :=
      Nat.le_ceil _
    have h2 : ((⌈(2 * ((s : ℝ) + (M : ℝ)) + 2) / s⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
      have : ⌈(2 * ((s : ℝ) + (M : ℝ)) + 2) / s⌉₊ ≤ n := by
        have hmid : max (⌈(2 * ((s : ℝ) + (M : ℝ)) + 2) / s⌉₊ + 1)
            (⌈4 * Real.Gamma (1 + s * (p : ℝ)) / (s ^ 2 * Real.Gamma (1 + s * (1 : ℝ)))⌉₊ + 1) ≤ n :=
          le_trans (le_max_right _ _) hn
        have := le_trans (le_max_left _ _) hmid
        omega
      exact_mod_cast this
    have h3 : (2 * ((s : ℝ) + (M : ℝ)) + 2) / s ≤ (n : ℝ) := le_trans h1 h2
    rw [div_le_iff₀ hs] at h3
    linarith
  have hone : (1 : ℝ) ≤ 1 + s * ((n : ℝ) - 1) - (M : ℝ) := by
    have h1 : (2 : ℝ) / s ≤ (n : ℝ) := by
      have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      have hsn : (s / 2) * (n : ℝ) ≥ 1 := by nlinarith [hlin, hM0, hs]
      rw [div_le_iff₀ hs]
      linarith
    nlinarith [hlin, hs, h1]
  -- the gamma ratio across the block
  have hxpos : (0 : ℝ) < 1 + s * ((n : ℝ) - (p : ℝ)) := by
    have hnp : (0 : ℝ) ≤ (n : ℝ) - (p : ℝ) := by
      have : (p : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : p ≤ n)
      linarith
    nlinarith
  have htpos : (0 : ℝ) < s * ((p : ℝ) - 1) := by nlinarith
  have hxt : (1 + s * ((n : ℝ) - (p : ℝ))) + s * ((p : ℝ) - 1) = 1 + s * ((n : ℝ) - 1) := by ring
  have hypos : (0 : ℝ) < (1 + s * ((n : ℝ) - (p : ℝ))) + s * ((p : ℝ) - 1) - (M : ℝ) := by
    rw [hxt]; linarith
  have hratio := Gamma_div_Gamma_add_le hxpos htpos hMgt hypos
  rw [hxt] at hratio
  -- turn the ratio into a bound on the middle block
  have hGn1 : (0 : ℝ) < Real.Gamma (1 + s * ((n : ℝ) - 1)) := by
    refine Real.Gamma_pos_of_pos ?_
    linarith
  have hstep : Real.Gamma (1 + s * ((n : ℝ) - (p : ℝ)))
      ≤ (1 + s * ((n : ℝ) - 1) - (M : ℝ)) ^ (-(s * ((p : ℝ) - 1))) *
        Real.Gamma (1 + s * ((n : ℝ) - 1)) := by
    rw [div_le_iff₀ hGn1] at hratio
    linarith [hratio]
  have hexp : (1 + s * ((n : ℝ) - 1) - (M : ℝ)) ^ (-(s * ((p : ℝ) - 1)))
      ≤ (1 + s * ((n : ℝ) - 1) - (M : ℝ)) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hone (by linarith)
  have hsq : (1 + s * ((n : ℝ) - 1) - (M : ℝ)) ^ (-(2 : ℝ))
      = ((1 + s * ((n : ℝ) - 1) - (M : ℝ)) ^ (2 : ℕ))⁻¹ := by
    rw [Real.rpow_neg (by linarith), ← Real.rpow_natCast _ 2]
    norm_num
  have hlow2 : ((s / 2) * (n : ℝ)) ^ (2 : ℕ) ≤ (1 + s * ((n : ℝ) - 1) - (M : ℝ)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hlin 2
  have hsqpos : (0 : ℝ) < ((s / 2) * (n : ℝ)) ^ (2 : ℕ) := by positivity
  have hmiddle : (n : ℝ) * Real.Gamma (1 + s * (p : ℝ)) *
      ((1 + s * ((n : ℝ) - 1) - (M : ℝ)) ^ (2 : ℕ))⁻¹
      ≤ Real.Gamma (1 + s * (1 : ℝ)) := by
    have h1 : ((1 + s * ((n : ℝ) - 1) - (M : ℝ)) ^ (2 : ℕ))⁻¹ ≤ (((s / 2) * (n : ℝ)) ^ (2 : ℕ))⁻¹ := by
      have hh := one_div_le_one_div_of_le hsqpos hlow2
      rwa [one_div, one_div] at hh
    have h2 : (n : ℝ) * Real.Gamma (1 + s * (p : ℝ)) *
        ((1 + s * ((n : ℝ) - 1) - (M : ℝ)) ^ (2 : ℕ))⁻¹
        ≤ (n : ℝ) * Real.Gamma (1 + s * (p : ℝ)) * (((s / 2) * (n : ℝ)) ^ (2 : ℕ))⁻¹ :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    refine le_trans h2 ?_
    have h3 : (n : ℝ) * Real.Gamma (1 + s * (p : ℝ)) * (((s / 2) * (n : ℝ)) ^ (2 : ℕ))⁻¹
        = 4 * Real.Gamma (1 + s * (p : ℝ)) / (s ^ 2 * (n : ℝ)) := by
      field_simp
      ring
    rw [h3]
    have hthr : 4 * Real.Gamma (1 + s * (p : ℝ)) / (s ^ 2 * Real.Gamma (1 + s * (1 : ℝ)))
        ≤ (n : ℝ) := by
      have h1' : 4 * Real.Gamma (1 + s * (p : ℝ)) / (s ^ 2 * Real.Gamma (1 + s * (1 : ℝ)))
          ≤ ((⌈4 * Real.Gamma (1 + s * (p : ℝ)) /
              (s ^ 2 * Real.Gamma (1 + s * (1 : ℝ)))⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h2' : ⌈4 * Real.Gamma (1 + s * (p : ℝ)) /
          (s ^ 2 * Real.Gamma (1 + s * (1 : ℝ)))⌉₊ ≤ n := by
        have hmid : max (⌈(2 * ((s : ℝ) + (M : ℝ)) + 2) / s⌉₊ + 1)
            (⌈4 * Real.Gamma (1 + s * (p : ℝ)) /
              (s ^ 2 * Real.Gamma (1 + s * (1 : ℝ)))⌉₊ + 1) ≤ n :=
          le_trans (le_max_right _ _) hn
        have := le_trans (le_max_right _ _) hmid
        omega
      have h3' : ((⌈4 * Real.Gamma (1 + s * (p : ℝ)) /
          (s ^ 2 * Real.Gamma (1 + s * (1 : ℝ)))⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2'
      linarith
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < s ^ 2 * (n : ℝ))]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < s ^ 2 * Real.Gamma (1 + s * (1 : ℝ)))] at hthr
    nlinarith [hthr, hG1, hnR, hs]
  -- assemble the three blocks
  set B1 : ℝ := Real.Gamma (1 + s * (1 : ℝ)) * Real.Gamma (1 + s * ((n - 1 : ℕ) : ℝ)) with hB1
  have hB1pos : (0 : ℝ) < B1 := by
    rw [hB1]
    have h2 : (0 : ℝ) < Real.Gamma (1 + s * ((n - 1 : ℕ) : ℝ)) := by
      refine Real.Gamma_pos_of_pos ?_
      have : (0 : ℝ) ≤ s * ((n - 1 : ℕ) : ℝ) := mul_nonneg hs.le (Nat.cast_nonneg _)
      linarith
    exact mul_pos hG1 h2
  have hcardA : ((Finset.Ico 1 p).card : ℝ) ≤ (p : ℝ) := by
    rw [Nat.card_Ico]
    have : ((p - 1 : ℕ) : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr (by omega)
    exact this
  have hcardC : ((Finset.Ico (n - p + 1) n).card : ℝ) ≤ (p : ℝ) := by
    rw [Nat.card_Ico]
    have : (n - (n - p + 1)) ≤ p := by omega
    exact_mod_cast this
  have hcardB : ((Finset.Ico p (n - p + 1)).card : ℝ) ≤ (n : ℝ) := by
    rw [Nat.card_Ico]
    have : (n - p + 1 - p) ≤ n := by omega
    exact_mod_cast this
  have hA : ∑ i ∈ Finset.Ico 1 p,
      Real.Gamma (1 + s * (i : ℝ)) * Real.Gamma (1 + s * ((n - i : ℕ) : ℝ)) ≤ (p : ℝ) * B1 := by
    have hb : ∀ i ∈ Finset.Ico 1 p,
        Real.Gamma (1 + s * (i : ℝ)) * Real.Gamma (1 + s * ((n - i : ℕ) : ℝ)) ≤ B1 := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      have h := gammaPair_le_endpoint hs (p := 1) (i := i) (n := n) hi.1 (by omega)
      rw [Nat.cast_one] at h
      exact h
    have hsum := Finset.sum_le_card_nsmul _ _ _ hb
    rw [nsmul_eq_mul] at hsum
    refine le_trans hsum ?_
    exact mul_le_mul_of_nonneg_right hcardA hB1pos.le
  have hC : ∑ i ∈ Finset.Ico (n - p + 1) n,
      Real.Gamma (1 + s * (i : ℝ)) * Real.Gamma (1 + s * ((n - i : ℕ) : ℝ)) ≤ (p : ℝ) * B1 := by
    have hb : ∀ i ∈ Finset.Ico (n - p + 1) n,
        Real.Gamma (1 + s * (i : ℝ)) * Real.Gamma (1 + s * ((n - i : ℕ) : ℝ)) ≤ B1 := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      have h := gammaPair_le_endpoint hs (p := 1) (i := n - i) (n := n) (by omega) (by omega)
      rw [Nat.cast_one] at h
      have hrw : n - (n - i) = i := by omega
      rw [hrw] at h
      calc Real.Gamma (1 + s * (i : ℝ)) * Real.Gamma (1 + s * ((n - i : ℕ) : ℝ))
          = Real.Gamma (1 + s * ((n - i : ℕ) : ℝ)) * Real.Gamma (1 + s * (i : ℝ)) := by ring
        _ ≤ B1 := h
    have hsum := Finset.sum_le_card_nsmul _ _ _ hb
    rw [nsmul_eq_mul] at hsum
    refine le_trans hsum ?_
    exact mul_le_mul_of_nonneg_right hcardC hB1pos.le
  have hB : ∑ i ∈ Finset.Ico p (n - p + 1),
      Real.Gamma (1 + s * (i : ℝ)) * Real.Gamma (1 + s * ((n - i : ℕ) : ℝ)) ≤ B1 := by
    have hb : ∀ i ∈ Finset.Ico p (n - p + 1),
        Real.Gamma (1 + s * (i : ℝ)) * Real.Gamma (1 + s * ((n - i : ℕ) : ℝ))
          ≤ Real.Gamma (1 + s * (p : ℝ)) * Real.Gamma (1 + s * ((n - p : ℕ) : ℝ)) := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      exact gammaPair_le_endpoint hs hi.1 (by omega)
    have hsum := Finset.sum_le_card_nsmul _ _ _ hb
    rw [nsmul_eq_mul] at hsum
    have hGnp : Real.Gamma (1 + s * ((n - p : ℕ) : ℝ))
        ≤ ((1 + s * ((n : ℝ) - 1) - (M : ℝ)) ^ (2 : ℕ))⁻¹ *
          Real.Gamma (1 + s * ((n - 1 : ℕ) : ℝ)) := by
      rw [hcastnp, hcastn1]
      refine le_trans hstep ?_
      refine mul_le_mul_of_nonneg_right ?_ hGn1.le
      rw [← hsq]
      exact hexp
    have hchain : ((Finset.Ico p (n - p + 1)).card : ℝ) *
        (Real.Gamma (1 + s * (p : ℝ)) * Real.Gamma (1 + s * ((n - p : ℕ) : ℝ))) ≤ B1 := by
      have h1 : ((Finset.Ico p (n - p + 1)).card : ℝ) *
          (Real.Gamma (1 + s * (p : ℝ)) * Real.Gamma (1 + s * ((n - p : ℕ) : ℝ)))
          ≤ (n : ℝ) * (Real.Gamma (1 + s * (p : ℝ)) *
            (((1 + s * ((n : ℝ) - 1) - (M : ℝ)) ^ (2 : ℕ))⁻¹ *
              Real.Gamma (1 + s * ((n - 1 : ℕ) : ℝ)))) := by
        refine mul_le_mul hcardB ?_ (by positivity) hnR.le
        exact mul_le_mul_of_nonneg_left hGnp hGp.le
      refine le_trans h1 ?_
      have h2 : (n : ℝ) * (Real.Gamma (1 + s * (p : ℝ)) *
          (((1 + s * ((n : ℝ) - 1) - (M : ℝ)) ^ (2 : ℕ))⁻¹ *
            Real.Gamma (1 + s * ((n - 1 : ℕ) : ℝ))))
          = ((n : ℝ) * Real.Gamma (1 + s * (p : ℝ)) *
              ((1 + s * ((n : ℝ) - 1) - (M : ℝ)) ^ (2 : ℕ))⁻¹) *
            Real.Gamma (1 + s * ((n - 1 : ℕ) : ℝ)) := by ring
      rw [h2, hB1]
      refine mul_le_mul_of_nonneg_right hmiddle ?_
      refine le_of_lt (Real.Gamma_pos_of_pos ?_)
      have : (0 : ℝ) ≤ s * ((n - 1 : ℕ) : ℝ) := mul_nonneg hs.le (Nat.cast_nonneg _)
      linarith
    exact le_trans hsum hchain
  have hs1 : ∑ i ∈ Finset.Ico 1 p,
        Real.Gamma (1 + s * (i : ℝ)) * Real.Gamma (1 + s * ((n - i : ℕ) : ℝ)) +
      ∑ i ∈ Finset.Ico p (n - p + 1),
        Real.Gamma (1 + s * (i : ℝ)) * Real.Gamma (1 + s * ((n - i : ℕ) : ℝ))
      = ∑ i ∈ Finset.Ico 1 (n - p + 1),
        Real.Gamma (1 + s * (i : ℝ)) * Real.Gamma (1 + s * ((n - i : ℕ) : ℝ)) :=
    Finset.sum_Ico_consecutive _ (by omega) (by omega)
  have hs2 : ∑ i ∈ Finset.Ico 1 (n - p + 1),
        Real.Gamma (1 + s * (i : ℝ)) * Real.Gamma (1 + s * ((n - i : ℕ) : ℝ)) +
      ∑ i ∈ Finset.Ico (n - p + 1) n,
        Real.Gamma (1 + s * (i : ℝ)) * Real.Gamma (1 + s * ((n - i : ℕ) : ℝ))
      = ∑ i ∈ Finset.Ico 1 n,
        Real.Gamma (1 + s * (i : ℝ)) * Real.Gamma (1 + s * ((n - i : ℕ) : ℝ)) :=
    Finset.sum_Ico_consecutive _ (by omega) (by omega)
  have hppos : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  calc ∑ i ∈ Finset.Ico 1 n,
        Real.Gamma (1 + s * (i : ℝ)) * Real.Gamma (1 + s * ((n - i : ℕ) : ℝ))
      = (∑ i ∈ Finset.Ico 1 p,
            Real.Gamma (1 + s * (i : ℝ)) * Real.Gamma (1 + s * ((n - i : ℕ) : ℝ)) +
          ∑ i ∈ Finset.Ico p (n - p + 1),
            Real.Gamma (1 + s * (i : ℝ)) * Real.Gamma (1 + s * ((n - i : ℕ) : ℝ))) +
        ∑ i ∈ Finset.Ico (n - p + 1) n,
          Real.Gamma (1 + s * (i : ℝ)) * Real.Gamma (1 + s * ((n - i : ℕ) : ℝ)) := by
        rw [hs1, hs2]
    _ ≤ ((p : ℝ) * B1 + B1) + (p : ℝ) * B1 := by
        refine add_le_add (add_le_add hA hB) hC
    _ = (2 * (p : ℝ) + 1) * B1 := by ring

/-- The same estimate for the full profile `Γ(1+sk) β^k`: the geometric factor cancels. -/
theorem exists_gammaProfile_convolution_bound {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      ∑ i ∈ Finset.Ico 1 n, gammaProfile s β i * gammaProfile s β (n - i)
        ≤ K * (gammaProfile s β 1 * gammaProfile s β (n - 1)) := by
  obtain ⟨K, hK, hev⟩ := exists_gammaConvolution_bound hs
  refine ⟨K, hK, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hβn : (0 : ℝ) < β ^ n := pow_pos hβ n
  have hsplit : ∀ i ∈ Finset.Ico 1 n,
      gammaProfile s β i * gammaProfile s β (n - i)
        = (Real.Gamma (1 + s * (i : ℝ)) * Real.Gamma (1 + s * ((n - i : ℕ) : ℝ))) * β ^ n := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [gammaProfile, gammaProfile,
      show Real.Gamma (1 + s * (i : ℝ)) * β ^ i *
          (Real.Gamma (1 + s * ((n - i : ℕ) : ℝ)) * β ^ (n - i))
        = (Real.Gamma (1 + s * (i : ℝ)) * Real.Gamma (1 + s * ((n - i : ℕ) : ℝ))) *
          (β ^ i * β ^ (n - i)) by ring,
      ← pow_add, show i + (n - i) = n from by omega]
  have hrhs : gammaProfile s β 1 * gammaProfile s β (n - 1)
      = (Real.Gamma (1 + s * (1 : ℝ)) * Real.Gamma (1 + s * ((n - 1 : ℕ) : ℝ))) * β ^ n := by
    rw [gammaProfile, gammaProfile,
      show Real.Gamma (1 + s * ((1 : ℕ) : ℝ)) * β ^ 1 *
          (Real.Gamma (1 + s * ((n - 1 : ℕ) : ℝ)) * β ^ (n - 1))
        = (Real.Gamma (1 + s * ((1 : ℕ) : ℝ)) * Real.Gamma (1 + s * ((n - 1 : ℕ) : ℝ))) *
          (β ^ 1 * β ^ (n - 1)) by ring,
      ← pow_add, show 1 + (n - 1) = n from by omega, Nat.cast_one]
  rw [Finset.sum_congr rfl hsplit, ← Finset.sum_mul, hrhs]
  calc (∑ i ∈ Finset.Ico 1 n,
        Real.Gamma (1 + s * (i : ℝ)) * Real.Gamma (1 + s * ((n - i : ℕ) : ℝ))) * β ^ n
      ≤ (K * (Real.Gamma (1 + s * (1 : ℝ)) * Real.Gamma (1 + s * ((n - 1 : ℕ) : ℝ)))) * β ^ n :=
        mul_le_mul_of_nonneg_right hn hβn.le
    _ = K * ((Real.Gamma (1 + s * (1 : ℝ)) * Real.Gamma (1 + s * ((n - 1 : ℕ) : ℝ))) * β ^ n) := by
        ring

end GaloisForLFunctions.HTGeometry
