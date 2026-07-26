import GaloisForLFunctions.RHTower.MFreeLadder
import GaloisForLFunctions.RHTower.GammaInvGrowth

/-!
# High-exponent shells: a zero-free multiplier and the full zeta divisor

For `m ≥ 1` the *shell indicator* `a_m = [·, (m+1)-free] - [·, m-free]` is the indicator of the
integers whose largest prime exponent is exactly `m`.  Distinct shells have disjoint supports.
Its Dirichlet series factors through the `m`-free Möbius ladder of `MFreeLadder`:

```text
S_m(s) = ∑ a_m(n) n^(-s) = ζ(s) H_m(s),      H_m(s) = ζ((m+1)s)⁻¹ - ζ(ms)⁻¹ .
```

The main analytic content is that `H_m` acquires **no** zero of its own in the strict right
half-plane once `m` is large:

* `RHTower.riemannZeta_natCast_mul_sub_succ_mul_ne_zero` — for every `m ≥ 12`,
  `ζ(ms) - ζ((m+1)s) ≠ 0` whenever `re s > 1/2`;
* `RHTower.shellMultiplier_ne_zero` — hence `H_m(s) ≠ 0` there;
* `RHTower.analyticOrderAt_riemannZeta_mul_shellMultiplier` — the completed shell current
  `ζ · H_m` has, at every point of `re s > 1/2`, exactly the vanishing order of `ζ` itself:
  the shell carries the full strict right-half zeta divisor with the same multiplicities.

The proof of nonvanishing is a one-term domination.  On `re s > 1/2` and `m ≥ 12` the exponent
`m·re s` exceeds `6`, so the `n = 2` term of the absolutely convergent series
`ζ(ms) - ζ((m+1)s) = ∑_{n≥2} (n^{-ms} - n^{-(m+1)s})` strictly dominates the whole tail:
after normalising by `2^{-m·re s}` the head is at least `29/100` while the tail is at most
`(512/5)(3^{-6} + 4^{-6} + 1/2500) < 21/100`.
-/

noncomputable section

namespace RHTower

open Complex Filter ArithmeticFunction
open scoped LSeries.notation

/-! ## The high-exponent shell indicator -/

/-- The high-exponent shell indicator: `shellIndicator m n = 1` exactly when the largest
exponent in the prime factorisation of `n` equals `m`, and `0` otherwise. -/
def shellIndicator (m : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => mFreeIndicator (m + 1) n - mFreeIndicator m n, by simp⟩

@[simp] theorem shellIndicator_apply (m n : ℕ) :
    shellIndicator m n = mFreeIndicator (m + 1) n - mFreeIndicator m n := rfl

/-- `m`-freeness is inherited upwards along the exponent. -/
theorem mFree_of_le {m k n : ℕ} (hmk : m ≤ k) (h : MFree m n) : MFree k n :=
  fun p hp hdvd => h p hp ((pow_dvd_pow p hmk).trans hdvd)

theorem shellIndicator_eq_one_iff (m n : ℕ) :
    shellIndicator m n = 1 ↔ MFree (m + 1) n ∧ ¬ MFree m n := by
  rw [shellIndicator_apply, mFreeIndicator_apply, mFreeIndicator_apply]
  by_cases h2 : MFree m n
  · have h1 : MFree (m + 1) n := mFree_of_le (Nat.le_succ m) h2
    simp [h1, h2]
  · by_cases h1 : MFree (m + 1) n <;> simp [h1, h2]

theorem shellIndicator_eq_zero_or_one (m n : ℕ) :
    shellIndicator m n = 0 ∨ shellIndicator m n = 1 := by
  rw [shellIndicator_apply, mFreeIndicator_apply, mFreeIndicator_apply]
  by_cases h2 : MFree m n
  · have h1 : MFree (m + 1) n := mFree_of_le (Nat.le_succ m) h2
    simp [h1, h2]
  · by_cases h1 : MFree (m + 1) n <;> simp [h1, h2]

/-- **Disjoint shell supports.**  An integer belongs to at most one high-exponent shell. -/
theorem shellIndicator_eq_zero_of_ne {m k n : ℕ} (hmk : m ≠ k)
    (hm : shellIndicator m n ≠ 0) : shellIndicator k n = 0 := by
  by_contra hk
  obtain hm1 := (shellIndicator_eq_zero_or_one m n).resolve_left hm
  obtain hk1 := (shellIndicator_eq_zero_or_one k n).resolve_left hk
  obtain ⟨hmfree, hmnot⟩ := (shellIndicator_eq_one_iff m n).mp hm1
  obtain ⟨hkfree, hknot⟩ := (shellIndicator_eq_one_iff k n).mp hk1
  rcases lt_or_gt_of_ne hmk with h | h
  · exact hknot (mFree_of_le h hmfree)
  · exact hmnot (mFree_of_le h hkfree)

/-! ## The shell multiplier and its Dirichlet series -/

/-- The high-exponent shell multiplier `H_m(s) = ζ((m+1)s)⁻¹ - ζ(ms)⁻¹`. -/
def shellMultiplier (m : ℕ) (s : ℂ) : ℂ :=
  (riemannZeta (((m : ℂ) + 1) * s))⁻¹ - (riemannZeta ((m : ℂ) * s))⁻¹

theorem LSeriesSummable_mFreeIndicator (m : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable ↗(mFreeIndicator m) s := by
  refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => ?_) hs
  rw [mFreeIndicator_apply]
  split_ifs <;> simp

/-- **The shell Dirichlet series.**  `∑ a_m(n) n^{-s} = ζ(s) H_m(s)` on `re s > 1`. -/
theorem LSeries_shellIndicator {m : ℕ} (hm : m ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(shellIndicator m) s = riemannZeta s * shellMultiplier m s := by
  have hfun : ↗(shellIndicator m) = ↗(mFreeIndicator (m + 1)) - ↗(mFreeIndicator m) := by
    funext n; simp
  rw [hfun, LSeries_sub (LSeriesSummable_mFreeIndicator (m + 1) hs)
      (LSeriesSummable_mFreeIndicator m hs),
    LSeries_mFree_eq_riemannZeta_div (Nat.succ_ne_zero m) hs,
    LSeries_mFree_eq_riemannZeta_div hm hs, shellMultiplier]
  push_cast
  ring

/-! ## Elementary norm and power estimates -/

private theorem norm_one_div_natCast_cpow {n : ℕ} {z : ℂ} (hz : z.re ≠ 0) :
    ‖1 / (n : ℂ) ^ z‖ = (((n : ℝ)) ^ z.re)⁻¹ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hz0 : z ≠ 0 := fun h => hz (by simp [h])
    simp [Complex.zero_cpow hz0, Real.zero_rpow hz]
  · rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hn, one_div]

private theorem rpow_six_eq (x : ℝ) : x ^ (6 : ℝ) = x ^ (6 : ℕ) := by
  rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- `√2 < 2^σ` for `σ > 1/2`, in the crude rational form used below. -/
private theorem inv_two_rpow_lt {σ : ℝ} (hσ : 1 / 2 < σ) : ((2 : ℝ) ^ σ)⁻¹ < 71 / 100 := by
  have hbase : Real.sqrt 2 ≤ (2 : ℝ) ^ σ := by
    rw [Real.sqrt_eq_rpow]
    exact (Real.rpow_le_rpow_left_iff (by norm_num)).mpr (by linarith)
  have hlt : (100 : ℝ) / 71 < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have h : (100 : ℝ) / 71 < (2 : ℝ) ^ σ := lt_of_lt_of_le hlt hbase
  have hpos : (0 : ℝ) < (2 : ℝ) ^ σ := Real.rpow_pos_of_pos (by norm_num) _
  rw [inv_lt_iff_one_lt_mul₀ hpos]
  nlinarith

/-- `√3 < n^σ` for `σ > 1/2` and `n ≥ 3`, in the crude rational form used below. -/
private theorem inv_rpow_lt_three_fifths {σ x : ℝ} (hσ : 1 / 2 < σ) (hx : 3 ≤ x) :
    (x ^ σ)⁻¹ < 3 / 5 := by
  have h3 : Real.sqrt 3 ≤ (3 : ℝ) ^ σ := by
    rw [Real.sqrt_eq_rpow]
    exact (Real.rpow_le_rpow_left_iff (by norm_num)).mpr (by linarith)
  have hmono : (3 : ℝ) ^ σ ≤ x ^ σ := Real.rpow_le_rpow (by norm_num) hx (by linarith)
  have hlt : (5 : ℝ) / 3 < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have h : (5 : ℝ) / 3 < x ^ σ := lt_of_lt_of_le hlt (h3.trans hmono)
  have hpos : (0 : ℝ) < x ^ σ := lt_trans (by norm_num) h
  rw [inv_lt_iff_one_lt_mul₀ hpos]
  nlinarith

/-! ## The tail of the sixth-power series -/

private theorem summable_shift_inv_pow (p j : ℕ) (hp : 1 < p) :
    Summable (fun k : ℕ => (((k : ℝ) + (j : ℝ)) ^ p)⁻¹) := by
  have h0 : Summable (fun n : ℕ => (((n : ℝ)) ^ p)⁻¹) := by
    have h : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ p) :=
      (Real.summable_one_div_nat_pow (p := p)).mpr hp
    simpa [one_div] using h
  have h := (summable_nat_add_iff (f := fun n : ℕ => (((n : ℝ)) ^ p)⁻¹) j).2 h0
  simpa using h

private theorem summable_shift_six (j : ℕ) :
    Summable (fun k : ℕ => (((k : ℝ) + (j : ℝ)) ^ (6 : ℕ))⁻¹) :=
  summable_shift_inv_pow 6 j (by norm_num)

private theorem tsum_shift_inv_pow_six_five :
    ∑' k : ℕ, (((k : ℝ) + 5) ^ (6 : ℕ))⁻¹ ≤ 1 / 2500 := by
  have hS6 : Summable (fun k : ℕ => (((k : ℝ) + 5) ^ (6 : ℕ))⁻¹) := by
    simpa using summable_shift_six 5
  have hS2 : Summable (fun k : ℕ => (((k : ℝ) + 5) ^ (2 : ℕ))⁻¹) := by
    simpa using summable_shift_inv_pow 2 5 (by norm_num)
  have hsq : ∑' k : ℕ, (((k : ℝ) + 5) ^ (2 : ℕ))⁻¹ ≤ 1 / 4 := by
    have h := HilbertSchmidt.tsum_reciprocal_square_tail_le (m := 4) (by norm_num)
    have hfun : (fun k : ℕ => 1 / (((4 + k : ℕ) : ℝ) + 1) ^ 2)
        = fun k : ℕ => (((k : ℝ) + 5) ^ (2 : ℕ))⁻¹ := by
      funext k
      push_cast
      rw [one_div]
      ring_nf
    rw [hfun] at h
    simpa using h
  have hterm : ∀ k : ℕ,
      (((k : ℝ) + 5) ^ (6 : ℕ))⁻¹ ≤ (1 / 625) * (((k : ℝ) + 5) ^ (2 : ℕ))⁻¹ := by
    intro k
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h4 : (625 : ℝ) ≤ ((k : ℝ) + 5) ^ (4 : ℕ) := by
      calc (625 : ℝ) = (5 : ℝ) ^ (4 : ℕ) := by norm_num
        _ ≤ ((k : ℝ) + 5) ^ (4 : ℕ) := pow_le_pow_left₀ (by norm_num) (by linarith) 4
    have h2pos : (0 : ℝ) < ((k : ℝ) + 5) ^ (2 : ℕ) := by positivity
    have hsplit : ((k : ℝ) + 5) ^ (6 : ℕ) = ((k : ℝ) + 5) ^ (2 : ℕ) * ((k : ℝ) + 5) ^ (4 : ℕ) := by
      ring
    have hle : (625 : ℝ) * ((k : ℝ) + 5) ^ (2 : ℕ) ≤ ((k : ℝ) + 5) ^ (6 : ℕ) := by
      rw [hsplit]; nlinarith
    calc (((k : ℝ) + 5) ^ (6 : ℕ))⁻¹
        ≤ ((625 : ℝ) * ((k : ℝ) + 5) ^ (2 : ℕ))⁻¹ := inv_anti₀ (by positivity) hle
      _ = (1 / 625) * (((k : ℝ) + 5) ^ (2 : ℕ))⁻¹ := by rw [mul_inv, one_div]
  calc ∑' k : ℕ, (((k : ℝ) + 5) ^ (6 : ℕ))⁻¹
      ≤ ∑' k : ℕ, (1 / 625) * (((k : ℝ) + 5) ^ (2 : ℕ))⁻¹ :=
        Summable.tsum_le_tsum hterm hS6 (hS2.mul_left _)
    _ = (1 / 625) * ∑' k : ℕ, (((k : ℝ) + 5) ^ (2 : ℕ))⁻¹ := tsum_mul_left
    _ ≤ (1 / 625) * (1 / 4) := mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = 1 / 2500 := by norm_num

/-- The sixth-power tail beginning at `3` is at most `3^{-6} + 4^{-6} + 1/2500`. -/
theorem tsum_shift_inv_pow_six_three :
    ∑' k : ℕ, (((k : ℝ) + 3) ^ (6 : ℕ))⁻¹ ≤ 1 / 729 + 1 / 4096 + 1 / 2500 := by
  have hS3 : Summable (fun k : ℕ => (((k : ℝ) + 3) ^ (6 : ℕ))⁻¹) := by
    simpa using summable_shift_six 3
  have hS4 : Summable (fun k : ℕ => (((k : ℝ) + 4) ^ (6 : ℕ))⁻¹) := by
    simpa using summable_shift_six 4
  have h3 : ∑' k : ℕ, (((k : ℝ) + 3) ^ (6 : ℕ))⁻¹
      = ((3 : ℝ) ^ (6 : ℕ))⁻¹ + ∑' k : ℕ, (((k : ℝ) + 4) ^ (6 : ℕ))⁻¹ := by
    rw [hS3.tsum_eq_zero_add]
    congr 1
    · norm_num
    · exact tsum_congr fun k => by push_cast; ring_nf
  have h4 : ∑' k : ℕ, (((k : ℝ) + 4) ^ (6 : ℕ))⁻¹
      = ((4 : ℝ) ^ (6 : ℕ))⁻¹ + ∑' k : ℕ, (((k : ℝ) + 5) ^ (6 : ℕ))⁻¹ := by
    rw [hS4.tsum_eq_zero_add]
    congr 1
    · norm_num
    · exact tsum_congr fun k => by push_cast; ring_nf
  rw [h3, h4]
  have h5 := tsum_shift_inv_pow_six_five
  have e3 : ((3 : ℝ) ^ (6 : ℕ))⁻¹ = 1 / 729 := by norm_num
  have e4 : ((4 : ℝ) ^ (6 : ℕ))⁻¹ = 1 / 4096 := by norm_num
  rw [e3, e4]
  linarith

/-! ## The prime-two head and the strictly dominated tail -/

/-- The prime-two head `2^{-ms} - 2^{-(m+1)s}` of the shell difference. -/
def shellHead (m : ℕ) (s : ℂ) : ℂ :=
  1 / (2 : ℂ) ^ ((m : ℂ) * s) - 1 / (2 : ℂ) ^ (((m : ℂ) + 1) * s)

private theorem norm_one_div_two_cpow (z : ℂ) : ‖1 / (2 : ℂ) ^ z‖ = ((2 : ℝ) ^ z.re)⁻¹ := by
  rw [norm_div, norm_one, show ((2 : ℂ)) = ((2 : ℝ) : ℂ) by norm_num,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), one_div]

/-- The prime-two head is at least `29/100` of the normalising scale `2^{-m·re s}`, for every
`m` and every `s` in the strict right half-plane. -/
theorem le_norm_shellHead (m : ℕ) {s : ℂ} (hs : 1 / 2 < s.re) :
    ((2 : ℝ) ^ ((m : ℝ) * s.re))⁻¹ * (29 / 100) ≤ ‖shellHead m s‖ := by
  have hAre : ((m : ℂ) * s).re = (m : ℝ) * s.re := by simp [Complex.mul_re]
  have hBre : (((m : ℂ) + 1) * s).re = (m : ℝ) * s.re + s.re := by
    have h : (((m : ℂ) + 1) * s).re = ((m : ℝ) + 1) * s.re := by simp [Complex.mul_re]
    rw [h]; ring
  have hcpos : (0 : ℝ) < ((2 : ℝ) ^ ((m : ℝ) * s.re))⁻¹ :=
    inv_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)
  have e1 : ‖1 / (2 : ℂ) ^ ((m : ℂ) * s)‖ = ((2 : ℝ) ^ ((m : ℝ) * s.re))⁻¹ := by
    rw [norm_one_div_two_cpow, hAre]
  have e2 : ‖1 / (2 : ℂ) ^ (((m : ℂ) + 1) * s)‖
      = ((2 : ℝ) ^ ((m : ℝ) * s.re))⁻¹ * ((2 : ℝ) ^ s.re)⁻¹ := by
    rw [norm_one_div_two_cpow, hBre, Real.rpow_add (by norm_num), mul_inv]
  have hle : ‖1 / (2 : ℂ) ^ (((m : ℂ) + 1) * s)‖
      ≤ ((2 : ℝ) ^ ((m : ℝ) * s.re))⁻¹ * (71 / 100) := by
    rw [e2]
    exact mul_le_mul_of_nonneg_left (le_of_lt (inv_two_rpow_lt hs)) (le_of_lt hcpos)
  have hsub := norm_sub_norm_le (1 / (2 : ℂ) ^ ((m : ℂ) * s)) (1 / (2 : ℂ) ^ (((m : ℂ) + 1) * s))
  rw [e1] at hsub
  rw [shellHead]
  linarith

/-- **Prime-two domination.**  For every `m ≥ 12` and every `s` with `re s > 1/2`, the whole
tail of `ζ(ms) - ζ((m+1)s)` beyond its `n = 2` term is at most
`(512/5)(3^{-6} + 4^{-6} + 1/2500) < 21/100` times the normalising scale `2^{-m·re s}`. -/
theorem norm_riemannZeta_diff_sub_shellHead_le
    {m : ℕ} (hm : 12 ≤ m) {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖riemannZeta ((m : ℂ) * s) - riemannZeta (((m : ℂ) + 1) * s) - shellHead m s‖
      ≤ ((2 : ℝ) ^ ((m : ℝ) * s.re))⁻¹ * (512 / 5) * (1 / 729 + 1 / 4096 + 1 / 2500) := by
  have hm12 : (12 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hσ0 : (0 : ℝ) < s.re := by linarith
  have hAre : ((m : ℂ) * s).re = (m : ℝ) * s.re := by simp [Complex.mul_re]
  have hBre : (((m : ℂ) + 1) * s).re = ((m : ℝ) + 1) * s.re := by simp [Complex.mul_re]
  have hA6 : (6 : ℝ) < (m : ℝ) * s.re := by nlinarith
  have hA1 : 1 < ((m : ℂ) * s).re := by rw [hAre]; linarith
  have hB1 : 1 < (((m : ℂ) + 1) * s).re := by rw [hBre]; nlinarith
  set α : ℂ := (m : ℂ) * s with hαdef
  set β : ℂ := ((m : ℂ) + 1) * s with hβdef
  have hαre : α.re = (m : ℝ) * s.re := hAre
  have hβre : β.re = (m : ℝ) * s.re + s.re := by rw [hBre]; ring
  have hαre0 : α.re ≠ 0 := by rw [hαre]; linarith
  have hβre0 : β.re ≠ 0 := by rw [hβre]; linarith
  have hsumα : Summable (fun n : ℕ => 1 / (n : ℂ) ^ α) := summable_one_div_nat_cpow.mpr hA1
  have hsumβ : Summable (fun n : ℕ => 1 / (n : ℂ) ^ β) := summable_one_div_nat_cpow.mpr hB1
  set g : ℕ → ℂ := fun n => 1 / (n : ℂ) ^ α - 1 / (n : ℂ) ^ β with hgdef
  have hsumg : Summable g := hsumα.sub hsumβ
  have hD : riemannZeta α - riemannZeta β = ∑' n : ℕ, g n := by
    rw [zeta_eq_tsum_one_div_nat_cpow hA1, zeta_eq_tsum_one_div_nat_cpow hB1,
      hgdef, hsumα.tsum_sub hsumβ]
  -- the normalising constant
  set c : ℝ := ((2 : ℝ) ^ ((m : ℝ) * s.re))⁻¹ with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    exact inv_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)
  -- tail upper bound, termwise
  have htermwise : ∀ k : ℕ, ‖g (k + 3)‖ ≤ c * (512 / 5) * ((((k : ℝ) + 3)) ^ (6 : ℕ))⁻¹ := by
    intro k
    set n : ℕ := k + 3 with hndef
    have hn3 : (3 : ℝ) ≤ (n : ℝ) := by
      rw [hndef]; push_cast; have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have e1 : ‖1 / (n : ℂ) ^ α‖ = (((n : ℝ)) ^ ((m : ℝ) * s.re))⁻¹ := by
      rw [norm_one_div_natCast_cpow hαre0, hαre]
    have e2 : ‖1 / (n : ℂ) ^ β‖
        = (((n : ℝ)) ^ ((m : ℝ) * s.re))⁻¹ * (((n : ℝ)) ^ s.re)⁻¹ := by
      rw [norm_one_div_natCast_cpow hβre0, hβre, Real.rpow_add hnpos, mul_inv]
    have hApos : (0 : ℝ) < ((n : ℝ)) ^ ((m : ℝ) * s.re) := Real.rpow_pos_of_pos hnpos _
    have hsmall : (((n : ℝ)) ^ s.re)⁻¹ < 3 / 5 := inv_rpow_lt_three_fifths hs hn3
    have hsum2 : ‖g n‖ ≤ (((n : ℝ)) ^ ((m : ℝ) * s.re))⁻¹ * (8 / 5) := by
      have htri : ‖g n‖ ≤ ‖1 / (n : ℂ) ^ α‖ + ‖1 / (n : ℂ) ^ β‖ := by
        rw [hgdef]; exact norm_sub_le _ _
      rw [e1, e2] at htri
      have hApos' : (0 : ℝ) < (((n : ℝ)) ^ ((m : ℝ) * s.re))⁻¹ := inv_pos.mpr hApos
      nlinarith
    -- comparison of the `n`-th and `2`-nd powers
    have hkey : (((n : ℝ)) ^ ((m : ℝ) * s.re))⁻¹ ≤ c * 64 * ((((n : ℝ))) ^ (6 : ℕ))⁻¹ := by
      have h64 : (2 : ℝ) ^ ((m : ℝ) * s.re) = 64 * (2 : ℝ) ^ ((m : ℝ) * s.re - 6) := by
        have h := Real.rpow_add (x := (2 : ℝ)) (by norm_num) ((m : ℝ) * s.re - 6) 6
        rw [sub_add_cancel] at h
        rw [h, rpow_six_eq 2]
        norm_num
        ring
      have hsplitn : ((n : ℝ)) ^ ((m : ℝ) * s.re)
          = ((n : ℝ)) ^ ((m : ℝ) * s.re - 6) * ((n : ℝ)) ^ (6 : ℕ) := by
        have h := Real.rpow_add (x := (n : ℝ)) hnpos ((m : ℝ) * s.re - 6) 6
        rw [sub_add_cancel] at h
        rw [h, rpow_six_eq _]
      have hcmp : (2 : ℝ) ^ ((m : ℝ) * s.re - 6) ≤ ((n : ℝ)) ^ ((m : ℝ) * s.re - 6) :=
        Real.rpow_le_rpow (by norm_num) (by linarith) (by linarith)
      have hnp6 : (0 : ℝ) < ((n : ℝ)) ^ (6 : ℕ) := by positivity
      have h2p : (0 : ℝ) < (2 : ℝ) ^ ((m : ℝ) * s.re - 6) :=
        Real.rpow_pos_of_pos (by norm_num) _
      rw [hcdef, h64]
      rw [show (64 * (2 : ℝ) ^ ((m : ℝ) * s.re - 6))⁻¹ * 64 * ((((n : ℝ))) ^ (6 : ℕ))⁻¹
          = (((2 : ℝ) ^ ((m : ℝ) * s.re - 6)) * ((n : ℝ)) ^ (6 : ℕ))⁻¹ by
        field_simp]
      refine inv_anti₀ (mul_pos h2p hnp6) ?_
      rw [hsplitn]
      exact mul_le_mul_of_nonneg_right hcmp (le_of_lt hnp6)
    have hfinal : ‖g n‖ ≤ c * 64 * ((((n : ℝ))) ^ (6 : ℕ))⁻¹ * (8 / 5) := by
      refine hsum2.trans ?_
      exact mul_le_mul_of_nonneg_right hkey (by norm_num)
    have hcast : ((n : ℝ)) = (k : ℝ) + 3 := by rw [hndef]; push_cast; ring
    rw [hcast] at hfinal
    calc ‖g (k + 3)‖ = ‖g n‖ := by rw [hndef]
      _ ≤ c * 64 * ((((k : ℝ) + 3)) ^ (6 : ℕ))⁻¹ * (8 / 5) := hfinal
      _ = c * (512 / 5) * ((((k : ℝ) + 3)) ^ (6 : ℕ))⁻¹ := by ring
  -- tail upper bound, summed
  have hS3 : Summable (fun k : ℕ => ((((k : ℝ) + 3)) ^ (6 : ℕ))⁻¹) := by
    simpa using summable_shift_six 3
  have hmajSummable : Summable
      (fun k : ℕ => c * (512 / 5) * ((((k : ℝ) + 3)) ^ (6 : ℕ))⁻¹) := hS3.mul_left _
  have hnormSummable : Summable (fun k : ℕ => ‖g (k + 3)‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) htermwise hmajSummable
  have htail : ‖∑' k : ℕ, g (k + 3)‖ ≤ c * (512 / 5) * (1 / 729 + 1 / 4096 + 1 / 2500) := by
    calc ‖∑' k : ℕ, g (k + 3)‖ ≤ ∑' k : ℕ, ‖g (k + 3)‖ := norm_tsum_le_tsum_norm hnormSummable
      _ ≤ ∑' k : ℕ, c * (512 / 5) * ((((k : ℝ) + 3)) ^ (6 : ℕ))⁻¹ :=
          Summable.tsum_le_tsum htermwise hnormSummable hmajSummable
      _ = c * (512 / 5) * ∑' k : ℕ, ((((k : ℝ) + 3)) ^ (6 : ℕ))⁻¹ := tsum_mul_left
      _ ≤ c * (512 / 5) * (1 / 729 + 1 / 4096 + 1 / 2500) := by
          exact mul_le_mul_of_nonneg_left tsum_shift_inv_pow_six_three (by positivity)
  -- split the series at the head
  have hg0 : g 0 = 0 := by
    have hα0 : α ≠ 0 := fun h => hαre0 (by rw [h]; simp)
    have hβ0 : β ≠ 0 := fun h => hβre0 (by rw [h]; simp)
    simp [hgdef, Complex.zero_cpow hα0, Complex.zero_cpow hβ0]
  have hg1 : g 1 = 0 := by simp [hgdef]
  have hsplit : ∑' n : ℕ, g n = g 2 + ∑' k : ℕ, g (k + 3) := by
    have h := hsumg.sum_add_tsum_nat_add 3
    rw [← h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hg0, hg1]
    ring
  have hhead2 : g 2 = shellHead m s := by
    simp [hgdef, shellHead, hαdef, hβdef]
  rw [hD, hsplit, hhead2, add_sub_cancel_left]
  exact htail

/-- **High-exponent shell zero-free law.**  For every integer `m ≥ 12` the difference
`ζ(ms) - ζ((m+1)s)` has no zero in the strict right half-plane `re s > 1/2`: the prime-two
head strictly dominates the whole remaining tail. -/
theorem riemannZeta_natCast_mul_sub_succ_mul_ne_zero
    {m : ℕ} (hm : 12 ≤ m) {s : ℂ} (hs : 1 / 2 < s.re) :
    riemannZeta ((m : ℂ) * s) - riemannZeta (((m : ℂ) + 1) * s) ≠ 0 := by
  intro hzero
  have htail := norm_riemannZeta_diff_sub_shellHead_le hm hs
  have hhead := le_norm_shellHead m hs
  rw [hzero, zero_sub, norm_neg] at htail
  have hcpos : (0 : ℝ) < ((2 : ℝ) ^ ((m : ℝ) * s.re))⁻¹ :=
    inv_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)
  nlinarith

/-! ## Consequences: the shell multiplier and the strict right-half divisor -/

/-- **The shell multiplier is zero-free on `re s > 1/2`** for every `m ≥ 12`. -/
theorem shellMultiplier_ne_zero {m : ℕ} (hm : 12 ≤ m) {s : ℂ} (hs : 1 / 2 < s.re) :
    shellMultiplier m s ≠ 0 := by
  have hm12 : (12 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hσ0 : (0 : ℝ) < s.re := by linarith
  have hAre : ((m : ℂ) * s).re = (m : ℝ) * s.re := by simp [Complex.mul_re]
  have hBre : (((m : ℂ) + 1) * s).re = ((m : ℝ) + 1) * s.re := by simp [Complex.mul_re]
  have hA1 : 1 < ((m : ℂ) * s).re := by rw [hAre]; nlinarith
  have hB1 : 1 < (((m : ℂ) + 1) * s).re := by rw [hBre]; nlinarith
  have hdiff := riemannZeta_natCast_mul_sub_succ_mul_ne_zero hm hs
  intro hzero
  apply hdiff
  rw [shellMultiplier, sub_eq_zero, inv_inj] at hzero
  rw [hzero, sub_self]

/-- The shell multiplier is analytic on the strict right half-plane, for `m ≥ 12`. -/
theorem analyticAt_shellMultiplier {m : ℕ} (hm : 12 ≤ m) {s : ℂ} (hs : 1 / 2 < s.re) :
    AnalyticAt ℂ (shellMultiplier m) s := by
  have hm12 : (12 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hσ0 : (0 : ℝ) < s.re := by linarith
  have hAre : ((m : ℂ) * s).re = (m : ℝ) * s.re := by simp [Complex.mul_re]
  have hBre : (((m : ℂ) + 1) * s).re = ((m : ℝ) + 1) * s.re := by simp [Complex.mul_re]
  have hA1 : 1 < ((m : ℂ) * s).re := by rw [hAre]; nlinarith
  have hB1 : 1 < (((m : ℂ) + 1) * s).re := by rw [hBre]; nlinarith
  have hAne1 : ((m : ℂ) * s) ≠ 1 := by
    intro h
    rw [h] at hA1
    norm_num at hA1
  have hBne1 : (((m : ℂ) + 1) * s) ≠ 1 := by
    intro h
    rw [h] at hB1
    norm_num at hB1
  have hlinA : AnalyticAt ℂ (fun z : ℂ => (m : ℂ) * z) s := analyticAt_const.mul analyticAt_id
  have hlinB : AnalyticAt ℂ (fun z : ℂ => ((m : ℂ) + 1) * z) s :=
    analyticAt_const.mul analyticAt_id
  have hcompA : AnalyticAt ℂ (fun z : ℂ => riemannZeta ((m : ℂ) * z)) s :=
    (analyticOn_riemannZeta _ hAne1).comp hlinA
  have hcompB : AnalyticAt ℂ (fun z : ℂ => riemannZeta (((m : ℂ) + 1) * z)) s :=
    (analyticOn_riemannZeta _ hBne1).comp hlinB
  exact (hcompB.inv (riemannZeta_ne_zero_of_one_lt_re hB1)).sub
    (hcompA.inv (riemannZeta_ne_zero_of_one_lt_re hA1))

/-- **Divisor invariance under the shell multiplier.**  For `m ≥ 12` multiplication by `H_m`
changes no vanishing order at any point of the strict right half-plane. -/
theorem analyticOrderAt_mul_shellMultiplier
    {m : ℕ} (hm : 12 ≤ m) {s : ℂ} (hs : 1 / 2 < s.re) {f : ℂ → ℂ} (hf : AnalyticAt ℂ f s) :
    analyticOrderAt (fun z => f z * shellMultiplier m z) s = analyticOrderAt f s := by
  have hH : AnalyticAt ℂ (shellMultiplier m) s := analyticAt_shellMultiplier hm hs
  have hmul : analyticOrderAt (f * shellMultiplier m) s
      = analyticOrderAt f s + analyticOrderAt (shellMultiplier m) s :=
    analyticOrderAt_mul hf hH
  have hzero : analyticOrderAt (shellMultiplier m) s = 0 :=
    hH.analyticOrderAt_eq_zero.mpr (shellMultiplier_ne_zero hm hs)
  rw [show (fun z => f z * shellMultiplier m z) = f * shellMultiplier m from rfl, hmul, hzero,
    add_zero]

/-- **The shell current carries exactly the zeta divisor.**  For `m ≥ 12` and every point of
the strict right half-plane, the shell current `ζ · H_m` vanishes to exactly the same order
as `ζ`. -/
theorem analyticOrderAt_riemannZeta_mul_shellMultiplier
    {m : ℕ} (hm : 12 ≤ m) {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    analyticOrderAt (fun z => riemannZeta z * shellMultiplier m z) s
      = analyticOrderAt riemannZeta s :=
  analyticOrderAt_mul_shellMultiplier hm hs (analyticOn_riemannZeta _ hs1)

/-- Completed form: the completed shell current `Λ · H_m` has, at every point of the strict
right half-plane other than the pole, exactly the vanishing order of the completed zeta
function.  Together with `analyticOrderAt_riemannZeta_mul_shellMultiplier` this says that
`X_m` and `Ξ` have the same strict right-half divisor, with the same multiplicities. -/
theorem analyticOrderAt_completedRiemannZeta_mul_shellMultiplier
    {m : ℕ} (hm : 12 ≤ m) {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    analyticOrderAt (fun z => completedRiemannZeta z * shellMultiplier m z) s
      = analyticOrderAt completedRiemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hopen : IsOpen {z : ℂ | z ≠ 0 ∧ z ≠ 1} := by
    have h : {z : ℂ | z ≠ 0 ∧ z ≠ 1} = ({0}ᶜ : Set ℂ) ∩ ({1}ᶜ : Set ℂ) := by
      ext z; simp
    rw [h]
    exact isOpen_compl_singleton.inter isOpen_compl_singleton
  have hΛ : AnalyticAt ℂ completedRiemannZeta s :=
    DifferentiableOn.analyticAt
      (fun _ hz => (differentiableAt_completedZeta hz.1 hz.2).differentiableWithinAt)
      (hopen.mem_nhds ⟨hs0, hs1⟩)
  exact analyticOrderAt_mul_shellMultiplier hm hs hΛ

/-- Set-level form of the divisor identity: the shell current and `ζ` have the same zero set
on `re s > 1/2`. -/
theorem riemannZeta_mul_shellMultiplier_eq_zero_iff
    {m : ℕ} (hm : 12 ≤ m) {s : ℂ} (hs : 1 / 2 < s.re) :
    riemannZeta s * shellMultiplier m s = 0 ↔ riemannZeta s = 0 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · exact absurd h' (shellMultiplier_ne_zero hm hs)
  · intro h; rw [h, zero_mul]

/-- **Additive splitting of the shell logarithmic current.**  Wherever `ζ` itself does not
vanish, the logarithmic derivative of the shell current is the zeta logarithmic derivative plus
the shell correction; the correction is the logarithmic derivative of a function holomorphic and
zero-free on the whole strict right half-plane. -/
theorem logDeriv_riemannZeta_mul_shellMultiplier
    {m : ℕ} (hm : 12 ≤ m) {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) :
    logDeriv (fun z => riemannZeta z * shellMultiplier m z) s
      = logDeriv riemannZeta s + logDeriv (shellMultiplier m) s :=
  logDeriv_mul s hζ (shellMultiplier_ne_zero hm hs) (differentiableAt_riemannZeta hs1)
    (analyticAt_shellMultiplier hm hs).differentiableAt

/-! ## Positivity of the shell multiplier at the critical clock point -/

private theorem summable_inv_nat_pow {k : ℕ} (hk : 1 < k) :
    Summable (fun n : ℕ => (((n : ℝ)) ^ k)⁻¹) := by
  have h : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ k) :=
    (Real.summable_one_div_nat_pow (p := k)).mpr hk
  simpa [one_div] using h

private theorem riemannZeta_natCast_eq_ofReal_tsum {k : ℕ} (hk : 1 < k) :
    riemannZeta (k : ℂ) = ((∑' n : ℕ, (((n : ℝ)) ^ k)⁻¹ : ℝ) : ℂ) := by
  rw [zeta_nat_eq_tsum_of_gt_one hk, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  push_cast
  rw [one_div]

private theorem tsum_inv_nat_pow_pos {k : ℕ} (hk : 1 < k) :
    0 < ∑' n : ℕ, (((n : ℝ)) ^ k)⁻¹ := by
  refine Summable.tsum_pos (summable_inv_nat_pow hk) (fun n => by positivity) 1 ?_
  norm_num

private theorem tsum_inv_nat_pow_succ_lt {k : ℕ} (hk : 1 < k) :
    ∑' n : ℕ, (((n : ℝ)) ^ (k + 1))⁻¹ < ∑' n : ℕ, (((n : ℝ)) ^ k)⁻¹ := by
  refine Summable.tsum_lt_tsum (i := 2) (fun n => ?_) ?_
    (summable_inv_nat_pow (by omega)) (summable_inv_nat_pow hk)
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hk0 : k ≠ 0 := by omega
      simp [hk0]
    · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hpos : (0 : ℝ) < ((n : ℝ)) ^ k := by positivity
      have hmono : ((n : ℝ)) ^ k ≤ ((n : ℝ)) ^ (k + 1) := by
        rw [pow_succ]
        nlinarith
      exact inv_anti₀ hpos hmono
  · have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [h2]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hlt : (2 : ℝ) ^ k < (2 : ℝ) ^ (k + 1) := by
      rw [pow_succ]
      nlinarith
    exact (inv_lt_inv₀ (by positivity) hpos).mpr hlt

/-- **Positive shell residue.**  For every `m ≥ 2` the shell multiplier at the critical clock
point `s = 1` is a positive real number.  Hence `S_m = ζ · H_m` has a simple pole at `s = 1`
with positive residue `H_m(1) = ζ(m+1)⁻¹ - ζ(m)⁻¹ > 0`. -/
theorem shellMultiplier_one_eq_ofReal_pos {m : ℕ} (hm : 2 ≤ m) :
    ∃ r : ℝ, 0 < r ∧ shellMultiplier m 1 = (r : ℂ) := by
  have hm1 : 1 < m := hm
  have hZm : 0 < ∑' n : ℕ, (((n : ℝ)) ^ m)⁻¹ := tsum_inv_nat_pow_pos hm1
  have hZm1 : 0 < ∑' n : ℕ, (((n : ℝ)) ^ (m + 1))⁻¹ := tsum_inv_nat_pow_pos (by omega)
  have hlt : ∑' n : ℕ, (((n : ℝ)) ^ (m + 1))⁻¹ < ∑' n : ℕ, (((n : ℝ)) ^ m)⁻¹ :=
    tsum_inv_nat_pow_succ_lt hm1
  refine ⟨(∑' n : ℕ, (((n : ℝ)) ^ (m + 1))⁻¹)⁻¹ - (∑' n : ℕ, (((n : ℝ)) ^ m)⁻¹)⁻¹, ?_, ?_⟩
  · have : (∑' n : ℕ, (((n : ℝ)) ^ m)⁻¹)⁻¹ < (∑' n : ℕ, (((n : ℝ)) ^ (m + 1))⁻¹)⁻¹ :=
      (inv_lt_inv₀ hZm hZm1).mpr hlt
    linarith
  · have hA : ((m : ℂ)) * 1 = ((m : ℕ) : ℂ) := by ring
    have hB : (((m : ℂ)) + 1) * 1 = (((m + 1 : ℕ)) : ℂ) := by push_cast; ring
    rw [shellMultiplier, hA, hB, riemannZeta_natCast_eq_ofReal_tsum hm1,
      riemannZeta_natCast_eq_ofReal_tsum (show 1 < m + 1 by omega)]
    push_cast
    ring

end RHTower
