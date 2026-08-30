import GaloisForLFunctions.HTGeometry.CombinationModeDiophantineDivisor

/-!
# A Liouville frequency destroys square-summability of the mode-divided datum

The series `α = ∑ₖ 2^{-a_k}` with `a₀ = 2` and `a_{k+1} = a_k + 1 + 16^{a_k}` is irrational, and its
rational approximations `p_K / q_K` with `q_K = 2^{a_K}` satisfy

`0 < q_K α − p_K ≤ 2^{−16^{a_K}} ≤ exp(−(p_K + q_K)²)`,

because the gap `16^{a_K}` outgrows the square of the approximation size.  Hence the frequency
vector `(1, α)` has a nonvanishing linear form on every nonzero mode, yet the form is smaller than
`exp(−|m|²)` on modes of arbitrarily large size.  For every exponential decay rate the divided
series then has unbounded terms and is not summable: the cohomological equation has no `L²`
solution.

This is the converse half of the mode-division dichotomy whose positive half is
`summable_modeDivisor_of_diophantine`.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

def gapExp : ℕ → ℕ
  | 0 => 2
  | k + 1 => gapExp k + 1 + 16 ^ gapExp k

@[simp] theorem gapExp_zero : gapExp 0 = 2 := rfl
@[simp] theorem gapExp_succ (k : ℕ) : gapExp (k + 1) = gapExp k + 1 + 16 ^ gapExp k := rfl

theorem gapExp_lt_succ (k : ℕ) : gapExp k < gapExp (k + 1) := by
  have h : 0 < 16 ^ gapExp k := by positivity
  rw [gapExp_succ]
  omega

theorem two_le_gapExp (k : ℕ) : 2 ≤ gapExp k := by
  induction k with
  | zero => simp
  | succ k ih => have := gapExp_lt_succ k; omega

theorem add_two_le_gapExp (k : ℕ) : k + 2 ≤ gapExp k := by
  induction k with
  | zero => simp
  | succ k ih => have := gapExp_lt_succ k; omega

theorem gapExp_add_le (K j : ℕ) : gapExp K + j ≤ gapExp (K + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have h := gapExp_lt_succ (K + j)
      have he : K + (j + 1) = (K + j) + 1 := by omega
      rw [he]
      omega

theorem gapExp_mono {j k : ℕ} (h : j ≤ k) : gapExp j ≤ gapExp k :=
  (strictMono_nat_of_lt_succ gapExp_lt_succ).monotone h

/-- The terms of the super-Liouville series. -/
noncomputable def gapTerm (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ gapExp k

theorem gapTerm_pos (k : ℕ) : 0 < gapTerm k := by
  rw [gapTerm]; positivity

theorem gapTerm_le_geom (k : ℕ) : gapTerm k ≤ (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ k := by
  have h : gapTerm k ≤ (1 / 2 : ℝ) ^ (k + 2) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (add_two_le_gapExp k)
  have he : (1 / 2 : ℝ) ^ (k + 2) = (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ k := by
    rw [pow_add]; norm_num; ring
  rwa [he] at h

theorem summable_geom_half : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
  summable_geometric_of_lt_one (by norm_num) (by norm_num)

theorem tsum_geom_half : ∑' k : ℕ, (1 / 2 : ℝ) ^ k = 2 := by
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

theorem summable_quarter_geom : Summable (fun k : ℕ => (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ k) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) summable_geom_half
  nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) k]

theorem gapTerm_summable : Summable gapTerm :=
  Summable.of_nonneg_of_le (fun k => (gapTerm_pos k).le) gapTerm_le_geom summable_quarter_geom

/-- The super-Liouville number `α = ∑ₖ 2^{-a_k}`. -/
noncomputable def superLiouville : ℝ := ∑' k, gapTerm k

theorem superLiouville_le_one : superLiouville ≤ 1 := by
  have h1 : superLiouville ≤ ∑' k : ℕ, (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ k :=
    Summable.tsum_mono gapTerm_summable summable_quarter_geom gapTerm_le_geom
  rw [Summable.tsum_mul_left _ summable_geom_half, tsum_geom_half] at h1
  linarith

theorem superLiouville_pos : 0 < superLiouville :=
  lt_of_lt_of_le (gapTerm_pos 0) (gapTerm_summable.le_tsum 0 fun j _ => (gapTerm_pos j).le)

theorem gapTerm_shift_le (K j : ℕ) :
    gapTerm (j + (K + 1)) ≤ gapTerm (K + 1) * (1 / 2 : ℝ) ^ j := by
  have h : gapExp (K + 1) + j ≤ gapExp (j + (K + 1)) := by
    have := gapExp_add_le (K + 1) j
    rwa [show (K + 1) + j = j + (K + 1) by omega] at this
  calc gapTerm (j + (K + 1)) = (1 / 2 : ℝ) ^ gapExp (j + (K + 1)) := rfl
    _ ≤ (1 / 2 : ℝ) ^ (gapExp (K + 1) + j) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) h
    _ = gapTerm (K + 1) * (1 / 2 : ℝ) ^ j := by rw [pow_add]; rfl

theorem summable_gapTerm_shift (K : ℕ) : Summable (fun j : ℕ => gapTerm (j + (K + 1))) := by
  refine Summable.of_nonneg_of_le (fun j => (gapTerm_pos _).le) (gapTerm_shift_le K) ?_
  exact summable_geom_half.mul_left (gapTerm (K + 1))

theorem tail_eq (K : ℕ) :
    superLiouville - ∑ k ∈ Finset.range (K + 1), gapTerm k
      = ∑' j : ℕ, gapTerm (j + (K + 1)) := by
  have h := gapTerm_summable.sum_add_tsum_nat_add (K + 1)
  rw [superLiouville, ← h]
  ring

theorem tail_pos (K : ℕ) : 0 < ∑' j : ℕ, gapTerm (j + (K + 1)) :=
  lt_of_lt_of_le (gapTerm_pos (0 + (K + 1)))
    ((summable_gapTerm_shift K).le_tsum 0 fun _ _ => (gapTerm_pos _).le)

theorem tail_le (K : ℕ) :
    ∑' j : ℕ, gapTerm (j + (K + 1)) ≤ 2 * gapTerm (K + 1) := by
  have h := Summable.tsum_mono (summable_gapTerm_shift K)
    (summable_geom_half.mul_left (gapTerm (K + 1))) (gapTerm_shift_le K)
  have he : ∑' j : ℕ, gapTerm (K + 1) * (1 / 2 : ℝ) ^ j = gapTerm (K + 1) * 2 := by
    rw [Summable.tsum_mul_left _ summable_geom_half, tsum_geom_half]
  rw [he] at h
  linarith

/-- The denominator of the `K`-th rational approximation. -/
private def qDen (K : ℕ) : ℕ := 2 ^ gapExp K

/-- The numerator of the `K`-th rational approximation. -/
def pNum (K : ℕ) : ℕ := ∑ k ∈ Finset.range (K + 1), 2 ^ (gapExp K - gapExp k)

theorem qDen_pos (K : ℕ) : 0 < qDen K := by rw [qDen]; positivity

theorem qDen_mul_partial (K : ℕ) :
    (qDen K : ℝ) * ∑ k ∈ Finset.range (K + 1), gapTerm k = (pNum K : ℝ) := by
  rw [qDen, pNum, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hle : gapExp k ≤ gapExp K := gapExp_mono hk'
  rw [gapTerm, pow_sub₀ (2 : ℝ) (by norm_num) hle]
  rw [div_pow, one_pow]
  field_simp

theorem qAlpha_sub_pNum_eq (K : ℕ) :
    (qDen K : ℝ) * superLiouville - (pNum K : ℝ)
      = (qDen K : ℝ) * ∑' j : ℕ, gapTerm (j + (K + 1)) := by
  rw [← tail_eq K, ← qDen_mul_partial K]
  ring

theorem approx_pos (K : ℕ) : 0 < (qDen K : ℝ) * superLiouville - (pNum K : ℝ) := by
  rw [qAlpha_sub_pNum_eq K]
  have hq : (0 : ℝ) < (qDen K : ℝ) := by exact_mod_cast qDen_pos K
  exact mul_pos hq (tail_pos K)

theorem approx_upper (K : ℕ) :
    (qDen K : ℝ) * superLiouville - (pNum K : ℝ) ≤ (1 / 2 : ℝ) ^ (16 ^ gapExp K) := by
  rw [qAlpha_sub_pNum_eq K]
  have hqnn : (0 : ℝ) ≤ (qDen K : ℝ) := by positivity
  refine (mul_le_mul_of_nonneg_left (tail_le K) hqnn).trans (le_of_eq ?_)
  rw [qDen, gapTerm, gapExp_succ]
  push_cast
  set t : ℝ := (1 / 2 : ℝ) ^ (16 ^ gapExp K) with ht
  rw [pow_add, pow_add]
  have h3 : (2 : ℝ) ^ gapExp K * (1 / 2 : ℝ) ^ gapExp K = 1 := by
    rw [← mul_pow]; norm_num
  linear_combination t * h3

theorem partial_le_superLiouville (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), gapTerm k ≤ superLiouville := by
  have h := tail_eq K
  have h2 := (tail_pos K).le
  linarith [h ▸ h2]

theorem pNum_le_qDen (K : ℕ) : pNum K ≤ qDen K := by
  have hq : (0 : ℝ) < (qDen K : ℝ) := by exact_mod_cast qDen_pos K
  have h1 : (pNum K : ℝ) ≤ (qDen K : ℝ) := by
    rw [← qDen_mul_partial K]
    calc (qDen K : ℝ) * ∑ k ∈ Finset.range (K + 1), gapTerm k
        ≤ (qDen K : ℝ) * superLiouville :=
          mul_le_mul_of_nonneg_left (partial_le_superLiouville K) hq.le
      _ ≤ (qDen K : ℝ) * 1 := mul_le_mul_of_nonneg_left superLiouville_le_one hq.le
      _ = (qDen K : ℝ) := by ring
  exact_mod_cast h1

theorem superLiouville_irrational : Irrational superLiouville := by
  rintro ⟨r, hr⟩
  set K : ℕ := r.den with hK
  have hden : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.pos
  have hval : superLiouville = (r.num : ℝ) / (r.den : ℝ) := by
    rw [← hr, Rat.cast_def]
  set N : ℤ := (qDen K : ℤ) * r.num - (pNum K : ℤ) * (r.den : ℤ) with hN
  have hNr : (N : ℝ) / (r.den : ℝ) = (qDen K : ℝ) * superLiouville - (pNum K : ℝ) := by
    rw [hN, hval]
    push_cast
    field_simp
  have hNpos : (0 : ℝ) < (N : ℝ) / (r.den : ℝ) := by rw [hNr]; exact approx_pos K
  have hNint : 1 ≤ N := by
    have : (0 : ℝ) < (N : ℝ) := by
      have := mul_pos hNpos hden
      rwa [div_mul_cancel₀ _ (ne_of_gt hden)] at this
    have : (0 : ℤ) < N := by exact_mod_cast this
    omega
  have hlow : (1 : ℝ) / (r.den : ℝ) ≤ (qDen K : ℝ) * superLiouville - (pNum K : ℝ) := by
    rw [← hNr]
    have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNint
    gcongr
  have hup := approx_upper K
  have hKle : K ≤ 16 ^ gapExp K := by
    have h1 : K < 2 ^ K := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ K ≤ 16 ^ K := Nat.pow_le_pow_left (by norm_num) K
    have h3 : (16 : ℕ) ^ K ≤ 16 ^ gapExp K :=
      Nat.pow_le_pow_right (by norm_num) (le_trans (by omega) (add_two_le_gapExp K))
    omega
  have h2 : (1 / 2 : ℝ) ^ (16 ^ gapExp K) ≤ (1 / 2 : ℝ) ^ K :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hKle
  have hlt : (1 / 2 : ℝ) ^ K < 1 / (r.den : ℝ) := by
    have hKlt : (r.den : ℝ) < (2 : ℝ) ^ K := by
      have : K < 2 ^ K := Nat.lt_two_pow_self
      have h' : (K : ℝ) < ((2 ^ K : ℕ) : ℝ) := by exact_mod_cast this
      rw [hK] at *
      push_cast at h'
      exact h'
    rw [div_pow, one_pow]
    exact one_div_lt_one_div_of_lt hden hKlt
  linarith

/-- The Liouville frequency vector `(1, α)`. -/
noncomputable def liouvilleFrequency : Fin 2 → ℝ := ![1, superLiouville]

/-- The resonant modes of the Liouville frequency. -/
def liouvilleMode (K : ℕ) : Fin 2 → ℤ := ![-(pNum K : ℤ), (qDen K : ℤ)]

theorem modeForm_liouvilleMode (K : ℕ) :
    modeForm liouvilleFrequency (liouvilleMode K)
      = (qDen K : ℝ) * superLiouville - (pNum K : ℝ) := by
  rw [modeForm, Fin.sum_univ_two, liouvilleFrequency, liouvilleMode]
  simp
  ring

theorem modeNorm_liouvilleMode (K : ℕ) : modeNorm (liouvilleMode K) = pNum K + qDen K := by
  rw [modeNorm, Fin.sum_univ_two, liouvilleMode]
  simp

theorem liouvilleMode_ne_zero (K : ℕ) : liouvilleMode K ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  rw [liouvilleMode] at h1
  simp at h1
  have := qDen_pos K
  omega

theorem exp_le_two_pow (n : ℕ) (hn : 2 ≤ n) :
    Real.exp (((4 * 4 ^ n : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (16 ^ n) := by
  set B : ℕ := 4 * 4 ^ n with hB
  have h1 : Real.exp ((B : ℝ)) = Real.exp 1 ^ B := by
    have := Real.exp_nat_mul 1 B
    rw [mul_one] at this
    exact this
  have h2 : Real.exp 1 ^ B ≤ (4 : ℝ) ^ B :=
    pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) B
  have h3 : (4 : ℝ) ^ B = (2 : ℝ) ^ (2 * B) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
  have h4 : 2 * B ≤ 16 ^ n := by
    have h16 : (16 : ℕ) ^ n = 4 ^ n * 4 ^ n := by
      rw [show (16 : ℕ) = 4 * 4 by norm_num, mul_pow]
    have h4n : (16 : ℕ) ≤ 4 ^ n := by
      calc (16 : ℕ) = 4 ^ 2 := by norm_num
        _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    rw [hB, h16]
    nlinarith
  have h5 : (2 : ℝ) ^ (2 * B) ≤ (2 : ℝ) ^ (16 ^ n) :=
    pow_le_pow_right₀ (by norm_num) h4
  rw [h1]
  calc Real.exp 1 ^ B ≤ (4 : ℝ) ^ B := h2
    _ = (2 : ℝ) ^ (2 * B) := h3
    _ ≤ (2 : ℝ) ^ (16 ^ n) := h5

theorem abs_modeForm_liouvilleMode_le (K : ℕ) :
    |modeForm liouvilleFrequency (liouvilleMode K)|
      ≤ Real.exp (-((modeNorm (liouvilleMode K) : ℝ)) ^ 2) := by
  set n : ℕ := gapExp K with hn
  have hn2 : 2 ≤ n := two_le_gapExp K
  have hpos : 0 < modeForm liouvilleFrequency (liouvilleMode K) := by
    rw [modeForm_liouvilleMode]; exact approx_pos K
  rw [abs_of_pos hpos, modeForm_liouvilleMode]
  have hup : (qDen K : ℝ) * superLiouville - (pNum K : ℝ) ≤ (1 / 2 : ℝ) ^ (16 ^ n) :=
    approx_upper K
  have hM : modeNorm (liouvilleMode K) ≤ 2 * qDen K := by
    rw [modeNorm_liouvilleMode]
    have := pNum_le_qDen K
    omega
  have hMsq : (modeNorm (liouvilleMode K)) ^ 2 ≤ 4 * 4 ^ n := by
    have hq : qDen K = 2 ^ n := rfl
    have h2 : (2 * qDen K) ^ 2 = 4 * 4 ^ n := by
      rw [hq, mul_pow, ← pow_mul]
      norm_num
      rw [show n * 2 = 2 * n by ring, pow_mul]
      norm_num
    calc (modeNorm (liouvilleMode K)) ^ 2 ≤ (2 * qDen K) ^ 2 := Nat.pow_le_pow_left hM 2
      _ = 4 * 4 ^ n := h2
  have hexp1 : Real.exp (-(((4 * 4 ^ n : ℕ)) : ℝ))
      ≤ Real.exp (-((modeNorm (liouvilleMode K) : ℝ)) ^ 2) := by
    refine Real.exp_le_exp.mpr ?_
    have hcast : ((modeNorm (liouvilleMode K) : ℝ)) ^ 2 ≤ (((4 * 4 ^ n : ℕ)) : ℝ) := by
      exact_mod_cast hMsq
    linarith
  have hexp2 : (1 / 2 : ℝ) ^ (16 ^ n) ≤ Real.exp (-(((4 * 4 ^ n : ℕ)) : ℝ)) := by
    rw [Real.exp_neg, div_pow, one_pow]
    have hE : (0 : ℝ) < Real.exp (((4 * 4 ^ n : ℕ)) : ℝ) := Real.exp_pos _
    have h2p : (0 : ℝ) < (2 : ℝ) ^ (16 ^ n) := by positivity
    rw [← one_div]
    exact one_div_le_one_div_of_le hE (exp_le_two_pow n hn2)
  linarith

theorem modeForm_liouvilleFrequency_ne_zero (m : Fin 2 → ℤ) (hm : m ≠ 0) :
    modeForm liouvilleFrequency m ≠ 0 := by
  intro h
  rw [modeForm, Fin.sum_univ_two, liouvilleFrequency] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one] at h
  by_cases h1 : m 1 = 0
  · rw [h1] at h
    simp only [Int.cast_zero, zero_mul, add_zero, Int.cast_eq_zero] at h
    exact hm (funext fun i => by fin_cases i <;> simpa using by first | exact h | exact h1)
  · refine superLiouville_irrational ⟨(-(m 0) : ℚ) / ((m 1 : ℤ) : ℚ), ?_⟩
    have hm1 : ((m 1 : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h1
    push_cast
    field_simp
    linarith

theorem le_modeNorm_liouvilleMode (K : ℕ) : K ≤ modeNorm (liouvilleMode K) := by
  have h1 : K < 2 ^ K := Nat.lt_two_pow_self
  have h2 : (2 : ℕ) ^ K ≤ 2 ^ gapExp K :=
    Nat.pow_le_pow_right (by norm_num) (le_trans (by omega) (add_two_le_gapExp K))
  have h3 : qDen K = 2 ^ gapExp K := rfl
  rw [modeNorm_liouvilleMode]
  omega

/-- **Lemma R, converse half.**  There is a frequency vector on two coordinates whose linear form
never vanishes on a nonzero mode, yet is smaller than `exp(−|m|²)` along modes of arbitrarily large
size.  No fixed-exponent Diophantine condition can hold for it. -/
theorem exists_liouville_frequency :
    ∃ ω : Fin 2 → ℝ, (∀ m : Fin 2 → ℤ, m ≠ 0 → modeForm ω m ≠ 0) ∧
      ∀ N : ℕ, ∃ m : Fin 2 → ℤ, m ≠ 0 ∧ N ≤ modeNorm m ∧
        |modeForm ω m| ≤ Real.exp (-((modeNorm m : ℝ)) ^ 2) :=
  ⟨liouvilleFrequency, modeForm_liouvilleFrequency_ne_zero, fun N =>
    ⟨liouvilleMode N, liouvilleMode_ne_zero N, le_modeNorm_liouvilleMode N,
      abs_modeForm_liouvilleMode_le N⟩⟩

/-- **The mode-divided datum is not square-summable for the Liouville frequency.**  For every decay
rate the divided series has unbounded terms, so the cohomological equation has no `L²` solution. -/
theorem not_summable_liouvilleDivisor {ρ : ℝ} (hρ : 0 < ρ) :
    ¬ Summable (fun m : {m : Fin 2 → ℤ // m ≠ 0} =>
        Real.exp (-(2 * ρ) * (modeNorm (m : Fin 2 → ℤ) : ℝ))
          / (modeForm liouvilleFrequency (m : Fin 2 → ℤ)) ^ 2) := by
  intro hsum
  set F : {m : Fin 2 → ℤ // m ≠ 0} → ℝ := fun m =>
    Real.exp (-(2 * ρ) * (modeNorm (m : Fin 2 → ℤ) : ℝ))
      / (modeForm liouvilleFrequency (m : Fin 2 → ℤ)) ^ 2 with hF
  have hFnn : ∀ m, 0 ≤ F m := fun m => by rw [hF]; positivity
  set S : ℝ := ∑' m, F m with hS
  set K : ℕ := ⌈ρ + 1⌉₊ + ⌈S⌉₊ + 1 with hK
  set m₀ : {m : Fin 2 → ℤ // m ≠ 0} := ⟨liouvilleMode K, liouvilleMode_ne_zero K⟩ with hm₀
  set M : ℝ := (modeNorm (liouvilleMode K) : ℝ) with hM
  have hKM : (K : ℝ) ≤ M := by rw [hM]; exact_mod_cast le_modeNorm_liouvilleMode K
  have hρM : ρ + 1 ≤ M := le_trans (le_trans (Nat.le_ceil _) (by exact_mod_cast (by omega : ⌈ρ + 1⌉₊ ≤ K))) hKM
  have hSM : S < M := lt_of_lt_of_le (lt_of_le_of_lt (Nat.le_ceil S) (by exact_mod_cast (by omega : ⌈S⌉₊ < K))) hKM
  have hMpos : 0 < M := by linarith
  have habs := abs_modeForm_liouvilleMode_le K
  have hposf : 0 < modeForm liouvilleFrequency (liouvilleMode K) := by
    rw [modeForm_liouvilleMode]; exact approx_pos K
  have hle : modeForm liouvilleFrequency (liouvilleMode K) ≤ Real.exp (-(M ^ 2)) := by
    rw [← abs_of_pos hposf]; exact habs
  have hsq : (modeForm liouvilleFrequency (liouvilleMode K)) ^ 2 ≤ (Real.exp (-(M ^ 2))) ^ 2 :=
    pow_le_pow_left₀ hposf.le hle 2
  have hden : (0 : ℝ) < (modeForm liouvilleFrequency (liouvilleMode K)) ^ 2 := by positivity
  have hlow : Real.exp (2 * M ^ 2 - 2 * ρ * M) ≤ F m₀ := by
    rw [hF]
    have hnum : Real.exp (-(2 * ρ) * M) > 0 := Real.exp_pos _
    have hstep : Real.exp (-(2 * ρ) * M) / (Real.exp (-(M ^ 2))) ^ 2
        ≤ Real.exp (-(2 * ρ) * M) / (modeForm liouvilleFrequency (liouvilleMode K)) ^ 2 := by
      gcongr
    refine le_trans (le_of_eq ?_) hstep
    rw [← Real.exp_nat_mul, ← Real.exp_sub]
    ring_nf
  have hbound : F m₀ ≤ S := hsum.le_tsum m₀ fun j _ => hFnn j
  have hbig : M ≤ 2 * M ^ 2 - 2 * ρ * M := by nlinarith
  have hexpM : M + 1 ≤ Real.exp M := Real.add_one_le_exp M
  have : Real.exp M ≤ Real.exp (2 * M ^ 2 - 2 * ρ * M) := Real.exp_le_exp.mpr hbig
  linarith

end GaloisForLFunctions.HTGeometry





