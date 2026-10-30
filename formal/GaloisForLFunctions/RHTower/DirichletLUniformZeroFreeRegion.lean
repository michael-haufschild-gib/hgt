import GaloisForLFunctions.RHTower.DirichletLUniformPartialFraction
import GaloisForLFunctions.RHTower.DirichletLThreeFourOne
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegUniform
import GaloisForLFunctions.RHTower.VisibleCoprimeDirichletZeroJet

/-!
# A zero-free region for Dirichlet `L`-functions, uniform in the modulus

**Theorem** (`uniform_zero_free_region`). There is an absolute `c > 0` such that for every modulus
`q`, every nonprincipal character `χ` modulo `q` and every zero `β + iγ` of `L(s, χ)`,
`β ≤ 1 − c / log²(q(|γ| + 3))`, unless `χ` is real and the zero is real.

The proof is the classical one, with conductor-uniform inputs. Put `L = log(q(|γ| + 3)) ≥ 1`.

* *Complex characters.* At `σ = 1 + ε/L` the `3-4-1` inequality (`three_four_one_logDeriv`) with the
  pole bound `Re(−L₀'/L₀)(σ) ≤ 1/(σ − 1)` and the partial fraction (`neg_re_logDeriv_LFunction_le`) at
  heights `γ` (keeping the zero) and `2γ` (keeping nothing) gives `1 − β ≥ 1/(84 A L)`.
* *Real characters, `|γ| ≥ ε/L²`.* Now `χ² = 1` and `L(s, χ²)` is the principal `L`-function, with a pole:
  `Re(−L₀'/L₀)(σ + 2iγ) ≤ Re 1/(σ − 1 + 2iγ) + O(L²)` (`neg_re_logDeriv_zeta_le_pole`), and the pole term
  is at most `(σ − 1)/(4γ²)`.
* *Real characters, `0 < |γ| < ε/L²`.* The conjugate `β − iγ` is a zero as well
  (`RHTower.LFunction_inv_conj`), and `Re(1 + χ(n)) ≥ 0` (`two_term_logDeriv`) at real `σ` with both zeros
  kept excludes the pair.

The real zeros of real characters are Siegel's (`RHTower.siegel_zero_free`).
-/

noncomputable section

open Complex Metric

namespace RHTower

/-- `1 < log 3`. -/
theorem one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  exact Real.exp_one_lt_d9.trans (by norm_num)

/-- **`ζ` near `Re s = 1`, with its pole.** -/
theorem exists_neg_re_logDeriv_zeta_le_pole : ∃ D : ℝ, 0 < D ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 9/8 →
    (-deriv riemannZeta s / riemannZeta s).re ≤ ((s - 1)⁻¹).re + D * Real.log (|s.im| + 3) ^ 2 := by
  obtain ⟨C, L₀, hC, hL₀, hbound⟩ := Sieve.exists_bound_zetaLogDerivReg_uniform
  refine ⟨2 * C * (L₀ ^ 2 + 1), by positivity, fun s hs1 hs2 => ?_⟩
  have hs1' : s ≠ 1 := by intro h; rw [h, one_re] at hs1; exact lt_irrefl _ hs1
  have hG : zetaResidueUnit s ≠ 0 := by
    rw [zetaResidueUnit, Function.update_of_ne hs1']
    exact mul_ne_zero (sub_ne_zero.mpr hs1') (riemannZeta_ne_zero_of_one_lt_re hs1)
  have heq := Sieve.neg_logDeriv_riemannZeta_eq hs1' hG
  set K : ℝ := |s.im| + Real.exp L₀ with hKdef
  have hexpL : 1 ≤ Real.exp L₀ := Real.one_le_exp (by linarith)
  have hK : L₀ ≤ Real.log K := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    linarith [abs_nonneg s.im]
  have hKim : |s.im| ≤ K := by linarith
  have hlogK0 : 0 < Real.log K := by linarith
  have hlow : 1 - 1 / 40000 / Real.log K ≤ s.re := by
    have : 0 < 1 / 40000 / Real.log K := by positivity
    linarith
  have hreg := hbound s K hK hKim hlow hs2
  have hlogK : Real.log K ≤ L₀ + Real.log (|s.im| + 3) := by
    have hKle : K ≤ Real.exp L₀ * (|s.im| + 3) := by nlinarith [abs_nonneg s.im]
    calc Real.log K ≤ Real.log (Real.exp L₀ * (|s.im| + 3)) :=
          Real.log_le_log (by positivity) hKle
      _ = L₀ + Real.log (|s.im| + 3) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
  have hl1 : 1 ≤ Real.log (|s.im| + 3) :=
    one_lt_log_three.le.trans (Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im]))
  have hsplit : -deriv riemannZeta s / riemannZeta s = (s - 1)⁻¹ + Sieve.zetaLogDerivReg s := by
    rw [← heq, logDeriv_apply, neg_div]
  rw [hsplit, add_re]
  have hre : (Sieve.zetaLogDerivReg s).re ≤ C * Real.log K ^ 2 := (re_le_norm _).trans hreg
  have hsq : Real.log K ^ 2 ≤ (L₀ ^ 2 + 1) * 2 * Real.log (|s.im| + 3) ^ 2 := by
    have h1 : Real.log K ^ 2 ≤ (L₀ + Real.log (|s.im| + 3)) ^ 2 :=
      pow_le_pow_left₀ hlogK0.le hlogK 2
    have hl2 : 1 ≤ Real.log (|s.im| + 3) ^ 2 := by nlinarith
    have h2 : (L₀ + Real.log (|s.im| + 3)) ^ 2 ≤ 2 * L₀ ^ 2 + 2 * Real.log (|s.im| + 3) ^ 2 := by
      nlinarith [sq_nonneg (L₀ - Real.log (|s.im| + 3))]
    have h3 : L₀ ^ 2 ≤ L₀ ^ 2 * Real.log (|s.im| + 3) ^ 2 := le_mul_of_one_le_right (sq_nonneg _) hl2
    linarith
  nlinarith

variable {q : ℕ} [NeZero q]

/-- `Re(1 + χ(n)) ≥ 0`: the two-term inequality at real points. -/
theorem two_term_logDeriv (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ (-logDeriv (1 : DirichletCharacter ℂ q).LFunction σ).re + (-logDeriv χ.LFunction σ).re := by
  have hs : 1 < ((σ : ℂ)).re := by simpa using hσ
  rw [neg_logDeriv_LFunction_eq_LSeries _ hs, neg_logDeriv_LFunction_eq_LSeries _ hs]
  have h0 := hasSum_re (DirichletCharacter.LSeriesSummable_twist_vonMangoldt
    (1 : DirichletCharacter ℂ q) hs).LSeriesHasSum
  have h1 := hasSum_re (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs).LSeriesHasSum
  refine (h0.add h1).nonneg fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  show 0 ≤ (LSeries.term (fun n => (1 : DirichletCharacter ℂ q) n *
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) σ n).re +
    (LSeries.term (fun n => χ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) σ n).re
  rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne']
  have hnσ : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    rfl
  set a : ℝ := ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ with hadef
  have ha : 0 ≤ a :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hform : ∀ c : ℂ, c * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) ^ (σ : ℂ) =
      (a : ℂ) * c := by
    intro c
    have hpos : (0 : ℝ) < (n : ℝ) ^ σ := Real.rpow_pos_of_pos (by exact_mod_cast hn) σ
    rw [hnσ, hadef, Complex.ofReal_div]
    field_simp
  rw [hform, hform, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have hχ : -1 ≤ (χ n).re := by
    have h := Complex.abs_re_le_norm (χ n)
    linarith [neg_abs_le (χ n).re, χ.norm_le_one (n : ZMod q)]
  by_cases hu : IsUnit (n : ZMod q)
  · rw [MulChar.one_apply hu, one_re]
    nlinarith
  · rw [MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu, zero_re]
    simp

/-- A zero `β + iγ` with `β > 1/2` lies in the partial-fraction disc about `2 + iγ`. -/
theorem mem_pfBall_self {β γ : ℝ} (hβ : 1/2 < β) (hβ1 : β < 1) :
    ((β : ℂ) + γ * I) ∈ closedBall (2 + (γ : ℂ) * I) (22/25 * (91/50)) := by
  rw [mem_closedBall, Complex.dist_eq]
  have : (β : ℂ) + γ * I - (2 + γ * I) = ((β - 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith

/-- The kept zero contributes `1/(σ − β)` at height `γ`. -/
theorem re_inv_sub_zero_self (σ β γ : ℝ) :
    (((σ : ℂ) + γ * I - ((β : ℂ) + γ * I))⁻¹).re = 1 / (σ - β) := by
  have : (σ : ℂ) + γ * I - ((β : ℂ) + γ * I) = ((σ - β : ℝ) : ℂ) := by push_cast; ring
  rw [this, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]

/-- `log(q(2|γ| + 3)) ≤ 2 log(q(|γ| + 3))`. -/
theorem log_conductor_double_le (γ : ℝ) :
    Real.log ((q : ℝ) * (|2 * γ| + 3)) ≤ 2 * Real.log ((q : ℝ) * (|γ| + 3)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  rw [← Real.log_rpow (by positivity), abs_mul, abs_two]
  refine Real.log_le_log (by positivity) ?_
  rw [show ((q : ℝ) * (|γ| + 3)) ^ (2 : ℝ) = ((q : ℝ) * (|γ| + 3)) ^ (2 : ℕ) by norm_cast]
  nlinarith [abs_nonneg γ, sq_nonneg (|γ| + 3)]

theorem one_le_pfConst : 1 ≤ pfConst := by unfold pfConst; norm_num

/-- The conductor logarithm is at least one. -/
theorem one_le_log_conductor (γ : ℝ) : 1 ≤ Real.log ((q : ℝ) * (|γ| + 3)) :=
  one_lt_log_three.le.trans (log_three_le_log_conductor γ)

/-- From `4/(σ − β) ≤ k P` with `σ = 1 + 1/(m P)` and `4m > k`: `β ≤ 1 − (4m − k)/(k m P)`. -/
theorem le_of_four_div_le {β σ P k m : ℝ} (hP : 0 < P) (hk : 0 < k) (hm : 0 < m)
    (hσ : σ = 1 + 1 / (m * P)) (hX : 0 < σ - β) (h : 4 * (1 / (σ - β)) ≤ k * P) :
    β ≤ 1 - (4 * m - k) / (k * m * P) := by
  have h4 : 4 ≤ k * P * (σ - β) := by
    have := mul_le_mul_of_nonneg_right h hX.le
    rwa [mul_assoc, one_div_mul_cancel hX.ne', mul_one] at this
  have hXge : 4 / (k * P) ≤ σ - β := by rw [div_le_iff₀ (by positivity)]; linarith
  have hid : (4 * m - k) / (k * m * P) = 4 / (k * P) - 1 / (m * P) := by
    field_simp
  rw [hid]
  linarith

/-- **Complex characters.** A zero `β + iγ` with `β > 1/2` of `L(s, χ)`, `χ² ≠ 1`, has
`β ≤ 1 − 1/(84 A L)`. -/
theorem zero_free_of_sq_ne_one {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1)
    {β γ : ℝ} (hβ : 1/2 < β) (hzero : χ.LFunction (β + γ * I) = 0) :
    β ≤ 1 - 1 / (84 * (pfConst * Real.log ((q : ℝ) * (|γ| + 3)))) := by
  have hL1 := one_le_log_conductor (q := q) γ
  have hβ1 : β < 1 := by simpa using re_lt_one_of_LFunction_eq_zero hχ1 hzero
  have hlog2 := log_conductor_double_le (q := q) γ
  obtain ⟨P, hPdef⟩ : ∃ P, P = pfConst * Real.log ((q : ℝ) * (|γ| + 3)) := ⟨_, rfl⟩
  rw [← hPdef]
  have hP : 1 ≤ P := by rw [hPdef]; nlinarith [one_le_pfConst]
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = 1 + 1 / (12 * P) := ⟨_, rfl⟩
  have hpos : 0 < 1 / (12 * P) := by positivity
  have hle1 : 1 / (12 * P) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hσ1 : 1 < σ := by linarith
  have hσ2 : σ ≤ 2 := by linarith
  have h1σ : 1 / (σ - 1) = 12 * P := by rw [hσdef, add_sub_cancel_left, one_div_one_div]
  have h341 := three_four_one_logDeriv χ hσ1 γ
  have hT0 := neg_re_logDeriv_trivChar_real_le (q := q) hσ1 hσ2
  have hT1 := neg_re_logDeriv_LFunction_le hχ1 γ hσ1 hσ2 {(β : ℂ) + γ * I}
    (by simp only [Finset.mem_singleton, forall_eq]; exact ⟨hzero, mem_pfBall_self hβ hβ1⟩)
  rw [Finset.sum_singleton, re_inv_sub_zero_self, ← hPdef] at hT1
  have hT2 := neg_re_logDeriv_LFunction_le (χ := χ ^ 2) hχ2 (2 * γ) hσ1 hσ2 ∅ (by simp)
  rw [Finset.sum_empty, sub_zero,
    show (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I = σ + 2 * γ * I by push_cast; ring] at hT2
  simp only [neg_re] at h341 hT0
  have hT2' : pfConst * Real.log ((q : ℝ) * (|2 * γ| + 3)) ≤ 2 * P := by
    rw [hPdef]; nlinarith [pfConst_pos]
  have hX : 0 < σ - β := by linarith
  have hmain : 4 * (1 / (σ - β)) ≤ 42 * P := by linarith
  have h := le_of_four_div_le (by linarith) (by norm_num) (by norm_num) hσdef hX hmain
  have hid : (4 * 12 - 42 : ℝ) / (42 * 12 * P) = 1 / (84 * P) := by field_simp; ring
  rwa [hid] at h

/-- **Real characters away from the real axis.** For `χ² = 1` and `|γ| ≥ 1/(4 M L²)`, a zero with
`β > 1/2` has `β ≤ 1 − 1/(28 M L²)`, where `M = 4A + 4D + 1`. -/
theorem zero_free_of_sq_eq_one_far {D : ℝ} (hD : 0 < D)
    (hζ : ∀ s : ℂ, 1 < s.re → s.re ≤ 9/8 →
      (-deriv riemannZeta s / riemannZeta s).re ≤ ((s - 1)⁻¹).re + D * Real.log (|s.im| + 3) ^ 2)
    {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 = 1)
    {β γ : ℝ} (hβ : 1/2 < β) (hzero : χ.LFunction (β + γ * I) = 0)
    (hfar : 1 / (4 * (4 * pfConst + 4 * D + 1) * Real.log ((q : ℝ) * (|γ| + 3)) ^ 2) ≤ |γ|) :
    β ≤ 1 - 1 / (28 * (4 * pfConst + 4 * D + 1) * Real.log ((q : ℝ) * (|γ| + 3)) ^ 2) := by
  have hL1 := one_le_log_conductor (q := q) γ
  have hβ1 : β < 1 := by simpa using re_lt_one_of_LFunction_eq_zero hχ1 hzero
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hlogγ : Real.log (|γ| + 3) ≤ Real.log ((q : ℝ) * (|γ| + 3)) :=
    Real.log_le_log (by positivity) (le_mul_of_one_le_left (by positivity) hq1)
  have hlogq : Real.log q ≤ Real.log ((q : ℝ) * (|γ| + 3)) :=
    Real.log_le_log (by positivity) (le_mul_of_one_le_right (by positivity) (by linarith [abs_nonneg γ]))
  have hlog2γ : Real.log (|2 * γ| + 3) ≤ 2 * Real.log (|γ| + 3) := by
    rw [← Real.log_rpow (by positivity), abs_mul, abs_two]
    refine Real.log_le_log (by positivity) ?_
    rw [show (|γ| + 3) ^ (2 : ℝ) = (|γ| + 3) ^ (2 : ℕ) by norm_cast]
    nlinarith [abs_nonneg γ]
  have hlog0 : 0 ≤ Real.log (|2 * γ| + 3) := Real.log_nonneg (by linarith [abs_nonneg (2 * γ)])
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log ((q : ℝ) * (|γ| + 3)) := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M, M = 4 * pfConst + 4 * D + 1 := ⟨_, rfl⟩
  rw [← hLdef, ← hMdef] at hfar ⊢
  rw [← hLdef] at hL1 hlogγ hlogq
  have hM : 5 ≤ M := by rw [hMdef]; linarith [one_le_pfConst]
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ, ℓ = L ^ 2 := ⟨_, rfl⟩
  rw [show (28 : ℝ) * M * L ^ 2 = 28 * M * ℓ by rw [hℓdef]] 
  rw [show (4 : ℝ) * M * L ^ 2 = 4 * M * ℓ by rw [hℓdef]] at hfar
  have hℓ : L ≤ ℓ := by rw [hℓdef]; nlinarith
  have hℓ1 : 1 ≤ ℓ := hL1.trans hℓ
  have hlogim2 : Real.log (|2 * γ| + 3) ^ 2 ≤ 4 * ℓ := by
    have h3 : Real.log (|2 * γ| + 3) ≤ 2 * L := by linarith
    calc Real.log (|2 * γ| + 3) ^ 2 ≤ (2 * L) ^ 2 := pow_le_pow_left₀ hlog0 h3 2
      _ = 4 * ℓ := by rw [hℓdef]; ring
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = 1 / (4 * M * ℓ) := ⟨_, rfl⟩
  rw [← hedef] at hfar
  have he : 0 < e := by rw [hedef]; positivity
  have he8 : e ≤ 1 / 8 := by
    rw [hedef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul hM hℓ1 (by norm_num) (by linarith)]
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = 1 + e := ⟨_, rfl⟩
  have hσ1 : 1 < σ := by linarith
  have hσ2 : σ ≤ 2 := by linarith
  have hσ98 : σ ≤ 9 / 8 := by linarith
  have h1σ : 1 / (σ - 1) = 4 * M * ℓ := by rw [hσdef, add_sub_cancel_left, hedef, one_div_one_div]
  have h341 := three_four_one_logDeriv χ hσ1 γ
  rw [hχ2] at h341
  have hT0 := neg_re_logDeriv_trivChar_real_le (q := q) hσ1 hσ2
  have hT1 := neg_re_logDeriv_LFunction_le hχ1 γ hσ1 hσ2 {(β : ℂ) + γ * I}
    (by simp only [Finset.mem_singleton, forall_eq]; exact ⟨hzero, mem_pfBall_self hβ hβ1⟩)
  rw [Finset.sum_singleton, re_inv_sub_zero_self, ← hLdef] at hT1
  -- The principal `L`-function at `σ + 2iγ`, with the pole of `ζ`.
  have hsre : ((σ : ℂ) + 2 * γ * I).re = σ := by simp
  have hsim : ((σ : ℂ) + 2 * γ * I).im = 2 * γ := by simp
  have hT2 := neg_re_logDeriv_trivChar_le (q := q) (s := (σ : ℂ) + 2 * γ * I)
    (by rw [hsre]; exact hσ1)
  have hz := hζ ((σ : ℂ) + 2 * γ * I) (by rw [hsre]; exact hσ1) (by rw [hsre]; exact hσ98)
  rw [hsim] at hz
  have hpole : (((σ : ℂ) + 2 * γ * I - 1)⁻¹).re = e / (e ^ 2 + 4 * γ ^ 2) := by
    have : (σ : ℂ) + 2 * γ * I - 1 = ((e : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * I := by
      rw [hσdef]; push_cast; ring
    rw [this, Complex.inv_re, Complex.normSq_add_mul_I]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero]
    ring_nf
  have hγ2 : e ^ 2 ≤ γ ^ 2 := by
    have := pow_le_pow_left₀ he.le hfar 2
    rwa [sq_abs] at this
  have hpolebd : e / (e ^ 2 + 4 * γ ^ 2) ≤ M * ℓ := by
    calc e / (e ^ 2 + 4 * γ ^ 2) ≤ e / (4 * e ^ 2) :=
          div_le_div_of_nonneg_left he.le (by positivity) (by nlinarith)
      _ = M * ℓ := by rw [hedef]; field_simp
  simp only [neg_re] at h341 hT0
  have hX : 0 < σ - β := by linarith
  have hDℓ : D * Real.log (|2 * γ| + 3) ^ 2 ≤ D * (4 * ℓ) := mul_le_mul_of_nonneg_left hlogim2 hD.le
  have hAℓ : pfConst * L ≤ pfConst * ℓ := mul_le_mul_of_nonneg_left hℓ pfConst_pos.le
  have hmain : 4 * (1 / (σ - β)) ≤ 14 * M * ℓ := by
    rw [hpole] at hz
    simp only [neg_re] at hT2
    have hMℓ' : M * ℓ = 4 * (pfConst * ℓ) + 4 * (D * ℓ) + ℓ := by rw [hMdef]; ring
    have hlogqℓ : Real.log q ≤ ℓ := hlogq.trans hℓ
    linarith
  have hMℓ : 0 < M * ℓ := by positivity
  have h := le_of_four_div_le hMℓ (by norm_num : (0 : ℝ) < 14) (by norm_num : (0 : ℝ) < 4)
    (by rw [hσdef, hedef]; ring) hX (by linarith)
  have hid : (4 * 4 - 14 : ℝ) / (14 * 4 * (M * ℓ)) = 1 / (28 * M * ℓ) := by field_simp; ring
  rwa [hid] at h

/-- **Real characters near the real axis.** For `χ² = 1` and `0 < |γ| < 1/(4 M L²)`, a zero with
`β > 1/2` has `β ≤ 1 − 1/(5 M L²)`: its conjugate `β − iγ` is a zero too, and the two-term inequality
at real `σ` keeps both. -/
theorem zero_free_of_sq_eq_one_near {D : ℝ} (hD : 0 < D) {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1)
    (hχ2 : χ ^ 2 = 1) {β γ : ℝ} (hβ : 1/2 < β) (hγ0 : γ ≠ 0) (hzero : χ.LFunction (β + γ * I) = 0)
    (hnear : |γ| < 1 / (4 * (4 * pfConst + 4 * D + 1) * Real.log ((q : ℝ) * (|γ| + 3)) ^ 2))
    (hM5 : 5 ≤ 4 * pfConst + 4 * D + 1) :
    β ≤ 1 - 1 / (5 * (4 * pfConst + 4 * D + 1) * Real.log ((q : ℝ) * (|γ| + 3)) ^ 2) := by
  have hL1 := one_le_log_conductor (q := q) γ
  have hβ1 : β < 1 := by simpa using re_lt_one_of_LFunction_eq_zero hχ1 hzero
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hlog3q : Real.log ((q : ℝ) * (|(0 : ℝ)| + 3)) ≤ Real.log ((q : ℝ) * (|γ| + 3)) :=
    Real.log_le_log (by positivity) (by rw [abs_zero]; nlinarith [abs_nonneg γ])
  -- The conjugate zero.
  have hinv : χ⁻¹ = χ := inv_eq_of_mul_eq_one_right (by rw [← sq, hχ2])
  have hconj' : χ.LFunction ((β : ℂ) + ((-γ : ℝ) : ℂ) * I) = 0 := by
    have h := LFunction_inv_conj χ hχ1 ((β : ℂ) + γ * I)
    rw [hinv, hzero, map_zero] at h
    have hc : (starRingEnd ℂ) ((β : ℂ) + γ * I) = (β : ℂ) + ((-γ : ℝ) : ℂ) * I := by
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring
    rw [hc] at h
    exact h
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log ((q : ℝ) * (|γ| + 3)) := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M, M = 4 * pfConst + 4 * D + 1 := ⟨_, rfl⟩
  rw [← hLdef, ← hMdef] at hnear ⊢
  rw [← hLdef] at hL1 hlog3q
  rw [← hMdef] at hM5
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ, ℓ = L ^ 2 := ⟨_, rfl⟩
  rw [show (5 : ℝ) * M * L ^ 2 = 5 * M * ℓ by rw [hℓdef]]
  rw [show (4 : ℝ) * M * L ^ 2 = 4 * M * ℓ by rw [hℓdef]] at hnear
  have hℓ : L ≤ ℓ := by rw [hℓdef]; nlinarith
  have hℓ1 : 1 ≤ ℓ := hL1.trans hℓ
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = 1 / (4 * M * ℓ) := ⟨_, rfl⟩
  rw [← hedef] at hnear
  have he : 0 < e := by rw [hedef]; positivity
  have he8 : e ≤ 1 / 8 := by
    rw [hedef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul hM5 hℓ1 (by norm_num) (by linarith)]
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = 1 + 2 * e := ⟨_, rfl⟩
  have hσ1 : 1 < σ := by linarith
  have hσ2 : σ ≤ 2 := by linarith
  have h1σ : 1 / (σ - 1) = 2 * (M * ℓ) := by
    rw [hσdef, add_sub_cancel_left, hedef]; field_simp; ring
  -- Both zeros lie in the partial-fraction disc about `2`.
  have hγ8 : |γ| ≤ 1 / 8 := by linarith
  have hγsq : γ ^ 2 ≤ 1 / 64 := by
    have := pow_le_pow_left₀ (abs_nonneg γ) hγ8 2
    rw [sq_abs] at this; linarith
  have hball : ∀ g : ℝ, g ^ 2 ≤ 1 / 64 →
      ((β : ℂ) + g * I) ∈ closedBall (2 + ((0 : ℝ) : ℂ) * I) (22/25 * (91/50)) := by
    intro g hg
    rw [mem_closedBall, Complex.dist_eq, ← sq_le_sq₀ (norm_nonneg _) (by norm_num), Complex.sq_norm,
      Complex.normSq_apply]
    simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, sub_im, add_im, mul_im]
    norm_num
    nlinarith
  have hne : ((β : ℂ) + γ * I) ≠ (β : ℂ) + ((-γ : ℝ) : ℂ) * I := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hγ0 (by linarith)
  have hT1 := neg_re_logDeriv_LFunction_le hχ1 0 hσ1 hσ2
    {(β : ℂ) + γ * I, (β : ℂ) + ((-γ : ℝ) : ℂ) * I} (by
      intro ρ hρ
      rcases Finset.mem_insert.mp hρ with rfl | hρ'
      · exact ⟨hzero, hball γ hγsq⟩
      · rw [Finset.mem_singleton.mp hρ']
        exact ⟨hconj', hball (-γ) (by rw [neg_sq]; exact hγsq)⟩)
  rw [Finset.sum_pair hne] at hT1
  have hX : 0 < σ - β := by linarith
  have hre : ∀ g : ℝ, (((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ((β : ℂ) + g * I))⁻¹).re =
      (σ - β) / ((σ - β) ^ 2 + g ^ 2) := by
    intro g
    have : (σ : ℂ) + ((0 : ℝ) : ℂ) * I - ((β : ℂ) + g * I) =
        ((σ - β : ℝ) : ℂ) + ((-g : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, Complex.inv_re, Complex.normSq_add_mul_I]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero]
    ring_nf
  rw [hre γ, hre (-γ), neg_sq] at hT1
  have h2 := two_term_logDeriv χ hσ1
  have hT0 := neg_re_logDeriv_trivChar_real_le (q := q) hσ1 hσ2
  have hpt : (σ : ℂ) + ((0 : ℝ) : ℂ) * I = σ := by push_cast; ring
  rw [hpt] at hT1
  simp only [neg_re] at h2 hT0
  -- `γ² ≤ X²/4`, so the pair contributes at least `8/(5X)`.
  have hXe : 2 * e ≤ σ - β := by linarith
  have hγX : 4 * γ ^ 2 ≤ (σ - β) ^ 2 := by
    have h1 : 2 * |γ| ≤ σ - β := by linarith
    have := pow_le_pow_left₀ (by positivity) h1 2
    rw [mul_pow, sq_abs] at this; linarith
  have hpair : 8 / (5 * (σ - β)) ≤ 2 * ((σ - β) / ((σ - β) ^ 2 + γ ^ 2)) := by
    rw [div_le_iff₀ (by positivity)]
    have hden : 0 < (σ - β) ^ 2 + γ ^ 2 := by positivity
    rw [mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hden]
    nlinarith
  have hAℓ : pfConst * L ≤ M * ℓ / 4 := by
    have h1 : pfConst * L ≤ pfConst * ℓ := mul_le_mul_of_nonneg_left hℓ pfConst_pos.le
    have h2' : 4 * pfConst ≤ M := by rw [hMdef]; linarith
    nlinarith [mul_le_mul_of_nonneg_right h2' (by linarith : (0 : ℝ) ≤ ℓ)]
  have hAlog : pfConst * Real.log ((q : ℝ) * (|(0 : ℝ)| + 3)) ≤ pfConst * L :=
    mul_le_mul_of_nonneg_left hlog3q pfConst_pos.le
  have hmain : 4 * (1 / (σ - β)) ≤ 45 / 8 * (M * ℓ) := by
    have h85 : 8 / (5 * (σ - β)) = 8 / 5 * (1 / (σ - β)) := by field_simp
    set Y := (σ - β) / ((σ - β) ^ 2 + γ ^ 2)
    have s1 : 8 / 5 * (1 / (σ - β)) ≤ 2 * Y := h85 ▸ hpair
    have k1 := add_le_add hT0 hT1
    rw [h1σ] at k1
    have s2 : 2 * Y ≤ 2 * (M * ℓ) - 1 / 5 + pfConst * Real.log ((q : ℝ) * (|(0 : ℝ)| + 3)) := by
      linarith [h2, k1]
    linarith
  have hMℓ : 0 < M * ℓ := by positivity
  have h := le_of_four_div_le hMℓ (by norm_num : (0 : ℝ) < 45 / 8) (by norm_num : (0 : ℝ) < 2)
    (by rw [hσdef, hedef]; field_simp; ring) hX hmain
  have hcmp : 1 / (5 * M * ℓ) ≤ (4 * 2 - 45 / 8 : ℝ) / (45 / 8 * 2 * (M * ℓ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  linarith

/-- **A zero-free region for Dirichlet `L`-functions, uniform in the modulus.** -/
theorem uniform_zero_free_region : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ β γ : ℝ, χ.LFunction (β + γ * I) = 0 →
      (χ ^ 2 = 1 ∧ γ = 0) ∨ β ≤ 1 - c / Real.log ((q : ℝ) * (|γ| + 3)) ^ 2 := by
  obtain ⟨D, hD, hζ⟩ := exists_neg_re_logDeriv_zeta_le_pole
  set M := 4 * pfConst + 4 * D + 1 with hMdef
  have hA := one_le_pfConst
  have hM5 : 5 ≤ M := by rw [hMdef]; linarith
  refine ⟨1 / (84 * pfConst * M), by positivity, fun q _ χ hχ1 β γ hzero => ?_⟩
  have hL1 := one_le_log_conductor (q := q) γ
  set L := Real.log ((q : ℝ) * (|γ| + 3)) with hLdef
  have hℓ1 : 1 ≤ L ^ 2 := by nlinarith
  have hLℓ : L ≤ L ^ 2 := by nlinarith
  -- `c/L²` is below every case bound.
  have hM0 : 0 < M := by linarith
  have h28 : 28 * M ≤ 84 * pfConst * M := by nlinarith
  have h5 : 5 * M ≤ 84 * pfConst * M := by nlinarith
  have hc : ∀ k : ℝ, 0 < k → k ≤ 84 * pfConst * M → 1 / (84 * pfConst * M) / L ^ 2 ≤ 1 / (k * L ^ 2) := by
    intro k hk hkle
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  by_cases hβ : β ≤ 1 / 2
  · right
    have : 1 / (84 * pfConst * M) / L ^ 2 ≤ 1 / 2 := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  push Not at hβ
  by_cases hχ2 : χ ^ 2 = 1
  · by_cases hγ0 : γ = 0
    · exact Or.inl ⟨hχ2, hγ0⟩
    right
    by_cases hfar : 1 / (4 * M * L ^ 2) ≤ |γ|
    · have h := zero_free_of_sq_eq_one_far hD hζ hχ1 hχ2 hβ hzero hfar
      have := hc (28 * M) (by positivity) h28
      rw [← hMdef, ← hLdef] at h
      linarith
    · push Not at hfar
      have h := zero_free_of_sq_eq_one_near hD hχ1 hχ2 hβ hγ0 hzero hfar hM5
      have := hc (5 * M) (by positivity) h5
      rw [← hMdef, ← hLdef] at h
      linarith
  · right
    have h := zero_free_of_sq_ne_one hχ1 hχ2 hβ hzero
    have h1 : 1 / (84 * pfConst * M) / L ^ 2 ≤ 1 / (84 * (pfConst * L)) := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hLℓ (by positivity : (0 : ℝ) ≤ 84 * pfConst)]
    linarith

end RHTower
