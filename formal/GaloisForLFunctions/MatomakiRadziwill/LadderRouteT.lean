import GaloisForLFunctions.MatomakiRadziwill.LadderHM
import GaloisForLFunctions.MatomakiRadziwill.PrimeBlockRouteT
import Mathlib.NumberTheory.ArithmeticFunction.Liouville

/-!
# The twisted Liouville function and Route T at the top scale

`f = λχ` (`twLiouville`) is completely multiplicative with `|f| ≤ 1` and `f(p) = −χ(p)`.  At the top
scale `Pr* = {A < p ≤ B prime}` a block `{p : ⌊H log p⌋ = v}` is the set of all primes of an
interval `(P', Q']` (`block_eq_Ioc`), and its normalised polynomial is
`Q_v(w) = −Σ_{P' < p ≤ Q'} χ(p) p^{-1-iτ}`, `τ = −2πw` (`blockQ_twLiouville_eq`).  Route T for `χ`
(`exists_primeBlock_le`) then bounds every block pointwise (`exists_norm_blockQ_twLiouville_le`):
`|Q_v(w)| ≤ (log X)^{-A}` for `|w| ≤ X/(2π)`, once `log A ≥ (log X)^θ`, `B ≤ X`, `H ≥ 2`.
-/

open Finset Complex ArithmeticFunction RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

variable {q : ℕ}

/-- The twisted Liouville function `λχ`. -/
def twLiouville (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ := (liouville n : ℂ) * χ n

theorem twLiouville_mul (χ : DirichletCharacter ℂ q) (a b : ℕ) :
    twLiouville χ (a * b) = twLiouville χ a * twLiouville χ b := by
  rw [twLiouville, twLiouville, twLiouville, liouville_apply_mul, Nat.cast_mul, map_mul]
  push_cast
  ring

theorem norm_twLiouville_le (χ : DirichletCharacter ℂ q) (n : ℕ) : ‖twLiouville χ n‖ ≤ 1 := by
  rw [twLiouville, norm_mul]
  have h1 : ‖((liouville n : ℤ) : ℂ)‖ ≤ 1 := by
    by_cases hn : n = 0
    · subst hn; simp
    · rw [liouville_apply hn]
      push_cast
      rw [norm_pow, norm_neg, norm_one, one_pow]
  exact mul_le_one₀ h1 (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)

theorem twLiouville_prime (χ : DirichletCharacter ℂ q) {p : ℕ} (hp : p.Prime) :
    twLiouville χ p = -χ p := by
  rw [twLiouville, liouville_apply hp.ne_zero, cardFactors_apply_prime hp]
  push_cast
  ring

/-- A block of the top scale is the set of all primes of an interval. -/
theorem block_eq_Ioc {A B : ℕ} {H : ℝ} (hH : 0 < H) (v : ℕ) :
    ((Ioc A B).filter Nat.Prime).filter (fun p => blk H p = v)
      = (Ioc (max A (⌈Real.exp ((v : ℝ) / H)⌉₊ - 1))
          (min B (⌈Real.exp (((v : ℝ) + 1) / H)⌉₊ - 1))).filter Nat.Prime := by
  ext p
  simp only [mem_filter, mem_Ioc, max_lt_iff, le_min_iff]
  constructor
  · rintro ⟨⟨⟨hA, hB⟩, hp⟩, hv⟩
    obtain ⟨h1, h2⟩ := exp_blk_le hH hp.one_lt.le
    rw [hv] at h1 h2
    have c1 : ⌈Real.exp ((v : ℝ) / H)⌉₊ ≤ p := Nat.ceil_le.mpr h1
    have c2 : p < ⌈Real.exp (((v : ℝ) + 1) / H)⌉₊ := Nat.lt_ceil.mpr h2
    exact ⟨⟨⟨hA, by omega⟩, hB, by omega⟩, hp⟩
  · rintro ⟨⟨⟨hA, h1⟩, hB, h2⟩, hp⟩
    refine ⟨⟨⟨hA, hB⟩, hp⟩, ?_⟩
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hlog : 0 ≤ H * Real.log p := mul_nonneg hH.le (Real.log_nonneg hp1)
    have e1 : Real.exp ((v : ℝ) / H) ≤ p := by
      have : ⌈Real.exp ((v : ℝ) / H)⌉₊ ≤ p := by omega
      exact Nat.ceil_le.mp this
    have e2 : (p : ℝ) < Real.exp (((v : ℝ) + 1) / H) := by
      have : p < ⌈Real.exp (((v : ℝ) + 1) / H)⌉₊ := by omega
      exact Nat.lt_ceil.mp this
    have hp0 : (0 : ℝ) < p := by linarith
    rw [blk, Nat.floor_eq_iff hlog]
    constructor
    · have := Real.log_le_log (Real.exp_pos _) e1
      rw [Real.log_exp, div_le_iff₀ hH] at this
      linarith
    · have := Real.log_lt_log hp0 e2
      rw [Real.log_exp, lt_div_iff₀ hH] at this
      linarith

/-- The normalised block polynomial of `λχ` is minus a twisted prime sum. -/
theorem blockQ_twLiouville_eq (χ : DirichletCharacter ℂ q) (Pr : Finset ℕ)
    (hPr : ∀ p ∈ Pr, p.Prime) (H : ℝ) (v : ℕ) (w : ℝ) :
    blockQ (twLiouville χ) Pr H v w
      = -∑ p ∈ Pr.filter (fun p => blk H p = v),
          χ p * (p : ℂ) ^ (-(1 + (((-(2 * Real.pi * w)) : ℝ) : ℂ) * I)) := by
  rw [blockQ, logPoly_eq_sum_mul_unitLogPhase, ← sum_neg_distrib]
  refine sum_congr rfl fun p hp => ?_
  have hpp := hPr p (mem_filter.mp hp).1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  rw [coefA, twLiouville_prime χ hpp, unitLogPhase]
  have hcpow : (p : ℂ) ^ (-(1 + (((-(2 * Real.pi * w)) : ℝ) : ℂ) * I))
      = (p : ℂ)⁻¹ * Complex.exp (((2 * Real.pi * (w * Real.log p) : ℝ) : ℂ) * I) := by
    rw [show -(1 + (((-(2 * Real.pi * w)) : ℝ) : ℂ) * I)
        = -1 + (((2 * Real.pi * w) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.cpow_add _ _ (by exact_mod_cast hpp.ne_zero), Complex.cpow_neg_one,
      Complex.cpow_def_of_ne_zero (by exact_mod_cast hpp.ne_zero),
      ← Complex.ofReal_natCast, ← Complex.ofReal_log hp0.le]
    congr 2
    push_cast
    ring
  rw [hcpow]
  field_simp

theorem exp_half_lt : Real.exp (1 / 2) < 1.7 := by
  have h1 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 : Real.exp 1 < 2.89 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h3 : 0 < Real.exp (1 / 2) := Real.exp_pos _
  nlinarith

/-- The interval of a top-scale block has ratio at most two. -/
theorem block_Q_le_two_P {Pa : ℕ} (hPa : 8 ≤ Pa) {H : ℝ} (hH : 2 ≤ H) (v Pb : ℕ) :
    min Pb (⌈Real.exp (((v : ℝ) + 1) / H)⌉₊ - 1)
      ≤ 2 * max Pa (⌈Real.exp ((v : ℝ) / H)⌉₊ - 1) := by
  set E := Real.exp ((v : ℝ) / H) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hH0 : (0 : ℝ) < H := by linarith
  have hexp : Real.exp (((v : ℝ) + 1) / H) < 1.7 * E := by
    rw [show ((v : ℝ) + 1) / H = (v : ℝ) / H + 1 / H by ring, Real.exp_add, ← hE]
    have h1 : Real.exp (1 / H) ≤ Real.exp (1 / 2) :=
      Real.exp_le_exp.mpr (one_div_le_one_div_of_le (by norm_num) hH)
    have := exp_half_lt
    nlinarith
  -- `Q' < 1.7 E`
  have hQ : ((min Pb (⌈Real.exp (((v : ℝ) + 1) / H)⌉₊ - 1) : ℕ) : ℝ) < 1.7 * E := by
    have hc := Nat.ceil_lt_add_one (Real.exp_pos (((v : ℝ) + 1) / H)).le
    have h1 : ((min Pb (⌈Real.exp (((v : ℝ) + 1) / H)⌉₊ - 1) : ℕ) : ℝ)
        ≤ ((⌈Real.exp (((v : ℝ) + 1) / H)⌉₊ - 1 : ℕ) : ℝ) := by exact_mod_cast min_le_right _ _
    have h2 : ((⌈Real.exp (((v : ℝ) + 1) / H)⌉₊ - 1 : ℕ) : ℝ) < Real.exp (((v : ℝ) + 1) / H) := by
      rcases Nat.eq_zero_or_pos ⌈Real.exp (((v : ℝ) + 1) / H)⌉₊ with h0 | hpos
      · rw [h0]; simp; exact Real.exp_pos _
      · rw [Nat.cast_sub hpos]; push_cast; linarith
    linarith
  -- `P' ≥ max(8, E − 1)`
  have hP1 : (8 : ℝ) ≤ ((max Pa (⌈E⌉₊ - 1) : ℕ) : ℝ) := by
    have : 8 ≤ max Pa (⌈E⌉₊ - 1) := le_trans hPa (le_max_left _ _)
    exact_mod_cast this
  have hP2 : E - 1 ≤ ((max Pa (⌈E⌉₊ - 1) : ℕ) : ℝ) := by
    have h1 : ((⌈E⌉₊ - 1 : ℕ) : ℝ) ≤ ((max Pa (⌈E⌉₊ - 1) : ℕ) : ℝ) := by
      exact_mod_cast le_max_right _ _
    have h2 : E - 1 ≤ ((⌈E⌉₊ - 1 : ℕ) : ℝ) := by
      have hc : E ≤ (⌈E⌉₊ : ℝ) := Nat.le_ceil E
      have hpos : 1 ≤ ⌈E⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
        intro h; rw [Nat.ceil_eq_zero] at h; linarith)
      rw [Nat.cast_sub hpos]; push_cast; linarith
    linarith
  have hlt : ((min Pb (⌈Real.exp (((v : ℝ) + 1) / H)⌉₊ - 1) : ℕ) : ℝ)
      < 2 * ((max Pa (⌈E⌉₊ - 1) : ℕ) : ℝ) := by
    rcases le_or_gt 7 E with h7 | h7
    · linarith
    · linarith
  have : min Pb (⌈Real.exp (((v : ℝ) + 1) / H)⌉₊ - 1) < 2 * max Pa (⌈E⌉₊ - 1) := by
    exact_mod_cast hlt
  omega

/-- **Route T at the top scale of the ladder.** -/
theorem exists_norm_blockQ_twLiouville_le [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {θ A : ℝ}
    (hθ : 2 / 3 < θ) (hA : 0 ≤ A) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ (Pa Pb : ℕ) (H : ℝ), 2 ≤ H →
      Real.log X ^ θ ≤ Real.log Pa → (Pb : ℝ) ≤ X → ∀ v : ℕ, ∀ w : ℝ, 2 * Real.pi * |w| ≤ X →
        ‖blockQ (twLiouville χ) ((Ioc Pa Pb).filter Nat.Prime) H v w‖ ≤ 1 / Real.log X ^ A := by
  obtain ⟨X₀, hX₀⟩ := exists_primeBlock_le χ hχ hθ hA
  refine ⟨max X₀ (Real.exp 4), fun X hX Pa Pb H hH hlogPa hPbX v w hw => ?_⟩
  have hX1 : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp 4 ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos 4) hXe
  have hlogX : 4 ≤ Real.log X := by rw [Real.le_log_iff_exp_le hX0]; exact hXe
  have hH0 : (0 : ℝ) < H := by linarith
  -- `(log X)^θ ≥ 2`, so `Pa ≥ 8`
  have hθ2 : 2 ≤ Real.log X ^ θ := by
    have h1 : Real.log X ^ (1 / 2 : ℝ) ≤ Real.log X ^ θ :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h2 : (4 : ℝ) ^ (1 / 2 : ℝ) ≤ Real.log X ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hlogX (by norm_num)
    have h3 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
      rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  have hPa : 8 ≤ Pa := by
    have hlog2 : 2 ≤ Real.log Pa := le_trans hθ2 hlogPa
    have hPa0 : 0 < Pa := by
      by_contra h0
      have : Pa = 0 := by omega
      rw [this] at hlog2
      simp at hlog2
      linarith
    have hpos : (0 : ℝ) < Pa := by exact_mod_cast hPa0
    have h1 : Real.exp 2 ≤ Pa := by
      rw [← Real.exp_log hpos]; exact Real.exp_le_exp.mpr hlog2
    have h2 : (7 : ℝ) < Real.exp 2 := by
      have := Real.add_one_le_exp (1 : ℝ)
      have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      have h4 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      nlinarith
    have : (7 : ℝ) < Pa := lt_of_lt_of_le h2 h1
    have : 7 < Pa := by exact_mod_cast this
    omega
  have hprimes : ∀ p ∈ (Ioc Pa Pb).filter Nat.Prime, p.Prime := fun p hp => (mem_filter.mp hp).2
  rw [blockQ_twLiouville_eq χ _ hprimes H v w, norm_neg, block_eq_Ioc hH0 v]
  have hτ : |(-(2 * Real.pi * w))| ≤ X := by
    rw [abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    exact hw
  have hL0 : 0 ≤ 1 / Real.log X ^ A := by
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Real.log X) A
    positivity
  have hQ2 := block_Q_le_two_P hPa hH v Pb
  by_cases hPQ : max Pa (⌈Real.exp ((v : ℝ) / H)⌉₊ - 1) ≤ min Pb (⌈Real.exp (((v : ℝ) + 1) / H)⌉₊ - 1)
  · refine hX₀ X hX1 _ hτ _ _ ?_ hPQ hQ2 ?_
    · have hPa0 : (0 : ℝ) < Pa := by exact_mod_cast (show 0 < Pa by omega)
      exact le_trans hlogPa (Real.log_le_log hPa0 (by exact_mod_cast le_max_left _ _))
    · exact le_trans (by exact_mod_cast min_le_left _ _) hPbX
  · have hempty : (Ioc (max Pa (⌈Real.exp ((v : ℝ) / H)⌉₊ - 1))
        (min Pb (⌈Real.exp (((v : ℝ) + 1) / H)⌉₊ - 1))).filter Nat.Prime = ∅ := by
      rw [filter_eq_empty_iff]
      intro p hp
      rw [mem_Ioc] at hp
      omega
    rw [hempty, sum_empty, norm_zero]
    exact hL0

end

end GaloisForLFunctions.MatomakiRadziwill
