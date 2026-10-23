import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheQuarterLawOfSymmetricResidueFlips
import GaloisForLFunctions.RHTower.DirichletLEulerLogarithmRightOfTheOneLine

/-!
# The quarter law of residue flips

For every `q ≥ 1` and every `S ⊆ ZMod q`, the half-damped weight `f_{q,S}(d) d^{-1/2}` of the
residue-class flip is paid **iff** more than a quarter of the unit classes are flipped,
`φ(q) < 4 #(S ∩ (ZMod q)ˣ)` (`receiverBounded_residueFlip_half_iff_general`).

Without symmetry the coefficients `s_χ = Σ_{u ∈ S unit} χ(u⁻¹)` are complex, and
`−Re(s_χ Σ_p χ(p) p^{-w}) ≤ |s_χ| (|ℓ_χ(w)| + S)`, `ℓ_χ` the Euler logarithm of `L(·, χ)`
(`norm_tsum_char_sub_eulerLog_le`). So `|F| ≤ e^B |ζ|^{1−2ρ} exp((2/φ) Σ_{χ≠1} |s_χ| |ℓ_χ|)`
(`exists_norm_residueFlip_le_exp`), and `|ℓ_χ|` is bounded on the box `|Im w| ≤ 9` and
`≤ 9 log log|Im w| + C` beyond (`RHTower.exists_norm_eulerLog_le_box`,
`RHTower.exists_norm_eulerLog_le_large`): the exponential factor is at most a power of `log|Im w|`, and
the line-energy argument of the symmetric case applies verbatim
(`exists_norm_residueFlip_bounds_of`, `receiverBounded_residueFlip_half_of_bounds`).

With `not_receiverBounded_residueFlip_half_of_le` this decides the half-damped receiver on the whole
residue family: the flipped proportion `1/4` is the exact threshold.
-/

open Filter Topology MeasureTheory Complex Set
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- The prime sum of a character is its Euler logarithm up to `S = Σ_p p^{-2}`. -/
theorem norm_tsum_char_sub_eulerLog_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {w : ℂ}
    (hw : 1 < w.re) :
    ‖∑' p : Nat.Primes, χ p * ((p : ℕ) : ℂ) ^ (-w) - RHTower.eulerLog χ w‖ ≤ primeSquareMass := by
  set y : Nat.Primes → ℂ := fun p => χ p * ((p : ℕ) : ℂ) ^ (-w)
  have hy : ∀ p : Nat.Primes, ‖y p‖ ≤ ((p : ℕ) : ℝ) ^ (-w.re) := fun p =>
    RHTower.norm_char_prime_cpow_le χ p
  have hys : Summable y := (Nat.Primes.summable_rpow.mpr (by linarith)).of_norm_bounded hy
  have hL : Summable (fun p : Nat.Primes => -Complex.log (1 - y p)) := hys.clog_one_sub.neg
  have hterm : ∀ p : Nat.Primes, ‖y p - -Complex.log (1 - y p)‖ ≤ ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
    intro p
    have hyh : ‖-y p‖ ≤ 1 / 2 := by
      rw [norm_neg]; exact (hy p).trans (_root_.RHTower.prime_rpow_neg_le_half hw.le p)
    have h := norm_log_one_add_sub_self_le_sq hyh
    rw [norm_neg, ← sub_eq_add_neg] at h
    calc ‖y p - -Complex.log (1 - y p)‖ = ‖Complex.log (1 - y p) - -y p‖ := by
          congr 1; ring
      _ ≤ ‖y p‖ ^ 2 := h
      _ ≤ ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
          refine (pow_le_pow_left₀ (norm_nonneg _) (hy p) 2).trans ?_
          rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_lt.le)
            (by push_cast; linarith)
  have hdiff := hys.sub hL
  rw [RHTower.eulerLog, ← hys.tsum_sub hL]
  exact (norm_tsum_le_tsum_norm hdiff.norm).trans
    (Summable.tsum_le_tsum hterm hdiff.norm summable_primeSquare)

/-- **The general Euler bound**: on `Re w > 1`,
`log|F(w)| ≤ (1 − 2s_1/φ) log|ζ(w)| + (2/φ) Σ_{χ ≠ 1} |s_χ| |ℓ_χ(w)| + B`. -/
theorem exists_log_norm_residueFlip_le_general {q : ℕ} [NeZero q] (S : Finset (ZMod q)) :
    ∃ B : ℝ, ∀ w : ℂ, 1 < w.re →
      Real.log ‖∑' n : ℕ, (residueFlip q S n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
        (1 - 2 * (setCoeff S 1).re / q.totient) * Real.log ‖riemannZeta w‖ +
          2 / q.totient * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            ‖setCoeff S χ‖ * ‖RHTower.eulerLog χ w‖ + B := by
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hS₂ : 0 ≤ primeSquareMass := tsum_nonneg fun p => by positivity
  set s₁ : ℝ := (setCoeff S 1).re
  have hs₁im : (setCoeff S 1).im = 0 := by rw [setCoeff_one, Complex.natCast_im]
  refine ⟨primeSquareMass + |1 - 2 * s₁ / q.totient| * primeSquareMass +
    2 * |s₁| / q.totient * (q + 1) + 2 * (q + 1) +
    2 / q.totient * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      ‖setCoeff S χ‖ * primeSquareMass, fun w hw => ?_⟩
  have hF := abs_log_norm_tsum_sub_re_le (cweightedPatternHom (residueFlip q S) w) hw fun n => by
    simp only [cweightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_natCast]
    exact mul_le_of_le_one_left (norm_nonneg _) (abs_residueFlip_le_one q S n)
  have hFn : ∑' n, cweightedPatternHom (residueFlip q S) w n =
      ∑' n : ℕ, (residueFlip q S n : ℂ) * ((n : ℝ) : ℂ) ^ (-w) := tsum_congr fun n => rfl
  have hFp : ∑' p : Nat.Primes, cweightedPatternHom (residueFlip q S) w p =
      ∑' p : Nat.Primes, (residueFlip q S p : ℂ) * ((p : ℕ) : ℂ) ^ (-w) := tsum_congr fun p => by
    simp only [cweightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      Complex.ofReal_natCast]
  have hS2 : ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) = primeSquareMass := rfl
  rw [hFn, hFp, tsum_residueFlip_prime_eq S hw, hS2] at hF
  -- the principal sum is `P − N`
  have hys := summable_prime_cpow_neg hw
  have hNs : Summable (fun p : Nat.Primes =>
      if IsUnit ((p : ℕ) : ZMod q) then (0 : ℂ) else ((p : ℕ) : ℂ) ^ (-w)) :=
    hys.norm.of_norm_bounded fun p => by split_ifs <;> simp
  have hP1 : ∑' p : Nat.Primes, (1 : DirichletCharacter ℂ q) p * ((p : ℕ) : ℂ) ^ (-w) =
      ∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-w) -
        ∑' p : Nat.Primes, (if IsUnit ((p : ℕ) : ZMod q) then 0 else ((p : ℕ) : ℂ) ^ (-w)) := by
    rw [← hys.tsum_sub hNs]
    refine tsum_congr fun p => ?_
    by_cases hu : IsUnit ((p : ℕ) : ZMod q)
    · rw [MulChar.one_apply hu, if_pos hu]; ring
    · rw [MulChar.map_nonunit _ hu, if_neg hu]; ring
  -- real parts of the split
  have hre : (∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-w) - 2 / (q.totient : ℂ) *
      ∑ χ : DirichletCharacter ℂ q, setCoeff S χ * ∑' p : Nat.Primes, χ p * ((p : ℕ) : ℂ) ^ (-w) +
        ∑' p : Nat.Primes, ((residueFlip q S p : ℂ) - 1) *
          (if IsUnit ((p : ℕ) : ZMod q) then 0 else ((p : ℕ) : ℂ) ^ (-w))).re =
      (1 - 2 * s₁ / q.totient) * (∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-w)).re +
        2 * s₁ / q.totient *
          (∑' p : Nat.Primes, (if IsUnit ((p : ℕ) : ZMod q) then 0 else ((p : ℕ) : ℂ) ^ (-w))).re -
        2 / q.totient * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          (setCoeff S χ * ∑' p : Nat.Primes, χ p * ((p : ℕ) : ℂ) ^ (-w)).re +
        (∑' p : Nat.Primes, ((residueFlip q S p : ℂ) - 1) *
          (if IsUnit ((p : ℕ) : ZMod q) then 0 else ((p : ℕ) : ℂ) ^ (-w))).re := by
    have hc : (2 / (q.totient : ℂ)) = (((2 / q.totient : ℝ)) : ℂ) := by push_cast; rfl
    rw [Complex.add_re, Complex.sub_re, hc, Complex.re_ofReal_mul, Complex.re_sum,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ q)), hP1,
      Complex.mul_re, hs₁im, zero_mul, sub_zero, Complex.sub_re]
    ring
  rw [hre] at hF
  set P := ∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-w)
  set N := ∑' p : Nat.Primes, (if IsUnit ((p : ℕ) : ZMod q) then 0 else ((p : ℕ) : ℂ) ^ (-w))
  set E := ∑' p : Nat.Primes, ((residueFlip q S p : ℂ) - 1) *
    (if IsUnit ((p : ℕ) : ZMod q) then 0 else ((p : ℕ) : ℂ) ^ (-w))
  have hζ := abs_log_norm_riemannZeta_sub_re_le hw
  have hNb : |N.re| ≤ q + 1 :=
    (Complex.abs_re_le_norm _).trans (norm_tsum_nonunit_primes_le (q := q) hw)
  have hEb : |E.re| ≤ 2 * (q + 1) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    have h := norm_tsum_nonunit_primes_mul_le (q := q) hw
      (fun n => (residueFlip q S n : ℂ) - 1) fun n => by
        have h1 := abs_residueFlip_le_one q S n
        calc ‖(residueFlip q S n : ℂ) - 1‖ ≤ ‖(residueFlip q S n : ℂ)‖ + ‖(1 : ℂ)‖ :=
              norm_sub_le _ _
          _ ≤ 1 + 1 := by rw [Complex.norm_real, Real.norm_eq_abs, norm_one]; linarith
          _ = 2 := by norm_num
    refine le_of_eq_of_le ?_ h
    congr 1
    refine tsum_congr fun p => ?_
    split_ifs <;> simp
  -- each nonprincipal term
  have hχs : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      -(setCoeff S χ * ∑' p : Nat.Primes, χ p * ((p : ℕ) : ℂ) ^ (-w)).re ≤
        ‖setCoeff S χ‖ * ‖RHTower.eulerLog χ w‖ + ‖setCoeff S χ‖ * primeSquareMass := by
    intro χ _
    have h1 := neg_le_abs ((setCoeff S χ * ∑' p : Nat.Primes, χ p * ((p : ℕ) : ℂ) ^ (-w)).re)
    have h2 := Complex.abs_re_le_norm (setCoeff S χ * ∑' p : Nat.Primes, χ p * ((p : ℕ) : ℂ) ^ (-w))
    rw [norm_mul] at h2
    have h3 : ‖∑' p : Nat.Primes, χ p * ((p : ℕ) : ℂ) ^ (-w)‖ ≤
        ‖RHTower.eulerLog χ w‖ + primeSquareMass := by
      have := norm_sub_norm_le (∑' p : Nat.Primes, χ p * ((p : ℕ) : ℂ) ^ (-w)) (RHTower.eulerLog χ w)
      linarith [norm_tsum_char_sub_eulerLog_le χ hw]
    have h4 := mul_le_mul_of_nonneg_left h3 (norm_nonneg (setCoeff S χ))
    linarith
  have hsumχ := Finset.sum_le_sum hχs
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib] at hsumχ
  have hφ2 : 0 ≤ 2 / (q.totient : ℝ) := by positivity
  have hsumχ' := mul_le_mul_of_nonneg_left hsumχ hφ2
  have hζterm : (1 - 2 * s₁ / q.totient) * P.re ≤
      (1 - 2 * s₁ / q.totient) * Real.log ‖riemannZeta w‖ +
        |1 - 2 * s₁ / q.totient| * primeSquareMass := by
    have h2 : |(1 - 2 * s₁ / q.totient) * (P.re - Real.log ‖riemannZeta w‖)| ≤
        |1 - 2 * s₁ / q.totient| * primeSquareMass := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact hζ) (abs_nonneg _)
    have h3 := le_abs_self ((1 - 2 * s₁ / q.totient) * (P.re - Real.log ‖riemannZeta w‖))
    linarith [mul_sub (1 - 2 * s₁ / q.totient) P.re (Real.log ‖riemannZeta w‖)]
  have hNterm : 2 * s₁ / q.totient * N.re ≤ 2 * |s₁| / q.totient * (q + 1) := by
    have h1 : 2 * s₁ / q.totient * N.re ≤ |2 * s₁ / q.totient * N.re| := le_abs_self _
    have h2 : |2 * s₁ / q.totient * N.re| = 2 * |s₁| / q.totient * |N.re| := by
      rw [abs_mul, abs_div, abs_mul, abs_two, abs_of_pos hφ]
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hNb (by positivity))
  have hEterm := le_abs_self E.re
  have hFle := (abs_le.mp hF).2
  linarith

/-- **The general Euler bound as an exponential**:
`|F(w)| ≤ e^B |ζ(w)|^{1 − 2s_1/φ} exp((2/φ) Σ_{χ ≠ 1} |s_χ| |ℓ_χ(w)|)` on `Re w > 1`. -/
theorem exists_norm_residueFlip_le_exp {q : ℕ} [NeZero q] (S : Finset (ZMod q)) :
    ∃ B : ℝ, ∀ w : ℂ, 1 < w.re →
      ‖∑' n : ℕ, (residueFlip q S n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
        Real.exp B * ‖riemannZeta w‖ ^ (1 - 2 * (setCoeff S 1).re / q.totient) *
          Real.exp (2 / q.totient * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            ‖setCoeff S χ‖ * ‖RHTower.eulerLog χ w‖) := by
  obtain ⟨B, hB⟩ := exists_log_norm_residueFlip_le_general S
  refine ⟨B, fun w hw => ?_⟩
  have hζ := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re hw.le)
  rcases (norm_nonneg (∑' n : ℕ, (residueFlip q S n : ℂ) * ((n : ℝ) : ℂ) ^ (-w))).eq_or_lt
    with h0 | hpos
  · rw [← h0]; positivity
  rw [← Real.exp_log hpos, Real.rpow_def_of_pos hζ, ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h := hB w hw
  linarith

/-- The exponential factor is bounded on the box and a power of `log|Im w|` beyond. -/
theorem exists_exp_eulerLog_sum_le {q : ℕ} [NeZero q] (S : Finset (ZMod q)) :
    ∃ Ml Cl : ℝ, ∃ N : ℕ, 0 ≤ Ml ∧ 0 ≤ Cl ∧ ∀ w : ℂ, 1 < w.re → w.re ≤ 2 →
      (|w.im| ≤ 9 → Real.exp (2 / q.totient * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ‖setCoeff S χ‖ * ‖RHTower.eulerLog χ w‖) ≤ Ml) ∧
      (9 ≤ |w.im| → Real.exp (2 / q.totient * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ‖setCoeff S χ‖ * ‖RHTower.eulerLog χ w‖) ≤ Cl * Real.log |w.im| ^ N) := by
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hbox : ∀ χ : DirichletCharacter ℂ q, ∃ C : ℝ, 0 ≤ C ∧ (χ ≠ 1 → ∀ σ t : ℝ, 1 < σ → σ ≤ 2 →
      |t| ≤ 9 → ‖RHTower.eulerLog χ (σ + t * I)‖ ≤ C) := fun χ => by
    by_cases hχ : χ = 1
    · exact ⟨0, le_rfl, fun h => absurd hχ h⟩
    · obtain ⟨C, hC⟩ := RHTower.exists_norm_eulerLog_le_box hχ
      exact ⟨|C|, abs_nonneg _, fun _ σ t h1 h2 h3 => (hC σ t h1 h2 h3).trans (le_abs_self C)⟩
  choose Cb hCb0 hCb using hbox
  have hlarge : ∀ χ : DirichletCharacter ℂ q, ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 1 < σ → σ ≤ 2 →
      9 ≤ |t| → ‖RHTower.eulerLog χ (σ + t * I)‖ ≤ 9 * Real.log (Real.log |t|) + C := fun χ => by
    obtain ⟨C, hC⟩ := RHTower.exists_norm_eulerLog_le_large χ
    exact ⟨|C|, abs_nonneg _, fun σ t h1 h2 h3 => (hC σ t h1 h2 h3).trans (by linarith [le_abs_self C])⟩
  choose Cl' hCl0 hCl using hlarge
  set E := Finset.univ.erase (1 : DirichletCharacter ℂ q)
  set c₀ : ℝ := 2 / q.totient * ∑ χ ∈ E, ‖setCoeff S χ‖
  have hc₀ : 0 ≤ c₀ := mul_nonneg (by positivity) (Finset.sum_nonneg fun χ _ => norm_nonneg _)
  refine ⟨Real.exp (2 / q.totient * ∑ χ ∈ E, ‖setCoeff S χ‖ * Cb χ),
    Real.exp (2 / q.totient * ∑ χ ∈ E, ‖setCoeff S χ‖ * Cl' χ), ⌈9 * c₀⌉₊, (Real.exp_pos _).le,
    (Real.exp_pos _).le, fun w hw hw2 => ⟨fun ht => ?_, fun ht => ?_⟩⟩
  · have hwst : w = (w.re : ℂ) + (w.im : ℂ) * I := (Complex.re_add_im w).symm
    refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun χ hχ => ?_)
      (by positivity))
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h := hCb χ (Finset.ne_of_mem_erase hχ) w.re w.im hw hw2 ht
    rwa [← hwst] at h
  · have hwst : w = (w.re : ℂ) + (w.im : ℂ) * I := (Complex.re_add_im w).symm
    set L := Real.log |w.im|
    have hL2 : 2 < L := by
      have h := Real.log_lt_log (Real.exp_pos 2)
        (lt_of_lt_of_le RHTower.exp_two_lt_eight (by linarith : (8 : ℝ) ≤ |w.im|))
      rwa [Real.log_exp] at h
    have hL : 0 < L := by linarith
    have hsum : 2 / q.totient * ∑ χ ∈ E, ‖setCoeff S χ‖ * ‖RHTower.eulerLog χ w‖ ≤
        9 * c₀ * Real.log L + 2 / q.totient * ∑ χ ∈ E, ‖setCoeff S χ‖ * Cl' χ := by
      have h : ∑ χ ∈ E, ‖setCoeff S χ‖ * ‖RHTower.eulerLog χ w‖ ≤
          ∑ χ ∈ E, (‖setCoeff S χ‖ * (9 * Real.log L) + ‖setCoeff S χ‖ * Cl' χ) := by
        refine Finset.sum_le_sum fun χ _ => ?_
        have h1 := hCl χ w.re w.im hw hw2 ht
        rw [← hwst] at h1
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      rw [Finset.sum_add_distrib, ← Finset.sum_mul] at h
      have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 / q.totient)
      simp only [c₀]
      nlinarith
    have hpow : Real.exp (9 * c₀ * Real.log L) ≤ L ^ ⌈9 * c₀⌉₊ := by
      rw [mul_comm, ← Real.rpow_def_of_pos hL, ← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (Nat.le_ceil _)
    calc Real.exp (2 / q.totient * ∑ χ ∈ E, ‖setCoeff S χ‖ * ‖RHTower.eulerLog χ w‖)
        ≤ Real.exp (9 * c₀ * Real.log L + 2 / q.totient * ∑ χ ∈ E, ‖setCoeff S χ‖ * Cl' χ) :=
          Real.exp_le_exp.mpr hsum
      _ = Real.exp (2 / q.totient * ∑ χ ∈ E, ‖setCoeff S χ‖ * Cl' χ) *
            Real.exp (9 * c₀ * Real.log L) := by rw [Real.exp_add]; ring
      _ ≤ Real.exp (2 / q.totient * ∑ χ ∈ E, ‖setCoeff S χ‖ * Cl' χ) * L ^ ⌈9 * c₀⌉₊ :=
          mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le

/-- **The quarter law of residue flips.** For every `q ≥ 1` and every `S ⊆ ZMod q`, the half-damped
weight `f_{q,S}(d) d^{-1/2}` is paid iff more than a quarter of the unit classes are flipped:
`φ(q) < 4 #(S ∩ (ZMod q)ˣ)`. -/
theorem receiverBounded_residueFlip_half_iff_general {q : ℕ} [NeZero q] (S : Finset (ZMod q)) :
    ReceiverBounded (fun d => residueFlip q S d * (d : ℝ) ^ (-(1 / 2 : ℝ))) ↔
      q.totient < 4 * (S.filter IsUnit).card := by
  constructor
  · intro h
    by_contra h4
    exact not_receiverBounded_residueFlip_half_of_le S (not_lt.mp h4) h
  · intro h4
    obtain ⟨B, hB⟩ := exists_norm_residueFlip_le_exp S
    obtain ⟨Ml, Cl, N, hMl, hCl, hΦ⟩ := exists_exp_eulerLog_sum_le S
    obtain ⟨A, B₁, hA, hbd⟩ := exists_norm_residueFlip_bounds_of (S := S)
      (Φ := fun w => Real.exp (2 / q.totient * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        ‖setCoeff S χ‖ * ‖RHTower.eulerLog χ w‖)) (N := N)
      (fun w => (Real.exp_pos _).le) hMl hCl hB
      (fun w hw hw2 ht => (hΦ w hw hw2).1 ht) (fun w hw hw2 ht => (hΦ w hw hw2).2 ht)
    exact receiverBounded_residueFlip_half_of_bounds hA hbd h4

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
