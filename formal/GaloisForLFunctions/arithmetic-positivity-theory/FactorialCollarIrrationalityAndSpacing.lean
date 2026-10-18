import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTailPhase
import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzTailPhaseCells

/-! Exact arithmetic collar irrationality, cubic resonance classification, and
uniform four-branch frequency separation for the factorial correction phases.

The shifted frequency `λ_N = N (1 + ε_N)` satisfies `4 λ_N^3 = N^2 (4 N + 1)`.
Because consecutive positive integer cubes cannot differ by one and `4 N` is
coprime to `4 N + 1`, every `1 + ε_N` and `λ_N` is irrational, preventing any
resonance between shifted and integer harmonics. Shifted-to-shifted resonances
are classified by the exact cubic Diophantine law `k^3 N^2 (4 N + 1) = ℓ^3 M^2 (4 M + 1)`.
Within each fixed harmonic layer `k ≥ 1`, the collar bounds `1/15 ≤ λ_N - N ≤ 1/12`
separate all four signed frequency branches `{± k N, ± k λ_N : N ≥ 1}` by at least `k / 15`. -/

open Set
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- The shifted frequency `λ_N = N (1 + ε_N)` of the factorial arithmetic collar. -/
def factorialShiftedFreq (N : ℕ) : ℝ :=
  (N : ℝ) * (1 + sourceFactorialCollar N)

/-- The collar displacement `δ_N = λ_N - N = N ε_N`. -/
def factorialCollarShift (N : ℕ) : ℝ :=
  (N : ℝ) * sourceFactorialCollar N

theorem factorialShiftedFreq_eq_add_shift (N : ℕ) :
    factorialShiftedFreq N = (N : ℝ) + factorialCollarShift N := by
  unfold factorialShiftedFreq factorialCollarShift
  ring

theorem factorialShiftedFreq_pos {N : ℕ} (hN : 1 ≤ N) :
    0 < factorialShiftedFreq N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hε : 0 < sourceFactorialCollar N := sourceFactorialCollar_pos hN
  unfold factorialShiftedFreq
  positivity

/-- Exact cubic relation `(1 + ε_N)^3 = (4 N + 1) / (4 N)` for `N ≥ 1`. -/
theorem one_add_sourceFactorialCollar_cube {N : ℕ} (hN : 1 ≤ N) :
    (1 + sourceFactorialCollar N) ^ 3 = (4 * (N : ℝ) + 1) / (4 * (N : ℝ)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc : (1 + sourceFactorialCollar N) ^ 3 = 1 + 1 / (4 * (N : ℝ)) := by
    rw [← exp_three_sourceFactorialWidth N]
    unfold sourceFactorialCollar
    rw [show 1 + (Real.exp (sourceFactorialWidth N) - 1) = Real.exp (sourceFactorialWidth N) by ring,
      show 3 * sourceFactorialWidth N =
        sourceFactorialWidth N + sourceFactorialWidth N + sourceFactorialWidth N by ring,
      Real.exp_add, Real.exp_add]
    ring
  rw [hc]
  field_simp

/-- Exact polynomial identity `4 λ_N^3 = N^2 (4 N + 1)` for `N ≥ 1`. -/
theorem four_mul_factorialShiftedFreq_cube {N : ℕ} (hN : 1 ≤ N) :
    4 * (factorialShiftedFreq N) ^ 3 = (N : ℝ) ^ 2 * (4 * (N : ℝ) + 1) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  unfold factorialShiftedFreq
  rw [mul_pow, one_add_sourceFactorialCollar_cube hN]
  field_simp

/-- Two positive integers cannot have cubes differing by one: `(b + 1)^3 - b^3 = 3 b^2 + 3 b + 1 > 1`. -/
theorem cube_ne_cube_add_one_of_pos {a b : ℕ} (hb : 1 ≤ b) :
    a ^ 3 ≠ b ^ 3 + 1 := by
  intro h
  rcases lt_trichotomy a (b + 1) with hlt | rfl | hgt
  · have hle : a ≤ b := Nat.lt_succ_iff.mp hlt
    have hpow : a ^ 3 ≤ b ^ 3 := Nat.pow_le_pow_left hle 3
    omega
  · nlinarith [hb]
  · have hge : b + 2 ≤ a := hgt
    have hpow : (b + 2) ^ 3 ≤ a ^ 3 := Nat.pow_le_pow_left hge 3
    nlinarith [hb]

/-- No rational number `q` has cube `(4 N + 1) / (4 N)` for `N ≥ 1`. -/
theorem rat_cube_ne_four_mul_add_one_div {N : ℕ} (hN : 1 ≤ N) (q : ℚ) :
    (q : ℝ) ^ 3 ≠ (4 * (N : ℝ) + 1) / (4 * (N : ℝ)) := by
  intro hq
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hqpos3 : (0 : ℝ) < (q : ℝ) ^ 3 := by
    rw [hq]
    positivity
  have hqposR : (0 : ℝ) < (q : ℝ) := by
    by_contra hnot
    have hle : (q : ℝ) ≤ 0 := not_lt.mp hnot
    have : (q : ℝ) ^ 3 ≤ 0 := by nlinarith [sq_nonneg (q : ℝ)]
    linarith
  have hqpos : 0 < q := by exact_mod_cast hqposR
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hqpos
  let a : ℕ := q.num.natAbs
  let b : ℕ := q.den
  have ha_int : q.num = (a : ℤ) := (Int.natAbs_of_nonneg hnum_pos.le).symm
  have ha_eq : (q.num : ℝ) = (a : ℝ) := by exact_mod_cast ha_int
  have hb_pos : 1 ≤ b := Nat.succ_le_of_lt q.den_pos
  have hq_cast : (q : ℝ) = (a : ℝ) / (b : ℝ) := by
    rw [← Rat.num_div_den q, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, ha_eq]
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
  have hrelR : (a : ℝ) ^ 3 * (4 * (N : ℝ)) = (b : ℝ) ^ 3 * (4 * (N : ℝ) + 1) := by
    rw [hq_cast, div_pow] at hq
    have h1 := (div_eq_iff (pow_ne_zero 3 hbR)).mp hq
    calc
      (a : ℝ) ^ 3 * (4 * (N : ℝ)) =
          ((4 * (N : ℝ) + 1) / (4 * (N : ℝ)) * (b : ℝ) ^ 3) * (4 * (N : ℝ)) :=
        congrArg (· * (4 * (N : ℝ))) h1
      _ = (b : ℝ) ^ 3 * (4 * (N : ℝ) + 1) := by field_simp
  have hrel : a ^ 3 * (4 * N) = b ^ 3 * (4 * N + 1) := by exact_mod_cast hrelR
  have hcop_ab : Nat.Coprime a b := q.reduced
  have hcop_a3b3 : Nat.Coprime (a ^ 3) (b ^ 3) := hcop_ab.pow 3 3
  have hdvd_b3 : b ^ 3 ∣ 4 * N := by
    refine hcop_a3b3.symm.dvd_of_dvd_mul_left ?_
    exact ⟨4 * N + 1, hrel⟩
  have hcop_N : Nat.Coprime (4 * N) (4 * N + 1) :=
    Nat.coprime_self_add_right.mpr (Nat.coprime_one_right (4 * N))
  have hdvd_4N : 4 * N ∣ b ^ 3 := by
    refine hcop_N.dvd_of_dvd_mul_left ?_
    have hcomm : (4 * N + 1) * b ^ 3 = (4 * N) * a ^ 3 := by linarith [hrel]
    rw [hcomm]
    exact dvd_mul_right (4 * N) (a ^ 3)
  have hb3_eq : b ^ 3 = 4 * N := Nat.dvd_antisymm hdvd_b3 hdvd_4N
  have ha3_eq : a ^ 3 = b ^ 3 + 1 := by
    nlinarith [hrel, hb3_eq, hN]
  exact cube_ne_cube_add_one_of_pos hb_pos ha3_eq

/-- The collar dilation factor `1 + ε_N` is irrational for every `N ≥ 1`. -/
theorem irrational_one_add_sourceFactorialCollar {N : ℕ} (hN : 1 ≤ N) :
    Irrational (1 + sourceFactorialCollar N) := by
  rintro ⟨q, hq⟩
  apply rat_cube_ne_four_mul_add_one_div hN q
  rw [hq, one_add_sourceFactorialCollar_cube hN]

/-- The shifted frequency `λ_N = N (1 + ε_N)` is irrational for every `N ≥ 1`. -/
theorem irrational_factorialShiftedFreq {N : ℕ} (hN : 1 ≤ N) :
    Irrational (factorialShiftedFreq N) := by
  rintro ⟨q, hq⟩
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  apply irrational_one_add_sourceFactorialCollar hN
  refine ⟨q / (N : ℚ), ?_⟩
  rw [Rat.cast_div, Rat.cast_natCast, hq]
  unfold factorialShiftedFreq
  exact mul_div_cancel_left₀ _ hNR

/-- No positive integer harmonic of `λ_N` can equal any rational or integer frequency. -/
theorem mul_factorialShiftedFreq_ne_mul_nat {k m N M : ℕ} (hk : 1 ≤ k) (hN : 1 ≤ N) :
    (k : ℝ) * factorialShiftedFreq N ≠ (m : ℝ) * (M : ℝ) := by
  intro h
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  apply irrational_factorialShiftedFreq hN
  refine ⟨((m * M : ℕ) : ℚ) / (k : ℚ), ?_⟩
  rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast, Nat.cast_mul, ← h]
  exact mul_div_cancel_left₀ _ hkR

/-- Exact cubic Diophantine classification of resonances between two shifted harmonics `k λ_N` and `ℓ λ_M`. -/
theorem mul_factorialShiftedFreq_eq_iff {k ℓ N M : ℕ}
    (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) (hN : 1 ≤ N) (hM : 1 ≤ M) :
    (k : ℝ) * factorialShiftedFreq N = (ℓ : ℝ) * factorialShiftedFreq M ↔
      k ^ 3 * N ^ 2 * (4 * N + 1) = ℓ ^ 3 * M ^ 2 * (4 * M + 1) := by
  have hposL : 0 ≤ (k : ℝ) * factorialShiftedFreq N := by
    have := factorialShiftedFreq_pos hN
    positivity
  have hposR : 0 ≤ (ℓ : ℝ) * factorialShiftedFreq M := by
    have := factorialShiftedFreq_pos hM
    positivity
  constructor
  · intro h
    have h3 : 4 * ((k : ℝ) * factorialShiftedFreq N) ^ 3 =
        4 * ((ℓ : ℝ) * factorialShiftedFreq M) ^ 3 := by rw [h]
    have hL : 4 * ((k : ℝ) * factorialShiftedFreq N) ^ 3 =
        (k : ℝ) ^ 3 * ((N : ℝ) ^ 2 * (4 * (N : ℝ) + 1)) := by
      calc
        4 * ((k : ℝ) * factorialShiftedFreq N) ^ 3 =
            (k : ℝ) ^ 3 * (4 * (factorialShiftedFreq N) ^ 3) := by ring
        _ = (k : ℝ) ^ 3 * ((N : ℝ) ^ 2 * (4 * (N : ℝ) + 1)) := by
          rw [four_mul_factorialShiftedFreq_cube hN]
    have hR : 4 * ((ℓ : ℝ) * factorialShiftedFreq M) ^ 3 =
        (ℓ : ℝ) ^ 3 * ((M : ℝ) ^ 2 * (4 * (M : ℝ) + 1)) := by
      calc
        4 * ((ℓ : ℝ) * factorialShiftedFreq M) ^ 3 =
            (ℓ : ℝ) ^ 3 * (4 * (factorialShiftedFreq M) ^ 3) := by ring
        _ = (ℓ : ℝ) ^ 3 * ((M : ℝ) ^ 2 * (4 * (M : ℝ) + 1)) := by
          rw [four_mul_factorialShiftedFreq_cube hM]
    rw [hL, hR] at h3
    exact_mod_cast (show (k : ℝ) ^ 3 * (N : ℝ) ^ 2 * (4 * (N : ℝ) + 1) =
      (ℓ : ℝ) ^ 3 * (M : ℝ) ^ 2 * (4 * (M : ℝ) + 1) by linarith [h3])
  · intro hnat
    have hR : (k : ℝ) ^ 3 * ((N : ℝ) ^ 2 * (4 * (N : ℝ) + 1)) =
        (ℓ : ℝ) ^ 3 * ((M : ℝ) ^ 2 * (4 * (M : ℝ) + 1)) := by
      have hcast : ((k ^ 3 * N ^ 2 * (4 * N + 1) : ℕ) : ℝ) =
          ((ℓ ^ 3 * M ^ 2 * (4 * M + 1) : ℕ) : ℝ) := congrArg Nat.cast hnat
      push_cast at hcast
      linarith
    have hcube : ((k : ℝ) * factorialShiftedFreq N) ^ 3 =
        ((ℓ : ℝ) * factorialShiftedFreq M) ^ 3 := by
      have h4 : 4 * ((k : ℝ) * factorialShiftedFreq N) ^ 3 =
          4 * ((ℓ : ℝ) * factorialShiftedFreq M) ^ 3 := by
        calc
          4 * ((k : ℝ) * factorialShiftedFreq N) ^ 3 =
              (k : ℝ) ^ 3 * (4 * (factorialShiftedFreq N) ^ 3) := by ring
          _ = (k : ℝ) ^ 3 * ((N : ℝ) ^ 2 * (4 * (N : ℝ) + 1)) := by
            rw [four_mul_factorialShiftedFreq_cube hN]
          _ = (ℓ : ℝ) ^ 3 * ((M : ℝ) ^ 2 * (4 * (M : ℝ) + 1)) := hR
          _ = (ℓ : ℝ) ^ 3 * (4 * (factorialShiftedFreq M) ^ 3) := by
            rw [four_mul_factorialShiftedFreq_cube hM]
          _ = 4 * ((ℓ : ℝ) * factorialShiftedFreq M) ^ 3 := by ring
      linarith
    have hdiff : ((k : ℝ) * factorialShiftedFreq N - (ℓ : ℝ) * factorialShiftedFreq M) *
        (((k : ℝ) * factorialShiftedFreq N) ^ 2 +
          ((k : ℝ) * factorialShiftedFreq N) * ((ℓ : ℝ) * factorialShiftedFreq M) +
          ((ℓ : ℝ) * factorialShiftedFreq M) ^ 2) = 0 := by
      linarith [hcube]
    rcases mul_eq_zero.mp hdiff with hsub | hquad
    · linarith
    · have hposL' : 0 < (k : ℝ) * factorialShiftedFreq N :=
        mul_pos (by exact_mod_cast (show 0 < k by omega)) (factorialShiftedFreq_pos hN)
      nlinarith [sq_nonneg ((k : ℝ) * factorialShiftedFreq N),
        sq_nonneg ((ℓ : ℝ) * factorialShiftedFreq M), mul_nonneg hposL hposR]

/-- Uniform two-sided collar bounds `1/15 ≤ δ_N = λ_N - N ≤ 1/12` for all `N ≥ 1`. -/
theorem factorialCollarShift_bounds {N : ℕ} (hN : 1 ≤ N) :
    (1 / 15 : ℝ) ≤ factorialCollarShift N ∧ factorialCollarShift N ≤ 1 / 12 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlo := (sourceFactorialWidth_bounds hN).1.trans (sourceFactorialWidth_le_collar N)
  have hlo' : (1 / 15 : ℝ) ≤ (N : ℝ) * sourceFactorialCollar N := by
    have h := mul_le_mul_of_nonneg_left hlo hNp.le
    calc
      (1 / 15 : ℝ) = (N : ℝ) * (1 / (15 * (N : ℝ))) := by field_simp
      _ ≤ (N : ℝ) * sourceFactorialCollar N := h
  exact ⟨hlo', sourceFactorialCollar_scaled_le_twelfth hN⟩

theorem factorialShiftedFreq_sub_self_bounds {N : ℕ} (hN : 1 ≤ N) :
    (1 / 15 : ℝ) ≤ factorialShiftedFreq N - (N : ℝ) ∧
      factorialShiftedFreq N - (N : ℝ) ≤ 1 / 12 := by
  rw [factorialShiftedFreq_eq_add_shift, add_sub_cancel_left]
  exact factorialCollarShift_bounds hN

/-- Uniform dilation separation `m λ_N - λ_{m N} ≥ 1/20` for all `m ≥ 2` and `N ≥ 1`. -/
theorem mul_factorialShiftedFreq_sub_dilation_ge {m N : ℕ} (hm : 2 ≤ m) (hN : 1 ≤ N) :
    (1 / 20 : ℝ) ≤ (m : ℝ) * factorialShiftedFreq N - factorialShiftedFreq (m * N) := by
  have hmN : 1 ≤ m * N := Nat.mul_pos (by omega) (by omega)
  obtain ⟨hloN, _⟩ := factorialCollarShift_bounds hN
  obtain ⟨_, hhiMN⟩ := factorialCollarShift_bounds hmN
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  rw [factorialShiftedFreq_eq_add_shift N, factorialShiftedFreq_eq_add_shift (m * N)]
  push_cast
  have h1 : (2 / 15 : ℝ) ≤ (m : ℝ) * factorialCollarShift N := by nlinarith
  linarith

/-- Positive base frequency at scale index `n` (`N = n + 1`) and parity branch `j`:
`N` when `j % 2 = 0` and `λ_N` when `j % 2 = 1`. -/
def factorialBaseBranchFreq (n : ℕ) (j : Fin 4) : ℝ :=
  if j.val % 2 = 0 then ((n + 1 : ℕ) : ℝ) else factorialShiftedFreq (n + 1)

/-- The four signed frequency branches at harmonic `k ≥ 1` and scale index `n` (`N = n + 1`). -/
def factorialHarmonicBranchFreq (k : ℕ) (idx : ℕ × Fin 4) : ℝ :=
  (k : ℝ) * (if idx.2.val < 2 then factorialBaseBranchFreq idx.1 idx.2
    else -factorialBaseBranchFreq idx.1 idx.2)

theorem factorialBaseBranchFreq_ge_one (n : ℕ) (j : Fin 4) :
    (1 : ℝ) ≤ factorialBaseBranchFreq n j := by
  have hN : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  obtain ⟨hlo, _⟩ := factorialShiftedFreq_sub_self_bounds (N := n + 1) (by omega)
  unfold factorialBaseBranchFreq
  split_ifs <;> linarith

private theorem pos_branch_gap {n m : ℕ} {j₁ j₂ : Fin 4}
    (hne : n ≠ m ∨ j₁.val % 2 ≠ j₂.val % 2) :
    (1 / 15 : ℝ) ≤ |factorialBaseBranchFreq n j₁ - factorialBaseBranchFreq m j₂| := by
  obtain ⟨hlo_n, hhi_n⟩ := factorialShiftedFreq_sub_self_bounds (N := n + 1) (by omega)
  obtain ⟨hlo_m, hhi_m⟩ := factorialShiftedFreq_sub_self_bounds (N := m + 1) (by omega)
  unfold factorialBaseBranchFreq
  rcases lt_trichotomy n m with hlt | rfl | hgt
  · have hnm : ((n + 1 : ℕ) : ℝ) + 1 ≤ ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show n + 2 ≤ m + 1 by omega)
    have hle : (if j₁.val % 2 = 0 then ((n + 1 : ℕ) : ℝ) else factorialShiftedFreq (n + 1)) +
        1 / 15 ≤
        (if j₂.val % 2 = 0 then ((m + 1 : ℕ) : ℝ) else factorialShiftedFreq (m + 1)) := by
      split_ifs <;> linarith
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hmod : j₁.val % 2 ≠ j₂.val % 2 := hne.resolve_left (not_not.mpr rfl)
    by_cases h1 : j₁.val % 2 = 0
    · have h2 : j₂.val % 2 ≠ 0 := fun h => hmod (h1.trans h.symm)
      rw [if_pos h1, if_neg h2, abs_of_nonpos (by linarith)]
      linarith
    · have h2 : j₂.val % 2 = 0 := by omega
      rw [if_neg h1, if_pos h2, abs_of_nonneg (by linarith)]
      linarith
  · have hmn : ((m + 1 : ℕ) : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show m + 2 ≤ n + 1 by omega)
    have hle : (if j₂.val % 2 = 0 then ((m + 1 : ℕ) : ℝ) else factorialShiftedFreq (m + 1)) +
        1 / 15 ≤
        (if j₁.val % 2 = 0 then ((n + 1 : ℕ) : ℝ) else factorialShiftedFreq (n + 1)) := by
      split_ifs <;> linarith
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- All four signed frequency branches `{± k N, ± k λ_N : N ≥ 1}` at harmonic `k ≥ 1`
are pairwise separated by at least `k / 15`. -/
theorem four_branch_harmonic_freq_gap_ge (k : ℕ) {u v : ℕ × Fin 4} (huv : u ≠ v) :
    (k : ℝ) / 15 ≤ |factorialHarmonicBranchFreq k u - factorialHarmonicBranchFreq k v| := by
  rcases eq_zero_or_pos k with rfl | hk
  · simp
  have hkR : (0 : ℝ) ≤ k := by positivity
  unfold factorialHarmonicBranchFreq
  rw [← mul_sub, abs_mul, abs_of_nonneg hkR, div_eq_mul_one_div]
  refine mul_le_mul_of_nonneg_left ?_ hkR
  by_cases hsign : (u.2.val < 2) = (v.2.val < 2)
  · have hne2 : u.1 ≠ v.1 ∨ u.2.val % 2 ≠ v.2.val % 2 := by
      by_contra hnot
      push Not at hnot
      apply huv
      rcases u with ⟨n, ⟨j₁, hj₁⟩⟩
      rcases v with ⟨m, ⟨j₂, hj₂⟩⟩
      rcases hnot with ⟨rfl, hmod⟩
      ext
      · rfl
      · dsimp at hsign hmod ⊢
        have hiff : j₁ < 2 ↔ j₂ < 2 := Eq.to_iff hsign
        omega
    have hgap := pos_branch_gap hne2
    by_cases hu2 : u.2.val < 2
    · have hv2 : v.2.val < 2 := hsign ▸ hu2
      rw [if_pos hu2, if_pos hv2]
      exact hgap
    · have hv2 : ¬ v.2.val < 2 := hsign ▸ hu2
      rw [if_neg hu2, if_neg hv2,
        show -factorialBaseBranchFreq u.1 u.2 - -factorialBaseBranchFreq v.1 v.2 =
          -(factorialBaseBranchFreq u.1 u.2 - factorialBaseBranchFreq v.1 v.2) by ring,
        abs_neg]
      exact hgap
  · have hu1 := factorialBaseBranchFreq_ge_one u.1 u.2
    have hv1 := factorialBaseBranchFreq_ge_one v.1 v.2
    by_cases hu2 : u.2.val < 2
    · have hv2 : ¬ v.2.val < 2 := by
        intro hv2
        exact hsign (by simp [hu2, hv2])
      rw [if_pos hu2, if_neg hv2, sub_neg_eq_add, abs_of_nonneg (by linarith)]
      linarith
    · have hv2 : v.2.val < 2 := by
        by_contra hv2
        exact hsign (by simp [hu2, hv2])
      rw [if_neg hu2, if_pos hv2, abs_of_nonpos (by linarith)]
      linarith

end

end GaloisForLFunctions.ArithmeticPositivityTheory
