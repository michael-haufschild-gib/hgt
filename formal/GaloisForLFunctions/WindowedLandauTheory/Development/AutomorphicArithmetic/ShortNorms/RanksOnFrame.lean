import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameCyclicGenerator

/-! Rank parameters on a given frame at the prescribed scale. -/

open WindowedLandauTheory.BasicNotions WindowedLandauTheory.BasicNotions.LevelStarExponents WindowedLandauTheory.MainNotions WindowedLandauTheory.MainNotions.Inhab NumberField

namespace GlobalTheory.EX

private theorem exists_even_between (A : ℝ) (hA : 2 ≤ A) : ∃ m : ℕ, Even m ∧ A ≤ m ∧ (m : ℝ) ≤ 2 * A := by
  refine ⟨2 * ⌈A / 2⌉₊, even_two_mul _, ?_, ?_⟩
  · have := Nat.le_ceil (A / 2)
    push_cast; linarith
  · have := Nat.ceil_lt_add_one (a := A / 2) (by linarith)
    push_cast; linarith

private theorem exists_ranks_of_frame (φ : WindowedLandauTheory.HC.Frame) (k m T W : ℕ) (hk : Even k) (hm : Even m) (h2 : 2 ≤ m) (h3 : m + 3 ≤ k)
    (hmf : m ≤ 2 * φ.ord) (hfk : 2 * φ.ord ≤ k) :
    ∃ R : Ranks, R.toFrame = φ ∧ R.k = k ∧ R.m = m ∧ R.r + R.t = 8 * R.f * R.r + 4 + T * (8 * W) := by
  obtain ⟨r, hr⟩ : ∃ r, r = k + m - 1 := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f, f = 2 * φ.ord := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, p = f * r := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = T * W := ⟨_, rfl⟩
  have hpr : r ≤ p := by
    rw [hp, hf]
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (by norm_num) φ.ord_pos)
  obtain ⟨k', hk'⟩ := hk
  obtain ⟨m', hm'⟩ := hm
  have hmt : m ≤ 8 * p + 4 + 8 * q - r + 1 := by omega
  refine ⟨⟨φ, k, m, 8 * p + 4 + 8 * q - r, ⟨k', hk'⟩, ⟨m', hm'⟩, ?_, h2, h3, by omega, by omega, hmf, hfk, ?_⟩,
    rfl, rfl, rfl, ?_⟩
  · rw [Nat.odd_iff]; omega
  · rw [sq]
    exact (Nat.mul_le_mul_left m hmt).trans (Nat.le_add_left _ _)
  · show (k + m - 1) + (8 * p + 4 + 8 * q - r) = 8 * (2 * φ.ord) * (k + m - 1) + 4 + T * (8 * W)
    rw [← hr, ← hf, mul_assoc 8 f r, ← hp, mul_left_comm T 8 W, ← hq]
    omega

theorem exists_ranks_rankVal_frame : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ s : Scale, s.eps = eps → x0 ≤ s.x →
    ∀ φ : WindowedLandauTheory.HC.Frame, s.x ^ (2 + 8 * s.eps) ≤ (φ.ord : ℝ) → (φ.ord : ℝ) ≤ 2 * s.x ^ (2 + 8 * s.eps) →
      ∃ R : Ranks, R.toFrame = φ ∧ RankVal s R := by
  intro eps h0 h1
  refine ⟨16, fun s hs hx φ he1 hp2 => ?_⟩
  subst hs
  have hx1 : (1 : ℝ) ≤ s.x := by linarith
  have hx0 : (0 : ℝ) < s.x := by linarith
  have hH1 : s.x ^ 2 ≤ s.x ^ (2 + 8 * s.eps) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have hH2 : s.x ^ (2 + 8 * s.eps) ≤ s.x ^ 3 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have he2 : (φ.ord : ℝ) ≤ 2 * s.x ^ 3 := by linarith
  have hB : s.x ^ 4 ≤ s.x ^ (9 / 2 + 10 * s.eps) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have hd : s.x * s.delta1 = s.x ^ (1 - s.eps / 8) := by
    unfold Scale.delta1
    rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]
  have hA1 : 2 ≤ Real.sqrt (s.x * s.delta1) := by
    apply Real.le_sqrt_of_sq_le
    rw [hd]
    have h1 : s.x ^ (1 / 2 : ℝ) ≤ s.x ^ (1 - s.eps / 8) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h2 : (4 : ℝ) ≤ s.x ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      apply Real.le_sqrt_of_sq_le
      linarith
    linarith
  have hA2 : Real.sqrt (s.x * s.delta1) ≤ s.x := by
    rw [Real.sqrt_le_left hx0.le, hd, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have hmul (j : ℕ) : 16 * s.x ^ j ≤ s.x ^ (j + 1) := by
    rw [pow_succ, mul_comm (s.x ^ j)]
    exact mul_le_mul_of_nonneg_right hx (by positivity)
  have p2 : 16 * s.x ≤ s.x ^ 2 := by simpa using hmul 1
  have p3 := hmul 2
  have p4 := hmul 3
  norm_num only at p3 p4
  obtain ⟨m, hm, hm1, hm2⟩ := exists_even_between _ hA1
  obtain ⟨k, hk, hk1, hk2⟩ := exists_even_between (s.x ^ (9 / 2 + 10 * s.eps)) (by linarith)
  have a1 : 2 ≤ m := by
    have : ((2 : ℕ) : ℝ) ≤ m := by push_cast; linarith
    exact_mod_cast this
  have a2 : m + 3 ≤ k := by
    have : (m : ℝ) + 3 ≤ k := by linarith
    exact_mod_cast this
  have a3 : m ≤ 2 * φ.ord := by
    have : (m : ℝ) ≤ 2 * (φ.ord : ℝ) := by linarith
    exact_mod_cast this
  have a4 : 2 * φ.ord ≤ k := by
    have : 2 * (φ.ord : ℝ) ≤ k := by linarith
    exact_mod_cast this
  obtain ⟨R, rfl, rfl, rfl, hR⟩ := exists_ranks_of_frame φ k m (TOv s)
    ⌈10 * ((k + m - 1 : ℕ) : ℝ) * (((2 * φ.ord : ℕ) : ℝ) +
      ((2 * φ.ord : ℕ) : ℝ) ^ 2 * ((k : ℝ) - 1) ^ 3 * s.L ^ 2 / m) / 8⌉₊ hk hm a1 a2 a3 a4
  exact ⟨R, rfl, ⟨he1, hp2⟩, ⟨hm1, hm2⟩, ⟨hk1, hk2⟩, hR⟩

end GlobalTheory.EX
