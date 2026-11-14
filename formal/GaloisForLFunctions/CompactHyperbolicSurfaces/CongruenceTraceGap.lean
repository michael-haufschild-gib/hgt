import GaloisForLFunctions.HTGeometry.ModularCongruenceCover
import GaloisForLFunctions.CompactHyperbolicSurfaces.HyperbolicElements
import GaloisForLFunctions.CompactHyperbolicSurfaces.QuaternionGroup

/-!
# The sharp trace gap in a principal congruence subgroup

Writing `A = 1 + nB` in the determinant identity gives
`tr A - 2 = -n² det B`. Thus every trace other than `2` has absolute value
at least `n² - 2`. The product of the two opposite cusp parabolics attains
this bound for `n ≥ 3`.

This is the arithmetic mechanism behind the systolic scale in
Gaster–Martínez-Granado–Simon, *Simple Length Multiplicity on X(n)*,
§2; the parabolic product is the matrix identity in Lemma 2.2(i).
-/

open Matrix CongruenceSubgroup
open scoped MatrixGroups

namespace GaloisForLFunctions.CompactHyperbolicSurfaces
open HTGeometry

/-- The determinant improves trace congruence from level `n` to level `n²`. -/
theorem congruence_sq_dvd_trace_sub_two (n : ℕ) (A : Gamma n) :
    (n : ℤ) ^ 2 ∣ slTrace A.val - 2 := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩⟩ := gamma_dvd A.property
  have hdet := sl_det A.val
  have haa : A.val 0 0 = 1 + n * a := by linarith only [ha]
  have hdd : A.val 1 1 = 1 + n * d := by linarith only [hd]
  refine ⟨b * c - a * d, ?_⟩
  dsimp only [slTrace]
  rw [haa, hdd, hb, hc] at hdet
  rw [haa, hdd]
  linear_combination hdet

/-- Trace `2` is isolated from all other traces by the squared congruence level. -/
theorem congruence_trace_gap (n : ℕ) (A : Gamma n) :
    slTrace A.val = 2 ∨ (n : ℤ) ^ 2 - 2 ≤ |slTrace A.val| := by
  by_cases h : slTrace A.val = 2
  · exact Or.inl h
  right
  have hdvd := congruence_sq_dvd_trace_sub_two n A
  have hpos : 0 < |slTrace A.val - 2| := abs_pos.mpr (sub_ne_zero.mpr h)
  have hdabs : (n : ℤ) ^ 2 ∣ |slTrace A.val - 2| := by
    obtain ⟨m, hm⟩ := hdvd
    exact ⟨|m|, by rw [hm, abs_mul, abs_of_nonneg (sq_nonneg _)]⟩
  have hle := Int.le_of_dvd hpos hdabs
  have htri := abs_sub (slTrace A.val) 2
  norm_num only [abs_ofNat] at htri
  linarith only [hle, htri]

/-- Holonomy of two opposite cusp parabolics with common area parameter `n`. -/
def cuspPair (n : ℤ) : SL(2, ℤ) :=
  ⟨!![1 - n ^ 2, n; -n, 1], by rw [Matrix.det_fin_two_of]; ring⟩

/-- The parabolic product belongs to the principal congruence group. -/
theorem cuspPair_mem (n : ℕ) : cuspPair n ∈ Gamma n := by
  apply Gamma_mem.mpr
  simp [cuspPair]

@[simp] theorem slTrace_cuspPair (n : ℤ) : slTrace (cuspPair n) = 2 - n ^ 2 := by
  simp only [slTrace, cuspPair, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- Every level at least three realizes the smallest possible nonparabolic absolute trace. -/
theorem congruence_trace_gap_attained (k : ℕ) :
    ∃ A : Gamma (k + 3),
      2 < |slTrace A.val| ∧ |slTrace A.val| = ((k + 3 : ℕ) : ℤ) ^ 2 - 2 := by
  refine ⟨⟨cuspPair (k + 3 : ℕ), cuspPair_mem (k + 3)⟩, ?_⟩
  have hn : (3 : ℤ) ≤ (k + 3 : ℕ) := by exact_mod_cast (Nat.le_add_left 3 k)
  have hs : (4 : ℤ) < ((k + 3 : ℕ) : ℤ) ^ 2 := by nlinarith only [hn]
  rw [slTrace_cuspPair, abs_of_neg (by linarith only [hs])]
  constructor <;> linarith only [hs]

/-- The sharp minimum over all hyperbolic absolute traces at level `k+3`. -/
theorem congruence_trace_minimum (k : ℕ) :
    IsLeast {t : ℤ | ∃ A : Gamma (k + 3), 2 < |slTrace A.val| ∧ t = |slTrace A.val|}
      (((k + 3 : ℕ) : ℤ) ^ 2 - 2) := by
  constructor
  · obtain ⟨A, hA, ht⟩ := congruence_trace_gap_attained k
    exact ⟨A, hA, ht.symm⟩
  · rintro t ⟨A, hA, rfl⟩
    rcases congruence_trace_gap (k + 3) A with h | h
    · rw [h] at hA
      norm_num at hA
    · exact h

/-- Integer matrices embedded in the existing real hyperbolic-length model. -/
noncomputable def realCongruenceMatrix (A : SL(2, ℤ)) : SL(2, ℝ) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A

theorem trSL_realCongruenceMatrix (A : SL(2, ℤ)) :
    trSL (realCongruenceMatrix A) = (slTrace A : ℝ) := by
  simp [realCongruenceMatrix, trSL, slTrace, Matrix.SpecialLinearGroup.map]

/-- Exact minimum translation length among hyperbolic elements of the principal congruence group. -/
theorem congruence_length_minimum (k : ℕ) :
    IsLeast {l : ℝ | ∃ A : Gamma (k + 3),
      2 < |slTrace A.val| ∧ l = hypLen (realCongruenceMatrix A.val)}
      (2 * Real.arcosh ((((k + 3 : ℕ) : ℝ) ^ 2 - 2) / 2)) := by
  have hn : (3 : ℝ) ≤ (k + 3 : ℕ) := by exact_mod_cast (Nat.le_add_left 3 k)
  have hbase : 0 < (((k + 3 : ℕ) : ℝ) ^ 2 - 2) / 2 := by nlinarith only [hn]
  constructor
  · obtain ⟨A, hA, ht⟩ := congruence_trace_gap_attained k
    refine ⟨A, hA, ?_⟩
    unfold hypLen
    rw [trSL_realCongruenceMatrix, ← Int.cast_abs]
    have ht' : (|slTrace A.val| : ℝ) = ((k + 3 : ℕ) : ℝ) ^ 2 - 2 := by exact_mod_cast ht
    rw [ht']
  · rintro l ⟨A, hA, rfl⟩
    have ht := (congruence_trace_minimum k).2 ⟨A, hA, rfl⟩
    have ht' : ((k + 3 : ℕ) : ℝ) ^ 2 - 2 ≤ (|slTrace A.val| : ℝ) := by exact_mod_cast ht
    have hpos : 0 < (|slTrace A.val| : ℝ) / 2 := by
      have : (2 : ℝ) < (|slTrace A.val| : ℝ) := by exact_mod_cast hA
      linarith only [this]
    unfold hypLen
    rw [trSL_realCongruenceMatrix, ← Int.cast_abs]
    have hmono := (Real.arcosh_le_arcosh hbase hpos).mpr (by linarith only [ht'])
    linarith only [hmono]

/-- The same squared-level quantization holds for the quaternion order's compact quotients. -/
theorem quaternion_congruence_trace_quantized (n : ℕ) (A : congGroup n) :
    ∃ m : ℤ, trSL A.val = 2 + (n : ℝ) ^ 2 * m := by
  obtain ⟨x, hnorm, ⟨u, rfl⟩, hmat⟩ := A.property
  have htrace : trSL A.val = 2 * ((quatOne + (n : ℤ) • u) 0 : ℝ) := by
    change ((A.val : Matrix (Fin 2) (Fin 2) ℝ) 0 0) + A.val 1 1 = _
    rw [hmat]
    simp only [quatMat_apply, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  have hnorm' : 2 * (n : ℤ) * u 0 + (n : ℤ) ^ 2 * nrd u = 0 := by
    simp only [nrd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, quatOne,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.cons_val_fin_one,
      zero_add] at hnorm ⊢
    linear_combination hnorm
  refine ⟨-nrd u, ?_⟩
  rw [htrace]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, quatOne,
    Matrix.cons_val_zero, Int.cast_add, Int.cast_one, Int.cast_mul, Int.cast_natCast,
    Int.cast_neg]
  have he : 2 * (n : ℝ) * u 0 + (n : ℝ) ^ 2 * (nrd u : ℝ) = 0 := by exact_mod_cast hnorm'
  linarith only [he]

#print axioms congruence_sq_dvd_trace_sub_two
#print axioms congruence_trace_gap
#print axioms congruence_trace_minimum
#print axioms congruence_length_minimum
#print axioms quaternion_congruence_trace_quantized

end GaloisForLFunctions.CompactHyperbolicSurfaces
