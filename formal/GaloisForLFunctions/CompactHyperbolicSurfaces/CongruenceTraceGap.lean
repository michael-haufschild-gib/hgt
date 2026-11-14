import GaloisForLFunctions.HTGeometry.ModularCongruenceCover
import GaloisForLFunctions.CompactHyperbolicSurfaces.HyperbolicElements

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
  have hle := Int.le_of_dvd hpos (dvd_abs.mpr hdvd)
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

end GaloisForLFunctions.CompactHyperbolicSurfaces
