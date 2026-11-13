import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ZMod.Basic

/-!
# An order in the quaternion algebra `(2, 3)_ℚ` inside `M₂(ℝ)`

`B = (2, 3)_ℚ` has basis `1, i, j, ij` with `i² = 2`, `j² = 3`, `ij = −ji`.  The order
`O = ℤ⟨1, i, j, ij⟩` (coordinates `x : Fin 4 → ℤ`) embeds in `M₂(ℝ)` by `i ↦ diag(√2, −√2)`,
`j ↦ [[0, 3], [1, 0]]`:

  `x ↦ [[x₀ + x₁√2, 3(x₂ + x₃√2)], [x₂ − x₃√2, x₀ − x₁√2]]` (`quatMat`),

with reduced norm `nrd x = det = x₀² − 2x₁² − 3x₂² + 6x₃²`.

* `quatMat_mul`, `adjugate_quatMat`: the embedding is multiplicative and conjugation is the
  adjugate.
* `eq_zero_of_nrd_eq_zero`: the norm form is anisotropic, so `B` is a division algebra (descent:
  squares mod 3 force every coordinate to be divisible by 3).
* `quatCoeff_quatMatR`: the coordinates are linear functions of the matrix entries.
-/

open Matrix

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

noncomputable section

/-- The real embedding `v ↦ [[v₀ + v₁√2, 3(v₂ + v₃√2)], [v₂ − v₃√2, v₀ − v₁√2]]`. -/
def quatMatR (v : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![v 0 + v 1 * √2, 3 * (v 2 + v 3 * √2); v 2 - v 3 * √2, v 0 - v 1 * √2]

/-- The embedding of the order `O`. -/
def quatMat (x : Fin 4 → ℤ) : Matrix (Fin 2) (Fin 2) ℝ := quatMatR fun k => (x k : ℝ)

/-- The reduced norm `x₀² − 2x₁² − 3x₂² + 6x₃²`. -/
def nrd (x : Fin 4 → ℤ) : ℤ := x 0 ^ 2 - 2 * x 1 ^ 2 - 3 * x 2 ^ 2 + 6 * x 3 ^ 2

/-- Multiplication in `O`. -/
def quatMul (x y : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![x 0 * y 0 + 2 * x 1 * y 1 + 3 * x 2 * y 2 - 6 * x 3 * y 3,
    x 0 * y 1 + x 1 * y 0 - 3 * x 2 * y 3 + 3 * x 3 * y 2,
    x 0 * y 2 + x 2 * y 0 + 2 * x 1 * y 3 - 2 * x 3 * y 1,
    x 0 * y 3 + x 3 * y 0 + x 1 * y 2 - x 2 * y 1]

/-- Conjugation `x̄ = x₀ − x₁ i − x₂ j − x₃ ij`. -/
def quatConj (x : Fin 4 → ℤ) : Fin 4 → ℤ := ![x 0, -x 1, -x 2, -x 3]

/-- The unit of `O`. -/
def quatOne : Fin 4 → ℤ := ![1, 0, 0, 0]

theorem sqrt_two_mul_self : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)

theorem quatMat_apply (x : Fin 4 → ℤ) :
    quatMat x = !![(x 0 : ℝ) + x 1 * √2, 3 * ((x 2 : ℝ) + x 3 * √2);
      (x 2 : ℝ) - x 3 * √2, (x 0 : ℝ) - x 1 * √2] := rfl

theorem quatMat_one : quatMat quatOne = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [quatMat_apply, quatOne]

theorem quatMat_neg_one : quatMat (-quatOne) = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [quatMat_apply, quatOne]

theorem quatMat_add (x y : Fin 4 → ℤ) : quatMat (x + y) = quatMat x + quatMat y := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [quatMat_apply] <;> ring

theorem quatMat_smul (c : ℤ) (x : Fin 4 → ℤ) : quatMat (c • x) = (c : ℝ) • quatMat x := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [quatMat_apply] <;> ring

/-- **The embedding is multiplicative.** -/
theorem quatMat_mul (x y : Fin 4 → ℤ) : quatMat x * quatMat y = quatMat (quatMul x y) := by
  have h := sqrt_two_mul_self
  ext i j; fin_cases i <;> fin_cases j <;>
    simp only [quatMat_apply, quatMul, Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Fin.zero_eta, Fin.mk_one] <;>
    push_cast
  · linear_combination ((x 1 : ℝ) * y 1 - 3 * x 3 * y 3) * h
  · linear_combination 3 * ((x 1 : ℝ) * y 3 - x 3 * y 1) * h
  · linear_combination ((x 1 : ℝ) * y 3 - x 3 * y 1) * h
  · linear_combination ((x 1 : ℝ) * y 1 - 3 * x 3 * y 3) * h

/-- **Conjugation is the adjugate.** -/
theorem adjugate_quatMat (x : Fin 4 → ℤ) : adjugate (quatMat x) = quatMat (quatConj x) := by
  rw [adjugate_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [quatMat_apply, quatConj] <;> ring

/-- **The determinant is the reduced norm.** -/
theorem det_quatMat (x : Fin 4 → ℤ) : (quatMat x).det = nrd x := by
  have h := sqrt_two_mul_self
  rw [det_fin_two, quatMat_apply]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, nrd]
  push_cast
  linear_combination (-(x 1 : ℝ) ^ 2 + 3 * x 3 ^ 2) * h

theorem nrd_quatConj (x : Fin 4 → ℤ) : nrd (quatConj x) = nrd x := by
  simp [nrd, quatConj]

/-! ### Anisotropy -/

/-- `u² + v² ≡ 0 mod 3` forces `3 ∣ u, v`. -/
theorem three_dvd_of_sq_add_sq {u v : ℤ} (h : (3 : ℤ) ∣ u ^ 2 + v ^ 2) :
    (3 : ℤ) ∣ u ∧ (3 : ℤ) ∣ v := by
  have key : ∀ p q : ZMod 3, p ^ 2 + q ^ 2 = 0 → p = 0 ∧ q = 0 := by decide
  have h' : ((u : ZMod 3)) ^ 2 + (v : ZMod 3) ^ 2 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (u ^ 2 + v ^ 2) 3).mpr h
    push_cast at this
    exact this
  obtain ⟨hu, hv⟩ := key _ _ h'
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd u 3).mp hu,
    (ZMod.intCast_zmod_eq_zero_iff_dvd v 3).mp hv⟩

/-- A zero of the norm form has all coordinates divisible by `3`. -/
theorem three_dvd_of_nrd_eq_zero {x : Fin 4 → ℤ} (h : nrd x = 0) : ∀ k, (3 : ℤ) ∣ x k := by
  unfold nrd at h
  obtain ⟨h0, h1⟩ := three_dvd_of_sq_add_sq (u := x 0) (v := x 1)
    ⟨x 2 ^ 2 - 2 * x 3 ^ 2 + x 1 ^ 2, by linear_combination h⟩
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := h1
  obtain ⟨h2, h3⟩ := three_dvd_of_sq_add_sq (u := x 2) (v := x 3)
    ⟨a ^ 2 - 2 * b ^ 2 + x 3 ^ 2, by rw [ha, hb] at h; linarith⟩
  intro k
  fin_cases k
  · exact ⟨a, ha⟩
  · exact ⟨b, hb⟩
  · exact h2
  · exact h3

/-- **`B` is a division algebra**: the norm form `x₀² − 2x₁² − 3x₂² + 6x₃²` is anisotropic. -/
theorem eq_zero_of_nrd_eq_zero (x : Fin 4 → ℤ) (h : nrd x = 0) : x = 0 := by
  induction hn : (x 0).natAbs + (x 1).natAbs + (x 2).natAbs + (x 3).natAbs
    using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    have hd := three_dvd_of_nrd_eq_zero h
    choose y hy using hd
    have hx : x = (3 : ℤ) • y := funext fun k => by rw [hy k]; rfl
    have hny : nrd y = 0 := by
      have : nrd x = 9 * nrd y := by
        rw [hx]; simp only [nrd, Pi.smul_apply, smul_eq_mul]; ring
      omega
    by_contra hne
    have hy0 : y ≠ 0 := fun h0 => hne (by rw [hx, h0, smul_zero])
    have hsize : (y 0).natAbs + (y 1).natAbs + (y 2).natAbs + (y 3).natAbs < n := by
      have hpos : 0 < (y 0).natAbs + (y 1).natAbs + (y 2).natAbs + (y 3).natAbs := by
        by_contra hz
        apply hy0
        have e0 : y 0 = 0 := by omega
        have e1 : y 1 = 0 := by omega
        have e2 : y 2 = 0 := by omega
        have e3 : y 3 = 0 := by omega
        funext k
        fin_cases k
        · exact e0
        · exact e1
        · exact e2
        · exact e3
      rw [← hn, hy 0, hy 1, hy 2, hy 3]
      simp only [Int.natAbs_mul]
      norm_num
      omega
    exact hy0 (ih _ hsize y hny rfl)

/-! ### Reading coordinates off the matrix -/

/-- `x₀ = (m₀₀ + m₁₁)/2`, `x₁ = (m₀₀ − m₁₁)/(2√2)`, `x₂ = (m₀₁/3 + m₁₀)/2`,
`x₃ = (m₀₁/3 − m₁₀)/(2√2)`. -/
def quatCoeff (M : Matrix (Fin 2) (Fin 2) ℝ) : Fin 4 → ℝ :=
  ![(M 0 0 + M 1 1) / 2, (M 0 0 - M 1 1) / (2 * √2), (M 0 1 / 3 + M 1 0) / 2,
    (M 0 1 / 3 - M 1 0) / (2 * √2)]

theorem quatCoeff_quatMatR (v : Fin 4 → ℝ) : quatCoeff (quatMatR v) = v := by
  have hs : √2 ≠ 0 := by positivity
  funext k
  fin_cases k <;> simp [quatCoeff, quatMatR] <;> field_simp <;> ring

theorem quatMatR_injective : Function.Injective quatMatR := fun v w h => by
  rw [← quatCoeff_quatMatR v, ← quatCoeff_quatMatR w, h]

theorem quatMat_injective : Function.Injective quatMat := fun x y h => by
  have h' := quatMatR_injective h
  funext k
  exact_mod_cast congrFun h' k

/-- Entries bounded by `t` give coordinates bounded by `t`. -/
theorem abs_quatCoeff_le {M : Matrix (Fin 2) (Fin 2) ℝ} {t : ℝ} (hM : ∀ i j, |M i j| ≤ t) :
    ∀ k, |quatCoeff M k| ≤ t := by
  have hs : 1 ≤ √2 := by rw [Real.one_le_sqrt]; norm_num
  have h00 := abs_le.mp (hM 0 0)
  have h01 := abs_le.mp (hM 0 1)
  have h10 := abs_le.mp (hM 1 0)
  have h11 := abs_le.mp (hM 1 1)
  have hs2 : 0 < 2 * √2 := by positivity
  intro k
  fin_cases k
  · show |(M 0 0 + M 1 1) / 2| ≤ t
    rw [abs_le]; constructor <;> linarith
  · show |(M 0 0 - M 1 1) / (2 * √2)| ≤ t
    rw [abs_le]; constructor
    · rw [le_div_iff₀ hs2]; nlinarith
    · rw [div_le_iff₀ hs2]; nlinarith
  · show |(M 0 1 / 3 + M 1 0) / 2| ≤ t
    rw [abs_le]; constructor <;> linarith
  · show |(M 0 1 / 3 - M 1 0) / (2 * √2)| ≤ t
    rw [abs_le]; constructor
    · rw [le_div_iff₀ hs2]; nlinarith
    · rw [div_le_iff₀ hs2]; nlinarith

theorem abs_coord_le_of_entries {x : Fin 4 → ℤ} {t : ℝ} (hM : ∀ i j, |quatMat x i j| ≤ t) :
    ∀ k, |(x k : ℝ)| ≤ t := fun k => by
  have := abs_quatCoeff_le hM k
  rwa [quatMat, quatCoeff_quatMatR] at this

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
