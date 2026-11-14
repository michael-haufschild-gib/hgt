import GaloisForLFunctions.CompactHyperbolicSurfaces.QuaternionWalls
import Mathlib.NumberTheory.PellMatiyasevic

/-!
# The wall crossing `χ(η) = −2` on `Γ(5)`

Take `z₀ = i√3` and `η = ι(26 + 15j)` (`26 + 15√3 = (2 + √3)³ ≡ 1 mod 5`).  Both `z₀` and `ηz₀` lie on
the circle `|z|² = 3`, the axis of the units of `ℤ[j] = ℤ[√3]`, where a pure quaternion
`w = x₁i + x₂j + x₃ij` has `H_w(z) = −2√2 (3x₃ + x₁ Re z)` (`wallSide_of_normSq_eq_three`).  With
`Re ηz₀ = 2340/1351`, a wall separating `z₀` from `ηz₀` has `x₁² > 3x₃²`, so the norm equation
`2x₁² + 3x₂² − 6x₃² = 2` forces `x₂ = 0` and the Pell equation `x₁² − 3x₃² = 1`, whose solutions are
the powers of `2 + √3`; the congruences mod 5 leave exactly `w = 26i − 15ij` and
`w = 1351i − 780ij` (`wall_cross_classify`), both crossed in the negative direction:

  `χ(η) = θ(ηz₀) = −2`   (`wallCount_eta`, `wallHom_eta`).
-/

open Matrix UpperHalfPlane Set
open scoped MatrixGroups

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

noncomputable section

/-! ### The Pell equation `x² − 3y² = 1` -/

private theorem a12 : 1 < 2 := by norm_num

/-- Every solution of `x² = 1 + 3y²` is `(xₙ, yₙ)`, `xₙ + yₙ√3 = (2 + √3)ⁿ`. -/
theorem pell_three {x y : ℕ} (h : x * x = 1 + 3 * y * y) :
    ∃ n, x = Pell.xn a12 n ∧ y = Pell.yn a12 n :=
  Pell.eq_pell a12 (Nat.sub_eq_of_eq_add h)

theorem pell_x_vals : Pell.xn a12 0 = 1 ∧ Pell.xn a12 1 = 2 ∧ Pell.xn a12 2 = 7 ∧
    Pell.xn a12 3 = 26 ∧ Pell.xn a12 4 = 97 ∧ Pell.xn a12 5 = 362 ∧ Pell.xn a12 6 = 1351 := by
  decide

theorem pell_y_vals : Pell.yn a12 0 = 0 ∧ Pell.yn a12 1 = 1 ∧ Pell.yn a12 2 = 4 ∧
    Pell.yn a12 3 = 15 ∧ Pell.yn a12 4 = 56 ∧ Pell.yn a12 5 = 209 ∧ Pell.yn a12 6 = 780 ∧
    Pell.yn a12 7 = 2911 := by
  decide

/-- **The walls crossed between `z₀` and `ηz₀`**, in coordinates `a = x₁`, `b = x₂`, `c = x₃`:
a sign change of `3c + a·Re z` between `Re z = 0` and `Re z = 2340/1351` forces `a² > 3c²`, hence
`b = 0`, `a² − 3c² = 1` with `|a| ≤ 1351`, and the congruences `a ≡ 1`, `c ≡ 0 mod 5` leave two
solutions. -/
theorem wall_cross_classify {a b c : ℤ} (hnrd : 2 * a ^ 2 + 3 * b ^ 2 - 6 * c ^ 2 = 2)
    (ha : a % 5 = 1) (hc : c % 5 = 0)
    (hcase : (4053 * c + 2340 * a < 0 ∧ 0 ≤ c) ∨ (0 ≤ 4053 * c + 2340 * a ∧ c < 0)) :
    b = 0 ∧ ((a = 26 ∧ c = -15) ∨ (a = 1351 ∧ c = -780)) := by
  obtain ⟨hX0, hX1, hX2, hX3, hX4, hX5, hX6⟩ := pell_x_vals
  obtain ⟨hY0, hY1, hY2, hY3, hY4, hY5, hY6, hY7⟩ := pell_y_vals
  have hb_of : 0 < a ^ 2 - 3 * c ^ 2 → b = 0 ∧ a ^ 2 - 3 * c ^ 2 = 1 := by
    intro hpos
    have hpos1 : 1 ≤ a ^ 2 - 3 * c ^ 2 := by omega
    have hb2 : b ^ 2 ≤ 0 := by linarith
    have hb : b = 0 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp
      (le_antisymm hb2 (sq_nonneg b))
    refine ⟨hb, ?_⟩
    rw [hb] at hnrd
    linarith
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exfalso
    have hsq : 4053 * c * (4053 * c) < -2340 * a * (-2340 * a) :=
      mul_self_lt_mul_self (by linarith) (by linarith)
    obtain ⟨-, hpell⟩ := hb_of (by linarith [sq_nonneg c])
    have hbound : 3 * a ^ 2 < 5475603 := by linarith
    obtain ⟨x, hxa⟩ : ∃ x : ℕ, -a = x := ⟨(-a).toNat, (Int.toNat_of_nonneg (by linarith)).symm⟩
    obtain ⟨y, hyc⟩ : ∃ y : ℕ, c = y := ⟨c.toNat, (Int.toNat_of_nonneg h2).symm⟩
    have hxy : x * x = 1 + 3 * y * y := by
      have : ((x * x : ℕ) : ℤ) = ((1 + 3 * y * y : ℕ) : ℤ) := by
        push_cast; rw [← hxa, ← hyc]; linear_combination hpell
      exact_mod_cast this
    obtain ⟨n, hxn, hyn⟩ := pell_three hxy
    have hx1351 : x < 1351 := by
      have h3 : (x : ℤ) * x < 1351 * 1351 := by rw [← hxa]; linarith
      have h4 : x * x < 1351 * 1351 := by exact_mod_cast h3
      by_contra hc'
      have := Nat.mul_self_le_mul_self (not_lt.mp hc')
      omega
    have hn : n < 6 := (Pell.strictMono_x a12).lt_iff_lt.mp (by rw [← hxn, hX6]; exact hx1351)
    interval_cases n <;> simp only [hX0, hX1, hX2, hX3, hX4, hX5] at hxn <;> omega
  · have hsq : -4053 * c * (-4053 * c) ≤ 2340 * a * (2340 * a) :=
      mul_self_le_mul_self (by linarith) (by linarith)
    have hc2 : 0 < c ^ 2 := by nlinarith
    obtain ⟨hb, hpell⟩ := hb_of (by linarith)
    have hbound : c ^ 2 ≤ 608400 := by linarith
    obtain ⟨x, hxa⟩ : ∃ x : ℕ, a = x := ⟨a.toNat, (Int.toNat_of_nonneg (by linarith)).symm⟩
    obtain ⟨y, hyc⟩ : ∃ y : ℕ, -c = y := ⟨(-c).toNat, (Int.toNat_of_nonneg (by linarith)).symm⟩
    have hxy : x * x = 1 + 3 * y * y := by
      have : ((x * x : ℕ) : ℤ) = ((1 + 3 * y * y : ℕ) : ℤ) := by
        push_cast; rw [← hxa, ← hyc]; linear_combination hpell
      exact_mod_cast this
    obtain ⟨n, hxn, hyn⟩ := pell_three hxy
    have hy780 : y ≤ 780 := by
      have h3 : (y : ℤ) * y ≤ 780 * 780 := by rw [← hyc]; linarith
      have h4 : y * y ≤ 780 * 780 := by exact_mod_cast h3
      by_contra hc'
      have := Nat.mul_self_lt_mul_self (not_le.mp hc')
      omega
    have hn : n < 7 := (Pell.strictMono_y a12).lt_iff_lt.mp (by rw [← hyn, hY7]; omega)
    refine ⟨hb, ?_⟩
    interval_cases n <;> simp only [hX0, hX1, hX2, hX3, hX4, hX5, hX6, hY0, hY1, hY2, hY3, hY4,
      hY5, hY6] at hxn hyn <;> omega

/-! ### The points `z₀ = i√3` and `ηz₀` -/

/-- `z₀ = i√3`. -/
def zS3 : ℍ := UpperHalfPlane.mk ((√3 : ℝ) * Complex.I) (by simp)

theorem zS3_re : zS3.re = 0 := by simp [zS3]

theorem zS3_im : zS3.im = √3 := by simp [zS3]

/-- `26 + 15j`. -/
def etaQ : Fin 4 → ℤ := ![26, 0, 15, 0]

theorem nrd_etaQ : nrd etaQ = 1 := by decide

/-- `η = ι(26 + 15j) = [[26, 45], [15, 26]]`. -/
def etaSL : SL(2, ℝ) := ⟨quatMat etaQ, by rw [det_quatMat, nrd_etaQ]; norm_num⟩

theorem etaSL_entries : etaSL 0 0 = 26 ∧ etaSL 0 1 = 45 ∧ etaSL 1 0 = 15 ∧ etaSL 1 1 = 26 := by
  have e0 : etaQ 0 = 26 := rfl
  have e1 : etaQ 1 = 0 := rfl
  have e2 : etaQ 2 = 15 := rfl
  have e3 : etaQ 3 = 0 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · show quatMat etaQ 0 0 = 26
    norm_num [quatMat_apply, e0, e1]
  · show quatMat etaQ 0 1 = 45
    norm_num [quatMat_apply, e2, e3]
  · show quatMat etaQ 1 0 = 15
    norm_num [quatMat_apply, e2, e3]
  · show quatMat etaQ 1 1 = 26
    norm_num [quatMat_apply, e0, e1]

theorem etaSL_mem : etaSL ∈ congGroup 5 :=
  mem_congGroup.mpr ⟨etaQ, nrd_etaQ, ⟨![5, 0, 3, 0], by funext k; fin_cases k <;> simp [etaQ, quatOne]⟩,
    rfl⟩

/-- `η` as an element of `Γ(5)`. -/
def etaG : congGroup 5 := ⟨etaSL, etaSL_mem⟩

theorem denomSq_eta : denomSq etaSL zS3 = 1351 := by
  obtain ⟨-, -, h10, h11⟩ := etaSL_entries
  rw [denomSq, h10, h11, zS3_re, zS3_im, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem re_eta : (etaSL • zS3).re = 2340 / 1351 := by
  obtain ⟨h00, h01, h10, h11⟩ := etaSL_entries
  rw [re_smul_SL, denomSq_eta, h00, h01, h10, h11, zS3_re, zS3_im,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem im_eta : (etaSL • zS3).im = √3 / 1351 := by
  rw [im_smul_SL, denomSq_eta, zS3_im]

theorem normSq_zS3 : zS3.re ^ 2 + zS3.im ^ 2 = 3 := by
  rw [zS3_re, zS3_im, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num

theorem normSq_eta : (etaSL • zS3).re ^ 2 + (etaSL • zS3).im ^ 2 = 3 := by
  rw [re_eta, im_eta, div_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num

/-! ### The crossing terms -/

/-- On the circle `|z|² = 3`, `H_w(z) = −2√2 (3x₃ + x₁ Re z)` for a pure `w`. -/
theorem wallSide_of_normSq_eq_three {w : Fin 4 → ℤ} (hw0 : w 0 = 0) {z : ℍ}
    (hz : z.re ^ 2 + z.im ^ 2 = 3) : wallSide w z = -(2 * √2) * (3 * w 3 + w 1 * z.re) := by
  simp only [wallSide, hermForm, hermR, quatMat_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, hw0,
    Int.cast_zero]
  rw [hz]; ring

theorem posInd_neg_mul {k : ℝ} (hk : 0 < k) (t : ℝ) :
    posInd (-k * t) = if t < 0 then 1 else 0 := by
  unfold posInd
  by_cases ht : t < 0
  · rw [if_pos (by nlinarith), if_pos ht]
  · rw [if_neg (fun h => by nlinarith [not_lt.mp ht]), if_neg ht]

/-- The crossing term of a wall between `z₀` and `ηz₀`. -/
def crossTerm (w : Fin 4 → ℤ) : ℤ :=
  (if 4053 * w 3 + 2340 * w 1 < 0 then 1 else 0) - (if w 3 < 0 then 1 else 0)

theorem posInd_sub_eq_crossTerm {w : Fin 4 → ℤ} (hw0 : w 0 = 0) :
    posInd (wallSide w (etaSL • zS3)) - posInd (wallSide w zS3) = crossTerm w := by
  have hk : (0 : ℝ) < 2 * √2 := by positivity
  rw [wallSide_of_normSq_eq_three hw0 normSq_eta, wallSide_of_normSq_eq_three hw0 normSq_zS3,
    posInd_neg_mul hk, posInd_neg_mul hk, re_eta, zS3_re, crossTerm]
  have c1 : (3 * (w 3 : ℝ) + (w 1 : ℝ) * (2340 / 1351) < 0) ↔ 4053 * w 3 + 2340 * w 1 < 0 := by
    constructor
    · intro h
      have : ((4053 * w 3 + 2340 * w 1 : ℤ) : ℝ) < 0 := by push_cast; linarith
      exact_mod_cast this
    · intro h
      have : ((4053 * w 3 + 2340 * w 1 : ℤ) : ℝ) < 0 := by exact_mod_cast h
      push_cast at this
      linarith
  have c2 : (3 * (w 3 : ℝ) + (w 1 : ℝ) * 0 < 0) ↔ w 3 < 0 := by
    rw [mul_zero, add_zero]
    constructor
    · intro h
      have : (w 3 : ℝ) < 0 := by linarith
      exact_mod_cast this
    · intro h
      have : (w 3 : ℝ) < 0 := by exact_mod_cast h
      linarith
  simp only [c1, c2]

/-- A wall with a nonzero crossing term is `26i − 15ij` or `1351i − 780ij`. -/
theorem eq_of_crossTerm_ne_zero {w : Fin 4 → ℤ} (hw : w ∈ wallSet 5) (h : crossTerm w ≠ 0) :
    w = ![0, 26, 0, -15] ∨ w = ![0, 1351, 0, -780] := by
  obtain ⟨hw0, hw2, u, hu⟩ := hw
  have h1 : w 1 = 1 + 5 * u 1 := by
    have := congrFun hu 1; simpa [quatI] using this
  have h3 : w 3 = 5 * u 3 := by
    have := congrFun hu 3; simpa [quatI] using this
  have hnrd : 2 * w 1 ^ 2 + 3 * w 2 ^ 2 - 6 * w 3 ^ 2 = 2 := by
    have := hw2; simp only [nrd, hw0] at this; linarith
  have hcase : (4053 * w 3 + 2340 * w 1 < 0 ∧ 0 ≤ w 3) ∨
      (0 ≤ 4053 * w 3 + 2340 * w 1 ∧ w 3 < 0) := by
    unfold crossTerm at h
    by_cases hA : 4053 * w 3 + 2340 * w 1 < 0 <;> by_cases hB : w 3 < 0
    · simp [hA, hB] at h
    · exact Or.inl ⟨hA, not_lt.mp hB⟩
    · exact Or.inr ⟨not_lt.mp hA, hB⟩
    · simp [hA, hB] at h
  obtain ⟨hb, hac⟩ := wall_cross_classify hnrd (by omega) (by omega) hcase
  rcases hac with ⟨ha, hc⟩ | ⟨ha, hc⟩
  · left; funext k; fin_cases k <;> simp [hw0, ha, hb, hc]
  · right; funext k; fin_cases k <;> simp [hw0, ha, hb, hc]

/-- The wall `26i − 15ij`. -/
def wallA : wallSet 5 :=
  ⟨![0, 26, 0, -15], rfl, by decide, ![0, 5, 0, -3], by
    funext k; fin_cases k <;> simp [quatI]⟩

/-- The wall `1351i − 780ij`. -/
def wallB : wallSet 5 :=
  ⟨![0, 1351, 0, -780], rfl, by decide, ![0, 270, 0, -156], by
    funext k; fin_cases k <;> simp [quatI]⟩

/-- **The wall crossing.**  `θ(ηz₀) = −2`. -/
theorem wallCount_eta : wallCount 5 zS3 (etaSL • zS3) = -2 := by
  classical
  have hterm : ∀ w : wallSet 5,
      posInd (wallSide w (etaSL • zS3)) - posInd (wallSide w zS3) = crossTerm w :=
    fun w => posInd_sub_eq_crossTerm w.2.1
  have hne : wallA ≠ wallB := by
    intro h
    have := congrArg (fun w : wallSet 5 => (w : Fin 4 → ℤ) 1) h
    simp [wallA, wallB] at this
  rw [wallCount, finsum_congr hterm,
    finsum_eq_sum_of_support_subset (s := {wallA, wallB}) _ ?_]
  · have hA : crossTerm (wallA : Fin 4 → ℤ) = -1 := by decide
    have hB : crossTerm (wallB : Fin 4 → ℤ) = -1 := by decide
    rw [Finset.sum_pair hne, hA, hB]
    norm_num
  · intro w hw
    rcases eq_of_crossTerm_ne_zero w.2 hw with h | h
    · simp [show w = wallA from Subtype.ext h]
    · simp [show w = wallB from Subtype.ext h]

/-- **`χ(η) = −2`**: the wall homomorphism of `Γ(5)` based at `i√3` is nonzero. -/
theorem wallHom_eta : wallHom zS3 etaG = Multiplicative.ofAdd (-2) := by
  rw [wallHom_apply]
  exact congrArg Multiplicative.ofAdd wallCount_eta

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
