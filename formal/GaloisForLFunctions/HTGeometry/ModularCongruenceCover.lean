import GaloisForLFunctions.HTGeometry.ModularMonodromyCover

/-!
# Principal congruence subgroups are torsion free

For `n ≥ 3` the principal congruence subgroup `Γ(n) ⊆ SL(2,ℤ)` contains no element whose square
or cube lies in `{±1}` other than `±1` itself.  The mechanism is the Cayley–Hamilton identity
`A² = (tr A)·A − 1` for a determinant-one `2 × 2` matrix: it forces `tr A ∈ {0, ±1, ±2}` in every
torsion case, while a matrix congruent to the identity mod `n` has trace congruent to `2`.  The
residual case `n = 3`, `tr A = −1` is excluded by reading the relation `A² + A + 1 = 0` modulo
`9`.

Equivalently, the image of `Γ(n)` in `PSL(2,ℤ) = SL(2,ℤ)/{±1}` is torsion free for `n ≥ 3`.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix CongruenceSubgroup ModularGroup
open scoped MatrixGroups

section NegOne

/-- `-1` in `SL(2, ℤ)`. -/
def slNegOne : SL(2, ℤ) := ⟨!![-1, 0; 0, -1], by norm_num [Matrix.det_fin_two_of]⟩

@[simp] theorem slNegOne_coe :
    (slNegOne : Matrix (Fin 2) (Fin 2) ℤ) = !![-1, 0; 0, -1] := rfl

theorem slNegOne_mul_self : slNegOne * slNegOne = 1 := by
  apply Subtype.ext
  show (!![(-1 : ℤ), 0; 0, -1]) * !![(-1 : ℤ), 0; 0, -1] = (1 : Matrix (Fin 2) (Fin 2) ℤ)
  norm_num [Matrix.mul_fin_two, ← Matrix.one_fin_two]

theorem slNegOne_ne_one : slNegOne ≠ 1 := by
  intro h
  have := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
  simp at this

theorem slNegOne_central (A : SL(2, ℤ)) : Commute slNegOne A := by
  show slNegOne * A = A * slNegOne
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

/-- The central subgroup `{±1}` of `SL(2, ℤ)`. -/
def slPM : Subgroup SL(2, ℤ) where
  carrier := {A | A = 1 ∨ A = slNegOne}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro A B (rfl | rfl) (rfl | rfl)
    · exact Or.inl (one_mul _)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl slNegOne_mul_self
  inv_mem' := by
    rintro A (rfl | rfl)
    · exact Or.inl inv_one
    · exact Or.inr (inv_eq_of_mul_eq_one_right slNegOne_mul_self)

theorem mem_slPM {A : SL(2, ℤ)} : A ∈ slPM ↔ A = 1 ∨ A = slNegOne := Iff.rfl

end NegOne

section Entries

/-- The trace of an element of `SL(2, ℤ)`. -/
def slTrace (A : SL(2, ℤ)) : ℤ := (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + A 1 1

theorem sl_det (A : SL(2, ℤ)) :
    (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
  have h := A.2
  rwa [Matrix.det_fin_two] at h

theorem sl_mul_entry (A B : SL(2, ℤ)) (i j : Fin 2) :
    ((A * B : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j
      = (A : Matrix (Fin 2) (Fin 2) ℤ) i 0 * (B : Matrix (Fin 2) (Fin 2) ℤ) 0 j
        + (A : Matrix (Fin 2) (Fin 2) ℤ) i 1 * (B : Matrix (Fin 2) (Fin 2) ℤ) 1 j := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl_ext {A B : SL(2, ℤ)}
    (h : ∀ i j, (A : Matrix (Fin 2) (Fin 2) ℤ) i j = (B : Matrix (Fin 2) (Fin 2) ℤ) i j) :
    A = B := by
  apply Subtype.ext
  ext i j
  exact h i j

theorem sl_one_entry (i j : Fin 2) :
    ((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j = if i = j then 1 else 0 := by
  simp [Matrix.one_apply]

end Entries

section Torsion

/-- A diagonal element of `SL(2, ℤ)` with equal diagonal entries is `±1`. -/
theorem sl_eq_pm_one_of_offdiag {A : SL(2, ℤ)}
    (hb : (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0) (hc : (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0)
    (had : (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = A 1 1) : A = 1 ∨ A = slNegOne := by
  have hdet := sl_det A
  rw [hb, hc, ← had] at hdet
  have hsq : (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * A 0 0 = 1 := by linarith
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hsq with ⟨h1, _⟩ | ⟨h1, _⟩
  · left
    refine sl_ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [sl_one_entry, hb, hc, h1, ← had]
  · right
    refine sl_ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [hb, hc, h1, ← had]

/-- **Square roots of `1`.**  An element of `SL(2, ℤ)` squaring to `1` is `±1`. -/
theorem sl_eq_pm_one_of_sq_eq_one {A : SL(2, ℤ)} (h : A * A = 1) : A = 1 ∨ A = slNegOne := by
  have e00 := sl_mul_entry A A 0 0
  have e01 := sl_mul_entry A A 0 1
  have e10 := sl_mul_entry A A 1 0
  have e11 := sl_mul_entry A A 1 1
  rw [h] at e00 e01 e10 e11
  rw [sl_one_entry] at e00 e01 e10 e11
  norm_num at e00 e01 e10 e11
  have hdet := sl_det A
  set a := (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set b := (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  set c := (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set d := (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have hta : (a + d) * a = 2 := by nlinarith
  have htd : (a + d) * d = 2 := by nlinarith
  have htb : (a + d) * b = 0 := by nlinarith
  have htc : (a + d) * c = 0 := by nlinarith
  have ht2 : (a + d - 2) * (a + d + 2) = 0 := by nlinarith
  have htne : a + d ≠ 0 := by
    rcases mul_eq_zero.mp ht2 with h' | h' <;> omega
  have hb0 : b = 0 := by
    rcases mul_eq_zero.mp htb with h' | h'
    · exact absurd h' htne
    · exact h'
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp htc with h' | h'
    · exact absurd h' htne
    · exact h'
  have had : a = d := by
    have : (a + d) * (a - d) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' htne
    · linarith
  exact sl_eq_pm_one_of_offdiag hb0 hc0 had

/-- **Square roots of `−1`.**  An element of `SL(2, ℤ)` squaring to `−1` has trace zero. -/
theorem sl_trace_eq_zero_of_sq_eq_negOne {A : SL(2, ℤ)} (h : A * A = slNegOne) :
    slTrace A = 0 := by
  have e00 := sl_mul_entry A A 0 0
  have e01 := sl_mul_entry A A 0 1
  have e10 := sl_mul_entry A A 1 0
  have e11 := sl_mul_entry A A 1 1
  rw [h] at e00 e01 e10 e11
  simp only [slNegOne_coe] at e00 e01 e10 e11
  norm_num at e00 e01 e10 e11
  have hdet := sl_det A
  set a := (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set b := (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  set c := (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set d := (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have hta : (a + d) * a = 0 := by nlinarith
  have htd : (a + d) * d = 0 := by nlinarith
  have htb : (a + d) * b = 0 := by nlinarith
  have htc : (a + d) * c = 0 := by nlinarith
  by_contra hne
  have hne' : a + d ≠ 0 := by
    simpa [slTrace] using hne
  have ha0 : a = 0 := by
    rcases mul_eq_zero.mp hta with h' | h'
    · exact absurd h' hne'
    · exact h'
  have hd0 : d = 0 := by
    rcases mul_eq_zero.mp htd with h' | h'
    · exact absurd h' hne'
    · exact h'
  exact hne' (by rw [ha0, hd0]; ring)

/-- Cayley–Hamilton, entrywise: `A² = (tr A)·A − 1`. -/
theorem sl_sq_entry (A : SL(2, ℤ)) (i j : Fin 2) :
    ((A * A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j
      = slTrace A * (A : Matrix (Fin 2) (Fin 2) ℤ) i j - (if i = j then 1 else 0) := by
  have hdet := sl_det A
  rw [sl_mul_entry]
  fin_cases i <;> fin_cases j <;> simp [slTrace] <;> linarith [hdet]

/-- The cube, entrywise: `A³ = (tr² − 1)·A − (tr)·1`. -/
theorem sl_cube_entry (A : SL(2, ℤ)) (i j : Fin 2) :
    ((A * A * A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j
      = (slTrace A ^ 2 - 1) * (A : Matrix (Fin 2) (Fin 2) ℤ) i j
        - slTrace A * (if i = j then 1 else 0) := by
  have hij := sl_sq_entry A i j
  rw [sl_mul_entry] at hij
  have hone := sl_mul_entry 1 A i j
  rw [one_mul] at hone
  simp only [sl_one_entry] at hone
  rw [sl_mul_entry, sl_sq_entry A i 0, sl_sq_entry A i 1]
  linear_combination (slTrace A) * hij + hone

/-- **Cube roots of `1`.**  Either the element is `±1` or its trace is `−1`. -/
theorem sl_cube_one_cases {A : SL(2, ℤ)} (h : A * A * A = 1) :
    (A = 1 ∨ A = slNegOne) ∨ slTrace A = -1 := by
  have e00 := sl_cube_entry A 0 0
  have e01 := sl_cube_entry A 0 1
  have e10 := sl_cube_entry A 1 0
  have e11 := sl_cube_entry A 1 1
  rw [h, sl_one_entry] at e00 e01 e10 e11
  norm_num at e00 e01 e10 e11
  by_cases hts : slTrace A ^ 2 - 1 = 0
  · right
    rw [hts] at e00
    linarith [e00]
  · left
    have hb0 : (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0 := by
      rcases e01 with h' | h'
      · exact absurd h' hts
      · exact h'
    have hc0 : (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by
      rcases e10 with h' | h'
      · exact absurd h' hts
      · exact h'
    have had : (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = A 1 1 := by
      have hdiff : (slTrace A ^ 2 - 1) *
          ((A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1) = 0 := by
        have := e00
        have := e11
        nlinarith [e00, e11]
      rcases mul_eq_zero.mp hdiff with h' | h'
      · exact absurd h' hts
      · linarith
    exact sl_eq_pm_one_of_offdiag hb0 hc0 had

/-- **Cube roots of `−1`.**  Either the element is `±1` or its trace is `1`. -/
theorem sl_cube_negOne_cases {A : SL(2, ℤ)} (h : A * A * A = slNegOne) :
    (A = 1 ∨ A = slNegOne) ∨ slTrace A = 1 := by
  have e00 := sl_cube_entry A 0 0
  have e01 := sl_cube_entry A 0 1
  have e10 := sl_cube_entry A 1 0
  have e11 := sl_cube_entry A 1 1
  rw [h] at e00 e01 e10 e11
  simp only [slNegOne_coe] at e00 e01 e10 e11
  norm_num at e00 e01 e10 e11
  by_cases hts : slTrace A ^ 2 - 1 = 0
  · right
    rw [hts] at e00
    linarith [e00]
  · left
    have hb0 : (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0 := by
      rcases e01 with h' | h'
      · exact absurd h' hts
      · exact h'
    have hc0 : (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by
      rcases e10 with h' | h'
      · exact absurd h' hts
      · exact h'
    have had : (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = A 1 1 := by
      have hdiff : (slTrace A ^ 2 - 1) *
          ((A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1) = 0 := by
        nlinarith [e00, e11]
      rcases mul_eq_zero.mp hdiff with h' | h'
      · exact absurd h' hts
      · linarith
    exact sl_eq_pm_one_of_offdiag hb0 hc0 had

end Torsion

section Congruence

variable {n : ℕ}

theorem gamma_dvd {A : SL(2, ℤ)} (hA : A ∈ Gamma n) :
    (n : ℤ) ∣ (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - 1 ∧
      (n : ℤ) ∣ (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 ∧
      (n : ℤ) ∣ (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧
      (n : ℤ) ∣ (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - 1 := by
  obtain ⟨h00, h01, h10, h11⟩ := Gamma_mem.mp hA
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : (((A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - 1 : ℤ) : ZMod n) = 0 := by
      push_cast
      rw [h00]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  · have : (((A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod n) = 0 := h01
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  · have : (((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod n) = 0 := h10
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  · have : (((A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - 1 : ℤ) : ZMod n) = 0 := by
      push_cast
      rw [h11]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this

theorem gamma_dvd_trace_sub_two {A : SL(2, ℤ)} (hA : A ∈ Gamma n) :
    (n : ℤ) ∣ slTrace A - 2 := by
  obtain ⟨h1, -, -, h2⟩ := gamma_dvd hA
  obtain ⟨u, hu⟩ := h1
  obtain ⟨v, hv⟩ := h2
  exact ⟨u + v, by simp only [slTrace]; linarith⟩

/-- **`Γ(n)` has no element of order two in `PSL(2,ℤ)`** for `n ≥ 3`. -/
theorem gamma_sq_mem_slPM {A : SL(2, ℤ)} (hn : 3 ≤ n) (hA : A ∈ Gamma n)
    (h : A * A ∈ slPM) : A ∈ slPM := by
  rcases mem_slPM.mp h with h' | h'
  · exact mem_slPM.mpr (sl_eq_pm_one_of_sq_eq_one h')
  · exfalso
    have ht := sl_trace_eq_zero_of_sq_eq_negOne h'
    obtain ⟨u, hu⟩ := gamma_dvd_trace_sub_two hA
    rw [ht] at hu
    have hn' : (3 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    have : (n : ℤ) ∣ 2 := ⟨-u, by linarith⟩
    have := Int.le_of_dvd (by norm_num) this
    omega

/-- **`Γ(n)` has no element of order three in `PSL(2,ℤ)`** for `n ≥ 3`. -/
theorem gamma_cube_mem_slPM {A : SL(2, ℤ)} (hn : 3 ≤ n) (hA : A ∈ Gamma n)
    (h : A * A * A ∈ slPM) : A ∈ slPM := by
  have hn' : (3 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  obtain ⟨u, hu⟩ := gamma_dvd_trace_sub_two hA
  rcases mem_slPM.mp h with h' | h'
  · rcases sl_cube_one_cases h' with hpm | ht
    · exact mem_slPM.mpr hpm
    · -- trace `−1` forces `n = 3`, excluded by reading `A² + A + 1 = 0` modulo `9`
      exfalso
      rw [ht] at hu
      have hdvd3 : (n : ℤ) ∣ 3 := ⟨-u, by linarith⟩
      have hle := Int.le_of_dvd (by norm_num) hdvd3
      have hn3 : (n : ℤ) = 3 := by omega
      obtain ⟨ha, hb, hc, -⟩ := gamma_dvd hA
      rw [hn3] at ha hb hc
      obtain ⟨α, hα⟩ := ha
      obtain ⟨β, hβ⟩ := hb
      obtain ⟨γ, hγ⟩ := hc
      -- the `(0,0)` entry of `A² = (tr A)·A − 1`
      have hsq := sl_sq_entry A 0 0
      rw [sl_mul_entry, ht] at hsq
      norm_num at hsq
      -- `a² + b c + a + 1 = 0`
      have hrel : (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0
          + (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0
          + (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + 1 = 0 := by linarith
      have ha' : (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 + 3 * α := by linarith
      have hK : 3 + 9 * (α + α * α + β * γ) = 0 := by
        rw [ha', hβ, hγ] at hrel
        linear_combination hrel
      omega
  · rcases sl_cube_negOne_cases h' with hpm | ht
    · exact mem_slPM.mpr hpm
    · exfalso
      rw [ht] at hu
      have : (n : ℤ) ∣ 1 := ⟨-u, by linarith⟩
      have := Int.le_of_dvd (by norm_num) this
      omega

end Congruence

section Cover

open Equiv

variable {n : ℕ}

theorem slNegOne_inv : (slNegOne : SL(2, ℤ))⁻¹ = slNegOne :=
  inv_eq_of_mul_eq_one_right slNegOne_mul_self

theorem negOne_mul_negOne_mul (A B : SL(2, ℤ)) : (slNegOne * A) * (slNegOne * B) = A * B := by
  calc (slNegOne * A) * (slNegOne * B) = slNegOne * (A * slNegOne) * B := by
        simp only [mul_assoc]
    _ = slNegOne * (slNegOne * A) * B := by rw [← (slNegOne_central A).eq]
    _ = (slNegOne * slNegOne) * (A * B) := by simp only [mul_assoc]
    _ = A * B := by rw [slNegOne_mul_self, one_mul]

theorem negOne_mul_cube (A : SL(2, ℤ)) :
    (slNegOne * A) * (slNegOne * A) * (slNegOne * A) = slNegOne * (A * A * A) := by
  rw [negOne_mul_negOne_mul, ← mul_assoc, ← (slNegOne_central (A * A)).eq, mul_assoc]

theorem negOne_mul_inv (A : SL(2, ℤ)) : slNegOne * A⁻¹ = (slNegOne * A)⁻¹ := by
  rw [_root_.mul_inv_rev, slNegOne_inv]
  exact (slNegOne_central A⁻¹).eq

theorem eq_negOne_mul_of_negOne_mul {A B : SL(2, ℤ)} (h : slNegOne * A = B) :
    A = slNegOne * B := by
  rw [← h, ← mul_assoc, slNegOne_mul_self, one_mul]

theorem negOne_conj (g : SL(2, ℤ)) : g⁻¹ * slNegOne * g = slNegOne := by
  rw [← (slNegOne_central g⁻¹).eq, mul_assoc, inv_mul_cancel, mul_one]

/-- `Γ(n)·{±1}`: the preimage in `SL(2,ℤ)` of the image of `Γ(n)` in `PSL(2,ℤ)`. -/
def gammaPM (n : ℕ) : Subgroup SL(2, ℤ) where
  carrier := {A | A ∈ Gamma n ∨ slNegOne * A ∈ Gamma n}
  one_mem' := Or.inl (one_mem _)
  mul_mem' := by
    rintro A B (hA | hA) (hB | hB)
    · exact Or.inl (mul_mem hA hB)
    · refine Or.inr ?_
      have hswap : slNegOne * (A * B) = A * (slNegOne * B) := by
        rw [← mul_assoc, (slNegOne_central A).eq, mul_assoc]
      rw [hswap]
      exact mul_mem hA hB
    · refine Or.inr ?_
      rw [← mul_assoc]
      exact mul_mem hA hB
    · refine Or.inl ?_
      rw [← negOne_mul_negOne_mul A B]
      exact mul_mem hA hB
  inv_mem' := by
    rintro A (hA | hA)
    · exact Or.inl (inv_mem hA)
    · refine Or.inr ?_
      rw [negOne_mul_inv]
      exact inv_mem hA

theorem mem_gammaPM {A : SL(2, ℤ)} :
    A ∈ gammaPM n ↔ A ∈ Gamma n ∨ slNegOne * A ∈ Gamma n := Iff.rfl

theorem gamma_le_gammaPM : Gamma n ≤ gammaPM n := fun _ h => Or.inl h

theorem slNegOne_mem_gammaPM : slNegOne ∈ gammaPM n :=
  Or.inr (by rw [slNegOne_mul_self]; exact one_mem _)

/-- Conjugates of a square root of `−1` avoid `Γ(n)·{±1}` for `n ≥ 3`. -/
theorem not_mem_gammaPM_of_sq (hn : 3 ≤ n) {C : SL(2, ℤ)} (hsq : C * C = slNegOne)
    (hC1 : C ≠ 1) (hCm : C ≠ slNegOne) (g : SL(2, ℤ)) : g⁻¹ * C * g ∉ gammaPM n := by
  intro hmem
  have hA2 : (g⁻¹ * C * g) * (g⁻¹ * C * g) = slNegOne := by
    have hstep : (g⁻¹ * C * g) * (g⁻¹ * C * g) = g⁻¹ * (C * C) * g := by group
    rw [hstep, hsq, negOne_conj]
  have hconj : ∀ B : SL(2, ℤ), B = 1 ∨ B = slNegOne → g⁻¹ * C * g = B → False := by
    rintro B (rfl | rfl) hB
    · refine hC1 ?_
      have hC : C = g * (1 : SL(2, ℤ)) * g⁻¹ := by rw [← hB]; group
      simpa using hC
    · refine hCm ?_
      have hC : C = g * slNegOne * g⁻¹ := by rw [← hB]; group
      rw [hC, ← (slNegOne_central g).eq, mul_assoc, mul_inv_cancel, mul_one]
  rcases mem_gammaPM.mp hmem with hA | hA
  · exact hconj _ (mem_slPM.mp (gamma_sq_mem_slPM hn hA (by rw [hA2]; exact Or.inr rfl))) rfl
  · have hB2 : (slNegOne * (g⁻¹ * C * g)) * (slNegOne * (g⁻¹ * C * g)) = slNegOne := by
      rw [negOne_mul_negOne_mul, hA2]
    have hmem2 := gamma_sq_mem_slPM hn hA (by rw [hB2]; exact Or.inr rfl)
    rcases mem_slPM.mp hmem2 with h' | h'
    · refine hconj slNegOne (Or.inr rfl) ?_
      rw [eq_negOne_mul_of_negOne_mul h', mul_one]
    · refine hconj 1 (Or.inl rfl) ?_
      rw [eq_negOne_mul_of_negOne_mul h', slNegOne_mul_self]

/-- Conjugates of a cube root of `−1` avoid `Γ(n)·{±1}` for `n ≥ 3`. -/
theorem not_mem_gammaPM_of_cube (hn : 3 ≤ n) {C : SL(2, ℤ)} (hcube : C * C * C = slNegOne)
    (hC1 : C ≠ 1) (hCm : C ≠ slNegOne) (g : SL(2, ℤ)) : g⁻¹ * C * g ∉ gammaPM n := by
  intro hmem
  have hA3 : (g⁻¹ * C * g) * (g⁻¹ * C * g) * (g⁻¹ * C * g) = slNegOne := by
    have hstep : (g⁻¹ * C * g) * (g⁻¹ * C * g) * (g⁻¹ * C * g) = g⁻¹ * (C * C * C) * g := by
      group
    rw [hstep, hcube, negOne_conj]
  have hconj : ∀ B : SL(2, ℤ), B = 1 ∨ B = slNegOne → g⁻¹ * C * g = B → False := by
    rintro B (rfl | rfl) hB
    · refine hC1 ?_
      have hC : C = g * (1 : SL(2, ℤ)) * g⁻¹ := by rw [← hB]; group
      simpa using hC
    · refine hCm ?_
      have hC : C = g * slNegOne * g⁻¹ := by rw [← hB]; group
      rw [hC, ← (slNegOne_central g).eq, mul_assoc, mul_inv_cancel, mul_one]
  rcases mem_gammaPM.mp hmem with hA | hA
  · exact hconj _ (mem_slPM.mp (gamma_cube_mem_slPM hn hA (by rw [hA3]; exact Or.inr rfl))) rfl
  · have hB3 : (slNegOne * (g⁻¹ * C * g)) * (slNegOne * (g⁻¹ * C * g))
        * (slNegOne * (g⁻¹ * C * g)) = 1 := by
      rw [negOne_mul_cube, hA3, slNegOne_mul_self]
    have hmem2 := gamma_cube_mem_slPM hn hA (by rw [hB3]; exact Or.inl rfl)
    rcases mem_slPM.mp hmem2 with h' | h'
    · refine hconj slNegOne (Or.inr rfl) ?_
      rw [eq_negOne_mul_of_negOne_mul h', mul_one]
    · refine hconj 1 (Or.inl rfl) ?_
      rw [eq_negOne_mul_of_negOne_mul h', slNegOne_mul_self]

theorem S_mul_S : ModularGroup.S * ModularGroup.S = slNegOne := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, slNegOne_coe]
  norm_num [Matrix.mul_fin_two]

theorem S_ne_one : ModularGroup.S ≠ 1 := by
  intro h
  have := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
  simp [ModularGroup.coe_S] at this

theorem S_ne_negOne : ModularGroup.S ≠ slNegOne := by
  intro h
  have := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
  simp [ModularGroup.coe_S] at this

theorem ST_coe : ((ModularGroup.S * ModularGroup.T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
    = !![0, -1; 1, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, ModularGroup.coe_T]
  norm_num [Matrix.mul_fin_two]

theorem ST_cube : (ModularGroup.S * ModularGroup.T) * (ModularGroup.S * ModularGroup.T)
    * (ModularGroup.S * ModularGroup.T) = slNegOne := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ST_coe, slNegOne_coe]
  norm_num [Matrix.mul_fin_two]

theorem ST_entry : ((ModularGroup.S * ModularGroup.T : SL(2, ℤ))
    : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 0 := by
  rw [ST_coe]
  norm_num

theorem ST_ne_one : ModularGroup.S * ModularGroup.T ≠ 1 := by
  intro h
  have h0 := ST_entry
  rw [h] at h0
  simp at h0

theorem ST_ne_negOne : ModularGroup.S * ModularGroup.T ≠ slNegOne := by
  intro h
  have h0 := ST_entry
  rw [h] at h0
  simp at h0

/-- The central element acts trivially on the cosets of `Γ(n)·{±1}`. -/
theorem mk_negOne_mul (g : SL(2, ℤ)) :
    (QuotientGroup.mk (slNegOne * g) : SL(2, ℤ) ⧸ gammaPM n) = QuotientGroup.mk g := by
  rw [QuotientGroup.eq]
  have hrw : (slNegOne * g)⁻¹ * g = slNegOne := by
    rw [_root_.mul_inv_rev, slNegOne_inv]
    exact negOne_conj g
  rw [hrw]
  exact slNegOne_mem_gammaPM

/-- A coset is fixed by left translation exactly when the conjugate lies in the subgroup. -/
theorem mk_mul_eq_iff {C g : SL(2, ℤ)} :
    (QuotientGroup.mk (C * g) : SL(2, ℤ) ⧸ gammaPM n) = QuotientGroup.mk g
      ↔ g⁻¹ * C * g ∈ gammaPM n := by
  rw [QuotientGroup.eq]
  have hkey : (C * g)⁻¹ * g = (g⁻¹ * C * g)⁻¹ := by group
  rw [hkey, Subgroup.inv_mem_iff]

variable [NeZero n]

theorem gammaPM_finiteIndex : (gammaPM n).FiniteIndex :=
  haveI : (Gamma n).FiniteIndex := CongruenceSubgroup.instFiniteIndexGamma n
  Subgroup.finiteIndex_of_le gamma_le_gammaPM

noncomputable instance : Fintype (SL(2, ℤ) ⧸ gammaPM n) :=
  haveI := gammaPM_finiteIndex (n := n)
  Subgroup.fintypeQuotientOfFiniteIndex

noncomputable instance : DecidableEq (SL(2, ℤ) ⧸ gammaPM n) := Classical.decEq _

/-- The coset monodromy of the order-two elliptic point. -/
noncomputable def congX (n : ℕ) [NeZero n] : Equiv.Perm (SL(2, ℤ) ⧸ gammaPM n) :=
  MulAction.toPermHom SL(2, ℤ) (SL(2, ℤ) ⧸ gammaPM n) ModularGroup.S

/-- The coset monodromy of the order-three elliptic point. -/
noncomputable def congY (n : ℕ) [NeZero n] : Equiv.Perm (SL(2, ℤ) ⧸ gammaPM n) :=
  MulAction.toPermHom SL(2, ℤ) (SL(2, ℤ) ⧸ gammaPM n) (ModularGroup.S * ModularGroup.T)

theorem congX_apply (g : SL(2, ℤ)) :
    congX n (QuotientGroup.mk g) = QuotientGroup.mk (ModularGroup.S * g) := rfl

theorem congY_apply (g : SL(2, ℤ)) :
    congY n (QuotientGroup.mk g)
      = QuotientGroup.mk (ModularGroup.S * ModularGroup.T * g) := rfl

theorem congX_sq : (congX n) ^ 2 = 1 := by
  ext q
  induction q using Quotient.inductionOn with
  | h g =>
      show ((congX n) ^ 2) (QuotientGroup.mk g) = QuotientGroup.mk g
      rw [pow_two, Equiv.Perm.mul_apply, congX_apply, congX_apply, ← mul_assoc, S_mul_S,
        mk_negOne_mul]

theorem congY_cube : (congY n) ^ 3 = 1 := by
  ext q
  induction q using Quotient.inductionOn with
  | h g =>
      show ((congY n) ^ 3) (QuotientGroup.mk g) = QuotientGroup.mk g
      have hsplit : (congY n) ^ 3 = congY n * (congY n * congY n) := by
        rw [pow_succ, pow_succ, pow_one]
        group
      rw [hsplit, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, congY_apply, congY_apply,
        congY_apply]
      have hkey : ModularGroup.S * ModularGroup.T * (ModularGroup.S * ModularGroup.T *
          (ModularGroup.S * ModularGroup.T * g)) = slNegOne * g := by
        rw [← ST_cube]
        simp only [mul_assoc]
      rw [hkey, mk_negOne_mul]

theorem congX_free (hn : 3 ≤ n) (q : SL(2, ℤ) ⧸ gammaPM n) : congX n q ≠ q := by
  induction q using Quotient.inductionOn with
  | h g =>
      rw [congX_apply]
      intro hq
      exact not_mem_gammaPM_of_sq hn S_mul_S S_ne_one S_ne_negOne g (mk_mul_eq_iff.mp hq)

theorem congY_free (hn : 3 ≤ n) (q : SL(2, ℤ) ⧸ gammaPM n) : congY n q ≠ q := by
  induction q using Quotient.inductionOn with
  | h g =>
      rw [congY_apply]
      intro hq
      exact not_mem_gammaPM_of_cube hn ST_cube ST_ne_one ST_ne_negOne g (mk_mul_eq_iff.mp hq)

/-- The two coset monodromies generate a transitive group of permutations of the cosets. -/
theorem congXY_transitive (s t : SL(2, ℤ) ⧸ gammaPM n) :
    ∃ σ ∈ Subgroup.closure ({congX n, congY n} : Set (Equiv.Perm (SL(2, ℤ) ⧸ gammaPM n))),
      σ s = t := by
  induction s using Quotient.inductionOn with
  | h g =>
      induction t using Quotient.inductionOn with
      | h h =>
          have hgen : Subgroup.closure ({ModularGroup.S, ModularGroup.S * ModularGroup.T} :
              Set SL(2, ℤ)) = ⊤ := by
            refine top_unique ?_
            rw [← _root_.SpecialLinearGroup.SL2Z_generators, Subgroup.closure_le]
            rintro x (rfl | hx)
            · exact Subgroup.subset_closure (Or.inl rfl)
            · simp only [Set.mem_singleton_iff] at hx
              subst hx
              have hmul := mul_mem
                (inv_mem (Subgroup.subset_closure (Or.inl rfl) :
                  ModularGroup.S ∈ Subgroup.closure ({ModularGroup.S,
                    ModularGroup.S * ModularGroup.T} : Set SL(2, ℤ))))
                (Subgroup.subset_closure (Or.inr rfl) :
                  ModularGroup.S * ModularGroup.T ∈ Subgroup.closure ({ModularGroup.S,
                    ModularGroup.S * ModularGroup.T} : Set SL(2, ℤ)))
              rwa [← mul_assoc, inv_mul_cancel, one_mul] at hmul
          have hmem : (h * g⁻¹) ∈ Subgroup.closure ({ModularGroup.S,
              ModularGroup.S * ModularGroup.T} : Set SL(2, ℤ)) := by
            rw [hgen]; trivial
          refine ⟨MulAction.toPermHom SL(2, ℤ) (SL(2, ℤ) ⧸ gammaPM n) (h * g⁻¹), ?_, ?_⟩
          · have himg : Subgroup.map (MulAction.toPermHom SL(2, ℤ) (SL(2, ℤ) ⧸ gammaPM n))
                (Subgroup.closure ({ModularGroup.S, ModularGroup.S * ModularGroup.T} :
                  Set SL(2, ℤ)))
                = Subgroup.closure ((MulAction.toPermHom SL(2, ℤ) (SL(2, ℤ) ⧸ gammaPM n)) ''
                  ({ModularGroup.S, ModularGroup.S * ModularGroup.T} : Set SL(2, ℤ))) :=
              MonoidHom.map_closure _ _
            have hin : MulAction.toPermHom SL(2, ℤ) (SL(2, ℤ) ⧸ gammaPM n) (h * g⁻¹) ∈
                Subgroup.map (MulAction.toPermHom SL(2, ℤ) (SL(2, ℤ) ⧸ gammaPM n))
                  (Subgroup.closure ({ModularGroup.S, ModularGroup.S * ModularGroup.T} :
                    Set SL(2, ℤ))) := ⟨h * g⁻¹, hmem, rfl⟩
            rw [himg] at hin
            refine Subgroup.closure_mono ?_ hin
            rintro _ ⟨x, hx, rfl⟩
            rcases hx with hx | hx
            · exact Or.inl (by rw [hx]; rfl)
            · simp only [Set.mem_singleton_iff] at hx
              exact Or.inr (by rw [hx]; rfl)
          · show (QuotientGroup.mk (h * g⁻¹ * g) : SL(2, ℤ) ⧸ gammaPM n) = QuotientGroup.mk h
            rw [mul_assoc, inv_mul_cancel, mul_one]

/-- **The principal congruence cover.**  For `n ≥ 3` the coset action of `SL(2,ℤ)` on
`Γ(n)·{±1}` is the monodromy of a connected unramified cover of the modular orbifold: the modular
curve `X(n)`. -/
noncomputable def congruenceModularCover (hn : 3 ≤ n) :
    ModularCover (SL(2, ℤ) ⧸ gammaPM n) where
  X := congX n
  Y := congY n
  freeX := by
    refine ⟨congX_sq, ?_⟩
    intro k hk0 hk2 q hfix
    interval_cases k
    exact congX_free hn q (by simpa using hfix)
  freeY := by
    refine ⟨congY_cube, ?_⟩
    intro k hk0 hk3 q hfix
    have hone : congY n q = q := by
      interval_cases k
      · simpa using hfix
      · have hsplit : (congY n) ^ 4 = (congY n) ^ 2 * (congY n) ^ 2 := by
          rw [← pow_add]
        have h4 : ((congY n) ^ 4) q = q := by
          rw [hsplit, Equiv.Perm.mul_apply, hfix, hfix]
        have hred : (congY n) ^ 4 = congY n := by
          rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, congY_cube, one_mul]
        rw [hred] at h4
        exact h4
    exact congY_free hn q hone
  transitive := congXY_transitive

/-- The `n` cosets of `Γ(n)·{±1}` represented by powers of `T` are distinct, so the index is at
least `n`. -/
theorem index_gammaPM_ge (hn : 3 ≤ n) : n ≤ (gammaPM n).index := by
  classical
  haveI := gammaPM_finiteIndex (n := n)
  have hinj : Function.Injective
      (fun k : Fin n => (QuotientGroup.mk (ModularGroup.T ^ ((k : ℕ) : ℤ))
        : SL(2, ℤ) ⧸ gammaPM n)) := by
    intro j k hjk
    rw [QuotientGroup.eq] at hjk
    have hpow : (ModularGroup.T ^ ((j : ℕ) : ℤ))⁻¹ * ModularGroup.T ^ ((k : ℕ) : ℤ)
        = ModularGroup.T ^ (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ)) := by
      rw [← _root_.zpow_neg, ← _root_.zpow_add]
      congr 1
      ring
    rw [hpow] at hjk
    set m : ℤ := ((k : ℕ) : ℤ) - ((j : ℕ) : ℤ) with hm
    have hdvd : (n : ℤ) ∣ m := by
      rcases mem_gammaPM.mp hjk with hA | hA
      · obtain ⟨-, h01, -, -⟩ := Gamma_mem.mp hA
        rw [ModularGroup.coe_T_zpow] at h01
        norm_num at h01
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h01
      · exfalso
        obtain ⟨h00, -, -, -⟩ := Gamma_mem.mp hA
        have hentry : ((slNegOne * ModularGroup.T ^ m : SL(2, ℤ))
            : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = -1 := by
          rw [Matrix.SpecialLinearGroup.coe_mul, slNegOne_coe, ModularGroup.coe_T_zpow]
          norm_num [Matrix.mul_fin_two]
        rw [hentry] at h00
        have h2 : ((2 : ℤ) : ZMod n) = 0 := by
          have := h00
          push_cast at this ⊢
          linear_combination -this
        have hdvd2 : (n : ℤ) ∣ 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by
          exact_mod_cast h2)
        have := Int.le_of_dvd (by norm_num) hdvd2
        have hn' : (3 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
        omega
    obtain ⟨c, hc⟩ := hdvd
    have hb1 : ((j : ℕ) : ℤ) < n := by exact_mod_cast j.isLt
    have hb2 : ((k : ℕ) : ℤ) < n := by exact_mod_cast k.isLt
    have hb3 : (0 : ℤ) ≤ ((j : ℕ) : ℤ) := by positivity
    have hb4 : (0 : ℤ) ≤ ((k : ℕ) : ℤ) := by positivity
    have hjk' : ((j : ℕ) : ℤ) = ((k : ℕ) : ℤ) := by
      rcases lt_trichotomy c 0 with hc' | hc' | hc'
      · nlinarith [hc, hm]
      · rw [hc', mul_zero] at hc
        omega
      · nlinarith [hc, hm]
    exact Fin.ext (by exact_mod_cast hjk')
  have hcard := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_fin] at hcard
  rw [Subgroup.index, Nat.card_eq_fintype_card]
  exact hcard

/-- **The modular curves `X(n)`.**  For `n ≥ 3` the principal congruence cover of the modular
orbifold is connected and unramified, and its degree — the index of `Γ(n)·{±1}` in `SL(2,ℤ)`,
i.e. the index of the torsion-free group `Γ(n)` in `PSL(2,ℤ)` — obeys the exact modular storage
law `D = 6(2g + s − 2)`. -/
theorem congruence_modular_capacity (hn : 3 ≤ n) :
    ∃ g : ℤ, ((gammaPM n).index : ℤ)
      = 6 * (2 * g + ((congruenceModularCover hn).cuspCount : ℤ) - 2) := by
  obtain ⟨g, -, hg⟩ := (congruenceModularCover hn).modular_capacity_exact
  refine ⟨g, ?_⟩
  rw [← hg]
  congr 1
  rw [Subgroup.index, Nat.card_eq_fintype_card]
  rfl

/-- The principal congruence covers have unbounded degree. -/
theorem exists_congruence_index_gt (B : ℕ) : ∃ n : ℕ, 3 ≤ n ∧ B < (gammaPM n).index := by
  refine ⟨max 3 (B + 1), le_max_left _ _, ?_⟩
  haveI : NeZero (max 3 (B + 1)) := ⟨by omega⟩
  have := index_gammaPM_ge (n := max 3 (B + 1)) (le_max_left _ _)
  omega

end Cover

end GaloisForLFunctions.HTGeometry
