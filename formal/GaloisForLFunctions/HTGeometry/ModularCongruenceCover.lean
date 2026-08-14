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
  · have : (((A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod n) = 0 := by
      push_cast
      exact h01
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  · have : (((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod n) = 0 := by
      push_cast
      exact h10
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
      have hswap : A * B = (slNegOne * A) * (slNegOne * B) := by
        rw [← mul_assoc, mul_assoc slNegOne A slNegOne, ← (slNegOne_central A).eq,
          ← mul_assoc, ← mul_assoc, slNegOne_mul_self, one_mul]
      rw [hswap]
      exact mul_mem hA hB
  inv_mem' := by
    rintro A (hA | hA)
    · exact Or.inl (inv_mem hA)
    · refine Or.inr ?_
      have hswap : slNegOne * A⁻¹ = (slNegOne * A)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right slNegOne_mul_self,
          (slNegOne_central A⁻¹).eq]
      rw [hswap]
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
    rw [hstep, hsq, ← (slNegOne_central g⁻¹).eq, mul_assoc, mul_inv_cancel, mul_one]
  have hconj : ∀ B : SL(2, ℤ), B = 1 ∨ B = slNegOne → g⁻¹ * C * g = B → False := by
    rintro B (rfl | rfl) hB
    · exact hC1 (by
        have := congrArg (fun x => g * x * g⁻¹) hB
        simpa [mul_assoc] using this)
    · exact hCm (by
        have := congrArg (fun x => g * x * g⁻¹) hB
        simp only [mul_one] at this
        rw [← (slNegOne_central g).eq] at this
        simpa [mul_assoc] using this)
  rcases mem_gammaPM.mp hmem with hA | hA
  · have := gamma_sq_mem_slPM hn hA (by rw [hA2]; exact Or.inr rfl)
    exact hconj _ (mem_slPM.mp this) rfl
  · have hB2 : (slNegOne * (g⁻¹ * C * g)) * (slNegOne * (g⁻¹ * C * g)) = slNegOne := by
      have hstep : (slNegOne * (g⁻¹ * C * g)) * (slNegOne * (g⁻¹ * C * g))
          = (slNegOne * slNegOne) * ((g⁻¹ * C * g) * (g⁻¹ * C * g)) := by
        rw [mul_assoc, ← mul_assoc (g⁻¹ * C * g) slNegOne,
          ← (slNegOne_central (g⁻¹ * C * g)).eq, mul_assoc, ← mul_assoc]
      rw [hstep, slNegOne_mul_self, one_mul, hA2]
    have hmem2 := gamma_sq_mem_slPM hn hA (by rw [hB2]; exact Or.inr rfl)
    rcases mem_slPM.mp hmem2 with h' | h'
    · refine hconj slNegOne (Or.inr rfl) ?_
      have := congrArg (fun x => slNegOne * x) h'
      simpa [← mul_assoc, slNegOne_mul_self] using this.symm
    · refine hconj 1 (Or.inl rfl) ?_
      have := congrArg (fun x => slNegOne * x) h'
      simpa [← mul_assoc, slNegOne_mul_self] using this.symm

/-- Conjugates of a cube root of `−1` avoid `Γ(n)·{±1}` for `n ≥ 3`. -/
theorem not_mem_gammaPM_of_cube (hn : 3 ≤ n) {C : SL(2, ℤ)} (hcube : C * C * C = slNegOne)
    (hC1 : C ≠ 1) (hCm : C ≠ slNegOne) (g : SL(2, ℤ)) : g⁻¹ * C * g ∉ gammaPM n := by
  intro hmem
  have hA3 : (g⁻¹ * C * g) * (g⁻¹ * C * g) * (g⁻¹ * C * g) = slNegOne := by
    have hstep : (g⁻¹ * C * g) * (g⁻¹ * C * g) * (g⁻¹ * C * g) = g⁻¹ * (C * C * C) * g := by
      group
    rw [hstep, hcube, ← (slNegOne_central g⁻¹).eq, mul_assoc, mul_inv_cancel, mul_one]
  have hconj : ∀ B : SL(2, ℤ), B = 1 ∨ B = slNegOne → g⁻¹ * C * g = B → False := by
    rintro B (rfl | rfl) hB
    · exact hC1 (by
        have := congrArg (fun x => g * x * g⁻¹) hB
        simpa [mul_assoc] using this)
    · exact hCm (by
        have := congrArg (fun x => g * x * g⁻¹) hB
        simp only [mul_one] at this
        rw [← (slNegOne_central g).eq] at this
        simpa [mul_assoc] using this)
  rcases mem_gammaPM.mp hmem with hA | hA
  · have := gamma_cube_mem_slPM hn hA (by rw [hA3]; exact Or.inr rfl)
    exact hconj _ (mem_slPM.mp this) rfl
  · set A := g⁻¹ * C * g with hAdef
    have hB3 : (slNegOne * A) * (slNegOne * A) * (slNegOne * A) = 1 := by
      have hstep : (slNegOne * A) * (slNegOne * A) * (slNegOne * A)
          = (slNegOne * slNegOne * slNegOne) * (A * A * A) := by
        have h1 : Commute slNegOne A := slNegOne_central A
        simp only [mul_assoc]
        rw [← h1.eq]
        simp only [← mul_assoc]
        rw [mul_assoc slNegOne slNegOne A, ← (slNegOne_central A).eq]
        group
      rw [hstep, hA3]
      rw [mul_assoc, slNegOne_mul_self, mul_one, slNegOne_mul_self]
    have hmem2 := gamma_cube_mem_slPM hn hA (by rw [hB3]; exact Or.inl rfl)
    rcases mem_slPM.mp hmem2 with h' | h'
    · refine hconj slNegOne (Or.inr rfl) ?_
      have := congrArg (fun x => slNegOne * x) h'
      simpa [← mul_assoc, slNegOne_mul_self] using this.symm
    · refine hconj 1 (Or.inl rfl) ?_
      have := congrArg (fun x => slNegOne * x) h'
      simpa [← mul_assoc, slNegOne_mul_self] using this.symm

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

theorem ST_ne_one : ModularGroup.S * ModularGroup.T ≠ 1 := by
  intro h
  have := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
  simp [ST_coe] at this

theorem ST_ne_negOne : ModularGroup.S * ModularGroup.T ≠ slNegOne := by
  intro h
  have := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
  simp [ST_coe] at this

/-- The central element acts trivially on the cosets of `Γ(n)·{±1}`. -/
theorem mk_negOne_mul (g : SL(2, ℤ)) :
    (QuotientGroup.mk (slNegOne * g) : SL(2, ℤ) ⧸ gammaPM n) = QuotientGroup.mk g := by
  rw [QuotientGroup.eq]
  have hrw : (slNegOne * g)⁻¹ * g = slNegOne := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right slNegOne_mul_self, mul_assoc,
      ← (slNegOne_central g).eq, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hrw]
  exact slNegOne_mem_gammaPM

/-- A coset is fixed by left translation exactly when the conjugate lies in the subgroup. -/
theorem mk_mul_eq_iff {C g : SL(2, ℤ)} :
    (QuotientGroup.mk (C * g) : SL(2, ℤ) ⧸ gammaPM n) = QuotientGroup.mk g
      ↔ g⁻¹ * C * g ∈ gammaPM n := by
  rw [QuotientGroup.eq]
  constructor
  · intro h
    have hrw : g⁻¹ * C * g = ((C * g)⁻¹ * g)⁻¹ := by
      rw [mul_inv_rev, inv_inv, mul_inv_rev, inv_inv, mul_assoc]
    rw [hrw]
    exact inv_mem h
  · intro h
    have hrw : (C * g)⁻¹ * g = (g⁻¹ * C * g)⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, inv_inv, mul_assoc]
    rw [hrw]
    exact inv_mem h

variable [NeZero n]

theorem gammaPM_finiteIndex : (gammaPM n).FiniteIndex :=
  haveI : (Gamma n).FiniteIndex := CongruenceSubgroup.instFiniteIndexGamma
  Subgroup.finiteIndex_of_le gamma_le_gammaPM

noncomputable instance : Fintype (SL(2, ℤ) ⧸ gammaPM n) :=
  haveI := gammaPM_finiteIndex (n := n)
  Subgroup.fintypeQuotientOfFiniteIndex

noncomputable instance : DecidableEq (SL(2, ℤ) ⧸ gammaPM n) := Classical.decEq _

/-- **The principal congruence cover.**  For `n ≥ 3` the coset action of `SL(2,ℤ)` on
`Γ(n)·{±1}` is the monodromy of a connected unramified cover of the modular orbifold: the modular
curve `X(n)`. -/
noncomputable def congruenceModularCover (hn : 3 ≤ n) :
    ModularCover (SL(2, ℤ) ⧸ gammaPM n) where
  X := MulAction.toPermHom SL(2, ℤ) (SL(2, ℤ) ⧸ gammaPM n) ModularGroup.S
  Y := MulAction.toPermHom SL(2, ℤ) (SL(2, ℤ) ⧸ gammaPM n) (ModularGroup.S * ModularGroup.T)
  freeX := by
    constructor
    · rw [← map_pow]
      have hsq : ModularGroup.S ^ 2 = slNegOne := by
        rw [pow_two]; exact S_mul_S
      rw [hsq]
      ext q
      refine Quotient.inductionOn q fun g => ?_
      exact mk_negOne_mul g
    · intro k hk0 hk2 q
      interval_cases k
      refine Quotient.inductionOn q fun g => ?_
      simp only [pow_one]
      intro hfix
      have : (QuotientGroup.mk (ModularGroup.S * g) : SL(2, ℤ) ⧸ gammaPM n)
          = QuotientGroup.mk g := hfix
      exact not_mem_gammaPM_of_sq hn S_mul_S S_ne_one S_ne_negOne g (mk_mul_eq_iff.mp this)
  freeY := by
    constructor
    · rw [← map_pow]
      have hcube : (ModularGroup.S * ModularGroup.T) ^ 3 = slNegOne := by
        rw [pow_succ, pow_succ, pow_one]; exact ST_cube
      rw [hcube]
      ext q
      refine Quotient.inductionOn q fun g => ?_
      exact mk_negOne_mul g
    · intro k hk0 hk3 q hfix
      -- a fixed point of `Y^2` is a fixed point of `Y`, since `Y^3 = 1`
      have hbase : ∀ g : SL(2, ℤ),
          (QuotientGroup.mk (ModularGroup.S * ModularGroup.T * g) : SL(2, ℤ) ⧸ gammaPM n)
            ≠ QuotientGroup.mk g := by
        intro g hg
        exact not_mem_gammaPM_of_cube hn ST_cube ST_ne_one ST_ne_negOne g
          (mk_mul_eq_iff.mp hg)
      interval_cases k
      · refine Quotient.inductionOn q (fun g => ?_) hfix
        intro hg
        exact hbase g hg
      · -- `k = 2`
        refine Quotient.inductionOn q (fun g => ?_) hfix
        intro hg
        refine hbase (ModularGroup.S * ModularGroup.T * g) ?_
        have h2 : ((ModularGroup.S * ModularGroup.T) ^ 2 * g)
            = ModularGroup.S * ModularGroup.T * (ModularGroup.S * ModularGroup.T * g) := by
          rw [pow_two, mul_assoc]
        have hq : (QuotientGroup.mk ((ModularGroup.S * ModularGroup.T) ^ 2 * g)
            : SL(2, ℤ) ⧸ gammaPM n) = QuotientGroup.mk g := hg
        rw [h2] at hq
        have h3 : (QuotientGroup.mk (ModularGroup.S * ModularGroup.T *
            (ModularGroup.S * ModularGroup.T * (ModularGroup.S * ModularGroup.T * g)))
            : SL(2, ℤ) ⧸ gammaPM n)
            = QuotientGroup.mk (ModularGroup.S * ModularGroup.T * g) := by
          rw [hq]
        have h4 : ModularGroup.S * ModularGroup.T *
            (ModularGroup.S * ModularGroup.T * (ModularGroup.S * ModularGroup.T * g))
            = slNegOne * g := by
          rw [← mul_assoc, ← mul_assoc, ST_cube]
        rw [h4, mk_negOne_mul] at h3
        exact h3.symm
  transitive := by
    intro s t
    refine Quotient.inductionOn₂ s t fun g h => ?_
    have hgen : Subgroup.closure ({ModularGroup.S, ModularGroup.S * ModularGroup.T} :
        Set SL(2, ℤ)) = ⊤ := by
      refine top_unique ?_
      rw [← Matrix.SpecialLinearGroup.SL2Z_generators, Subgroup.closure_le]
      rintro x (rfl | hx)
      · exact Subgroup.subset_closure (Or.inl rfl)
      · simp only [Set.mem_singleton_iff] at hx
        subst hx
        have hT : ModularGroup.T = ModularGroup.S⁻¹ * (ModularGroup.S * ModularGroup.T) := by
          rw [← mul_assoc, inv_mul_cancel, one_mul]
        rw [hT]
        exact mul_mem (inv_mem (Subgroup.subset_closure (Or.inl rfl)))
          (Subgroup.subset_closure (Or.inr rfl))
    have hmem : (h * g⁻¹) ∈ Subgroup.closure ({ModularGroup.S,
        ModularGroup.S * ModularGroup.T} : Set SL(2, ℤ)) := by
      rw [hgen]; trivial
    refine ⟨MulAction.toPermHom SL(2, ℤ) (SL(2, ℤ) ⧸ gammaPM n) (h * g⁻¹), ?_, ?_⟩
    · have himg : Subgroup.map (MulAction.toPermHom SL(2, ℤ) (SL(2, ℤ) ⧸ gammaPM n))
          (Subgroup.closure ({ModularGroup.S, ModularGroup.S * ModularGroup.T} : Set SL(2, ℤ)))
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
      · exact Or.inl (by rw [hx])
      · simp only [Set.mem_singleton_iff] at hx
        exact Or.inr (by rw [hx])
    · show (QuotientGroup.mk (h * g⁻¹ * g) : SL(2, ℤ) ⧸ gammaPM n) = QuotientGroup.mk h
      rw [mul_assoc, inv_mul_cancel, mul_one]

end Cover

end GaloisForLFunctions.HTGeometry
