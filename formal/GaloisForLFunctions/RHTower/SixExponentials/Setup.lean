import Mathlib

/-!
# Six exponentials: frequencies, sample points, and the product formula

Data: `x₀, x₁` rationally independent and `y₀, y₁, y₂` rationally independent complex numbers.
The auxiliary exponential polynomial uses the frequencies `λ_{ab} = (a+1) x₀ + (b+1) x₁` for
`a, b < L` and is sampled at the points `m₀' y₀ + m₁' y₁ + m₂' y₂` with `m_j' = m_j + 1 ≤ M`.
Rational independence makes both families injective, and the value of `exp(λ_{ab} · s_m)` is a
monomial in the six exponentials `exp(x_i y_j)`.
-/

open Complex Finset

namespace GaloisForLFunctions.RHTower.SixExponentials

/-- The data of the six exponentials theorem. -/
structure Data where
  x : Fin 2 → ℂ
  y : Fin 3 → ℂ
  hx : ∀ a b : ℤ, (a : ℂ) * x 0 + (b : ℂ) * x 1 = 0 → a = 0 ∧ b = 0
  hy : ∀ m : Fin 3 → ℤ, (∑ j, (m j : ℂ) * y j) = 0 → m = 0

namespace Data

variable (D : Data)

/-- The six exponentials `exp(x_i y_j)`. -/
noncomputable def E (i : Fin 2) (j : Fin 3) : ℂ := Complex.exp (D.x i * D.y j)

theorem E_ne_zero (i : Fin 2) (j : Fin 3) : D.E i j ≠ 0 := Complex.exp_ne_zero _

/-- Exponent vector of a frequency index. -/
def expo {L : ℕ} (ab : Fin L × Fin L) : Fin 2 → ℕ := ![ab.1.val + 1, ab.2.val + 1]

theorem expo_zero {L : ℕ} (ab : Fin L × Fin L) : expo ab 0 = ab.1.val + 1 := rfl

theorem expo_one {L : ℕ} (ab : Fin L × Fin L) : expo ab 1 = ab.2.val + 1 := rfl

theorem expo_pos {L : ℕ} (ab : Fin L × Fin L) (i : Fin 2) : 0 < expo ab i := by
  fin_cases i <;> simp [expo]

theorem expo_le {L : ℕ} (ab : Fin L × Fin L) (i : Fin 2) : expo ab i ≤ L := by
  fin_cases i <;> simp [expo]

/-- The frequency `(a+1) x₀ + (b+1) x₁`. -/
noncomputable def freq {L : ℕ} (ab : Fin L × Fin L) : ℂ := ∑ i, (expo ab i : ℂ) * D.x i

/-- The shifted sample multi-index `m_j + 1`. -/
def npt {M : ℕ} (m : Fin 3 → Fin M) (j : Fin 3) : ℕ := (m j).val + 1

theorem npt_pos {M : ℕ} (m : Fin 3 → Fin M) (j : Fin 3) : 0 < npt m j := Nat.succ_pos _

theorem npt_le {M : ℕ} (m : Fin 3 → Fin M) (j : Fin 3) : npt m j ≤ M := (m j).isLt

/-- The sample point `∑ (m_j + 1) y_j`. -/
noncomputable def pt {M : ℕ} (m : Fin 3 → Fin M) : ℂ := ∑ j, (npt m j : ℂ) * D.y j

theorem freq_injective (L : ℕ) : Function.Injective (fun ab : Fin L × Fin L => D.freq ab) := by
  intro ab ab' h
  simp only [freq, Fin.sum_univ_two, expo_zero, expo_one] at h
  have h1 := D.hx ((ab.1.val : ℤ) - ab'.1.val) ((ab.2.val : ℤ) - ab'.2.val) (by
    push_cast at h ⊢
    linear_combination h)
  obtain ⟨ha, hb⟩ := h1
  have ha' : ab.1.val = ab'.1.val := by omega
  have hb' : ab.2.val = ab'.2.val := by omega
  exact Prod.ext (Fin.ext ha') (Fin.ext hb')

theorem pt_injective (M : ℕ) : Function.Injective (fun m : Fin 3 → Fin M => D.pt m) := by
  intro m m' h
  simp only [pt, npt] at h
  have h1 := D.hy (fun j => ((m j).val : ℤ) - (m' j).val) (by
    push_cast
    simp only [sub_mul, Finset.sum_sub_distrib]
    have h' : ∑ j, ((((m j).val + 1 : ℕ) : ℂ)) * D.y j
        = ∑ j, ((((m' j).val + 1 : ℕ) : ℂ)) * D.y j := h
    push_cast at h'
    simp only [add_mul, one_mul, Finset.sum_add_distrib] at h'
    linear_combination h')
  funext j
  have := congrFun h1 j
  simp only [Pi.zero_apply] at this
  exact Fin.ext (by omega)

/-- `X = ‖x₀‖ + ‖x₁‖`. -/
noncomputable def X : ℝ := ∑ i, ‖D.x i‖

/-- `Y = ‖y₀‖ + ‖y₁‖ + ‖y₂‖`. -/
noncomputable def Y : ℝ := ∑ j, ‖D.y j‖

theorem X_nonneg : 0 ≤ D.X := Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem Y_nonneg : 0 ≤ D.Y := Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem y_ne_zero (j : Fin 3) : D.y j ≠ 0 := by
  intro h
  have := D.hy (Pi.single j 1) (by
    rw [Finset.sum_eq_single j]
    · simp [h]
    · intro b _ hb; simp [hb]
    · intro hj; exact absurd (Finset.mem_univ j) hj)
  have h1 := congrFun this j
  simp at h1

theorem Y_pos : 0 < D.Y := by
  have h : 0 < ‖D.y 0‖ := norm_pos_iff.mpr (D.y_ne_zero 0)
  have : ‖D.y 0‖ ≤ D.Y :=
    Finset.single_le_sum (f := fun j => ‖D.y j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ 0)
  linarith

theorem norm_freq_le {L : ℕ} (ab : Fin L × Fin L) : ‖D.freq ab‖ ≤ L * D.X := by
  unfold freq X
  calc ‖∑ i, (expo ab i : ℂ) * D.x i‖ ≤ ∑ i, ‖(expo ab i : ℂ) * D.x i‖ := norm_sum_le _ _
    _ ≤ ∑ i, (L : ℝ) * ‖D.x i‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast expo_le ab i) (norm_nonneg _)
    _ = L * ∑ i, ‖D.x i‖ := by rw [Finset.mul_sum]

theorem norm_pt_le {M : ℕ} (m : Fin 3 → Fin M) : ‖D.pt m‖ ≤ M * D.Y := by
  unfold pt Y
  calc ‖∑ j, (npt m j : ℂ) * D.y j‖ ≤ ∑ j, ‖(npt m j : ℂ) * D.y j‖ := norm_sum_le _ _
    _ ≤ ∑ j, (M : ℝ) * ‖D.y j‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast npt_le m j) (norm_nonneg _)
    _ = M * ∑ j, ‖D.y j‖ := by rw [Finset.mul_sum]

/-- The exponent of `exp(x_i y_j)` in `exp(λ_{ab} s_m)`. -/
def ex {L M : ℕ} (ab : Fin L × Fin L) (m : Fin 3 → Fin M) (i : Fin 2) (j : Fin 3) : ℕ :=
  expo ab i * npt m j

theorem ex_le {L M : ℕ} (ab : Fin L × Fin L) (m : Fin 3 → Fin M) (i : Fin 2) (j : Fin 3) :
    ex ab m i j ≤ L * M :=
  Nat.mul_le_mul (expo_le ab i) (npt_le m j)

theorem sum_ex_le {L M : ℕ} (ab : Fin L × Fin L) (m : Fin 3 → Fin M) :
    ∑ i, ∑ j, ex ab m i j ≤ 6 * L * M := by
  calc ∑ i : Fin 2, ∑ j : Fin 3, ex ab m i j ≤ ∑ i : Fin 2, ∑ j : Fin 3, L * M :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ex_le ab m i j
    _ = 6 * L * M := by simp [Finset.sum_const, Finset.card_univ]; ring

/-- **Product formula.**  `exp(λ_{ab} s_m) = ∏_{i,j} exp(x_i y_j)^{e_i(ab) n_j(m)}`. -/
theorem exp_freq_mul_pt {L M : ℕ} (ab : Fin L × Fin L) (m : Fin 3 → Fin M) :
    Complex.exp (D.freq ab * D.pt m) = ∏ i, ∏ j, D.E i j ^ ex ab m i j := by
  have h : D.freq ab * D.pt m = ∑ i, ∑ j, ((ex ab m i j : ℕ) : ℂ) * (D.x i * D.y j) := by
    unfold freq pt ex
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [h, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Complex.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Complex.exp_nat_mul]
  rfl

end Data

end GaloisForLFunctions.RHTower.SixExponentials
