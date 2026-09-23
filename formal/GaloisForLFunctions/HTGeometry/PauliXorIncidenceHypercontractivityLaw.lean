import Mathlib
import GaloisForLFunctions.HTGeometry.ChoiShortcutEnergyDefectKurtosisLaw
import GaloisForLFunctions.QuantumAlg.Primitives.QNN.Algebras.PauliAlgebra

/-!
# Dimension-free fourth incidence for fixed-weight Pauli labels

This file proves an elementary, deliberately nonsharp hypercontractive law for the phase-free
XOR incidence of Pauli coefficient families.  A four-linear Cauchy--Schwarz law tensorizes over
qubits.  The one-qubit four-point expansion has no term with exactly one nonidentity label; this
missing linear term makes coordinate induction close with a dimension-independent constant.

For nonnegative coefficients supported on Pauli weight at most `q`, the final theorem is

`fourthIncidence c <= (9^q * sqrt (sum_s c_s^(2 : ℕ)))^(4 : ℕ)`.

No probabilistic, spectral-gap, or asymptotic hypothesis is used.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {G : Type*} [Fintype G] [AddCommGroup G]

noncomputable def corr (f g : G → ℝ) (u : G) : ℝ :=
  ∑ x, f x * g (x + u)

noncomputable def corrTripleEquiv : (G × G × G) ≃ (G × G × G) where
  toFun p := (p.2.2 - p.2.1, p.2.1, p.2.1 + p.1)
  invFun p := (p.2.2 - p.2.1, p.2.1, p.2.1 + p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

theorem sum_corr_sq_eq (f g : G → ℝ) :
    (∑ u, corr f g u ^ (2 : ℕ)) = ∑ v, corr f f v * corr g g v := by
  classical
  calc
    (∑ u, corr f g u ^ (2 : ℕ)) =
        ∑ p : G × G × G,
          f p.2.1 * g (p.2.1 + p.1) * (f p.2.2 * g (p.2.2 + p.1)) := by
      simp only [Fintype.sum_prod_type, corr, sq, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      conv_lhs => rw [Finset.sum_comm]
    _ = ∑ p : G × G × G,
          (fun q : G × G × G =>
            f q.2.1 * f (q.2.1 + q.1) * (g q.2.2 * g (q.2.2 + q.1)))
            (corrTripleEquiv (G := G) p) := by
      apply Finset.sum_congr rfl
      intro p hp
      rcases p with ⟨u, x, y⟩
      dsimp [corrTripleEquiv]
      ring_nf
      congr 2 <;> abel
    _ = ∑ p : G × G × G,
          f p.2.1 * f (p.2.1 + p.1) * (g p.2.2 * g (p.2.2 + p.1)) := by
      exact Equiv.sum_comp (corrTripleEquiv (G := G))
        (fun p : G × G × G =>
          f p.2.1 * f (p.2.1 + p.1) * (g p.2.2 * g (p.2.2 + p.1)))
    _ = ∑ v, corr f f v * corr g g v := by
      simp only [Fintype.sum_prod_type, corr, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      conv_rhs => rw [Finset.sum_comm]

noncomputable def fourthIncidence (f : G → ℝ) : ℝ :=
  ∑ u, corr f f u ^ (2 : ℕ)

noncomputable def crossIncidence (f₁ f₂ f₃ f₄ : G → ℝ) : ℝ :=
  ∑ u, corr f₁ f₂ u * corr f₃ f₄ u

theorem fourthIncidence_nonneg (f : G → ℝ) : 0 ≤ fourthIncidence f := by
  unfold fourthIncidence
  positivity

theorem corr_nonneg {f g : G → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (u : G) :
    0 ≤ corr f g u := by
  unfold corr
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hf x) (hg (x + u))

theorem crossIncidence_nonneg {f₁ f₂ f₃ f₄ : G → ℝ}
    (h₁ : ∀ x, 0 ≤ f₁ x) (h₂ : ∀ x, 0 ≤ f₂ x)
    (h₃ : ∀ x, 0 ≤ f₃ x) (h₄ : ∀ x, 0 ≤ f₄ x) :
    0 ≤ crossIncidence f₁ f₂ f₃ f₄ := by
  unfold crossIncidence
  exact Finset.sum_nonneg fun u _ =>
    mul_nonneg (corr_nonneg h₁ h₂ u) (corr_nonneg h₃ h₄ u)

theorem corr_normSq_sq_le (f g : G → ℝ) :
    (∑ u, corr f g u ^ (2 : ℕ)) ^ (2 : ℕ) ≤ fourthIncidence f * fourthIncidence g := by
  rw [sum_corr_sq_eq]
  simpa only [fourthIncidence] using
    (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset G)
      (fun u => corr f f u) (fun u => corr g g u))

theorem crossIncidence_pow_four_le (f₁ f₂ f₃ f₄ : G → ℝ) :
    crossIncidence f₁ f₂ f₃ f₄ ^ (4 : ℕ) ≤
      fourthIncidence f₁ * fourthIncidence f₂ * fourthIncidence f₃ * fourthIncidence f₄ := by
  let S₁₂ : ℝ := ∑ u, corr f₁ f₂ u ^ (2 : ℕ)
  let S₃₄ : ℝ := ∑ u, corr f₃ f₄ u ^ (2 : ℕ)
  have hcross : crossIncidence f₁ f₂ f₃ f₄ ^ (2 : ℕ) ≤ S₁₂ * S₃₄ := by
    simpa only [crossIncidence, S₁₂, S₃₄] using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset G)
        (fun u => corr f₁ f₂ u) (fun u => corr f₃ f₄ u))
  have hS₁₂ : S₁₂ ^ (2 : ℕ) ≤ fourthIncidence f₁ * fourthIncidence f₂ := by
    simpa only [S₁₂] using corr_normSq_sq_le f₁ f₂
  have hS₃₄ : S₃₄ ^ (2 : ℕ) ≤ fourthIncidence f₃ * fourthIncidence f₄ := by
    simpa only [S₃₄] using corr_normSq_sq_le f₃ f₄
  have hS₁₂0 : 0 ≤ S₁₂ := by dsimp [S₁₂]; positivity
  have hS₃₄0 : 0 ≤ S₃₄ := by dsimp [S₃₄]; positivity
  calc
    crossIncidence f₁ f₂ f₃ f₄ ^ (4 : ℕ) = (crossIncidence f₁ f₂ f₃ f₄ ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
    _ ≤ (S₁₂ * S₃₄) ^ (2 : ℕ) := pow_le_pow_left₀ (sq_nonneg _) hcross 2
    _ = S₁₂ ^ (2 : ℕ) * S₃₄ ^ (2 : ℕ) := by ring
    _ ≤ (fourthIncidence f₁ * fourthIncidence f₂) *
        (fourthIncidence f₃ * fourthIncidence f₄) :=
      mul_le_mul hS₁₂ hS₃₄ (sq_nonneg S₃₄)
        (mul_nonneg (fourthIncidence_nonneg f₁) (fourthIncidence_nonneg f₂))
    _ = _ := by ring

theorem crossIncidence_le_of_fourth_bounds {f₁ f₂ f₃ f₄ : G → ℝ}
    {A₁ A₂ A₃ A₄ : ℝ}
    (h₁ : ∀ x, 0 ≤ f₁ x) (h₂ : ∀ x, 0 ≤ f₂ x)
    (h₃ : ∀ x, 0 ≤ f₃ x) (h₄ : ∀ x, 0 ≤ f₄ x)
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hA₃ : 0 ≤ A₃) (hA₄ : 0 ≤ A₄)
    (hb₁ : fourthIncidence f₁ ≤ A₁ ^ (4 : ℕ))
    (hb₂ : fourthIncidence f₂ ≤ A₂ ^ (4 : ℕ))
    (hb₃ : fourthIncidence f₃ ≤ A₃ ^ (4 : ℕ))
    (hb₄ : fourthIncidence f₄ ≤ A₄ ^ (4 : ℕ)) :
    crossIncidence f₁ f₂ f₃ f₄ ≤ A₁ * A₂ * A₃ * A₄ := by
  have hcross0 := crossIncidence_nonneg h₁ h₂ h₃ h₄
  have h12 : fourthIncidence f₁ * fourthIncidence f₂ ≤ A₁ ^ (4 : ℕ) * A₂ ^ (4 : ℕ) :=
    mul_le_mul hb₁ hb₂ (fourthIncidence_nonneg f₂) (pow_nonneg hA₁ 4)
  have h123 : fourthIncidence f₁ * fourthIncidence f₂ * fourthIncidence f₃ ≤
      A₁ ^ (4 : ℕ) * A₂ ^ (4 : ℕ) * A₃ ^ (4 : ℕ) :=
    mul_le_mul h12 hb₃ (fourthIncidence_nonneg f₃)
      (mul_nonneg (pow_nonneg hA₁ 4) (pow_nonneg hA₂ 4))
  have h1234 : fourthIncidence f₁ * fourthIncidence f₂ * fourthIncidence f₃ *
      fourthIncidence f₄ ≤ A₁ ^ (4 : ℕ) * A₂ ^ (4 : ℕ) * A₃ ^ (4 : ℕ) * A₄ ^ (4 : ℕ) :=
    mul_le_mul h123 hb₄ (fourthIncidence_nonneg f₄)
      (mul_nonneg (mul_nonneg (pow_nonneg hA₁ 4) (pow_nonneg hA₂ 4)) (pow_nonneg hA₃ 4))
  apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num)
    (mul_nonneg (mul_nonneg (mul_nonneg hA₁ hA₂) hA₃) hA₄)
  calc
    crossIncidence f₁ f₂ f₃ f₄ ^ (4 : ℕ) ≤
        fourthIncidence f₁ * fourthIncidence f₂ * fourthIncidence f₃ * fourthIncidence f₄ :=
      crossIncidence_pow_four_le f₁ f₂ f₃ f₄
    _ ≤ A₁ ^ (4 : ℕ) * A₂ ^ (4 : ℕ) * A₃ ^ (4 : ℕ) * A₄ ^ (4 : ℕ) := h1234
    _ = (A₁ * A₂ * A₃ * A₄) ^ (4 : ℕ) := by ring

section Tensor

variable {A : Type*} [Fintype A] [AddCommGroup A]

noncomputable def fiber (F : A × G → ℝ) (a : A) : G → ℝ := fun x => F (a, x)

theorem corr_product (F : A × G → ℝ) (u : A × G) :
    corr F F u = ∑ a, corr (fiber F a) (fiber F (a + u.1)) u.2 := by
  classical
  rcases u with ⟨u, v⟩
  simp only [corr, fiber, Fintype.sum_prod_type]
  change (∑ x, ∑ y, F (x, y) * F (x + u, y + v)) = _
  rfl

theorem fourthIncidence_product_le {F : A × G → ℝ} {B : A → ℝ}
    (hF : ∀ z, 0 ≤ F z) (hB : ∀ a, 0 ≤ B a)
    (hbound : ∀ a, fourthIncidence (fiber F a) ≤ B a ^ (4 : ℕ)) :
    fourthIncidence F ≤ fourthIncidence B := by
  classical
  have hBexpand : fourthIncidence B =
      ∑ u, ∑ a, ∑ b, B a * B (a + u) * (B b * B (b + u)) := by
    simp only [fourthIncidence, corr, sq, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    conv_lhs => rw [Finset.sum_comm]
  rw [hBexpand]
  unfold fourthIncidence
  rw [Fintype.sum_prod_type]
  simp_rw [corr_product]
  simp only [sq, Finset.sum_mul, Finset.mul_sum]
  let K : G → A → A → A → ℝ := fun y u a b =>
    corr (fiber F b) (fiber F (b + u)) y *
      corr (fiber F a) (fiber F (a + u)) y
  change (∑ u, ∑ y, ∑ a, ∑ b, K y u a b) ≤
    ∑ u, ∑ a, ∑ b, B a * B (a + u) * (B b * B (b + u))
  apply Finset.sum_le_sum
  intro u hu
  rw [show (∑ y, ∑ a, ∑ b, K y u a b) =
      ∑ a, ∑ y, ∑ b, K y u a b from Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a ha
  rw [show (∑ y, ∑ b, K y u a b) =
      ∑ b, ∑ y, K y u a b from Finset.sum_comm]
  apply Finset.sum_le_sum
  intro b hb
  change crossIncidence (fiber F b) (fiber F (b + u))
      (fiber F a) (fiber F (a + u)) ≤ _
  have hfa : ∀ x, 0 ≤ fiber F a x := fun x => hF (a, x)
  have hfau : ∀ x, 0 ≤ fiber F (a + u) x := fun x => hF (a + u, x)
  have hfb : ∀ x, 0 ≤ fiber F b x := fun x => hF (b, x)
  have hfbu : ∀ x, 0 ≤ fiber F (b + u) x := fun x => hF (b + u, x)
  simpa only [mul_comm, mul_left_comm, mul_assoc] using
    (crossIncidence_le_of_fourth_bounds hfb hfbu hfa hfau
      (hB b) (hB (b + u)) (hB a) (hB (a + u))
      (hbound b) (hbound (b + u)) (hbound a) (hbound (a + u)))

end Tensor

abbrev QubitLabel := Fin 2 × Fin 2


theorem qubitLabel_fourthIncidence_le (B : QubitLabel → ℝ)
    (hB : ∀ a, 0 ≤ B a) :
    fourthIncidence B ≤
      B (0, 0) ^ (4 : ℕ) +
        6 * B (0, 0) ^ (2 : ℕ) * (B (1, 0) + B (0, 1) + B (1, 1)) ^ (2 : ℕ) +
        4 * B (0, 0) * (B (1, 0) + B (0, 1) + B (1, 1)) ^ (3 : ℕ) +
        (B (1, 0) + B (0, 1) + B (1, 1)) ^ (4 : ℕ) := by
  simp only [fourthIncidence, corr, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num [Fin.add_def]
  ring_nf
  have h0 := hB (0, 0)
  have h1 := hB (1, 0)
  have h2 := hB (0, 1)
  have h3 := hB (1, 1)
  rw [← sub_nonneg]
  ring_nf
  positivity

theorem quartic_missing_linear_absorption {A B C X Y : ℝ}
    (hC : 0 ≤ C) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hA : A = C * X) (hB0 : 0 ≤ B) (hB : B ≤ C * Y / 3) :
    A ^ (4 : ℕ) + 6 * A ^ (2 : ℕ) * B ^ (2 : ℕ) + 4 * A * B ^ (3 : ℕ) + B ^ (4 : ℕ) ≤
      (C * Real.sqrt (X ^ (2 : ℕ) + Y ^ (2 : ℕ))) ^ (4 : ℕ) := by
  subst A
  have hCY : 0 ≤ C * Y / 3 := by positivity
  have hB2 : B ^ (2 : ℕ) ≤ (C * Y / 3) ^ (2 : ℕ) := pow_le_pow_left₀ hB0 hB 2
  have hB3 : B ^ (3 : ℕ) ≤ (C * Y / 3) ^ (3 : ℕ) := pow_le_pow_left₀ hB0 hB 3
  have hB4 : B ^ (4 : ℕ) ≤ (C * Y / 3) ^ (4 : ℕ) := pow_le_pow_left₀ hB0 hB 4
  have hpoly :
      (C * X) ^ (4 : ℕ) + 6 * (C * X) ^ (2 : ℕ) * B ^ (2 : ℕ) + 4 * (C * X) * B ^ (3 : ℕ) + B ^ (4 : ℕ) ≤
        (C * X) ^ (4 : ℕ) + 6 * (C * X) ^ (2 : ℕ) * (C * Y / 3) ^ (2 : ℕ) +
          4 * (C * X) * (C * Y / 3) ^ (3 : ℕ) + (C * Y / 3) ^ (4 : ℕ) := by
    gcongr
  have hXY : 2 * X * Y ≤ X ^ (2 : ℕ) + Y ^ (2 : ℕ) := by nlinarith [sq_nonneg (X - Y)]
  have hXYscaled : 2 * X * Y * Y ^ (2 : ℕ) ≤ (X ^ (2 : ℕ) + Y ^ (2 : ℕ)) * Y ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_right hXY (sq_nonneg Y)
  have hcore :
      X ^ (4 : ℕ) + 6 * X ^ (2 : ℕ) * (Y / 3) ^ (2 : ℕ) + 4 * X * (Y / 3) ^ (3 : ℕ) + (Y / 3) ^ (4 : ℕ) ≤
        (X ^ (2 : ℕ) + Y ^ (2 : ℕ)) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (X * Y), sq_nonneg (Y ^ (2 : ℕ)), hXYscaled]
  have hsum : 0 ≤ X ^ (2 : ℕ) + Y ^ (2 : ℕ) := by positivity
  have hsqrt : Real.sqrt (X ^ (2 : ℕ) + Y ^ (2 : ℕ)) ^ (2 : ℕ) = X ^ (2 : ℕ) + Y ^ (2 : ℕ) :=
    Real.sq_sqrt hsum
  calc
    (C * X) ^ (4 : ℕ) + 6 * (C * X) ^ (2 : ℕ) * B ^ (2 : ℕ) + 4 * (C * X) * B ^ (3 : ℕ) + B ^ (4 : ℕ) ≤ _ := hpoly
    _ = C ^ (4 : ℕ) *
        (X ^ (4 : ℕ) + 6 * X ^ (2 : ℕ) * (Y / 3) ^ (2 : ℕ) + 4 * X * (Y / 3) ^ (3 : ℕ) + (Y / 3) ^ (4 : ℕ)) := by ring
    _ ≤ C ^ (4 : ℕ) * (X ^ (2 : ℕ) + Y ^ (2 : ℕ)) ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left hcore (pow_nonneg hC 4)
    _ = C ^ (4 : ℕ) * (Real.sqrt (X ^ (2 : ℕ) + Y ^ (2 : ℕ)) ^ (2 : ℕ)) ^ (2 : ℕ) := by rw [hsqrt]
    _ = (C * Real.sqrt (X ^ (2 : ℕ) + Y ^ (2 : ℕ))) ^ (4 : ℕ) := by ring

theorem corr_comp_addEquiv {K : Type*} [Fintype K] [AddCommGroup K]
    (e : K ≃+ G) (f g : G → ℝ) (u : K) :
    corr (f ∘ e) (g ∘ e) u = corr f g (e u) := by
  classical
  unfold corr
  change (∑ x, f (e x) * g (e (x + u))) = _
  simp_rw [e.map_add]
  exact Equiv.sum_comp e.toEquiv (fun x => f x * g (x + e u))

theorem fourthIncidence_comp_addEquiv {K : Type*} [Fintype K] [AddCommGroup K]
    (e : K ≃+ G) (f : G → ℝ) :
    fourthIncidence (f ∘ e) = fourthIncidence f := by
  classical
  unfold fourthIncidence
  simp_rw [corr_comp_addEquiv e f f]
  exact Equiv.sum_comp e.toEquiv (fun u => corr f f u ^ (2 : ℕ))

abbrev QubitCube (n : ℕ) := Fin n → QubitLabel

noncomputable def qubitCubeSuccAddEquiv (n : ℕ) :
    (QubitLabel × QubitCube n) ≃+ QubitCube (n + 1) where
  toEquiv := Fin.consEquiv (fun _ : Fin (n + 1) => QubitLabel)
  map_add' x y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

noncomputable def cubeWeight {n : ℕ} (s : QubitCube n) : ℕ :=
  ∑ i, if s i = 0 then 0 else 1

theorem cubeWeight_cons {n : ℕ} (a : QubitLabel) (s : QubitCube n) :
    cubeWeight (Fin.cons a s) = (if a = 0 then 0 else 1) + cubeWeight s := by
  simp [cubeWeight, Fin.sum_univ_succ]

theorem one_le_cubeWeight_of_ne_zero {n : ℕ} {s : QubitCube n} (hs : s ≠ 0) :
    1 ≤ cubeWeight s := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hs
  have hi0 : s i ≠ 0 := by simpa using hi
  unfold cubeWeight
  have hle := Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun j => if s j = 0 then 0 else 1)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  simpa [hi0] using hle

noncomputable def cubeEnergy {n : ℕ} (c : QubitCube n → ℝ) : ℝ :=
  ∑ s, c s ^ (2 : ℕ)

theorem cubeEnergy_nonneg {n : ℕ} (c : QubitCube n → ℝ) : 0 ≤ cubeEnergy c := by
  unfold cubeEnergy
  positivity

theorem cubeEnergy_succ_fibers {n : ℕ} (c : QubitCube (n + 1) → ℝ) :
    cubeEnergy c = ∑ a : QubitLabel, cubeEnergy (fun s => c (Fin.cons a s)) := by
  classical
  unfold cubeEnergy
  rw [← Equiv.sum_comp (qubitCubeSuccAddEquiv n).toEquiv (fun s => c s ^ (2 : ℕ))]
  rw [Fintype.sum_prod_type]
  rfl

theorem corr_eq_ite_of_supported_zero [DecidableEq G] (f : G → ℝ)
    (hf : ∀ x, x ≠ 0 → f x = 0) (u : G) :
    corr f f u = if u = 0 then f 0 ^ (2 : ℕ) else 0 := by
  classical
  by_cases hu : u = 0
  · subst u
    rw [if_pos rfl]
    unfold corr
    rw [Finset.sum_eq_single 0]
    · simp [sq]
    · intro x hx hx0
      simp [hf x hx0]
    · simp
  · rw [if_neg hu]
    unfold corr
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      simp [hf u hu]
    · simp [hf x hx0]

theorem fourthIncidence_eq_pow_four_of_supported_zero [DecidableEq G] (f : G → ℝ)
    (hf : ∀ x, x ≠ 0 → f x = 0) :
    fourthIncidence f = f 0 ^ (4 : ℕ) := by
  classical
  unfold fourthIncidence
  simp_rw [corr_eq_ite_of_supported_zero f hf]
  rw [Finset.sum_eq_single 0]
  · simp [sq]
    ring
  · intro u hu hu0
    simp [hu0]
  · simp

theorem cubeEnergy_eq_sq_of_supported_zero {n : ℕ} (c : QubitCube n → ℝ)
    (hc : ∀ s, s ≠ 0 → c s = 0) :
    cubeEnergy c = c 0 ^ (2 : ℕ) := by
  classical
  unfold cubeEnergy
  exact Finset.sum_eq_single 0
    (fun s _ hs0 => by simp [hc s hs0])
    (by simp)

theorem cube_fourth_degree_zero {n : ℕ} (c : QubitCube n → ℝ)
    (hc : ∀ s, 0 ≤ c s)
    (hdegree : ∀ s, c s ≠ 0 → cubeWeight s ≤ 0) :
    fourthIncidence c ≤ (Real.sqrt (cubeEnergy c)) ^ (4 : ℕ) := by
  have hsupp : ∀ s, s ≠ 0 → c s = 0 := by
    intro s hs
    by_contra hcs
    have hw1 := one_le_cubeWeight_of_ne_zero hs
    have hw0 := hdegree s hcs
    omega
  rw [fourthIncidence_eq_pow_four_of_supported_zero c hsupp,
    cubeEnergy_eq_sq_of_supported_zero c hsupp]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (hc 0)]

theorem cube_fourth_succ_step {n q : ℕ} (c : QubitCube (n + 1) → ℝ)
    (hc : ∀ s, 0 ≤ c s)
    (hzero : fourthIncidence (fun s : QubitCube n => c (Fin.cons 0 s)) ≤
      (9 ^ (q + 1) * Real.sqrt (cubeEnergy (fun s : QubitCube n => c (Fin.cons 0 s)))) ^ (4 : ℕ))
    (htail : ∀ a : QubitLabel, a ≠ 0 →
      fourthIncidence (fun s : QubitCube n => c (Fin.cons a s)) ≤
        (9 ^ q * Real.sqrt (cubeEnergy (fun s : QubitCube n => c (Fin.cons a s)))) ^ (4 : ℕ)) :
    fourthIncidence c ≤ (9 ^ (q + 1) * Real.sqrt (cubeEnergy c)) ^ (4 : ℕ) := by
  classical
  let e := qubitCubeSuccAddEquiv n
  let F : QubitLabel × QubitCube n → ℝ := c ∘ e
  let E : QubitLabel → ℝ := fun a => cubeEnergy (fun s : QubitCube n => c (Fin.cons a s))
  let B : QubitLabel → ℝ := fun a =>
    if a = 0 then 9 ^ (q + 1) * Real.sqrt (E a) else 9 ^ q * Real.sqrt (E a)
  have hE (a : QubitLabel) : 0 ≤ E a := cubeEnergy_nonneg _
  have hB (a : QubitLabel) : 0 ≤ B a := by
    dsimp [B]
    split_ifs <;> positivity
  have hF (z : QubitLabel × QubitCube n) : 0 ≤ F z := hc (e z)
  have hfiber (a : QubitLabel) :
      fiber F a = fun s : QubitCube n => c (Fin.cons a s) := by
    rfl
  have hBbound (a : QubitLabel) : fourthIncidence (fiber F a) ≤ B a ^ (4 : ℕ) := by
    rw [hfiber]
    by_cases ha : a = 0
    · subst a
      simpa [B, E] using hzero
    · simpa [B, E, ha] using htail a ha
  have hproduct : fourthIncidence F ≤ fourthIncidence B :=
    fourthIncidence_product_le hF hB hBbound
  have hfourth : fourthIncidence F = fourthIncidence c :=
    fourthIncidence_comp_addEquiv e c
  rw [hfourth] at hproduct
  have hqubit := qubitLabel_fourthIncidence_le B hB
  let E0 := E (0, 0)
  let E1 := E (1, 0)
  let E2 := E (0, 1)
  let E3 := E (1, 1)
  let X := Real.sqrt E0
  let Y := Real.sqrt (E1 + E2 + E3)
  let C : ℝ := 9 ^ (q + 1)
  let T := B (1, 0) + B (0, 1) + B (1, 1)
  have hE0 : 0 ≤ E0 := hE (0, 0)
  have hE1 : 0 ≤ E1 := hE (1, 0)
  have hE2 : 0 ≤ E2 := hE (0, 1)
  have hE3 : 0 ≤ E3 := hE (1, 1)
  have htailE : 0 ≤ E1 + E2 + E3 := by positivity
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hY : 0 ≤ Y := Real.sqrt_nonneg _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsqrt1 : Real.sqrt E1 ≤ Y := by
    apply Real.sqrt_le_sqrt
    linarith
  have hsqrt2 : Real.sqrt E2 ≤ Y := by
    apply Real.sqrt_le_sqrt
    linarith
  have hsqrt3 : Real.sqrt E3 ≤ Y := by
    apply Real.sqrt_le_sqrt
    linarith
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hT : T ≤ C * Y / 3 := by
    dsimp [T, B, C]
    rw [pow_succ]
    have hsum : Real.sqrt E1 + Real.sqrt E2 + Real.sqrt E3 ≤ 3 * Y := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 9 ^ q by positivity)]
  have hB0 : B (0, 0) = C * X := by simp [B, C, X, E0]
  have habsorb := quartic_missing_linear_absorption hC hX hY hB0 hT0 hT
  have henergy : cubeEnergy c = E0 + (E1 + E2 + E3) := by
    rw [cubeEnergy_succ_fibers]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
    change (E0 + E2) + (E1 + E3) = E0 + (E1 + E2 + E3)
    ring
  have hXY : X ^ (2 : ℕ) + Y ^ (2 : ℕ) = cubeEnergy c := by
    dsimp [X, Y]
    rw [Real.sq_sqrt hE0, Real.sq_sqrt htailE, henergy]
  calc
    fourthIncidence c ≤ fourthIncidence B := hproduct
    _ ≤ B (0, 0) ^ (4 : ℕ) + 6 * B (0, 0) ^ (2 : ℕ) * T ^ (2 : ℕ) +
        4 * B (0, 0) * T ^ (3 : ℕ) + T ^ (4 : ℕ) := hqubit
    _ ≤ (C * Real.sqrt (X ^ (2 : ℕ) + Y ^ (2 : ℕ))) ^ (4 : ℕ) := habsorb
    _ = (9 ^ (q + 1) * Real.sqrt (cubeEnergy c)) ^ (4 : ℕ) := by rw [hXY]

theorem cube_fourth_hypercontractive : ∀ (n q : ℕ) (c : QubitCube n → ℝ),
    (∀ s, 0 ≤ c s) →
    (∀ s, c s ≠ 0 → cubeWeight s ≤ q) →
    fourthIncidence c ≤ (9 ^ q * Real.sqrt (cubeEnergy c)) ^ (4 : ℕ) := by
  intro n
  induction n with
  | zero =>
      intro q c hc hdegree
      have hsupp : ∀ s : QubitCube 0, s ≠ 0 → c s = 0 := by
        intro s hs
        exact False.elim (hs (Subsingleton.elim s 0))
      rw [fourthIncidence_eq_pow_four_of_supported_zero c hsupp,
        cubeEnergy_eq_sq_of_supported_zero c hsupp,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (hc 0)]
      have hfac : (1 : ℝ) ≤ 9 ^ q := one_le_pow₀ (by norm_num)
      have hmul : c 0 ≤ 9 ^ q * c 0 := by
        calc
          c 0 = 1 * c 0 := by ring
          _ ≤ 9 ^ q * c 0 := mul_le_mul_of_nonneg_right hfac (hc 0)
      exact pow_le_pow_left₀ (hc 0) hmul 4
  | succ n ih =>
      intro q c hc hdegree
      cases q with
      | zero =>
          simpa using cube_fourth_degree_zero c hc hdegree
      | succ q =>
          apply cube_fourth_succ_step c hc
          · apply ih (q + 1) (fun s : QubitCube n => c (Fin.cons 0 s))
            · intro s
              exact hc (Fin.cons 0 s)
            · intro s hs
              have h := hdegree (Fin.cons 0 s) hs
              rw [cubeWeight_cons] at h
              simpa using h
          · intro a ha
            apply ih q (fun s : QubitCube n => c (Fin.cons a s))
            · intro s
              exact hc (Fin.cons a s)
            · intro s hs
              have h := hdegree (Fin.cons a s) hs
              rw [cubeWeight_cons, if_neg ha] at h
              omega

/-! ### Phase-twisted Pauli-square bridge -/

/-- The additive two-bit label used by the incidence proof, converted to the QNN Pauli convention
`I,X,Y,Z = 0,1,2,3`. -/
def qubitLabelToFin4 (a : QubitLabel) : Fin 4 :=
  ![![0, 3], ![1, 2]] a.1 a.2

theorem qubitLabelToFin4_add (a b : QubitLabel) :
    qubitLabelToFin4 (a + b) =
      QuantumAlg.xor4 (qubitLabelToFin4 a) (qubitLabelToFin4 b) := by
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  fin_cases a₁ <;> fin_cases a₂ <;> fin_cases b₁ <;> fin_cases b₂ <;>
    decide

theorem qubitLabelToFin4_injective : Function.Injective qubitLabelToFin4 := by
  intro a b h
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  fin_cases a₁ <;> fin_cases a₂ <;> fin_cases b₁ <;> fin_cases b₂ <;>
    simp_all [qubitLabelToFin4]

def cubePauliLabel {n : ℕ} (s : QubitCube n) : Fin n → Fin 4 :=
  fun i => qubitLabelToFin4 (s i)

theorem cubePauliLabel_add {n : ℕ} (s t : QubitCube n) :
    cubePauliLabel (s + t) = QuantumAlg.pauliXor (cubePauliLabel s) (cubePauliLabel t) := by
  funext i
  exact qubitLabelToFin4_add (s i) (t i)

theorem cubePauliLabel_injective {n : ℕ} : Function.Injective (@cubePauliLabel n) := by
  intro s t h
  funext i
  exact qubitLabelToFin4_injective (congrFun h i)

theorem norm_phase1 (a b : Fin 4) : ‖QuantumAlg.phase1 a b‖ = 1 := by
  fin_cases a <;> fin_cases b <;> simp [QuantumAlg.phase1]

theorem norm_pauliPhase {n : ℕ} (s t : Fin n → Fin 4) :
    ‖QuantumAlg.pauliPhase s t‖ = 1 := by
  rw [QuantumAlg.pauliPhase, norm_prod]
  simp [norm_phase1]

theorem qubitLabel_add_self (a : QubitLabel) : a + a = 0 := by
  rcases a with ⟨a₁, a₂⟩
  ext <;> fin_cases a₁ <;> fin_cases a₂ <;> decide

theorem cube_add_self {n : ℕ} (s : QubitCube n) : s + s = 0 := by
  funext i
  exact qubitLabel_add_self (s i)

noncomputable def pairReverseSumEquiv {G : Type*} [AddCommGroup G] :
    (G × G) ≃ (G × G) where
  toFun p := (p.2 + p.1, p.2)
  invFun p := (p.1 - p.2, p.2)
  left_inv p := by
    rcases p with ⟨s, t⟩
    ext
    · dsimp
      abel
    · rfl
  right_inv p := by
    rcases p with ⟨u, s⟩
    ext
    · dsimp
      abel
    · rfl

/-- Real Pauli Hamiltonian represented in the complete `n`-qubit Pauli basis. -/
noncomputable def pauliHamiltonian {n : ℕ} (c : QubitCube n → ℝ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  ∑ s, (c s : ℂ) • QuantumAlg.pauliMat (cubePauliLabel s)

theorem pauliHamiltonian_mul_self_expand {n : ℕ} (c : QubitCube n → ℝ) :
    pauliHamiltonian c * pauliHamiltonian c =
      ∑ p : QubitCube n × QubitCube n,
        (((c p.2 * c p.1 : ℝ) : ℂ) *
          QuantumAlg.pauliPhase (cubePauliLabel p.2) (cubePauliLabel p.1)) •
          QuantumAlg.pauliMat (cubePauliLabel (p.2 + p.1)) := by
  classical
  simp only [pauliHamiltonian, Finset.sum_mul, Finset.mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _hs
  apply Finset.sum_congr rfl
  intro t _ht
  rw [smul_mul_assoc, mul_smul_comm, QuantumAlg.pauliMat_mul_closed,
    ← cubePauliLabel_add]
  simp only [smul_smul, Complex.ofReal_mul]
  ring_nf

noncomputable def pauliSquareCoeff {n : ℕ} (c : QubitCube n → ℝ) (u : QubitCube n) : ℂ :=
  ∑ s, ((c s * c (s + u) : ℝ) : ℂ) *
    QuantumAlg.pauliPhase (cubePauliLabel s) (cubePauliLabel (s + u))

/-- Squaring a Pauli Hamiltonian is a phase-twisted XOR convolution of its coefficients. -/
theorem pauliHamiltonian_sq_grouped {n : ℕ} (c : QubitCube n → ℝ) :
    pauliHamiltonian c * pauliHamiltonian c =
      ∑ u, pauliSquareCoeff c u • QuantumAlg.pauliMat (cubePauliLabel u) := by
  classical
  rw [pauliHamiltonian_mul_self_expand]
  calc
    (∑ p : QubitCube n × QubitCube n,
        (((c p.2 * c p.1 : ℝ) : ℂ) *
          QuantumAlg.pauliPhase (cubePauliLabel p.2) (cubePauliLabel p.1)) •
          QuantumAlg.pauliMat (cubePauliLabel (p.2 + p.1))) =
        ∑ p : QubitCube n × QubitCube n,
          (fun q : QubitCube n × QubitCube n =>
            (((c q.2 * c (q.2 + q.1) : ℝ) : ℂ) *
              QuantumAlg.pauliPhase (cubePauliLabel q.2)
                (cubePauliLabel (q.2 + q.1))) •
              QuantumAlg.pauliMat (cubePauliLabel q.1))
            (pairReverseSumEquiv p) := by
      apply Finset.sum_congr rfl
      intro p _hp
      have hcancel : p.2 + (p.2 + p.1) = p.1 := by
        calc
          p.2 + (p.2 + p.1) = (p.2 + p.2) + p.1 := by abel
          _ = p.1 := by rw [cube_add_self]; simp
      dsimp [pairReverseSumEquiv]
      rw [hcancel]
    _ = ∑ p : QubitCube n × QubitCube n,
          (((c p.2 * c (p.2 + p.1) : ℝ) : ℂ) *
            QuantumAlg.pauliPhase (cubePauliLabel p.2)
              (cubePauliLabel (p.2 + p.1))) •
            QuantumAlg.pauliMat (cubePauliLabel p.1) := by
      exact Equiv.sum_comp (pairReverseSumEquiv (G := QubitCube n))
        (fun p : QubitCube n × QubitCube n =>
          (((c p.2 * c (p.2 + p.1) : ℝ) : ℂ) *
            QuantumAlg.pauliPhase (cubePauliLabel p.2)
              (cubePauliLabel (p.2 + p.1))) •
            QuantumAlg.pauliMat (cubePauliLabel p.1))
    _ = ∑ u, pauliSquareCoeff c u • QuantumAlg.pauliMat (cubePauliLabel u) := by
      simp only [Fintype.sum_prod_type, pauliSquareCoeff, Finset.sum_smul]

noncomputable def phaseCorr {G : Type*} [Fintype G] [AddCommGroup G]
    (c : G → ℝ) (phase : G → ℂ) (u : G) : ℂ :=
  ∑ x, ((c x * c (x + u) : ℝ) : ℂ) * phase x

theorem norm_phaseCorr_le_corr_abs {G : Type*} [Fintype G] [AddCommGroup G]
    (c : G → ℝ) (phase : G → ℂ) (hphase : ∀ x, ‖phase x‖ ≤ 1) (u : G) :
    ‖phaseCorr c phase u‖ ≤ corr (fun x => |c x|) (fun x => |c x|) u := by
  classical
  calc
    ‖phaseCorr c phase u‖ ≤
        ∑ x, ‖((c x * c (x + u) : ℝ) : ℂ) * phase x‖ := norm_sum_le _ _
    _ ≤ ∑ x, |c x| * |c (x + u)| := by
      apply Finset.sum_le_sum
      intro x _hx
      calc
        ‖((c x * c (x + u) : ℝ) : ℂ) * phase x‖ =
            |c x * c (x + u)| * ‖phase x‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ |c x * c (x + u)| * 1 :=
          mul_le_mul_of_nonneg_left (hphase x) (abs_nonneg _)
        _ = |c x| * |c (x + u)| := by rw [mul_one, abs_mul]
    _ = corr (fun x => |c x|) (fun x => |c x|) u := rfl

theorem normSq_phaseCorr_le_corr_abs_sq {G : Type*} [Fintype G] [AddCommGroup G]
    (c : G → ℝ) (phase : G → ℂ) (hphase : ∀ x, ‖phase x‖ ≤ 1) (u : G) :
    Complex.normSq (phaseCorr c phase u) ≤
      corr (fun x => |c x|) (fun x => |c x|) u ^ (2 : ℕ) := by
  rw [Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_phaseCorr_le_corr_abs c phase hphase u) 2

theorem sum_normSq_phaseCorr_le_fourthIncidence_abs
    {G : Type*} [Fintype G] [AddCommGroup G]
    (c : G → ℝ) (phase : G → G → ℂ) (hphase : ∀ u x, ‖phase u x‖ ≤ 1) :
    (∑ u, Complex.normSq (phaseCorr c (phase u) u)) ≤
      fourthIncidence (fun x => |c x|) := by
  unfold fourthIncidence
  exact Finset.sum_le_sum fun u _ =>
    normSq_phaseCorr_le_corr_abs_sq c (phase u) (hphase u) u

theorem sum_normSq_pauliSquareCoeff_le_fourthIncidence_abs {n : ℕ}
    (c : QubitCube n → ℝ) :
    (∑ u, Complex.normSq (pauliSquareCoeff c u)) ≤
      fourthIncidence (fun s => |c s|) := by
  simpa only [pauliSquareCoeff, phaseCorr] using
    (sum_normSq_phaseCorr_le_fourthIncidence_abs c
      (fun u s => QuantumAlg.pauliPhase (cubePauliLabel s) (cubePauliLabel (s + u)))
      (fun _u _s => (norm_pauliPhase _ _).le))

/-- Exact Parseval identity for the complete Pauli basis. -/
theorem hsInner_pauli_sum_self {n : ℕ} (a : QubitCube n → ℂ) :
    QuantumAlg.hsInner
        (∑ u, a u • QuantumAlg.pauliMat (cubePauliLabel u))
        (∑ u, a u • QuantumAlg.pauliMat (cubePauliLabel u)) =
      (2 ^ n : ℂ) * ∑ u, (Complex.normSq (a u) : ℂ) := by
  classical
  simp only [QuantumAlg.hsInner_sum_left, QuantumAlg.hsInner_sum_right,
    QuantumAlg.hsInner_smul_left, QuantumAlg.hsInner_smul_right,
    QuantumAlg.pauliMat_hsInner]
  simp only [cubePauliLabel_injective.eq_iff, Complex.normSq_eq_conj_mul_self,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _hu
  simp
  ring_nf

/-- The fourth matrix trace is dominated by the phase-free XOR incidence, with no qubit-count
loss beyond the Hilbert-space dimension factor forced by Pauli normalization. -/
theorem hsInner_pauliHamiltonian_sq_re_le {n : ℕ} (c : QubitCube n → ℝ) :
    (QuantumAlg.hsInner (pauliHamiltonian c * pauliHamiltonian c)
      (pauliHamiltonian c * pauliHamiltonian c)).re ≤
      (2 ^ n : ℝ) * fourthIncidence (fun s => |c s|) := by
  rw [pauliHamiltonian_sq_grouped]
  have hre := congrArg Complex.re (hsInner_pauli_sum_self
    (fun u => pauliSquareCoeff c u))
  rw [hre]
  rw [Complex.mul_re]
  have htwo : ∀ k : ℕ,
      ((2 ^ k : ℂ).re) = (2 ^ k : ℝ) ∧ ((2 ^ k : ℂ).im) = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => simp [pow_succ, ih.1, ih.2]
  rw [(htwo n).1, (htwo n).2, zero_mul, sub_zero]
  rw [← Complex.reCLM_apply, _root_.map_sum]
  simp only [Complex.reCLM_apply, Complex.ofReal_re]
  have hD : 0 ≤ (2 ^ n : ℝ) := pow_nonneg (by norm_num) n
  exact mul_le_mul_of_nonneg_left
    (sum_normSq_pauliSquareCoeff_le_fourthIncidence_abs c) hD

theorem pauliHamiltonian_isHermitian {n : ℕ} (c : QubitCube n → ℝ) :
    (pauliHamiltonian c).IsHermitian := by
  classical
  rw [pauliHamiltonian, Matrix.IsHermitian, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.conjTranspose_smul,
    show star ((c s : ℝ) : ℂ) = ((c s : ℝ) : ℂ) from Complex.conj_ofReal _]
  congr 1
  exact QuantumAlg.pauliMat_isHermitian _

theorem trace_pauliHamiltonian_sq_re_eq {n : ℕ} (c : QubitCube n → ℝ) :
    (Matrix.trace (pauliHamiltonian c * pauliHamiltonian c)).re =
      (2 ^ n : ℝ) * ∑ s, c s ^ (2 : ℕ) := by
  have hH : Matrix.conjTranspose (pauliHamiltonian c) = pauliHamiltonian c :=
    pauliHamiltonian_isHermitian c
  calc
    (Matrix.trace (pauliHamiltonian c * pauliHamiltonian c)).re =
        (QuantumAlg.hsInner (pauliHamiltonian c) (pauliHamiltonian c)).re := by
      rw [QuantumAlg.hsInner_def, hH]
    _ = ((2 ^ n : ℂ) * ∑ s, (Complex.normSq ((c s : ℝ) : ℂ) : ℂ)).re := by
      exact congrArg Complex.re (hsInner_pauli_sum_self (fun s => ((c s : ℝ) : ℂ)))
    _ = (2 ^ n : ℝ) * ∑ s, c s ^ (2 : ℕ) := by
      have htwo : ∀ k : ℕ,
          ((2 ^ k : ℂ).re) = (2 ^ k : ℝ) ∧ ((2 ^ k : ℂ).im) = 0 := by
        intro k
        induction k with
        | zero => simp
        | succ k ih => simp [pow_succ, ih.1, ih.2]
      rw [Complex.mul_re, (htwo n).1, (htwo n).2, zero_mul, sub_zero]
      rw [← Complex.reCLM_apply, _root_.map_sum]
      simp only [Complex.reCLM_apply, Complex.ofReal_re, Complex.normSq_ofReal, pow_two]

theorem hsInner_pauliHamiltonian_sq_eq_trace_four {n : ℕ} (c : QubitCube n → ℝ) :
    QuantumAlg.hsInner (pauliHamiltonian c * pauliHamiltonian c)
      (pauliHamiltonian c * pauliHamiltonian c) =
        Matrix.trace ((pauliHamiltonian c * pauliHamiltonian c) *
          (pauliHamiltonian c * pauliHamiltonian c)) := by
  rw [QuantumAlg.hsInner_def, Matrix.conjTranspose_mul]
  have hH : Matrix.conjTranspose (pauliHamiltonian c) = pauliHamiltonian c :=
    pauliHamiltonian_isHermitian c
  rw [hH]

theorem trace_pauliHamiltonian_four_re_le {n : ℕ} (c : QubitCube n → ℝ) :
    (Matrix.trace ((pauliHamiltonian c * pauliHamiltonian c) *
      (pauliHamiltonian c * pauliHamiltonian c))).re ≤
        (2 ^ n : ℝ) * fourthIncidence (fun s => |c s|) := by
  rw [← hsInner_pauliHamiltonian_sq_eq_trace_four]
  exact hsInner_pauliHamiltonian_sq_re_le c

/-- Fourth spectral moment as the real fourth trace of a finite Hermitian matrix. -/
theorem trace_four_re_eq_sum_four_eigenvalues
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    (Matrix.trace ((H * H) * (H * H))).re = ∑ i, hH.eigenvalues i ^ (4 : ℕ) := by
  let K := hH.eigenvectorUnitary
  let D := Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ))
  have hspec : H = (K : Matrix ι ι ℂ) * D * star (K : Matrix ι ι ℂ) :=
    hH.spectral_theorem
  have hunit : star (K : Matrix ι ι ℂ) * (K : Matrix ι ι ℂ) = 1 :=
    Unitary.coe_star_mul_self K
  have hcollapse :
      Matrix.trace (((H * H) * (H * H))) =
        Matrix.trace ((D * D) * (D * D)) := by
    rw [hspec]
    have hmatrix :
        ((((K : Matrix ι ι ℂ) * D * star (K : Matrix ι ι ℂ)) *
            ((K : Matrix ι ι ℂ) * D * star (K : Matrix ι ι ℂ))) *
          (((K : Matrix ι ι ℂ) * D * star (K : Matrix ι ι ℂ)) *
            ((K : Matrix ι ι ℂ) * D * star (K : Matrix ι ι ℂ)))) =
          (K : Matrix ι ι ℂ) * ((D * D) * (D * D)) *
            star (K : Matrix ι ι ℂ) := by
      calc
        _ = (K : Matrix ι ι ℂ) * D *
            (star (K : Matrix ι ι ℂ) * (K : Matrix ι ι ℂ)) * D *
            (star (K : Matrix ι ι ℂ) * (K : Matrix ι ι ℂ)) * D *
            (star (K : Matrix ι ι ℂ) * (K : Matrix ι ι ℂ)) * D *
            star (K : Matrix ι ι ℂ) := by noncomm_ring
        _ = _ := by rw [hunit]; noncomm_ring
    rw [hmatrix]
    calc
      Matrix.trace ((K : Matrix ι ι ℂ) * ((D * D) * (D * D)) *
          star (K : Matrix ι ι ℂ)) = Matrix.trace (star (K : Matrix ι ι ℂ) *
          (K : Matrix ι ι ℂ) * ((D * D) * (D * D))) :=
        Matrix.trace_mul_cycle _ _ _
      _ = Matrix.trace ((D * D) * (D * D)) := by rw [hunit, Matrix.one_mul]
  rw [hcollapse]
  dsimp [D]
  simp only [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  rw [← Complex.reCLM_apply, _root_.map_sum]
  simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
    add_zero]
  ring_nf

/-- Incidence control implies a dimension-free normalized spectral kurtosis bound. -/
theorem pauliHamiltonian_eigenKurtosis_of_incidence {n q : ℕ}
    (c : QubitCube n → ℝ)
    (hinc : fourthIncidence (fun s => |c s|) ≤
      (9 ^ q * Real.sqrt (∑ s, c s ^ (2 : ℕ))) ^ (4 : ℕ)) :
    (Fintype.card (Fin (2 ^ n)) : ℝ) *
        (∑ i, (pauliHamiltonian_isHermitian c).eigenvalues i ^ (4 : ℕ)) ≤
      (9 ^ q : ℝ) ^ (4 : ℕ) *
        (∑ i, (pauliHamiltonian_isHermitian c).eigenvalues i ^ (2 : ℕ)) ^ (2 : ℕ) := by
  let H := pauliHamiltonian c
  let hH : H.IsHermitian := pauliHamiltonian_isHermitian c
  let E : ℝ := ∑ s, c s ^ (2 : ℕ)
  let D : ℝ := (2 ^ n : ℝ)
  have hcard : (Fintype.card (Fin (2 ^ n)) : ℝ) = D := by simp [D]
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hinc' : fourthIncidence (fun s => |c s|) ≤ (9 ^ q : ℝ) ^ (4 : ℕ) * E ^ (2 : ℕ) := by
    calc
      fourthIncidence (fun s => |c s|) ≤
          (9 ^ q * Real.sqrt E) ^ (4 : ℕ) := by simpa [E] using hinc
      _ = (9 ^ q : ℝ) ^ (4 : ℕ) * E ^ (2 : ℕ) := by
        rw [mul_pow]
        have hsqrt : (Real.sqrt E) ^ (4 : ℕ) = E ^ (2 : ℕ) := by
          calc
            (Real.sqrt E) ^ (4 : ℕ) = ((Real.sqrt E) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
            _ = E ^ (2 : ℕ) := by rw [Real.sq_sqrt hE]
        rw [hsqrt]
  have hfour : (∑ i, hH.eigenvalues i ^ (4 : ℕ)) ≤
      D * fourthIncidence (fun s => |c s|) := by
    have h := trace_pauliHamiltonian_four_re_le c
    rw [trace_four_re_eq_sum_four_eigenvalues H hH] at h
    simpa [H, hH, D] using h
  have hsecond : (∑ i, hH.eigenvalues i ^ (2 : ℕ)) = D * E := by
    rw [← trace_mul_self_re_eq_sum_sq_eigenvalues H hH]
    simpa [H, D, E] using trace_pauliHamiltonian_sq_re_eq c
  rw [hcard]
  calc
    D * (∑ i, hH.eigenvalues i ^ (4 : ℕ)) ≤
        D * (D * fourthIncidence (fun s => |c s|)) :=
      mul_le_mul_of_nonneg_left hfour (by positivity)
    _ ≤ D * (D * ((9 ^ q : ℝ) ^ (4 : ℕ) * E ^ (2 : ℕ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hinc' (by positivity)) (by positivity)
    _ = (9 ^ q : ℝ) ^ (4 : ℕ) * (D * E) ^ (2 : ℕ) := by ring
    _ = (9 ^ q : ℝ) ^ (4 : ℕ) * (∑ i, hH.eigenvalues i ^ (2 : ℕ)) ^ (2 : ℕ) := by rw [hsecond]

/-- **Fixed-locality Pauli kurtosis law.** Every real Pauli Hamiltonian whose coefficients vanish
above weight `q` has normalized spectral kurtosis at most `(9^q)^(4 : ℕ)`, independently of qubit count. -/
theorem pauliHamiltonian_eigenKurtosis {n q : ℕ} (c : QubitCube n → ℝ)
    (hdegree : ∀ s, c s ≠ 0 → cubeWeight s ≤ q) :
    (Fintype.card (Fin (2 ^ n)) : ℝ) *
        (∑ i, (pauliHamiltonian_isHermitian c).eigenvalues i ^ (4 : ℕ)) ≤
      (9 ^ q : ℝ) ^ (4 : ℕ) *
        (∑ i, (pauliHamiltonian_isHermitian c).eigenvalues i ^ (2 : ℕ)) ^ (2 : ℕ) := by
  apply pauliHamiltonian_eigenKurtosis_of_incidence c
  have hcube := cube_fourth_hypercontractive n q (fun s => |c s|)
    (fun s => abs_nonneg (c s))
    (fun s hs => hdegree s (abs_ne_zero.mp hs))
  simpa [cubeEnergy, sq_abs] using hcube

/-- The fixed-locality kurtosis constant plugs directly into the gap-free Choi-shortcut tube law. -/
theorem pauliHamiltonian_choiShortcut_commutatorEnergy_le_traceEnergy
    {n q : ℕ} (c : QubitCube n → ℝ)
    (hdegree : ∀ s, c s ≠ 0 → cubeWeight s ≤ q)
    (T W : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (hcomm : pauliHamiltonian c * (T : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) =
      (T : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) * pauliHamiltonian c)
    (hfidelity : 16 * (9 ^ q : ℝ) ^ (4 : ℕ) *
        ((Fintype.card (Fin (2 ^ n)) : ℝ) ^ (2 : ℕ) -
          Complex.normSq (Matrix.trace
            (star (T : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) *
              (W : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)))) ≤
        (Fintype.card (Fin (2 ^ n)) : ℝ) ^ (2 : ℕ)) :
    finiteMatrixHilbertSchmidtEnergy
        (pauliHamiltonian c * (W : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) -
          (W : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) * pauliHamiltonian c) ≤
      (Matrix.trace (pauliHamiltonian c * pauliHamiltonian c)).re := by
  exact finiteUnitary_choiShortcut_commutatorEnergy_le_traceEnergy_of_eigenKurtosis
    (pauliHamiltonian c) (pauliHamiltonian_isHermitian c) T W hcomm
    ((9 ^ q : ℝ) ^ (4 : ℕ)) (pauliHamiltonian_eigenKurtosis c hdegree) hfidelity

end

end GaloisForLFunctions.HTGeometry
