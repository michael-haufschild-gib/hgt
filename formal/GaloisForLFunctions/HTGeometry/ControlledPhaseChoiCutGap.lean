import GaloisForLFunctions.HTGeometry.FiniteRegularizedDeterminant
import GaloisForLFunctions.RHTower.AutonomousReturnReflection
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

open scoped BigOperators Matrix Kronecker
open Matrix

/-!
# Controlled-phase Choi cut gap

A unitary factoring across a one-qubit cut cannot have high normalized Choi fidelity with a
controlled phase whose phase lies in the closed left half-plane. The proof retains arbitrary
unit-modulus background phases and all off-cut degrees of freedom; Hilbert--Schmidt normalization
cancels dimension exactly. The rational fidelity bound `7/8` gives the uniform trace-distance gap
`sqrt (1/8)`.
-/

namespace GaloisForLFunctions.HTGeometry.ControlledPhaseChoiCutGap

theorem norm_one_add_le_three_halves_of_unit_re_nonpos (z : ℂ)
    (hz : ‖z‖ = 1) (hre : z.re ≤ 0) :
    ‖1 + z‖ ≤ (3 : ℝ) / 2 := by
  have hs := norm_add_sq (𝕜 := ℂ) (1 : ℂ) z
  have hsq : ‖1 + z‖ ^ 2 ≤ 2 := by
    simp [RCLike.inner_apply, hz] at hs
    nlinarith
  nlinarith [sq_nonneg (‖1 + z‖ - 3 / 2), norm_nonneg (1 + z)]

theorem two_phase_pair_energy_le (P Q z : ℂ)
    (hz : ‖z‖ = 1) (hre : z.re ≤ 0) :
    ‖P + Q‖ ^ 2 + ‖P + z * Q‖ ^ 2 ≤
      ((7 : ℝ) / 2) * (‖P‖ ^ 2 + ‖Q‖ ^ 2) := by
  have h1 := norm_add_sq (𝕜 := ℂ) P Q
  have h2 := norm_add_sq (𝕜 := ℂ) P (z * Q)
  have hzQ : ‖z * Q‖ = ‖Q‖ := by rw [norm_mul, hz, one_mul]
  have hcross :
      (inner ℂ P Q).re + (inner ℂ P (z * Q)).re =
        (inner ℂ P ((1 + z) * Q)).re := by
    rw [add_mul, inner_add_right]
    simp
  have hinner :
      (inner ℂ P ((1 + z) * Q)).re ≤ ‖P‖ * ‖1 + z‖ * ‖Q‖ := by
    calc
      (inner ℂ P ((1 + z) * Q)).re
          ≤ ‖inner ℂ P ((1 + z) * Q)‖ := by
            exact le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
      _ ≤ ‖P‖ * ‖((1 + z) * Q)‖ := norm_inner_le_norm _ _
      _ = ‖P‖ * ‖1 + z‖ * ‖Q‖ := by rw [norm_mul]; ring
  have hphase := norm_one_add_le_three_halves_of_unit_re_nonpos z hz hre
  have hnonnegP := norm_nonneg P
  have hnonnegQ := norm_nonneg Q
  have hcrossR :
      RCLike.re (inner ℂ P Q) + RCLike.re (inner ℂ P (z * Q)) =
        RCLike.re (inner ℂ P ((1 + z) * Q)) := hcross
  have hprod : ‖P‖ * ‖1 + z‖ * ‖Q‖ ≤ (3 / 2 : ℝ) * ‖P‖ * ‖Q‖ := by
    have := mul_le_mul_of_nonneg_left hphase hnonnegP
    exact mul_le_mul_of_nonneg_right (by linarith) hnonnegQ
  have hcrossBound :
      RCLike.re (inner ℂ P Q) + RCLike.re (inner ℂ P (z * Q)) ≤
        (3 / 2 : ℝ) * ‖P‖ * ‖Q‖ := by
    rw [hcrossR]
    exact hinner.trans hprod
  rw [hzQ] at h2
  rw [h1, h2]
  nlinarith [sq_nonneg (‖P‖ - ‖Q‖), hcrossBound]

theorem trace_conjTranspose_mul_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℂ) (f : ι → ℂ) :
    Matrix.trace (Wᴴ * Matrix.diagonal f) =
      ∑ i : ι, starRingEnd ℂ (W i i) * f i := by
  classical
  rw [GaloisForLFunctions.RHTower.trace_conjTranspose_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Matrix.diagonal, Ne.symm hji]
  · simp

variable {γ : Type*} [Fintype γ] [DecidableEq γ]

abbrev ProductIndex (γ : Type*) := Bool × (Bool × γ)

def productControlledPhaseTarget (z : ℂ) (r : Bool × γ → ℂ) :
    Matrix (ProductIndex γ) (ProductIndex γ) ℂ :=
  Matrix.diagonal fun x => r x.2 * if x.1 && x.2.1 then z else 1

theorem trace_kronecker_conj_productControlledPhaseTarget
    (A : Matrix Bool Bool ℂ) (B : Matrix (Bool × γ) (Bool × γ) ℂ)
    (z : ℂ) (r : Bool × γ → ℂ) :
    Matrix.trace ((A ⊗ₖ B)ᴴ * productControlledPhaseTarget z r) =
      ∑ a : Bool, starRingEnd ℂ (A a a) *
        ∑ y : Bool × γ, starRingEnd ℂ (B y y) * r y *
          (if a && y.1 then z else 1) := by
  change Matrix.trace ((A ⊗ₖ B)ᴴ * Matrix.diagonal
      (fun x : ProductIndex γ => r x.2 * if x.1 && x.2.1 then z else 1)) = _
  rw [trace_conjTranspose_mul_diagonal]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  simp
  split_ifs <;> ring

theorem norm_sum_sq_le_card_mul_sum_sq {ι : Type*} [Fintype ι]
    (w : ι → ℂ) :
    ‖∑ i : ι, w i‖ ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ i : ι, ‖w i‖ ^ 2 := by
  classical
  have h1 : ‖∑ i : ι, w i‖ ≤ ∑ i : ι, ‖w i‖ := norm_sum_le _ _
  have h2 : (∑ i : ι, ‖w i‖) ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ i : ι, ‖w i‖ ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun i => ‖w i‖))
  have h0 := norm_nonneg (∑ i : ι, w i)
  have hsum0 : 0 ≤ ∑ i : ι, ‖w i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  nlinarith

theorem norm_two_term_sq_le (a b x y : ℂ) :
    ‖a * x + b * y‖ ^ 2 ≤
      (‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have htri : ‖a * x + b * y‖ ≤ ‖a‖ * ‖x‖ + ‖b‖ * ‖y‖ := by
    calc
      ‖a * x + b * y‖ ≤ ‖a * x‖ + ‖b * y‖ := norm_add_le _ _
      _ = _ := by rw [norm_mul, norm_mul]
  have hleft := norm_nonneg (a * x + b * y)
  have hright : 0 ≤ ‖a‖ * ‖x‖ + ‖b‖ * ‖y‖ := by positivity
  have hsquare : ‖a * x + b * y‖ ^ 2 ≤
      (‖a‖ * ‖x‖ + ‖b‖ * ‖y‖) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (‖a‖ * ‖y‖ - ‖b‖ * ‖x‖)]

def phaseFibreSum (B : Matrix (Bool × γ) (Bool × γ) ℂ)
    (r : Bool × γ → ℂ) (b : Bool) : ℂ :=
  ∑ g : γ, starRingEnd ℂ (B (b, g) (b, g)) * r (b, g)

theorem trace_kronecker_conj_productControlledPhaseTarget_eq_pair
    (A : Matrix Bool Bool ℂ) (B : Matrix (Bool × γ) (Bool × γ) ℂ)
    (z : ℂ) (r : Bool × γ → ℂ) :
    Matrix.trace ((A ⊗ₖ B)ᴴ * productControlledPhaseTarget z r) =
      starRingEnd ℂ (A false false) *
          (phaseFibreSum B r false + phaseFibreSum B r true) +
        starRingEnd ℂ (A true true) *
          (phaseFibreSum B r false + z * phaseFibreSum B r true) := by
  rw [trace_kronecker_conj_productControlledPhaseTarget]
  simp only [Fintype.sum_bool, Bool.false_and, Bool.true_and]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  unfold phaseFibreSum
  simp
  rw [← Finset.sum_mul]
  ring_nf

noncomputable def diagonalEnergy {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℂ) : ℝ := ∑ i : ι, ‖M i i‖ ^ 2

omit [DecidableEq γ] in
theorem phaseFibreSum_norm_sq_le
    (B : Matrix (Bool × γ) (Bool × γ) ℂ) (r : Bool × γ → ℂ)
    (hr : ∀ y, ‖r y‖ = 1) (b : Bool) :
    ‖phaseFibreSum B r b‖ ^ 2 ≤
      (Fintype.card γ : ℝ) * ∑ g : γ, ‖B (b, g) (b, g)‖ ^ 2 := by
  unfold phaseFibreSum
  refine (norm_sum_sq_le_card_mul_sum_sq
    (fun g : γ => starRingEnd ℂ (B (b, g) (b, g)) * r (b, g))).trans_eq ?_
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  rw [norm_mul, RCLike.norm_conj, hr, mul_one]

omit [DecidableEq γ] in
theorem phase_pair_energy_le_diagonalEnergy
    (B : Matrix (Bool × γ) (Bool × γ) ℂ) (z : ℂ)
    (r : Bool × γ → ℂ) (hz : ‖z‖ = 1) (hre : z.re ≤ 0)
    (hr : ∀ y, ‖r y‖ = 1) :
    ‖phaseFibreSum B r false + phaseFibreSum B r true‖ ^ 2 +
        ‖phaseFibreSum B r false + z * phaseFibreSum B r true‖ ^ 2 ≤
      ((7 : ℝ) / 2) * (Fintype.card γ : ℝ) * diagonalEnergy B := by
  let P := phaseFibreSum B r false
  let Q := phaseFibreSum B r true
  have hp := phaseFibreSum_norm_sq_le B r hr false
  have hq := phaseFibreSum_norm_sq_le B r hr true
  have hpair := two_phase_pair_energy_le P Q z hz hre
  have hcard : 0 ≤ (Fintype.card γ : ℝ) := by positivity
  have hdiag : diagonalEnergy B =
      (∑ g : γ, ‖B (false, g) (false, g)‖ ^ 2) +
        ∑ g : γ, ‖B (true, g) (true, g)‖ ^ 2 := by
    unfold diagonalEnergy
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    ring
  dsimp only [P, Q] at hpair ⊢
  rw [hdiag]
  nlinarith

theorem trace_productControlledPhaseTarget_norm_sq_le
    (A : Matrix Bool Bool ℂ) (B : Matrix (Bool × γ) (Bool × γ) ℂ)
    (z : ℂ) (r : Bool × γ → ℂ) (hz : ‖z‖ = 1) (hre : z.re ≤ 0)
    (hr : ∀ y, ‖r y‖ = 1) :
    ‖Matrix.trace ((A ⊗ₖ B)ᴴ * productControlledPhaseTarget z r)‖ ^ 2 ≤
      diagonalEnergy A * (((7 : ℝ) / 2) * (Fintype.card γ : ℝ) *
        diagonalEnergy B) := by
  rw [trace_kronecker_conj_productControlledPhaseTarget_eq_pair]
  let P := phaseFibreSum B r false
  let Q := phaseFibreSum B r true
  have hc := norm_two_term_sq_le
    (starRingEnd ℂ (A false false)) (starRingEnd ℂ (A true true))
    (P + Q) (P + z * Q)
  have hpair := phase_pair_energy_le_diagonalEnergy B z r hz hre hr
  have hdiagA : diagonalEnergy A = ‖A false false‖ ^ 2 + ‖A true true‖ ^ 2 := by
    unfold diagonalEnergy
    simp
    ring
  rw [RCLike.norm_conj, RCLike.norm_conj, ← hdiagA] at hc
  dsimp only [P, Q] at hc
  have hdiagA0 : 0 ≤ diagonalEnergy A := by
    unfold diagonalEnergy
    positivity
  exact hc.trans (mul_le_mul_of_nonneg_left hpair hdiagA0)

theorem matHSNormSq_kronecker {α β : Type*}
    [Fintype α] [Fintype β]
    (A : Matrix α α ℂ) (B : Matrix β β ℂ) :
    GaloisForLFunctions.HTGeometry.matHSNormSq (A ⊗ₖ B) =
      GaloisForLFunctions.HTGeometry.matHSNormSq A *
        GaloisForLFunctions.HTGeometry.matHSNormSq B := by
  unfold GaloisForLFunctions.HTGeometry.matHSNormSq
  simp only [Fintype.sum_prod_type, Matrix.kronecker_apply, norm_mul, mul_pow]
  simp_rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_mul]
  rw [Finset.sum_mul_sum]

theorem matHSNormSq_eq_card_of_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℂ) (hW : Wᴴ * W = 1) :
    GaloisForLFunctions.HTGeometry.matHSNormSq W = Fintype.card ι := by
  have htrace := GaloisForLFunctions.HTGeometry.matHSNormSq_eq_trace W
  rw [hW, Matrix.trace_one] at htrace
  exact_mod_cast htrace

theorem diagonalEnergy_product_le_card_of_kronecker_unitary
    (A : Matrix Bool Bool ℂ) (B : Matrix (Bool × γ) (Bool × γ) ℂ)
    (hW : (A ⊗ₖ B)ᴴ * (A ⊗ₖ B) = 1) :
    diagonalEnergy A * diagonalEnergy B ≤ Fintype.card (ProductIndex γ) := by
  have hA := GaloisForLFunctions.HTGeometry.sum_diag_normSq_le A
  have hB := GaloisForLFunctions.HTGeometry.sum_diag_normSq_le B
  change diagonalEnergy A ≤ GaloisForLFunctions.HTGeometry.matHSNormSq A at hA
  change diagonalEnergy B ≤ GaloisForLFunctions.HTGeometry.matHSNormSq B at hB
  have hA0 : 0 ≤ diagonalEnergy A := by unfold diagonalEnergy; positivity
  have hB0 : 0 ≤ diagonalEnergy B := by unfold diagonalEnergy; positivity
  have hHSA0 := GaloisForLFunctions.HTGeometry.matHSNormSq_nonneg A
  calc
    diagonalEnergy A * diagonalEnergy B ≤
        GaloisForLFunctions.HTGeometry.matHSNormSq A *
          GaloisForLFunctions.HTGeometry.matHSNormSq B :=
      mul_le_mul hA hB hB0 hHSA0
    _ = GaloisForLFunctions.HTGeometry.matHSNormSq (A ⊗ₖ B) :=
      (matHSNormSq_kronecker A B).symm
    _ = Fintype.card (ProductIndex γ) :=
      matHSNormSq_eq_card_of_unitary (A ⊗ₖ B) hW

theorem trace_productControlledPhaseTarget_norm_sq_le_seven_eighth
    (A : Matrix Bool Bool ℂ) (B : Matrix (Bool × γ) (Bool × γ) ℂ)
    (z : ℂ) (r : Bool × γ → ℂ) (hz : ‖z‖ = 1) (hre : z.re ≤ 0)
    (hr : ∀ y, ‖r y‖ = 1)
    (hW : (A ⊗ₖ B)ᴴ * (A ⊗ₖ B) = 1) :
    ‖Matrix.trace ((A ⊗ₖ B)ᴴ * productControlledPhaseTarget z r)‖ ^ 2 ≤
      ((7 : ℝ) / 8) * (Fintype.card (ProductIndex γ) : ℝ) ^ 2 := by
  have htrace := trace_productControlledPhaseTarget_norm_sq_le A B z r hz hre hr
  have hprod := diagonalEnergy_product_le_card_of_kronecker_unitary A B hW
  have hcoef : 0 ≤ (7 / 2 : ℝ) * (Fintype.card γ : ℝ) := by positivity
  have hprodR : diagonalEnergy A * diagonalEnergy B ≤
      (Fintype.card (ProductIndex γ) : ℝ) := by exact_mod_cast hprod
  have hscaled := mul_le_mul_of_nonneg_left hprodR hcoef
  have hcard : (Fintype.card (ProductIndex γ) : ℝ) =
      4 * (Fintype.card γ : ℝ) := by
    simp [ProductIndex]
    ring
  calc
    ‖Matrix.trace ((A ⊗ₖ B)ᴴ * productControlledPhaseTarget z r)‖ ^ 2
        ≤ diagonalEnergy A * ((7 / 2 : ℝ) * (Fintype.card γ : ℝ) *
            diagonalEnergy B) := htrace
    _ = ((7 / 2 : ℝ) * (Fintype.card γ : ℝ)) *
          (diagonalEnergy A * diagonalEnergy B) := by ring
    _ ≤ ((7 / 2 : ℝ) * (Fintype.card γ : ℝ)) *
          (Fintype.card (ProductIndex γ) : ℝ) := hscaled
    _ = ((7 : ℝ) / 8) * (Fintype.card (ProductIndex γ) : ℝ) ^ 2 := by
      rw [hcard]
      ring

theorem productControlledPhaseTarget_unitary
    (z : ℂ) (r : Bool × γ → ℂ) (hz : ‖z‖ = 1) (hr : ∀ y, ‖r y‖ = 1) :
    (productControlledPhaseTarget z r)ᴴ * productControlledPhaseTarget z r = 1 := by
  let f : ProductIndex γ → ℂ :=
    fun x => r x.2 * if x.1 && x.2.1 then z else 1
  have hf : ∀ x, ‖f x‖ = 1 := by
    intro x
    dsimp only [f]
    rw [norm_mul, hr]
    split_ifs
    · rw [hz, one_mul]
    · simp
  change (Matrix.diagonal f)ᴴ * Matrix.diagonal f = 1
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext x
  have hs : Complex.normSq (f x) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hf]
    norm_num
  rw [Pi.star_apply]
  change (starRingEnd ℂ) (f x) * f x = 1
  rw [← Complex.normSq_eq_conj_mul_self]
  exact_mod_cast hs

theorem choiDist_kronecker_productControlledPhaseTarget_ge
    [Nonempty γ]
    (A : Matrix Bool Bool ℂ) (B : Matrix (Bool × γ) (Bool × γ) ℂ)
    (z : ℂ) (r : Bool × γ → ℂ) (hz : ‖z‖ = 1) (hre : z.re ≤ 0)
    (hr : ∀ y, ‖r y‖ = 1)
    (hW : (A ⊗ₖ B)ᴴ * (A ⊗ₖ B) = 1) :
    Real.sqrt ((1 : ℝ) / 8) ≤
      GaloisForLFunctions.RHTower.choiDist (A ⊗ₖ B)
        (productControlledPhaseTarget z r) := by
  let D : ℝ := Fintype.card (ProductIndex γ)
  have hDN : 0 < Fintype.card (ProductIndex γ) := Fintype.card_pos
  have hD : 0 < D := by
    change (0 : ℝ) < Fintype.card (ProductIndex γ)
    exact_mod_cast hDN
  have htrace := trace_productControlledPhaseTarget_norm_sq_le_seven_eighth
    A B z r hz hre hr hW
  have hratio :
      (‖Matrix.trace ((A ⊗ₖ B)ᴴ * productControlledPhaseTarget z r)‖ / D) ^ 2 ≤
        (7 : ℝ) / 8 := by
    rw [div_pow, div_le_iff₀ (sq_pos_of_pos hD)]
    dsimp only [D]
    nlinarith
  rw [GaloisForLFunctions.RHTower.choiDist_eq hDN]
  apply Real.sqrt_le_sqrt
  linarith

theorem controlledZ_product_choi_gap (n : ℕ)
    (A : Matrix Bool Bool ℂ)
    (B : Matrix (Bool × Fin (n + 1)) (Bool × Fin (n + 1)) ℂ)
    (hW : (A ⊗ₖ B)ᴴ * (A ⊗ₖ B) = 1) :
    Real.sqrt ((1 : ℝ) / 8) ≤
      GaloisForLFunctions.RHTower.choiDist (A ⊗ₖ B)
        (productControlledPhaseTarget (-1) (fun _ => 1)) := by
  apply choiDist_kronecker_productControlledPhaseTarget_ge
  · norm_num
  · norm_num
  · intro y
    norm_num
  · exact hW

end GaloisForLFunctions.HTGeometry.ControlledPhaseChoiCutGap
