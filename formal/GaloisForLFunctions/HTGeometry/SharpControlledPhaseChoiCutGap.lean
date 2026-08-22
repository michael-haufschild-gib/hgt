import GaloisForLFunctions.HTGeometry.ControlledPhaseChoiCutGap

open scoped BigOperators Matrix Kronecker
open Matrix

/-!
# Sharp controlled-phase Choi cut gap

`ControlledPhaseChoiCutGap` bounds `‖1 + z‖` by `3/2` for a unit phase in the closed left
half-plane and obtains the rational normalized-fidelity ceiling `7/8`.  The extremal value of
`‖1 + z‖` on that half-circle is `√2`, attained at `z = ±i`, so the same Cauchy--Schwarz /
Gram-eigenvalue chain gives the *sharp* ceiling `(2 + √2)/4` and therefore the sharp uniform
trace-distance gap

`ε⋆ = √((1 - 2^{-1/2})/2) = √((2 - √2)/4) > √(1/8)`.

Writing `z = e^{-iφ}`, `‖1 + z‖ = 2|cos(φ/2)|`, so the constant below is the Gram largest
eigenvalue `N(1 + |cos(φ/2)|)` of the two target phase vectors, normalized by the full
Hilbert--Schmidt mass of the factorized circuit.
-/

namespace GaloisForLFunctions.HTGeometry.SharpControlledPhaseChoiCutGap

open GaloisForLFunctions.HTGeometry.ControlledPhaseChoiCutGap

/-- The sharp chord bound on the closed left half of the unit circle. -/
theorem norm_one_add_le_sqrt_two_of_unit_re_nonpos (z : ℂ)
    (hz : ‖z‖ = 1) (hre : z.re ≤ 0) :
    ‖1 + z‖ ≤ Real.sqrt 2 := by
  have hs := norm_add_sq (𝕜 := ℂ) (1 : ℂ) z
  have hsq : ‖1 + z‖ ^ 2 ≤ 2 := by
    simp [RCLike.inner_apply, hz] at hs
    nlinarith
  have hmono := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _)] at hmono

/-- Sharp two-phase energy bound: the Gram largest eigenvalue is `2 + ‖1 + z‖ ≤ 2 + √2`. -/
theorem two_phase_pair_energy_le_sharp (P Q z : ℂ)
    (hz : ‖z‖ = 1) (hre : z.re ≤ 0) :
    ‖P + Q‖ ^ 2 + ‖P + z * Q‖ ^ 2 ≤
      (2 + Real.sqrt 2) * (‖P‖ ^ 2 + ‖Q‖ ^ 2) := by
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
  have hphase := norm_one_add_le_sqrt_two_of_unit_re_nonpos z hz hre
  have hnonnegP := norm_nonneg P
  have hnonnegQ := norm_nonneg Q
  have hcrossR :
      RCLike.re (inner ℂ P Q) + RCLike.re (inner ℂ P (z * Q)) =
        RCLike.re (inner ℂ P ((1 + z) * Q)) := hcross
  have hprod : ‖P‖ * ‖1 + z‖ * ‖Q‖ ≤ Real.sqrt 2 * ‖P‖ * ‖Q‖ := by
    have := mul_le_mul_of_nonneg_left hphase hnonnegP
    exact mul_le_mul_of_nonneg_right (by linarith) hnonnegQ
  have hcrossBound :
      RCLike.re (inner ℂ P Q) + RCLike.re (inner ℂ P (z * Q)) ≤
        Real.sqrt 2 * ‖P‖ * ‖Q‖ := by
    rw [hcrossR]
    exact hinner.trans hprod
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rw [hzQ] at h2
  rw [h1, h2]
  nlinarith [sq_nonneg (‖P‖ - ‖Q‖), hcrossBound, hs2]

variable {γ : Type*} [Fintype γ] [DecidableEq γ]

omit [DecidableEq γ] in
theorem phase_pair_energy_le_diagonalEnergy_sharp
    (B : Matrix (Bool × γ) (Bool × γ) ℂ) (z : ℂ)
    (r : Bool × γ → ℂ) (hz : ‖z‖ = 1) (hre : z.re ≤ 0)
    (hr : ∀ y, ‖r y‖ = 1) :
    ‖phaseFibreSum B r false + phaseFibreSum B r true‖ ^ 2 +
        ‖phaseFibreSum B r false + z * phaseFibreSum B r true‖ ^ 2 ≤
      (2 + Real.sqrt 2) * (Fintype.card γ : ℝ) * diagonalEnergy B := by
  have hp := phaseFibreSum_norm_sq_le B r hr false
  have hq := phaseFibreSum_norm_sq_le B r hr true
  have hpair := two_phase_pair_energy_le_sharp
    (phaseFibreSum B r false) (phaseFibreSum B r true) z hz hre
  have hdiag : diagonalEnergy B =
      (∑ g : γ, ‖B (false, g) (false, g)‖ ^ 2) +
        ∑ g : γ, ‖B (true, g) (true, g)‖ ^ 2 := by
    unfold diagonalEnergy
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    ring
  have hsum : ‖phaseFibreSum B r false‖ ^ 2 + ‖phaseFibreSum B r true‖ ^ 2 ≤
      (Fintype.card γ : ℝ) * diagonalEnergy B := by
    rw [hdiag, mul_add]
    linarith
  have hc : (0 : ℝ) ≤ 2 + Real.sqrt 2 := by positivity
  calc
    ‖phaseFibreSum B r false + phaseFibreSum B r true‖ ^ 2 +
        ‖phaseFibreSum B r false + z * phaseFibreSum B r true‖ ^ 2
        ≤ (2 + Real.sqrt 2) *
            (‖phaseFibreSum B r false‖ ^ 2 + ‖phaseFibreSum B r true‖ ^ 2) := hpair
    _ ≤ (2 + Real.sqrt 2) * ((Fintype.card γ : ℝ) * diagonalEnergy B) :=
        mul_le_mul_of_nonneg_left hsum hc
    _ = (2 + Real.sqrt 2) * (Fintype.card γ : ℝ) * diagonalEnergy B := by ring

theorem trace_productControlledPhaseTarget_norm_sq_le_sharp
    (A : Matrix Bool Bool ℂ) (B : Matrix (Bool × γ) (Bool × γ) ℂ)
    (z : ℂ) (r : Bool × γ → ℂ) (hz : ‖z‖ = 1) (hre : z.re ≤ 0)
    (hr : ∀ y, ‖r y‖ = 1) :
    ‖Matrix.trace ((A ⊗ₖ B)ᴴ * productControlledPhaseTarget z r)‖ ^ 2 ≤
      diagonalEnergy A * ((2 + Real.sqrt 2) * (Fintype.card γ : ℝ) *
        diagonalEnergy B) := by
  rw [trace_kronecker_conj_productControlledPhaseTarget_eq_pair]
  have hc := norm_two_term_sq_le
    (starRingEnd ℂ (A false false)) (starRingEnd ℂ (A true true))
    (phaseFibreSum B r false + phaseFibreSum B r true)
    (phaseFibreSum B r false + z * phaseFibreSum B r true)
  have hpair := phase_pair_energy_le_diagonalEnergy_sharp B z r hz hre hr
  have hdiagA : diagonalEnergy A = ‖A false false‖ ^ 2 + ‖A true true‖ ^ 2 := by
    unfold diagonalEnergy
    simp
    ring
  rw [RCLike.norm_conj, RCLike.norm_conj, ← hdiagA] at hc
  have hdiagA0 : 0 ≤ diagonalEnergy A := by
    unfold diagonalEnergy
    positivity
  exact hc.trans (mul_le_mul_of_nonneg_left hpair hdiagA0)

/-- The sharp normalized-fidelity ceiling `(2 + √2)/4` replacing the rational `7/8`. -/
theorem trace_productControlledPhaseTarget_norm_sq_le_sharp_const
    (A : Matrix Bool Bool ℂ) (B : Matrix (Bool × γ) (Bool × γ) ℂ)
    (z : ℂ) (r : Bool × γ → ℂ) (hz : ‖z‖ = 1) (hre : z.re ≤ 0)
    (hr : ∀ y, ‖r y‖ = 1)
    (hW : (A ⊗ₖ B)ᴴ * (A ⊗ₖ B) = 1) :
    ‖Matrix.trace ((A ⊗ₖ B)ᴴ * productControlledPhaseTarget z r)‖ ^ 2 ≤
      ((2 + Real.sqrt 2) / 4) * (Fintype.card (ProductIndex γ) : ℝ) ^ 2 := by
  have htrace := trace_productControlledPhaseTarget_norm_sq_le_sharp A B z r hz hre hr
  have hprod := diagonalEnergy_product_le_card_of_kronecker_unitary A B hW
  have hcoef : 0 ≤ (2 + Real.sqrt 2) * (Fintype.card γ : ℝ) := by positivity
  have hprodR : diagonalEnergy A * diagonalEnergy B ≤
      (Fintype.card (ProductIndex γ) : ℝ) := by exact_mod_cast hprod
  have hscaled := mul_le_mul_of_nonneg_left hprodR hcoef
  have hcard : (Fintype.card (ProductIndex γ) : ℝ) =
      4 * (Fintype.card γ : ℝ) := by
    simp [ProductIndex]
    ring
  calc
    ‖Matrix.trace ((A ⊗ₖ B)ᴴ * productControlledPhaseTarget z r)‖ ^ 2
        ≤ diagonalEnergy A * ((2 + Real.sqrt 2) * (Fintype.card γ : ℝ) *
            diagonalEnergy B) := htrace
    _ = ((2 + Real.sqrt 2) * (Fintype.card γ : ℝ)) *
          (diagonalEnergy A * diagonalEnergy B) := by ring
    _ ≤ ((2 + Real.sqrt 2) * (Fintype.card γ : ℝ)) *
          (Fintype.card (ProductIndex γ) : ℝ) := hscaled
    _ = ((2 + Real.sqrt 2) / 4) * (Fintype.card (ProductIndex γ) : ℝ) ^ 2 := by
      rw [hcard]
      ring

/-- The sharp uniform Choi trace-distance gap `ε⋆ = √((2 - √2)/4)`. -/
noncomputable def epsilonStar : ℝ := Real.sqrt ((2 - Real.sqrt 2) / 4)

theorem epsilonStar_eq_card_form :
    epsilonStar = Real.sqrt ((1 - 1 / Real.sqrt 2) / 2) := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hinv : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    field_simp
    linarith [h2]
  rw [epsilonStar, hinv]
  ring_nf

theorem sqrt_one_div_eight_lt_epsilonStar : Real.sqrt ((1 : ℝ) / 8) < epsilonStar := by
  have hlt : (1 : ℝ) / 8 < (2 - Real.sqrt 2) / 4 := by
    have h : Real.sqrt 2 < 3 / 2 := by
      have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg 2]
    linarith
  exact Real.sqrt_lt_sqrt (by norm_num) hlt

theorem epsilonStar_nonneg : 0 ≤ epsilonStar := Real.sqrt_nonneg _

theorem choiDist_kronecker_productControlledPhaseTarget_ge_sharp
    [Nonempty γ]
    (A : Matrix Bool Bool ℂ) (B : Matrix (Bool × γ) (Bool × γ) ℂ)
    (z : ℂ) (r : Bool × γ → ℂ) (hz : ‖z‖ = 1) (hre : z.re ≤ 0)
    (hr : ∀ y, ‖r y‖ = 1)
    (hW : (A ⊗ₖ B)ᴴ * (A ⊗ₖ B) = 1) :
    epsilonStar ≤
      GaloisForLFunctions.RHTower.choiDist (A ⊗ₖ B)
        (productControlledPhaseTarget z r) := by
  let D : ℝ := Fintype.card (ProductIndex γ)
  have hDN : 0 < Fintype.card (ProductIndex γ) := Fintype.card_pos
  have hD : 0 < D := by
    change (0 : ℝ) < Fintype.card (ProductIndex γ)
    exact_mod_cast hDN
  have htrace := trace_productControlledPhaseTarget_norm_sq_le_sharp_const
    A B z r hz hre hr hW
  have hratio :
      (‖Matrix.trace ((A ⊗ₖ B)ᴴ * productControlledPhaseTarget z r)‖ / D) ^ 2 ≤
        (2 + Real.sqrt 2) / 4 := by
    rw [div_pow, div_le_iff₀ (sq_pos_of_pos hD)]
    dsimp only [D]
    nlinarith
  rw [GaloisForLFunctions.RHTower.choiDist_eq hDN, epsilonStar]
  apply Real.sqrt_le_sqrt
  linarith

end GaloisForLFunctions.HTGeometry.SharpControlledPhaseChoiCutGap
