import GaloisForLFunctions.RHTower.SchanuelDefectLattice
import Mathlib.LinearAlgebra.LinearIndependent.Basic

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Logarithmic Kähler defect of an arbitrary ordered additive/multiplicative pair. -/
def kaehlerPairDefect (R K : Type*) [CommRing R] [Field K] [Algebra R K]
    (x y : K) : KaehlerDifferential R K :=
  y⁻¹ • KaehlerDifferential.D R K y - KaehlerDifferential.D R K x

/-- Exact branch-defect identity before dividing by the nonzero branch denominator. -/
theorem smul_kaehlerPairDefect_eq_of_zpow_of_affine
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (x y z w tau : K) (m k : ℤ) (hw0 : w ≠ 0)
    (hw : w ^ m = y)
    (hz : (m : K) * z = x + (k : K) * tau) :
    (m : K) • kaehlerPairDefect R K z w =
      kaehlerPairDefect R K x y - (k : K) • KaehlerDifferential.D R K tau := by
  let D := KaehlerDifferential.D R K
  have hlog := derivation_log_zpow D w m hw0
  rw [hw] at hlog
  have hcoord : (m : K) • D z = D x + (k : K) • D tau := by
    calc
      (m : K) • D z = D ((m : K) * z) := by
        rw [D.leibniz]
        simp
      _ = D (x + (k : K) * tau) := congrArg D hz
      _ = D x + (k : K) • D tau := by
        rw [map_add, D.leibniz]
        simp
  simp only [kaehlerPairDefect, smul_sub]
  rw [← hlog, hcoord]
  abel

/-- Exact divided branch-defect formula. -/
theorem kaehlerPairDefect_eq_inv_smul_of_zpow_of_affine
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (x y z w tau : K) (m k : ℤ) (hmK : (m : K) ≠ 0) (hw0 : w ≠ 0)
    (hw : w ^ m = y)
    (hz : (m : K) * z = x + (k : K) * tau) :
    kaehlerPairDefect R K z w =
      ((m : K)⁻¹) •
        (kaehlerPairDefect R K x y - (k : K) • KaehlerDifferential.D R K tau) := by
  rw [← smul_kaehlerPairDefect_eq_of_zpow_of_affine x y z w tau m k hw0 hw hz,
    smul_smul, inv_mul_cancel₀ hmK, one_smul]

/-- Two affine shifts of a rank-one defect pair have rank two precisely when the coefficient
determinant is nonzero. -/
theorem linearIndependent_rankOne_period_shift
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (epsilon dtau : V) (hbase : LinearIndependent F ![epsilon, dtau])
    (rho k₁ k₂ : F) (hdet : k₁ * rho - k₂ ≠ 0) :
    LinearIndependent F ![epsilon - k₁ • dtau, rho • epsilon - k₂ • dtau] := by
  let shifted : Fin 2 → V := ![epsilon - k₁ • dtau, rho • epsilon - k₂ • dtau]
  change LinearIndependent F shifted
  rw [Fintype.linearIndependent_iff]
  intro q hq i
  let p : Fin 2 → F := ![q 0 + q 1 * rho, -(q 0 * k₁ + q 1 * k₂)]
  have hp : ∑ j, p j • ![epsilon, dtau] j = 0 := by
    rw [Fin.sum_univ_two]
    simp only [p, Matrix.cons_val_zero, Matrix.cons_val_one]
    calc
      (q 0 + q 1 * rho) • epsilon + -(q 0 * k₁ + q 1 * k₂) • dtau =
          q 0 • shifted 0 + q 1 • shifted 1 := by
            simp only [shifted, Matrix.cons_val_zero, Matrix.cons_val_one]
            module
      _ = 0 := by simpa [Fin.sum_univ_two] using hq
  have hp0 := Fintype.linearIndependent_iff.mp hbase p hp 0
  have hp1 := Fintype.linearIndependent_iff.mp hbase p hp 1
  simp only [p, Matrix.cons_val_zero, Matrix.cons_val_one] at hp0 hp1
  have hq1det : (k₁ * rho - k₂) * q 1 = 0 := by
    linear_combination k₁ * hp0 + hp1
  have hq1 : q 1 = 0 := (mul_eq_zero.mp hq1det).resolve_left hdet
  have hq0 : q 0 = 0 := by simpa [hq1] using hp0
  fin_cases i
  · exact hq0
  · exact hq1

/-- Multiplying both shifted defects by one common nonzero inverse denominator preserves their
rank-two conclusion. -/
theorem linearIndependent_rankOne_period_shift_inv_smul
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (epsilon dtau : V) (hbase : LinearIndependent F ![epsilon, dtau])
    (rho k₁ k₂ m : F) (hdet : k₁ * rho - k₂ ≠ 0) (hm : m ≠ 0) :
    LinearIndependent F ![
      m⁻¹ • (epsilon - k₁ • dtau),
      m⁻¹ • (rho • epsilon - k₂ • dtau)] := by
  let shifted : Fin 2 → V :=
    ![epsilon - k₁ • dtau, rho • epsilon - k₂ • dtau]
  have hshifted : LinearIndependent F shifted :=
    linearIndependent_rankOne_period_shift epsilon dtau hbase rho k₁ k₂ hdet
  let f : V →ₗ[F] V := LinearMap.lsmul F V m⁻¹
  have hf : LinearMap.ker f = ⊥ := LinearMap.ker_lsmul (inv_ne_zero hm)
  have himage := hshifted.map' f hf
  have hfun : (fun i => f (shifted i)) =
      ![m⁻¹ • (epsilon - k₁ • dtau), m⁻¹ • (rho • epsilon - k₂ • dtau)] := by
    funext i
    fin_cases i <;> simp [shifted, f]
  rw [← hfun]
  exact himage

end

end GaloisForLFunctions.RHTower

