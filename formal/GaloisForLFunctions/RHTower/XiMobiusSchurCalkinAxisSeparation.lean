import GaloisForLFunctions.RHTower.XiMobiusSchurValuationIntertwiner
import GaloisForLFunctions.RHTower.XiPrimeSeamSparseEdgeCalkin
import GaloisForLFunctions.HTGeometry.HilbertSchmidtRectangular
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact

/-!
# Prime-index Schur compactness does not imply Sonin/Calkin compactness

The genuine Möbius Schur depth derivative is square-summable jointly in prime and valuation
depth.  It therefore defines a Hilbert--Schmidt, hence compact, rectangular operator from the
depth Hilbert space to the prime Hilbert space.

This is not the compactness required by the prime-seam route.  Every coefficient of the same
Schur Gram is strictly positive, and lifting even one such coefficient to the literal Sonin
quadratic corner produces a noncompact operator.  Prime-index decay and internal Calkin
compactness are different axes: a globally compact arithmetic marking cannot be substituted for
eventual compactness of the adjacent-prime seam corners.

This closes the tempting Gamma-Schur-to-SEC shortcut.  A viable bridge must regularize the
internal infinite-multiplicity Sonin carrier coefficient-faithfully; summability across prime
labels alone cannot do it.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Rectangular coefficient matrix of the actual Möbius Schur forward differences: prime rows,
valuation-depth columns. -/
def xiMobiusPrimeSchurDifferenceRectKernel : Nat.Primes × ℕ → ℂ :=
  fun pe => (xiMobiusPrimeSchurForwardDifference pe.1 pe.2 : ℂ)

/-- Each prime row has finite squared depth energy. -/
theorem summable_normSq_xiMobiusPrimeSchurForwardDifference
    (p : Nat.Primes) :
    Summable (fun e : ℕ => ‖(xiMobiusPrimeSchurForwardDifference p e : ℂ)‖ ^ 2) := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hq1 : q < 1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  have hplus : 1 + q ≠ 0 := by linarith
  have hgeom : Summable (fun e : ℕ => (q ^ 2) ^ e) := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg q)]
    nlinarith
  refine (hgeom.mul_left (q ^ 2 * (1 - q) ^ 2 / (1 + q) ^ 2)).congr (fun e => ?_)
  rw [xiMobiusPrimeSchurForwardDifference_eq_geometric]
  dsimp only [q]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  field_simp [hplus]
  ring

/-- The squared depth energy of one row is its exact completed Schur diagonal. -/
theorem tsum_normSq_xiMobiusPrimeSchurForwardDifference
    (p : Nat.Primes) :
    (∑' e : ℕ, ‖(xiMobiusPrimeSchurForwardDifference p e : ℂ)‖ ^ 2) =
      xiMobiusPrimeSchurDifferenceKernel p p := by
  rw [← tsum_xiMobiusPrimeSchurForwardDifference_mul_eq_kernel p p]
  apply tsum_congr
  intro e
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

/-- Joint prime-depth square summability of the literal source coefficients. -/
theorem xiMobiusPrimeSchurDifferenceRectKernel_isHSRect :
    HilbertSchmidt.IsHSRect xiMobiusPrimeSchurDifferenceRectKernel := by
  rw [HilbertSchmidt.IsHSRect,
    summable_prod_of_nonneg (fun _ => sq_nonneg _)]
  refine ⟨?_, ?_⟩
  · intro p
    exact summable_normSq_xiMobiusPrimeSchurForwardDifference p
  · refine summable_xiMobiusPrimeSchurDifferenceKernel_self.congr (fun p => ?_)
    change xiMobiusPrimeSchurDifferenceKernel p p =
      ∑' y : ℕ, ‖(xiMobiusPrimeSchurForwardDifference p y : ℂ)‖ ^ 2
    exact (tsum_normSq_xiMobiusPrimeSchurForwardDifference p).symm

/-- Genuine prime-by-depth Möbius Schur synthesis operator. -/
def xiMobiusPrimeSchurDifferenceRectOperator :
    lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : Nat.Primes => ℂ) 2 :=
  HilbertSchmidt.toOperatorRect xiMobiusPrimeSchurDifferenceRectKernel_isHSRect

/-- The arithmetic Schur synthesis is Hilbert--Schmidt. -/
theorem xiMobiusPrimeSchurDifferenceRectOperator_isHilbertSchmidt :
    xiMobiusPrimeSchurDifferenceRectOperator.IsHilbertSchmidt :=
  HilbertSchmidt.isHilbertSchmidt_toOperatorRect
    xiMobiusPrimeSchurDifferenceRectKernel_isHSRect

/-- Consequently the prime-index arithmetic Schur synthesis is compact. -/
theorem xiMobiusPrimeSchurDifferenceRectOperator_isCompactOperator :
    IsCompactOperator xiMobiusPrimeSchurDifferenceRectOperator :=
  xiMobiusPrimeSchurDifferenceRectOperator_isHilbertSchmidt.isCompactOperator

/-- Every cross-prime coefficient of the completed Möbius Schur Gram is strictly positive. -/
theorem xiMobiusPrimeSchurDifferenceKernel_pos (p q : Nat.Primes) :
    0 < xiMobiusPrimeSchurDifferenceKernel p q := by
  have hp0 := xiTransversePrimeApertureDiskNode_pos 1 p
  have hq0 := xiTransversePrimeApertureDiskNode_pos 1 q
  have hp1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num : (0 : ℕ) < 1) p
  have hq1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num : (0 : ℕ) < 1) q
  have hpq1 : xiTransversePrimeApertureDiskNode 1 p *
      xiTransversePrimeApertureDiskNode 1 q < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left hp0.le hp1 hq1.le
  simp only [xiMobiusPrimeSchurDifferenceKernel]
  exact div_pos
    (mul_pos (mul_pos (mul_pos hp0 hq0) (sub_pos.mpr hp1)) (sub_pos.mpr hq1))
    (mul_pos (mul_pos (by positivity) (by positivity)) (sub_pos.mpr hpq1))

/-- **Axis-separation no-go.** Although the complete prime-depth coefficient matrix is compact,
lifting any one of its nonzero Gram coefficients to the literal infinite Sonin corner is
noncompact. -/
theorem xiMobiusPrimeSchurDifference_soninLift_not_isCompactOperator
    {a : ℝ} (ha : 0 < a) (p q : Nat.Primes) :
    ¬ IsCompactOperator
      (xiSeamCoboundaryCorner a ((p : ℕ) : ℝ) ((q : ℕ) : ℝ)
        (one_lt_natPrime_cast p) (one_lt_natPrime_cast q)
        (xiMobiusPrimeSchurDifferenceKernel p q : ℂ)) := by
  intro hcompact
  have hzero := eq_zero_of_isCompactOperator_xiSeamCoboundaryCorner
    ha (one_lt_natPrime_cast p) (one_lt_natPrime_cast q) hcompact
  exact (Complex.ofReal_ne_zero.mpr
    (xiMobiusPrimeSchurDifferenceKernel_pos p q).ne') hzero

end

end RHTower
