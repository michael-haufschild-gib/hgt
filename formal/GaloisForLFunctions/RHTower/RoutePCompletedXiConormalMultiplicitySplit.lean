import GaloisForLFunctions.RHTower.RoutePCompletedXiConormalBaseResidue
import GaloisForLFunctions.RHTower.XiWeilCauchyCoreMultiplicity

/-!
# Route P completed Xi conormal multiplicity split

P-G182 exposed a quadratic-versus-linear analytic-multiplicity mismatch between a raw completed-Xi
logarithmic residue and the divisor Hilbert metric. This module proves that the existing
multiplicity-copy fibre removes that mismatch canonically. The codiagonal residue `m * v` has a
unique minimum-energy lift: put one copy of `v` on each of its `m` divisor copies. Equivalently,
split an arbitrary scalar residue equally by `1 / m`.

The split conserves total residue, has squared norm exactly `1 / m`, and satisfies an exact
Pythagorean variance law against every other residue-conserving copy resolution. Applied to the
actual completed-Xi conormal column, every fibre coordinate converges to P-G182's base radial
feature. Thus the forced inverse-square-root multiplicity half-density is already the operator norm
of canonical copy resolution; multiplicity is no longer part of Route P's open analytic bound.
-/

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-- Canonical equal split from one total residue to its analytic-multiplicity copy fibre. -/
def routePXiConormalMultiplicitySplit (rho : XiDivisorSupport) (v : ℂ) :
    Fin (xiSupportMultiplicity rho) → ℂ :=
  fun _ => v / (xiSupportMultiplicity rho : ℂ)

/-- The codiagonal of the equal split recovers the unsplit residue exactly. -/
theorem routePXiConormalMultiplicitySplit_sum
    (rho : XiDivisorSupport) (v : ℂ) :
    ∑ j, routePXiConormalMultiplicitySplit rho v j = v := by
  have hm : (xiSupportMultiplicity rho : ℂ) ≠ 0 := by
    exact_mod_cast (xiSupportMultiplicity_pos rho).ne'
  simp only [routePXiConormalMultiplicitySplit, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel₀ v hm

/-- Splitting a raw multiplicity residue puts one normalized residue on every copy. -/
theorem routePXiConormalMultiplicitySplit_raw_apply
    (rho : XiDivisorSupport) (v : ℂ)
    (j : Fin (xiSupportMultiplicity rho)) :
    routePXiConormalMultiplicitySplit rho
        ((xiSupportMultiplicity rho : ℂ) * v) j = v := by
  have hm : (xiSupportMultiplicity rho : ℂ) ≠ 0 := by
    exact_mod_cast (xiSupportMultiplicity_pos rho).ne'
  rw [routePXiConormalMultiplicitySplit]
  exact mul_div_cancel_left₀ v hm

/-- Squared norm of the equal-splitting operator is exactly inverse analytic multiplicity. -/
theorem routePXiConormalMultiplicitySplit_energy
    (rho : XiDivisorSupport) (v : ℂ) :
    ∑ j, Complex.normSq (routePXiConormalMultiplicitySplit rho v j) =
      Complex.normSq v / (xiSupportMultiplicity rho : ℝ) := by
  have hmR : (xiSupportMultiplicity rho : ℝ) ≠ 0 := by
    exact_mod_cast (xiSupportMultiplicity_pos rho).ne'
  simp only [routePXiConormalMultiplicitySplit, Complex.normSq_div,
    Complex.normSq_natCast, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The split raw residue has exactly the linear divisor-multiplicity energy. -/
theorem routePXiConormalMultiplicitySplit_raw_energy
    (rho : XiDivisorSupport) (v : ℂ) :
    ∑ j, Complex.normSq
        (routePXiConormalMultiplicitySplit rho
          ((xiSupportMultiplicity rho : ℂ) * v) j) =
      (xiSupportMultiplicity rho : ℝ) * Complex.normSq v := by
  simp_rw [routePXiConormalMultiplicitySplit_raw_apply]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Raw residue energy is multiplicity times its canonical copy-resolved energy. -/
theorem routePXiConormal_raw_energy_eq_multiplicity_mul_split_energy
    (rho : XiDivisorSupport) (v : ℂ) :
    Complex.normSq ((xiSupportMultiplicity rho : ℂ) * v) =
      (xiSupportMultiplicity rho : ℝ) *
        ∑ j, Complex.normSq
          (routePXiConormalMultiplicitySplit rho
            ((xiSupportMultiplicity rho : ℂ) * v) j) := by
  rw [routePXiConormalMultiplicitySplit_raw_energy, Complex.normSq_mul,
    Complex.normSq_natCast]
  ring

/-- Equal splitting is contractive from raw scalar energy to copy-resolved divisor energy. -/
theorem routePXiConormalMultiplicitySplit_raw_energy_le
    (rho : XiDivisorSupport) (v : ℂ) :
    (∑ j, Complex.normSq
        (routePXiConormalMultiplicitySplit rho
          ((xiSupportMultiplicity rho : ℂ) * v) j)) ≤
      Complex.normSq ((xiSupportMultiplicity rho : ℂ) * v) := by
  rw [routePXiConormal_raw_energy_eq_multiplicity_mul_split_energy]
  have hm : (1 : ℝ) ≤ xiSupportMultiplicity rho := by
    exact_mod_cast (xiSupportMultiplicity_pos rho)
  have henergy : 0 ≤ ∑ j, Complex.normSq
      (routePXiConormalMultiplicitySplit rho
        ((xiSupportMultiplicity rho : ℂ) * v) j) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  nlinarith

/-- Exact Hilbert variance law: among all copy vectors with raw codiagonal `m * v`, the equal
split is the orthogonal, minimum-energy lift. -/
theorem routePXiConormalMultiplicitySplit_pythagorean
    (rho : XiDivisorSupport) (v : ℂ)
    (u : Fin (xiSupportMultiplicity rho) → ℂ)
    (hsum : ∑ j, u j = (xiSupportMultiplicity rho : ℂ) * v) :
    ∑ j, Complex.normSq (u j) =
      (xiSupportMultiplicity rho : ℝ) * Complex.normSq v +
        ∑ j, Complex.normSq (u j - v) := by
  have hcross : ∑ j, (u j * (starRingEnd ℂ) v).re =
      (xiSupportMultiplicity rho : ℝ) * Complex.normSq v := by
    calc
      ∑ j, (u j * (starRingEnd ℂ) v).re =
          ((∑ j, u j) * (starRingEnd ℂ) v).re := by
        rw [Finset.sum_mul, Complex.re_sum]
      _ = (((xiSupportMultiplicity rho : ℂ) * v) * (starRingEnd ℂ) v).re := by
        rw [hsum]
      _ = (xiSupportMultiplicity rho : ℝ) * Complex.normSq v := by
        rw [mul_assoc, Complex.mul_conj]
        simp
  have hconst : ∑ _j : Fin (xiSupportMultiplicity rho), Complex.normSq v =
      (xiSupportMultiplicity rho : ℝ) * Complex.normSq v := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    ∑ j, Complex.normSq (u j) =
        (xiSupportMultiplicity rho : ℝ) * Complex.normSq v +
          ∑ j, (Complex.normSq (u j) + Complex.normSq v -
            2 * (u j * (starRingEnd ℂ) v).re) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hconst,
        ← Finset.mul_sum, hcross]
      ring
    _ = (xiSupportMultiplicity rho : ℝ) * Complex.normSq v +
        ∑ j, Complex.normSq (u j - v) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [Complex.normSq_sub]

/-- Consequently the canonical equal split is no more energetic than any copy resolution with
the same conserved raw residue. -/
theorem routePXiConormalMultiplicitySplit_minimal_energy
    (rho : XiDivisorSupport) (v : ℂ)
    (u : Fin (xiSupportMultiplicity rho) → ℂ)
    (hsum : ∑ j, u j = (xiSupportMultiplicity rho : ℂ) * v) :
    (∑ j, Complex.normSq
        (routePXiConormalMultiplicitySplit rho
          ((xiSupportMultiplicity rho : ℂ) * v) j)) ≤
      ∑ j, Complex.normSq (u j) := by
  rw [routePXiConormalMultiplicitySplit_raw_energy]
  rw [routePXiConormalMultiplicitySplit_pythagorean rho v u hsum]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

/-- Equality in the minimum-energy law forces the constant copy resolution, so the canonical
half-density lift is unique. -/
theorem routePXiConormalMultiplicitySplit_unique_minimizer
    (rho : XiDivisorSupport) (v : ℂ)
    (u : Fin (xiSupportMultiplicity rho) → ℂ)
    (hsum : ∑ j, u j = (xiSupportMultiplicity rho : ℂ) * v) :
    (∑ j, Complex.normSq (u j)) =
        ∑ j, Complex.normSq
          (routePXiConormalMultiplicitySplit rho
            ((xiSupportMultiplicity rho : ℂ) * v) j) ↔
      ∀ j, u j = v := by
  rw [routePXiConormalMultiplicitySplit_raw_energy]
  constructor
  · intro henergy
    rw [routePXiConormalMultiplicitySplit_pythagorean rho v u hsum] at henergy
    have hzero : ∑ j, Complex.normSq (u j - v) = 0 := by linarith
    intro j
    have hfun := (Fintype.sum_eq_zero_iff_of_nonneg
      (fun k => Complex.normSq_nonneg (u k - v))).mp hzero
    have hj : Complex.normSq (u j - v) = 0 := congrFun hfun j
    exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp hj)
  · intro hu
    calc
      ∑ j, Complex.normSq (u j) =
          ∑ _j : Fin (xiSupportMultiplicity rho), Complex.normSq v := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hu j]
      _ = (xiSupportMultiplicity rho : ℝ) * Complex.normSq v := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Copy resolution converts the actual raw completed-Xi conormal residue into one base feature on
every analytic-multiplicity copy. -/
theorem routePCompletedXiConormalColumn_fiber_residue
    (rho : XiDivisorSupport)
    (j : Fin (xiSupportMultiplicity rho)) (r : ℝ) :
    Tendsto
      (fun z : ℂ =>
        routePXiConormalMultiplicitySplit rho
          ((z - (rho : ℂ)) * routePCompletedXiConormalColumn z r) j)
      (nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ))
      (nhds (routePXiBaseConormalResidueFeature (rho : ℂ) r)) := by
  change Tendsto
    (fun z : ℂ =>
      ((z - (rho : ℂ)) * routePCompletedXiConormalColumn z r) /
        (xiSupportMultiplicity rho : ℂ))
    (nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ))
    (nhds (routePXiBaseConormalResidueFeature (rho : ℂ) r))
  rw [xiSupportMultiplicity_eq_analyticOrderAt_toNat]
  exact routePCompletedXiConormalColumn_normalized_residue
    (xi_eq_zero_of_mem_divisor_support rho) r

end

end RHTower
