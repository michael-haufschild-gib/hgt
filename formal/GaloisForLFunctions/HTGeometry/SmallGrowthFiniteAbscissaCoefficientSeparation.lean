import GaloisForLFunctions.HTGeometry.FiniteAbscissaRationalCoordinateIndependence
import GaloisForLFunctions.HTGeometry.SmallGrowthDirichletCoefficientSeparation

/-!
# Small-growth coefficient separation in the upper-end meromorphic carrier

This module clears the chosen entire denominators of `F_s` coefficients inside the upper-end
fraction field.  It converts a carrier equality into the literal rotated L-series relation on a
codiscrete subset of a sufficiently high half-plane.
-/

open Filter Set Topology LSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance smallGrowthSeparationUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

/-- Simultaneously clearing a finite family of fraction coefficients leaves an equality in the
upper-end analytic domain. -/
theorem upperEnd_clear_fraction_linear_relation {d : ℕ}
    (N D L : Fin d → upperEndAnalyticSubring) (hD : ∀ i, D i ≠ 0)
    (h : ∑ i, (algebraMap upperEndAnalyticSubring upperEndMeroField (N i) /
          algebraMap upperEndAnalyticSubring upperEndMeroField (D i)) *
        algebraMap upperEndAnalyticSubring upperEndMeroField (L i) = 0) :
    ∑ i, N i * L i *
      ∏ j ∈ (Finset.univ : Finset (Fin d)).erase i, D j = 0 := by
  let P : upperEndAnalyticSubring := ∏ i, D i
  have hmul := congrArg (fun z : upperEndMeroField =>
    algebraMap upperEndAnalyticSubring upperEndMeroField P * z) h
  rw [mul_zero, Finset.mul_sum] at hmul
  have heach : ∀ i,
      algebraMap upperEndAnalyticSubring upperEndMeroField P *
          ((algebraMap upperEndAnalyticSubring upperEndMeroField (N i) /
            algebraMap upperEndAnalyticSubring upperEndMeroField (D i)) *
            algebraMap upperEndAnalyticSubring upperEndMeroField (L i)) =
        algebraMap upperEndAnalyticSubring upperEndMeroField
          (N i * L i *
            ∏ j ∈ (Finset.univ : Finset (Fin d)).erase i, D j) := by
    intro i
    have hDi : algebraMap upperEndAnalyticSubring upperEndMeroField (D i) ≠ 0 := by
      simpa only [map_zero] using
        (IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField).ne (hD i)
    have hP : D i * ∏ j ∈ (Finset.univ : Finset (Fin d)).erase i, D j = P :=
      Finset.mul_prod_erase Finset.univ D (Finset.mem_univ i)
    rw [← hP]
    simp only [map_mul]
    field_simp
  rw [Finset.sum_congr rfl (fun i _ => heach i), ← map_sum] at hmul
  exact (IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField)
    (hmul.trans (map_zero _).symm)

/-- An equality in the upper-end meromorphic field with coefficients in `F_s` yields the literal
rotated L-series relation off a codiscrete exceptional set and above one finite height. -/
theorem upperEnd_smallGrowth_relation_eventually_rotated {d : ℕ}
    (A : Fin d → finiteAbscissaArithmeticSubalgebra)
    (phi : Fin d → SmallGrowthMeromorphicField)
    (hrel : ∑ i, smallGrowthMeromorphicToUpperEnd (phi i) *
      finiteAbscissaLSeriesToUpperEndMero (A i) = 0) :
    ∃ H : ℝ, ∀ᶠ z in Filter.codiscrete ℂ, H < z.im →
      ∑ i, smallGrowthFunction (phi i) z *
        LSeries (fun n => (A i).1 n) (-Complex.I * z) = 0 := by
  classical
  let p : ∀ i : Fin d, EntireFractionPresentation ((phi i : SmallGrowthMeromorphicField) :
      EntireField ℂ) := fun i => smallGrowthPresentation (phi i)
  let N : Fin d → upperEndAnalyticSubring := fun i =>
    entireToUpperEndAnalytic (p i).numerator
  let D : Fin d → upperEndAnalyticSubring := fun i =>
    entireToUpperEndAnalytic (p i).denominator
  let L : Fin d → upperEndAnalyticSubring := fun i =>
    finiteAbscissaLSeriesToUpperEndAnalytic (A i)
  have hD : ∀ i, D i ≠ 0 := by
    intro i
    exact entireToUpperEndAnalytic_injective.ne (p i).denominator_ne_zero
  have hphi : ∀ i, smallGrowthMeromorphicToUpperEnd (phi i) =
      algebraMap upperEndAnalyticSubring upperEndMeroField (N i) /
        algebraMap upperEndAnalyticSubring upperEndMeroField (D i) := by
    intro i
    change entireFieldToUpperEndMero ((phi i : SmallGrowthMeromorphicField) : EntireField ℂ) = _
    rw [(p i).eq_div, map_div₀]
    simp only [entireFieldToUpperEndMero_algebraMap, N, D]
  have hrel' : ∑ i,
      (algebraMap upperEndAnalyticSubring upperEndMeroField (N i) /
        algebraMap upperEndAnalyticSubring upperEndMeroField (D i)) *
          algebraMap upperEndAnalyticSubring upperEndMeroField (L i) = 0 := by
    simpa only [hphi, finiteAbscissaLSeriesToUpperEndMero_eq_algebraMap, L] using hrel
  have hclear := upperEnd_clear_fraction_linear_relation N D L hD hrel'
  let cleared : ℂ → ℂ := fun z =>
    ∑ i, ((p i).numerator : ℂ → ℂ) z *
      LSeries (fun n => (A i).1 n) (-Complex.I * z) *
        ∏ j ∈ (Finset.univ : Finset (Fin d)).erase i,
          ((p j).denominator : ℂ → ℂ) z
  have hclearedGerm : Germ.coeRingHom upperEndFilter cleared = 0 := by
    have hval := congrArg (fun q : upperEndAnalyticSubring =>
      (q : Germ upperEndFilter ℂ)) hclear
    rw [ZeroMemClass.coe_zero] at hval
    calc
      Germ.coeRingHom upperEndFilter cleared =
          ∑ i, Germ.coeRingHom upperEndFilter
            (fun z => ((p i).numerator : ℂ → ℂ) z *
              LSeries (fun n => (A i).1 n) (-Complex.I * z) *
                ∏ j ∈ (Finset.univ : Finset (Fin d)).erase i,
                  ((p j).denominator : ℂ → ℂ) z) := by
        rw [show cleared = ∑ i, fun z => ((p i).numerator : ℂ → ℂ) z *
            LSeries (fun n => (A i).1 n) (-Complex.I * z) *
              ∏ j ∈ (Finset.univ : Finset (Fin d)).erase i,
                ((p j).denominator : ℂ → ℂ) z by
          funext z
          simp [cleared]]
        rw [map_sum]
      _ = ∑ i, ((N i * L i *
          ∏ j ∈ (Finset.univ : Finset (Fin d)).erase i, D j :
            upperEndAnalyticSubring) : Germ upperEndFilter ℂ) := by
        apply Finset.sum_congr rfl
        intro i _
        change Germ.coeRingHom upperEndFilter
            (((p i).numerator : ℂ → ℂ) *
              (fun z => LSeries (fun n => (A i).1 n) (-Complex.I * z)) *
                ∏ j ∈ (Finset.univ : Finset (Fin d)).erase i,
                  ((p j).denominator : ℂ → ℂ)) = _
        rw [MulMemClass.coe_mul, MulMemClass.coe_mul, map_mul, map_mul]
        simp only [N, D, L, entireToUpperEndAnalytic_coe,
          finiteAbscissaLSeriesToUpperEndAnalytic_coe,
          finiteAbscissaLSeriesToUpperEndGerm]
        rw [map_prod]
        rfl
      _ = 0 := by simpa only [map_sum] using hval
  rw [← Germ.coe_zero, Germ.coe_eq] at hclearedGerm
  rw [upperEndFilter_basis.eventually_iff] at hclearedGerm
  obtain ⟨H, -, hH⟩ := hclearedGerm
  refine ⟨H, ?_⟩
  have hden : ∀ᶠ z in Filter.codiscrete ℂ, ∀ i,
      ((p i).denominator : ℂ → ℂ) z ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    exact (p i).denominator_eventually_ne_zero
  filter_upwards [hden] with z hz
  intro hzH
  have hclearZ : cleared z = 0 := hH hzH
  let Pz : ℂ := ∏ i, ((p i).denominator : ℂ → ℂ) z
  have hPz : Pz ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hz i
  have heach : ∀ i,
      Pz * (smallGrowthFunction (phi i) z *
        LSeries (fun n => (A i).1 n) (-Complex.I * z)) =
      ((p i).numerator : ℂ → ℂ) z *
        LSeries (fun n => (A i).1 n) (-Complex.I * z) *
          ∏ j ∈ (Finset.univ : Finset (Fin d)).erase i,
            ((p j).denominator : ℂ → ℂ) z := by
    intro i
    change Pz * (((p i).numerator : ℂ → ℂ) z /
        ((p i).denominator : ℂ → ℂ) z *
          LSeries (fun n => (A i).1 n) (-Complex.I * z)) = _
    have hprod : ((p i).denominator : ℂ → ℂ) z *
        ∏ j ∈ (Finset.univ : Finset (Fin d)).erase i,
          ((p j).denominator : ℂ → ℂ) z = Pz := by
      exact Finset.mul_prod_erase Finset.univ
        (fun j => ((p j).denominator : ℂ → ℂ) z) (Finset.mem_univ i)
    rw [← hprod]
    field_simp
    ring
  have hmul : Pz * ∑ i, smallGrowthFunction (phi i) z *
      LSeries (fun n => (A i).1 n) (-Complex.I * z) = 0 := by
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun i _ => heach i)]
    exact hclearZ
  exact (mul_eq_zero.mp hmul).resolve_left hPz

end

end GaloisForLFunctions.HTGeometry
