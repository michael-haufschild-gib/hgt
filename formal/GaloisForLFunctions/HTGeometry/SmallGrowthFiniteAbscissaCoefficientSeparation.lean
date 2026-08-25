import GaloisForLFunctions.HTGeometry.FiniteAbscissaRationalCoordinateIndependence
import GaloisForLFunctions.HTGeometry.SmallGrowthRotatedDirichletCoefficientSeparation

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
    have hval := congrArg (Subring.subtype upperEndAnalyticSubring) hclear
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
      _ = ∑ i, upperEndAnalyticSubring.subtype (N i * L i *
          ∏ j ∈ (Finset.univ : Finset (Fin d)).erase i, D j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [show (fun z => ((p i).numerator : ℂ → ℂ) z *
            LSeries (fun n => (A i).1 n) (-Complex.I * z) *
              ∏ j ∈ (Finset.univ : Finset (Fin d)).erase i,
                ((p j).denominator : ℂ → ℂ) z) =
            ((p i).numerator : ℂ → ℂ) *
              (fun z => LSeries (fun n => (A i).1 n) (-Complex.I * z)) *
                ∏ j ∈ (Finset.univ : Finset (Fin d)).erase i,
                  ((p j).denominator : ℂ → ℂ) by
          funext z
          simp]
        rw [map_mul, map_mul]
        rw [map_mul (Subring.subtype upperEndAnalyticSubring),
          map_mul (Subring.subtype upperEndAnalyticSubring),
          map_prod (Subring.subtype upperEndAnalyticSubring)]
        have hnum : upperEndAnalyticSubring.subtype
            (entireToUpperEndAnalytic (p i).numerator) =
            Germ.coeRingHom upperEndFilter ((p i).numerator : ℂ → ℂ) :=
          entireToUpperEndAnalytic_coe (p i).numerator
        have hseries : upperEndAnalyticSubring.subtype
            (finiteAbscissaLSeriesToUpperEndAnalytic (A i)) =
            Germ.coeRingHom upperEndFilter
              (fun z => LSeries (fun n => (A i).1 n) (-Complex.I * z)) := by
          exact finiteAbscissaLSeriesToUpperEndAnalytic_coe (A i)
        have hdenom : ∀ j, upperEndAnalyticSubring.subtype
            (entireToUpperEndAnalytic (p j).denominator) =
            Germ.coeRingHom upperEndFilter ((p j).denominator : ℂ → ℂ) := fun j =>
          entireToUpperEndAnalytic_coe (p j).denominator
        simp only [N, D, L, hnum, hseries, hdenom, map_prod]
      _ = 0 := by simpa only [map_sum, map_zero] using hval
  have hclearedEventually : ∀ᶠ z in upperEndFilter, cleared z = 0 := by
    apply Germ.coe_eq.mp
    change Germ.coeRingHom upperEndFilter cleared =
      Germ.coeRingHom upperEndFilter (0 : ℂ → ℂ)
    simpa only [map_zero] using hclearedGerm
  rw [upperEndFilter_basis.eventually_iff] at hclearedEventually
  obtain ⟨H, -, hH⟩ := hclearedEventually
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
    calc
      _ = (((p i).denominator : ℂ → ℂ) z *
          (((p i).numerator : ℂ → ℂ) z /
            ((p i).denominator : ℂ → ℂ) z)) *
          (∏ j ∈ (Finset.univ : Finset (Fin d)).erase i,
            ((p j).denominator : ℂ → ℂ) z) *
          LSeries (fun n => (A i).1 n) (-Complex.I * z) := by ring
      _ = _ := by
        rw [mul_div_cancel₀ _ (hz i)]
        ring
  have hmul : Pz * ∑ i, smallGrowthFunction (phi i) z *
      LSeries (fun n => (A i).1 n) (-Complex.I * z) = 0 := by
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun i _ => heach i)]
    exact hclearZ
  exact (mul_eq_zero.mp hmul).resolve_left hPz

/-- Exact coefficient separation for finite-abscissa arithmetic sources with coefficients in the
Nagoshi field, after realization in the upper-end meromorphic carrier. -/
theorem smallGrowth_finiteAbscissa_relation_coeff_eq_zero {d : ℕ}
    (A : Fin d → finiteAbscissaArithmeticSubalgebra)
    (phi : Fin d → SmallGrowthMeromorphicField)
    (hrel : ∑ i, smallGrowthMeromorphicToUpperEnd (phi i) *
      finiteAbscissaLSeriesToUpperEndMero (A i) = 0) :
    ∀ n, 1 ≤ n →
      ∑ i, complexToSmallGrowthMeromorphic ((A i).1 n) * phi i = 0 := by
  classical
  choose H hH using fun i => (A i).2
  let x₁ : ℝ := ∑ i, (|H i| + 1)
  have hsum : ∀ i, LSeriesSummable (fun n => (A i).1 n) (x₁ : ℂ) := by
    intro i
    have hterm : |H i| + 1 ≤ x₁ := by
      dsimp only [x₁]
      exact Finset.single_le_sum (f := fun j => |H j| + 1)
        (fun j _ => by positivity) (Finset.mem_univ i)
    have hHlt : H i < x₁ :=
      lt_of_lt_of_le (by linarith [le_abs_self (H i)]) hterm
    exact hH i x₁ hHlt
  obtain ⟨B, hraw⟩ := upperEnd_smallGrowth_relation_eventually_rotated A phi hrel
  have hrawLe : ∀ᶠ z in Filter.codiscrete ℂ, B + 1 ≤ z.im →
      ∑ i, smallGrowthFunction (phi i) z *
        LSeries (fun n => (A i).1 n) (-Complex.I * z) = 0 := by
    filter_upwards [hraw] with z hz
    intro hzB
    exact hz (lt_of_lt_of_le (lt_add_one B) hzB)
  exact smallGrowth_rotated_LSeries_relation_coeff_eq_zero
    (fun i n => (A i).1 n) hsum phi hrawLe

end

end GaloisForLFunctions.HTGeometry
