import GaloisForLFunctions.HTGeometry.ProjectiveHorizonChartBasis

/-!
# The chart transcendence basis is independent

Lifting the inverse chart substitution to the localization away from the chart denominator produces
a map sending each affine chart jet back to its homogeneous coordinate while fixing the tower of the
denominator.  Composing with it shows that the denominator tower together with all chart jets is an
algebraically independent family in the homogeneous jet field.

Together with the chart generation already available, this family is a transcendence basis adapted
to one affine chart.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-! ## The inverse substitution on the chart localization -/

omit [Fintype n] in
theorem chartBack_chartDenom_pow (i : n) (m : ℕ) :
    chartBack (K := K) i (chartDenom i K ^ m) = chartDenom i K ^ m := by
  rw [map_pow, chartDenom, chartBack_X_self]

/-- The inverse chart substitution followed by the localization map. -/
def chartBackToLoc (i : n) : MvPolynomial (n × ℕ) K →+* ChartLoc i K :=
  (algebraMap (MvPolynomial (n × ℕ) K) (ChartLoc i K)).comp (chartBack i).toRingHom

omit [Fintype n] in
theorem chartBackToLoc_apply (i : n) (p : MvPolynomial (n × ℕ) K) :
    chartBackToLoc (K := K) i p =
      algebraMap (MvPolynomial (n × ℕ) K) (ChartLoc i K) (chartBack i p) := rfl

omit [Fintype n] in
theorem isUnit_back_powers (i : n) :
    ∀ y : Submonoid.powers (chartDenom i K),
      IsUnit (chartBackToLoc (K := K) i (y : MvPolynomial (n × ℕ) K)) := by
  rintro ⟨_, m, rfl⟩
  rw [chartBackToLoc_apply, chartBack_chartDenom_pow, map_pow]
  exact (IsLocalization.map_units (ChartLoc i K)
    (⟨chartDenom i K, Submonoid.mem_powers _⟩ :
      Submonoid.powers (chartDenom i K))).pow m

/-- The inverse chart substitution, extended to the chart localization. -/
def chartLocBack (i : n) : ChartLoc i K →ₐ[K] ChartLoc i K :=
  { IsLocalization.lift (isUnit_back_powers (K := K) i) with
    commutes' := fun c => by
      show IsLocalization.lift (isUnit_back_powers (K := K) i)
        (algebraMap K (ChartLoc i K) c) = _
      rw [IsScalarTower.algebraMap_apply K (MvPolynomial (n × ℕ) K) (ChartLoc i K),
        IsLocalization.lift_eq, chartBackToLoc_apply, AlgHom.commutes] }

omit [Fintype n] in
theorem chartLocBack_algebraMap (i : n) (p : MvPolynomial (n × ℕ) K) :
    chartLocBack i (algebraMap (MvPolynomial (n × ℕ) K) (ChartLoc i K) p) =
      algebraMap (MvPolynomial (n × ℕ) K) (ChartLoc i K) (chartBack i p) :=
  IsLocalization.lift_eq (isUnit_back_powers (K := K) i) p

omit [Fintype n] in
theorem chartLocBack_invSelf (i : n) :
    chartLocBack i (IsLocalization.Away.invSelf (S := ChartLoc i K) (chartDenom i K)) =
      IsLocalization.Away.invSelf (S := ChartLoc i K) (chartDenom i K) := by
  have hmul := IsLocalization.Away.mul_invSelf (S := ChartLoc i K) (chartDenom i K)
  have hback := congrArg (chartLocBack (K := K) i) hmul
  rw [map_mul, chartLocBack_algebraMap, chartBack_X_self, map_one] at hback
  calc chartLocBack i (IsLocalization.Away.invSelf (S := ChartLoc i K) (chartDenom i K))
      = (algebraMap (MvPolynomial (n × ℕ) K) (ChartLoc i K) (chartDenom i K) *
          IsLocalization.Away.invSelf (chartDenom i K)) *
            chartLocBack i (IsLocalization.Away.invSelf (chartDenom i K)) := by
        rw [hmul, one_mul]
    _ = IsLocalization.Away.invSelf (chartDenom i K) *
          (algebraMap (MvPolynomial (n × ℕ) K) (ChartLoc i K) (chartDenom i K) *
            chartLocBack i (IsLocalization.Away.invSelf (chartDenom i K))) := by ring
    _ = IsLocalization.Away.invSelf (chartDenom i K) := by rw [hback, mul_one]

omit [Fintype n] in
theorem chartLocBack_chartJetLoc {i k : n} (hk : k ≠ i) (l : ℕ) :
    chartLocBack i (chartJetLoc (K := K) i k l) =
      algebraMap (MvPolynomial (n × ℕ) K) (ChartLoc i K) (MvPolynomial.X (k, l)) := by
  have hmul := IsLocalization.Away.mul_invSelf (S := ChartLoc i K) (chartDenom i K)
  rw [chartJetLoc, map_mul, map_pow, chartLocBack_algebraMap, chartLocBack_invSelf,
    chartBack_affineNumer hk, map_mul, map_pow, mul_assoc, ← mul_pow]
  rw [show algebraMap (MvPolynomial (n × ℕ) K) (ChartLoc i K)
      (MvPolynomial.X ((i, 0) : n × ℕ)) = algebraMap _ _ (chartDenom i K) from rfl, hmul,
    one_pow, mul_one]

/-! ## The chart basis -/

/-- The chart transcendence basis: the tower of the chart denominator together with all chart
jets, realised in the chart localization. -/
def chartBasisLoc (i : n) : n × ℕ → ChartLoc i K := fun p =>
  if p.1 = i then algebraMap (MvPolynomial (n × ℕ) K) (ChartLoc i K) (MvPolynomial.X p)
  else chartJetLoc i p.1 p.2

omit [Fintype n] in
theorem chartLocBack_chartBasisLoc (i : n) (p : n × ℕ) :
    chartLocBack i (chartBasisLoc (K := K) i p) =
      algebraMap (MvPolynomial (n × ℕ) K) (ChartLoc i K) (MvPolynomial.X p) := by
  rw [chartBasisLoc]
  by_cases hp : p.1 = i
  · rw [if_pos hp, chartLocBack_algebraMap]
    congr 1
    obtain ⟨k, l⟩ := p
    simp only at hp
    subst hp
    exact chartBack_X_self k l
  · rw [if_neg hp, chartLocBack_chartJetLoc hp]

omit [Fintype n] [DecidableEq n] in
theorem algebraMap_chartLoc_injective (i : n) :
    Function.Injective (algebraMap (MvPolynomial (n × ℕ) K) (ChartLoc i K)) := by
  refine IsLocalization.injective (M := Submonoid.powers (chartDenom i K)) (ChartLoc i K) ?_
  rw [Submonoid.powers_le]
  exact mem_nonZeroDivisors_of_ne_zero (chartDenom_ne_zero i)

omit [Fintype n] in
/-- The chart basis is algebraically independent inside the chart localization. -/
theorem algebraicIndependent_chartBasisLoc (i : n) :
    AlgebraicIndependent K (chartBasisLoc (K := K) i) := by
  have hX : AlgebraicIndependent K
      (fun p : n × ℕ =>
        algebraMap (MvPolynomial (n × ℕ) K) (ChartLoc i K) (MvPolynomial.X p)) :=
    ((IsScalarTower.toAlgHom K (MvPolynomial (n × ℕ) K)
      (ChartLoc i K)).algebraicIndependent_iff
        (algebraMap_chartLoc_injective (K := K) i)).2
      (MvPolynomial.algebraicIndependent_X (n × ℕ) K)
  refine AlgebraicIndependent.of_comp (chartLocBack (K := K) i) ?_
  have hfun : (chartLocBack (K := K) i) ∘ (chartBasisLoc (K := K) i) =
      fun p : n × ℕ =>
        algebraMap (MvPolynomial (n × ℕ) K) (ChartLoc i K) (MvPolynomial.X p) := by
    funext p
    exact chartLocBack_chartBasisLoc i p
  rw [hfun]
  exact hX

/-! ## The chart basis in the jet field -/

/-- The chart transcendence basis inside the homogeneous jet field: the denominator tower together
with all chart jets. -/
def chartBasis (i : n) : n × ℕ → HomogeneousJetField n K := fun p =>
  if p.1 = i then freeCoordinate K (n × ℕ) p else affineJet i p.1 p.2

omit [Fintype n] in
theorem chartLocToField_chartBasisLoc (i : n) (p : n × ℕ) :
    chartLocToField i (chartBasisLoc (K := K) i p) = chartBasis i p := by
  rw [chartBasisLoc, chartBasis]
  by_cases hp : p.1 = i
  · rw [if_pos hp, if_pos hp, chartLocToField_algebraMap]
    rfl
  · rw [if_neg hp, if_neg hp, chartLocToField_chartJetLoc]

omit [Fintype n] in
/-- **Chart transcendence basis.**  The tower of the chart denominator together with all jets of the
affine chart coordinates is algebraically independent over the constants.  With the chart generation
already available, it is a transcendence basis of the homogeneous jet field. -/
theorem algebraicIndependent_chartBasis (i : n) :
    AlgebraicIndependent K (chartBasis (K := K) i) := by
  have hmap := (algebraicIndependent_chartBasisLoc (K := K) i).map
    (f := chartLocToField (K := K) i) ((chartLocToField_injective i).injOn)
  have hfun : (chartLocToField (K := K) i) ∘ (chartBasisLoc (K := K) i) =
      chartBasis (K := K) i := by
    funext p
    exact chartLocToField_chartBasisLoc i p
  rw [hfun] at hmap
  exact hmap

end

end GaloisForLFunctions.HTGeometry
