import GaloisForLFunctions.HTGeometry.CriticalSourceChartFractionRing
import GaloisForLFunctions.HTGeometry.CriticalObservationChartRing

/-!
# The source chart is integral over the observation chart

The marked observation chart ring embeds into the source chart ring: the observed raw coordinates
are variables, the observed reciprocal coordinates are the numerators of
`CriticalSourceChartLocalization` divided by powers of the (invertible) constant term, and the
marked product becomes a unit because its numerator is a factor of the inverted chart polynomial.

Every generator of the source chart — the raw variables, the inverse of the constant term, and the
inverse of the chart polynomial — is integral over the observation chart, so

```text
Algebra.IsIntegral (criticalObservationChartRing K m n) (criticalSourceChartRing K m n)
```

This is the ring-theoretic form of the finiteness of the critical horizon map on the marked chart,
in exactly the shape the complex-point surjectivity theorem
(`AlgSpec.surjective_precomp_of_isIntegral`) consumes.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)]

theorem isUnit_algebraMap_criticalSourceChartPoly :
    IsUnit (algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n)
      (criticalSourceChartPoly K m n)) :=
  IsLocalization.map_units (M := Submonoid.powers (criticalSourceChartPoly K m n))
    (criticalSourceChartRing K m n)
    (⟨criticalSourceChartPoly K m n, ⟨1, pow_one _⟩⟩ : Submonoid.powers _)

theorem algebraMap_criticalSourceChartPoly_factor :
    algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n)
        (criticalSourceChartPoly K m n) =
      algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n)
          (X (⟨0, by have := (Fact.out : 0 < m); omega⟩ : Fin (m + n))) *
        (algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n)
            (X (⟨m, by have := (Fact.out : 0 < n); omega⟩ : Fin (m + n))) *
          algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n)
            (criticalSourceRecipNumerator K m n (k := n)
              (by have := (Fact.out : 0 < m); omega))) := by
  rw [← map_mul, ← map_mul, ← mul_assoc]
  exact congrArg _ (criticalSourceChartPoly_eq K m n)

theorem isUnit_algebraMap_chartX0 :
    IsUnit (algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n)
      (X (⟨0, by have := (Fact.out : 0 < m); omega⟩ : Fin (m + n)))) := by
  have h := isUnit_algebraMap_criticalSourceChartPoly K (m := m) (n := n)
  rw [algebraMap_criticalSourceChartPoly_factor] at h
  exact isUnit_of_mul_isUnit_left h

theorem isUnit_algebraMap_chartXm :
    IsUnit (algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n)
      (X (⟨m, by have := (Fact.out : 0 < n); omega⟩ : Fin (m + n)))) := by
  have h := isUnit_algebraMap_criticalSourceChartPoly K (m := m) (n := n)
  rw [algebraMap_criticalSourceChartPoly_factor] at h
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right h)

theorem isUnit_algebraMap_chartNumerator :
    IsUnit (algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n)
      (criticalSourceRecipNumerator K m n (k := n) (by have := (Fact.out : 0 < m); omega))) := by
  have h := isUnit_algebraMap_criticalSourceChartPoly K (m := m) (n := n)
  rw [algebraMap_criticalSourceChartPoly_factor] at h
  exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right h)

/-- The inverse of the constant raw coordinate inside the source chart ring. -/
def chartInvX0 : criticalSourceChartRing K m n :=
  ↑(isUnit_algebraMap_chartX0 K (m := m) (n := n)).unit⁻¹

theorem algebraMap_chartX0 :
    algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)
        (algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n)
          (X (⟨0, by have := (Fact.out : 0 < m); omega⟩ : Fin (m + n)))) =
      criticalSourceRaw K m n ⟨0, by have := (Fact.out : 0 < m); omega⟩ := by
  rw [algebraMap_criticalSourceChartRing_apply, MvPolynomial.aeval_X]

theorem algebraMap_chartInvX0 :
    algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)
        (chartInvX0 K (m := m) (n := n)) *
      criticalSourceRaw K m n ⟨0, by have := (Fact.out : 0 < m); omega⟩ = 1 := by
  have h := (isUnit_algebraMap_chartX0 K (m := m) (n := n)).val_inv_mul
  have := congrArg (algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)) h
  rw [map_mul, map_one, algebraMap_chartX0] at this
  exact this

omit [CharZero K] [IsAlgClosed K] [Fact (0 < m)] [Fact (0 < n)] in
/-- The numerator identity inside the actual critical source field. -/
theorem aeval_criticalSourceRecipNumerator {k : ℕ} (hk : k < m + n) :
    MvPolynomial.aeval (criticalSourceRaw K m n) (criticalSourceRecipNumerator K m n hk) =
      criticalSourceRaw K m n ⟨0, by omega⟩ ^ (k + 1) * criticalSourceRecip K m n ⟨k, hk⟩ := by
  apply Subtype.ext
  rw [show ((MvPolynomial.aeval (criticalSourceRaw K m n)
        (criticalSourceRecipNumerator K m n hk) : criticalSourceField K m n) :
        genericJetField K (m + n))
      = MvPolynomial.aeval (criticalSourceRawFamily K m n)
        (criticalSourceRecipNumerator K m n hk) from
    coe_aeval_criticalSourceRaw K m n _]
  rw [criticalSourceRecipNumerator_spec]
  rfl

/-- The `k`-th reciprocal coordinate as an element of the source chart ring. -/
def chartRecip {k : ℕ} (hk : k < m + n) : criticalSourceChartRing K m n :=
  algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n)
      (criticalSourceRecipNumerator K m n hk) *
    chartInvX0 K (m := m) (n := n) ^ (k + 1)

theorem algebraMap_chartRecip {k : ℕ} (hk : k < m + n) :
    algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)
        (chartRecip K (m := m) (n := n) hk) = criticalSourceRecip K m n ⟨k, hk⟩ := by
  have hx0 := algebraMap_chartInvX0 K (m := m) (n := n)
  rw [chartRecip, map_mul, map_pow, algebraMap_criticalSourceChartRing_apply,
    aeval_criticalSourceRecipNumerator]
  have hne : criticalSourceRaw K m n ⟨0, by have := (Fact.out : 0 < m); omega⟩ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hx0
    exact zero_ne_one hx0
  have hinv : algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)
      (chartInvX0 K (m := m) (n := n))
      = (criticalSourceRaw K m n ⟨0, by have := (Fact.out : 0 < m); omega⟩)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm] at hx0 ⊢; exact hx0)
  rw [hinv, inv_pow]
  field_simp

instance criticalObservationRingSourceGroundTower :
    IsScalarTower K (criticalObservationRing K m n) (criticalSourceField K m n) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply (criticalObservationRing K m n)
      (criticalObservationField K m n) (criticalSourceField K m n),
      ← IsScalarTower.algebraMap_apply K (criticalObservationRing K m n)
        (criticalObservationField K m n),
      ← IsScalarTower.algebraMap_apply K (criticalObservationField K m n)
        (criticalSourceField K m n)]

/-- The observation coordinates inside the source chart ring. -/
def chartObservationCoord : Fin n ⊕ Fin m → criticalSourceChartRing K m n
  | Sum.inl i => algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n)
      (X (⟨m + (i : ℕ), by omega⟩ : Fin (m + n)))
  | Sum.inr j => chartRecip K (m := m) (n := n) (k := n + (j : ℕ)) (by omega)

/-- The observation coordinate ring maps into the source chart ring. -/
def observationRingToChart :
    criticalObservationRing K m n →ₐ[K] criticalSourceChartRing K m n :=
  MvPolynomial.aeval (chartObservationCoord K (m := m) (n := n))

theorem algebraMap_observationRingToChart (p : criticalObservationRing K m n) :
    algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)
        (observationRingToChart K (m := m) (n := n) p) =
      algebraMap (criticalObservationRing K m n) (criticalSourceField K m n) p := by
  have hext :
      ((IsScalarTower.toAlgHom K (criticalSourceChartRing K m n)
          (criticalSourceField K m n)).comp
        (observationRingToChart K (m := m) (n := n)))
        = IsScalarTower.toAlgHom K (criticalObservationRing K m n)
            (criticalSourceField K m n) := by
    apply MvPolynomial.algHom_ext
    rintro (i | j)
    · show algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)
        (observationRingToChart K (m := m) (n := n) (X (Sum.inl i))) = _
      rw [observationRingToChart, MvPolynomial.aeval_X]
      show algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)
        (algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n)
          (X (⟨m + (i : ℕ), by omega⟩ : Fin (m + n)))) = _
      rw [algebraMap_criticalSourceChartRing_apply, MvPolynomial.aeval_X]
      exact (algebraMap_criticalObservationRing_X_inl K i).symm
    · show algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)
        (observationRingToChart K (m := m) (n := n) (X (Sum.inr j))) = _
      rw [observationRingToChart, MvPolynomial.aeval_X]
      show algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)
        (chartRecip K (m := m) (n := n) (k := n + (j : ℕ)) (by omega)) = _
      rw [algebraMap_chartRecip]
      exact (algebraMap_criticalObservationRing_X_inr K j).symm
  exact DFunLike.congr_fun hext p

theorem isUnit_observationRingToChart_marked :
    IsUnit (observationRingToChart K (m := m) (n := n) (criticalObservationMarked K)) := by
  rw [criticalObservationMarked, map_mul]
  refine IsUnit.mul ?_ ?_
  · show IsUnit (observationRingToChart K (m := m) (n := n)
      (X (Sum.inl (⟨0, Fact.out⟩ : Fin n))))
    rw [observationRingToChart, MvPolynomial.aeval_X]
    show IsUnit (algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n)
      (X (⟨m + (0 : ℕ), by have := (Fact.out : 0 < n); omega⟩ : Fin (m + n))))
    exact isUnit_algebraMap_chartXm K (m := m) (n := n)
  · show IsUnit (observationRingToChart K (m := m) (n := n)
      (X (Sum.inr (⟨0, Fact.out⟩ : Fin m))))
    rw [observationRingToChart, MvPolynomial.aeval_X]
    show IsUnit (chartRecip K (m := m) (n := n) (k := n + (0 : ℕ))
      (by have := (Fact.out : 0 < m); omega))
    rw [chartRecip]
    refine IsUnit.mul ?_ (IsUnit.pow _ ?_)
    · exact isUnit_algebraMap_chartNumerator K (m := m) (n := n)
    · exact (isUnit_algebraMap_chartX0 K (m := m) (n := n)).unit⁻¹.isUnit

/-- The observation chart ring maps into the source chart ring. -/
noncomputable instance criticalObservationChartToSourceChartAlgebra :
    Algebra (criticalObservationChartRing K m n) (criticalSourceChartRing K m n) :=
  (IsLocalization.Away.lift (S := criticalObservationChartRing K m n)
    (criticalObservationMarked K)
    (g := (observationRingToChart K (m := m) (n := n)).toRingHom)
    (isUnit_observationRingToChart_marked K)).toAlgebra

instance criticalSourceChartRingObservationTower :
    IsScalarTower (criticalObservationChartRing K m n) (criticalSourceChartRing K m n)
      (criticalSourceField K m n) := by
  refine IsScalarTower.of_algebraMap_eq' ?_
  refine IsLocalization.ringHom_ext
    (Submonoid.powers (criticalObservationMarked K (m := m) (n := n))) ?_
  refine RingHom.ext fun p => ?_
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [← IsScalarTower.algebraMap_apply (criticalObservationRing K m n)
    (criticalObservationChartRing K m n) (criticalSourceField K m n) p,
    show algebraMap (criticalObservationChartRing K m n) (criticalSourceChartRing K m n)
        (algebraMap (criticalObservationRing K m n) (criticalObservationChartRing K m n) p)
      = observationRingToChart K (m := m) (n := n) p from
    IsLocalization.Away.lift_eq _ _ p]
  rw [algebraMap_observationRingToChart]

instance criticalObservationChartSourceChartGroundTower :
    IsScalarTower K (criticalObservationChartRing K m n) (criticalSourceChartRing K m n) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply K (criticalObservationRing K m n)
      (criticalObservationChartRing K m n) c,
      show algebraMap (criticalObservationChartRing K m n) (criticalSourceChartRing K m n)
          (algebraMap (criticalObservationRing K m n) (criticalObservationChartRing K m n)
            (algebraMap K (criticalObservationRing K m n) c))
        = observationRingToChart K (m := m) (n := n)
            (algebraMap K (criticalObservationRing K m n) c) from
      IsLocalization.Away.lift_eq _ _ _]
    rw [AlgHom.commutes]

/-- Integrality descends through the injective chart-to-field map. -/
theorem isIntegral_chart_of_isIntegral_source {d : criticalSourceChartRing K m n}
    (h : IsIntegral (criticalObservationChartRing K m n)
      (algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n) d)) :
    IsIntegral (criticalObservationChartRing K m n) d :=
  (isIntegral_algHom_iff
    (IsScalarTower.toAlgHom (criticalObservationChartRing K m n)
      (criticalSourceChartRing K m n) (criticalSourceField K m n))
    (algebraMap_criticalSourceChartRing_injective K m n)).1 h

theorem isIntegral_chart_algebraMap_X (j : Fin (m + n)) :
    IsIntegral (criticalObservationChartRing K m n)
      (algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n) (X j)) := by
  apply isIntegral_chart_of_isIntegral_source
  rw [algebraMap_criticalSourceChartRing_apply, MvPolynomial.aeval_X]
  exact criticalSourceCoordinate_isIntegral_chartRing K _ (Or.inl ⟨j, rfl⟩)

theorem criticalSourceRaw_zero_mul_criticalSourceRecip_zero :
    criticalSourceRaw K m n ⟨0, by have := (Fact.out : 0 < m); omega⟩ *
        criticalSourceRecip K m n ⟨0, by have := (Fact.out : 0 < m); omega⟩ = 1 := by
  apply Subtype.ext
  exact criticalAmbientRaw_zero_mul_recip_zero K m n

theorem algebraMap_chartInvX0_eq :
    algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)
        (chartInvX0 K (m := m) (n := n)) =
      criticalSourceRecip K m n ⟨0, by have := (Fact.out : 0 < m); omega⟩ := by
  have h1 := algebraMap_chartInvX0 K (m := m) (n := n)
  have h2 := criticalSourceRaw_zero_mul_criticalSourceRecip_zero K (m := m) (n := n)
  have hne : criticalSourceRaw K m n ⟨0, by have := (Fact.out : 0 < m); omega⟩ ≠ 0 := by
    intro h
    rw [h, zero_mul] at h2
    exact zero_ne_one h2
  apply mul_right_cancel₀ hne
  rw [h1, mul_comm]
  exact h2.symm

theorem isIntegral_chartInvX0 :
    IsIntegral (criticalObservationChartRing K m n) (chartInvX0 K (m := m) (n := n)) := by
  apply isIntegral_chart_of_isIntegral_source
  rw [algebraMap_chartInvX0_eq]
  exact criticalSourceCoordinate_isIntegral_chartRing K _ (Or.inr ⟨_, rfl⟩)

theorem isIntegral_chart_algebraMap (p : MvPolynomial (Fin (m + n)) K) :
    IsIntegral (criticalObservationChartRing K m n)
      (algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n) p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      have h : algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n) (C a)
          = algebraMap (criticalObservationChartRing K m n) (criticalSourceChartRing K m n)
            (algebraMap K (criticalObservationChartRing K m n) a) := by
        show algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n)
            (algebraMap K (MvPolynomial (Fin (m + n)) K) a) = _
        rw [← IsScalarTower.algebraMap_apply K (criticalObservationChartRing K m n)
          (criticalSourceChartRing K m n) a,
          ← IsScalarTower.algebraMap_apply K (MvPolynomial (Fin (m + n)) K)
            (criticalSourceChartRing K m n) a]
      rw [h]
      exact isIntegral_algebraMap
  | add p q hp hq =>
      rw [map_add]
      exact hp.add hq
  | mul_X p j hp =>
      rw [map_mul]
      exact hp.mul (isIntegral_chart_algebraMap_X K j)

/-- The inverse of the chart polynomial inside the source chart ring. -/
def chartInvG : criticalSourceChartRing K m n :=
  ↑(isUnit_algebraMap_criticalSourceChartPoly K (m := m) (n := n)).unit⁻¹

theorem chartInvG_mul :
    chartInvG K (m := m) (n := n) *
      algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n)
        (criticalSourceChartPoly K m n) = 1 :=
  (isUnit_algebraMap_criticalSourceChartPoly K (m := m) (n := n)).val_inv_mul

theorem algebraMap_chartInvG_mul :
    algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)
        (chartInvG K (m := m) (n := n)) *
      MvPolynomial.aeval (criticalSourceRaw K m n) (criticalSourceChartPoly K m n) = 1 := by
  have h := congrArg
    (algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n))
    (chartInvG_mul K (m := m) (n := n))
  rwa [map_mul, map_one, algebraMap_criticalSourceChartRing_apply] at h

theorem isIntegral_chartInvG :
    IsIntegral (criticalObservationChartRing K m n) (chartInvG K (m := m) (n := n)) := by
  apply isIntegral_chart_of_isIntegral_source
  have hmul := algebraMap_chartInvG_mul K (m := m) (n := n)
  have hchart : MvPolynomial.aeval (criticalSourceRaw K m n) (criticalSourceChartPoly K m n)
      = criticalSourceRaw K m n ⟨0, by have := (Fact.out : 0 < m); omega⟩ ^ (n + 2) *
        (criticalSourceRaw K m n ⟨m, by have := (Fact.out : 0 < n); omega⟩ *
          criticalSourceRecip K m n ⟨n, by have := (Fact.out : 0 < m); omega⟩) := by
    rw [criticalSourceChartPoly_eq, map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
      aeval_criticalSourceRecipNumerator]
    ring
  have hy0 : criticalSourceRaw K m n ⟨0, by have := (Fact.out : 0 < m); omega⟩ *
      criticalSourceRecip K m n ⟨0, by have := (Fact.out : 0 < m); omega⟩ = 1 :=
    criticalSourceRaw_zero_mul_criticalSourceRecip_zero K (m := m) (n := n)
  have hmarked : algebraMap (criticalObservationChartRing K m n) (criticalSourceField K m n)
      (IsLocalization.Away.invSelf (criticalObservationMarked K (m := m) (n := n))) *
      (criticalSourceRaw K m n ⟨m, by have := (Fact.out : 0 < n); omega⟩ *
        criticalSourceRecip K m n ⟨n, by have := (Fact.out : 0 < m); omega⟩) = 1 := by
    have h := IsLocalization.Away.mul_invSelf
      (S := criticalObservationChartRing K m n)
      (criticalObservationMarked K (m := m) (n := n))
    have h2 := congrArg
      (algebraMap (criticalObservationChartRing K m n) (criticalSourceField K m n)) h
    rw [map_mul, map_one, ← IsScalarTower.algebraMap_apply,
      algebraMap_criticalObservationMarked K] at h2
    rw [mul_comm]
    exact h2
  have himg : algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)
      (chartInvG K (m := m) (n := n))
      = criticalSourceRecip K m n ⟨0, by have := (Fact.out : 0 < m); omega⟩ ^ (n + 2) *
        algebraMap (criticalObservationChartRing K m n) (criticalSourceField K m n)
          (IsLocalization.Away.invSelf (criticalObservationMarked K (m := m) (n := n))) := by
    have hne : MvPolynomial.aeval (criticalSourceRaw K m n)
        (criticalSourceChartPoly K m n) ≠ 0 :=
      aeval_criticalSourceRaw_chartPoly_ne_zero K m n
    apply mul_right_cancel₀ hne
    rw [hmul, hchart]
    symm
    calc criticalSourceRecip K m n ⟨0, by have := (Fact.out : 0 < m); omega⟩ ^ (n + 2) *
          algebraMap (criticalObservationChartRing K m n) (criticalSourceField K m n)
            (IsLocalization.Away.invSelf (criticalObservationMarked K (m := m) (n := n))) *
          (criticalSourceRaw K m n ⟨0, by have := (Fact.out : 0 < m); omega⟩ ^ (n + 2) *
            (criticalSourceRaw K m n ⟨m, by have := (Fact.out : 0 < n); omega⟩ *
              criticalSourceRecip K m n ⟨n, by have := (Fact.out : 0 < m); omega⟩))
        = (criticalSourceRaw K m n ⟨0, by have := (Fact.out : 0 < m); omega⟩ *
            criticalSourceRecip K m n ⟨0, by have := (Fact.out : 0 < m); omega⟩) ^ (n + 2) *
          (algebraMap (criticalObservationChartRing K m n) (criticalSourceField K m n)
            (IsLocalization.Away.invSelf (criticalObservationMarked K (m := m) (n := n))) *
            (criticalSourceRaw K m n ⟨m, by have := (Fact.out : 0 < n); omega⟩ *
              criticalSourceRecip K m n ⟨n, by have := (Fact.out : 0 < m); omega⟩)) := by
          rw [mul_pow]; ring
      _ = 1 := by rw [hy0, hmarked, one_pow, one_mul]
  rw [himg]
  exact (((criticalSourceCoordinate_isIntegral_chartRing K _
    (Or.inr ⟨⟨0, by have := (Fact.out : 0 < m); omega⟩, rfl⟩)).pow (n + 2)).mul
      isIntegral_algebraMap)

/-- **The critical source chart is integral over the marked observation chart.** -/
instance criticalSourceChartRing_isIntegral :
    Algebra.IsIntegral (criticalObservationChartRing K m n) (criticalSourceChartRing K m n) := by
  constructor
  intro d
  obtain ⟨⟨p, s⟩, hd⟩ := IsLocalization.mk'_surjective
    (Submonoid.powers (criticalSourceChartPoly K m n)) d
  obtain ⟨k, hk⟩ := s.property
  have hspec : d * algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n)
      (s : MvPolynomial (Fin (m + n)) K)
      = algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n) p := by
    rw [← hd]
    exact IsLocalization.mk'_spec _ _ _
  have hs : algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n)
      (s : MvPolynomial (Fin (m + n)) K)
      = (algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n)
          (criticalSourceChartPoly K m n)) ^ k := by
    rw [← hk, map_pow]
  have hdeq : d = algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n) p *
      chartInvG K (m := m) (n := n) ^ k := by
    calc d = d * 1 ^ k := by rw [one_pow, mul_one]
      _ = d * (algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n)
              (criticalSourceChartPoly K m n) * chartInvG K (m := m) (n := n)) ^ k := by
          rw [mul_comm (algebraMap _ _ (criticalSourceChartPoly K m n)),
            chartInvG_mul]
      _ = (d * algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n)
              (s : MvPolynomial (Fin (m + n)) K)) * chartInvG K (m := m) (n := n) ^ k := by
          rw [hs, mul_pow]; ring
      _ = _ := by rw [hspec]
  rw [hdeq]
  exact (isIntegral_chart_algebraMap K p).mul ((isIntegral_chartInvG K).pow k)

/-- **Every element of the source field integral over the observation chart lies in the source
chart.**  This is the integral-closedness of the principal open, in the form the block
normalization consumes. -/
theorem exists_criticalSourceChart_of_isIntegral {x : criticalSourceField K m n}
    (hx : IsIntegral (criticalObservationChartRing K m n) x) :
    ∃ d : criticalSourceChartRing K m n,
      algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n) d = x :=
  IsIntegrallyClosed.isIntegral_iff.1
    (show IsIntegral (criticalSourceChartRing K m n) x from hx.tower_top)

end

end GaloisForLFunctions.HTGeometry
