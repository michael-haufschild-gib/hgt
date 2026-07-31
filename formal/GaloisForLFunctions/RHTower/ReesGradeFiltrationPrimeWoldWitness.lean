import GaloisForLFunctions.RHTower.ReesGradeFiltrationFlatRadicalLaw
import GaloisForLFunctions.RHTower.CriticalActivationReesSourceLaw
import GaloisForLFunctions.RHTower.PrimeValuationHellingerReesReflectionFracture

/-!
# The Rees grade filtration on the prime Wold boundary scale

The prime Wold boundary volume is positive at every stage and tends to zero, so it is a
contracting scale in the sense of the Rees grade filtration.  Every grade of that filtration is
therefore inhabited on this scale — by every bounded family, and by an explicit family of
prescribed inverse-power growth — while the filtration is strictly increasing at each step and the
all-orders-flat radical is a proper ideal.

This turns the prime-Wold no-sewing statements into statements with content: no bounded operator
family, and no multiplier of any prescribed inverse-power growth, carries the flat reflected
irregular gauge onto the vacuum half-density.
-/

open Filter Asymptotics
open GaloisForLFunctions
open scoped Topology

namespace RHTower

noncomputable section

/-! ## The prime Wold boundary volume is a contracting scale -/

/-- The prime Wold boundary volume is eventually positive and at most one. -/
theorem primeWoldBoundaryVolumeBelow_eventually_contracting :
    ∀ᶠ N in atTop, 0 < primeWoldBoundaryVolumeBelow N ∧
      primeWoldBoundaryVolumeBelow N ≤ 1 := by
  have hlt : ∀ᶠ N in atTop, primeWoldBoundaryVolumeBelow N < 1 :=
    tendsto_primeWoldBoundaryVolumeBelow_zero.eventually (eventually_lt_nhds one_pos)
  filter_upwards [hlt] with N hN
  exact ⟨primeWoldBoundaryVolumeBelow_pos N, hN.le⟩

/-- The prime Wold boundary volume is eventually nonzero. -/
theorem primeWoldBoundaryVolumeBelow_eventually_ne_zero :
    ∀ᶠ N in atTop, primeWoldBoundaryVolumeBelow N ≠ 0 :=
  Filter.Eventually.of_forall fun N => (primeWoldBoundaryVolumeBelow_pos N).ne'

/-! ## Every grade is inhabited on this scale -/

/-- Every bounded germ has every finite Rees grade on the prime Wold scale. -/
theorem reesGradeAtMost_primeWold_of_isBigO_one {E : Type*} [SeminormedAddCommGroup E]
    {f : ℕ → E} (hf : f =O[atTop] fun _ => (1 : ℝ)) (K : ℕ) :
    ReesGradeAtMost atTop primeWoldBoundaryVolumeBelow K f :=
  reesGradeAtMost_of_isBigO_one primeWoldBoundaryVolumeBelow_eventually_contracting hf K

/-- Every bounded family of continuous linear maps has every finite operator Rees grade on the
prime Wold scale. -/
theorem reesOperatorGradeAtMost_primeWold_of_isBigO_one
    {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] {R : ℕ → (E →L[ℝ] F)}
    (hR : (fun N => ‖R N‖) =O[atTop] fun _ => (1 : ℝ)) (K : ℕ) :
    ReesOperatorGradeAtMost atTop primeWoldBoundaryVolumeBelow K R :=
  reesOperatorGradeAtMost_of_isBigO_one
    primeWoldBoundaryVolumeBelow_eventually_contracting hR K

/-- A constant family of continuous linear maps has every finite operator Rees grade on the prime
Wold scale. -/
theorem reesOperatorGradeAtMost_primeWold_const
    {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] (T : E →L[ℝ] F) (K : ℕ) :
    ReesOperatorGradeAtMost atTop primeWoldBoundaryVolumeBelow K (fun _ => T) :=
  reesOperatorGradeAtMost_const primeWoldBoundaryVolumeBelow_eventually_contracting T K

/-- The exact inverse power of the prime Wold volume realizes its own grade. -/
theorem reesGradeAtMost_primeWold_inv_pow (K : ℕ) :
    ReesGradeAtMost atTop primeWoldBoundaryVolumeBelow K
      (fun N => (primeWoldBoundaryVolumeBelow N)⁻¹ ^ K) :=
  reesGradeAtMost_inv_pow K

/-- The Rees filtration on the prime Wold scale is strictly increasing at every step. -/
theorem not_reesGradeAtMost_primeWold_inv_pow_succ (K : ℕ) :
    ¬ ReesGradeAtMost atTop primeWoldBoundaryVolumeBelow K
      (fun N => (primeWoldBoundaryVolumeBelow N)⁻¹ ^ (K + 1)) :=
  not_reesGradeAtMost_inv_pow_succ
    (Filter.Eventually.of_forall fun N => primeWoldBoundaryVolumeBelow_pos N)
    tendsto_primeWoldBoundaryVolumeBelow_zero K

/-- The all-orders-flat radical of the prime Wold scale is a proper ideal. -/
theorem not_reesAllOrdersFlat_primeWold_one :
    ¬ ReesAllOrdersFlat atTop primeWoldBoundaryVolumeBelow (fun _ : ℕ => (1 : ℝ)) :=
  not_reesAllOrdersFlat_one
    (Filter.Eventually.of_forall fun N => primeWoldBoundaryVolumeBelow_pos N)
    tendsto_primeWoldBoundaryVolumeBelow_zero

/-! ## No-sewing statements with an inhabited hypothesis class -/

/-- No multiplier of prescribed inverse-power growth sews the flat reflected irregular gauge onto
the vacuum half-density. -/
theorem no_invPowMultiplier_sews_primeWold_flat_to_halfNormal (K : ℕ) :
    (fun N => (primeWoldBoundaryVolumeBelow N)⁻¹ ^ K *
        ‖primeWoldReflectedIrregularGauge (1 : ℂ) N‖) ≠
      primeWoldHalfNormalSector :=
  no_finiteReesMultiplier_sews_flat_to_halfNormal K
    (fun N => (primeWoldBoundaryVolumeBelow N)⁻¹ ^ K)
    (reesGradeAtMost_primeWold_inv_pow K)

/-- No bounded family of continuous linear maps sews the flat reflected irregular gauge onto the
vacuum half-density. -/
theorem no_boundedOperator_sews_primeWold_flat_to_halfNormal
    (R : ℕ → (ℝ →L[ℝ] ℝ))
    (hR : (fun N => ‖R N‖) =O[atTop] fun _ => (1 : ℝ)) :
    (fun N => R N ‖primeWoldReflectedIrregularGauge (1 : ℂ) N‖) ≠
      primeWoldHalfNormalSector :=
  no_finiteReesOperator_sews_flat_to_nonflat atTop primeWoldBoundaryVolumeBelow 0 R
    (fun N => ‖primeWoldReflectedIrregularGauge (1 : ℂ) N‖) primeWoldHalfNormalSector
    primeWoldBoundaryVolumeBelow_eventually_ne_zero
    (reesOperatorGradeAtMost_primeWold_of_isBigO_one hR 0)
    (norm_primeWoldReflectedIrregularGauge_reesAllOrdersFlat (t := 1) (by norm_num))
    primeWoldHalfNormalSector_not_reesAllOrdersFlat

/-- An operator family of prescribed inverse-power growth also fails to sew the two sectors. -/
theorem no_invPowOperator_sews_primeWold_flat_to_halfNormal (K : ℕ) :
    (fun N => ((primeWoldBoundaryVolumeBelow N)⁻¹ ^ K •
        ContinuousLinearMap.id ℝ ℝ) ‖primeWoldReflectedIrregularGauge (1 : ℂ) N‖) ≠
      primeWoldHalfNormalSector :=
  no_finiteReesOperator_sews_flat_to_nonflat atTop primeWoldBoundaryVolumeBelow K
    (fun N => (primeWoldBoundaryVolumeBelow N)⁻¹ ^ K • ContinuousLinearMap.id ℝ ℝ)
    (fun N => ‖primeWoldReflectedIrregularGauge (1 : ℂ) N‖) primeWoldHalfNormalSector
    primeWoldBoundaryVolumeBelow_eventually_ne_zero
    (reesOperatorGradeAtMost_inv_pow_smul_const _ K)
    (norm_primeWoldReflectedIrregularGauge_reesAllOrdersFlat (t := 1) (by norm_num))
    primeWoldHalfNormalSector_not_reesAllOrdersFlat

/-! ## The reflected Hellinger sectors, against inhabited operator classes -/

/-- No bounded family of continuous linear maps sews the positive squared Hellinger sector onto
its reflection. -/
theorem no_boundedOperator_sews_reflected_Hellinger_sectors
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) (R : ℕ → (ℝ →L[ℝ] ℝ))
    (hR : (fun N => ‖R N‖) =O[atTop] fun _ => (1 : ℝ)) :
    (fun N => R N (primeValuationSquaredHellingerBelow c N)) ≠
      primeValuationSquaredHellingerBelow (-c) :=
  no_finiteReesOperator_sews_reflected_Hellinger_sectors hc hcHalf 0 R
    (reesOperatorGradeAtMost_primeWold_of_isBigO_one hR 0)

/-- No multiplier of prescribed inverse-power growth sews the positive squared Hellinger sector
onto its reflection. -/
theorem no_invPowMultiplier_sews_reflected_Hellinger_sectors
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) (K : ℕ) :
    (fun N => (primeWoldBoundaryVolumeBelow N)⁻¹ ^ K *
        primeValuationSquaredHellingerBelow c N) ≠
      primeValuationSquaredHellingerBelow (-c) := by
  intro hsew
  refine no_finiteReesOperator_sews_reflected_Hellinger_sectors hc hcHalf K
    (fun N => (primeWoldBoundaryVolumeBelow N)⁻¹ ^ K • ContinuousLinearMap.id ℝ ℝ)
    (reesOperatorGradeAtMost_inv_pow_smul_const _ K) ?_
  rw [← hsew]
  funext N
  simp

/-! ## The law on the arithmetic scale -/

/-- **Prime Wold Rees filtration law.**  On the prime Wold boundary scale the finite-Rees-grade
class is inhabited at every level — by every bounded family and by an explicit family of
prescribed inverse-power growth — the filtration is strictly increasing at every step, the
all-orders-flat radical is a proper ideal, and no member of any grade sews the flat reflected
irregular gauge onto the vacuum half-density. -/
theorem primeWoldReesFiltration_law :
    (∀ K : ℕ, ReesGradeAtMost atTop primeWoldBoundaryVolumeBelow K
        (fun N => (primeWoldBoundaryVolumeBelow N)⁻¹ ^ K) ∧
      ¬ ReesGradeAtMost atTop primeWoldBoundaryVolumeBelow K
        (fun N => (primeWoldBoundaryVolumeBelow N)⁻¹ ^ (K + 1))) ∧
      (¬ ReesAllOrdersFlat atTop primeWoldBoundaryVolumeBelow (fun _ : ℕ => (1 : ℝ))) ∧
      (∀ (K : ℕ) (r : ℕ → ℝ),
        ReesGradeAtMost atTop primeWoldBoundaryVolumeBelow K r →
          (fun N => r N * ‖primeWoldReflectedIrregularGauge (1 : ℂ) N‖) ≠
            primeWoldHalfNormalSector) :=
  ⟨fun K => ⟨reesGradeAtMost_primeWold_inv_pow K,
      not_reesGradeAtMost_primeWold_inv_pow_succ K⟩,
    not_reesAllOrdersFlat_primeWold_one,
    fun K r hr => no_finiteReesMultiplier_sews_flat_to_halfNormal K r hr⟩

end

end RHTower
