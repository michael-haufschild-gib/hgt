import GaloisForLFunctions.RHTower.XiWeilHilbertCore
import GaloisForLFunctions.RHTower.XiHedenmalmFourierEquation
import GaloisForLFunctions.RHTower.XiHadamardFactorization
import GaloisForLFunctions.RHTower.XiDivisorSupportedMetric
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix

/-!
# The Hedenmalm eigenfunctions span the Xi evaluation carrier under simplicity

The multiplicity-exact Xi evaluation space is indexed by `XiZeroCopy`. If every Xi zero is
simple, that copy index has one point over each centered zero. The removable Hedenmalm quotient
at a zero then evaluates to `I * XiC'` at its own coordinate and to zero at every other coordinate.
It is therefore a nonzero scalar multiple of the canonical `ell^2` basis vector.

Consequently the algebraic span of the actual Hedenmalm eigenfunction evaluations is dense in the
whole Xi `ell^2` carrier. This is the formal completion core needed before constructing the closed
diagonal realization of the Hedenmalm differential pair. No RH or simplicity assumption is
asserted: both enter explicitly as theorem hypotheses.
-/

open Complex
open HilbertSchmidt

namespace RHTower

noncomputable section

/-- Every centered Xi zero is simple. -/
def XiZerosSimple : Prop :=
  ∀ {alpha : ℂ}, XiC alpha = 0 → deriv XiC alpha ≠ 0

/-- A nonzero derivative at one divisor support point makes that local analytic multiplicity
exactly one, without assuming simplicity elsewhere. -/
theorem xiDivisorMultiplicity_eq_one_of_deriv_ne_zero
    (rho : XiDivisorSupport)
    (hderiv : deriv XiC (xiSpectralPointSupport rho) ≠ 0) :
    Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) = 1 := by
  have hpos := xi_divisor_pos_on_support rho
  have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) := by
    omega
  let q : XiZeroCopy := ⟨rho, ⟨0, hn⟩⟩
  have hzero : XiC (xiSpectralPointSupport rho) = 0 := by
    simpa only [q, xiSpectralPoint_eq_support] using XiC_xiSpectralPoint_eq_zero q
  have horder :=
    (XiC_analytic (xiSpectralPointSupport rho) (Set.mem_univ _)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      hzero hderiv
  rw [XiC_analyticOrderAt_support] at horder
  exact ENat.coe_inj.mp horder

/-- Simplicity makes the analytic divisor multiplicity at every support point exactly one. -/
theorem xiDivisorMultiplicity_eq_one_of_simple
    (hsimple : XiZerosSimple) (rho : XiDivisorSupport) :
    Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) = 1 := by
  have hpos := xi_divisor_pos_on_support rho
  have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) := by
    omega
  let q : XiZeroCopy := ⟨rho, ⟨0, hn⟩⟩
  have hzero : XiC (xiSpectralPointSupport rho) = 0 := by
    simpa only [q, xiSpectralPoint_eq_support] using XiC_xiSpectralPoint_eq_zero q
  have horder :=
    (XiC_analytic (xiSpectralPointSupport rho) (Set.mem_univ _)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      hzero (hsimple hzero)
  rw [XiC_analyticOrderAt_support] at horder
  exact ENat.coe_inj.mp horder

/-- Under simplicity, two divisor copies with the same centered spectral coordinate are equal. -/
theorem xiSpectralPoint_injective_of_simple (hsimple : XiZerosSimple) :
    Function.Injective xiSpectralPoint := by
  intro q r hqr
  have hbase : q.1 = r.1 := by
    apply xiSpectralPointSupport_injective
    simpa only [xiSpectralPoint_eq_support] using hqr
  apply Sigma.eq hbase
  have hmult := xiDivisorMultiplicity_eq_one_of_simple hsimple r.1
  haveI : Subsingleton
      (Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (r.1 : ℂ)))) := by
    rw [hmult]
    infer_instance
  apply Subsingleton.elim

/-- A divisor copy over a simple centered zero is the unique copy at that spectral point. -/
theorem xiZeroCopy_eq_of_spectralPoint_eq_of_deriv_ne_zero
    (q r : XiZeroCopy) (hqr : xiSpectralPoint q = xiSpectralPoint r)
    (hderiv : deriv XiC (xiSpectralPoint q) ≠ 0) : q = r := by
  have hbase : q.1 = r.1 := by
    apply xiSpectralPointSupport_injective
    simpa only [xiSpectralPoint_eq_support] using hqr
  apply Sigma.eq hbase
  have hderivSupport : deriv XiC (xiSpectralPointSupport r.1) ≠ 0 := by
    simpa only [← hbase, ← xiSpectralPoint_eq_support] using hderiv
  have hmult := xiDivisorMultiplicity_eq_one_of_deriv_ne_zero r.1 hderivSupport
  haveI : Subsingleton
      (Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (r.1 : ℂ)))) := by
    rw [hmult]
    infer_instance
  apply Subsingleton.elim

/-- The actual Xi-divisor evaluation vector of the Hedenmalm eigenfunction at the copy `q`. -/
def xiThetaEigenEvaluationLp (q : XiZeroCopy) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  xiWeilEvaluationLp (xiThetaEigenFourier (xiSpectralPoint q))
    (xiThetaEigenFourier_squareSummable (XiC_xiSpectralPoint_eq_zero q))

@[simp] theorem xiThetaEigenEvaluationLp_apply (q r : XiZeroCopy) :
    xiThetaEigenEvaluationLp q r =
      xiThetaEigenFourier (xiSpectralPoint q) (xiSpectralPoint r) := rfl

/-- Under simplicity, an evaluated Hedenmalm eigenfunction is exactly its nonzero derivative
amplitude times one canonical `ell^2` coordinate vector. -/
theorem xiThetaEigenEvaluationLp_eq_smul_single
    (hsimple : XiZerosSimple) (q : XiZeroCopy) :
    xiThetaEigenEvaluationLp q =
      (I * deriv XiC (xiSpectralPoint q)) • lp.single 2 q (1 : ℂ) := by
  apply Subtype.ext
  funext r
  by_cases hrq : r = q
  · subst r
    rw [xiThetaEigenEvaluationLp_apply, xiThetaEigenFourier_self]
    change I * deriv XiC (xiSpectralPoint q) =
      (I * deriv XiC (xiSpectralPoint q)) *
        (lp.single 2 q (1 : ℂ) : lp (fun _ : XiZeroCopy => ℂ) 2) q
    rw [lp.single_apply_self, mul_one]
  · have hpoint : xiSpectralPoint r ≠ xiSpectralPoint q := by
      intro h
      exact hrq ((xiSpectralPoint_injective_of_simple hsimple) h)
    rw [xiThetaEigenEvaluationLp_apply,
      xiThetaEigenFourier_spectralPoint_eq_zero
        (XiC_xiSpectralPoint_eq_zero q) r hpoint]
    change 0 = (I * deriv XiC (xiSpectralPoint q)) *
      (lp.single 2 q (1 : ℂ) : lp (fun _ : XiZeroCopy => ℂ) 2) r
    rw [lp.single_apply_ne _ _ _ hrq, mul_zero]

/-- The coordinate formula is local: a nonzero derivative at `q` alone makes its theta
eigenfunction evaluation a nonzero multiple of the single coordinate `q`. -/
theorem xiThetaEigenEvaluationLp_eq_smul_single_of_deriv_ne_zero
    (q : XiZeroCopy) (hderiv : deriv XiC (xiSpectralPoint q) ≠ 0) :
    xiThetaEigenEvaluationLp q =
      (I * deriv XiC (xiSpectralPoint q)) • lp.single 2 q (1 : ℂ) := by
  apply Subtype.ext
  funext r
  by_cases hrq : r = q
  · subst r
    rw [xiThetaEigenEvaluationLp_apply, xiThetaEigenFourier_self]
    change I * deriv XiC (xiSpectralPoint q) =
      (I * deriv XiC (xiSpectralPoint q)) *
        (lp.single 2 q (1 : ℂ) : lp (fun _ : XiZeroCopy => ℂ) 2) q
    rw [lp.single_apply_self, mul_one]
  · have hpoint : xiSpectralPoint r ≠ xiSpectralPoint q := by
      intro h
      exact hrq (xiZeroCopy_eq_of_spectralPoint_eq_of_deriv_ne_zero q r h.symm hderiv).symm
    rw [xiThetaEigenEvaluationLp_apply,
      xiThetaEigenFourier_spectralPoint_eq_zero
        (XiC_xiSpectralPoint_eq_zero q) r hpoint]
    change 0 = (I * deriv XiC (xiSpectralPoint q)) *
      (lp.single 2 q (1 : ℂ) : lp (fun _ : XiZeroCopy => ℂ) 2) r
    rw [lp.single_apply_ne _ _ _ hrq, mul_zero]

/-- At a multiple Xi zero, the corresponding Hedenmalm theta eigenfunction is literally the zero
vector in the multiplicity-exact Weil evaluation carrier. -/
theorem xiThetaEigenEvaluationLp_eq_zero_of_deriv_eq_zero
    (q : XiZeroCopy) (hderiv : deriv XiC (xiSpectralPoint q) = 0) :
    xiThetaEigenEvaluationLp q = 0 := by
  apply Subtype.ext
  funext r
  rw [xiThetaEigenEvaluationLp_apply]
  by_cases hrq : xiSpectralPoint r = xiSpectralPoint q
  · rw [hrq, xiThetaEigenFourier_self, hderiv, mul_zero]
    rfl
  · exact xiThetaEigenFourier_spectralPoint_eq_zero
      (XiC_xiSpectralPoint_eq_zero q) r hrq

/-- Algebraic span of all actual Hedenmalm eigenfunction evaluation vectors. -/
def xiThetaEigenAlgebraicSubspace :
    Submodule ℂ (lp (fun _ : XiZeroCopy => ℂ) 2) :=
  Submodule.span ℂ (Set.range xiThetaEigenEvaluationLp)

/-- Canonical basis coordinates lying over simple Xi zeros. -/
def xiSimpleCoordinateBasisSet :
    Set (lp (fun _ : XiZeroCopy => ℂ) 2) :=
  Set.range (fun q : {q : XiZeroCopy // deriv XiC (xiSpectralPoint q) ≠ 0} =>
    lp.single 2 q.1 (1 : ℂ))

/-- Algebraic coordinate space supported on the simple part of the actual Xi divisor. -/
def xiSimpleCoordinateAlgebraicSubspace :
    Submodule ℂ (lp (fun _ : XiZeroCopy => ℂ) 2) :=
  Submodule.span ℂ xiSimpleCoordinateBasisSet

/-- Exact unconditional defect law: the Hedenmalm theta eigenfunction span is precisely the
algebraic span of the divisor coordinates lying over simple Xi zeros. Every multiple-zero fiber is
deleted in full. -/
theorem xiThetaEigenAlgebraicSubspace_eq_simpleCoordinateSubspace :
    xiThetaEigenAlgebraicSubspace = xiSimpleCoordinateAlgebraicSubspace := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, rfl⟩
    by_cases hderiv : deriv XiC (xiSpectralPoint q) ≠ 0
    · rw [xiThetaEigenEvaluationLp_eq_smul_single_of_deriv_ne_zero q hderiv]
      exact xiSimpleCoordinateAlgebraicSubspace.smul_mem _
        (Submodule.subset_span ⟨⟨q, hderiv⟩, rfl⟩)
    · have hzero : deriv XiC (xiSpectralPoint q) = 0 := not_ne_iff.mp hderiv
      rw [xiThetaEigenEvaluationLp_eq_zero_of_deriv_eq_zero q hzero]
      exact xiSimpleCoordinateAlgebraicSubspace.zero_mem
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, rfl⟩
    have heig : xiThetaEigenEvaluationLp q.1 ∈ xiThetaEigenAlgebraicSubspace :=
      Submodule.subset_span (Set.mem_range_self q.1)
    have hc : I * deriv XiC (xiSpectralPoint q.1) ≠ 0 :=
      mul_ne_zero I_ne_zero q.2
    have hscaled := xiThetaEigenAlgebraicSubspace.smul_mem
      (I * deriv XiC (xiSpectralPoint q.1))⁻¹ heig
    rw [xiThetaEigenEvaluationLp_eq_smul_single_of_deriv_ne_zero q.1 q.2,
      inv_smul_smul₀ hc] at hscaled
    exact hscaled

/-- The same exact defect law after Hilbert completion. -/
theorem xiThetaEigenHilbertClosure_eq_simpleCoordinateClosure :
    xiThetaEigenAlgebraicSubspace.topologicalClosure =
      xiSimpleCoordinateAlgebraicSubspace.topologicalClosure := by
  rw [xiThetaEigenAlgebraicSubspace_eq_simpleCoordinateSubspace]

/-- Simplicity makes the Hedenmalm eigenfunction evaluation span dense in the full Xi carrier. -/
theorem xiThetaEigenAlgebraicSubspace_dense_of_simple
    (hsimple : XiZerosSimple) :
    Dense (xiThetaEigenAlgebraicSubspace :
      Set (lp (fun _ : XiZeroCopy => ℂ) 2)) := by
  have hbasisDense : Dense
      (Submodule.span ℂ (Set.range (lpBasis XiZeroCopy)) :
        Set (lp (fun _ : XiZeroCopy => ℂ) 2)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr (lpBasis XiZeroCopy).dense_span
  have hle : Submodule.span ℂ (Set.range (lpBasis XiZeroCopy)) ≤
      xiThetaEigenAlgebraicSubspace := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, rfl⟩
    rw [lpBasis_apply]
    have heig : xiThetaEigenEvaluationLp q ∈ xiThetaEigenAlgebraicSubspace :=
      Submodule.subset_span (Set.mem_range_self q)
    have hc : I * deriv XiC (xiSpectralPoint q) ≠ 0 :=
      mul_ne_zero I_ne_zero (hsimple (XiC_xiSpectralPoint_eq_zero q))
    have hscaled := xiThetaEigenAlgebraicSubspace.smul_mem
      (I * deriv XiC (xiSpectralPoint q))⁻¹ heig
    rw [xiThetaEigenEvaluationLp_eq_smul_single hsimple q,
      inv_smul_smul₀ hc] at hscaled
    exact hscaled
  exact hbasisDense.mono hle

/-- Equivalently, the Hilbert closure of the eigenfunction evaluation span is the whole carrier. -/
theorem xiThetaEigenHilbertClosure_eq_top_of_simple
    (hsimple : XiZerosSimple) :
    xiThetaEigenAlgebraicSubspace.topologicalClosure = ⊤ :=
  Submodule.dense_iff_topologicalClosure_eq_top.mp
    (xiThetaEigenAlgebraicSubspace_dense_of_simple hsimple)

/-- The closed coordinate hyperplane used to detect a missing theta eigenvector. -/
def xiCoordinateZeroSubspace (q : XiZeroCopy) :
    Submodule ℂ (lp (fun _ : XiZeroCopy => ℂ) 2) where
  carrier := {v | v q = 0}
  zero_mem' := rfl
  add_mem' := by
    intro x y hx hy
    change x q = 0 at hx
    change y q = 0 at hy
    change (x + y) q = 0
    change x q + y q = 0
    rw [hx, hy, add_zero]
  smul_mem' := by
    intro c x hx
    change x q = 0 at hx
    change (c • x) q = 0
    change c * x q = 0
    rw [hx, mul_zero]

theorem xiCoordinateZeroSubspace_isClosed (q : XiZeroCopy) :
    IsClosed (xiCoordinateZeroSubspace q :
      Set (lp (fun _ : XiZeroCopy => ℂ) 2)) := by
  change IsClosed {v : lp (fun _ : XiZeroCopy => ℂ) 2 | v q = 0}
  have hcont : Continuous
      (fun v : lp (fun _ : XiZeroCopy => ℂ) 2 => v q) :=
    (lp.evalCLM ℂ (fun _ : XiZeroCopy => ℂ) 2 q).continuous
  exact isClosed_eq hcont continuous_const

/-- If the derivative at one Xi zero vanishes, every theta eigenfunction evaluation lies in the
closed hyperplane that kills the corresponding divisor coordinate. -/
theorem xiThetaEigenAlgebraicSubspace_le_coordinateZero_of_deriv_eq_zero
    (q : XiZeroCopy) (hderiv : deriv XiC (xiSpectralPoint q) = 0) :
    xiThetaEigenAlgebraicSubspace ≤ xiCoordinateZeroSubspace q := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨p, rfl⟩
  change xiThetaEigenEvaluationLp p q = 0
  rw [xiThetaEigenEvaluationLp_apply]
  by_cases hpq : xiSpectralPoint q = xiSpectralPoint p
  · rw [hpq, xiThetaEigenFourier_self]
    have hderivp : deriv XiC (xiSpectralPoint p) = 0 := by
      rw [← hpq]
      exact hderiv
    rw [hderivp, mul_zero]
  · exact xiThetaEigenFourier_spectralPoint_eq_zero
      (XiC_xiSpectralPoint_eq_zero p) q hpq

/-- Density of the theta eigenfunction evaluations forces every Xi zero to be simple. -/
theorem XiZerosSimple_of_xiThetaEigenAlgebraicSubspace_dense
    (hdense : Dense (xiThetaEigenAlgebraicSubspace :
      Set (lp (fun _ : XiZeroCopy => ℂ) 2))) :
    XiZerosSimple := by
  intro alpha halpha
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy alpha).mp halpha
  intro hderiv
  have hderivq : deriv XiC (xiSpectralPoint q) = 0 := by simpa [hq] using hderiv
  have hle := xiThetaEigenAlgebraicSubspace_le_coordinateZero_of_deriv_eq_zero q hderivq
  have hclosure : xiThetaEigenAlgebraicSubspace.topologicalClosure ≤
      xiCoordinateZeroSubspace q :=
    xiThetaEigenAlgebraicSubspace.topologicalClosure_minimal hle
      (xiCoordinateZeroSubspace_isClosed q)
  have htop : xiThetaEigenAlgebraicSubspace.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp hdense
  have hsingle : (lp.single 2 q (1 : ℂ) : lp (fun _ : XiZeroCopy => ℂ) 2) ∈
      xiCoordinateZeroSubspace q := by
    apply hclosure
    rw [htop]
    exact Submodule.mem_top
  change (lp.single 2 q (1 : ℂ) : lp (fun _ : XiZeroCopy => ℂ) 2) q = 0 at hsingle
  rw [lp.single_apply_self] at hsingle
  exact one_ne_zero hsingle

/-- The actual theta eigenfunction evaluations are complete in the multiplicity-exact Xi carrier
if and only if every Xi zero is simple. -/
theorem xiThetaEigenAlgebraicSubspace_dense_iff_simple :
    Dense (xiThetaEigenAlgebraicSubspace :
      Set (lp (fun _ : XiZeroCopy => ℂ) 2)) ↔ XiZerosSimple :=
  ⟨XiZerosSimple_of_xiThetaEigenAlgebraicSubspace_dense,
    xiThetaEigenAlgebraicSubspace_dense_of_simple⟩

/-- Under RH, unit mass on every divisor copy is a real-divisor weight. -/
def xiUnitRealDivisorWeight (hRH : RiemannHypothesis) : XiRealDivisorWeight where
  weight := fun _ => 1
  supported_real := fun q _ => xiSpectralPoint_real_of_rh hRH q

/-- The mass of the unit divisor weight is exactly the analytic multiplicity. -/
theorem xiRealDivisorMass_unit (hRH : RiemannHypothesis) (alpha : ℂ) :
    xiRealDivisorMass (xiUnitRealDivisorWeight hRH) alpha =
      xiSpectralMultiplicity alpha := by
  simp [xiRealDivisorMass, xiUnitRealDivisorWeight, xiSpectralMultiplicity]

/-- Under RH and simplicity, the unit divisor metric is conservative on every theta
eigenfunction. -/
theorem xiUnitRealDivisorWeight_conservative_of_simple
    (hRH : RiemannHypothesis) (hsimple : XiZerosSimple) :
    XiThetaMetricConservative (xiUnitRealDivisorWeight hRH) := by
  rw [xiThetaMetricConservative_iff_mass_pos_and_simple]
  intro alpha halpha
  constructor
  · rw [xiRealDivisorMass_unit]
    exact_mod_cast xiSpectralMultiplicity_pos_of_XiC_eq_zero halpha
  · exact hsimple halpha

/-- A conservative divisor-supported Hedenmalm metric exists exactly under RH plus simplicity. -/
theorem exists_conservative_xiThetaMetric_iff_rh_and_simple :
    (∃ c : XiRealDivisorWeight, XiThetaMetricConservative c) ↔
      RiemannHypothesis ∧ XiZerosSimple := by
  constructor
  · rintro ⟨c, hc⟩
    exact xiThetaMetricConservative_implies_rh_and_simple c hc
  · rintro ⟨hRH, hsimple⟩
    exact ⟨xiUnitRealDivisorWeight hRH,
      xiUnitRealDivisorWeight_conservative_of_simple hRH hsimple⟩

/-- The direct route chain: conservativity forces RH and simplicity, and simplicity then makes the
actual Hedenmalm eigenfunction evaluations complete in the full Xi Hilbert carrier. -/
theorem conservative_xiThetaMetric_implies_rh_simple_and_eigen_dense
    (c : XiRealDivisorWeight) (hcon : XiThetaMetricConservative c) :
    RiemannHypothesis ∧ XiZerosSimple ∧
      Dense (xiThetaEigenAlgebraicSubspace :
        Set (lp (fun _ : XiZeroCopy => ℂ) 2)) := by
  obtain ⟨hRH, hsimple⟩ := xiThetaMetricConservative_implies_rh_and_simple c hcon
  exact ⟨hRH, hsimple, xiThetaEigenAlgebraicSubspace_dense_of_simple hsimple⟩

end

end RHTower
