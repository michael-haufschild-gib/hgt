import GaloisForLFunctions.HTGeometry.StokesUniversalMicrolocalWittLaw
import GaloisForLFunctions.RHTower.MobiusThetaPhysicalParacyclicSourceNullHomology
import GaloisForLFunctions.RHTower.DeningerCenteredFlowCountercharacterRelativeCurvatureNoGo
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Arithmetic Xi realization of the unique Stokes rank port

A common scalar twist cancels on every mixed Hom/Stokes channel.  Conversely, finite distinct
Puiseux coefficients give positive mixed irregularity between every two distinct continuation
orbits, so any scalar tuple invisible to all mixed channels is one common central scalar.  On
determinant lines that scalar has exponent equal to the ramification-weighted physical rank.

The Deninger half-density mate gain therefore has an unconditional arithmetic realization as the
unique channel-invisible central monodromy of the coefficient-generated Stokes skeleton.  At an
actual Xi divisor point, holonomy minus identity on the first nonzero Xi jet is exactly the
already-constructed rational-adelic cyclic residue transgression.  No global vanishing or RH
premise occurs.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.IrregularStokes

noncomputable section

/-! ## Central scalar twists and determinant weight -/

/-- Scalar multiplier induced on a mixed Hom channel by independently twisting its target and
source blocks. -/
def scalarHomTransport {n : ℕ} (lambda : Fin n → ℂˣ)
    (i j : Fin n) (z : ℂ) : ℂ :=
  ((lambda j * (lambda i)⁻¹ : ℂˣ) : ℂ) * z

/-- A common scalar cancels exactly between target and source on every mixed Hom channel. -/
theorem scalarHomTransport_const {n : ℕ} (lambda : ℂˣ)
    (i j : Fin n) (z : ℂ) :
    scalarHomTransport (fun _ => lambda) i j z = z := by
  simp [scalarHomTransport]

/-- On a nonempty complete interaction graph, scalar invisibility is equivalent to one common
central scalar. -/
theorem scalarHomTransport_invisible_iff_constant
    {n : ℕ} (hn : 0 < n) (lambda : Fin n → ℂˣ) :
    (∀ i j z, scalarHomTransport lambda i j z = z) ↔
      ∃ mu : ℂˣ, ∀ i, lambda i = mu := by
  constructor
  · intro h
    let i0 : Fin n := ⟨0, hn⟩
    refine ⟨lambda i0, ?_⟩
    intro i
    have hz := h i0 i 1
    have hu : lambda i * (lambda i0)⁻¹ = 1 := by
      apply Units.ext
      simpa [scalarHomTransport] using hz
    have hm := congrArg (fun u : ℂˣ => u * lambda i0) hu
    simpa using hm
  · rintro ⟨mu, hmu⟩ i j z
    simp [scalarHomTransport, hmu]

/-- Two vertices lie in the same unoriented interaction component when they are related by the
equivalence closure of the directed mixed-channel relation. -/
def SameInteractionComponent {n : ℕ} (edge : Fin n → Fin n → Prop) :
    Fin n → Fin n → Prop :=
  Relation.EqvGen edge

/-- **Universal component law.**  The kernel of scalar relative-channel transport consists
exactly of scalar tuples constant on interaction components.  No connectedness or completeness
hypothesis is built into this statement. -/
theorem scalarHomTransport_invisible_iff_componentwise
    {n : ℕ} (edge : Fin n → Fin n → Prop) (lambda : Fin n → ℂˣ) :
    (∀ i j, edge i j → ∀ z, scalarHomTransport lambda i j z = z) ↔
      ∀ i j, SameInteractionComponent edge i j → lambda i = lambda j := by
  constructor
  · intro h i j hij
    induction hij with
    | rel i j hij =>
        have hz := h i j hij 1
        have hu : lambda j * (lambda i)⁻¹ = 1 := by
          apply Units.ext
          simpa [scalarHomTransport] using hz
        have hm := congrArg (fun u : ℂˣ => u * lambda i) hu
        simpa using hm.symm
    | refl i => rfl
    | symm i j _ ih => exact ih.symm
    | trans i j k _ _ hij hjk => exact hij.trans hjk
  · intro h i j hij z
    have hlambda : lambda i = lambda j :=
      h i j (Relation.EqvGen.rel i j hij)
    simp [scalarHomTransport, hlambda]

/-- Integral ramification-weighted physical rank of an actual dimension vector. -/
def physicalRankNat {n : ℕ} (r x : Fin n → ℕ) : ℕ :=
  ∑ i, r i * x i

/-- Ramification-weighted physical rank carried by one chosen component of a finite partition. -/
def componentPhysicalRankNat {n k : ℕ} (component : Fin n → Fin k)
    (r x : Fin n → ℕ) (a : Fin k) : ℕ :=
  ∑ i with component i = a, r i * x i

/-- A common scalar acts on the product of block determinant lines with exponent equal to total
physical rank. -/
theorem commonScalar_determinantWeight {n : ℕ}
    (lambda : ℂ) (r x : Fin n → ℕ) :
    (∏ i, lambda ^ (r i * x i)) =
      lambda ^ physicalRankNat r x := by
  simpa [physicalRankNat] using
    (Finset.prod_pow_eq_pow_sum Finset.univ (fun i => r i * x i) lambda)

/-- If a scalar tuple is constant with value `lambda a` on the fibre of component label `a`, its
determinant character factors through the component physical-rank ports. -/
theorem componentScalar_determinantWeight {n k : ℕ}
    (lambda : Fin k → ℂ) (component : Fin n → Fin k)
    (r x : Fin n → ℕ) :
    (∏ i, lambda (component i) ^ (r i * x i)) =
      ∏ a, lambda a ^ componentPhysicalRankNat component r x a := by
  rw [← Finset.prod_fiberwise Finset.univ component
    (fun i => lambda (component i) ^ (r i * x i))]
  apply Finset.prod_congr rfl
  intro a _
  rw [componentPhysicalRankNat, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

/-- Matrix-level determinant response of a scalar monodromy twist. -/
theorem scalarTwist_det {r : ℕ} (lambda : ℂ)
    (T : Matrix (Fin r) (Fin r) ℂ) :
    Matrix.det (lambda • T) = lambda ^ r * Matrix.det T := by
  rw [Matrix.det_smul, Fintype.card_fin]

/-! ## Formal-contact blindness and coefficient-generated connectedness -/

/-- Two coefficient systems occupy the same formal contact stratum when all coefficient equality
patterns agree at every exponent. -/
def SameCoefficientEqualityPattern {m K N : ℕ}
    (p q : FinitePuiseuxFamily m K N) : Prop :=
  ∀ i j e, (p.coeff i e = p.coeff j e) ↔
    (q.coeff i e = q.coeff j e)

/-- Formal-contact strata forget all coefficient magnitudes that do not change an equality
pattern. -/
theorem contactNumerator_eq_of_sameCoefficientEqualityPattern
    {m K N : ℕ} {p q : FinitePuiseuxFamily m K N}
    (h : SameCoefficientEqualityPattern p q) (i j : Fin m) :
    p.contactNumerator i j = q.contactNumerator i j := by
  unfold FinitePuiseuxFamily.contactNumerator
  apply Finset.sup_congr rfl
  intro e _
  exact if_congr (h i j e) rfl rfl

namespace PuiseuxOrbitCoareaDatum

variable {n m K N : ℕ}

/-- A scalar tuple is invisible when it acts trivially on every nonzero coefficient-generated
mixed Hom channel. -/
def ScalarTwistInvisible
    (d : PuiseuxOrbitCoareaDatum n m K N) (lambda : Fin n → ℂˣ) : Prop :=
  ∀ i j, 0 < d.normalizedHomIrregularity i j →
    ∀ z, scalarHomTransport lambda i j z = z

/-- Distinct coefficient-generated continuation orbits have strictly positive mixed Hom
irregularity.  Thus their interaction graph is complete. -/
theorem normalizedHomIrregularity_pos_of_ne
    (d : PuiseuxOrbitCoareaDatum n m K N) {i j : Fin n} (hij : i ≠ j) :
    0 < d.normalizedHomIrregularity i j := by
  obtain ⟨a, ha⟩ := d.orbit_surjective i
  obtain ⟨b, hb⟩ := d.orbit_surjective j
  rw [normalizedHomIrregularity]
  refine Finset.sum_pos' ?_ ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, ?_⟩
  · intro a' _
    apply Finset.sum_nonneg
    intro b' _
    positivity
  · refine Finset.sum_pos' ?_ ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, ?_⟩
    · intro b' _
      positivity
    · have hab : a ≠ b := by
        intro hab
        apply hij
        calc
          i = d.orbit a := ha.symm
          _ = d.orbit b := by rw [hab]
          _ = j := hb
      exact div_pos
        (Nat.cast_pos.mpr (d.branches.contactNumerator_pos_of_ne hab))
        (Nat.cast_pos.mpr d.branches.coverDegree_pos)

/-- **Connected central-twist classification.**  A scalar twist invisible to all
coefficient-generated Hom/Stokes channels is exactly one common central scalar. -/
theorem scalarTwistInvisible_iff_constant
    (d : PuiseuxOrbitCoareaDatum n m K N) (hn : 0 < n)
    (lambda : Fin n → ℂˣ) :
    d.ScalarTwistInvisible lambda ↔
      ∃ mu : ℂˣ, ∀ i, lambda i = mu := by
  constructor
  · intro h
    apply (scalarHomTransport_invisible_iff_constant hn lambda).mp
    intro i j z
    by_cases hij : i = j
    · subst j
      simp [scalarHomTransport]
    · exact h i j (d.normalizedHomIrregularity_pos_of_ne hij) z
  · intro h
    have hall := (scalarHomTransport_invisible_iff_constant hn lambda).2 h
    intro i j _ z
    exact hall i j z

/-- The integral determinant exponent is the natural-number lattice restriction of the same real
physical-rank functional appearing in the Stokes coarea law. -/
theorem physicalRank_natCast
    (d : PuiseuxOrbitCoareaDatum n m K N) (x : Fin n → ℕ) :
    d.toOrbitCoareaDatum.physicalRank (fun i => (x i : ℝ)) =
      (physicalRankNat d.toOrbitCoareaDatum.ramification x : ℝ) := by
  rw [OrbitCoareaDatum.physicalRank_eq_ramification_sum]
  simp [physicalRankNat, mul_comm]

/-- Mixed Hom irregularities are constant on a formal contact stratum. -/
theorem normalizedHomIrregularity_eq_of_contactNumerator_eq
    (d e : PuiseuxOrbitCoareaDatum n m K N)
    (horbit : d.orbit = e.orbit)
    (hcontact : ∀ a b, d.branches.contactNumerator a b =
      e.branches.contactNumerator a b)
    (i j : Fin n) :
    d.normalizedHomIrregularity i j = e.normalizedHomIrregularity i j := by
  simp only [normalizedHomIrregularity]
  simp_rw [horbit, hcontact]

/-- The coefficient-generated Cartan/coarea polarization is constant on each formal contact
stratum.  Continuous arithmetic clock magnitude therefore cannot be recovered from this bare
quadratic datum. -/
theorem cartanQuadratic_eq_of_contactNumerator_eq
    (d e : PuiseuxOrbitCoareaDatum n m K N)
    (horbit : d.orbit = e.orbit)
    (hcontact : ∀ a b, d.branches.contactNumerator a b =
      e.branches.contactNumerator a b)
    (x : Fin n → ℝ) :
    d.toOrbitCoareaDatum.cartanQuadratic x =
      e.toOrbitCoareaDatum.cartanQuadratic x := by
  have hphys : d.toOrbitCoareaDatum.physicalRank x =
      e.toOrbitCoareaDatum.physicalRank x := by
    simp [OrbitCoareaDatum.physicalRank, OrbitCoareaDatum.liftCharge,
      PuiseuxOrbitCoareaDatum.toOrbitCoareaDatum, horbit]
  have hhom : ∀ i j,
      d.toOrbitCoareaDatum.homIrregularity i j =
        e.toOrbitCoareaDatum.homIrregularity i j := by
    intro i j
    rw [d.homIrregularity_eq_normalizedCoefficientSum,
      e.homIrregularity_eq_normalizedCoefficientSum]
    exact d.normalizedHomIrregularity_eq_of_contactNumerator_eq
      e horbit hcontact i j
  have hpair : d.toOrbitCoareaDatum.contactPairing x =
      e.toOrbitCoareaDatum.contactPairing x := by
    rw [← d.toOrbitCoareaDatum.orbitContactPairing_eq_contactPairing,
      ← e.toOrbitCoareaDatum.orbitContactPairing_eq_contactPairing]
    simp only [OrbitCoareaDatum.orbitContactPairing]
    simp_rw [hhom]
  simp only [OrbitCoareaDatum.cartanQuadratic]
  rw [hphys, hpair]
  rfl

end PuiseuxOrbitCoareaDatum

/-! ## Arithmetic central holonomy and the Xi source transgression -/

/-- Holonomy minus identity for the Deninger arithmetic central character acting on one complex
coefficient. -/
def centralHolonomyDefect (n : ℕ) (s : ℂ) (c : ℂ) : ℂ :=
  ((RHTower.deningerHalfDensityMateGain n s : ℂ) - 1) * c

/-- The arithmetic central character is multiplicative in the positive integer clock. -/
theorem centralHolonomyDefect_mul_clock
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (s : ℂ) :
    RHTower.deningerHalfDensityMateGain (m * n) s =
      RHTower.deningerHalfDensityMateGain m s *
        RHTower.deningerHalfDensityMateGain n s :=
  RHTower.deningerHalfDensityMateGain_mul hm hn s

/-- Critical reflection dualizes the arithmetic central local system. -/
theorem centralHolonomy_reflection (n : ℕ) (s : ℂ) :
    RHTower.deningerHalfDensityMateGain n (1 - star s) =
      (RHTower.deningerHalfDensityMateGain n s)⁻¹ :=
  RHTower.deningerHalfDensityMateGain_reflection n s

/-- Clock exponentiation is exactly determinant exponentiation by an integral physical rank. -/
theorem centralHolonomy_pow_clock
    {n : ℕ} (hn : 0 < n) (m : ℕ) (s : ℂ) :
    RHTower.deningerHalfDensityMateGain (n ^ m) s =
      RHTower.deningerHalfDensityMateGain n s ^ m := by
  induction m with
  | zero => simp [RHTower.deningerHalfDensityMateGain]
  | succ m ih =>
      rw [pow_succ,
        RHTower.deningerHalfDensityMateGain_mul (pow_pos hn m) hn s,
        ih, pow_succ]

/-- Holonomy defect on the determinant line of a dimension vector. -/
def determinantCentralHolonomyDefect {n : ℕ}
    (clock : ℕ) (s : ℂ) (r x : Fin n → ℕ) (c : ℂ) : ℂ :=
  ((RHTower.deningerHalfDensityMateGain clock s : ℂ) ^
      physicalRankNat r x - 1) * c

/-- Reading the physical rank through the arithmetic clock or through determinant holonomy gives
the same unsquared defect. -/
theorem centralHolonomyDefect_pow_clock_eq_determinant
    {k n : ℕ} (hn : 0 < n) (s : ℂ) (r x : Fin k → ℕ) (c : ℂ) :
    centralHolonomyDefect (n ^ physicalRankNat r x) s c =
      determinantCentralHolonomyDefect n s r x c := by
  simp only [centralHolonomyDefect, determinantCentralHolonomyDefect]
  rw [centralHolonomy_pow_clock hn]
  norm_cast

/-- **Xi arithmetic realization.**  The certified rational-adelic cyclic residue transgression is
literally holonomy minus identity of the arithmetic central twist on the first Xi jet landing. -/
theorem ccmXiResidue_eq_centralHolonomyDefect
    (n : ℕ) (rho : RHTower.XiDivisorSupport)
    (x : RHTower.CCMRationalAdelicDegreeOneCyclicSource) :
    RHTower.ccmRationalAdelicTwoLegCyclicResidue
      (GaloisForLFunctions.HTGeometry.cyclicParacyclicEquivarianceDefect
        RHTower.ccmRationalAdelicDegreeOneCyclicRotation
        (RHTower.sourceDaggerNormalizedDegreeOneRotationLinear n (rho : ℂ))
        (RHTower.ccmMobiusThetaXiJetTwoLegLanding
          (RHTower.xiSupportMultiplicity rho)
          (RHTower.xiSpectralPointSupport rho)) x) =
      centralHolonomyDefect n (rho : ℂ)
        (RHTower.thetaInternalJetLeadingSourceCoefficient rho *
          RHTower.ccmRationalAdelicDegreeOneTrace x) := by
  rw [RHTower.ccmMobiusThetaTwoLegParacyclicDefect_residue]
  simp [centralHolonomyDefect]
  ring

/-- **Rank-port/Xi determinant law.**  If the arithmetic clock is raised by the integral
physical-rank port, the rational-adelic Xi residue is exactly holonomy minus identity on the
corresponding determinant line. -/
theorem ccmXiResidue_rankPortClock_eq_determinantCentralHolonomyDefect
    {k n : ℕ} (hn : 0 < n) (rho : RHTower.XiDivisorSupport)
    (v : RHTower.CCMRationalAdelicDegreeOneCyclicSource)
    (r x : Fin k → ℕ) :
    RHTower.ccmRationalAdelicTwoLegCyclicResidue
      (GaloisForLFunctions.HTGeometry.cyclicParacyclicEquivarianceDefect
        RHTower.ccmRationalAdelicDegreeOneCyclicRotation
        (RHTower.sourceDaggerNormalizedDegreeOneRotationLinear
          (n ^ physicalRankNat r x) (rho : ℂ))
        (RHTower.ccmMobiusThetaXiJetTwoLegLanding
          (RHTower.xiSupportMultiplicity rho)
          (RHTower.xiSpectralPointSupport rho)) v) =
      determinantCentralHolonomyDefect n (rho : ℂ) r x
        (RHTower.thetaInternalJetLeadingSourceCoefficient rho *
          RHTower.ccmRationalAdelicDegreeOneTrace v) := by
  rw [ccmXiResidue_eq_centralHolonomyDefect]
  exact centralHolonomyDefect_pow_clock_eq_determinant hn _ _ _ _

/-- On the literal ordinary-prime trace-one cycle, the central holonomy defect retains the complete
first nonzero Xi jet. -/
theorem ccmXiPrimeResidue_eq_centralHolonomyDefect
    (n : ℕ) (rho : RHTower.XiDivisorSupport) (p : Nat.Primes) :
    RHTower.ccmRationalAdelicTwoLegCyclicResidue
      (GaloisForLFunctions.HTGeometry.cyclicParacyclicEquivarianceDefect
        RHTower.ccmRationalAdelicDegreeOneCyclicRotation
        (RHTower.sourceDaggerNormalizedDegreeOneRotationLinear n (rho : ℂ))
        (RHTower.ccmMobiusThetaXiJetTwoLegLanding
          (RHTower.xiSupportMultiplicity rho)
          (RHTower.xiSpectralPointSupport rho))
        (RHTower.ccmRationalAdelicOrdinaryPrimeCycleAtom p)) =
      centralHolonomyDefect n (rho : ℂ)
        (RHTower.thetaInternalJetLeadingSourceCoefficient rho) := by
  rw [ccmXiResidue_eq_centralHolonomyDefect]
  simp [RHTower.ccmRationalAdelicOrdinaryPrimeCycleAtom_trace_eq_one]

/-- The realized Xi central holonomy defect vanishes exactly on the critical line.  This is a
classifier, not a global vanishing assertion. -/
theorem ccmXiPrimeCentralHolonomyDefect_eq_zero_iff
    {n : ℕ} (hn : 2 ≤ n) (rho : RHTower.XiDivisorSupport) :
    centralHolonomyDefect n (rho : ℂ)
        (RHTower.thetaInternalJetLeadingSourceCoefficient rho) = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    have hc := RHTower.thetaInternalJetLeadingSourceCoefficient_ne_zero rho
    have hfactor :
        (RHTower.deningerHalfDensityMateGain n (rho : ℂ) : ℂ) - 1 = 0 :=
      (mul_eq_zero.mp h).resolve_right hc
    have hgain : RHTower.deningerHalfDensityMateGain n (rho : ℂ) = 1 := by
      exact_mod_cast (sub_eq_zero.mp hfactor)
    exact (RHTower.deningerHalfDensityMateGain_eq_one_iff_re_eq_half hn _).mp hgain
  · intro hline
    have hgain :=
      (RHTower.deningerHalfDensityMateGain_eq_one_iff_re_eq_half hn (rho : ℂ)).2 hline
    simp [centralHolonomyDefect, hgain]

/-- A positive physical-rank determinant port has zero Xi holonomy defect exactly on the critical
line.  Rank zero is excluded because its determinant character is identically trivial. -/
theorem ccmXiPrimeDeterminantCentralHolonomyDefect_eq_zero_iff
    {k n : ℕ} (hn : 2 ≤ n) (rho : RHTower.XiDivisorSupport)
    (r x : Fin k → ℕ) (hport : 0 < physicalRankNat r x) :
    determinantCentralHolonomyDefect n (rho : ℂ) r x
        (RHTower.thetaInternalJetLeadingSourceCoefficient rho) = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_two hn
  rw [← centralHolonomyDefect_pow_clock_eq_determinant hnpos]
  exact ccmXiPrimeCentralHolonomyDefect_eq_zero_iff
    (le_trans hn (Nat.le_pow hport)) rho

end
end GaloisForLFunctions.IrregularStokes
