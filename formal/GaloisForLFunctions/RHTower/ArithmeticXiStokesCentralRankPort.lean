import GaloisForLFunctions.HTGeometry.StokesUniversalMicrolocalWittLaw
import GaloisForLFunctions.RHTower.MobiusThetaPhysicalParacyclicSourceNullHomology
import GaloisForLFunctions.RHTower.DeningerCenteredFlowCountercharacterRelativeCurvatureNoGo
import GaloisForLFunctions.RHTower.PrimeClockCriticalProfile
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Connected.TotallyDisconnected

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
open Filter Topology

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

/-- A continuously varying physical-rank family on a preconnected parameter space is constant,
because physical rank is discrete. -/
theorem continuousPhysicalRankFamily_constant
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (rank : X → ℕ) (hrank : Continuous rank) (s t : X) :
    rank s = rank t :=
  PreconnectedSpace.constant (by infer_instance : PreconnectedSpace X) hrank

/-- The Deninger central defect cannot be realized as one continuously varying physical rank on
the complex parameter plane. -/
theorem not_exists_continuousPhysicalRank_eq_centralDefect
    {n : ℕ} (hn : 2 ≤ n) :
    ¬ ∃ rank : ℂ → ℕ, Continuous rank ∧
      ∀ s, (rank s : ℝ) = RHTower.deningerHalfDensityMateGain n s - 1 := by
  rintro ⟨rank, hrank, hrealize⟩
  have hconst : rank (0 : ℂ) = rank (1 / 2 : ℂ) :=
    continuousPhysicalRankFamily_constant rank hrank _ _
  have hhalfGain :
      RHTower.deningerHalfDensityMateGain n (1 / 2 : ℂ) = 1 :=
    (RHTower.deningerHalfDensityMateGain_eq_one_iff_re_eq_half hn _).2 (by norm_num)
  have hhalfRank : rank (1 / 2 : ℂ) = 0 := by
    have h := hrealize (1 / 2 : ℂ)
    rw [hhalfGain, sub_self] at h
    exact_mod_cast h
  have hzeroRank : rank (0 : ℂ) = 0 := hconst.trans hhalfRank
  have hzeroGain : RHTower.deningerHalfDensityMateGain n (0 : ℂ) = 1 := by
    have h := hrealize (0 : ℂ)
    rw [hzeroRank, Nat.cast_zero] at h
    linarith
  have hline :=
    (RHTower.deningerHalfDensityMateGain_eq_one_iff_re_eq_half hn (0 : ℂ)).1 hzeroGain
  norm_num at hline

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

/-! ## Reflection-paired prime energy and arithmetic vanishing -/

/-- Real determinant-holonomy defect at a prime clock.  At a Xi divisor this is the normalized
rank-powered cyclic residue, with the nonzero leading Xi jet divided out. -/
def determinantCentralGainDefect (p M : ℕ) (s : ℂ) : ℝ :=
  RHTower.deningerHalfDensityMateGain p s ^ M - 1

/-- The positive reflected prime energy selected by the Stokes determinant-rank port. -/
def stokesRankPortPrimeEnergy (N M : ℕ) (s : ℂ) : ℝ :=
  RHTower.primeClockCutoffEnergy N ((M : ℝ) * (s.re - 1 / 2))

/-- Determinant holonomy at rank `M` is the exponential of twice the rank-scaled horizontal
coordinate. -/
theorem centralHolonomy_pow_eq_exp_rankPort (p M : ℕ) (s : ℂ) :
    RHTower.deningerHalfDensityMateGain p s ^ M =
      Real.exp (2 * (M : ℝ) * (s.re - 1 / 2) * Real.log p) := by
  rw [RHTower.deningerHalfDensityMateGain, ← Real.exp_nat_mul]
  congr 1
  ring

/-- Reflection pairing turns two signed determinant defects into one positive hyperbolic square. -/
theorem determinantCentralGainDefect_reflection_product
    (p M : ℕ) (s : ℂ) :
    -(determinantCentralGainDefect p M s *
        determinantCentralGainDefect p M (1 - star s)) =
      4 * Real.sinh ((M : ℝ) * (s.re - 1 / 2) * Real.log p) ^ 2 := by
  rw [determinantCentralGainDefect, determinantCentralGainDefect,
    centralHolonomy_pow_eq_exp_rankPort,
    centralHolonomy_pow_eq_exp_rankPort]
  have hreflect : (1 - star s).re - 1 / 2 = -(s.re - 1 / 2) := by
    simp
    ring
  rw [hreflect]
  let u : ℝ := (M : ℝ) * (s.re - 1 / 2) * Real.log p
  rw [show 2 * (M : ℝ) * (s.re - 1 / 2) * Real.log p = 2 * u by
      dsimp [u]; ring,
    show 2 * (M : ℝ) * (-(s.re - 1 / 2)) * Real.log p = -(2 * u) by
      dsimp [u]; ring]
  change -((Real.exp (2 * u) - 1) * (Real.exp (-(2 * u)) - 1)) =
    4 * Real.sinh u ^ 2
  rw [Real.sinh_eq, Real.exp_neg]
  have hdouble : Real.exp (2 * u) = Real.exp u ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hdouble, Real.exp_neg u]
  field_simp [Real.exp_ne_zero]
  ring

/-- Exact factorization of the Stokes prime energy as the negative product of the two normalized
Xi-compatible transgression defects at reflected parameters. -/
theorem stokesRankPortPrimeEnergy_eq_reflectionDefectSum
    (N M : ℕ) (s : ℂ) :
    stokesRankPortPrimeEnergy N M s =
      ∑ p ∈ Nat.primesLE N,
        -(determinantCentralGainDefect p M s *
          determinantCentralGainDefect p M (1 - star s)) / p := by
  rw [stokesRankPortPrimeEnergy, RHTower.primeClockCutoffEnergy_eq_sinh]
  apply Finset.sum_congr rfl
  intro p hp
  rw [determinantCentralGainDefect_reflection_product]

/-- At a cutoff containing the prime `2`, prime-clock energy vanishes only at zero horizontal
displacement. -/
theorem primeClockCutoffEnergy_eq_zero_iff
    {N : ℕ} (hN : 2 ≤ N) (ε : ℝ) :
    RHTower.primeClockCutoffEnergy N ε = 0 ↔ ε = 0 := by
  have hsusceptibility : 0 < RHTower.primeClockSusceptibility N := by
    rw [RHTower.primeClockSusceptibility]
    apply Finset.sum_pos'
    · intro p hp
      positivity
    · refine ⟨2, Nat.mem_primesLE.mpr ⟨hN, by norm_num⟩, ?_⟩
      positivity
  constructor
  · intro hzero
    have hlower := RHTower.primeClockCutoffEnergy_quadratic_lower N ε
    rw [hzero] at hlower
    have hepsilon : ε ^ 2 = 0 := by nlinarith [sq_nonneg ε]
    exact sq_eq_zero_iff.mp hepsilon
  · rintro rfl
    exact RHTower.primeClockCutoffEnergy_zero N

/-- **Finite arithmetic vanishing theorem.**  For positive physical rank and any cutoff containing
`2`, reflection-paired Stokes/Xi prime energy vanishes exactly on the critical line. -/
theorem stokesRankPortPrimeEnergy_eq_zero_iff
    {N M : ℕ} (hN : 2 ≤ N) (hM : 0 < M) (s : ℂ) :
    stokesRankPortPrimeEnergy N M s = 0 ↔ s.re = 1 / 2 := by
  rw [stokesRankPortPrimeEnergy, primeClockCutoffEnergy_eq_zero_iff hN]
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  constructor
  · intro h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hMne)
  · intro h
    rw [h, sub_self, mul_zero]

/-- The universal Mertens profile is even. -/
theorem primeClockUniversalProfile_neg (c : ℝ) :
    RHTower.primeClockUniversalProfile (-c) =
      RHTower.primeClockUniversalProfile c := by
  unfold RHTower.primeClockUniversalProfile
  apply intervalIntegral.integral_congr
  intro u hu
  unfold RHTower.primeClockScalingProfileIntegrand
  rw [neg_mul, Real.sinh_neg]
  ring

/-- The prime-clock profile dominates its exact quadratic susceptibility limit. -/
theorem primeClockUniversalProfile_quadratic_lower (c : ℝ) :
    2 * c ^ 2 ≤ RHTower.primeClockUniversalProfile c := by
  have hleft : Tendsto
      (fun N : ℕ => 4 * c ^ 2 *
        (RHTower.primeClockSusceptibility N / Real.log N ^ 2))
      Filter.atTop (nhds (2 * c ^ 2)) := by
    have h := RHTower.tendsto_primeClockSusceptibility_div_log_sq.const_mul
      (4 * c ^ 2)
    convert h using 1
    norm_num
    ring
  apply le_of_tendsto_of_tendsto hleft
    (RHTower.tendsto_primeClockCutoffEnergy_critical_profile c)
  filter_upwards [Filter.eventually_ge_atTop 2] with N hN
  exact (RHTower.primeClockCutoffEnergy_critical_scaled_sandwich N c hN).1

/-- The universal Mertens profile vanishes only at the central scaling coordinate. -/
theorem primeClockUniversalProfile_eq_zero_iff (c : ℝ) :
    RHTower.primeClockUniversalProfile c = 0 ↔ c = 0 := by
  constructor
  · intro hzero
    have hlower := primeClockUniversalProfile_quadratic_lower c
    rw [hzero] at hlower
    nlinarith [sq_nonneg c]
  · rintro rfl
    simp [RHTower.primeClockUniversalProfile,
      RHTower.primeClockScalingProfileIntegrand]

/-- The universal Mertens profile is strictly positive away from zero. -/
theorem primeClockUniversalProfile_pos_iff (c : ℝ) :
    0 < RHTower.primeClockUniversalProfile c ↔ c ≠ 0 := by
  constructor
  · intro hpos hzero
    subst c
    simp [RHTower.primeClockUniversalProfile,
      RHTower.primeClockScalingProfileIntegrand] at hpos
  · intro hc
    have hlower := primeClockUniversalProfile_quadratic_lower c
    have hsq : 0 < c ^ 2 := sq_pos_of_ne_zero hc
    nlinarith

/-- Subcritical rank-port windows have vanishing prime energy. -/
theorem tendsto_stokesRankPortPrimeEnergy_zero_of_scaled_tendsto_zero
    (M : ℕ) (s : ℕ → ℂ)
    (hscaled : Tendsto
      (fun N : ℕ => (M : ℝ) * ((s N).re - 1 / 2) * Real.log N)
      Filter.atTop (nhds 0)) :
    Tendsto (fun N : ℕ => stokesRankPortPrimeEnergy N M (s N))
      Filter.atTop (nhds 0) := by
  simpa [stokesRankPortPrimeEnergy] using
    RHTower.tendsto_primeClockCutoffEnergy_zero_of_scaled_tendsto_zero
      (fun N : ℕ => (M : ℝ) * ((s N).re - 1 / 2)) hscaled

/-- **Rank-port/Mertens critical-window law.**  If the forced rank-scaled horizontal coordinate
times `log N` tends to `c`, the reflected Stokes/Xi prime energy tends to the universal prime-clock
profile.  In particular the limit is independent of the Stokes ranks after this forced scaling. -/
theorem tendsto_stokesRankPortPrimeEnergy_critical_profile
    (M : ℕ) (s : ℕ → ℂ) (c : ℝ)
    (hscaled : Tendsto
      (fun N : ℕ => (M : ℝ) * ((s N).re - 1 / 2) * Real.log N)
      Filter.atTop (nhds c)) :
    Tendsto (fun N : ℕ => stokesRankPortPrimeEnergy N M (s N))
      Filter.atTop (nhds (RHTower.primeClockUniversalProfile c)) := by
  let cN : ℕ → ℝ := fun N =>
    (M : ℝ) * ((s N).re - 1 / 2) * Real.log N
  have hprofile :=
    RHTower.tendsto_primeClockCutoffEnergy_critical_profile_of_tendsto cN c hscaled
  apply hprofile.congr'
  filter_upwards [Filter.eventually_ge_atTop 2] with N hN
  have hlogne : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [stokesRankPortPrimeEnergy]
  congr 1
  dsimp [cN]
  field_simp

/-- Supercritical rank-port windows have divergent prime energy. -/
theorem tendsto_stokesRankPortPrimeEnergy_atTop_of_scaled_tendsto_atTop
    (M : ℕ) (s : ℕ → ℂ)
    (hscaled : Tendsto
      (fun N : ℕ => |(M : ℝ) * ((s N).re - 1 / 2)| * Real.log N)
      Filter.atTop Filter.atTop) :
    Tendsto (fun N : ℕ => stokesRankPortPrimeEnergy N M (s N))
      Filter.atTop Filter.atTop := by
  simpa [stokesRankPortPrimeEnergy] using
    RHTower.tendsto_primeClockCutoffEnergy_atTop_of_scaled_tendsto_atTop
      (fun N : ℕ => (M : ℝ) * ((s N).re - 1 / 2)) hscaled

/-- Global unitarity of the pre-divisor arithmetic central character on Xi support.  Positivity of
the holonomy makes `gain = 1` exactly the rank-one unitary condition. -/
def XiArithmeticCentralCharacterUnitary (n : ℕ) : Prop :=
  ∀ rho : RHTower.XiDivisorSupport,
    RHTower.deningerHalfDensityMateGain n (rho : ℂ) = 1

/-- The arithmetic central character is unitary on every Xi divisor fibre exactly when RH holds.
This is a classifier and does not assert either side. -/
theorem xiArithmeticCentralCharacterUnitary_iff_riemannHypothesis
    {n : ℕ} (hn : 2 ≤ n) :
    XiArithmeticCentralCharacterUnitary n ↔ RiemannHypothesis := by
  rw [← RHTower.xiBoundaryCharacterNeutral_iff_riemannHypothesis]
  unfold XiArithmeticCentralCharacterUnitary RHTower.XiBoundaryCharacterNeutral
  apply forall_congr'
  intro rho
  rw [RHTower.deningerHalfDensityMateGain_eq_one_iff_re_eq_half hn,
    RHTower.xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff]

end
end GaloisForLFunctions.IrregularStokes
