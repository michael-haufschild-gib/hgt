import GaloisForLFunctions.RHTower.XiShiftedHardEdgePolynomialGaussianFiniteHankelCriterion
import GaloisForLFunctions.RHTower.XiShiftedParabolicDegreeHorizon

/-!
# Cofinal linear finite-Hankel dimension at the Route-U hard edge

The existing exact finite-Hankel criterion used an existential compact-support cutoff.  This
module resolves that cutoff quantitatively.  At integral hard-edge mass `k + 1`, cutoff index `n`
has an explicit Chebyshev truncation `(n + 1) * (k + 1) + 1`.  Its reciprocal pullback has at most
one more coefficient.  False RH therefore produces negative finite shifted-Hankel quadratics
cofinally with dimension linear in hard-edge mass.  The parabolic degree horizon gives the
opposite dimension inequality for the same packets.

No numerical evaluation or zero-location hypothesis is used.
-/

open scoped BigOperators SchwartzMap FourierTransform
open Complex Filter Polynomial Set

noncomputable section

namespace RHTower

/-- Explicit positive-frequency truncation for cutoff index `n` at integral hard-edge mass
`k + 1`. -/
def routeUExplicitFiniteChebyshevCutoff (n k : ℕ) : ℕ :=
  (n + 1) * (k + 1) + 1

/-- The canonical expanding cutoff vanishes beyond the explicit hard-edge truncation. -/
theorem routeURealEvenCompactApproximation_eq_zero_of_explicitCutoff
    (n k j : ℕ) (g : SchwartzMap ℝ ℝ)
    (hj : routeUExplicitFiniteChebyshevCutoff n k ≤ j) :
    SchwartzMap.compactSupportApproximation n (routeURealEvenAmplitude g)
        (routeUHardEdgeMesh (k : ℝ) * (j + 1 : ℝ)) = 0 := by
  rw [SchwartzMap.compactSupportApproximation_apply]
  suffices SchwartzMap.scaledUnitCutoff n
      (routeUHardEdgeMesh (k : ℝ) * (j + 1 : ℝ)) = 0 by
    rw [this, zero_mul]
  rw [SchwartzMap.scaledUnitCutoff_apply]
  apply image_eq_zero_of_notMem_tsupport
  rw [SchwartzMap.compactIntervalCutoff_tsupport]
  simp only [abs_zero, zero_add, Set.mem_setOf_eq]
  have hjNat : (n + 1) * (k + 1) < j + 1 := by
    dsimp only [routeUExplicitFiniteChebyshevCutoff] at hj
    omega
  have hjReal : (((n + 1) * (k + 1) : ℕ) : ℝ) < ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast hjNat
  have hkPos : 0 < (k : ℝ) + 1 := by positivity
  have hnPos : 0 < (n : ℝ) + 1 := by positivity
  have hmass : routeUHardEdgeMass (k : ℝ) = (k : ℝ) + 1 := by
    rw [routeUHardEdgeMass, abs_of_nonneg (Nat.cast_nonneg k)]
    ring
  have hmesh : routeUHardEdgeMesh (k : ℝ) = 2 / ((k : ℝ) + 1) := by
    rw [routeUHardEdgeMesh, hmass]
  have hlarge :
      2 * ((n : ℝ) + 1) <
        routeUHardEdgeMesh (k : ℝ) * ((j : ℝ) + 1) := by
    rw [hmesh, div_mul_eq_mul_div, lt_div_iff₀ hkPos]
    push_cast at hjReal
    nlinarith
  have hscaled :
      2 < ((n : ℝ) + 1)⁻¹ *
        (routeUHardEdgeMesh (k : ℝ) * ((j : ℝ) + 1)) := by
    calc
      2 = ((n : ℝ) + 1)⁻¹ * (2 * ((n : ℝ) + 1)) := by
        field_simp
      _ < ((n : ℝ) + 1)⁻¹ *
          (routeUHardEdgeMesh (k : ℝ) * ((j : ℝ) + 1)) :=
        mul_lt_mul_of_pos_left hlarge (inv_pos.mpr hnPos)
  rw [abs_of_pos (lt_trans (by norm_num) hscaled)]
  exact not_le_of_gt hscaled

/-- The explicit finite Chebyshev packet has degree at most its truncation. -/
theorem natDegree_routeUFiniteChebyshevPacketPolynomial_le
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (r : ℝ) (N : ℕ) :
    (routeUFiniteChebyshevPacketPolynomial n g r N).natDegree ≤ N := by
  rw [routeUFiniteChebyshevPacketPolynomial]
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · rw [Polynomial.natDegree_C]
    exact Nat.zero_le N
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    calc
      (Polynomial.C
          (2 * routeUHardEdgeMesh r *
            (SchwartzMap.compactSupportApproximation n (routeURealEvenAmplitude g)
              (routeUHardEdgeMesh r * (j + 1 : ℝ))).re) *
          Polynomial.Chebyshev.T ℝ ((j + 1 : ℕ) : ℤ)).natDegree ≤
          (Polynomial.Chebyshev.T ℝ ((j + 1 : ℕ) : ℤ)).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
      _ = j + 1 := by
        simp only [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast]
      _ ≤ N := Finset.mem_range.mp hj

/-- Explicit packet used by the cofinal quantitative criterion. -/
def routeUExplicitFiniteChebyshevPacket
    (n k : ℕ) (g : SchwartzMap ℝ ℝ) : Polynomial ℝ :=
  routeUFiniteChebyshevPacketPolynomial n g (k : ℝ)
    (routeUExplicitFiniteChebyshevCutoff n k)

/-- Exact coefficient-vector size of the reciprocal pullback of the explicit packet. -/
def routeUExplicitFiniteHankelSize
    (n k : ℕ) (g : SchwartzMap ℝ ℝ) : ℕ :=
  xiHardEdgeLiftSize (routeUHardEdgeMass (k : ℝ))
    (routeUExplicitFiniteChebyshevPacket n k g)

/-- Reciprocal pullback enlarges the explicit truncation by at most one coefficient. -/
theorem routeUExplicitFiniteHankelSize_le_linear
    (n k : ℕ) (g : SchwartzMap ℝ ℝ) :
    routeUExplicitFiniteHankelSize n k g ≤ (n + 1) * (k + 1) + 2 := by
  calc
    routeUExplicitFiniteHankelSize n k g ≤
        (routeUExplicitFiniteChebyshevPacket n k g).natDegree + 1 :=
      xiHardEdgeLiftSize_le_natDegree_add_one _ _
    _ ≤ routeUExplicitFiniteChebyshevCutoff n k + 1 :=
      Nat.add_le_add_right
        (natDegree_routeUFiniteChebyshevPacketPolynomial_le n g (k : ℝ)
          (routeUExplicitFiniteChebyshevCutoff n k)) 1
    _ = (n + 1) * (k + 1) + 2 := by
      simp only [routeUExplicitFiniteChebyshevCutoff]

/-- Exact shifted-Hankel quadratic associated to the explicit cofinal packet. -/
def routeUExplicitPolynomialGaussianFiniteHankelQuadratic
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (n k : ℕ) : ℝ :=
  routeUPolynomialGaussianFiniteHankelQuadratic P t n k
    (routeUExplicitFiniteChebyshevCutoff n k)

/-- The existential finite-lattice witness upgrades to the explicit linear truncation. -/
theorem routeUExplicitFiniteHankelQuadratic_eq_sampleDivisorSum
    (n k : ℕ) (g : SchwartzMap ℝ ℝ) :
    routeUHardEdgeMass (k : ℝ) ^ 2 *
        xiShiftedReciprocalHankelQuadratic
          (routeUHardEdgeMass (k : ℝ) ^ 2)
          (xiHardEdgeLiftCoefficients (routeUHardEdgeMass (k : ℝ))
            (routeUExplicitFiniteChebyshevPacket n k g)) =
      (∑' q : XiZeroCopy,
        routeUXiComplexHardEdgeSampleDivisorTerm n (routeURealEvenAmplitude g)
          (k : ℝ) q).re := by
  exact routeUFiniteHankelQuadratic_eq_sampleDivisorSum n g (k : ℝ)
    (routeUExplicitFiniteChebyshevCutoff n k)
    (fun j hj =>
      routeURealEvenCompactApproximation_eq_zero_of_explicitCutoff n k j g hj)

/-- A negative explicit packet must lie strictly below the universal parabolic dimension
horizon. -/
theorem routeUHardEdgeMass_sq_lt_parabolic_size_sq_of_explicitQuadratic_neg
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (n k : ℕ)
    (hneg : routeUExplicitPolynomialGaussianFiniteHankelQuadratic P t n k < 0) :
    routeUHardEdgeMass (k : ℝ) ^ 2 <
      routeUParabolicDegreeHorizon *
        (routeUExplicitFiniteHankelSize n k (routeUXiHeatPhysicalReal P t) : ℝ) ^ 2 := by
  let g : SchwartzMap ℝ ℝ := routeUXiHeatPhysicalReal P t
  let packet : Polynomial ℝ := routeUExplicitFiniteChebyshevPacket n k g
  let a : ℝ := routeUHardEdgeMass (k : ℝ)
  let d : ℕ := (xiHardEdgeReciprocalPolynomial a packet).natDegree
  let c : Fin (d + 1) → ℝ := xiHardEdgeLiftCoefficients a packet
  have hquad : xiShiftedReciprocalHankelQuadratic (a ^ 2) c < 0 := by
    simpa only [routeUExplicitPolynomialGaussianFiniteHankelQuadratic,
      routeUPolynomialGaussianFiniteHankelQuadratic, g, packet, a, d, c,
      routeUExplicitFiniteChebyshevPacket, routeUExplicitFiniteHankelSize,
      xiHardEdgeLiftSize] using hneg
  have hc : c ≠ 0 := by
    intro hc0
    rw [hc0] at hquad
    have hfalse : (0 : ℝ) < 0 := by
      simpa only [xiShiftedReciprocalHankelQuadratic, Pi.zero_apply, zero_mul,
        Finset.sum_const_zero] using hquad
    exact (lt_irrefl 0) hfalse
  by_contra hnot
  have hy : routeUParabolicDegreeHorizon * (((d + 1 : ℕ) : ℝ)) ^ 2 ≤ a ^ 2 := by
    simpa only [g, packet, a, d, routeUExplicitFiniteHankelSize,
      xiHardEdgeLiftSize] using le_of_not_gt hnot
  have hpos := xiShiftedReciprocalHankelQuadratic_pos_of_parabolic d c hc hy
  exact (not_lt_of_ge hpos.le) hquad

/-- Closed false-RH phase with cofinal negative packets and two-sided hard-edge dimension
control. -/
def XiShiftedHardEdgeCofinalLinearNegativePhase : Prop :=
  ∃ (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (n K : ℕ),
    ∀ k : ℕ, K ≤ k →
      routeUExplicitPolynomialGaussianFiniteHankelQuadratic P t n k < 0 ∧
      routeUHardEdgeMass (k : ℝ) ^ 2 <
        routeUParabolicDegreeHorizon *
          (routeUExplicitFiniteHankelSize n k (routeUXiHeatPhysicalReal P t) : ℝ) ^ 2 ∧
      routeUExplicitFiniteHankelSize n k (routeUXiHeatPhysicalReal P t) ≤
        (n + 1) * (k + 1) + 2

/-- Failure of RH gives one polynomial--Gaussian carrier whose explicit finite Hankel packets are
negative at every sufficiently large integral hard-edge mass, with dimension trapped between the
parabolic lower scale and an explicit linear upper scale. -/
theorem xiShiftedHardEdgeCofinalLinearNegativePhase_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    XiShiftedHardEdgeCofinalLinearNegativePhase := by
  have hnot : ¬ ∀ (P : Polynomial ℝ) (t : ℝ), 0 < t →
      0 ≤ xiPolynomialGaussianHeatTraceReal P t := by
    intro hall
    exact hRH
      (riemannHypothesis_iff_forall_xiPolynomialGaussianHeatTraceReal_nonneg.mpr hall)
  push Not at hnot
  obtain ⟨P, τ, hτ, htraceNeg⟩ := hnot
  let t : {τ : ℝ // 0 < τ} := ⟨τ, hτ⟩
  have hcutLim := tendsto_routeUXiPolynomialGaussianCutoffDivisorTrace P t
  have hcutRe : Tendsto (fun n : ℕ =>
      (∑' q : XiZeroCopy,
        routeUComplexPositiveFourierExtension n
          (routeUXiHeatPhysicalComplex P t) (xiSpectralPoint q) ^ 2).re)
      atTop (nhds (xiPolynomialGaussianHeatTraceReal P τ)) := by
    have h := (Complex.reCLM.continuous.tendsto
      (xiPolynomialGaussianHeatTrace P τ)).comp hcutLim
    have hfun :
        ((Complex.reCLM : ℂ → ℝ) ∘ fun n : ℕ =>
          ∑' q : XiZeroCopy,
            routeUComplexPositiveFourierExtension n
              (routeUXiHeatPhysicalComplex P t) (xiSpectralPoint q) ^ 2) =
        fun n : ℕ =>
          (∑' q : XiZeroCopy,
            routeUComplexPositiveFourierExtension n
              (routeUXiHeatPhysicalComplex P t) (xiSpectralPoint q) ^ 2).re := by
      funext n
      exact Complex.reCLM_apply _
    rw [hfun] at h
    have hreval : (Complex.reCLM : ℂ → ℝ)
        (xiPolynomialGaussianHeatTrace P τ) =
          (xiPolynomialGaussianHeatTrace P τ).re := Complex.reCLM_apply _
    rw [hreval] at h
    simpa only [xiPolynomialGaussianHeatTraceReal] using h
  have hcutEventually : ∀ᶠ n : ℕ in atTop,
      (∑' q : XiZeroCopy,
        routeUComplexPositiveFourierExtension n
          (routeUXiHeatPhysicalComplex P t) (xiSpectralPoint q) ^ 2).re < 0 :=
    hcutRe.eventually (Iio_mem_nhds htraceNeg)
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 hcutEventually
  have hcutNeg := hn n le_rfl
  let g : SchwartzMap ℝ ℝ := routeUXiHeatPhysicalReal P t
  have hhardLim :=
    tendsto_tsum_routeUXiComplexHardEdgeSampleDivisorTerm_natCast n
      (routeURealEvenAmplitude g)
  have htarget :
      (∑' q : XiZeroCopy,
        routeUComplexPositiveFourierExtension n (routeURealEvenAmplitude g)
          (xiSpectralPoint q) ^ 2) =
      ∑' q : XiZeroCopy,
        routeUComplexPositiveFourierExtension n
          (routeUXiHeatPhysicalComplex P t) (xiSpectralPoint q) ^ 2 := by
    rw [show routeURealEvenAmplitude g = routeUXiHeatPhysicalComplex P t by
      exact routeURealEvenAmplitude_heatPhysical_eq P t]
  have hhardRe : Tendsto (fun k : ℕ =>
      (∑' q : XiZeroCopy,
        routeUXiComplexHardEdgeSampleDivisorTerm n
          (routeURealEvenAmplitude g) (k : ℝ) q).re)
      atTop
      (nhds ((∑' q : XiZeroCopy,
        routeUComplexPositiveFourierExtension n
          (routeUXiHeatPhysicalComplex P t) (xiSpectralPoint q) ^ 2).re)) := by
    rw [← htarget]
    have h := (Complex.reCLM.continuous.tendsto _).comp hhardLim
    have hfun :
        ((Complex.reCLM : ℂ → ℝ) ∘ fun k : ℕ =>
          ∑' q : XiZeroCopy,
            routeUXiComplexHardEdgeSampleDivisorTerm n
              (routeURealEvenAmplitude g) (k : ℝ) q) =
        fun k : ℕ =>
          (∑' q : XiZeroCopy,
            routeUXiComplexHardEdgeSampleDivisorTerm n
              (routeURealEvenAmplitude g) (k : ℝ) q).re := by
      funext k
      exact Complex.reCLM_apply _
    rw [hfun] at h
    exact h
  have hhardEventually : ∀ᶠ k : ℕ in atTop,
      (∑' q : XiZeroCopy,
        routeUXiComplexHardEdgeSampleDivisorTerm n
          (routeURealEvenAmplitude g) (k : ℝ) q).re < 0 :=
    hhardRe.eventually (Iio_mem_nhds hcutNeg)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hhardEventually
  refine ⟨P, t, n, K, fun k hk => ?_⟩
  have hsampleNeg := hK k hk
  have hquadEq := routeUExplicitFiniteHankelQuadratic_eq_sampleDivisorSum n k g
  have hmass : 0 < routeUHardEdgeMass (k : ℝ) ^ 2 :=
    sq_pos_of_pos (routeUHardEdgeMass_pos (k : ℝ))
  have hquadNeg :
      routeUExplicitPolynomialGaussianFiniteHankelQuadratic P t n k < 0 := by
    change xiShiftedReciprocalHankelQuadratic
      (routeUHardEdgeMass (k : ℝ) ^ 2)
      (xiHardEdgeLiftCoefficients (routeUHardEdgeMass (k : ℝ))
        (routeUFiniteChebyshevPacketPolynomial n
          (routeUXiHeatPhysicalReal P t) (k : ℝ)
          (routeUExplicitFiniteChebyshevCutoff n k))) < 0
    dsimp only [g, routeUExplicitFiniteChebyshevPacket] at hquadEq
    nlinarith
  exact ⟨hquadNeg,
    routeUHardEdgeMass_sq_lt_parabolic_size_sq_of_explicitQuadratic_neg
      P t n k hquadNeg,
    routeUExplicitFiniteHankelSize_le_linear n k (routeUXiHeatPhysicalReal P t)⟩

/-- **Closed quantitative hard-edge criterion.**  False RH is exactly the existence of one
cofinal explicit negative finite-Hankel family whose dimension is trapped on the square-root shift
scale. -/
theorem not_rh_iff_xiShiftedHardEdgeCofinalLinearNegativePhase :
    ¬ RiemannHypothesis ↔ XiShiftedHardEdgeCofinalLinearNegativePhase := by
  constructor
  · exact xiShiftedHardEdgeCofinalLinearNegativePhase_of_not_rh
  · rintro ⟨P, t, n, K, hphase⟩
    have hneg := (hphase K le_rfl).1
    apply not_rh_iff_exists_negative_routeUPolynomialGaussianFiniteHankelQuadratic.mpr
    exact ⟨P, t, n, K, routeUExplicitFiniteChebyshevCutoff n K, hneg⟩

/-- Premise-free phase dichotomy. -/
theorem riemannHypothesis_or_xiShiftedHardEdgeCofinalLinearNegativePhase :
    RiemannHypothesis ∨ XiShiftedHardEdgeCofinalLinearNegativePhase := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · exact Or.inr (xiShiftedHardEdgeCofinalLinearNegativePhase_of_not_rh hRH)

end RHTower
