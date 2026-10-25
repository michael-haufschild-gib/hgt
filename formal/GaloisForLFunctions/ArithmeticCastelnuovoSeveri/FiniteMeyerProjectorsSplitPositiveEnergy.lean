import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PositiveMeyerDegreesSeeReducedCriticalJets
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeyerCriticalTopAlgebra
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeyerFiniteProjectorAlgebra

/-!
# Exact finite critical projection of positive Meyer energy

Actual causal projectors cut out complete local jet blocks. They are central
multipliers of the genuine convolution algebra and commute with arithmetic sharp
on critical packets. Every positive Hermitian degree therefore splits into the
selected finite energy and a nonnegative complementary energy, without continuity.
The supremum of finite projected energies is finite and leaves a nonnegative
residual in the full energy.
-/

noncomputable section
open Complex RHTower
open scoped ComplexConjugate
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

private theorem cohomologySharp_jet (u : DeningerMeyerStrongLogCohomology)
    (rho : XiDivisorSupport) (j : DeningerArithmeticJetIndex rho) :
    deningerMeyerXiSupportJetEvaluationLM rho j (meyerCohomologySharp u) =
      (-1 : ℂ) ^ j.val * star (deningerMeyerXiSupportJetEvaluationLM (meyerLineReflect rho)
        ⟨j.val, by rw [meyerLineReflect_multiplicity]; exact j.isLt⟩ u) := by
  induction u using Submodule.Quotient.induction_on with
  | H g =>
    rw [meyerCohomologySharp_mk, deningerMeyerXiSupportJetEvaluationLM_mk,
      deningerMeyerXiSupportJetEvaluationLM_mk]
    exact meyerSourceSharp_jet g j.val rho

private theorem cohomology_jet_congr {rho sigma : XiDivisorSupport} (h : rho = sigma)
    (j : DeningerArithmeticJetIndex rho) (k : DeningerArithmeticJetIndex sigma)
    (hj : j.val = k.val) (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerXiSupportJetEvaluationLM rho j u =
      deningerMeyerXiSupportJetEvaluationLM sigma k u := by
  subst sigma
  exact congrArg (fun i => deningerMeyerXiSupportJetEvaluationLM rho i u) (Fin.ext hj)

private theorem cohomologySharp_fixed_jet (u : DeningerMeyerStrongLogCohomology)
    (rho : XiDivisorSupport) (hfix : meyerLineReflect rho = rho)
    (j : DeningerArithmeticJetIndex rho) :
    deningerMeyerXiSupportJetEvaluationLM rho j (meyerCohomologySharp u) =
      (-1 : ℂ) ^ j.val * star (deningerMeyerXiSupportJetEvaluationLM rho j u) := by
  rw [cohomologySharp_jet, cohomology_jet_congr hfix _ j rfl u]

/-- On a finite critical packet the actual causal projector commutes with arithmetic sharp. -/
theorem meyerFiniteCriticalProjector_sharp (S : Finset XiDivisorSupport)
    (hcrit : ∀ rho ∈ S, (rho : ℂ).re = 1 / 2)
    (u : DeningerMeyerStrongLogCohomology) :
    meyerCohomologySharp (deningerMeyerFiniteXiCausalProjector S u) =
      deningerMeyerFiniteXiCausalProjector S (meyerCohomologySharp u) := by
  classical
  apply deningerMeyerCohomology_eq_of_XiJets_eq
  intro rho j
  by_cases hr : rho ∈ S
  · have hfix := meyerLineReflect_eq_self_of_critical rho (hcrit rho hr)
    rw [cohomologySharp_fixed_jet _ rho hfix, meyerFiniteXiCausalProjector_jet,
      if_pos hr, meyerFiniteXiCausalProjector_jet, if_pos hr,
      cohomologySharp_fixed_jet _ rho hfix]
  · have href : meyerLineReflect rho ∉ S := by
      intro he
      have hfix := meyerLineReflect_eq_self_of_critical (meyerLineReflect rho)
        (hcrit (meyerLineReflect rho) he)
      rw [meyerLineReflect_sq] at hfix
      exact hr (hfix.symm ▸ he)
    rw [cohomologySharp_jet, meyerFiniteXiCausalProjector_jet, if_neg href,
      star_zero, mul_zero, meyerFiniteXiCausalProjector_jet, if_neg hr]

/-- Selected and complementary critical source blocks have genuinely zero mixed sharp product. -/
theorem meyerFiniteCriticalProjector_complement_product_zero (S : Finset XiDivisorSupport)
    (hcrit : ∀ rho ∈ S, (rho : ℂ).re = 1 / 2)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerCohomologyConvolution (deningerMeyerFiniteXiCausalProjector S u)
      (meyerCohomologySharp (u - deningerMeyerFiniteXiCausalProjector S u)) = 0 := by
  have hz : deningerMeyerFiniteXiCausalProjector S
      (u - deningerMeyerFiniteXiCausalProjector S u) = 0 := by
    rw [map_sub, deningerMeyerFiniteXiCausalProjector_idempotent, sub_self]
  rw [meyerFiniteXiCausalProjector_mul_left,
    ← meyerFiniteXiCausalProjector_mul_right,
    ← meyerFiniteCriticalProjector_sharp S hcrit, hz, map_zero, map_zero]

/-- A critical packet splits the actual sharp square in genuine cohomology. -/
theorem meyerFiniteCriticalProjector_square_decomposition (S : Finset XiDivisorSupport)
    (hcrit : ∀ rho ∈ S, (rho : ℂ).re = 1 / 2)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerCohomologyConvolution u (meyerCohomologySharp u) =
      deningerMeyerCohomologyConvolution (deningerMeyerFiniteXiCausalProjector S u)
        (meyerCohomologySharp (deningerMeyerFiniteXiCausalProjector S u)) +
      deningerMeyerCohomologyConvolution (u - deningerMeyerFiniteXiCausalProjector S u)
        (meyerCohomologySharp (u - deningerMeyerFiniteXiCausalProjector S u)) := by
  let p := deningerMeyerFiniteXiCausalProjector S u
  let r := u - p
  have hpr : deningerMeyerCohomologyConvolution p (meyerCohomologySharp r) = 0 :=
    meyerFiniteCriticalProjector_complement_product_zero S hcrit u
  have hrp : deningerMeyerCohomologyConvolution r (meyerCohomologySharp p) = 0 := by
    have he := congrArg meyerCohomologySharp hpr
    rw [meyerCohomologySharp_convolution, meyerCohomologySharp_sq, map_zero,
      deningerMeyerCohomologyConvolution_comm] at he
    exact he
  have hu : u = p + r := by dsimp only [r]; abel
  calc
    deningerMeyerCohomologyConvolution u (meyerCohomologySharp u) =
        deningerMeyerCohomologyConvolution (p + r) (meyerCohomologySharp (p + r)) := by
      rw [← hu]
    _ = _ := by
      simp only [map_add, LinearMap.add_apply, hpr, hrp, add_zero, zero_add]

/-- Every Hermitian degree has an exact orthogonal finite-packet energy decomposition. -/
theorem meyerFiniteCriticalProjector_degree_decomposition
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hd : ∀ u, d (meyerCohomologySharp u) = conj (d u))
    (S : Finset XiDivisorSupport) (hcrit : ∀ rho ∈ S, (rho : ℂ).re = 1 / 2)
    (u : DeningerMeyerStrongLogCohomology) :
    meyerDegreePair d u u =
      meyerDegreePair d (deningerMeyerFiniteXiCausalProjector S u)
        (deningerMeyerFiniteXiCausalProjector S u) +
      meyerDegreePair d (u - deningerMeyerFiniteXiCausalProjector S u)
        (u - deningerMeyerFiniteXiCausalProjector S u) := by
  let p := deningerMeyerFiniteXiCausalProjector S u
  let r := u - p
  have hpr : meyerDegreePair d p r = 0 := by
    rw [meyerDegreePair, meyerFiniteCriticalProjector_complement_product_zero S hcrit u, map_zero]
  have hrp : meyerDegreePair d r p = 0 := by
    rw [meyerDegreePair_conj_symm d hd, hpr, map_zero]
  have hu : u = p + r := by dsimp only [r]; abel
  calc
    meyerDegreePair d u u = meyerDegreePair d (p + r) (p + r) := by rw [← hu]
    _ = _ := by
      rw [meyerDegreePair_add_left, meyerDegreePair_add_right, meyerDegreePair_add_right,
        hpr, hrp, add_zero, zero_add]

/-- A positive Hermitian degree bounds every finite critical square-energy projection. -/
theorem meyerFiniteCriticalProjector_degree_le
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hd : ∀ u, d (meyerCohomologySharp u) = conj (d u))
    (hpos : ∀ u, 0 ≤ (meyerDegreePair d u u).re)
    (S : Finset XiDivisorSupport) (hcrit : ∀ rho ∈ S, (rho : ℂ).re = 1 / 2)
    (u : DeningerMeyerStrongLogCohomology) :
    (meyerDegreePair d (deningerMeyerFiniteXiCausalProjector S u)
      (deningerMeyerFiniteXiCausalProjector S u)).re ≤ (meyerDegreePair d u u).re := by
  have he := congrArg Complex.re (meyerFiniteCriticalProjector_degree_decomposition d hd S hcrit u)
  rw [Complex.add_re] at he
  linarith only [he, hpos (u - deningerMeyerFiniteXiCausalProjector S u)]

/-- Saturation of the finite energy bound is exactly a null complementary square. -/
theorem meyerFiniteCriticalProjector_degree_eq_iff
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hd : ∀ u, d (meyerCohomologySharp u) = conj (d u))
    (S : Finset XiDivisorSupport) (hcrit : ∀ rho ∈ S, (rho : ℂ).re = 1 / 2)
    (u : DeningerMeyerStrongLogCohomology) :
    (meyerDegreePair d (deningerMeyerFiniteXiCausalProjector S u)
      (deningerMeyerFiniteXiCausalProjector S u)).re = (meyerDegreePair d u u).re ↔
      (meyerDegreePair d (u - deningerMeyerFiniteXiCausalProjector S u)
        (u - deningerMeyerFiniteXiCausalProjector S u)).re = 0 := by
  have he := congrArg Complex.re (meyerFiniteCriticalProjector_degree_decomposition d hd S hcrit u)
  rw [Complex.add_re] at he
  constructor <;> intro h <;> linarith only [he, h]


/-- The selected sharp square is the projection of the original actual square. -/
theorem meyerFiniteCriticalProjector_square (S : Finset XiDivisorSupport)
    (hcrit : ∀ rho ∈ S, (rho : ℂ).re = 1 / 2)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerCohomologyConvolution (deningerMeyerFiniteXiCausalProjector S u)
      (meyerCohomologySharp (deningerMeyerFiniteXiCausalProjector S u)) =
      deningerMeyerFiniteXiCausalProjector S
        (deningerMeyerCohomologyConvolution u (meyerCohomologySharp u)) := by
  rw [meyerFiniteCriticalProjector_sharp S hcrit,
    meyerFiniteXiCausalProjector_mul_right, meyerFiniteXiCausalProjector_mul_left,
    deningerMeyerFiniteXiCausalProjector_idempotent]

private theorem point_degree_cohomology_square (rho : XiDivisorSupport)
    (hr : (rho : ℂ).re = 1 / 2) (u : DeningerMeyerStrongLogCohomology) :
    meyerPointDegree rho (deningerMeyerCohomologyConvolution u (meyerCohomologySharp u)) =
      (Complex.normSq (meyerPointDegree rho u) : ℂ) := by
  induction u using Submodule.Quotient.induction_on with
  | H g =>
    rw [meyerCohomologySharp_mk, deningerMeyerCohomologyConvolution_mk,
      meyerPointDegree_sharp_square rho hr, meyerPointDegree_mk]

/-- The finite projected energy has precisely the critical zeroth-value weights. -/
theorem meyerFiniteCriticalProjector_degree_formula
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hd : ∀ u, d (meyerCohomologySharp u) = conj (d u))
    (hpos : ∀ u, 0 ≤ (meyerDegreePair d u u).re)
    (S : Finset XiDivisorSupport) (hcrit : ∀ rho ∈ S, (rho : ℂ).re = 1 / 2)
    (u : DeningerMeyerStrongLogCohomology) :
    (meyerDegreePair d (deningerMeyerFiniteXiCausalProjector S u)
      (deningerMeyerFiniteXiCausalProjector S u)).re =
      ∑ q : DeningerMeyerFiniteXiJetSlot S,
        if q.2.val = 0 then
          (d (meyerHasseJetClass q.1.1 q.2)).re * Complex.normSq (meyerPointDegree q.1.1 u)
        else 0 := by
  classical
  rw [meyerDegreePair, meyerFiniteCriticalProjector_square S hcrit]
  change (d (deningerMeyerFiniteXiCausalSection S
    (deningerMeyerFiniteXiJetPacketLM S
      (deningerMeyerCohomologyConvolution u (meyerCohomologySharp u))))).re = _
  rw [meyerPositiveDegree_finite_causal_formula d hd hpos, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro q _
  have hfix := meyerLineReflect_eq_self_of_critical q.1.1 (hcrit q.1.1 q.1.2)
  by_cases hj : q.2.val = 0
  · rw [if_pos ⟨hfix, hj⟩, if_pos hj]
    have hq : q.2 = ⟨0, xiSupportMultiplicity_pos q.1.1⟩ := Fin.ext hj
    have hval : deningerMeyerFiniteXiJetPacketLM S
        (deningerMeyerCohomologyConvolution u (meyerCohomologySharp u)) q =
          (Complex.normSq (meyerPointDegree q.1.1 u) : ℂ) := by
      rw [deningerMeyerFiniteXiJetPacketLM_apply, hq]
      exact point_degree_cohomology_square q.1.1 (hcrit q.1.1 q.1.2) u
    rw [hval, Complex.re_ofReal_mul, Complex.ofReal_re, mul_comm]
  · rw [if_neg (fun h => hj h.2), if_neg hj, Complex.zero_re]

/-- Every finite critical weighted-value energy is bounded by the full actual source square. -/
theorem meyerFiniteCriticalWeightedEnergy_le
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hd : ∀ u, d (meyerCohomologySharp u) = conj (d u))
    (hpos : ∀ u, 0 ≤ (meyerDegreePair d u u).re)
    (S : Finset XiDivisorSupport) (hcrit : ∀ rho ∈ S, (rho : ℂ).re = 1 / 2)
    (u : DeningerMeyerStrongLogCohomology) :
    (∑ q : DeningerMeyerFiniteXiJetSlot S,
      if q.2.val = 0 then
        (d (meyerHasseJetClass q.1.1 q.2)).re * Complex.normSq (meyerPointDegree q.1.1 u)
      else 0) ≤ (meyerDegreePair d u u).re := by
  rw [← meyerFiniteCriticalProjector_degree_formula d hd hpos S hcrit u]
  exact meyerFiniteCriticalProjector_degree_le d hd hpos S hcrit u

/-- Finite projection evaluates every positive degree through its critical value weights. -/
theorem meyerPositiveDegree_projector_formula
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hd : ∀ u, d (meyerCohomologySharp u) = conj (d u))
    (hpos : ∀ u, 0 ≤ (meyerDegreePair d u u).re)
    (S : Finset XiDivisorSupport) (u : DeningerMeyerStrongLogCohomology) :
    d (deningerMeyerFiniteXiCausalProjector S u) =
      ∑ q : DeningerMeyerFiniteXiJetSlot S,
        if meyerLineReflect q.1.1 = q.1.1 ∧ q.2.val = 0 then
          deningerMeyerXiSupportJetEvaluationLM q.1.1 q.2 u *
            ((d (meyerHasseJetClass q.1.1 q.2)).re : ℂ) else 0 := by
  change d (deningerMeyerFiniteXiCausalSection S (deningerMeyerFiniteXiJetPacketLM S u)) = _
  rw [meyerPositiveDegree_finite_causal_formula d hd hpos]
  simp only [deningerMeyerFiniteXiJetPacketLM_apply]

private theorem point_degree_projector (S : Finset XiDivisorSupport)
    (rho : XiDivisorSupport) (u : DeningerMeyerStrongLogCohomology) :
    meyerPointDegree rho (deningerMeyerFiniteXiCausalProjector S u) =
      if rho ∈ S then meyerPointDegree rho u else 0 :=
  meyerFiniteXiCausalProjector_jet S u rho ⟨0, xiSupportMultiplicity_pos rho⟩

private theorem point_degree_sharp_fixed (rho : XiDivisorSupport)
    (hr : meyerLineReflect rho = rho) (u : DeningerMeyerStrongLogCohomology) :
    meyerPointDegree rho (meyerCohomologySharp u) = conj (meyerPointDegree rho u) := by
  change deningerMeyerXiSupportJetEvaluationLM rho ⟨0, xiSupportMultiplicity_pos rho⟩
    (meyerCohomologySharp u) = _
  rw [cohomologySharp_fixed_jet _ rho hr, pow_zero, one_mul]
  rfl

private theorem positive_degree_zero_on_finite_range
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hd : ∀ u, d (meyerCohomologySharp u) = conj (d u))
    (hpos : ∀ u, 0 ≤ (meyerDegreePair d u u).re)
    (S : Finset XiDivisorSupport) (u : DeningerMeyerStrongLogCohomology)
    (hP : deningerMeyerFiniteXiCausalProjector S u = u)
    (hz : ∀ rho ∈ S, meyerLineReflect rho = rho → meyerPointDegree rho u = 0) : d u = 0 := by
  classical
  rw [← hP, meyerPositiveDegree_projector_formula d hd hpos]
  apply Finset.sum_eq_zero
  intro q _
  split_ifs with h
  · have hq : q.2 = ⟨0, xiSupportMultiplicity_pos q.1.1⟩ := Fin.ext h.2
    rw [hq]
    change meyerPointDegree q.1.1 u * _ = 0
    rw [hz q.1.1 q.1.2 h.1, zero_mul]
  · rfl

/-- Every finite packet has zero mixed degree against its complement for a positive degree. -/
theorem meyerFiniteProjector_positive_cross_degree_zero
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hd : ∀ u, d (meyerCohomologySharp u) = conj (d u))
    (hpos : ∀ u, 0 ≤ (meyerDegreePair d u u).re)
    (S : Finset XiDivisorSupport) (u : DeningerMeyerStrongLogCohomology) :
    meyerDegreePair d (deningerMeyerFiniteXiCausalProjector S u)
      (u - deningerMeyerFiniteXiCausalProjector S u) = 0 := by
  unfold meyerDegreePair
  apply positive_degree_zero_on_finite_range d hd hpos S
  · rw [← meyerFiniteXiCausalProjector_mul_left,
      deningerMeyerFiniteXiCausalProjector_idempotent]
  · intro rho hr hfix
    simp only [meyerPointDegree_product, point_degree_sharp_fixed rho hfix,
      map_sub, point_degree_projector, if_pos hr, sub_self, map_zero, mul_zero]

/-- Positive degree energy splits along every finite packet, including off-line blocks. -/
theorem meyerFiniteProjector_positive_degree_decomposition
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hd : ∀ u, d (meyerCohomologySharp u) = conj (d u))
    (hpos : ∀ u, 0 ≤ (meyerDegreePair d u u).re)
    (S : Finset XiDivisorSupport) (u : DeningerMeyerStrongLogCohomology) :
    meyerDegreePair d u u =
      meyerDegreePair d (deningerMeyerFiniteXiCausalProjector S u)
        (deningerMeyerFiniteXiCausalProjector S u) +
      meyerDegreePair d (u - deningerMeyerFiniteXiCausalProjector S u)
        (u - deningerMeyerFiniteXiCausalProjector S u) := by
  let p := deningerMeyerFiniteXiCausalProjector S u
  let r := u - p
  have hpr : meyerDegreePair d p r = 0 :=
    meyerFiniteProjector_positive_cross_degree_zero d hd hpos S u
  have hrp : meyerDegreePair d r p = 0 := by
    rw [meyerDegreePair_conj_symm d hd, hpr, map_zero]
  have hu : u = p + r := by dsimp only [r]; abel
  calc
    meyerDegreePair d u u = meyerDegreePair d (p + r) (p + r) := by rw [← hu]
    _ = _ := by
      rw [meyerDegreePair_add_left, meyerDegreePair_add_right, meyerDegreePair_add_right,
        hpr, hrp, add_zero, zero_add]

/-- The finite positive energy keeps precisely the selected critical zeroth values. -/
theorem meyerFiniteProjector_positive_degree_formula
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hd : ∀ u, d (meyerCohomologySharp u) = conj (d u))
    (hpos : ∀ u, 0 ≤ (meyerDegreePair d u u).re)
    (S : Finset XiDivisorSupport) (u : DeningerMeyerStrongLogCohomology) :
    (meyerDegreePair d (deningerMeyerFiniteXiCausalProjector S u)
      (deningerMeyerFiniteXiCausalProjector S u)).re =
      ∑ q : DeningerMeyerFiniteXiJetSlot S,
        if meyerLineReflect q.1.1 = q.1.1 ∧ q.2.val = 0 then
          (d (meyerHasseJetClass q.1.1 q.2)).re * Complex.normSq (meyerPointDegree q.1.1 u)
        else 0 := by
  classical
  let v := deningerMeyerCohomologyConvolution (deningerMeyerFiniteXiCausalProjector S u)
    (meyerCohomologySharp (deningerMeyerFiniteXiCausalProjector S u))
  have hP : deningerMeyerFiniteXiCausalProjector S v = v := by
    dsimp only [v]
    rw [← meyerFiniteXiCausalProjector_mul_left,
      deningerMeyerFiniteXiCausalProjector_idempotent]
  change (d v).re = _
  rw [← hP, meyerPositiveDegree_projector_formula d hd hpos, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro q _
  split_ifs with h
  · have hq : q.2 = ⟨0, xiSupportMultiplicity_pos q.1.1⟩ := Fin.ext h.2
    have hv : deningerMeyerXiSupportJetEvaluationLM q.1.1 q.2 v =
        (Complex.normSq (meyerPointDegree q.1.1 u) : ℂ) := by
      rw [hq]
      change meyerPointDegree q.1.1
        (deningerMeyerCohomologyConvolution (deningerMeyerFiniteXiCausalProjector S u)
          (meyerCohomologySharp (deningerMeyerFiniteXiCausalProjector S u))) = _
      rw [meyerPointDegree_product, point_degree_sharp_fixed q.1.1 h.1]
      simp only [point_degree_projector, if_pos q.1.2]
      exact Complex.mul_conj _
    rw [hv, Complex.re_ofReal_mul, Complex.ofReal_re, mul_comm]
  · rfl

/-- Every finite positive projection is bounded by the full source energy. -/
theorem meyerFiniteProjector_positive_degree_le
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hd : ∀ u, d (meyerCohomologySharp u) = conj (d u))
    (hpos : ∀ u, 0 ≤ (meyerDegreePair d u u).re)
    (S : Finset XiDivisorSupport) (u : DeningerMeyerStrongLogCohomology) :
    (meyerDegreePair d (deningerMeyerFiniteXiCausalProjector S u)
      (deningerMeyerFiniteXiCausalProjector S u)).re ≤ (meyerDegreePair d u u).re := by
  have he := congrArg Complex.re (meyerFiniteProjector_positive_degree_decomposition d hd hpos S u)
  rw [Complex.add_re] at he
  linarith only [he, hpos (u - deningerMeyerFiniteXiCausalProjector S u)]

/-- Equality in a finite projection bound is exactly zero complementary square energy. -/
theorem meyerFiniteProjector_positive_degree_eq_iff
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hd : ∀ u, d (meyerCohomologySharp u) = conj (d u))
    (hpos : ∀ u, 0 ≤ (meyerDegreePair d u u).re)
    (S : Finset XiDivisorSupport) (u : DeningerMeyerStrongLogCohomology) :
    (meyerDegreePair d (deningerMeyerFiniteXiCausalProjector S u)
      (deningerMeyerFiniteXiCausalProjector S u)).re = (meyerDegreePair d u u).re ↔
      (meyerDegreePair d (u - deningerMeyerFiniteXiCausalProjector S u)
        (u - deningerMeyerFiniteXiCausalProjector S u)).re = 0 := by
  have he := congrArg Complex.re (meyerFiniteProjector_positive_degree_decomposition d hd hpos S u)
  rw [Complex.add_re] at he
  constructor <;> intro h <;> linarith only [he, h]

/-- The regular energy recovered from all finite causal projections. -/
def meyerDegreeRegularEnergy (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (u : DeningerMeyerStrongLogCohomology) : ℝ :=
  sSup (Set.range fun S : Finset XiDivisorSupport =>
    (meyerDegreePair d (deningerMeyerFiniteXiCausalProjector S u)
      (deningerMeyerFiniteXiCausalProjector S u)).re)

/-- Positive finite energies have a genuine supremum between zero and the full energy. -/
theorem meyerPositiveDegree_regular_energy_bounds
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hd : ∀ u, d (meyerCohomologySharp u) = conj (d u))
    (hpos : ∀ u, 0 ≤ (meyerDegreePair d u u).re)
    (u : DeningerMeyerStrongLogCohomology) :
    (∀ S : Finset XiDivisorSupport,
      (meyerDegreePair d (deningerMeyerFiniteXiCausalProjector S u)
        (deningerMeyerFiniteXiCausalProjector S u)).re ≤ meyerDegreeRegularEnergy d u) ∧
      0 ≤ meyerDegreeRegularEnergy d u ∧
      meyerDegreeRegularEnergy d u ≤ (meyerDegreePair d u u).re := by
  have hb : BddAbove (Set.range fun S : Finset XiDivisorSupport =>
      (meyerDegreePair d (deningerMeyerFiniteXiCausalProjector S u)
        (deningerMeyerFiniteXiCausalProjector S u)).re) := by
    refine ⟨(meyerDegreePair d u u).re, ?_⟩
    rintro _ ⟨S, rfl⟩
    exact meyerFiniteProjector_positive_degree_le d hd hpos S u
  have hsup (S : Finset XiDivisorSupport) :
      (meyerDegreePair d (deningerMeyerFiniteXiCausalProjector S u)
        (deningerMeyerFiniteXiCausalProjector S u)).re ≤ meyerDegreeRegularEnergy d u :=
    le_csSup hb ⟨S, rfl⟩
  refine ⟨hsup, (hpos _).trans (hsup ∅), csSup_le ⟨_, ∅, rfl⟩ ?_⟩
  rintro _ ⟨S, rfl⟩
  exact meyerFiniteProjector_positive_degree_le d hd hpos S u

/-- The full energy splits into the regular supremum and a nonnegative residual. -/
theorem meyerPositiveDegree_regular_residual
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hd : ∀ u, d (meyerCohomologySharp u) = conj (d u))
    (hpos : ∀ u, 0 ≤ (meyerDegreePair d u u).re)
    (u : DeningerMeyerStrongLogCohomology) :
    0 ≤ (meyerDegreePair d u u).re - meyerDegreeRegularEnergy d u ∧
      (meyerDegreePair d u u).re = meyerDegreeRegularEnergy d u +
        ((meyerDegreePair d u u).re - meyerDegreeRegularEnergy d u) := by
  refine ⟨sub_nonneg.mpr (meyerPositiveDegree_regular_energy_bounds d hd hpos u).2.2, ?_⟩
  ring

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerFiniteCriticalProjector_sharp
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerFiniteCriticalProjector_complement_product_zero
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerFiniteCriticalProjector_square_decomposition
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerFiniteCriticalProjector_degree_decomposition
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerFiniteCriticalProjector_degree_le
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerFiniteCriticalProjector_degree_eq_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerFiniteCriticalProjector_square
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerFiniteCriticalProjector_degree_formula
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerFiniteCriticalWeightedEnergy_le
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerPositiveDegree_projector_formula
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerFiniteProjector_positive_cross_degree_zero
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerFiniteProjector_positive_degree_decomposition
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerFiniteProjector_positive_degree_formula
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerFiniteProjector_positive_degree_le
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerFiniteProjector_positive_degree_eq_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerPositiveDegree_regular_energy_bounds
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerPositiveDegree_regular_residual
