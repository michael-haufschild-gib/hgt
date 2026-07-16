import GaloisForLFunctions.RHTower.MobiusCriticalFisherTangentHilbertLift

open Complex Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

namespace RHTower

/-- The signed squarefree-Möbius source after the positive moving critical damping. -/
def infiniteMobiusCriticalDampedSignedWeight
    (sigma u : ℝ) (n : ℕ) : ℂ :=
  (Real.exp (-(u * (sigma - 1) * Real.log n)) : ℂ) *
    infiniteMobiusSignedWeight sigma n

private theorem norm_infiniteMobiusCriticalDampedSignedWeight_sq
    {sigma u : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    ‖infiniteMobiusCriticalDampedSignedWeight sigma u n‖ ^ 2 =
      Real.exp (-(u * (sigma - 1) * Real.log n)) ^ 2 *
        squarefreeMobiusProbability sigma n := by
  rw [infiniteMobiusCriticalDampedSignedWeight, norm_mul, mul_pow,
    norm_infiniteMobiusSignedWeight_sq hsigma, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

private theorem summable_norm_sq_infiniteMobiusCriticalDampedSignedWeight
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    Summable (fun n : ℕ =>
      ‖infiniteMobiusCriticalDampedSignedWeight sigma u n‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) ?_
    (summable_squarefreeMobiusProbability hsigma)
  intro n
  rw [norm_infiniteMobiusCriticalDampedSignedWeight_sq hsigma]
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hexp : Real.exp (-(u * (sigma - 1) * Real.log n)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg (mul_nonneg hu (sub_nonneg.mpr hsigma.le)) hlog)
  have hexp0 := Real.exp_pos (-(u * (sigma - 1) * Real.log n))
  have hsquare : Real.exp (-(u * (sigma - 1) * Real.log n)) ^ 2 ≤ 1 := by
    nlinarith
  exact mul_le_of_le_one_left (squarefreeMobiusProbability_nonneg hsigma n) hsquare

/-- The moving positive damping of the signed source is an actual Hilbert-space vector. -/
def infiniteMobiusCriticalDampedSignedWeightLp
    (sigma u : ℝ) (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    lp (fun _ : ℕ => ℂ) 2 :=
  ⟨infiniteMobiusCriticalDampedSignedWeight sigma u,
    HilbertSchmidt.memℓp_of_sq
      (summable_norm_sq_infiniteMobiusCriticalDampedSignedWeight hsigma hu)⟩

private theorem exp_critical_log_mul_probability_eq_boundaryLayerTerm
    {sigma u : ℝ} (n : ℕ) :
    Real.exp (-(u * (sigma - 1) * Real.log n)) *
        squarefreeMobiusProbability sigma n =
      squarefreeMobiusBoundaryLayerTerm sigma u n := by
  by_cases hsq : Squarefree n
  · have hn0 : n ≠ 0 := fun hn => by subst n; exact not_squarefree_zero hsq
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
    unfold squarefreeMobiusBoundaryLayerTerm
    calc
      _ = squarefreeMobiusProbability sigma n *
          Real.exp (Real.log n * (-(u * (sigma - 1)))) := by
        rw [mul_comm]
        congr 2
        ring
      _ = _ := by rw [Real.rpow_def_of_pos hnpos]
  · simp [squarefreeMobiusBoundaryLayerTerm, squarefreeMobiusProbability,
      squarefreeMobiusMass, hsq]

/-- The positive moving critical boundary transform is the matrix coefficient of the actual
signed source and its damped copy. -/
theorem inner_infiniteMobiusSignedWeight_damped_eq_boundaryLayerLaplace
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    inner ℂ (infiniteMobiusSignedWeightLp sigma hsigma)
      (infiniteMobiusCriticalDampedSignedWeightLp sigma u hsigma hu) =
      squarefreeMobiusBoundaryLayerLaplace sigma u := by
  rw [lp.inner_eq_tsum]
  simp only [infiniteMobiusSignedWeightLp,
    infiniteMobiusCriticalDampedSignedWeightLp, RCLike.inner_apply]
  rw [show (∑' n : ℕ,
      infiniteMobiusCriticalDampedSignedWeight sigma u n *
        (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n)) =
      ∑' n : ℕ, (squarefreeMobiusBoundaryLayerTerm sigma u n : ℂ) by
    apply tsum_congr
    intro n
    rw [infiniteMobiusCriticalDampedSignedWeight]
    have hnorm : infiniteMobiusSignedWeight sigma n *
        (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n) =
        (squarefreeMobiusProbability sigma n : ℂ) := by
      calc
        _ = ((‖infiniteMobiusSignedWeight sigma n‖ : ℂ) ^ 2) :=
          RCLike.mul_conj (infiniteMobiusSignedWeight sigma n)
        _ = _ := by rw [← Complex.ofReal_pow,
          norm_infiniteMobiusSignedWeight_sq hsigma]
    calc
      _ = (Real.exp (-(u * (sigma - 1) * Real.log n)) : ℂ) *
          (infiniteMobiusSignedWeight sigma n *
            (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n)) := by ring
      _ = _ := by
        rw [hnorm]
        have hcast := congrArg Complex.ofReal
          (exp_critical_log_mul_probability_eq_boundaryLayerTerm
            (sigma := sigma) (u := u) n)
        simpa only [Complex.ofReal_mul] using hcast]
  rw [← Complex.ofReal_tsum (squarefreeMobiusBoundaryLayerTerm sigma u)]
  exact ofReal_tsum_squarefreeMobiusBoundaryLayerTerm sigma u

/-- The moving critical damping with the Möbius parity restored. -/
def infiniteMobiusCriticalParityDampedWeight
    (sigma u : ℝ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
    infiniteMobiusCriticalDampedSignedWeight sigma u n

private theorem summable_norm_sq_infiniteMobiusCriticalParityDampedWeight
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    Summable (fun n : ℕ =>
      ‖infiniteMobiusCriticalParityDampedWeight sigma u n‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) ?_
    (summable_norm_sq_infiniteMobiusCriticalDampedSignedWeight hsigma hu)
  intro n
  rw [infiniteMobiusCriticalParityDampedWeight, norm_mul, mul_pow]
  have hmu : ‖(((ArithmeticFunction.moebius n : ℤ) : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  have hmu0 := norm_nonneg (((ArithmeticFunction.moebius n : ℤ) : ℂ))
  have hsq : ‖(((ArithmeticFunction.moebius n : ℤ) : ℂ))‖ ^ 2 ≤ 1 := by nlinarith
  exact mul_le_of_le_one_left (sq_nonneg _) hsq

/-- The parity-damped signed source is an actual Hilbert-space vector. -/
def infiniteMobiusCriticalParityDampedWeightLp
    (sigma u : ℝ) (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    lp (fun _ : ℕ => ℂ) 2 :=
  ⟨infiniteMobiusCriticalParityDampedWeight sigma u,
    HilbertSchmidt.memℓp_of_sq
      (summable_norm_sq_infiniteMobiusCriticalParityDampedWeight hsigma hu)⟩

/-- The signed moving boundary transform is the matrix coefficient of the source and its
parity-damped copy. -/
theorem inner_infiniteMobiusSignedWeight_parityDamped_eq_multiplier
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    inner ℂ (infiniteMobiusSignedWeightLp sigma hsigma)
      (infiniteMobiusCriticalParityDampedWeightLp sigma u hsigma hu) =
      infiniteMobiusLaplaceMultiplier sigma (mobiusCriticalBoundaryRate sigma u) := by
  rw [lp.inner_eq_tsum]
  simp only [infiniteMobiusSignedWeightLp,
    infiniteMobiusCriticalParityDampedWeightLp, RCLike.inner_apply]
  unfold infiniteMobiusLaplaceMultiplier
  apply tsum_congr
  intro n
  unfold infiniteMobiusCriticalParityDampedWeight
    infiniteMobiusCriticalDampedSignedWeight
    infiniteMobiusLaplaceMultiplierTerm signedMobiusProbability
  have hnorm : infiniteMobiusSignedWeight sigma n *
      (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n) =
      (squarefreeMobiusProbability sigma n : ℂ) := by
    calc
      _ = ((‖infiniteMobiusSignedWeight sigma n‖ : ℂ) ^ 2) :=
        RCLike.mul_conj (infiniteMobiusSignedWeight sigma n)
      _ = _ := by rw [← Complex.ofReal_pow,
        norm_infiniteMobiusSignedWeight_sq hsigma]
  rw [show Real.pi * mobiusCriticalBoundaryRate sigma u =
      u * (sigma - 1) by
    unfold mobiusCriticalBoundaryRate
    field_simp [Real.pi_ne_zero]]
  have hexp : (Real.exp (-(u * (sigma - 1) * Real.log n)) : ℂ) =
      Complex.exp (-((u * (sigma - 1) * Real.log n : ℝ) : ℂ)) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    rfl
  calc
    _ = ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
        (Real.exp (-(u * (sigma - 1) * Real.log n)) : ℂ) *
          (infiniteMobiusSignedWeight sigma n *
            (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n)) := by ring
    _ = _ := by rw [hnorm, hexp]; ring

private theorem boundaryLayerTerm_eq_totalRatio_mul_probability
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) (n : ℕ) :
    squarefreeMobiusBoundaryLayerTerm sigma u n =
      (squarefreeMobiusTotal (mobiusCriticalBoundaryParameter sigma u) /
        squarefreeMobiusTotal sigma) *
          squarefreeMobiusProbability
            (mobiusCriticalBoundaryParameter sigma u) n := by
  have hparam : 1 < mobiusCriticalBoundaryParameter sigma u := by
    unfold mobiusCriticalBoundaryParameter
    nlinarith
  rw [squarefreeMobiusBoundaryLayerTerm_eq,
    squarefreeMobiusProbability]
  field_simp [ne_of_gt (squarefreeMobiusTotal_pos hsigma),
    ne_of_gt (squarefreeMobiusTotal_pos hparam)]

private theorem summable_boundaryLayerTerm_mul_centeredLog
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    Summable (fun n : ℕ => squarefreeMobiusBoundaryLayerTerm sigma u n *
      (Real.log n - squarefreeMobiusLogMoment 1 sigma)) := by
  have hparam : 1 < mobiusCriticalBoundaryParameter sigma u := by
    unfold mobiusCriticalBoundaryParameter
    nlinarith
  let ratio := squarefreeMobiusTotal (mobiusCriticalBoundaryParameter sigma u) /
    squarefreeMobiusTotal sigma
  have h1 : Summable (fun n : ℕ =>
      squarefreeMobiusProbability (mobiusCriticalBoundaryParameter sigma u) n *
        Real.log n) := by
    simpa only [pow_one] using
      summable_squarefreeMobiusLogMoment 1 hparam
  have h0 := (summable_squarefreeMobiusProbability hparam).mul_left
    (-squarefreeMobiusLogMoment 1 sigma)
  have hcenter : Summable (fun n : ℕ =>
      squarefreeMobiusProbability (mobiusCriticalBoundaryParameter sigma u) n *
        (Real.log n - squarefreeMobiusLogMoment 1 sigma)) := by
    apply (h1.add h0).congr
    intro n
    ring
  apply (hcenter.mul_left ratio).congr
  intro n
  rw [boundaryLayerTerm_eq_totalRatio_mul_probability hsigma hu]
  dsimp [ratio]
  ring

private theorem tsum_boundaryLayerTerm_mul_centeredLog
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    (∑' n : ℕ, squarefreeMobiusBoundaryLayerTerm sigma u n *
      (Real.log n - squarefreeMobiusLogMoment 1 sigma)) =
      (squarefreeMobiusTotal (mobiusCriticalBoundaryParameter sigma u) /
        squarefreeMobiusTotal sigma) *
        (squarefreeMobiusLogMoment 1 (mobiusCriticalBoundaryParameter sigma u) -
          squarefreeMobiusLogMoment 1 sigma) := by
  have hparam : 1 < mobiusCriticalBoundaryParameter sigma u := by
    unfold mobiusCriticalBoundaryParameter
    nlinarith
  let ratio := squarefreeMobiusTotal (mobiusCriticalBoundaryParameter sigma u) /
    squarefreeMobiusTotal sigma
  rw [show (fun n : ℕ => squarefreeMobiusBoundaryLayerTerm sigma u n *
      (Real.log n - squarefreeMobiusLogMoment 1 sigma)) =
      fun n => ratio *
        (squarefreeMobiusProbability (mobiusCriticalBoundaryParameter sigma u) n *
          (Real.log n - squarefreeMobiusLogMoment 1 sigma)) by
    funext n
    rw [boundaryLayerTerm_eq_totalRatio_mul_probability hsigma hu]
    dsimp [ratio]
    ring]
  rw [tsum_mul_left]
  rw [show (fun n : ℕ =>
      squarefreeMobiusProbability (mobiusCriticalBoundaryParameter sigma u) n *
        (Real.log n - squarefreeMobiusLogMoment 1 sigma)) =
      fun n => squarefreeMobiusProbability (mobiusCriticalBoundaryParameter sigma u) n *
          Real.log n +
        (-squarefreeMobiusLogMoment 1 sigma) *
          squarefreeMobiusProbability (mobiusCriticalBoundaryParameter sigma u) n by
    funext n
    ring]
  have h1 : Summable (fun n : ℕ =>
      squarefreeMobiusProbability (mobiusCriticalBoundaryParameter sigma u) n *
        Real.log n) := by
    simpa only [pow_one] using summable_squarefreeMobiusLogMoment 1 hparam
  rw [Summable.tsum_add h1
    ((summable_squarefreeMobiusProbability hparam).mul_left _), tsum_mul_left]
  rw [show (∑' n : ℕ,
      squarefreeMobiusProbability (mobiusCriticalBoundaryParameter sigma u) n *
        Real.log n) =
      squarefreeMobiusLogMoment 1 (mobiusCriticalBoundaryParameter sigma u) by
    unfold squarefreeMobiusLogMoment
    simp only [pow_one]]
  rw [tsum_squarefreeMobiusProbability hparam]
  dsimp [ratio]
  ring

/-- The Fisher tangent against the positively damped source is exactly the positive boundary
transform times a shifted-minus-unshifted logarithmic moment. -/
theorem inner_fisherTangent_damped_eq_boundaryLayer_momentDifference
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    inner ℂ (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
      (infiniteMobiusCriticalDampedSignedWeightLp sigma u hsigma hu) =
      ((-2 * (sigma - 1) : ℝ) : ℂ) *
        squarefreeMobiusBoundaryLayerLaplace sigma u *
          ((squarefreeMobiusLogMoment 1 (mobiusCriticalBoundaryParameter sigma u) -
            squarefreeMobiusLogMoment 1 sigma : ℝ) : ℂ) := by
  rw [lp.inner_eq_tsum]
  simp only [infiniteMobiusCriticalFisherTangentLp,
    infiniteMobiusCriticalDampedSignedWeightLp, RCLike.inner_apply]
  rw [show (∑' n : ℕ,
      infiniteMobiusCriticalDampedSignedWeight sigma u n *
        (starRingEnd ℂ) (infiniteMobiusCriticalFisherTangentWeight sigma n)) =
      ∑' n : ℕ, (((-2 * (sigma - 1) *
        (squarefreeMobiusBoundaryLayerTerm sigma u n *
          (Real.log n - squarefreeMobiusLogMoment 1 sigma)) : ℝ) : ℂ)) by
    apply tsum_congr
    intro n
    unfold infiniteMobiusCriticalDampedSignedWeight
      infiniteMobiusCriticalFisherTangentWeight
    have hnorm : infiniteMobiusSignedWeight sigma n *
        (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n) =
        (squarefreeMobiusProbability sigma n : ℂ) := by
      calc
        _ = ((‖infiniteMobiusSignedWeight sigma n‖ : ℂ) ^ 2) :=
          RCLike.mul_conj (infiniteMobiusSignedWeight sigma n)
        _ = _ := by rw [← Complex.ofReal_pow,
          norm_infiniteMobiusSignedWeight_sq hsigma]
    simp only [map_mul, Complex.conj_ofReal]
    have hterm := exp_critical_log_mul_probability_eq_boundaryLayerTerm
      (sigma := sigma) (u := u) n
    calc
      _ = ((-2 * (sigma - 1) *
          (Real.log n - squarefreeMobiusLogMoment 1 sigma) : ℝ) : ℂ) *
            ((Real.exp (-(u * (sigma - 1) * Real.log n)) : ℂ) *
              (infiniteMobiusSignedWeight sigma n *
                (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n))) := by ring
      _ = _ := by
        rw [hnorm]
        have hcast := congrArg Complex.ofReal hterm
        rw [Complex.ofReal_mul] at hcast
        rw [hcast]
        push_cast
        ring]
  rw [← Complex.ofReal_tsum (fun n : ℕ =>
    -2 * (sigma - 1) *
      (squarefreeMobiusBoundaryLayerTerm sigma u n *
        (Real.log n - squarefreeMobiusLogMoment 1 sigma)))]
  rw [tsum_mul_left]
  rw [tsum_boundaryLayerTerm_mul_centeredLog hsigma hu]
  rw [squarefreeMobiusBoundaryLayerLaplace, ← Complex.ofReal_div]
  push_cast
  ring

private theorem tendsto_mobiusCriticalBoundaryParameter_nhdsWithin
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun sigma : ℝ => mobiusCriticalBoundaryParameter sigma u)
      (nhdsWithin 1 (Set.Ioi 1)) (nhdsWithin 1 (Set.Ioi 1)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hcont : ContinuousAt
        (fun sigma : ℝ => mobiusCriticalBoundaryParameter sigma u) 1 := by
      unfold mobiusCriticalBoundaryParameter
      fun_prop
    simpa [mobiusCriticalBoundaryParameter] using
      hcont.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    unfold mobiusCriticalBoundaryParameter
    change 1 < sigma at hsigma
    change 1 < sigma + u * (sigma - 1)
    nlinarith

private theorem tendsto_scaled_logMoment_at_boundaryParameter
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun sigma : ℝ =>
      (sigma - 1) *
        squarefreeMobiusLogMoment 1 (mobiusCriticalBoundaryParameter sigma u))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds ((1 + u)⁻¹)) := by
  have hden : 1 + u ≠ 0 := by nlinarith
  have hcrit := tendsto_squarefreeMobiusLogMoment_one_critical.comp
    (tendsto_mobiusCriticalBoundaryParameter_nhdsWithin hu)
  have hconst : Tendsto (fun _ : ℝ => (1 + u)⁻¹)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds ((1 + u)⁻¹)) := tendsto_const_nhds
  have hscaled := hconst.mul hcrit
  convert hscaled using 1
  · funext sigma
    simp only [Function.comp_apply]
    unfold mobiusCriticalBoundaryParameter
    field_simp [hden]
    ring
  · field_simp

/-- The proof-independent scalar formula for the Fisher-tangent/damped-source coefficient. -/
def infiniteMobiusCriticalFisherTangentDampedCoefficient
    (sigma u : ℝ) : ℂ :=
  ((-2 * (sigma - 1) : ℝ) : ℂ) *
    squarefreeMobiusBoundaryLayerLaplace sigma u *
      ((squarefreeMobiusLogMoment 1 (mobiusCriticalBoundaryParameter sigma u) -
        squarefreeMobiusLogMoment 1 sigma : ℝ) : ℂ)

/-- The actual Hilbert-space coefficient agrees with its proof-independent scalar formula. -/
theorem inner_fisherTangent_damped_eq_coefficient
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    inner ℂ (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
      (infiniteMobiusCriticalDampedSignedWeightLp sigma u hsigma hu) =
      infiniteMobiusCriticalFisherTangentDampedCoefficient sigma u := by
  exact inner_fisherTangent_damped_eq_boundaryLayer_momentDifference hsigma hu

/-- The Fisher-tangent/damped-source coefficient has the universal critical profile
`2u / (1 + u)²`. -/
theorem tendsto_infiniteMobiusCriticalFisherTangentDampedCoefficient
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun sigma : ℝ =>
      infiniteMobiusCriticalFisherTangentDampedCoefficient sigma u)
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (((2 * u / (1 + u) ^ 2 : ℝ) : ℂ))) := by
  have hden : 1 + u ≠ 0 := by nlinarith
  have hboundary := tendsto_squarefreeMobiusBoundaryLayerLaplace hu
  have hboundaryCast : Tendsto
      (fun sigma : ℝ => squarefreeMobiusBoundaryLayerLaplace sigma u)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds ((((1 + u)⁻¹ : ℝ) : ℂ))) := by
    convert hboundary using 1
    rw [Complex.ofReal_inv]
  have hshift := tendsto_scaled_logMoment_at_boundaryParameter hu
  have hbase := tendsto_squarefreeMobiusLogMoment_one_critical
  have hdiff : Tendsto (fun sigma : ℝ =>
      (sigma - 1) *
        (squarefreeMobiusLogMoment 1 (mobiusCriticalBoundaryParameter sigma u) -
          squarefreeMobiusLogMoment 1 sigma))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds ((1 + u)⁻¹ - 1)) := by
    simpa [mul_sub] using hshift.sub hbase
  have hdiffComplex : Tendsto (fun sigma : ℝ =>
      (((sigma - 1) *
        (squarefreeMobiusLogMoment 1 (mobiusCriticalBoundaryParameter sigma u) -
          squarefreeMobiusLogMoment 1 sigma) : ℝ) : ℂ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds ((((1 + u)⁻¹ - 1 : ℝ) : ℂ))) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hdiff
  have hconst : Tendsto (fun _ : ℝ => (-2 : ℂ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (-2 : ℂ)) := tendsto_const_nhds
  have hproduct := (hconst.mul hboundaryCast).mul hdiffComplex
  convert hproduct using 1
  · funext sigma
    unfold infiniteMobiusCriticalFisherTangentDampedCoefficient
    push_cast
    ring
  · congr 1
    norm_cast
    field_simp [hden]
    norm_num

end RHTower
