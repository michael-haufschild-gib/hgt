import GaloisForLFunctions.RHTower.XiEndpointCompletedValueBound

/-!
# The endpoint reflection channel is a convergent holomorphic Neumann carrier

The exact completed-value bound places the raw reciprocal Xi divisor vector strictly inside the
unit ball.  The functional-equation reflection can therefore be reconstructed pointwise by a
convergent geometric series in the conjugate reciprocal coordinate:

`1 / (1 - conj rho) = -sum_{n >= 1} conj(1 / rho)^n`.

Multiplying by the raw reciprocal coordinate removes the conjugation from the endpoint cross term.
After a uniform `9/10` bound and Tonelli interchange, the completed endpoint curvature becomes the
absolutely convergent all-order holomorphic trace series

`C_endpoint = -sum_{n >= 0} re(sum_rho rho^(-(n+2)))`.

Thus the reflected endpoint channel is not independent data: completion and the strict source
contraction reconstruct it cofinally from the holomorphic reciprocal-power traces.
-/

open Complex

namespace RHTower

noncomputable section

/-- The raw reciprocal Hermitian mass is strictly below `3/4`. -/
theorem xiRawReciprocalHermitianMass_lt_three_fourths :
    xiRawReciprocalHermitianMass < 3 / 4 := by
  have hmass :=
    xiRawReciprocalHermitianMass_le_three_halves_mul_endpointCurvature
  have hC := xiEndpointCompletedCurvature_lt_one_half
  nlinarith

/-- Every raw reciprocal Xi coordinate lies in the open unit disk. -/
theorem xiRawReciprocalCoordinate_norm_lt_one (q : XiZeroCopy) :
    ‖xiRawReciprocalCoordinate q‖ < 1 := by
  have hterm : ‖xiRawReciprocalCoordinate q‖ ^ 2 ≤
      xiRawReciprocalHermitianMass := by
    rw [xiRawReciprocalHermitianMass]
    exact summable_norm_xiRawReciprocalCoordinate_sq.le_tsum q
      (fun _ _ => sq_nonneg _)
  have hmass := xiRawReciprocalHermitianMass_lt_three_fourths
  have hn := norm_nonneg (xiRawReciprocalCoordinate q)
  nlinarith

/-- The critical-line reflection is the Möbius transform of the conjugate raw reciprocal
coordinate. -/
theorem xiRawReciprocalCoordinate_lineConj_eq_mobius (q : XiZeroCopy) :
    xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q) =
      -((starRingEnd ℂ) (xiRawReciprocalCoordinate q)) /
        (1 - (starRingEnd ℂ) (xiRawReciprocalCoordinate q)) := by
  have hrho : (q.1 : ℂ) ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.zero_im] at him
    exact xi_divisor_support_im_ne_zero q.1 him
  have hrhoOne : (q.1 : ℂ) ≠ 1 := by
    intro hone
    have him := congrArg Complex.im hone
    simp only [Complex.one_im] at him
    exact xi_divisor_support_im_ne_zero q.1 him
  have hstar : (starRingEnd ℂ) (q.1 : ℂ) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hrho
  have hstarOne : (starRingEnd ℂ) (q.1 : ℂ) ≠ 1 := by
    intro h
    apply hrhoOne
    have := congrArg (starRingEnd ℂ) h
    simpa using this
  rw [xiRawReciprocalCoordinate, xiRawReciprocalCoordinate]
  change (1 - (starRingEnd ℂ) (q.1 : ℂ))⁻¹ = _
  simp only [map_inv₀]
  field_simp [hstar, hstarOne]
  rw [show (starRingEnd ℂ) (q.1 : ℂ) - 1 =
      -(1 - (starRingEnd ℂ) (q.1 : ℂ)) by ring]

/-- **Cofinal pointwise reflection reconstruction.** -/
theorem hasSum_xiRawReciprocalCoordinate_lineConj_neumann (q : XiZeroCopy) :
    HasSum (fun n : ℕ =>
      -((starRingEnd ℂ) (xiRawReciprocalCoordinate q)) ^ (n + 1))
      (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q)) := by
  let z : ℂ := (starRingEnd ℂ) (xiRawReciprocalCoordinate q)
  have hz : ‖z‖ < 1 := by
    simpa [z] using xiRawReciprocalCoordinate_norm_lt_one q
  have hgeom := hasSum_geometric_of_norm_lt_one hz
  have hmul := hgeom.mul_left (-z)
  rw [xiRawReciprocalCoordinate_lineConj_eq_mobius]
  change HasSum (fun n : ℕ => -(z ^ (n + 1))) (-z / (1 - z))
  convert hmul using 1
  all_goals try rfl
  funext n
  rw [pow_succ]
  ring

/-- The endpoint cross term is the holomorphic Möbius transform of the raw reciprocal
coordinate. -/
theorem xiEndpointCrossTerm_eq_holomorphic_mobius (q : XiZeroCopy) :
    xiRawReciprocalCoordinate q *
        (starRingEnd ℂ)
          (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q)) =
      -(xiRawReciprocalCoordinate q) ^ 2 /
        (1 - xiRawReciprocalCoordinate q) := by
  rw [xiRawReciprocalCoordinate_lineConj_eq_mobius]
  simp only [map_div₀, map_neg, map_sub, map_one, starRingEnd_apply, star_star]
  have hrho : xiRawReciprocalCoordinate q ≠ 0 := by
    rw [xiRawReciprocalCoordinate]
    exact inv_ne_zero (by
      intro hzero
      have him := congrArg Complex.im hzero
      simp only [Complex.zero_im] at him
      exact xi_divisor_support_im_ne_zero q.1 him)
  field_simp [hrho]

/-- Every endpoint cross term is the sum of its holomorphic reciprocal-power trace fiber. -/
theorem hasSum_xiEndpointCrossTerm_holomorphicPowers (q : XiZeroCopy) :
    HasSum (fun n : ℕ => -(xiRawReciprocalCoordinate q) ^ (n + 2))
      (xiRawReciprocalCoordinate q *
        (starRingEnd ℂ)
          (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))) := by
  let z : ℂ := xiRawReciprocalCoordinate q
  have hz : ‖z‖ < 1 := xiRawReciprocalCoordinate_norm_lt_one q
  have hgeom := hasSum_geometric_of_norm_lt_one hz
  have hmul := hgeom.mul_left (-(z ^ 2))
  rw [xiEndpointCrossTerm_eq_holomorphic_mobius]
  change HasSum (fun n : ℕ => -(z ^ (n + 2))) (-(z ^ 2) / (1 - z))
  convert hmul using 1
  all_goals try rfl
  funext n
  rw [show n + 2 = 2 + n by omega, pow_add]
  ring

/-- The multiplicity-exact raw reciprocal-power trace. -/
def xiRawReciprocalPowerTrace (k : ℕ) : ℂ :=
  ∑' q : XiZeroCopy, xiRawReciprocalCoordinate q ^ k

/-- A uniform rational disk bound convenient for absolute double-series estimates. -/
theorem xiRawReciprocalCoordinate_norm_lt_nine_tenths (q : XiZeroCopy) :
    ‖xiRawReciprocalCoordinate q‖ < 9 / 10 := by
  have hterm : ‖xiRawReciprocalCoordinate q‖ ^ 2 ≤
      xiRawReciprocalHermitianMass := by
    rw [xiRawReciprocalHermitianMass]
    exact summable_norm_xiRawReciprocalCoordinate_sq.le_tsum q
      (fun _ _ => sq_nonneg _)
  have hmass := xiRawReciprocalHermitianMass_lt_three_fourths
  have hn := norm_nonneg (xiRawReciprocalCoordinate q)
  nlinarith

/-- Every raw reciprocal-power trace of order at least two is absolutely summable. -/
theorem summable_xiRawReciprocalCoordinate_pow_add_two (n : ℕ) :
    Summable (fun q : XiZeroCopy => xiRawReciprocalCoordinate q ^ (n + 2)) := by
  apply Summable.of_norm_bounded
    (summable_norm_xiRawReciprocalCoordinate_sq.mul_left ((9 / 10 : ℝ) ^ n))
  intro q
  rw [norm_pow, pow_add]
  have hp := pow_le_pow_left₀ (norm_nonneg _)
    (xiRawReciprocalCoordinate_norm_lt_nine_tenths q).le n
  nlinarith [sq_nonneg ‖xiRawReciprocalCoordinate q‖]

/-- Absolute summability of the full reciprocal-power trace carrier. -/
theorem summable_xiRawReciprocalNeumann_double :
    Summable (fun p : ℕ × XiZeroCopy =>
      -(xiRawReciprocalCoordinate p.2) ^ (p.1 + 2)) := by
  let ratio : ℝ := 9 / 10
  have hratio0 : 0 ≤ ratio := by norm_num [ratio]
  have hratio1 : ratio < 1 := by norm_num [ratio]
  have hgeom : Summable (fun n : ℕ => ratio ^ n) :=
    summable_geometric_of_lt_one hratio0 hratio1
  have hmajor : Summable (fun p : ℕ × XiZeroCopy =>
      ratio ^ p.1 * ‖xiRawReciprocalCoordinate p.2‖ ^ 2) := by
    rw [summable_prod_of_nonneg (fun p =>
      mul_nonneg (pow_nonneg hratio0 _) (sq_nonneg _))]
    constructor
    · intro n
      exact summable_norm_xiRawReciprocalCoordinate_sq.mul_left (ratio ^ n)
    · apply Summable.of_nonneg_of_le
          (fun n => tsum_nonneg fun _ =>
            mul_nonneg (pow_nonneg hratio0 _) (sq_nonneg _))
          (fun _ => le_rfl)
      convert hgeom.mul_right xiRawReciprocalHermitianMass using 1
      all_goals try rfl
      funext n
      rw [xiRawReciprocalHermitianMass, ← tsum_mul_left]
  apply Summable.of_norm_bounded hmajor
  rintro ⟨n, q⟩
  rw [norm_neg, norm_pow, pow_add]
  have hp := pow_le_pow_left₀ (norm_nonneg _)
    (xiRawReciprocalCoordinate_norm_lt_nine_tenths q).le n
  dsimp [ratio]
  exact mul_le_mul_of_nonneg_right hp (sq_nonneg _)

/-- **Global all-order holomorphic reconstruction of the endpoint cross trace.** -/
theorem hasSum_xiEndpointCrossTrace_allOrder :
    HasSum (fun n : ℕ => -xiRawReciprocalPowerTrace (n + 2))
      (∑' q : XiZeroCopy,
        xiRawReciprocalCoordinate q *
          (starRingEnd ℂ)
            (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))) := by
  let f : ℕ × XiZeroCopy → ℂ := fun p =>
    -(xiRawReciprocalCoordinate p.2) ^ (p.1 + 2)
  have hf : Summable f := summable_xiRawReciprocalNeumann_double
  have hfiberN : ∀ n : ℕ,
      HasSum (fun q : XiZeroCopy => f (n, q))
        (-xiRawReciprocalPowerTrace (n + 2)) := by
    intro n
    exact (summable_xiRawReciprocalCoordinate_pow_add_two n).hasSum.neg
  have hseq := hf.hasSum.prod_fiberwise hfiberN
  have htarget : (∑' p : ℕ × XiZeroCopy, f p) =
      ∑' q : XiZeroCopy,
        xiRawReciprocalCoordinate q *
          (starRingEnd ℂ)
            (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q)) := by
    calc
      (∑' p : ℕ × XiZeroCopy, f p) =
          ∑' n : ℕ, ∑' q : XiZeroCopy, f (n, q) := hf.tsum_prod
      _ = ∑' q : XiZeroCopy, ∑' n : ℕ, f (n, q) :=
        (Summable.tsum_comm hf).symm
      _ = _ := by
        apply tsum_congr
        intro q
        exact (hasSum_xiEndpointCrossTerm_holomorphicPowers q).tsum_eq
  rw [htarget] at hseq
  exact hseq

/-- The full complex endpoint cross trace is the completed Xi logarithmic derivative at the
boundary point. -/
theorem xiEndpointCrossTrace_eq_completedLogDeriv :
    (∑' q : XiZeroCopy,
      xiRawReciprocalCoordinate q *
        (starRingEnd ℂ)
          (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))) =
      -logDeriv XiC (I / 2) / (I / 2) := by
  have hlog := logDeriv_XiC_eq_relativeResolventTrace XiC_I_half_ne
  have hres := xiRelativeResolventTrace_eq_reciprocalSquareResolvent XiC_I_half_ne
  have hsum :
      (∑' q : XiZeroCopy, xiReciprocalSquareResolventTerm (I / 2) q) =
        ∑' q : XiZeroCopy,
          xiRawReciprocalCoordinate q *
            (starRingEnd ℂ)
              (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q)) := by
    apply tsum_congr
    intro q
    exact endpoint_term_eq q
  rw [hlog, hres, hsum]
  have hz : (I / 2 : ℂ) ≠ 0 := div_ne_zero I_ne_zero (by norm_num)
  field_simp [hz]

/-- **All-order holomorphic trace reading of the completed endpoint source.** -/
theorem hasSum_completedEndpointLogDeriv_holomorphicTraces :
    HasSum (fun n : ℕ => -xiRawReciprocalPowerTrace (n + 2))
      (-logDeriv XiC (I / 2) / (I / 2)) := by
  rw [← xiEndpointCrossTrace_eq_completedLogDeriv]
  exact hasSum_xiEndpointCrossTrace_allOrder

/-- **Completed endpoint curvature as an all-order holomorphic trace series.** -/
theorem hasSum_xiEndpointCompletedCurvature_holomorphicTraces :
    HasSum (fun n : ℕ => -(xiRawReciprocalPowerTrace (n + 2)).re)
      xiEndpointCompletedCurvature := by
  have h := Complex.reCLM.hasSum hasSum_xiEndpointCrossTrace_allOrder
  convert h using 1
  all_goals try rfl
  simpa using! xiEndpointCompletedCurvature_eq_cross_re

end

end RHTower
