/-
The Farey-numerator sum, and why every classical tool fails on it for one reason.

The campaign's one actionable analytic target is square-root cancellation in the sum over the Farey
numerator,

    Σ_(a mod q) ε(a, q) · e(N √(2a/q))  ≪  q^(1/2+ε)    uniformly for  q ≤ N^(1/3),

which would give `μ(1/2) ≤ 1/12`.  Put `q = N^y` with `0 < y ≤ 1/3`.  On a dyadic block of length `q`
the phase `g(a) = N√(2a/q)` has `|g'| ≍ N/q`, so the exponential-sum data is

    length `q = N^y` ,   `F ≍ q·|g'| ≍ N` ,   `F/length = N^(1-y)` ,

and an exponent pair `(κ, λ)` gives the bound `N^(κ(1-y) + λ y)`.

* **Nontriviality** — beating the trivial bound `N^y` — is `κ(1-y) + λy < y`.  At the extreme
  `y = 1/3` this is exactly `2κ + λ < 1`.  Weyl's pair sits *on* that boundary; every later landmark
  is strictly inside it.

* **The target** `N^(y/2)` requires `κ(1-y) + λy ≤ y/2`, i.e.

        **κ + y·d(κ, λ) ≤ 0** ,   `d(κ, λ) = λ - κ - 1/2` .

  Since `κ ≥ 0` and `λ ≥ 1/2` force `d ≥ -κ`, and `0 < y < 1`, this collapses to `κ = 0` and
  `λ = 1/2`.

So the target is reachable inside the exponent-pair framework only at the conjectural corner.  The
four separate failures recorded for van der Corput, Poisson, Pólya–Vinogradov and Weyl differencing
are one failure: reaching the target needs `λ ≤ 1/2 - 2κ`, and the exponent-pair region meets that
half-plane only at `(0, 1/2)` — the same corner that decides the Lindelöf hypothesis.
-/
import GaloisForLFunctions.HTGeometry.EligibilityCriterion

namespace HTGeometry

/-! ### The exponent-pair bound on the Farey-numerator sum -/

/-- Exponent of the bound an exponent pair gives on the Farey-numerator sum at `q = N^y`. -/
def fareyPairExponent (κ lam y : ℚ) : ℚ := κ * (1 - y) + lam * y

/-- The trivial bound's exponent. -/
def fareyTrivialExponent (y : ℚ) : ℚ := y

/-- The square-root target's exponent. -/
def fareyTargetExponent (y : ℚ) : ℚ := y / 2

/-- **Nontriviality is `κ(1-y) < y(1-λ)`.** -/
theorem farey_nontrivial_iff (κ lam y : ℚ) :
    fareyPairExponent κ lam y < fareyTrivialExponent y ↔ κ * (1 - y) < y * (1 - lam) := by
  unfold fareyPairExponent fareyTrivialExponent
  constructor <;> intro h <;> nlinarith

/-- **At the extreme length `q = N^(1/3)` nontriviality is exactly `2κ + λ < 1`.** -/
theorem farey_nontrivial_at_third (κ lam : ℚ) :
    fareyPairExponent κ lam (1 / 3) < fareyTrivialExponent (1 / 3) ↔ 2 * κ + lam < 1 := by
  unfold fareyPairExponent fareyTrivialExponent
  constructor <;> intro h <;> nlinarith

/-- **Weyl's pair lies exactly on the nontriviality boundary.** -/
theorem weyl_on_nontriviality_boundary : 2 * weylKappa + weylLambda = 1 := by
  unfold weylKappa weylLambda; norm_num

/-- **Every later landmark is strictly inside it.** -/
theorem landmarks_inside_nontriviality :
    2 * biKappa + biLambda < 1 ∧
      2 * huxleyPairKappa + huxleyPairLambda < 1 ∧
      2 * bourgainKappa + bourgainLambda < 1 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold biKappa biLambda; norm_num
  · unfold huxleyPairKappa huxleyPairLambda; norm_num
  · unfold bourgainKappa bourgainLambda; norm_num

/-- The most recent pairs are inside too. -/
theorem tty_inside_nontriviality :
    2 * ttyPair1Kappa + ttyPair1Lambda < 1 ∧ 2 * ttyPair2Kappa + ttyPair2Lambda < 1 := by
  constructor
  · unfold ttyPair1Kappa ttyPair1Lambda; norm_num
  · unfold ttyPair2Kappa ttyPair2Lambda; norm_num

/-! ### The target, and the collapse -/

/-- **The target is `κ + y·d ≤ 0`.** -/
theorem farey_target_iff (κ lam y : ℚ) :
    fareyPairExponent κ lam y ≤ fareyTargetExponent y ↔ κ + y * epDisplacement κ lam ≤ 0 := by
  unfold fareyPairExponent fareyTargetExponent epDisplacement
  constructor <;> intro h <;> nlinarith

/-- **The collapse.**  On the exponent-pair region the target forces the conjectural corner. -/
theorem farey_target_forces_corner {κ lam y : ℚ} (hκ : 0 ≤ κ) (hlam : 1 / 2 ≤ lam)
    (hy0 : 0 < y) (hy1 : y < 1)
    (htarget : fareyPairExponent κ lam y ≤ fareyTargetExponent y) :
    κ = 0 ∧ lam = 1 / 2 := by
  rw [farey_target_iff] at htarget
  unfold epDisplacement at htarget
  have hκ0 : κ = 0 := by nlinarith
  subst hκ0
  constructor
  · rfl
  · nlinarith

/-- **Equivalently, the target's half-plane is `λ ≤ 1/2 - κ(1-y)/y`**, which for `y = 1/3` is
`λ ≤ 1/2 - 2κ`. -/
theorem farey_target_halfplane {κ lam y : ℚ} (hy : 0 < y) :
    fareyPairExponent κ lam y ≤ fareyTargetExponent y ↔ lam ≤ 1 / 2 - κ * (1 - y) / y := by
  unfold fareyPairExponent fareyTargetExponent
  have hdiv : κ * (1 - y) / y * y = κ * (1 - y) := div_mul_cancel₀ _ (ne_of_gt hy)
  constructor
  · intro h
    have : (lam + κ * (1 - y) / y) * y ≤ (1 / 2 : ℚ) * y := by
      rw [add_mul, hdiv]; linarith
    have := le_of_mul_le_mul_right (by linarith : (lam + κ * (1 - y) / y) * y ≤ 1 / 2 * y) hy
    linarith
  · intro h
    have : (lam + κ * (1 - y) / y) * y ≤ (1 / 2 : ℚ) * y :=
      mul_le_mul_of_nonneg_right (by linarith) hy.le
    rw [add_mul, hdiv] at this
    linarith

/-- At `y = 1/3` the half-plane is `λ ≤ 1/2 - 2κ`, whose intersection with `λ ≥ 1/2`, `κ ≥ 0` is the
single point `(0, 1/2)`. -/
theorem farey_halfplane_at_third {κ lam : ℚ} (hκ : 0 ≤ κ) (hlam : 1 / 2 ≤ lam)
    (h : lam ≤ 1 / 2 - 2 * κ) : κ = 0 ∧ lam = 1 / 2 := by
  have hκ0 : κ = 0 := by linarith
  exact ⟨hκ0, by linarith⟩

/-! ### The unification of the four recorded failures -/

/-- **No landmark pair reaches the target**, at any admissible length. -/
theorem landmarks_miss_target {y : ℚ} (hy0 : 0 < y) (hy1 : y < 1) :
    ¬ (fareyPairExponent bourgainKappa bourgainLambda y ≤ fareyTargetExponent y) ∧
      ¬ (fareyPairExponent huxleyPairKappa huxleyPairLambda y ≤ fareyTargetExponent y) ∧
      ¬ (fareyPairExponent weylKappa weylLambda y ≤ fareyTargetExponent y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := (farey_target_forces_corner (by unfold bourgainKappa; norm_num)
      (by unfold bourgainLambda; norm_num) hy0 hy1 h).1
    unfold bourgainKappa at this; norm_num at this
  · intro h
    have := (farey_target_forces_corner (by unfold huxleyPairKappa; norm_num)
      (by unfold huxleyPairLambda; norm_num) hy0 hy1 h).1
    unfold huxleyPairKappa at this; norm_num at this
  · intro h
    have := (farey_target_forces_corner (by unfold weylKappa; norm_num)
      (by unfold weylLambda; norm_num) hy0 hy1 h).1
    unfold weylKappa at this; norm_num at this

/-- Nor do the most recent pairs. -/
theorem tty_pairs_miss_target {y : ℚ} (hy0 : 0 < y) (hy1 : y < 1) :
    ¬ (fareyPairExponent ttyPair1Kappa ttyPair1Lambda y ≤ fareyTargetExponent y) ∧
      ¬ (fareyPairExponent ttyPair2Kappa ttyPair2Lambda y ≤ fareyTargetExponent y) := by
  constructor
  · intro h
    have := (farey_target_forces_corner (by unfold ttyPair1Kappa; norm_num)
      (by unfold ttyPair1Lambda; norm_num) hy0 hy1 h).1
    unfold ttyPair1Kappa at this; norm_num at this
  · intro h
    have := (farey_target_forces_corner (by unfold ttyPair2Kappa; norm_num)
      (by unfold ttyPair2Lambda; norm_num) hy0 hy1 h).1
    unfold ttyPair2Kappa at this; norm_num at this

/-- **The gap between the corner and the target is the corner itself.**  The conjectural pair does
reach the target, at every admissible length. -/
theorem corner_reaches_target (y : ℚ) :
    fareyPairExponent 0 (1 / 2) y ≤ fareyTargetExponent y := by
  unfold fareyPairExponent fareyTargetExponent; linarith

/-- **The single cause.**  Reaching the target and reaching the Lindelöf exponent are the same
condition on the exponent-pair region: both require the corner `(0, 1/2)`. -/
theorem target_and_lindelof_share_the_corner {κ lam y : ℚ} (hκ : 0 ≤ κ) (hlam : 1 / 2 ≤ lam)
    (hy0 : 0 < y) (hy1 : y < 1)
    (htarget : fareyPairExponent κ lam y ≤ fareyTargetExponent y) :
    epMu κ lam = 0 := by
  obtain ⟨h1, h2⟩ := farey_target_forces_corner hκ hlam hy0 hy1 htarget
  rw [h1, h2]; unfold epMu; norm_num

end HTGeometry
