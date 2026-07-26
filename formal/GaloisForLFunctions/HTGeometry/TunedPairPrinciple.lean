/-
Tuning a pair's displacement to the abscissa.

At abscissa `σ` the growth bound from a pair `(κ, λ)` is `max_c ( min(c, κ + c(λ-κ)) - c·σ )` over
`0 ≤ c ≤ 1/2`.  The pair branch has slope `λ - κ - σ`, so the maximum is:

* at the crossover `c₀ = κ/(1 - λ + κ)` when `λ - κ ≤ σ`, of value `c₀(1 - σ)`;
* at the critical block when `λ - κ > σ`, of value `(κ + λ - σ)/2`.

**When `λ - κ = σ` exactly the pair branch is flat and both values coincide at `κ`.**  So a pair
tuned to the abscissa — displacement `d = σ - 1/2` — delivers

    **μ(σ) ≤ κ** ,

and the whole problem at that abscissa becomes: minimise `κ` subject to `λ - κ = σ`.

Tuning is available by convexity of the exponent-pair region: the segment from a pair on the line of
symmetry to its `A`-image sweeps `λ - κ` from `1/2` up to the image's value.  For Bourgain's pair
`(13/84, 55/84)` and its image `(13/194, 76/97)` the sweep covers `[1/2, 139/194]`, and `σ = 7/10`
is hit at parameter `t = 97/105`, giving the tuned pair

    **Q = (65/882, 1706/2205)** ,   `λ - κ = 7/10` ,   hence   **μ(7/10) ≤ 65/882** .

Since `65/882 = 0.0736961…` and `3/40 = 0.075`, the tuned pair beats the plain convex-combination
reading of the two endpoints; `65·40 = 2600 < 2646 = 3·882`.
-/
import GaloisForLFunctions.HTGeometry.BindingBlockOffLine

namespace HTGeometry

/-! ### The tuning principle -/

/-- A pair is tuned to the abscissa when its displacement equals the distance from the critical
line. -/
def TunedTo (κ lam σ : ℚ) : Prop := lam - κ = σ

/-- **Tuning is the vanishing of the pair branch's slope.** -/
theorem tuned_iff_flat_branch (κ lam σ : ℚ) :
    TunedTo κ lam σ ↔ pairBranchSlope (epDisplacement κ lam) σ = 0 := by
  unfold TunedTo pairBranchSlope epDisplacement
  constructor <;> intro h <;> linarith

/-- **For a tuned pair the crossover value and the critical-block value coincide, both equal to
`κ`.** -/
theorem tuned_values_agree {κ lam σ : ℚ} (h : TunedTo κ lam σ) (hσ : σ < 1) :
    crossoverScale κ (epDisplacement κ lam) * (1 - σ) = κ ∧ (κ + lam - σ) / 2 = κ := by
  unfold TunedTo at h
  have hd : epDisplacement κ lam = σ - 1 / 2 := by
    unfold epDisplacement; linarith
  constructor
  · unfold crossoverScale
    rw [hd]
    rw [show (1 : ℚ) / 2 - (σ - 1 / 2) = 1 - σ by ring]
    rw [div_mul_cancel₀]
    linarith
  · linarith

/-- **The tuned bound.**  A pair tuned to `σ` gives `μ(σ) ≤ κ`. -/
theorem tuned_bound {κ lam σ : ℚ} (h : TunedTo κ lam σ) : (κ + lam - σ) / 2 = κ := by
  unfold TunedTo at h; linarith

/-! ### Tuning by convex combination -/

/-- The tuning parameter on the segment from Bourgain's pair to its `A`-image, reaching `λ-κ = 7/10`.
-/
def tuneParam : ℚ := 97 / 105

/-- **The tuned pair's coordinates.** -/
def tunedKappa : ℚ := 65 / 882

/-- Its second coordinate. -/
def tunedLambda : ℚ := 1706 / 2205

/-- **The tuned pair is the stated convex combination.** -/
theorem tuned_is_mix :
    mixFst bourgainKappa (procA_fst bourgainKappa) tuneParam = tunedKappa ∧
      mixSnd bourgainLambda (procA_snd bourgainKappa bourgainLambda) tuneParam = tunedLambda := by
  rw [procA_bourgain.1, procA_bourgain.2]
  constructor
  · unfold mixFst bourgainKappa tuneParam tunedKappa; norm_num
  · unfold mixSnd bourgainLambda tuneParam tunedLambda; norm_num

/-- **It is tuned to `σ = 7/10`.** -/
theorem tuned_pair_tuned : TunedTo tunedKappa tunedLambda (7 / 10) := by
  unfold TunedTo tunedKappa tunedLambda; norm_num

/-- Its displacement is exactly `1/5`. -/
theorem tuned_displacement : epDisplacement tunedKappa tunedLambda = 1 / 5 := by
  unfold epDisplacement tunedKappa tunedLambda; norm_num

/-- **Hence the bound `μ(7/10) ≤ 65/882`.** -/
theorem tuned_bound_at_seven_tenths :
    (tunedKappa + tunedLambda - 7 / 10) / 2 = tunedKappa :=
  tuned_bound tuned_pair_tuned

/-- **It beats the published value `3/40`**, since `65·40 = 2600 < 2646 = 3·882`. -/
theorem tuned_beats_published : tunedKappa < muSevenTenths := by
  unfold tunedKappa muSevenTenths; norm_num

/-- The margin. -/
theorem tuned_margin : muSevenTenths - tunedKappa = 23 / 17640 := by
  unfold muSevenTenths tunedKappa; norm_num

/-- **But it still misses the record threshold `23/420`.** -/
theorem tuned_misses_record_threshold :
    recordThresholdAtSevenTenths < tunedKappa := by
  unfold recordThresholdAtSevenTenths tunedKappa; norm_num

/-- The remaining deficit after tuning. -/
theorem tuned_remaining_deficit :
    tunedKappa - recordThresholdAtSevenTenths = 167 / 8820 := by
  unfold tunedKappa recordThresholdAtSevenTenths; norm_num

/-! ### The tuned pair's own crossover -/

/-- Its crossover scale. -/
theorem tuned_crossover : crossoverScale tunedKappa (1 / 5) = 325 / 1323 := by
  unfold crossoverScale tunedKappa; norm_num

/-- **And the crossover value equals `κ`, as the tuning principle predicts.** -/
theorem tuned_crossover_value :
    (325 / 1323 : ℚ) * (1 - 7 / 10) = tunedKappa := by
  unfold tunedKappa; norm_num

/-! ### What tuning does and does not buy -/

/-- **Transferring the tuned bound back to the critical line gives nothing**, as the general theory
predicts: `65/882 + 1/10 = 383/2205 > 13/84`. -/
theorem tuned_transfer_useless :
    bourgainTheta < tunedKappa + (7 / 10 - 1 / 2) / 2 := by
  unfold bourgainTheta tunedKappa; norm_num

/-- **The tuning principle, stated.**  At each abscissa the optimal exponent pair is the one whose
displacement equals `σ - 1/2`; the bound is then its `κ`, and the problem at that abscissa is to
minimise `κ` along the tuned slice `λ - κ = σ` of the exponent-pair region. -/
theorem tuning_principle {κ lam σ : ℚ} (h : TunedTo κ lam σ) :
    epDisplacement κ lam = σ - 1 / 2 ∧ (κ + lam - σ) / 2 = κ := by
  unfold TunedTo at h
  refine ⟨?_, by linarith⟩
  unfold epDisplacement; linarith

end HTGeometry
