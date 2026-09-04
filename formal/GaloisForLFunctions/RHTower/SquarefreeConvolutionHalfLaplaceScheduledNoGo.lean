import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfLaplaceDiagonalNoGo

/-!
# Scheduled Laplace transport no-go

The reciprocal diagonal is only one instance of a general obstruction.  Any heat schedule whose
late samples stay bounded, whose adjacent intervals cover every sufficiently small positive time,
and whose adjacent first-moment transport cost stays bounded would make the complete boundary heat
profile bounded at zero.  The Mellin pole obstruction rules out every such schedule.
-/

open Complex Filter Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- At the boundary point, multiplication by the frequency leaves only the sharp `5/11`
coefficient growth. -/
theorem norm_squarefreeHalfBoundaryLaplaceCoeff_mul_natCast_le (n : ℕ) :
    ‖squarefreeHalfBoundaryLaplaceCoeff n‖ * (n : ℝ) ≤
      ((n : ℝ) + 1) ^ (5 / 11 : ℝ) := by
  by_cases hn : n = 0
  · subst n
    norm_num
  rw [squarefreeHalfBoundaryLaplaceCoeff, LSeries.norm_term_eq, if_neg hn]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hcoeff : ‖squarefreeConvolutionHalf n‖ ≤ 1 :=
    norm_squarefreeConvolutionHalf_le_one n
  have hdenpos : 0 < (n : ℝ) ^ boundaryExteriorPoint.re :=
    Real.rpow_pos_of_pos hnpos _
  have hfirst :
      (‖squarefreeConvolutionHalf n‖ / (n : ℝ) ^ boundaryExteriorPoint.re) * (n : ℝ) ≤
        (1 / (n : ℝ) ^ (6 / 11 : ℝ)) * (n : ℝ) := by
    have hdiv := div_le_div_of_nonneg_right hcoeff hdenpos.le
    norm_num [boundaryExteriorPoint] at hdiv ⊢
    exact mul_le_mul_of_nonneg_right hdiv hnpos.le
  refine hfirst.trans ?_
  have heq :
      (1 / (n : ℝ) ^ (6 / 11 : ℝ)) * (n : ℝ) =
        (n : ℝ) ^ (5 / 11 : ℝ) := by
    rw [one_div, ← Real.rpow_neg hnpos.le]
    calc
      (n : ℝ) ^ (-(6 / 11 : ℝ)) * (n : ℝ) =
          (n : ℝ) ^ (-(6 / 11 : ℝ)) * (n : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (n : ℝ) ^ (-(6 / 11 : ℝ) + 1) := (Real.rpow_add hnpos _ _).symm
      _ = (n : ℝ) ^ (5 / 11 : ℝ) := by norm_num
  rw [heq]
  exact Real.rpow_le_rpow hnpos.le (by linarith) (by norm_num)

private theorem scheduled_norm_exp_neg_nat_mul_sub_le
    (n : ℕ) {x y q : ℝ} (hqx : q ≤ x) (hqy : q ≤ y) :
    ‖Complex.exp (-(((n : ℝ) * x : ℝ) : ℂ)) -
        Complex.exp (-(((n : ℝ) * y : ℝ) : ℂ))‖ ≤
      Real.exp (-((n : ℝ) * q)) * (n : ℝ) * |x - y| := by
  have ha : -((n : ℝ) * x) ≤ -((n : ℝ) * q) := by
    exact neg_le_neg (mul_le_mul_of_nonneg_left hqx (Nat.cast_nonneg n))
  have hb : -((n : ℝ) * y) ≤ -((n : ℝ) * q) := by
    exact neg_le_neg (mul_le_mul_of_nonneg_left hqy (Nat.cast_nonneg n))
  have h := abs_exp_sub_exp_le ha hb
  have harg :
      |-((n : ℝ) * x) - -((n : ℝ) * y)| = (n : ℝ) * |x - y| := by
    rw [show -((n : ℝ) * x) - -((n : ℝ) * y) = -(n : ℝ) * (x - y) by ring,
      abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
  rw [show -(((n : ℝ) * x : ℝ) : ℂ) = ((-((n : ℝ) * x) : ℝ) : ℂ) by push_cast; ring,
    show -(((n : ℝ) * y : ℝ) : ℂ) = ((-((n : ℝ) * y) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp, ← Complex.ofReal_exp, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  calc
    |Real.exp (-((n : ℝ) * x)) - Real.exp (-((n : ℝ) * y))| ≤
        Real.exp (-((n : ℝ) * q)) *
          |-((n : ℝ) * x) - -((n : ℝ) * y)| := h
    _ = Real.exp (-((n : ℝ) * q)) * (n : ℝ) * |x - y| := by rw [harg]; ring

/-- Arithmetic coefficient decay improves the boundary heat transport exponent from `2` to
`16/11`. -/
theorem norm_squarefreeHalfBoundaryLaplaceProfile_sub_le_weighted
    {x y q : ℝ} (hx : 0 < x) (hy : 0 < y) (hq : 0 < q)
    (hqx : q ≤ x) (hqy : q ≤ y) :
    ‖squarefreeHalfBoundaryLaplaceProfile x -
        squarefreeHalfBoundaryLaplaceProfile y‖ ≤
      |x - y| *
        (1 + Real.exp q * 2 ^ (5 / 11 : ℝ) * (1 / q) ^ (16 / 11 : ℝ) *
          Real.Gamma (16 / 11 : ℝ)) := by
  let u : ℕ → ℝ := fun n =>
    ((n : ℝ) + 1) ^ (5 / 11 : ℝ) * Real.exp (-((n : ℝ) * q)) * |x - y|
  have hxsum := summable_coeffLaplaceTerm
    norm_squarefreeHalfBoundaryLaplaceCoeff_le_one hx
  have hysum := summable_coeffLaplaceTerm
    norm_squarefreeHalfBoundaryLaplaceCoeff_le_one hy
  have hmoment := summable_natSucc_rpow_exp_neg_and_tsum_le
    (r := (5 / 11 : ℝ)) (x := q) (by norm_num) hq
  have hu : Summable u := by
    have h := hmoment.1.mul_right |x - y|
    simpa only [u, mul_assoc] using h
  have hmomentBound :
      (∑' n : ℕ, ((n : ℝ) + 1) ^ (5 / 11 : ℝ) *
        Real.exp (-((n : ℝ) * q))) ≤
      1 + Real.exp q * 2 ^ (5 / 11 : ℝ) * (1 / q) ^ (16 / 11 : ℝ) *
        Real.Gamma (16 / 11 : ℝ) := by
    have hexponent : (5 / 11 : ℝ) + 1 = 16 / 11 := by norm_num
    simpa only [hexponent] using hmoment.2
  have hterm : ∀ n : ℕ,
      ‖squarefreeHalfBoundaryLaplaceCoeff n *
          Complex.exp (-(((n : ℝ) * x : ℝ) : ℂ)) -
        squarefreeHalfBoundaryLaplaceCoeff n *
          Complex.exp (-(((n : ℝ) * y : ℝ) : ℂ))‖ ≤ u n := by
    intro n
    rw [← mul_sub, norm_mul]
    have hexp := scheduled_norm_exp_neg_nat_mul_sub_le n hqx hqy
    have hweighted := norm_squarefreeHalfBoundaryLaplaceCoeff_mul_natCast_le n
    dsimp [u]
    calc
      ‖squarefreeHalfBoundaryLaplaceCoeff n‖ *
          ‖Complex.exp (-(((n : ℝ) * x : ℝ) : ℂ)) -
            Complex.exp (-(((n : ℝ) * y : ℝ) : ℂ))‖ ≤
          ‖squarefreeHalfBoundaryLaplaceCoeff n‖ *
            (Real.exp (-((n : ℝ) * q)) * (n : ℝ) * |x - y|) :=
        mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
      _ = (‖squarefreeHalfBoundaryLaplaceCoeff n‖ * (n : ℝ)) *
          Real.exp (-((n : ℝ) * q)) * |x - y| := by ring
      _ ≤ ((n : ℝ) + 1) ^ (5 / 11 : ℝ) *
          Real.exp (-((n : ℝ) * q)) * |x - y| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hweighted (Real.exp_pos _).le)
          (abs_nonneg _)
  have hdiff : Summable fun n : ℕ =>
      ‖squarefreeHalfBoundaryLaplaceCoeff n *
          Complex.exp (-(((n : ℝ) * x : ℝ) : ℂ)) -
        squarefreeHalfBoundaryLaplaceCoeff n *
          Complex.exp (-(((n : ℝ) * y : ℝ) : ℂ))‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hu
  unfold squarefreeHalfBoundaryLaplaceProfile coeffLaplaceProfile
  rw [← hxsum.tsum_sub hysum]
  calc
    ‖∑' n : ℕ,
        (squarefreeHalfBoundaryLaplaceCoeff n *
            Complex.exp (-(((n : ℝ) * x : ℝ) : ℂ)) -
          squarefreeHalfBoundaryLaplaceCoeff n *
            Complex.exp (-(((n : ℝ) * y : ℝ) : ℂ)))‖ ≤
        ∑' n : ℕ,
          ‖squarefreeHalfBoundaryLaplaceCoeff n *
              Complex.exp (-(((n : ℝ) * x : ℝ) : ℂ)) -
            squarefreeHalfBoundaryLaplaceCoeff n *
              Complex.exp (-(((n : ℝ) * y : ℝ) : ℂ))‖ :=
      norm_tsum_le_tsum_norm hdiff
    _ ≤ ∑' n : ℕ, u n := hdiff.tsum_le_tsum hterm hu
    _ = (∑' n : ℕ,
          ((n : ℝ) + 1) ^ (5 / 11 : ℝ) * Real.exp (-((n : ℝ) * q))) *
          |x - y| := by
      rw [tsum_mul_right]
    _ ≤ (1 + Real.exp q * 2 ^ (5 / 11 : ℝ) * (1 / q) ^ (16 / 11 : ℝ) *
          Real.Gamma (16 / 11 : ℝ)) * |x - y| :=
      mul_le_mul_of_nonneg_right hmomentBound (abs_nonneg _)
    _ = |x - y| *
        (1 + Real.exp q * 2 ^ (5 / 11 : ℝ) * (1 / q) ^ (16 / 11 : ℝ) *
          Real.Gamma (16 / 11 : ℝ)) := by ring

/-- Explicit first-moment majorant controlling transport of the bounded-coefficient boundary heat
profile between two positive times whose common lower bound is `q`. -/
def squarefreeHalfBoundaryLaplaceTransportMoment (q : ℝ) : ℝ :=
  1 + Real.exp q * 2 ^ (1 : ℝ) * (1 / q) ^ (2 : ℝ) * Real.Gamma 2

/-- Sharper first-moment majorant retaining the arithmetic `n⁻⁶/¹¹` boundary decay. -/
def squarefreeHalfBoundaryLaplaceWeightedTransportMoment (q : ℝ) : ℝ :=
  1 + Real.exp q * 2 ^ (5 / 11 : ℝ) * (1 / q) ^ (16 / 11 : ℝ) *
    Real.Gamma (16 / 11 : ℝ)

/-- Generic schedule interface parameterized by a proved adjacent-transport majorant. -/
def SquarefreeHalfBoundaryLaplaceTransportControlledWith
    (M : ℝ → ℝ) (τ : ℕ → ℝ) : Prop :=
  ∃ N₀ : ℕ, ∃ ε B K : ℝ,
    0 < ε ∧ 0 ≤ B ∧ 0 ≤ K ∧
    (∀ x : ℝ, 0 < x → x < ε →
      ∃ N : ℕ, N₀ ≤ N ∧ τ (N + 1) ≤ x ∧ x ≤ τ N) ∧
    (∀ N : ℕ, N₀ ≤ N → ‖squarefreeHalfBoundaryLaplaceProfile (τ N)‖ ≤ K) ∧
    (∀ N : ℕ, N₀ ≤ N →
      0 < τ (N + 1) ∧
        |τ N - τ (N + 1)| * M (τ (N + 1)) ≤ B)

/-- Controlled schedule using only the crude bounded-coefficient moment. -/
def SquarefreeHalfBoundaryLaplaceTransportControlled (τ : ℕ → ℝ) : Prop :=
  SquarefreeHalfBoundaryLaplaceTransportControlledWith
    squarefreeHalfBoundaryLaplaceTransportMoment τ

/-- Controlled schedule using the sharper arithmetic-weighted moment. -/
def SquarefreeHalfBoundaryLaplaceWeightedTransportControlled (τ : ℕ → ℝ) : Prop :=
  SquarefreeHalfBoundaryLaplaceTransportControlledWith
    squarefreeHalfBoundaryLaplaceWeightedTransportMoment τ

/-- Any real sequence converging to zero has an adjacent crossing interval below each positive
threshold smaller than its chosen head value.  Monotonicity is unnecessary: the first crossing
supplies the interval. -/
theorem exists_adjacent_heat_mesh_of_tendsto_zero
    {τ : ℕ → ℝ} (htend : Tendsto τ atTop (𝓝 0)) {N₀ : ℕ} {x : ℝ}
    (hx : 0 < x) (hxhead : x < τ N₀) :
    ∃ N : ℕ, N₀ ≤ N ∧ τ (N + 1) ≤ x ∧ x ≤ τ N := by
  have hevent : ∀ᶠ n : ℕ in atTop, τ n < x :=
    (tendsto_order.1 htend).2 x hx
  have hex : ∃ m : ℕ, N₀ ≤ m ∧ τ m ≤ x := by
    have hboth := (eventually_ge_atTop N₀).and hevent
    rcases hboth.exists with ⟨m, hmN, hmx⟩
    exact ⟨m, hmN, hmx.le⟩
  obtain ⟨m, hmN, hmx⟩ := hex
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmN
  have hexshift : ∃ j : ℕ, τ (N₀ + j) ≤ x := ⟨k, hmx⟩
  let j : ℕ := Nat.find hexshift
  have hj : τ (N₀ + j) ≤ x := Nat.find_spec hexshift
  have hjpos : 0 < j := by
    by_contra h
    have hjzero : j = 0 := Nat.eq_zero_of_not_pos h
    rw [hjzero, Nat.add_zero] at hj
    linarith
  let N : ℕ := N₀ + j - 1
  have hN : N₀ ≤ N := by
    dsimp [N]
    omega
  have hsucc : N + 1 = N₀ + j := by
    dsimp [N]
    omega
  have hself : N = N₀ + (j - 1) := by
    dsimp [N]
    omega
  have hprevNot : ¬ τ (N₀ + (j - 1)) ≤ x := by
    intro hprev
    have hle : j ≤ j - 1 := Nat.find_min' hexshift hprev
    omega
  refine ⟨N, hN, ?_, ?_⟩
  · rw [hsucc]
    exact hj
  · rw [hself]
    exact (not_le.mp hprevNot).le

private theorem squarefreeHalfBoundaryLaplaceBoundedAtZero_of_transportControlledWith
    {M : ℝ → ℝ} {τ : ℕ → ℝ}
    (hM : ∀ q : ℝ, 0 < q → 0 ≤ M q)
    (hinterp : ∀ {x y q : ℝ}, 0 < x → 0 < y → 0 < q → q ≤ x → q ≤ y →
      ‖squarefreeHalfBoundaryLaplaceProfile x -
          squarefreeHalfBoundaryLaplaceProfile y‖ ≤ |x - y| * M q)
    (hτ : SquarefreeHalfBoundaryLaplaceTransportControlledWith M τ) :
    SquarefreeHalfBoundaryLaplaceBoundedAtZero := by
  rcases hτ with ⟨N₀, ε, B, K, hε, hB, hK, hcover, hsamples, htransport⟩
  refine ⟨K + B, ε, add_nonneg hK hB, hε, ?_⟩
  intro x hx hxε
  obtain ⟨N, hN, hlo, hi⟩ := hcover x hx hxε
  obtain ⟨hq, hcost⟩ := htransport N hN
  have hy : 0 < τ N := hq.trans_le (hlo.trans hi)
  have hinterp := hinterp hx hy hq hlo (hlo.trans hi)
  have habs : |x - τ N| ≤ |τ N - τ (N + 1)| := by
    rw [abs_of_nonpos (sub_nonpos.mpr hi),
      abs_of_nonneg (sub_nonneg.mpr (hlo.trans hi))]
    linarith
  have hinterp' :
      ‖squarefreeHalfBoundaryLaplaceProfile x -
          squarefreeHalfBoundaryLaplaceProfile (τ N)‖ ≤ B := by
    refine hinterp.trans ?_
    exact (mul_le_mul_of_nonneg_right habs (hM _ hq)).trans hcost
  have hsample := hsamples N hN
  calc
    ‖squarefreeHalfBoundaryLaplaceProfile x‖ =
        ‖(squarefreeHalfBoundaryLaplaceProfile x -
            squarefreeHalfBoundaryLaplaceProfile (τ N)) +
          squarefreeHalfBoundaryLaplaceProfile (τ N)‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖squarefreeHalfBoundaryLaplaceProfile x -
            squarefreeHalfBoundaryLaplaceProfile (τ N)‖ +
          ‖squarefreeHalfBoundaryLaplaceProfile (τ N)‖ := norm_add_le _ _
    _ ≤ B + K := add_le_add hinterp' hsample
    _ = K + B := add_comm _ _

/-- Controlled scheduled samples force the complete boundary heat profile to be bounded at zero. -/
theorem squarefreeHalfBoundaryLaplaceBoundedAtZero_of_transportControlled
    {τ : ℕ → ℝ}
    (hτ : SquarefreeHalfBoundaryLaplaceTransportControlled τ) :
    SquarefreeHalfBoundaryLaplaceBoundedAtZero := by
  apply squarefreeHalfBoundaryLaplaceBoundedAtZero_of_transportControlledWith
    (M := squarefreeHalfBoundaryLaplaceTransportMoment) (τ := τ)
  · intro q hq
    unfold squarefreeHalfBoundaryLaplaceTransportMoment
    positivity
  · intro x y q hx hy hq hqx hqy
    exact norm_squarefreeHalfBoundaryLaplaceProfile_sub_le hx hy hq hqx hqy
  · exact hτ

/-- Arithmetic-weighted controlled samples also force zero-end boundedness.  The corresponding
mesh condition is weaker because its singular exponent is `16/11`, not `2`. -/
theorem squarefreeHalfBoundaryLaplaceBoundedAtZero_of_weightedTransportControlled
    {τ : ℕ → ℝ}
    (hτ : SquarefreeHalfBoundaryLaplaceWeightedTransportControlled τ) :
    SquarefreeHalfBoundaryLaplaceBoundedAtZero := by
  apply squarefreeHalfBoundaryLaplaceBoundedAtZero_of_transportControlledWith
    (M := squarefreeHalfBoundaryLaplaceWeightedTransportMoment) (τ := τ)
  · intro q hq
    unfold squarefreeHalfBoundaryLaplaceWeightedTransportMoment
    have hgamma : 0 < Real.Gamma (16 / 11 : ℝ) :=
      Real.Gamma_pos_of_pos (by norm_num)
    positivity
  · intro x y q hx hy hq hqx hqy
    exact norm_squarefreeHalfBoundaryLaplaceProfile_sub_le_weighted hx hy hq hqx hqy
  · exact hτ

/-- **Scheduled Laplace no-go.** No heat schedule can simultaneously have bounded late boundary
samples, cover all small heat times, and have bounded adjacent first-moment transport cost. -/
theorem not_squarefreeHalfBoundaryLaplaceTransportControlled (τ : ℕ → ℝ) :
    ¬ SquarefreeHalfBoundaryLaplaceTransportControlled τ := by
  intro hτ
  exact not_squarefreeHalfBoundaryLaplaceBoundedAtZero
    (squarefreeHalfBoundaryLaplaceBoundedAtZero_of_transportControlled hτ)

/-- **Weighted scheduled Laplace no-go.** Even the weaker `16/11` arithmetic transport condition
is incompatible with bounded samples covering all sufficiently small heat times. -/
theorem not_squarefreeHalfBoundaryLaplaceWeightedTransportControlled (τ : ℕ → ℝ) :
    ¬ SquarefreeHalfBoundaryLaplaceWeightedTransportControlled τ := by
  intro hτ
  exact not_squarefreeHalfBoundaryLaplaceBoundedAtZero
    (squarefreeHalfBoundaryLaplaceBoundedAtZero_of_weightedTransportControlled hτ)

/-- For a positive heat clock converging to zero, mesh coverage is automatic.  Therefore bounded
samples and uniformly bounded arithmetic-weighted adjacent cost cannot coexist. -/
theorem not_exists_bounded_samples_and_weighted_transport_of_tendsto_zero
    (τ : ℕ → ℝ) (hpos : ∀ N : ℕ, 0 < τ N)
    (htend : Tendsto τ atTop (𝓝 0)) :
    ¬ ∃ N₀ : ℕ, ∃ B K : ℝ,
      0 ≤ B ∧ 0 ≤ K ∧
      (∀ N : ℕ, N₀ ≤ N → ‖squarefreeHalfBoundaryLaplaceProfile (τ N)‖ ≤ K) ∧
      (∀ N : ℕ, N₀ ≤ N →
        |τ N - τ (N + 1)| *
            squarefreeHalfBoundaryLaplaceWeightedTransportMoment (τ (N + 1)) ≤ B) := by
  rintro ⟨N₀, B, K, hB, hK, hsamples, htransport⟩
  apply not_squarefreeHalfBoundaryLaplaceWeightedTransportControlled τ
  refine ⟨N₀, τ N₀, B, K, hpos N₀, hB, hK, ?_, hsamples, ?_⟩
  · intro x hx hxhead
    exact exists_adjacent_heat_mesh_of_tendsto_zero htend hx hxhead
  · intro N hN
    exact ⟨hpos (N + 1), htransport N hN⟩

/-- A `16/11`-dense adjacent gap directly gives a uniform weighted transport cost once the lower
heat time is at most one. -/
theorem abs_mul_squarefreeHalfBoundaryLaplaceWeightedTransportMoment_le
    {a b C : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hC : 0 ≤ C)
    (hgap : |a - b| ≤ C * b ^ (16 / 11 : ℝ)) :
    |a - b| * squarefreeHalfBoundaryLaplaceWeightedTransportMoment b ≤
      C * (1 + Real.exp 1 * 2 ^ (5 / 11 : ℝ) * Real.Gamma (16 / 11 : ℝ)) := by
  have hgamma : 0 < Real.Gamma (16 / 11 : ℝ) :=
    Real.Gamma_pos_of_pos (by norm_num)
  have hM : 0 ≤ squarefreeHalfBoundaryLaplaceWeightedTransportMoment b := by
    unfold squarefreeHalfBoundaryLaplaceWeightedTransportMoment
    positivity
  have hbp : 0 < b ^ (16 / 11 : ℝ) := Real.rpow_pos_of_pos hb _
  have hbpOne : b ^ (16 / 11 : ℝ) ≤ 1 := by
    simpa using Real.rpow_le_rpow hb.le hb1 (by norm_num : (0 : ℝ) ≤ 16 / 11)
  have hexp : Real.exp b ≤ Real.exp 1 := Real.exp_le_exp.mpr hb1
  have hinvpow :
      (1 / b) ^ (16 / 11 : ℝ) = (b ^ (16 / 11 : ℝ))⁻¹ := by
    rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) hb.le]
    norm_num
  calc
    |a - b| * squarefreeHalfBoundaryLaplaceWeightedTransportMoment b ≤
        (C * b ^ (16 / 11 : ℝ)) *
          squarefreeHalfBoundaryLaplaceWeightedTransportMoment b :=
      mul_le_mul_of_nonneg_right hgap hM
    _ = C * (b ^ (16 / 11 : ℝ) +
        Real.exp b * 2 ^ (5 / 11 : ℝ) * Real.Gamma (16 / 11 : ℝ)) := by
      unfold squarefreeHalfBoundaryLaplaceWeightedTransportMoment
      rw [hinvpow]
      field_simp [hbp.ne']
    _ ≤ C * (1 +
        Real.exp 1 * 2 ^ (5 / 11 : ℝ) * Real.Gamma (16 / 11 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      gcongr

/-- **Weighted mesh escape law.** Along every positive heat clock tending to zero, eventual
boundedness of the canonical boundary samples forces the normalized adjacent gaps to escape every
eventual `O(τ_(N+1)^(16/11))` bound. -/
theorem not_exists_bounded_samples_and_weighted_dense_gaps_of_tendsto_zero
    (τ : ℕ → ℝ) (hpos : ∀ N : ℕ, 0 < τ N)
    (htend : Tendsto τ atTop (𝓝 0)) :
    ¬ ∃ N₀ : ℕ, ∃ C K : ℝ,
      0 ≤ C ∧ 0 ≤ K ∧
      (∀ N : ℕ, N₀ ≤ N → ‖squarefreeHalfBoundaryLaplaceProfile (τ N)‖ ≤ K) ∧
      (∀ N : ℕ, N₀ ≤ N →
        |τ N - τ (N + 1)| ≤ C * (τ (N + 1)) ^ (16 / 11 : ℝ)) := by
  rintro ⟨N₀, C, K, hC, hK, hsamples, hgaps⟩
  have hevent : ∀ᶠ n : ℕ in atTop, τ n < 1 :=
    (tendsto_order.1 htend).2 1 (by norm_num)
  obtain ⟨N₁, hN₁⟩ := (eventually_atTop.1 hevent)
  let N₂ : ℕ := max N₀ N₁
  have hN₂₀ : N₀ ≤ N₂ := le_max_left _ _
  have hN₂₁ : N₁ ≤ N₂ := le_max_right _ _
  apply not_exists_bounded_samples_and_weighted_transport_of_tendsto_zero τ hpos htend
  refine ⟨N₂,
    C * (1 + Real.exp 1 * 2 ^ (5 / 11 : ℝ) * Real.Gamma (16 / 11 : ℝ)),
    K, ?_, hK, ?_, ?_⟩
  · have hgamma : 0 < Real.Gamma (16 / 11 : ℝ) :=
      Real.Gamma_pos_of_pos (by norm_num)
    positivity
  · intro N hN
    exact hsamples N (hN₂₀.trans hN)
  · intro N hN
    apply abs_mul_squarefreeHalfBoundaryLaplaceWeightedTransportMoment_le
    · exact hpos (N + 1)
    · exact (hN₁ (N + 1) (hN₂₁.trans (hN.trans (by omega)))).le
    · exact hC
    · exact hgaps N (hN₂₀.trans hN)

end

end RHTower
