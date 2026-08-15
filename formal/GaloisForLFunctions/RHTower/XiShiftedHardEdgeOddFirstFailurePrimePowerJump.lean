import GaloisForLFunctions.RHTower.XiShiftedHardEdgeDensityMeasure

/-!
# Prime-power quantization of Route-U odd first failure

The literal hard-edge density depends on aperture only through
`floor (exp (2 * sigma))`.  It is constant inside every cutoff chamber.  At
`sigma = log n / 2`, its right-continuous value differs from the incoming chamber by exactly one
von Mangoldt cosine atom.

Consequently a fixed odd state that is nonnegative at every strictly smaller aperture but negative
at `sigma` can fail only at a prime-power wall: `sigma = log n / 2` with `Lambda(n) != 0`.  Under
the natural integrability hypotheses, the exact newly entering prime-power response is strictly
positive.  No RH premise or numerical computation is used.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

theorem routeUHardEdgeDensity_eq_of_frequencyBound_eq
    {σ τ : ℝ} (hbound : routeUHardEdgeFrequencyBound σ = routeUHardEdgeFrequencyBound τ) :
    routeUHardEdgeDensity σ = routeUHardEdgeDensity τ := by
  funext x
  simp only [routeUHardEdgeDensity, hbound]

theorem routeUHardEdgePairing_eq_of_frequencyBound_eq
    {σ τ : ℝ} (hbound : routeUHardEdgeFrequencyBound σ = routeUHardEdgeFrequencyBound τ)
    (Φ : ℝ → ℝ) :
    routeUHardEdgePairing σ Φ = routeUHardEdgePairing τ Φ := by
  rw [routeUHardEdgePairing, routeUHardEdgePairing,
    routeUHardEdgeDensity_eq_of_frequencyBound_eq hbound]

theorem routeUHardEdgeOddForm_eq_of_frequencyBound_eq
    {σ τ : ℝ} (hbound : routeUHardEdgeFrequencyBound σ = routeUHardEdgeFrequencyBound τ)
    (H K : ℝ → ℝ) :
    routeUHardEdgeOddForm σ H K = routeUHardEdgeOddForm τ H K := by
  exact routeUHardEdgePairing_eq_of_frequencyBound_eq hbound _

theorem routeUHardEdgeDensity_eq_of_adjacent_frequencyBounds_of_vonMangoldt_eq_zero
    {σ τ : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hσ : routeUHardEdgeFrequencyBound σ = n)
    (hτ : routeUHardEdgeFrequencyBound τ = n - 1)
    (hΛ : ArithmeticFunction.vonMangoldt n = 0) :
    routeUHardEdgeDensity σ = routeUHardEdgeDensity τ := by
  funext x
  rw [routeUHardEdgeDensity, routeUHardEdgeDensity, hσ, hτ]
  let f : ℕ → ℝ := fun m =>
    (ArithmeticFunction.vonMangoldt m : ℝ) / Real.sqrt m * Real.cos (x * Real.log m)
  have hsum := Finset.sum_Icc_succ_top (a := 2) (b := n - 1) (by omega) f
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hsum
  change routeUArchimedeanRate x - ∑ m ∈ Finset.Icc 2 n, f m =
    routeUArchimedeanRate x - ∑ m ∈ Finset.Icc 2 (n - 1), f m
  rw [hsum]
  have hfn : f n = 0 := by simp [f, hΛ]
  rw [hfn, add_zero]

theorem routeUHardEdgeOddForm_eq_of_adjacent_frequencyBounds_of_vonMangoldt_eq_zero
    {σ τ : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hσ : routeUHardEdgeFrequencyBound σ = n)
    (hτ : routeUHardEdgeFrequencyBound τ = n - 1)
    (hΛ : ArithmeticFunction.vonMangoldt n = 0)
    (H K : ℝ → ℝ) :
    routeUHardEdgeOddForm σ H K = routeUHardEdgeOddForm τ H K := by
  unfold routeUHardEdgeOddForm routeUHardEdgePairing
  rw [routeUHardEdgeDensity_eq_of_adjacent_frequencyBounds_of_vonMangoldt_eq_zero
    hn hσ hτ hΛ]

theorem routeUHardEdgeFrequencyBound_log_nat_half {n : ℕ} (hn : 1 ≤ n) :
    routeUHardEdgeFrequencyBound (Real.log n / 2) = n := by
  rw [routeUHardEdgeFrequencyBound]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  rw [show 2 * (Real.log n / 2) = Real.log n by ring,
    Real.exp_log hnpos, Nat.floor_natCast]

def routeUHardEdgeIncomingAperture (n : ℕ) : ℝ :=
  Real.log ((n : ℝ) - 1 / 2) / 2

theorem routeUHardEdgeFrequencyBound_incomingAperture {n : ℕ} (hn : 2 ≤ n) :
    routeUHardEdgeFrequencyBound (routeUHardEdgeIncomingAperture n) = n - 1 := by
  rw [routeUHardEdgeFrequencyBound, routeUHardEdgeIncomingAperture]
  have hncast : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hypos : (0 : ℝ) < (n : ℝ) - 1 / 2 := by linarith
  rw [show 2 * (Real.log ((n : ℝ) - 1 / 2) / 2) =
      Real.log ((n : ℝ) - 1 / 2) by ring,
    Real.exp_log hypos]
  apply (Nat.floor_eq_iff hypos.le).2
  have hcast : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  rw [hcast]
  constructor <;> linarith

theorem routeUHardEdgeIncomingAperture_lt_log_nat_half {n : ℕ} (hn : 2 ≤ n) :
    routeUHardEdgeIncomingAperture n < Real.log n / 2 := by
  rw [routeUHardEdgeIncomingAperture]
  have hncast : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hypos : (0 : ℝ) < (n : ℝ) - 1 / 2 := by linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hn)
  have hylt : (n : ℝ) - 1 / 2 < (n : ℝ) := by norm_num
  have hlog := Real.strictMonoOn_log hypos hnpos hylt
  linarith

/-- The one new literal source atom entering at the `n`th hard-edge cutoff. -/
def routeUHardEdgePrimeJumpDensity (n : ℕ) (x : ℝ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
    Real.cos (x * Real.log n)

/-- Exact right-continuous density jump at the `n`th cutoff. -/
theorem routeUHardEdgeDensity_log_nat_half_eq_incoming_sub_primeJump
    {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    routeUHardEdgeDensity (Real.log n / 2) x =
      routeUHardEdgeDensity (routeUHardEdgeIncomingAperture n) x -
        routeUHardEdgePrimeJumpDensity n x := by
  rw [routeUHardEdgeDensity, routeUHardEdgeDensity,
    routeUHardEdgeFrequencyBound_log_nat_half (by omega : 1 ≤ n),
    routeUHardEdgeFrequencyBound_incomingAperture hn]
  let f : ℕ → ℝ := fun m =>
    (ArithmeticFunction.vonMangoldt m : ℝ) / Real.sqrt m * Real.cos (x * Real.log m)
  have hsum := Finset.sum_Icc_succ_top (a := 2) (b := n - 1) (by omega) f
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hsum
  change routeUArchimedeanRate x - ∑ m ∈ Finset.Icc 2 n, f m =
    routeUArchimedeanRate x - ∑ m ∈ Finset.Icc 2 (n - 1), f m -
      routeUHardEdgePrimeJumpDensity n x
  rw [hsum]
  unfold routeUHardEdgePrimeJumpDensity
  dsimp [f]
  ring

/-- Odd response of one newly entering von Mangoldt source atom. -/
def routeUHardEdgePrimeJumpOddResponse (n : ℕ) (H K : ℝ → ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ),
    u * (H u * K u) * routeUHardEdgePrimeJumpDensity n (Real.sqrt u) / Real.sqrt u

/-- Exact odd-form jump law, under only the two integrability conditions required for integral
linearity. -/
theorem routeUHardEdgeOddForm_log_nat_half_eq_incoming_sub_primeJumpResponse
    {n : ℕ} (hn : 2 ≤ n) (H K : ℝ → ℝ)
    (hbase : IntegrableOn (fun u : ℝ =>
      u * (H u * K u) *
        routeUHardEdgeDensity (routeUHardEdgeIncomingAperture n) (Real.sqrt u) /
          Real.sqrt u) (Ioi 0))
    (hjump : IntegrableOn (fun u : ℝ =>
      u * (H u * K u) * routeUHardEdgePrimeJumpDensity n (Real.sqrt u) /
        Real.sqrt u) (Ioi 0)) :
    routeUHardEdgeOddForm (Real.log n / 2) H K =
      routeUHardEdgeOddForm (routeUHardEdgeIncomingAperture n) H K -
        routeUHardEdgePrimeJumpOddResponse n H K := by
  unfold routeUHardEdgeOddForm routeUHardEdgePairing
  have hint :
      (∫ u in Ioi (0 : ℝ),
        u * (H u * K u) *
          routeUHardEdgeDensity (Real.log n / 2) (Real.sqrt u) / Real.sqrt u) =
      (∫ u in Ioi (0 : ℝ),
        u * (H u * K u) *
          routeUHardEdgeDensity (routeUHardEdgeIncomingAperture n) (Real.sqrt u) /
            Real.sqrt u) -
      ∫ u in Ioi (0 : ℝ),
        u * (H u * K u) * routeUHardEdgePrimeJumpDensity n (Real.sqrt u) /
          Real.sqrt u := by
    rw [← integral_sub hbase hjump]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [routeUHardEdgeDensity_log_nat_half_eq_incoming_sub_primeJump hn]
    ring
  rw [hint]
  unfold routeUHardEdgePrimeJumpOddResponse
  ring

theorem routeUHardEdgePrimeJumpOddResponse_pos_of_sign_loss
    {n : ℕ} (hn : 2 ≤ n) (H : ℝ → ℝ)
    (hbase : IntegrableOn (fun u : ℝ =>
      u * (H u * H u) *
        routeUHardEdgeDensity (routeUHardEdgeIncomingAperture n) (Real.sqrt u) /
          Real.sqrt u) (Ioi 0))
    (hjump : IntegrableOn (fun u : ℝ =>
      u * (H u * H u) * routeUHardEdgePrimeJumpDensity n (Real.sqrt u) /
        Real.sqrt u) (Ioi 0))
    (hincoming : 0 ≤ routeUHardEdgeOddForm (routeUHardEdgeIncomingAperture n) H H)
    (hafter : routeUHardEdgeOddForm (Real.log n / 2) H H < 0) :
    0 < routeUHardEdgePrimeJumpOddResponse n H H := by
  have hjumpLaw :=
    routeUHardEdgeOddForm_log_nat_half_eq_incoming_sub_primeJumpResponse
      hn H H hbase hjump
  linarith

/-- A first odd-sector sign loss can occur only when a literal prime-power source atom enters the
hard-edge cutoff. -/
theorem exists_primePower_of_routeUOddForm_firstFailure
    {σ : ℝ}
    (hbound : 2 ≤ routeUHardEdgeFrequencyBound σ)
    (H : ℝ → ℝ)
    (hneg : routeUHardEdgeOddForm σ H H < 0)
    (hbefore : ∀ τ : ℝ, τ < σ → 0 ≤ routeUHardEdgeOddForm τ H H) :
    ∃ n : ℕ, IsPrimePow n ∧ 2 ≤ n ∧ σ = Real.log n / 2 := by
  let X : ℝ := Real.exp (2 * σ)
  let n : ℕ := routeUHardEdgeFrequencyBound σ
  have hfloor : n = ⌊X⌋₊ := by rfl
  have hXpos : 0 < X := Real.exp_pos _
  have hnX : (n : ℝ) ≤ X := by
    rw [hfloor]
    exact Nat.floor_le hXpos.le
  have hXn : X < (n : ℝ) + 1 := by
    rw [hfloor]
    exact Nat.lt_floor_add_one X
  have hXeq : X = (n : ℝ) := by
    by_contra hne
    have hnltX : (n : ℝ) < X := lt_of_le_of_ne hnX (Ne.symm hne)
    let Y : ℝ := ((n : ℝ) + X) / 2
    let τ : ℝ := Real.log Y / 2
    have hYpos : 0 < Y := by dsimp [Y]; linarith
    have hnY : (n : ℝ) ≤ Y := by dsimp [Y]; linarith
    have hYn1 : Y < (n : ℝ) + 1 := by dsimp [Y]; linarith
    have hYltX : Y < X := by dsimp [Y]; linarith
    have hτlt : τ < σ := by
      have hlog := Real.strictMonoOn_log hYpos hXpos hYltX
      have hlogX : Real.log X = 2 * σ := by
        dsimp [X]
        rw [Real.log_exp]
      dsimp [τ]
      linarith
    have hτbound : routeUHardEdgeFrequencyBound τ = n := by
      rw [routeUHardEdgeFrequencyBound]
      have hexp : Real.exp (2 * τ) = Y := by
        dsimp [τ]
        rw [show 2 * (Real.log Y / 2) = Real.log Y by ring,
          Real.exp_log hYpos]
      rw [hexp]
      exact (Nat.floor_eq_iff hYpos.le).2 ⟨hnY, hYn1⟩
    have hsame : routeUHardEdgeOddForm σ H H = routeUHardEdgeOddForm τ H H := by
      apply routeUHardEdgeOddForm_eq_of_frequencyBound_eq
      rw [hτbound]
    have hnonneg := hbefore τ hτlt
    rw [← hsame] at hnonneg
    linarith
  have hn : 2 ≤ n := hbound
  have hσeq : σ = Real.log n / 2 := by
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hn)
    have hlog := congrArg Real.log hXeq
    dsimp [X] at hlog
    rw [Real.log_exp] at hlog
    linarith
  have hτlt := routeUHardEdgeIncomingAperture_lt_log_nat_half hn
  have hτbound := routeUHardEdgeFrequencyBound_incomingAperture hn
  have hσbound : routeUHardEdgeFrequencyBound σ = n := by rfl
  have hΛ : ArithmeticFunction.vonMangoldt n ≠ 0 := by
    intro hzero
    have hsame :=
      routeUHardEdgeOddForm_eq_of_adjacent_frequencyBounds_of_vonMangoldt_eq_zero
        hn hσbound hτbound hzero H H
    have hnonneg := hbefore (routeUHardEdgeIncomingAperture n) (by rwa [hσeq])
    rw [← hsame] at hnonneg
    linarith
  exact ⟨n, ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ, hn, hσeq⟩

end

end RHTower
