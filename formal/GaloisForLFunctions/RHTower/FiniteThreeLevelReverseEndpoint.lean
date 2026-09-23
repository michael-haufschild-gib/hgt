import GaloisForLFunctions.RHTower.FiniteThreeLevelMomentCarrier

/-!
# Reverse two-level endpoint of the three-level carrier

An `N`-atom head with `N - 1` equal large atoms and one smaller atom
is a positive endpoint of the three-level moment curve.  This endpoint
can lower the cubic target below the equal-share plateau while retaining
exact first and second moments.
-/

namespace RHTower

noncomputable section

/-- The reverse two-level head is inside the genuine positive three-level
spectral cone whenever its two atoms are distinct and nonnegative. -/
theorem threeLevelSpectralFeasible_at_reverseTwoLevel
    {E F a b : ℝ} {N : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b < a)
    (hfirst : ((N : ℝ) - 1) * a + b = E)
    (hsecond : ((N : ℝ) - 1) * a ^ (2 : ℕ) + b ^ (2 : ℕ) = F) :
    ThreeLevelSpectralFeasible E F a N := by
  have hmass : threeLevelResidualMass E a N = a + b := by
    unfold threeLevelResidualMass
    linarith
  have henergy : threeLevelResidualEnergy F a N =
      a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
    unfold threeLevelResidualEnergy
    nlinarith
  refine ⟨ha, ?_, ?_, ?_⟩
  · rw [hmass]
    linarith
  · rw [hmass, henergy]
    nlinarith [sq_pos_of_pos (sub_pos.mpr hba)]
  · rw [hmass, henergy]
    nlinarith [mul_nonneg ha hb]

/-- Along a plateau interval below `E / (N - 1)`, positivity of the two
endpoint carriers and concavity of the residual discriminant keep every
intermediate head positive.  This upgrades a cubic IVT root to a spectral
carrier rather than only an algebraic moment match. -/
theorem threeLevelSpectralFeasible_on_Icc
    {E F p q c : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hpq : p ≤ q)
    (hp : ThreeLevelSpectralFeasible E F p N)
    (hq : ThreeLevelSpectralFeasible E F q N)
    (hqbound : ((N : ℝ) - 1) * q ≤ E)
    (hc : c ∈ Set.Icc p q) :
    ThreeLevelSpectralFeasible E F c N := by
  have hNtwo : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hk : 0 ≤ (N : ℝ) - 2 := by linarith
  have hm : 0 < threeLevelResidualMass E c N := by
    have hqmass := hq.2.1
    have hle : threeLevelResidualMass E q N ≤
        threeLevelResidualMass E c N := by
      unfold threeLevelResidualMass
      nlinarith [mul_nonneg hk (sub_nonneg.mpr hc.2)]
    exact lt_of_lt_of_le hqmass hle
  have hupperFactor : 0 ≤ 2 * E - ((N : ℝ) - 1) * (q + c) := by
    have hNm1 : 0 ≤ (N : ℝ) - 1 := by linarith
    have hprod := mul_le_mul_of_nonneg_left hc.2 hNm1
    nlinarith
  have hgapIdentity :
      threeLevelResidualMass E c N ^ (2 : ℕ) -
          threeLevelResidualEnergy F c N =
        threeLevelResidualMass E q N ^ (2 : ℕ) -
          threeLevelResidualEnergy F q N +
          ((N : ℝ) - 2) * (q - c) *
            (2 * E - ((N : ℝ) - 1) * (q + c)) := by
    unfold threeLevelResidualMass threeLevelResidualEnergy
    ring
  refine ⟨le_trans hp.1 hc.1, hm,
    threeLevel_residual_feasible_on_Icc hN hpq hp.2.2.1 hq.2.2.1 hc, ?_⟩
  have hgapNonneg : 0 ≤
      ((N : ℝ) - 2) * (q - c) *
        (2 * E - ((N : ℝ) - 1) * (q + c)) := by
    exact mul_nonneg
      (mul_nonneg hk (sub_nonneg.mpr hc.2)) hupperFactor
  have hqgap := hq.2.2.2
  linarith [hgapIdentity]

/-- The cubic at the reverse endpoint is twice its literal third power sum. -/
theorem threeLevelCubic_at_reverseTwoLevel
    {E F a b : ℝ} {N : ℕ}
    (hfirst : ((N : ℝ) - 1) * a + b = E)
    (hsecond : ((N : ℝ) - 1) * a ^ (2 : ℕ) + b ^ (2 : ℕ) = F) :
    threeLevelCubic E F N a =
      2 * (((N : ℝ) - 1) * a ^ (3 : ℕ) + b ^ (3 : ℕ)) := by
  unfold threeLevelCubic
  rw [← hfirst, ← hsecond]
  ring

/-- Exact Hankel surplus of the reverse endpoint.  It is strictly above the
generic Cauchy wall when both atom values are positive and distinct.  Thus
source Hankel positivity alone does not guarantee a cubic bracket. -/
theorem reverseTwoLevel_cauchy_surplus
    {E F a b : ℝ} {N : ℕ}
    (hfirst : ((N : ℝ) - 1) * a + b = E)
    (hsecond : ((N : ℝ) - 1) * a ^ (2 : ℕ) + b ^ (2 : ℕ) = F) :
    E * (((N : ℝ) - 1) * a ^ (3 : ℕ) + b ^ (3 : ℕ)) - F ^ (2 : ℕ) =
      ((N : ℝ) - 1) * a * b * (a - b) ^ (2 : ℕ) := by
  rw [← hfirst, ← hsecond]
  ring

/-- Variance identity for a reverse two-level head; it pins its atom count
above the effective rank `E²/F`. -/
theorem reverseTwoLevel_variance_identity
    {E F a b : ℝ} {N : ℕ}
    (hfirst : ((N : ℝ) - 1) * a + b = E)
    (hsecond : ((N : ℝ) - 1) * a ^ (2 : ℕ) + b ^ (2 : ℕ) = F) :
    (N : ℝ) * F - E ^ (2 : ℕ) =
      ((N : ℝ) - 1) * (a - b) ^ (2 : ℕ) := by
  rw [← hfirst, ← hsecond]
  ring

/-- Exact amount by which the reverse endpoint lowers the equal-share cubic. -/
theorem threeLevelCubic_reverse_lt_mean
    {E F a b : ℝ} {N : ℕ} (hN : 3 ≤ N) (hba : b < a)
    (hfirst : ((N : ℝ) - 1) * a + b = E)
    (hsecond : ((N : ℝ) - 1) * a ^ (2 : ℕ) + b ^ (2 : ℕ) = F) :
    threeLevelCubic E F N a < threeLevelCubic E F N (E / (N : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  have hNm1 : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    linarith
  have hNm2 : (0 : ℝ) < (N : ℝ) - 2 := by
    have : (2 : ℝ) < N := by exact_mod_cast (show 2 < N by omega)
    linarith
  have hid :
      threeLevelCubic E F N (E / (N : ℝ)) - threeLevelCubic E F N a =
        2 * ((N : ℝ) - 1) * ((N : ℝ) - 2) * (a - b) ^ (3 : ℕ) /
          (N : ℝ) ^ (2 : ℕ) := by
    unfold threeLevelCubic
    rw [← hfirst, ← hsecond]
    field_simp [hNpos.ne']
    ring
  have hdiff : 0 <
      2 * ((N : ℝ) - 1) * ((N : ℝ) - 2) * (a - b) ^ (3 : ℕ) /
        (N : ℝ) ^ (2 : ℕ) := by
    have hd : 0 < a - b := sub_pos.mpr hba
    positivity
  linarith

/-- The exact source inequality required for the lower cubic bracket at a
reverse endpoint.  The source Hankel margin must pay the atom gap shown on
the right; mere strict positivity of that margin is insufficient. -/
theorem reverseTwoLevel_lowerBracket_iff_hankelMargin
    {E F G a b : ℝ} {N : ℕ} (hE : 0 < E)
    (hfirst : ((N : ℝ) - 1) * a + b = E)
    (hsecond : ((N : ℝ) - 1) * a ^ (2 : ℕ) + b ^ (2 : ℕ) = F) :
    threeLevelCubic E F N a ≤ 2 * G ↔
      ((N : ℝ) - 1) * a * b * (a - b) ^ (2 : ℕ) ≤
        E * G - F ^ (2 : ℕ) := by
  rw [threeLevelCubic_at_reverseTwoLevel hfirst hsecond]
  have hid := reverseTwoLevel_cauchy_surplus hfirst hsecond
  constructor
  · intro h
    have hCG : ((N : ℝ) - 1) * a ^ (3 : ℕ) + b ^ (3 : ℕ) ≤ G := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hCG hE.le
    linarith
  · intro h
    have hCG : ((N : ℝ) - 1) * a ^ (3 : ℕ) + b ^ (3 : ℕ) ≤ G := by
      nlinarith [hid]
    linarith

/-- A reverse two-level endpoint exists precisely in the finite-rank window
where the exceptional small atom stays nonnegative.  The two scalar moments
are matched exactly, without an asymptotic approximation. -/
theorem exists_reverseTwoLevelEndpoint
    {E F : ℝ} {N : ℕ} (hE : 0 < E) (hN : 2 ≤ N)
    (hlow : E ^ (2 : ℕ) / (N : ℝ) < F)
    (hhigh : F ≤ E ^ (2 : ℕ) / ((N : ℝ) - 1)) :
    ∃ a b : ℝ, 0 ≤ b ∧ b < a ∧
      ((N : ℝ) - 1) * a + b = E ∧
      ((N : ℝ) - 1) * a ^ (2 : ℕ) + b ^ (2 : ℕ) = F ∧
      ThreeLevelSpectralFeasible E F a N := by
  let d := twoLevelDeviation E F N
  let a := (E + d) / (N : ℝ)
  let b := (E - ((N : ℝ) - 1) * d) / (N : ℝ)
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := by linarith
  have hNm1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hdpos : 0 < d := twoLevelDeviation_pos_of_strictFloor hN hlow
  have hdsq : ((N : ℝ) - 1) * d ^ (2 : ℕ) =
      (N : ℝ) * F - E ^ (2 : ℕ) := by
    have h := twoLevelDeviation_sq hN hlow
    calc
      ((N : ℝ) - 1) * d ^ (2 : ℕ) = d ^ (2 : ℕ) * ((N : ℝ) - 1) := by ring
      _ = (N : ℝ) * F - E ^ (2 : ℕ) := (eq_div_iff hNm1.ne').1 h
  have hFbound : ((N : ℝ) - 1) * F ≤ E ^ (2 : ℕ) :=
    by simpa only [mul_comm] using (le_div_iff₀ hNm1).1 hhigh
  have hdBoundSq : (((N : ℝ) - 1) * d) ^ (2 : ℕ) ≤ E ^ (2 : ℕ) := by
    have hscale := mul_le_mul_of_nonneg_left hFbound hNpos.le
    have hdsqScaled := congrArg (fun t : ℝ => ((N : ℝ) - 1) * t) hdsq
    nlinarith [hdsqScaled]
  have hdBound : ((N : ℝ) - 1) * d ≤ E := by
    have hprod : 0 ≤ ((N : ℝ) - 1) * d := mul_nonneg hNm1.le hdpos.le
    nlinarith
  have hb : 0 ≤ b := by
    dsimp [b]
    exact div_nonneg (sub_nonneg.mpr hdBound) hNpos.le
  have hba : b < a := by
    dsimp [a, b]
    apply (div_lt_div_iff₀ hNpos hNpos).2
    nlinarith [mul_pos hNpos hdpos]
  have hfirst : ((N : ℝ) - 1) * a + b = E := by
    dsimp [a, b]
    field_simp [hNpos.ne']
    ring
  have hsecond : ((N : ℝ) - 1) * a ^ (2 : ℕ) + b ^ (2 : ℕ) = F := by
    have hscaled :
        (N : ℝ) * (((N : ℝ) - 1) * a ^ (2 : ℕ) + b ^ (2 : ℕ)) =
          E ^ (2 : ℕ) + ((N : ℝ) - 1) * d ^ (2 : ℕ) := by
      dsimp [a, b]
      field_simp [hNpos.ne']
      ring
    nlinarith [hdsq]
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  exact ⟨a, b, hb, hba, hfirst, hsecond,
    threeLevelSpectralFeasible_at_reverseTwoLevel ha hb hba hfirst hsecond⟩

/-- Any positive first two moments with effective rank at least two have
an admissible reverse endpoint at the first integer above that rank. -/
theorem exists_reverseTwoLevelEndpoint_at_effectiveRank
    {E F : ℝ} (hE : 0 < E) (hF : 0 < F)
    (hrank : 2 * F ≤ E ^ (2 : ℕ)) :
    ∃ N : ℕ, 3 ≤ N ∧ ∃ a b : ℝ, 0 ≤ b ∧ b < a ∧
      ((N : ℝ) - 1) * a + b = E ∧
      ((N : ℝ) - 1) * a ^ (2 : ℕ) + b ^ (2 : ℕ) = F ∧
      ThreeLevelSpectralFeasible E F a N := by
  let r : ℝ := E ^ (2 : ℕ) / F
  let N : ℕ := ⌊r⌋₊ + 1
  have hrnonneg : 0 ≤ r := by positivity
  have hrankReal : (2 : ℝ) ≤ r := by
    dsimp [r]
    exact (le_div_iff₀ hF).2 (by nlinarith)
  have hfloorTwo : 2 ≤ ⌊r⌋₊ := Nat.le_floor hrankReal
  have hN : 3 ≤ N := by dsimp [N]; omega
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  have hNm1 : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    linarith
  have hRlower : (N : ℝ) - 1 ≤ r := by
    have hfloor := Nat.floor_le hrnonneg
    dsimp [N]
    push_cast
    linarith
  have hRupper : r < (N : ℝ) := by
    have hfloor := Nat.lt_floor_add_one r
    dsimp [N]
    push_cast
    exact hfloor
  have hratio : r * F = E ^ (2 : ℕ) := by
    dsimp [r]
    field_simp [hF.ne']
  have hlow : E ^ (2 : ℕ) / N < F := by
    apply (div_lt_iff₀ hNpos).2
    have hscaled := mul_lt_mul_of_pos_right hRupper hF
    nlinarith [hscaled, hratio]
  have hhigh : F ≤ E ^ (2 : ℕ) / ((N : ℝ) - 1) := by
    apply (le_div_iff₀ hNm1).2
    have hscaled := mul_le_mul_of_nonneg_right hRlower hF.le
    nlinarith [hscaled, hratio]
  obtain ⟨a, b, hb, hba, hfirst, hsecond, hfeasible⟩ :=
    exists_reverseTwoLevelEndpoint hE (by omega : 2 ≤ N) hlow hhigh
  exact ⟨N, hN, a, b, hb, hba, hfirst, hsecond, hfeasible⟩

end

end RHTower
