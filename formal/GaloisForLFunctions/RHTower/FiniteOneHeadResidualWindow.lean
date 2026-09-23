import GaloisForLFunctions.RHTower.FiniteTwoLevelMomentCarrier

/-!
# One-atom sweep of a positive finite moment head

Fixing one atom at `x` leaves `E - x` mass and `F - x²` quadratic energy
for `N - 1` atoms.  The Cauchy admission budget is a concave quadratic in
`x`, so an admitted pair of endpoint heads admits every intermediate value
of the distinguished atom.  This is the first common-count ingredient for
moving a padded reverse K-RVM head toward a large-count upper head.
-/

namespace RHTower

noncomputable section

/-- Cauchy budget for the remaining `N - 1` atoms after fixing one atom. -/
def oneHeadResidualBudget (E F : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ((N : ℝ) - 1) * (F - x ^ (2 : ℕ)) - (E - x) ^ (2 : ℕ)

theorem oneHeadResidualBudget_chord_identity
    (E F : ℝ) (N : ℕ) (a b c : ℝ) :
    (b - a) * oneHeadResidualBudget E F N c =
      (b - c) * oneHeadResidualBudget E F N a +
        (c - a) * oneHeadResidualBudget E F N b +
          (N : ℝ) * (b - a) * (c - a) * (b - c) := by
  unfold oneHeadResidualBudget
  ring

/-- Completing the square identifies the two-level large atom as the
upper edge of the one-coordinate Cauchy window. -/
theorem oneHeadResidualBudget_scaled_identity
    (E F x : ℝ) (N : ℕ) :
    (N : ℝ) * oneHeadResidualBudget E F N x =
      ((N : ℝ) - 1) * ((N : ℝ) * F - E ^ (2 : ℕ)) -
        ((N : ℝ) * x - E) ^ (2 : ℕ) := by
  unfold oneHeadResidualBudget
  ring

/-- No coordinate of an admitted `N`-atom first/second-moment head can
exceed the large atom of the two-level head with the same moments. -/
theorem oneHeadResidualBudget_le_twoLevelLarge
    {E F x : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hlow : E ^ (2 : ℕ) / (N : ℝ) < F)
    (hbudget : 0 ≤ oneHeadResidualBudget E F N x) :
    x ≤ twoLevelLarge E F N := by
  let d := twoLevelDeviation E F N
  have hnpos : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  have hkpos : 0 ≤ (N : ℝ) - 1 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    linarith
  have hdpos : 0 ≤ d := twoLevelDeviation_nonneg E F N
  have hdsq := twoLevelDeviation_sq hN hlow
  have hkne : (N : ℝ) - 1 ≠ 0 := by
    have hNgt : (1 : ℝ) < N := by
      exact_mod_cast (show 1 < N by omega)
    linarith
  have hdsq' : ((N : ℝ) - 1) * d ^ (2 : ℕ) =
      (N : ℝ) * F - E ^ (2 : ℕ) := by
    calc
      ((N : ℝ) - 1) * d ^ (2 : ℕ) = d ^ (2 : ℕ) * ((N : ℝ) - 1) := by ring
      _ = (N : ℝ) * F - E ^ (2 : ℕ) := (eq_div_iff hkne).1 hdsq
  have hdsqScaled :
      (((N : ℝ) - 1) * d) ^ (2 : ℕ) =
        ((N : ℝ) - 1) * ((N : ℝ) * F - E ^ (2 : ℕ)) := by
    have h := congrArg (fun t : ℝ => ((N : ℝ) - 1) * t) hdsq'
    nlinarith
  have hsq : ((N : ℝ) * x - E) ^ (2 : ℕ) ≤
      (((N : ℝ) - 1) * d) ^ (2 : ℕ) := by
    have hscaled := oneHeadResidualBudget_scaled_identity E F x N
    nlinarith [mul_nonneg hnpos.le hbudget]
  have hlinear : (N : ℝ) * x - E ≤ ((N : ℝ) - 1) * d := by
    have hkd : 0 ≤ ((N : ℝ) - 1) * d := mul_nonneg hkpos hdpos
    nlinarith
  change x ≤ (E + ((N : ℝ) - 1) * d) / (N : ℝ)
  exact (le_div_iff₀ hnpos).2 (by linarith)

/-- The source's effective-rank gap `E² > 9F` keeps the large two-level
atom below one third of total mass, the range needed for both residual
positive-cone and rank-two monotonicity. -/
theorem twoLevelLarge_lt_third_mass_of_nine_energy_lt_mass_sq
    {E F : ℝ} {N : ℕ} (hE : 0 < E) (hN : 2 ≤ N)
    (hlow : E ^ (2 : ℕ) / (N : ℝ) < F)
    (h9 : 9 * F < E ^ (2 : ℕ)) :
    3 * twoLevelLarge E F N < E := by
  have hk : 0 ≤ (N : ℝ) - 1 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    linarith
  have hsecond := twoLevel_secondMoment (E := E) (F := F) hN hlow
  have htail : 0 ≤ ((N : ℝ) - 1) * twoLevelSmall E F N ^ (2 : ℕ) :=
    mul_nonneg hk (sq_nonneg _)
  have hLsq : twoLevelLarge E F N ^ (2 : ℕ) ≤ F := by linarith
  have hLpos := twoLevelLarge_pos (F := F) hE hN
  nlinarith

/-- The feasible distinguished-atom range has no Cauchy-budget gap. -/
theorem oneHeadResidualBudget_nonneg_on_Icc
    {E F a b c : ℝ} {N : ℕ} (hab : a ≤ b)
    (ha : 0 ≤ oneHeadResidualBudget E F N a)
    (hb : 0 ≤ oneHeadResidualBudget E F N b)
    (hc : c ∈ Set.Icc a b) :
    0 ≤ oneHeadResidualBudget E F N c := by
  by_cases heq : a = b
  · subst b
    have hca : c = a := le_antisymm hc.2 hc.1
    subst c
    exact ha
  have hablt : a < b := lt_of_le_of_ne hab heq
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hbc : 0 ≤ b - c := sub_nonneg.mpr hc.2
  have hca : 0 ≤ c - a := sub_nonneg.mpr hc.1
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hscaled : 0 ≤ (b - a) * oneHeadResidualBudget E F N c := by
    rw [oneHeadResidualBudget_chord_identity]
    have hleft := mul_nonneg hbc ha
    have hright := mul_nonneg hca hb
    have htail : 0 ≤ (N : ℝ) * (b - a) * (c - a) * (b - c) := by
      positivity
    positivity
  by_contra hnot
  have hneg : oneHeadResidualBudget E F N c < 0 := lt_of_not_ge hnot
  have hprodneg := mul_neg_of_pos_of_neg (sub_pos.mpr hablt) hneg
  exact (not_lt_of_ge hscaled) hprodneg

/-- Positivity of a distinguished atom and of both residual moments,
together with both sides of the residual positive moment cone. -/
def OneHeadResidualAdmissible (E F : ℝ) (N : ℕ) (x : ℝ) : Prop :=
  0 ≤ x ∧ 0 < E - x ∧ 0 < F - x ^ (2 : ℕ) ∧
    0 ≤ oneHeadResidualBudget E F N x ∧
      F - x ^ (2 : ℕ) ≤ (E - x) ^ (2 : ℕ)

/-- An admitted one-atom sweep stays admitted while its largest fixed atom
does not exceed half the mass.  That bound makes the residual upper cone
monotone along the interval. -/
theorem oneHeadResidualAdmissible_on_Icc
    {E F a b c : ℝ} {N : ℕ} (hab : a ≤ b)
    (hbhalf : 2 * b ≤ E)
    (ha : OneHeadResidualAdmissible E F N a)
    (hb : OneHeadResidualAdmissible E F N b)
    (hc : c ∈ Set.Icc a b) :
    OneHeadResidualAdmissible E F N c := by
  rcases ha with ⟨ha0, _, _, habudget, _⟩
  rcases hb with ⟨hb0, hbmass, hbenergy, hbbudget, hbupper⟩
  have hc0 : 0 ≤ c := le_trans ha0 hc.1
  have hmass : 0 < E - c := by linarith [hc.2]
  have hsq : c ^ (2 : ℕ) ≤ b ^ (2 : ℕ) := by
    have hprod := mul_nonneg (sub_nonneg.mpr hc.2)
      (add_nonneg hc0 hb0)
    nlinarith
  have henergy : 0 < F - c ^ (2 : ℕ) := by linarith
  have hupperIdentity :
      (E - c) ^ (2 : ℕ) - (F - c ^ (2 : ℕ)) =
        (E - b) ^ (2 : ℕ) - (F - b ^ (2 : ℕ)) +
          2 * (b - c) * (E - (b + c)) := by
    ring
  have hfactor : 0 ≤ E - (b + c) := by linarith [hc.2]
  have htail : 0 ≤ 2 * (b - c) * (E - (b + c)) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (sub_nonneg.mpr hc.2)) hfactor
  have hupper : F - c ^ (2 : ℕ) ≤ (E - c) ^ (2 : ℕ) := by
    linarith [hupperIdentity]
  exact ⟨hc0, hmass, henergy,
    oneHeadResidualBudget_nonneg_on_Icc hab habudget hbbudget hc, hupper⟩

/-- When the distinguished atom stays below one third of total mass,
the residual effective rank cannot cross below two if the upper endpoint
has rank at least two.  This keeps the reverse residual carrier available
throughout the one-atom sweep. -/
theorem oneHeadResidualRankTwo_on_Icc
    {E F b c : ℝ} (hcb : c ≤ b) (hbthird : 3 * b ≤ E)
    (hbrank : 2 * (F - b ^ (2 : ℕ)) ≤ (E - b) ^ (2 : ℕ)) :
    2 * (F - c ^ (2 : ℕ)) ≤ (E - c) ^ (2 : ℕ) := by
  have hid :
      (E - c) ^ (2 : ℕ) - 2 * (F - c ^ (2 : ℕ)) =
        (E - b) ^ (2 : ℕ) - 2 * (F - b ^ (2 : ℕ)) +
          (b - c) * (2 * E - 3 * (b + c)) := by
    ring
  have hfactor : 0 ≤ 2 * E - 3 * (b + c) := by linarith
  have htail : 0 ≤ (b - c) * (2 * E - 3 * (b + c)) :=
    mul_nonneg (sub_nonneg.mpr hcb) hfactor
  linarith [hid]

end

end RHTower
