import GaloisForLFunctions.RHTower.FiniteTwoLevelMomentCarrier

/-!
# Exact finite three-level moment carrier

Keep `N - 2` atoms at a free plateau `c`, and solve the remaining first and second moments by
the exact two-level construction.  The resulting third power sum is an explicit cubic in `c`.
This is the degree-three algebraic mechanism required to extend the K-RVM head beyond its current
quadratic and quartic incidence.
-/

namespace RHTower

noncomputable section

/-- The mass remaining after placing `N - 2` atoms at a plateau `c`. -/
def threeLevelResidualMass (E c : ℝ) (N : ℕ) : ℝ :=
  E - ((N : ℝ) - 2) * c

/-- The quadratic energy remaining after the plateau. -/
def threeLevelResidualEnergy (F c : ℝ) (N : ℕ) : ℝ :=
  F - ((N : ℝ) - 2) * c ^ (2 : ℕ)

/-- First exceptional atom of the three-level carrier. -/
def threeLevelLarge (E F c : ℝ) (N : ℕ) : ℝ :=
  twoLevelLarge (threeLevelResidualMass E c N)
    (threeLevelResidualEnergy F c N) 2

/-- Second exceptional atom of the three-level carrier. -/
def threeLevelMiddle (E F c : ℝ) (N : ℕ) : ℝ :=
  twoLevelSmall (threeLevelResidualMass E c N)
    (threeLevelResidualEnergy F c N) 2

theorem threeLevel_firstMoment (E F c : ℝ) (N : ℕ) :
    threeLevelLarge E F c N + threeLevelMiddle E F c N +
        ((N : ℝ) - 2) * c = E := by
  have hpair :
      twoLevelLarge (threeLevelResidualMass E c N)
          (threeLevelResidualEnergy F c N) 2 +
        twoLevelSmall (threeLevelResidualMass E c N)
          (threeLevelResidualEnergy F c N) 2 =
        threeLevelResidualMass E c N := by
    convert twoLevel_firstMoment (E := threeLevelResidualMass E c N)
      (F := threeLevelResidualEnergy F c N) (by norm_num : 2 ≤ 2) using 1
    all_goals norm_num
  rw [threeLevelLarge, threeLevelMiddle, hpair]
  simp only [threeLevelResidualMass]
  ring

theorem threeLevel_secondMoment
    {E F c : ℝ} {N : ℕ}
    (hres : threeLevelResidualMass E c N ^ (2 : ℕ) / 2 <
      threeLevelResidualEnergy F c N) :
    threeLevelLarge E F c N ^ (2 : ℕ) + threeLevelMiddle E F c N ^ (2 : ℕ) +
        ((N : ℝ) - 2) * c ^ (2 : ℕ) = F := by
  have hpair :
      twoLevelLarge (threeLevelResidualMass E c N)
          (threeLevelResidualEnergy F c N) 2 ^ (2 : ℕ) +
        twoLevelSmall (threeLevelResidualMass E c N)
          (threeLevelResidualEnergy F c N) 2 ^ (2 : ℕ) =
        threeLevelResidualEnergy F c N := by
    convert twoLevel_secondMoment (E := threeLevelResidualMass E c N)
      (F := threeLevelResidualEnergy F c N) (by norm_num : 2 ≤ 2) hres using 1
    all_goals norm_num
  rw [threeLevelLarge, threeLevelMiddle, hpair]
  simp only [threeLevelResidualEnergy]
  ring

theorem twice_sum_cubes_of_sum_and_sq
    {a b M Q : ℝ} (hSum : a + b = M) (hSq : a ^ (2 : ℕ) + b ^ (2 : ℕ) = Q) :
    2 * (a ^ (3 : ℕ) + b ^ (3 : ℕ)) = 3 * M * Q - M ^ (3 : ℕ) := by
  calc
    2 * (a ^ (3 : ℕ) + b ^ (3 : ℕ)) =
        3 * (a + b) * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) - (a + b) ^ (3 : ℕ) := by ring
    _ = 3 * M * Q - M ^ (3 : ℕ) := by rw [hSum, hSq]

/-- The third power sum of the three-level carrier is a cubic polynomial in the plateau. -/
theorem threeLevel_twice_thirdMoment
    {E F c : ℝ} {N : ℕ}
    (hres : threeLevelResidualMass E c N ^ (2 : ℕ) / 2 <
      threeLevelResidualEnergy F c N) :
    2 * (threeLevelLarge E F c N ^ (3 : ℕ) + threeLevelMiddle E F c N ^ (3 : ℕ) +
        ((N : ℝ) - 2) * c ^ (3 : ℕ)) =
      3 * threeLevelResidualMass E c N * threeLevelResidualEnergy F c N -
        threeLevelResidualMass E c N ^ (3 : ℕ) + 2 * ((N : ℝ) - 2) * c ^ (3 : ℕ) := by
  have hsum :
      threeLevelLarge E F c N + threeLevelMiddle E F c N =
        threeLevelResidualMass E c N := by
    change twoLevelLarge (threeLevelResidualMass E c N)
        (threeLevelResidualEnergy F c N) 2 +
      twoLevelSmall (threeLevelResidualMass E c N)
        (threeLevelResidualEnergy F c N) 2 = threeLevelResidualMass E c N
    convert twoLevel_firstMoment (E := threeLevelResidualMass E c N)
      (F := threeLevelResidualEnergy F c N) (by norm_num : 2 ≤ 2) using 1
    all_goals norm_num
  have hsq :
      threeLevelLarge E F c N ^ (2 : ℕ) + threeLevelMiddle E F c N ^ (2 : ℕ) =
        threeLevelResidualEnergy F c N := by
    change twoLevelLarge (threeLevelResidualMass E c N)
        (threeLevelResidualEnergy F c N) 2 ^ (2 : ℕ) +
      twoLevelSmall (threeLevelResidualMass E c N)
        (threeLevelResidualEnergy F c N) 2 ^ (2 : ℕ) = threeLevelResidualEnergy F c N
    convert twoLevel_secondMoment (E := threeLevelResidualMass E c N)
      (F := threeLevelResidualEnergy F c N) (by norm_num : 2 ≤ 2) hres using 1
    all_goals norm_num
  have hcubes := twice_sum_cubes_of_sum_and_sq hsum hsq
  calc
    2 * (threeLevelLarge E F c N ^ (3 : ℕ) + threeLevelMiddle E F c N ^ (3 : ℕ) +
        ((N : ℝ) - 2) * c ^ (3 : ℕ)) =
      2 * (threeLevelLarge E F c N ^ (3 : ℕ) + threeLevelMiddle E F c N ^ (3 : ℕ)) +
        2 * ((N : ℝ) - 2) * c ^ (3 : ℕ) := by ring
    _ = 3 * threeLevelResidualMass E c N * threeLevelResidualEnergy F c N -
        threeLevelResidualMass E c N ^ (3 : ℕ) + 2 * ((N : ℝ) - 2) * c ^ (3 : ℕ) := by
      rw [hcubes]

/-- After fixing its first two power sums, the three-level carrier's third power sum is a
single explicit cubic in the plateau value.  Thus degree-three matching reduces to two endpoint
inequalities and one intermediate-value root, rather than a spectral ansatz. -/
theorem threeLevel_twice_thirdMoment_expanded
    {E F c : ℝ} {N : ℕ}
    (hres : threeLevelResidualMass E c N ^ (2 : ℕ) / 2 <
      threeLevelResidualEnergy F c N) :
    2 * (threeLevelLarge E F c N ^ (3 : ℕ) + threeLevelMiddle E F c N ^ (3 : ℕ) +
        ((N : ℝ) - 2) * c ^ (3 : ℕ)) =
      (3 * E * F - E ^ (3 : ℕ)) +
        3 * ((N : ℝ) - 2) * (E ^ (2 : ℕ) - F) * c -
        3 * E * ((N : ℝ) - 2) * ((N : ℝ) - 1) * c ^ (2 : ℕ) +
        ((N : ℝ) - 2) * (N : ℝ) * ((N : ℝ) - 1) * c ^ (3 : ℕ) := by
  rw [threeLevel_twice_thirdMoment hres]
  simp only [threeLevelResidualMass, threeLevelResidualEnergy]
  ring

/-- The scalar cubic whose feasible roots are exactly the degree-three three-level moment
matches. -/
def threeLevelCubic (E F : ℝ) (N : ℕ) (c : ℝ) : ℝ :=
  (3 * E * F - E ^ (3 : ℕ)) +
    3 * ((N : ℝ) - 2) * (E ^ (2 : ℕ) - F) * c -
    3 * E * ((N : ℝ) - 2) * ((N : ℝ) - 1) * c ^ (2 : ℕ) +
    ((N : ℝ) - 2) * (N : ℝ) * ((N : ℝ) - 1) * c ^ (3 : ℕ)

theorem threeLevel_twice_thirdMoment_eq_cubic
    {E F c : ℝ} {N : ℕ}
    (hres : threeLevelResidualMass E c N ^ (2 : ℕ) / 2 <
      threeLevelResidualEnergy F c N) :
    2 * (threeLevelLarge E F c N ^ (3 : ℕ) + threeLevelMiddle E F c N ^ (3 : ℕ) +
        ((N : ℝ) - 2) * c ^ (3 : ℕ)) = threeLevelCubic E F N c := by
  simpa only [threeLevelCubic] using threeLevel_twice_thirdMoment_expanded hres

/-- Exact degree-three matching predicate for an unweighted finite carrier. -/
def ThreeLevelMomentMatch (E F G : ℝ) (N : ℕ) : Prop :=
  ∃ c : ℝ,
    threeLevelResidualMass E c N ^ (2 : ℕ) / 2 < threeLevelResidualEnergy F c N ∧
      threeLevelLarge E F c N ^ (3 : ℕ) + threeLevelMiddle E F c N ^ (3 : ℕ) +
          ((N : ℝ) - 2) * c ^ (3 : ℕ) = G

/-- Conditions which make the three algebraic atoms squared spectral weights.  The residual
pair lies in the two-atom positive cone, while `c` is the repeated nonnegative plateau. -/
def ThreeLevelSpectralFeasible (E F c : ℝ) (N : ℕ) : Prop :=
  0 ≤ c ∧
    0 < threeLevelResidualMass E c N ∧
      threeLevelResidualMass E c N ^ (2 : ℕ) / 2 < threeLevelResidualEnergy F c N ∧
        threeLevelResidualEnergy F c N ≤ threeLevelResidualMass E c N ^ (2 : ℕ)

/-- The degree-three carrier exists exactly at a feasible root of its explicit cubic. -/
theorem threeLevelMomentMatch_iff_feasible_cubicRoot
    {E F G : ℝ} {N : ℕ} :
    ThreeLevelMomentMatch E F G N ↔
      ∃ c : ℝ,
        threeLevelResidualMass E c N ^ (2 : ℕ) / 2 < threeLevelResidualEnergy F c N ∧
          threeLevelCubic E F N c = 2 * G := by
  constructor
  · rintro ⟨c, hres, hmatch⟩
    refine ⟨c, hres, ?_⟩
    rw [← threeLevel_twice_thirdMoment_eq_cubic hres, hmatch]
  · rintro ⟨c, hres, hroot⟩
    refine ⟨c, hres, ?_⟩
    have htwice := threeLevel_twice_thirdMoment_eq_cubic hres
    rw [hroot] at htwice
    linarith

/-- A feasible interval and a scalar cubic bracket produce an exact finite three-level match. -/
theorem threeLevelMomentMatch_of_cubic_bracket
    {E F G a b : ℝ} {N : ℕ} (hab : a ≤ b)
    (hfeasible : ∀ c ∈ Set.Icc a b,
      threeLevelResidualMass E c N ^ (2 : ℕ) / 2 < threeLevelResidualEnergy F c N)
    (hlower : threeLevelCubic E F N a ≤ 2 * G)
    (hupper : 2 * G ≤ threeLevelCubic E F N b) :
    ThreeLevelMomentMatch E F G N := by
  have hcont : Continuous (threeLevelCubic E F N) := by
    unfold threeLevelCubic
    fun_prop
  have htarget : 2 * G ∈ Set.Icc
      (threeLevelCubic E F N a) (threeLevelCubic E F N b) :=
    ⟨hlower, hupper⟩
  obtain ⟨c, hc, hroot⟩ :=
    intermediate_value_Icc hab hcont.continuousOn htarget
  exact (threeLevelMomentMatch_iff_feasible_cubicRoot).mpr
    ⟨c, hfeasible c hc, hroot⟩

/-- The residual two-level discriminant is concave in the plateau.  Hence strict feasibility at
two endpoints forces strict feasibility throughout their closed interval. -/
theorem threeLevel_residual_feasible_on_Icc
    {E F a b : ℝ} {N : ℕ} (hN : 2 ≤ N) (hab : a ≤ b)
    (ha : threeLevelResidualMass E a N ^ (2 : ℕ) / 2 < threeLevelResidualEnergy F a N)
    (hb : threeLevelResidualMass E b N ^ (2 : ℕ) / 2 < threeLevelResidualEnergy F b N)
    {c : ℝ} (hc : c ∈ Set.Icc a b) :
    threeLevelResidualMass E c N ^ (2 : ℕ) / 2 < threeLevelResidualEnergy F c N := by
  by_cases habEq : a = b
  · subst b
    have hca : c = a := le_antisymm hc.2 hc.1
    subst c
    exact ha
  have hablt : a < b := lt_of_le_of_ne hab habEq
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hC : 0 ≤ ((N : ℝ) - 2) * (N : ℝ) / 2 := by positivity
  have hDa : 0 < threeLevelResidualEnergy F a N -
      threeLevelResidualMass E a N ^ (2 : ℕ) / 2 := by linarith
  have hDb : 0 < threeLevelResidualEnergy F b N -
      threeLevelResidualMass E b N ^ (2 : ℕ) / 2 := by linarith
  have hmain : 0 <
      (b - c) * (threeLevelResidualEnergy F a N -
        threeLevelResidualMass E a N ^ (2 : ℕ) / 2) +
      (c - a) * (threeLevelResidualEnergy F b N -
        threeLevelResidualMass E b N ^ (2 : ℕ) / 2) := by
    have hmin : 0 < min
        (threeLevelResidualEnergy F a N - threeLevelResidualMass E a N ^ (2 : ℕ) / 2)
        (threeLevelResidualEnergy F b N - threeLevelResidualMass E b N ^ (2 : ℕ) / 2) :=
      lt_min hDa hDb
    have hweight : 0 < b - a := sub_pos.mpr hablt
    have hbc : 0 ≤ b - c := sub_nonneg.mpr hc.2
    have hca : 0 ≤ c - a := sub_nonneg.mpr hc.1
    have hle :
        (b - a) * min
          (threeLevelResidualEnergy F a N - threeLevelResidualMass E a N ^ (2 : ℕ) / 2)
          (threeLevelResidualEnergy F b N - threeLevelResidualMass E b N ^ (2 : ℕ) / 2) ≤
          (b - c) * (threeLevelResidualEnergy F a N -
            threeLevelResidualMass E a N ^ (2 : ℕ) / 2) +
          (c - a) * (threeLevelResidualEnergy F b N -
            threeLevelResidualMass E b N ^ (2 : ℕ) / 2) := by
      calc
        (b - a) * min
            (threeLevelResidualEnergy F a N - threeLevelResidualMass E a N ^ (2 : ℕ) / 2)
            (threeLevelResidualEnergy F b N - threeLevelResidualMass E b N ^ (2 : ℕ) / 2) =
            (b - c) * min
              (threeLevelResidualEnergy F a N - threeLevelResidualMass E a N ^ (2 : ℕ) / 2)
              (threeLevelResidualEnergy F b N - threeLevelResidualMass E b N ^ (2 : ℕ) / 2) +
            (c - a) * min
              (threeLevelResidualEnergy F a N - threeLevelResidualMass E a N ^ (2 : ℕ) / 2)
              (threeLevelResidualEnergy F b N - threeLevelResidualMass E b N ^ (2 : ℕ) / 2) := by
              ring
        _ ≤ _ := add_le_add
          (mul_le_mul_of_nonneg_left (min_le_left _ _) hbc)
          (mul_le_mul_of_nonneg_left (min_le_right _ _) hca)
    exact lt_of_lt_of_le (mul_pos hweight hmin) hle
  have hcurve :
      (b - a) * (threeLevelResidualEnergy F c N -
        threeLevelResidualMass E c N ^ (2 : ℕ) / 2) =
        (b - c) * (threeLevelResidualEnergy F a N -
          threeLevelResidualMass E a N ^ (2 : ℕ) / 2) +
        (c - a) * (threeLevelResidualEnergy F b N -
          threeLevelResidualMass E b N ^ (2 : ℕ) / 2) +
        (((N : ℝ) - 2) * (N : ℝ) / 2) * (b - a) * (c - a) * (b - c) := by
    simp only [threeLevelResidualMass, threeLevelResidualEnergy]
    ring
  have htail : 0 ≤
      (((N : ℝ) - 2) * (N : ℝ) / 2) * (b - a) * (c - a) * (b - c) := by
    have hba : 0 ≤ b - a := sub_nonneg.mpr hab
    have hca : 0 ≤ c - a := sub_nonneg.mpr hc.1
    have hbc : 0 ≤ b - c := sub_nonneg.mpr hc.2
    positivity
  have hpositive : 0 < threeLevelResidualEnergy F c N -
      threeLevelResidualMass E c N ^ (2 : ℕ) / 2 := by
    have hweight : 0 < b - a := sub_pos.mpr hablt
    have hscaled : 0 < (b - a) *
        (threeLevelResidualEnergy F c N -
          threeLevelResidualMass E c N ^ (2 : ℕ) / 2) := by
      rw [hcurve]
      exact add_pos_of_pos_of_nonneg hmain htail
    exact pos_of_mul_pos_right hscaled hweight.le
  linarith

/-- Four endpoint inequalities suffice for an exact degree-three finite moment match: two for
residual feasibility and two for the cubic target bracket. -/
theorem threeLevelMomentMatch_of_endpoint_cubic_bracket
    {E F G a b : ℝ} {N : ℕ} (hN : 2 ≤ N) (hab : a ≤ b)
    (ha : threeLevelResidualMass E a N ^ (2 : ℕ) / 2 < threeLevelResidualEnergy F a N)
    (hb : threeLevelResidualMass E b N ^ (2 : ℕ) / 2 < threeLevelResidualEnergy F b N)
    (hlower : threeLevelCubic E F N a ≤ 2 * G)
    (hupper : 2 * G ≤ threeLevelCubic E F N b) :
    ThreeLevelMomentMatch E F G N :=
  threeLevelMomentMatch_of_cubic_bracket hab
    (fun _ hc => threeLevel_residual_feasible_on_Icc hN hab ha hb hc)
    hlower hupper

/-- Strictness above the finite-atom Cauchy floor makes the two-level atoms distinct. -/
theorem twoLevelDeviation_pos_of_strictFloor
    {E F : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hlow : E ^ (2 : ℕ) / (N : ℝ) < F) :
    0 < twoLevelDeviation E F N := by
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hNm1 : 0 < (N : ℝ) - 1 := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    linarith
  have hnum : 0 < (N : ℝ) * F - E ^ (2 : ℕ) := by
    rw [div_lt_iff₀ hNpos] at hlow
    linarith
  have hdevsq := twoLevelDeviation_sq hN hlow
  have hquot : 0 < ((N : ℝ) * F - E ^ (2 : ℕ)) / ((N : ℝ) - 1) :=
    div_pos hnum hNm1
  nlinarith [twoLevelDeviation_nonneg E F N]

/-- The old small atom lies strictly below the equal-share plateau. -/
theorem twoLevelSmall_lt_mean_of_strictFloor
    {E F : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hlow : E ^ (2 : ℕ) / (N : ℝ) < F) :
    twoLevelSmall E F N < E / (N : ℝ) := by
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hdiff : E / (N : ℝ) - twoLevelSmall E F N =
      twoLevelDeviation E F N / (N : ℝ) := by
    rw [twoLevelSmall]
    field_simp [hNpos.ne']
    ring
  have hpos : 0 < E / (N : ℝ) - twoLevelSmall E F N := by
    rw [hdiff]
    exact div_pos (twoLevelDeviation_pos_of_strictFloor hN hlow) hNpos
  linarith

/-- At the old two-level small atom, the three-level residual pair is strictly feasible.  This
embeds the already constructed quadratic/quartic carrier as one endpoint of the cubic family. -/
theorem threeLevel_residual_feasible_at_twoLevelSmall
    {E F : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hlow : E ^ (2 : ℕ) / (N : ℝ) < F) :
    threeLevelResidualMass E (twoLevelSmall E F N) N ^ (2 : ℕ) / 2 <
      threeLevelResidualEnergy F (twoLevelSmall E F N) N := by
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hdevpos := twoLevelDeviation_pos_of_strictFloor hN hlow
  have hgap : 0 < twoLevelLarge E F N - twoLevelSmall E F N := by
    have hdiff : twoLevelLarge E F N - twoLevelSmall E F N =
        twoLevelDeviation E F N := by
      rw [twoLevelLarge, twoLevelSmall]
      field_simp [hNpos.ne']
      ring
    rw [hdiff]
    exact hdevpos
  have hfirst := twoLevel_firstMoment (E := E) (F := F) hN
  have hsecond := twoLevel_secondMoment (E := E) (F := F) hN hlow
  have hmass : threeLevelResidualMass E (twoLevelSmall E F N) N =
      twoLevelLarge E F N + twoLevelSmall E F N := by
    unfold threeLevelResidualMass
    nlinarith [hfirst]
  have henergy : threeLevelResidualEnergy F (twoLevelSmall E F N) N =
      twoLevelLarge E F N ^ (2 : ℕ) + twoLevelSmall E F N ^ (2 : ℕ) := by
    unfold threeLevelResidualEnergy
    nlinarith [hsecond]
  rw [hmass, henergy]
  nlinarith [sq_pos_of_pos hgap]

/-- The old two-level head is a strict point of the genuine positive three-level spectral cone.
This is stronger than algebraic residual feasibility: all three squared weights are admissible
for a Hilbert diagonal. -/
theorem threeLevelSpectralFeasible_at_twoLevelSmall
    {E F : ℝ} {N : ℕ} (hE : 0 < E) (hN : 2 ≤ N)
    (hlow : E ^ (2 : ℕ) / (N : ℝ) < F) (hhigh : F < E ^ (2 : ℕ)) :
    ThreeLevelSpectralFeasible E F (twoLevelSmall E F N) N := by
  have hL : 0 < twoLevelLarge E F N := twoLevelLarge_pos hE hN
  have hS : 0 < twoLevelSmall E F N := twoLevelSmall_pos hE hN hlow hhigh
  have hfirst := twoLevel_firstMoment (E := E) (F := F) hN
  have hsecond := twoLevel_secondMoment (E := E) (F := F) hN hlow
  have hmass : threeLevelResidualMass E (twoLevelSmall E F N) N =
      twoLevelLarge E F N + twoLevelSmall E F N := by
    unfold threeLevelResidualMass
    nlinarith [hfirst]
  have henergy : threeLevelResidualEnergy F (twoLevelSmall E F N) N =
      twoLevelLarge E F N ^ (2 : ℕ) + twoLevelSmall E F N ^ (2 : ℕ) := by
    unfold threeLevelResidualEnergy
    nlinarith [hsecond]
  refine ⟨hS.le, ?_,
    threeLevel_residual_feasible_at_twoLevelSmall hN hlow, ?_⟩
  · rw [hmass]
    exact add_pos hL hS
  · rw [hmass, henergy]
    nlinarith [mul_pos hL hS]

/-- Exact positive-spectral admission of the equal-share plateau.  The upper
inequality is indispensable: the residual two-atom energy must not exceed the
square of its mass. -/
theorem threeLevelSpectralFeasible_at_mean_iff
    {E F : ℝ} {N : ℕ} (hE : 0 < E) (hN : 3 ≤ N) :
    ThreeLevelSpectralFeasible E F (E / (N : ℝ)) N ↔
      E ^ (2 : ℕ) / (N : ℝ) < F ∧
        F ≤ ((N : ℝ) + 2) * E ^ (2 : ℕ) / (N : ℝ) ^ (2 : ℕ) := by
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  have hmass :
      threeLevelResidualMass E (E / (N : ℝ)) N = 2 * E / N := by
    unfold threeLevelResidualMass
    field_simp [hNpos.ne']
    ring
  have hlowIdentity :
      threeLevelResidualEnergy F (E / (N : ℝ)) N -
        threeLevelResidualMass E (E / (N : ℝ)) N ^ (2 : ℕ) / 2 =
      F - E ^ (2 : ℕ) / N := by
    rw [hmass]
    unfold threeLevelResidualEnergy
    field_simp [hNpos.ne']
    ring
  have hhighIdentity :
      threeLevelResidualMass E (E / (N : ℝ)) N ^ (2 : ℕ) -
        threeLevelResidualEnergy F (E / (N : ℝ)) N =
      ((N : ℝ) + 2) * E ^ (2 : ℕ) / (N : ℝ) ^ (2 : ℕ) - F := by
    rw [hmass]
    unfold threeLevelResidualEnergy
    field_simp [hNpos.ne']
    ring
  constructor
  · rintro ⟨_, _, hlow, hhigh⟩
    constructor
    · linarith [hlowIdentity]
    · linarith [hhighIdentity]
  · rintro ⟨hlow, hhigh⟩
    refine ⟨div_nonneg hE.le hNpos.le, ?_, ?_, ?_⟩
    · rw [hmass]
      exact div_pos (mul_pos (by norm_num) hE) hNpos
    · linarith [hlowIdentity]
    · linarith [hhighIdentity]

/-- The first positive three-level head with admissible equal-share plateau
exists at the smallest integer strictly above the effective rank `E²/F`.
Its admission uses no asymptotic choice of atom count. -/
theorem exists_threeLevelSpectralFeasible_at_mean
    {E F : ℝ} (hE : 0 < E) (hF : 0 < F)
    (hrank : 2 * F ≤ E ^ (2 : ℕ)) :
    ∃ N : ℕ, 3 ≤ N ∧
      ThreeLevelSpectralFeasible E F (E / (N : ℝ)) N := by
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
  have hNplus : 0 ≤ (N : ℝ) + 2 := by positivity
  have hprod := mul_le_mul_of_nonneg_left hRlower hNplus
  have hpoly : (N : ℝ) ^ (2 : ℕ) ≤ ((N : ℝ) + 2) * r := by
    have hNthree : (3 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [hprod]
  have hpolyScaled := mul_le_mul_of_nonneg_right hpoly hF.le
  have hhigh :
      F ≤ ((N : ℝ) + 2) * E ^ (2 : ℕ) / (N : ℝ) ^ (2 : ℕ) := by
    apply (le_div_iff₀ (sq_pos_of_pos hNpos)).2
    nlinarith [hpolyScaled, hratio]
  exact ⟨N, hN,
    (threeLevelSpectralFeasible_at_mean_iff hE hN).2 ⟨hlow, hhigh⟩⟩

/-- The cubic's two-level endpoint is precisely twice the old carrier's third power sum. -/
theorem threeLevelCubic_at_twoLevelSmall
    {E F : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hlow : E ^ (2 : ℕ) / (N : ℝ) < F) :
    threeLevelCubic E F N (twoLevelSmall E F N) =
      2 * (twoLevelLarge E F N ^ (3 : ℕ) +
        ((N : ℝ) - 1) * twoLevelSmall E F N ^ (3 : ℕ)) := by
  let L : ℝ := twoLevelLarge E F N
  let S : ℝ := twoLevelSmall E F N
  have hfirst : L + ((N : ℝ) - 1) * S = E := by
    simpa only [L, S] using twoLevel_firstMoment (E := E) (F := F) hN
  have hsecond : L ^ (2 : ℕ) + ((N : ℝ) - 1) * S ^ (2 : ℕ) = F := by
    simpa only [L, S] using twoLevel_secondMoment (E := E) (F := F) hN hlow
  change threeLevelCubic E F N S =
    2 * (L ^ (3 : ℕ) + ((N : ℝ) - 1) * S ^ (3 : ℕ))
  unfold threeLevelCubic
  rw [← hfirst, ← hsecond]
  ring

/-- The equal-share plateau keeps the residual two-level problem strictly feasible whenever the
given second moment is above its `N`-atom Cauchy floor. -/
theorem threeLevel_residual_feasible_at_mean
    {E F : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hvariance : E ^ (2 : ℕ) / (N : ℝ) < F) :
    threeLevelResidualMass E (E / (N : ℝ)) N ^ (2 : ℕ) / 2 <
      threeLevelResidualEnergy F (E / (N : ℝ)) N := by
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hmul : E ^ (2 : ℕ) < F * (N : ℝ) :=
    (div_lt_iff₀ hNpos).mp hvariance
  rw [threeLevelResidualMass, threeLevelResidualEnergy]
  field_simp [hNpos.ne']
  nlinarith

/-- The cubic's value at its equal-share plateau is strictly positive.  This is the first
explicit endpoint for degree-three moment matching in the K-RVM head. -/
theorem threeLevel_twice_thirdMoment_at_mean_pos
    {E F : ℝ} {N : ℕ} (hN : 2 ≤ N) (hE : 0 < E)
    (hvariance : E ^ (2 : ℕ) / (N : ℝ) < F) :
    0 < 2 * (threeLevelLarge E F (E / (N : ℝ)) N ^ (3 : ℕ) +
        threeLevelMiddle E F (E / (N : ℝ)) N ^ (3 : ℕ) +
        ((N : ℝ) - 2) * (E / (N : ℝ)) ^ (3 : ℕ)) := by
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hmul : E ^ (2 : ℕ) < F * (N : ℝ) :=
    (div_lt_iff₀ hNpos).mp hvariance
  have hres := threeLevel_residual_feasible_at_mean hN hvariance
  rw [threeLevel_twice_thirdMoment_expanded hres]
  have hpoly :
      (3 * E * F - E ^ (3 : ℕ)) +
          3 * ((N : ℝ) - 2) * (E ^ (2 : ℕ) - F) * (E / (N : ℝ)) -
          3 * E * ((N : ℝ) - 2) * ((N : ℝ) - 1) * (E / (N : ℝ)) ^ (2 : ℕ) +
          ((N : ℝ) - 2) * (N : ℝ) * ((N : ℝ) - 1) * (E / (N : ℝ)) ^ (3 : ℕ) =
        (2 * E / (N : ℝ) ^ (2 : ℕ)) * (3 * F * (N : ℝ) - 2 * E ^ (2 : ℕ)) := by
    field_simp [hNpos.ne']
    ring
  rw [hpoly]
  have hinterior : 0 < 3 * F * (N : ℝ) - 2 * E ^ (2 : ℕ) := by
    nlinarith
  exact mul_pos (by positivity) hinterior

/-- Exact distance from the equal-share cubic endpoint to the Cauchy lower
wall.  It identifies the extra quantitative source margin needed to use this
endpoint in an intermediate-value bracket. -/
theorem threeLevelCubic_at_mean_sub_cauchy_floor
    {E F : ℝ} {N : ℕ} (hN : 0 < N) :
    E * (threeLevelCubic E F N (E / (N : ℝ)) / 2) - F ^ (2 : ℕ) =
      (((N : ℝ) * F - E ^ (2 : ℕ)) *
        (2 * E ^ (2 : ℕ) - (N : ℝ) * F)) / (N : ℝ) ^ (2 : ℕ) := by
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  unfold threeLevelCubic
  field_simp [hNne]
  ring

/-- At a genuinely nonuniform equal-share carrier, its cubic moment lies
strictly above the generic Cauchy lower wall.  Source Hankel positivity alone
does not bracket this endpoint. -/
theorem threeLevelCubic_at_mean_gt_cauchy_floor
    {E F : ℝ} {N : ℕ} (hN : 0 < N)
    (hlow : E ^ (2 : ℕ) / (N : ℝ) < F)
    (hhigh : F < 2 * E ^ (2 : ℕ) / (N : ℝ)) :
    F ^ (2 : ℕ) < E * (threeLevelCubic E F N (E / (N : ℝ)) / 2) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hleft : 0 < (N : ℝ) * F - E ^ (2 : ℕ) := by
    have h := (div_lt_iff₀ hNpos).1 hlow
    nlinarith
  have hright : 0 < 2 * E ^ (2 : ℕ) - (N : ℝ) * F := by
    have h := (lt_div_iff₀ hNpos).1 hhigh
    nlinarith
  have hquot : 0 <
      (((N : ℝ) * F - E ^ (2 : ℕ)) *
        (2 * E ^ (2 : ℕ) - (N : ℝ) * F)) / (N : ℝ) ^ (2 : ℕ) :=
    div_pos (mul_pos hleft hright) (sq_pos_of_pos hNpos)
  linarith [threeLevelCubic_at_mean_sub_cauchy_floor (E := E) (F := F) hN]

/-- Exact cubic change produced by splitting the old repeated small atom.  It has a double
root at the two-level endpoint, so the sixth energy cannot be increased by an infinitesimal
positive plateau deformation. -/
theorem threeLevelCubic_sub_of_twoLevelMoments
    {E F L S c : ℝ} {N : ℕ}
    (hNpos : 0 < N)
    (hfirst : L + ((N : ℝ) - 1) * S = E)
    (hsecond : L ^ (2 : ℕ) + ((N : ℝ) - 1) * S ^ (2 : ℕ) = F) :
    threeLevelCubic E F N c - threeLevelCubic E F N S =
      ((N : ℝ) - 2) * (N : ℝ) * ((N : ℝ) - 1) * (c - S) ^ (2 : ℕ) *
        (c - (3 * E / (N : ℝ) - 2 * S)) := by
  have hNreal : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hNpos)
  rw [← hfirst, ← hsecond]
  simp only [threeLevelCubic]
  field_simp [hNreal]
  ring

theorem threeLevelCubic_sub_at_twoLevelSmall_factor
    {E F c : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hlow : E ^ (2 : ℕ) / (N : ℝ) < F) :
    threeLevelCubic E F N c - threeLevelCubic E F N (twoLevelSmall E F N) =
      ((N : ℝ) - 2) * (N : ℝ) * ((N : ℝ) - 1) *
        (c - twoLevelSmall E F N) ^ (2 : ℕ) *
          (c - (3 * E / (N : ℝ) - 2 * twoLevelSmall E F N)) := by
  let L : ℝ := twoLevelLarge E F N
  let S : ℝ := twoLevelSmall E F N
  have hfirst : L + ((N : ℝ) - 1) * S = E := by
    simpa only [L, S] using twoLevel_firstMoment (E := E) (F := F) hN
  have hsecond : L ^ (2 : ℕ) + ((N : ℝ) - 1) * S ^ (2 : ℕ) = F := by
    simpa only [L, S] using twoLevel_secondMoment (E := E) (F := F) hN hlow
  exact threeLevelCubic_sub_of_twoLevelMoments (by omega) hfirst hsecond

/-- With at least three atoms, every plateau move from the old small atom toward equal sharing
strictly *decreases* the third power sum.  This rules out the previously tempting endpoint
orientation for a positive sixth-energy repair. -/
theorem threeLevelCubic_at_mean_lt_at_twoLevelSmall
    {E F : ℝ} {N : ℕ} (hN : 3 ≤ N)
    (hlow : E ^ (2 : ℕ) / (N : ℝ) < F) :
    threeLevelCubic E F N (E / (N : ℝ)) <
      threeLevelCubic E F N (twoLevelSmall E F N) := by
  have hNtwo : 2 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  have hNreal : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNminusTwo : (0 : ℝ) < (N : ℝ) - 2 := by
    linarith
  have hNminusOne : (0 : ℝ) < (N : ℝ) - 1 := by
    linarith
  have hgap : 0 < E / (N : ℝ) - twoLevelSmall E F N :=
    sub_pos.mpr (twoLevelSmall_lt_mean_of_strictFloor hNtwo hlow)
  have hfactor := threeLevelCubic_sub_at_twoLevelSmall_factor
    (E := E) (F := F) (c := E / (N : ℝ)) hNtwo hlow
  have hpositive : 0 <
      ((N : ℝ) - 2) * (N : ℝ) * ((N : ℝ) - 1) *
        (E / (N : ℝ) - twoLevelSmall E F N) ^ (2 : ℕ) := by
    positivity
  have hnegative :
      E / (N : ℝ) -
        (3 * E / (N : ℝ) - 2 * twoLevelSmall E F N) < 0 := by
    have hrewrite : E / (N : ℝ) -
        (3 * E / (N : ℝ) - 2 * twoLevelSmall E F N) =
        -2 * (E / (N : ℝ) - twoLevelSmall E F N) := by ring
    rw [hrewrite]
    linarith
  have hproduct :
      ((N : ℝ) - 2) * (N : ℝ) * ((N : ℝ) - 1) *
          (E / (N : ℝ) - twoLevelSmall E F N) ^ (2 : ℕ) *
        (E / (N : ℝ) -
          (3 * E / (N : ℝ) - 2 * twoLevelSmall E F N)) < 0 :=
    mul_neg_of_pos_of_neg hpositive hnegative
  have hdiff :
      threeLevelCubic E F N (E / (N : ℝ)) -
        threeLevelCubic E F N (twoLevelSmall E F N) < 0 := by
    rw [hfactor]
    exact hproduct
  linarith

/-- Below equal sharing, the cubic target never exceeds its two-level value.  Therefore a
positive deformation from the old repeated small atom can only lower the sixth energy. -/
theorem threeLevelCubic_le_at_twoLevelSmall_of_le_mean
    {E F c : ℝ} {N : ℕ} (hN : 3 ≤ N)
    (hlow : E ^ (2 : ℕ) / (N : ℝ) < F)
    (hcmean : c ≤ E / (N : ℝ)) :
    threeLevelCubic E F N c ≤
      threeLevelCubic E F N (twoLevelSmall E F N) := by
  have hNtwo : 2 ≤ N := by omega
  have hNreal : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNminusTwo : 0 ≤ (N : ℝ) - 2 := by linarith
  have hNminusOne : 0 ≤ (N : ℝ) - 1 := by linarith
  have hgap : 0 < E / (N : ℝ) - twoLevelSmall E F N :=
    sub_pos.mpr (twoLevelSmall_lt_mean_of_strictFloor hNtwo hlow)
  have hfactor := threeLevelCubic_sub_at_twoLevelSmall_factor
    (E := E) (F := F) (c := c) hNtwo hlow
  have hcoeff : 0 ≤
      ((N : ℝ) - 2) * (N : ℝ) * ((N : ℝ) - 1) *
        (c - twoLevelSmall E F N) ^ (2 : ℕ) := by
    have hNnonneg : (0 : ℝ) ≤ N := by positivity
    positivity
  have hlast : c - (3 * E / (N : ℝ) - 2 * twoLevelSmall E F N) ≤ 0 := by
    have hrewrite : c - (3 * E / (N : ℝ) - 2 * twoLevelSmall E F N) =
        (c - E / (N : ℝ)) -
          2 * (E / (N : ℝ) - twoLevelSmall E F N) := by ring
    rw [hrewrite]
    linarith
  have hproduct :
      ((N : ℝ) - 2) * (N : ℝ) * ((N : ℝ) - 1) *
          (c - twoLevelSmall E F N) ^ (2 : ℕ) *
        (c - (3 * E / (N : ℝ) - 2 * twoLevelSmall E F N)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hcoeff hlast
  have hdiff :
      threeLevelCubic E F N c -
        threeLevelCubic E F N (twoLevelSmall E F N) ≤ 0 := by
    rw [hfactor]
    exact hproduct
  linarith

end

end RHTower
