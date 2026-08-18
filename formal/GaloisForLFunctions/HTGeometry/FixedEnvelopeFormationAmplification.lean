import Mathlib

/-!
# Fixed-envelope formation amplification

Independent formation multiplies a radial exponent by degree while one source envelope retains a
fixed decay exponent.  This module proves the exact compact-admission phase diagram: degree `d` is
admitted exactly when `d * a < κ`; all positive degrees select `a ≤ 0`; reflected all-degree
admission selects `a = 0`.  It also proves packet fusion, logarithmic recovery, and the sharp
adaptive-decay countermodel.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Defect after `d` independent formations when source weight decays at rate `κ`
along a proper height and the radial character grows at rate `a`. -/
def fixedDecayAmplifiedDefect (height : ℕ → ℝ) (κ a : ℝ) (d n : ℕ) : ℝ :=
  Real.exp ((((d : ℝ) * a) - κ) * height n) - Real.exp (-κ * height n)

/-- Source-normalized packet produced by `d` independent formations. -/
def normalizedFormationPacket (height : ℕ → ℝ) (a : ℝ) (d n : ℕ) : ℝ :=
  Real.exp ((d : ℝ) * a * height n)

/-- Independent formation is represented by multiplication of normalized packets. -/
theorem normalizedFormationPacket_add (height : ℕ → ℝ) (a : ℝ) (d e n : ℕ) :
    normalizedFormationPacket height a (d + e) n =
      normalizedFormationPacket height a d n * normalizedFormationPacket height a e n := by
  rw [normalizedFormationPacket, normalizedFormationPacket, normalizedFormationPacket,
    ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- The formed defect is one fixed source envelope times the normalized packet increment. -/
theorem fixedDecayAmplifiedDefect_factorization (height : ℕ → ℝ)
    (κ a : ℝ) (d n : ℕ) :
    fixedDecayAmplifiedDefect height κ a d n =
      Real.exp (-κ * height n) * (normalizedFormationPacket height a d n - 1) := by
  rw [fixedDecayAmplifiedDefect, normalizedFormationPacket]
  rw [mul_sub, mul_one, ← Real.exp_add]
  congr 1
  ring_nf

/-- Functional-equation reflection acts by inversion on normalized packets. -/
theorem normalizedFormationPacket_reflection (height : ℕ → ℝ)
    (a : ℝ) (d n : ℕ) :
    normalizedFormationPacket height (-a) d n =
      (normalizedFormationPacket height a d n)⁻¹ := by
  rw [normalizedFormationPacket, normalizedFormationPacket, ← Real.exp_neg]
  congr 1
  ring

/-- The packet logarithm retains the formed exponent exactly. -/
theorem normalizedFormationPacket_log (height : ℕ → ℝ)
    (a : ℝ) (d n : ℕ) :
    Real.log (normalizedFormationPacket height a d n) =
      (d : ℝ) * a * height n := by
  simp [normalizedFormationPacket]

/-- One nonzero-height packet at positive formation degree reconstructs the radial exponent. -/
theorem normalizedFormationPacket_reconstructs_exponent (height : ℕ → ℝ)
    (a : ℝ) {d n : ℕ} (hd : 0 < d) (hheight : height n ≠ 0) :
    Real.log (normalizedFormationPacket height a d n) /
        ((d : ℝ) * height n) = a := by
  rw [normalizedFormationPacket_log]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  field_simp

/-- Reflection negates recovered information but erases none of it. -/
theorem normalizedFormationPacket_reflection_information_neutral (height : ℕ → ℝ)
    (a : ℝ) (d n : ℕ) :
    Real.log (normalizedFormationPacket height (-a) d n) =
      -Real.log (normalizedFormationPacket height a d n) := by
  simp [normalizedFormationPacket]

/-- Compact admission at one formation degree. -/
def DegreeCompactAdmission (height : ℕ → ℝ) (κ a : ℝ) (d : ℕ) : Prop :=
  Tendsto (fixedDecayAmplifiedDefect height κ a d) atTop (𝓝 0)

/-- Compact admission at every positive formation degree. -/
def AllDegreeCompactAdmission (height : ℕ → ℝ) (κ a : ℝ) : Prop :=
  ∀ d : ℕ, 0 < d → DegreeCompactAdmission height κ a d

/-- A positive fixed envelope decays along every proper height. -/
theorem tendsto_exp_neg_mul_height {height : ℕ → ℝ} {κ : ℝ}
    (hheight : Tendsto height atTop atTop) (hκ : 0 < κ) :
    Tendsto (fun n : ℕ => Real.exp (-κ * height n)) atTop (𝓝 0) := by
  have harg : Tendsto (fun n : ℕ => -κ * height n) atTop atBot := by
    simpa [mul_comm] using hheight.atTop_mul_const_of_neg (neg_lt_zero.mpr hκ)
  exact Real.tendsto_exp_atBot.comp harg

/-- Exact one-degree phase boundary: compact admission holds precisely below `d * a = κ`. -/
theorem degreeCompactAdmission_iff {height : ℕ → ℝ} {κ a : ℝ} {d : ℕ}
    (hheight : Tendsto height atTop atTop) (hκ : 0 < κ) :
    DegreeCompactAdmission height κ a d ↔ (d : ℝ) * a < κ := by
  constructor
  · intro hdef
    have hdecay := tendsto_exp_neg_mul_height hheight hκ
    have hsum : Tendsto
        (fun n : ℕ => fixedDecayAmplifiedDefect height κ a d n +
          Real.exp (-κ * height n)) atTop (𝓝 0) := by
      simpa [DegreeCompactAdmission] using hdef.add hdecay
    have hsum' : Tendsto
        (fun n : ℕ => Real.exp ((((d : ℝ) * a) - κ) * height n))
        atTop (𝓝 0) := by
      convert hsum using 1
      funext n
      simp [fixedDecayAmplifiedDefect]
    by_contra hlt
    have hle : κ ≤ (d : ℝ) * a := not_lt.mp hlt
    rcases hle.eq_or_lt with heq | hpos
    · have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
        convert hsum' using 1
        funext n
        rw [heq]
        simp
      have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hone
      norm_num at this
    · have hrate : 0 < (d : ℝ) * a - κ := sub_pos.mpr hpos
      have hlinear : Tendsto (fun n => (((d : ℝ) * a) - κ) * height n)
          atTop atTop := by
        exact Filter.Tendsto.const_mul_atTop hrate hheight
      have hgrow : Tendsto
          (fun n : ℕ => Real.exp ((((d : ℝ) * a) - κ) * height n))
          atTop atTop := Real.tendsto_exp_atTop.comp hlinear
      obtain ⟨n, hnsmall, hnlarge⟩ :=
        (hsum'.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))).and
          (hgrow.eventually_gt_atTop 1) |>.exists
      exact (not_lt_of_ge hnsmall) hnlarge
  · intro hrate
    have hfirst : Tendsto
        (fun n : ℕ => Real.exp ((((d : ℝ) * a) - κ) * height n))
        atTop (𝓝 0) := by
      have harg : Tendsto (fun n : ℕ => (((d : ℝ) * a) - κ) * height n)
          atTop atBot := by
        simpa [mul_comm] using
          hheight.atTop_mul_const_of_neg (sub_neg.mpr hrate)
      exact Real.tendsto_exp_atBot.comp harg
    unfold DegreeCompactAdmission
    convert hfirst.sub (tendsto_exp_neg_mul_height hheight hκ) using 1
    funext n
    simp [fixedDecayAmplifiedDefect]
    ring_nf

/-- At the admission wall the defect retains a unit boundary value. -/
theorem fixedDecayAmplifiedDefect_tendsto_one_of_eq {height : ℕ → ℝ}
    {κ a : ℝ} {d : ℕ} (hheight : Tendsto height atTop atTop) (hκ : 0 < κ)
    (hrate : (d : ℝ) * a = κ) :
    Tendsto (fixedDecayAmplifiedDefect height κ a d) atTop (𝓝 1) := by
  have hdecay := tendsto_exp_neg_mul_height hheight hκ
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hlim : Tendsto (fun n : ℕ => 1 - Real.exp (-κ * height n))
      atTop (𝓝 1) := by simpa using hone.sub hdecay
  convert hlim using 1
  funext n
  simp [fixedDecayAmplifiedDefect, hrate]

/-- Above the admission wall the formed defect escapes to positive infinity. -/
theorem fixedDecayAmplifiedDefect_tendsto_atTop_of_gt {height : ℕ → ℝ}
    {κ a : ℝ} {d : ℕ} (hheight : Tendsto height atTop atTop) (hκ : 0 < κ)
    (hrate : κ < (d : ℝ) * a) :
    Tendsto (fixedDecayAmplifiedDefect height κ a d) atTop atTop := by
  have hlinear : Tendsto (fun n => (((d : ℝ) * a) - κ) * height n)
      atTop atTop := Filter.Tendsto.const_mul_atTop (sub_pos.mpr hrate) hheight
  have hgrow : Tendsto
      (fun n : ℕ => Real.exp ((((d : ℝ) * a) - κ) * height n))
      atTop atTop := Real.tendsto_exp_atTop.comp hlinear
  have hdecay := tendsto_exp_neg_mul_height hheight hκ
  rw [tendsto_atTop]
  intro b
  filter_upwards [hgrow.eventually_gt_atTop (b + 1),
    hdecay.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with n hn hsmall
  rw [fixedDecayAmplifiedDefect]
  linarith

/-- Compact admission at every formation degree excludes positive radial drift. -/
theorem allDegreeCompactAdmission_implies_nonpos {height : ℕ → ℝ} {κ a : ℝ}
    (hheight : Tendsto height atTop atTop) (hκ : 0 < κ)
    (hcompact : AllDegreeCompactAdmission height κ a) : a ≤ 0 := by
  by_contra ha
  rw [not_le] at ha
  obtain ⟨d, hd⟩ := exists_nat_gt (κ / a)
  have hdpos : 0 < d := by
    have hzero : (0 : ℝ) < d := lt_of_le_of_lt (div_nonneg hκ.le ha.le) hd
    exact_mod_cast hzero
  have hphase := (degreeCompactAdmission_iff hheight hκ).mp (hcompact d hdpos)
  have := (div_lt_iff₀ ha).mp hd
  linarith

/-- Every nonpositive radial drift is admitted at all positive formation degrees. -/
theorem allDegreeCompactAdmission_of_nonpos {height : ℕ → ℝ} {κ a : ℝ}
    (hheight : Tendsto height atTop atTop) (hκ : 0 < κ) (ha : a ≤ 0) :
    AllDegreeCompactAdmission height κ a := by
  intro d hd
  apply (degreeCompactAdmission_iff hheight hκ).2
  have : (d : ℝ) * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg d) ha
  linarith

/-- One-sided all-degree compact admission is exactly the nonpositive chamber. -/
theorem allDegreeCompactAdmission_iff_nonpos {height : ℕ → ℝ} {κ a : ℝ}
    (hheight : Tendsto height atTop atTop) (hκ : 0 < κ) :
    AllDegreeCompactAdmission height κ a ↔ a ≤ 0 :=
  ⟨allDegreeCompactAdmission_implies_nonpos hheight hκ,
    allDegreeCompactAdmission_of_nonpos hheight hκ⟩

/-- Every positive radial drift is rejected at an explicitly finite formation degree. -/
theorem exists_detecting_degree_of_pos {height : ℕ → ℝ} {κ a : ℝ}
    (hheight : Tendsto height atTop atTop) (hκ : 0 < κ) (ha : 0 < a) :
    ∃ d : ℕ, 0 < d ∧ κ < (d : ℝ) * a ∧
      ¬ DegreeCompactAdmission height κ a d := by
  obtain ⟨d, hd⟩ := exists_nat_gt (κ / a)
  have hdpos : 0 < d := by
    have hzero : (0 : ℝ) < d := lt_of_le_of_lt (div_nonneg hκ.le ha.le) hd
    exact_mod_cast hzero
  have hrate : κ < (d : ℝ) * a := (div_lt_iff₀ ha).mp hd
  refine ⟨d, hdpos, hrate, ?_⟩
  rw [degreeCompactAdmission_iff hheight hκ]
  exact not_lt_of_ge hrate.le

/-- If source decay is allowed to increase with formation degree, positive drift can be hidden
at every finite degree.  This is the sharp reason fixed source decay is load-bearing. -/
def adaptiveDecayDefect (height : ℕ → ℝ) (a : ℝ) (d n : ℕ) : ℝ :=
  Real.exp (-height n) - Real.exp (-(1 + (d : ℝ) * a) * height n)

/-- Adaptive decay hides every nonnegative drift at every fixed formation degree. -/
theorem adaptiveDecayDefect_tendsto_zero {height : ℕ → ℝ} {a : ℝ}
    (hheight : Tendsto height atTop atTop) (ha : 0 ≤ a) (d : ℕ) :
    Tendsto (adaptiveDecayDefect height a d) atTop (𝓝 0) := by
  have hone : (0 : ℝ) < 1 := by norm_num
  have hcoeff : 0 < 1 + (d : ℝ) * a := by positivity
  have hfirst := tendsto_exp_neg_mul_height hheight hone
  have hsecond : Tendsto
      (fun n : ℕ => Real.exp (-(1 + (d : ℝ) * a) * height n))
      atTop (𝓝 0) := tendsto_exp_neg_mul_height hheight hcoeff
  convert hfirst.sub hsecond using 1
  funext n
  simp [adaptiveDecayDefect]
  ring_nf

/-- Closed positive-drift countermodel to selection under degree-dependent source decay. -/
def AdaptiveDecayPositiveDriftCountermodel : Prop :=
  ∀ (height : ℕ → ℝ), Tendsto height atTop atTop →
    ∀ d : ℕ, Tendsto (adaptiveDecayDefect height 1 d) atTop (𝓝 0)

theorem adaptiveDecayPositiveDriftCountermodel_closed :
    AdaptiveDecayPositiveDriftCountermodel := by
  intro height hheight d
  exact adaptiveDecayDefect_tendsto_zero hheight (by norm_num) d

/-- Bilateral all-degree compact admission selects the neutral exponent exactly. -/
theorem bilateralAllDegreeCompactAdmission_iff_zero {height : ℕ → ℝ} {κ a : ℝ}
    (hheight : Tendsto height atTop atTop) (hκ : 0 < κ) :
    (AllDegreeCompactAdmission height κ a ∧
      AllDegreeCompactAdmission height κ (-a)) ↔ a = 0 := by
  rw [allDegreeCompactAdmission_iff_nonpos hheight hκ,
    allDegreeCompactAdmission_iff_nonpos hheight hκ]
  constructor
  · rintro ⟨ha, hna⟩
    linarith
  · rintro rfl
    norm_num

/-- Closed capstone for fixed-envelope bilateral selection over every proper height. -/
def FixedDecayBilateralSelection : Prop :=
  ∀ (height : ℕ → ℝ) (κ a : ℝ), Tendsto height atTop atTop → 0 < κ →
    (AllDegreeCompactAdmission height κ a ∧
      AllDegreeCompactAdmission height κ (-a) ↔ a = 0)

theorem fixedDecayBilateralSelection_closed : FixedDecayBilateralSelection := by
  intro height κ a hheight hκ
  exact bilateralAllDegreeCompactAdmission_iff_zero hheight hκ

end


end GaloisForLFunctions.HTGeometry
