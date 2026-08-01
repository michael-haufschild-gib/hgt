import GaloisForLFunctions.HTGeometry.CountableWeightedDiracLinftyEquiv
import GaloisForLFunctions.HTGeometry.HerglotzFiniteAtomicChamber
import GaloisForLFunctions.HTGeometry.CircleAtomicCarrier

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MeasureTheory Set Topology Filter
open scoped ENNReal

noncomputable section

/-- Exact summability hypothesis `(H7)` for a discrete real Herglotz skeleton. -/
def DiscreteHerglotzH7 (ε atoms : ℕ → ℝ) : Prop :=
  Summable fun n => ε n / (1 + |atoms n|)

/-- The Nevanlinna weight is controlled by the exact `(H7)` denominator. -/
theorem nevanlinnaWeight_le_two_div_one_add_abs (t : ℝ) :
    nevanlinnaWeight t ≤ 2 / (1 + |t|) := by
  rw [nevanlinnaWeight, inv_eq_one_div]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 1 + t ^ 2)
    (by positivity : (0 : ℝ) < 1 + |t|)).2
  nlinarith [sq_nonneg (|t| - 1), sq_abs t]

/-- `(H7)` implies summability of the Nevanlinna-weighted atomic masses. -/
theorem summable_nevanlinnaWeight_of_discreteHerglotzH7
    {ε atoms : ℕ → ℝ} (hε : ∀ n, 0 ≤ ε n)
    (hH7 : DiscreteHerglotzH7 ε atoms) :
    Summable fun n => ε n * nevanlinnaWeight (atoms n) := by
  apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (hε n) (nevanlinnaWeight_pos _).le)
      (fun n => ?_) (hH7.mul_left 2)
  calc
    ε n * nevanlinnaWeight (atoms n)
        ≤ ε n * (2 / (1 + |atoms n|)) :=
      mul_le_mul_of_nonneg_left
        (nevanlinnaWeight_le_two_div_one_add_abs (atoms n)) (hε n)
    _ = 2 * (ε n / (1 + |atoms n|)) := by ring

/-- `(H7)` is exactly strong enough for the countable weighted Dirac measure to satisfy `H0`. -/
theorem integrable_nevanlinnaWeight_countableWeightedDirac_of_H7
    {ε atoms : ℕ → ℝ} (hε : ∀ n, 0 ≤ ε n)
    (hH7 : DiscreteHerglotzH7 ε atoms) :
    Integrable nevanlinnaWeight (HTGeometry.countableWeightedDirac ε atoms) := by
  apply HTGeometry.integrable_countableWeightedDirac hε
      (f := nevanlinnaWeight) (by
        apply Measurable.aestronglyMeasurable
        unfold nevanlinnaWeight
        fun_prop)
  simpa [abs_of_pos (nevanlinnaWeight_pos _)] using
    summable_nevanlinnaWeight_of_discreteHerglotzH7 hε hH7

/-- Strictly positive distinct atoms give the discrete measure infinite topological support. -/
theorem infinite_support_countableWeightedDirac
    {ε atoms : ℕ → ℝ} (hinj : Function.Injective atoms)
    (hε : ∀ n, 0 < ε n) :
    (HTGeometry.countableWeightedDirac ε atoms).support.Infinite := by
  apply support_infinite_of_injective
      (HTGeometry.countableWeightedDirac ε atoms) hinj
  intro n
  rw [HTGeometry.countableWeightedDirac_singleton ε hinj n]
  exact ENNReal.ofReal_pos.mpr (hε n)

/-- Escape of the real support makes every bounded support packet finite. -/
theorem finite_abs_atoms_le_of_tendsto
    {atoms : ℕ → ℝ} (hescape : Tendsto (fun n => |atoms n|) atTop atTop)
    (R : ℝ) : Set.Finite {n | |atoms n| ≤ R} := by
  have hev : ∀ᶠ n in cofinite, R < |atoms n| := by
    rw [Nat.cofinite_eq_atTop]
    exact hescape.eventually_gt_atTop R
  simpa only [not_lt] using Filter.eventually_cofinite.mp hev

/-- Pole carrier of a discrete real skeleton. -/
def discreteHerglotzPoleSet (atoms : ℕ → ℝ) : Set ℂ :=
  Set.range fun n => (atoms n : ℂ)

/-- An escaping real skeleton has a discrete, hence closed, pole carrier. -/
theorem isOpen_compl_discreteHerglotzPoleSet
    {atoms : ℕ → ℝ} (hescape : Tendsto (fun n => |atoms n|) atTop atTop) :
    IsOpen (discreteHerglotzPoleSet atoms)ᶜ := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  let R : ℝ := ‖z‖ + 1
  let F : Set ℕ := {n | |atoms n| ≤ R}
  have hF : F.Finite := finite_abs_atoms_le_of_tendsto hescape R
  let E : Set ℂ := (fun n : ℕ => (atoms n : ℂ)) '' F
  have hE : E.Finite := hF.image _
  refine ⟨Metric.ball z 1 \ E, ?_, Metric.isOpen_ball.sdiff hE.isClosed, ?_⟩
  · intro w hw
    rw [Set.mem_compl_iff]
    rintro ⟨n, rfl⟩
    apply hw.2
    refine ⟨n, ?_, rfl⟩
    change |atoms n| ≤ R
    have hdist : ‖(atoms n : ℂ) - z‖ < 1 := by
      simpa [Complex.dist_eq, norm_sub_rev] using Metric.mem_ball.mp hw.1
    have hnorm : ‖(atoms n : ℂ)‖ ≤ ‖z‖ + 1 := by
      calc
        ‖(atoms n : ℂ)‖ ≤ ‖(atoms n : ℂ) - z‖ + ‖z‖ := by
          simpa using norm_add_le ((atoms n : ℂ) - z) z
        _ ≤ ‖z‖ + 1 := by linarith
    change |atoms n| ≤ R
    simpa [R, Complex.norm_real, Real.norm_eq_abs] using hnorm
  · constructor
    · exact Metric.mem_ball_self zero_lt_one
    · intro hzE
      rcases hzE with ⟨n, hn, hnz⟩
      apply hz
      exact ⟨n, hnz⟩

/-- One term of the literal unregularized series `(1)`. -/
def discreteHerglotzCauchyTerm
    (ε atoms : ℕ → ℝ) (u : BoundedRealSequence) (n : ℕ) (z : ℂ) : ℂ :=
  ((ε n * Real.exp (u n) : ℝ) : ℂ) * ((atoms n : ℂ) - z)⁻¹

/-- Literal discrete Cauchy series `(1)`. -/
def discreteHerglotzCauchySeries
    (ε atoms : ℕ → ℝ) (u : BoundedRealSequence) (z : ℂ) : ℂ :=
  ∑' n, discreteHerglotzCauchyTerm ε atoms u n z

private theorem exp_boundedSequence_le (u : BoundedRealSequence) (n : ℕ) :
    Real.exp (u n) ≤ Real.exp ‖u‖ := by
  apply Real.exp_le_exp.mpr
  exact (le_abs_self (u n)).trans
    (by simpa [Real.norm_eq_abs] using
      lp.norm_apply_le_norm ENNReal.top_ne_zero u n)

/-- `(H7)` gives normal convergence of `(1)` away from its discrete pole carrier. -/
theorem summableLocallyUniformlyOn_discreteHerglotzCauchy_off_poles
    {ε atoms : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hH7 : DiscreteHerglotzH7 ε atoms)
    (hescape : Tendsto (fun n => |atoms n|) atTop atTop)
    (u : BoundedRealSequence) :
    SummableLocallyUniformlyOn
      (fun n => discreteHerglotzCauchyTerm ε atoms u n)
      (discreteHerglotzPoleSet atoms)ᶜ := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually
    (isOpen_compl_discreteHerglotzPoleSet hescape)
  intro K hK hKc
  obtain ⟨R, hR⟩ := hKc.isBounded.exists_norm_le
  let C : ℝ := 2 * Real.exp ‖u‖
  refine ⟨fun n => C * (ε n / (1 + |atoms n|)), hH7.mul_left C, ?_⟩
  have hfinite := finite_abs_atoms_le_of_tendsto hescape (2 * (R + 1))
  filter_upwards [hfinite.eventually_cofinite_notMem] with n hn
  intro z hz
  have hatomLarge : 2 * (R + 1) < |atoms n| := by
    simpa using lt_of_not_ge hn
  have hzNorm : ‖z‖ ≤ R := hR z hz
  have hden : (1 + |atoms n|) / 2 ≤ ‖(atoms n : ℂ) - z‖ := by
    calc
      (1 + |atoms n|) / 2 ≤ |atoms n| - R := by linarith
      _ ≤ ‖(atoms n : ℂ)‖ - ‖z‖ := by
        simp only [Complex.norm_real, Real.norm_eq_abs]
        linarith
      _ ≤ ‖(atoms n : ℂ) - z‖ := norm_sub_norm_le _ _
  have hdenpos : 0 < (1 + |atoms n|) / 2 := by positivity
  have hinv : ‖(atoms n : ℂ) - z‖⁻¹ ≤ 2 / (1 + |atoms n|) := by
    have hanti := one_div_le_one_div_of_le hdenpos hden
    simpa [one_div, div_eq_mul_inv] using hanti
  rw [discreteHerglotzCauchyTerm, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (mul_pos (hε n) (Real.exp_pos _))]
  calc
    ε n * Real.exp (u n) * ‖(atoms n : ℂ) - z‖⁻¹
        ≤ ε n * Real.exp ‖u‖ * ‖(atoms n : ℂ) - z‖⁻¹ := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left (exp_boundedSequence_le u n) (hε n).le
      · positivity
    _ ≤ ε n * Real.exp ‖u‖ * (2 / (1 + |atoms n|)) :=
      mul_le_mul_of_nonneg_left hinv
        (mul_nonneg (hε n).le (Real.exp_pos _).le)
    _ = C * (ε n / (1 + |atoms n|)) := by
      dsimp [C]
      ring

/-- The literal discrete series is holomorphic away from its poles. -/
theorem differentiableOn_discreteHerglotzCauchySeries_off_poles
    {ε atoms : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hH7 : DiscreteHerglotzH7 ε atoms)
    (hescape : Tendsto (fun n => |atoms n|) atTop atTop)
    (u : BoundedRealSequence) :
    DifferentiableOn ℂ (discreteHerglotzCauchySeries ε atoms u)
      (discreteHerglotzPoleSet atoms)ᶜ := by
  apply SummableLocallyUniformlyOn.differentiableOn
    (isOpen_compl_discreteHerglotzPoleSet hescape)
    (summableLocallyUniformlyOn_discreteHerglotzCauchy_off_poles hε hH7 hescape u)
  intro n z hz
  have hne : (atoms n : ℂ) - z ≠ 0 := by
    intro h
    apply hz
    exact ⟨n, sub_eq_zero.mp h⟩
  have hdiff : DifferentiableAt ℂ (fun w : ℂ => ((atoms n : ℂ) - w)⁻¹) z :=
    ((differentiableAt_const (c := (atoms n : ℂ))).sub differentiableAt_id).inv hne
  exact hdiff.const_mul ((ε n * Real.exp (u n) : ℝ) : ℂ)

/-- Pole set of a restricted subfamily. -/
def discreteHerglotzPoleSetOn (atoms : ℕ → ℝ) (S : Set ℕ) : Set ℂ :=
  Set.range fun n : S => (atoms n : ℂ)

private theorem finite_abs_atoms_le_on
    {atoms : ℕ → ℝ} (hescape : Tendsto (fun n => |atoms n|) atTop atTop)
    (S : Set ℕ) (R : ℝ) :
    Set.Finite {n : S | |atoms n| ≤ R} := by
  change ((Subtype.val : S → ℕ) ⁻¹' {n | |atoms n| ≤ R}).Finite
  exact (finite_abs_atoms_le_of_tendsto hescape R).preimage
    (Set.injOn_of_injective Subtype.val_injective)

private theorem isOpen_compl_discreteHerglotzPoleSetOn
    {atoms : ℕ → ℝ} (hescape : Tendsto (fun n => |atoms n|) atTop atTop)
    (S : Set ℕ) :
    IsOpen (discreteHerglotzPoleSetOn atoms S)ᶜ := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  let R : ℝ := ‖z‖ + 1
  let F : Set S := {n | |atoms n| ≤ R}
  have hF : F.Finite := finite_abs_atoms_le_on hescape S R
  let E : Set ℂ := (fun n : S => (atoms n : ℂ)) '' F
  have hE : E.Finite := hF.image _
  refine ⟨Metric.ball z 1 \ E, ?_, Metric.isOpen_ball.sdiff hE.isClosed, ?_⟩
  · intro w hw
    rw [Set.mem_compl_iff]
    rintro ⟨n, rfl⟩
    apply hw.2
    refine ⟨n, ?_, rfl⟩
    have hdist : ‖(atoms n : ℂ) - z‖ < 1 := by
      simpa [Complex.dist_eq, norm_sub_rev] using Metric.mem_ball.mp hw.1
    have hnorm : ‖(atoms n : ℂ)‖ ≤ ‖z‖ + 1 := by
      calc
        ‖(atoms n : ℂ)‖ ≤ ‖(atoms n : ℂ) - z‖ + ‖z‖ := by
          simpa using norm_add_le ((atoms n : ℂ) - z) z
        _ ≤ ‖z‖ + 1 := by linarith
    change |atoms (n : ℕ)| ≤ R
    simpa [R, Complex.norm_real, Real.norm_eq_abs] using hnorm
  · constructor
    · exact Metric.mem_ball_self zero_lt_one
    · intro hzE
      rcases hzE with ⟨n, hn, hnz⟩
      apply hz
      exact ⟨n, hnz⟩

private theorem summableLocallyUniformlyOn_discreteHerglotzCauchy_on_off_poles
    {ε atoms : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hH7 : DiscreteHerglotzH7 ε atoms)
    (hescape : Tendsto (fun n => |atoms n|) atTop atTop)
    (S : Set ℕ) (u : BoundedRealSequence) :
    SummableLocallyUniformlyOn
      (fun n : S => discreteHerglotzCauchyTerm ε atoms u n)
      (discreteHerglotzPoleSetOn atoms S)ᶜ := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually
    (isOpen_compl_discreteHerglotzPoleSetOn hescape S)
  intro K hK hKc
  obtain ⟨R, hR⟩ := hKc.isBounded.exists_norm_le
  let C : ℝ := 2 * Real.exp ‖u‖
  refine ⟨fun n : S => C * (ε n / (1 + |atoms n|)),
    (hH7.mul_left C).subtype S, ?_⟩
  have hfinite := finite_abs_atoms_le_on hescape S (2 * (R + 1))
  filter_upwards [hfinite.eventually_cofinite_notMem] with n hn
  intro z hz
  have hatomLarge : 2 * (R + 1) < |atoms n| := by
    simpa using lt_of_not_ge hn
  have hzNorm : ‖z‖ ≤ R := hR z hz
  have hden : (1 + |atoms n|) / 2 ≤ ‖(atoms n : ℂ) - z‖ := by
    calc
      (1 + |atoms n|) / 2 ≤ |atoms n| - R := by linarith
      _ ≤ ‖(atoms n : ℂ)‖ - ‖z‖ := by
        simp only [Complex.norm_real, Real.norm_eq_abs]
        linarith
      _ ≤ ‖(atoms n : ℂ) - z‖ := norm_sub_norm_le _ _
  have hdenpos : 0 < (1 + |atoms n|) / 2 := by positivity
  have hinv : ‖(atoms n : ℂ) - z‖⁻¹ ≤ 2 / (1 + |atoms n|) := by
    have hanti := one_div_le_one_div_of_le hdenpos hden
    simpa [one_div, div_eq_mul_inv] using hanti
  rw [discreteHerglotzCauchyTerm, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (mul_pos (hε n) (Real.exp_pos _))]
  calc
    ε n * Real.exp (u n) * ‖(atoms n : ℂ) - z‖⁻¹
        ≤ ε n * Real.exp ‖u‖ * ‖(atoms n : ℂ) - z‖⁻¹ := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left (exp_boundedSequence_le u n) (hε n).le
      · positivity
    _ ≤ ε n * Real.exp ‖u‖ * (2 / (1 + |atoms n|)) :=
      mul_le_mul_of_nonneg_left hinv
        (mul_nonneg (hε n).le (Real.exp_pos _).le)
    _ = C * (ε n / (1 + |atoms n|)) := by
      dsimp [C]
      ring

private def discreteHerglotzCauchyTail
    (ε atoms : ℕ → ℝ) (u : BoundedRealSequence) (n₀ : ℕ) (z : ℂ) : ℂ :=
  ∑' n : {n : ℕ // n ≠ n₀}, discreteHerglotzCauchyTerm ε atoms u n z

private theorem differentientiableOn_discreteHerglotzCauchyTail
    {ε atoms : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hH7 : DiscreteHerglotzH7 ε atoms)
    (hescape : Tendsto (fun n => |atoms n|) atTop atTop)
    (u : BoundedRealSequence) (n₀ : ℕ) :
    DifferentiableOn ℂ (discreteHerglotzCauchyTail ε atoms u n₀)
      (discreteHerglotzPoleSetOn atoms {n | n ≠ n₀})ᶜ := by
  apply SummableLocallyUniformlyOn.differentiableOn
    (isOpen_compl_discreteHerglotzPoleSetOn hescape {n | n ≠ n₀})
    (summableLocallyUniformlyOn_discreteHerglotzCauchy_on_off_poles
      hε hH7 hescape {n | n ≠ n₀} u)
  intro n z hz
  have hne : (atoms n : ℂ) - z ≠ 0 := by
    intro h
    apply hz
    exact ⟨n, sub_eq_zero.mp h⟩
  have hdiff : DifferentiableAt ℂ (fun w : ℂ => ((atoms n : ℂ) - w)⁻¹) z :=
    ((differentiableAt_const (c := (atoms n : ℂ))).sub differentiableAt_id).inv hne
  exact hdiff.const_mul ((ε n * Real.exp (u n) : ℝ) : ℂ)

private theorem summable_discreteHerglotzCauchyTerm
    {ε atoms : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hH7 : DiscreteHerglotzH7 ε atoms)
    (hescape : Tendsto (fun n => |atoms n|) atTop atTop)
    (u : BoundedRealSequence) (z : ℂ) :
    Summable fun n => discreteHerglotzCauchyTerm ε atoms u n z := by
  let C : ℝ := 2 * Real.exp ‖u‖
  apply Summable.of_norm_bounded_eventually (hH7.mul_left C)
  have hfinite := finite_abs_atoms_le_of_tendsto hescape (2 * (‖z‖ + 1))
  filter_upwards [hfinite.eventually_cofinite_notMem] with n hn
  have hatomLarge : 2 * (‖z‖ + 1) < |atoms n| := by
    simpa using lt_of_not_ge hn
  have hden : (1 + |atoms n|) / 2 ≤ ‖(atoms n : ℂ) - z‖ := by
    calc
      (1 + |atoms n|) / 2 ≤ |atoms n| - ‖z‖ := by linarith
      _ = ‖(atoms n : ℂ)‖ - ‖z‖ := by
        simp [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖(atoms n : ℂ) - z‖ := norm_sub_norm_le _ _
  have hdenpos : 0 < (1 + |atoms n|) / 2 := by positivity
  have hinv : ‖(atoms n : ℂ) - z‖⁻¹ ≤ 2 / (1 + |atoms n|) := by
    have hanti := one_div_le_one_div_of_le hdenpos hden
    simpa [one_div, div_eq_mul_inv] using hanti
  rw [discreteHerglotzCauchyTerm, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (mul_pos (hε n) (Real.exp_pos _))]
  calc
    ε n * Real.exp (u n) * ‖(atoms n : ℂ) - z‖⁻¹
        ≤ ε n * Real.exp ‖u‖ * ‖(atoms n : ℂ) - z‖⁻¹ := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left (exp_boundedSequence_le u n) (hε n).le
      · positivity
    _ ≤ ε n * Real.exp ‖u‖ * (2 / (1 + |atoms n|)) :=
      mul_le_mul_of_nonneg_left hinv
        (mul_nonneg (hε n).le (Real.exp_pos _).le)
    _ = C * (ε n / (1 + |atoms n|)) := by
      dsimp [C]
      ring

private theorem discreteHerglotzCauchySeries_eq_term_add_tail
    {ε atoms : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hH7 : DiscreteHerglotzH7 ε atoms)
    (hescape : Tendsto (fun n => |atoms n|) atTop atTop)
    (u : BoundedRealSequence) (n₀ : ℕ) :
    discreteHerglotzCauchySeries ε atoms u =
      fun z => discreteHerglotzCauchyTerm ε atoms u n₀ z +
        discreteHerglotzCauchyTail ε atoms u n₀ z := by
  funext z
  rw [discreteHerglotzCauchySeries,
    (summable_discreteHerglotzCauchyTerm hε hH7 hescape u z).tsum_eq_add_tsum_ite n₀]
  congr 1
  unfold discreteHerglotzCauchyTail
  let S : Set ℕ := {n | n ≠ n₀}
  calc
    (∑' n : ℕ, if n = n₀ then 0 else discreteHerglotzCauchyTerm ε atoms u n z) =
        ∑' n : ℕ, S.indicator
          (fun n => discreteHerglotzCauchyTerm ε atoms u n z) n := by
      apply tsum_congr
      intro n
      by_cases hn : n = n₀ <;> simp [S, hn]
    _ = ∑' n : S, discreteHerglotzCauchyTerm ε atoms u n z :=
      (tsum_subtype S (fun n => discreteHerglotzCauchyTerm ε atoms u n z)).symm

/-- Under the exact discrete hypotheses, series `(1)` is globally meromorphic, with its only
possible poles on the listed escaping real skeleton. -/
theorem meromorphicOn_discreteHerglotzCauchySeries
    {ε atoms : ℕ → ℝ} (hinj : Function.Injective atoms)
    (hε : ∀ n, 0 < ε n) (hH7 : DiscreteHerglotzH7 ε atoms)
    (hescape : Tendsto (fun n => |atoms n|) atTop atTop)
    (u : BoundedRealSequence) :
    MeromorphicOn (discreteHerglotzCauchySeries ε atoms u) Set.univ := by
  intro z hz
  by_cases hpole : z ∈ discreteHerglotzPoleSet atoms
  · rcases hpole with ⟨n₀, rfl⟩
    let S : Set ℕ := {n | n ≠ n₀}
    have hcenter : (atoms n₀ : ℂ) ∈ (discreteHerglotzPoleSetOn atoms S)ᶜ := by
      rw [Set.mem_compl_iff]
      rintro ⟨n, hn⟩
      apply n.property
      exact hinj (Complex.ofReal_injective hn)
    have htailDiff :=
      differentientiableOn_discreteHerglotzCauchyTail hε hH7 hescape u n₀
    have htailNhd := DifferentiableOn.analyticOnNhd htailDiff
      (isOpen_compl_discreteHerglotzPoleSetOn hescape S)
    have htail : AnalyticAt ℂ (discreteHerglotzCauchyTail ε atoms u n₀)
        (atoms n₀ : ℂ) := htailNhd (atoms n₀ : ℂ) hcenter
    have hden : AnalyticAt ℂ (fun z : ℂ => (atoms n₀ : ℂ) - z) (atoms n₀ : ℂ) :=
      analyticAt_const.sub analyticAt_id
    have hterm : MeromorphicAt (discreteHerglotzCauchyTerm ε atoms u n₀)
        (atoms n₀ : ℂ) := by
      unfold discreteHerglotzCauchyTerm
      exact (MeromorphicAt.const _ _).mul hden.meromorphicAt.inv
    rw [discreteHerglotzCauchySeries_eq_term_add_tail hε hH7 hescape u n₀]
    exact hterm.add htail.meromorphicAt
  · exact ((differentiableOn_discreteHerglotzCauchySeries_off_poles
      hε hH7 hescape u).analyticOnNhd
        (isOpen_compl_discreteHerglotzPoleSet hescape) z hpole).meromorphicAt

/-- Bochner integration against a countable weighted Dirac measure, for complex values. -/
theorem integral_countableWeightedDirac_complex
    {w x : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    {f : ℝ → ℂ} (hint : Integrable f (HTGeometry.countableWeightedDirac w x)) :
    ∫ y, f y ∂(HTGeometry.countableWeightedDirac w x) =
      ∑' n, (w n : ℂ) * f (x n) := by
  rw [HTGeometry.countableWeightedDirac] at hint ⊢
  rw [integral_sum_measure hint]
  refine tsum_congr fun n => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw n)]
  simp [Complex.real_smul]

/-- A bounded exponential parameter preserves regularized-kernel integrability. -/
theorem integrable_regularizedHerglotzKernel_mul_exp_Linfty
    (μ : Measure ℝ) (hH0 : Integrable nevanlinnaWeight μ)
    (u : Lp ℝ ⊤ μ) {z : ℂ} (hz : z.im ≠ 0) :
    Integrable
      (fun t => regularizedHerglotzKernel t z * (Real.exp (u t) : ℂ)) μ := by
  have hk := integrable_regularizedHerglotzKernel_of_nevanlinna μ hH0 hz
  have hexpMeas : AEStronglyMeasurable (fun t : ℝ => (Real.exp (u t) : ℂ)) μ := by
    apply Measurable.aestronglyMeasurable
    exact Complex.continuous_ofReal.measurable.comp
      (Real.measurable_exp.comp (Lp.stronglyMeasurable u).measurable)
  have hmeas := hk.aestronglyMeasurable.mul hexpMeas
  refine Integrable.mono' (hk.norm.const_mul (Real.exp ‖u‖)) hmeas ?_
  have hu : ∀ᵐ t ∂μ, |u t| ≤ ‖u‖ := by
    simpa only [Real.norm_eq_abs, Lp.norm_def, lpNorm, if_pos (Lp.memLp u).1] using
      ae_le_lpNorm_exponent_top (Lp.memLp u)
  filter_upwards [hu] with t ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (u t) ≤ Real.exp ‖u‖ :=
    Real.exp_le_exp.mpr ((le_abs_self (u t)).trans ht)
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hexp (norm_nonneg
    (regularizedHerglotzKernel t z))

/-- Real subtraction constant in the discrete regularized presentation. -/
def discreteHerglotzRegularizationConstant
    (ε atoms : ℕ → ℝ) (u : BoundedRealSequence) : ℝ :=
  ∑' n, ε n * Real.exp (u n) * atoms n / (1 + atoms n ^ 2)

/-- The subtraction kernel has the same `(H7)` majorant. -/
theorem abs_div_one_add_sq_le_two_div_one_add_abs (t : ℝ) :
    |t| / (1 + t ^ 2) ≤ 2 / (1 + |t|) := by
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 1 + t ^ 2)
    (by positivity : (0 : ℝ) < 1 + |t|)).2
  nlinarith [sq_nonneg (|t| - 1), sq_abs t]

/-- The real regularization constant converges absolutely under `(H7)`. -/
theorem summable_discreteHerglotzRegularizationConstant
    {ε atoms : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hH7 : DiscreteHerglotzH7 ε atoms) (u : BoundedRealSequence) :
    Summable fun n => ε n * Real.exp (u n) * atoms n / (1 + atoms n ^ 2) := by
  let C : ℝ := 2 * Real.exp ‖u‖
  apply Summable.of_norm_bounded (hH7.mul_left C)
  intro n
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_of_pos (hε n),
    abs_of_pos (Real.exp_pos _), abs_of_pos (by positivity : (0 : ℝ) < 1 + atoms n ^ 2)]
  calc
    ε n * Real.exp (u n) * |atoms n| / (1 + atoms n ^ 2)
        ≤ ε n * Real.exp ‖u‖ * (2 / (1 + |atoms n|)) := by
      calc
        ε n * Real.exp (u n) * |atoms n| / (1 + atoms n ^ 2)
            = (ε n * Real.exp (u n)) * (|atoms n| / (1 + atoms n ^ 2)) := by ring
        _ ≤ (ε n * Real.exp ‖u‖) * (2 / (1 + |atoms n|)) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left (exp_boundedSequence_le u n) (hε n).le
          · exact abs_div_one_add_sq_le_two_div_one_add_abs (atoms n)
          · positivity
          · exact mul_nonneg (hε n).le (Real.exp_pos _).le
    _ = C * (ε n / (1 + |atoms n|)) := by
      dsimp [C]
      ring

/-- Exact discrete identity: the literal regularized integral is the normally convergent
unregularized series minus one real constant. -/
theorem integral_regularizedHerglotz_countableWeightedDirac_eq_series_sub_const
    {ε atoms : ℕ → ℝ} (hinj : Function.Injective atoms)
    (hε : ∀ n, 0 < ε n) (hH7 : DiscreteHerglotzH7 ε atoms)
    (hescape : Tendsto (fun n => |atoms n|) atTop atTop)
    (u : BoundedRealSequence) {z : ℂ}
    (hzim : z.im ≠ 0) :
    ∫ t, regularizedHerglotzKernel t z *
        (Real.exp (countableWeightedDiracLinftyEquiv hinj hε u t) : ℂ)
          ∂(HTGeometry.countableWeightedDirac ε atoms) =
      discreteHerglotzCauchySeries ε atoms u z -
        (discreteHerglotzRegularizationConstant ε atoms u : ℂ) := by
  let μ := HTGeometry.countableWeightedDirac ε atoms
  let e := countableWeightedDiracLinftyEquiv hinj hε
  have hz : z ∈ (discreteHerglotzPoleSet atoms)ᶜ := by
    rw [Set.mem_compl_iff]
    rintro ⟨n, hn⟩
    apply hzim
    rw [← hn]
    simp
  have hH0 := integrable_nevanlinnaWeight_countableWeightedDirac_of_H7
    (fun n => (hε n).le) hH7
  have hint := integrable_regularizedHerglotzKernel_mul_exp_Linfty μ hH0 (e u) hzim
  rw [integral_countableWeightedDirac_complex (fun n => (hε n).le) hint]
  have hCauchy : Summable fun n => discreteHerglotzCauchyTerm ε atoms u n z :=
    (summableLocallyUniformlyOn_discreteHerglotzCauchy_off_poles
      hε hH7 hescape u).summable hz
  have hconstReal :=
    summable_discreteHerglotzRegularizationConstant hε hH7 u
  have hconstComplex : Summable fun n =>
      ((ε n * Real.exp (u n) * atoms n / (1 + atoms n ^ 2) : ℝ) : ℂ) :=
    Complex.summable_ofReal.mpr hconstReal
  unfold discreteHerglotzCauchySeries discreteHerglotzRegularizationConstant
  rw [Complex.ofReal_tsum]
  rw [← hCauchy.tsum_sub hconstComplex]
  apply tsum_congr
  intro n
  rw [countableWeightedDiracLinftyEquiv_apply_at hinj hε]
  simp only [discreteHerglotzCauchyTerm, regularizedHerglotzKernel]
  push_cast
  ring

end

end GaloisForLFunctions.HTGeometry
