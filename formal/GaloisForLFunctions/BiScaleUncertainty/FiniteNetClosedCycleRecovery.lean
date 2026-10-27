import GaloisForLFunctions.BiScaleUncertainty.ClosedCycleScalarRecovery

/-!
# Closed-cycle recovery on an arbitrary finite net

The exact positive-collar estimate depends only on coverage and the source
modulus. Uniform spacing is unnecessary: every finite net gives the same
separate pair and spoke error coefficients.
-/

noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.EnergyCycle
set_option autoImplicit false
variable {ι : Type*} {E : ℝ}

/-- One pair and one spoke at each of the supplied sample locations. -/
def finiteNetCycle (z : ι → ℝ) (n : ℕ) (i : Bool × ι) : List ℝ :=
  if i.1 then [z i.2 / ((n : ℝ) + 1), -(z i.2 / ((n : ℝ) + 1))] else spoke n (z i.2)

/-- All observations are literal closed cycles. -/
theorem finiteNetCycle_sum (z : ι → ℝ) (n : ℕ) (i : Bool × ι) :
    (finiteNetCycle z n i).sum = 0 := by
  rcases i with ⟨b, i⟩
  cases b <;> simp [finiteNetCycle, spoke_sum]

/-- The observation family has exactly two labels per sample. -/
theorem finiteNetCycle_count [Fintype ι] : Fintype.card (Bool × ι) = 2 * Fintype.card ι := by simp

/-- Every observation uses at most the stated maximum order. -/
theorem finiteNetCycle_length_le (z : ι → ℝ) (n : ℕ) (i : Bool × ι) :
    (finiteNetCycle z n i).length ≤ max 2 (n + 2) := by
  rcases i with ⟨b, i⟩
  cases b
  · change (spoke n (z i)).length ≤ max 2 (n + 2)
    rw [spoke_length]
    exact le_max_right _ _
  · change 2 ≤ max 2 (n + 2)
    exact le_max_left _ _

variable [Fintype ι] [Nonempty ι]

/-- Actual maximum pair discrepancy over the finite sample set. -/
def finiteNetPairError (f g : LevyEnergySource E) (z : ι → ℝ) (n : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : ι =>
    |value f (finiteNetCycle z n (true, i)) - value g (finiteNetCycle z n (true, i))|)

/-- Actual maximum spoke discrepancy over the same sample set. -/
def finiteNetSpokeError (f g : LevyEnergySource E) (z : ι → ℝ) (n : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : ι =>
    |value f (finiteNetCycle z n (false, i)) - value g (finiteNetCycle z n (false, i))|)

/-- Positive-collar conditioning holds at every arbitrary sample in the window. -/
theorem finiteNet_sample_recovery (f g : LevyEnergySource E) (z : ι → ℝ)
    {R ρ κ : ℝ} (hκ : 0 < κ) (n : ℕ) (hn : R ≤ ((n : ℝ) + 1) * ρ)
    (hz : ∀ i, |z i| ≤ R)
    (hf : ∀ t, |t| ≤ ρ → κ ≤ f.correlation t)
    (hg : ∀ t, |t| ≤ ρ → κ ≤ g.correlation t) (i : ι) :
    |f.correlation (z i) - g.correlation (z i)| ≤
      (finiteNetSpokeError f g z n + ((n : ℝ) + 1) * finiteNetPairError f g z n / (2 * κ)) /
        κ ^ (n + 1) := by
  have hp : 0 < (n : ℝ) + 1 := by positivity
  have hy : |z i / ((n : ℝ) + 1)| ≤ ρ := by
    rw [abs_div, abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    simpa only [mul_comm] using (hz i).trans hn
  have hpair := Finset.le_sup' (s := Finset.univ) (fun j : ι =>
    |value f (finiteNetCycle z n (true, j)) - value g (finiteNetCycle z n (true, j))|)
    (Finset.mem_univ i)
  have hspoke := Finset.le_sup' (s := Finset.univ) (fun j : ι =>
    |value f (finiteNetCycle z n (false, j)) - value g (finiteNetCycle z n (false, j))|)
    (Finset.mem_univ i)
  apply (correlation_recovery_of_collar f g n (z i) hκ (hf _ hy) (hg _ hy)).trans
  apply div_le_div_of_nonneg_right _ (pow_pos hκ (n + 1)).le
  exact add_le_add hspoke (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpair hp.le) (mul_pos (by norm_num) hκ).le)

/-- Every point covered by the finite net pays exactly two modulus errors. -/
theorem finiteNet_window_recovery (f g : LevyEnergySource E) (z : ι → ℝ)
    {R η ρ κ : ℝ} (hκ : 0 < κ) (n : ℕ) (hn : R ≤ ((n : ℝ) + 1) * ρ)
    (hz : ∀ i, |z i| ≤ R)
    (hnet : ∀ x : ℝ, |x| ≤ R → ∃ i, |x - z i| ≤ η)
    (hf : ∀ t, |t| ≤ ρ → κ ≤ f.correlation t)
    (hg : ∀ t, |t| ≤ ρ → κ ≤ g.correlation t)
    (ω : ℝ → ℝ)
    (hωf : ∀ x y, |x - y| ≤ η → |f.correlation x - f.correlation y| ≤ ω η)
    (hωg : ∀ x y, |x - y| ≤ η → |g.correlation x - g.correlation y| ≤ ω η)
    {x : ℝ} (hx : |x| ≤ R) :
    |f.correlation x - g.correlation x| ≤
      (finiteNetSpokeError f g z n + ((n : ℝ) + 1) * finiteNetPairError f g z n / (2 * κ)) /
        κ ^ (n + 1) + 2 * ω η := by
  obtain ⟨i, hi⟩ := hnet x hx
  have hm := finiteNet_sample_recovery f g z hκ n hn hz hf hg i
  have hfi := hωf x (z i) hi
  have hgi := hωg x (z i) hi
  have ht : |f.correlation x - g.correlation x| ≤
      |f.correlation x - f.correlation (z i)| + |f.correlation (z i) - g.correlation (z i)| +
        |g.correlation x - g.correlation (z i)| := by
    calc
      _ = |(f.correlation x - f.correlation (z i)) +
          (f.correlation (z i) - g.correlation (z i)) -
          (g.correlation x - g.correlation (z i))| := by congr 1; ring
      _ ≤ _ := (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  linarith only [ht, hm, hfi, hgi]

/-- Any finite net of the common support gives the exact global uniform recovery bound. -/
theorem finiteNet_global_recovery_norm (f g : LevyEnergySource E) (z : ι → ℝ)
    {R η ρ κ : ℝ} (hη : 0 ≤ η) (hκ : 0 < κ)
    (n : ℕ) (hn : R ≤ ((n : ℝ) + 1) * ρ)
    (hz : ∀ i, |z i| ≤ R)
    (hnet : ∀ x : ℝ, |x| ≤ R → ∃ i, |x - z i| ≤ η)
    (hf : ∀ t, |t| ≤ ρ → κ ≤ f.correlation t)
    (hg : ∀ t, |t| ≤ ρ → κ ≤ g.correlation t)
    (ω : ℝ → ℝ)
    (hωf : ∀ x y, |x - y| ≤ η → |f.correlation x - f.correlation y| ≤ ω η)
    (hωg : ∀ x y, |x - y| ≤ η → |g.correlation x - g.correlation y| ≤ ω η)
    (hsf : ∀ x, R < |x| → f.correlation x = 0)
    (hsg : ∀ x, R < |x| → g.correlation x = 0) :
    ‖f.complexCorrelation - g.complexCorrelation‖ ≤
      (finiteNetSpokeError f g z n + ((n : ℝ) + 1) * finiteNetPairError f g z n / (2 * κ)) /
        κ ^ (n + 1) + 2 * ω η := by
  apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
  intro x
  change ‖(f.correlation x : ℂ) - (g.correlation x : ℂ)‖ ≤ _
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  by_cases hx : |x| ≤ R
  · exact finiteNet_window_recovery f g z hκ n hn hz hnet hf hg ω hωf hωg hx
  · rw [hsf x (lt_of_not_ge hx), hsg x (lt_of_not_ge hx), sub_self, abs_zero]
    have hω : 0 ≤ ω η := by
      simpa only [sub_self, abs_zero] using hωf 0 0 (by simpa using hη)
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hp : 0 ≤ finiteNetPairError f g z n := (abs_nonneg _).trans
      (Finset.le_sup' (s := Finset.univ) (fun j : ι =>
        |value f (finiteNetCycle z n (true, j)) - value g (finiteNetCycle z n (true, j))|)
        (Finset.mem_univ i))
    have hs : 0 ≤ finiteNetSpokeError f g z n := (abs_nonneg _).trans
      (Finset.le_sup' (s := Finset.univ) (fun j : ι =>
        |value f (finiteNetCycle z n (false, j)) - value g (finiteNetCycle z n (false, j))|)
        (Finset.mem_univ i))
    exact add_nonneg (div_nonneg
      (add_nonneg hs (div_nonneg (mul_nonneg (by positivity) hp) (mul_pos (by norm_num) hκ).le))
      (pow_pos hκ (n + 1)).le) (mul_nonneg (by norm_num) hω)

/-- Maximum fitting error against an arbitrary measured array on the finite net. -/
def finiteNetDataResidual (f : LevyEnergySource E) (z : ι → ℝ) (n : ℕ)
    (a : Bool × ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i => |value f (finiteNetCycle z n i) - a i|)

/-- Two fits to the same array differ by at most the sum of their fitting errors. -/
theorem finiteNet_discrepancy_le_residual_sum (f g : LevyEnergySource E) (z : ι → ℝ)
    (n : ℕ) (a : Bool × ι → ℝ) (i : Bool × ι) :
    |value f (finiteNetCycle z n i) - value g (finiteNetCycle z n i)| ≤
      finiteNetDataResidual f z n a + finiteNetDataResidual g z n a := by
  calc
    _ = |(value f (finiteNetCycle z n i) - a i) -
        (value g (finiteNetCycle z n i) - a i)| := by congr 1; ring
    _ ≤ _ := (abs_sub _ _).trans (add_le_add
      (Finset.le_sup' (fun j : Bool × ι => |value f (finiteNetCycle z n j) - a j|)
        (Finset.mem_univ i))
      (Finset.le_sup' (fun j : Bool × ι => |value g (finiteNetCycle z n j) - a j|)
        (Finset.mem_univ i)))

/-- Recovery from arbitrary measured data retains the exact collar amplification. -/
theorem finiteNet_recovery_from_measured_array (f g : LevyEnergySource E) (z : ι → ℝ)
    {R η ρ κ : ℝ} (hη : 0 ≤ η) (hκ : 0 < κ)
    (n : ℕ) (hn : R ≤ ((n : ℝ) + 1) * ρ)
    (hz : ∀ i, |z i| ≤ R)
    (hnet : ∀ x : ℝ, |x| ≤ R → ∃ i, |x - z i| ≤ η)
    (hf : ∀ t, |t| ≤ ρ → κ ≤ f.correlation t)
    (hg : ∀ t, |t| ≤ ρ → κ ≤ g.correlation t)
    (ω : ℝ → ℝ)
    (hωf : ∀ x y, |x - y| ≤ η → |f.correlation x - f.correlation y| ≤ ω η)
    (hωg : ∀ x y, |x - y| ≤ η → |g.correlation x - g.correlation y| ≤ ω η)
    (hsf : ∀ x, R < |x| → f.correlation x = 0)
    (hsg : ∀ x, R < |x| → g.correlation x = 0) (a : Bool × ι → ℝ) :
    ‖f.complexCorrelation - g.complexCorrelation‖ ≤
      ((1 + ((n : ℝ) + 1) / (2 * κ)) *
        (finiteNetDataResidual f z n a + finiteNetDataResidual g z n a)) / κ ^ (n + 1) +
        2 * ω η := by
  have hp : finiteNetPairError f g z n ≤
      finiteNetDataResidual f z n a + finiteNetDataResidual g z n a := by
    apply Finset.sup'_le
    intro i _
    exact finiteNet_discrepancy_le_residual_sum f g z n a (true, i)
  have hs : finiteNetSpokeError f g z n ≤
      finiteNetDataResidual f z n a + finiteNetDataResidual g z n a := by
    apply Finset.sup'_le
    intro i _
    exact finiteNet_discrepancy_le_residual_sum f g z n a (false, i)
  apply (finiteNet_global_recovery_norm f g z hη hκ n hn hz hnet hf hg ω hωf hωg hsf hsg).trans
  apply add_le_add _ le_rfl
  apply div_le_div_of_nonneg_right _ (pow_pos hκ (n + 1)).le
  calc
    _ ≤ (finiteNetDataResidual f z n a + finiteNetDataResidual g z n a) +
        ((n : ℝ) + 1) * (finiteNetDataResidual f z n a + finiteNetDataResidual g z n a) /
          (2 * κ) := add_le_add hs
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity))
        (mul_pos (by norm_num) hκ).le)
    _ = _ := by ring

end GaloisForLFunctions.BiScaleUncertainty.EnergyCycle
