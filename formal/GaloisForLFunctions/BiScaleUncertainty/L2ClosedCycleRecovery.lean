import GaloisForLFunctions.BiScaleUncertainty.FiniteNetClosedCycleRecovery
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalL2Energy

/-!
# Finite closed-cycle recovery for real L² sources

Translation matrix coefficients supply continuity, evenness and the unit
bound for actual normalized L² autocorrelations. Positive collars and a
continuity modulus then give the exact finite-net recovery estimate,
without a compact-source, smoothness or finite-energy condition.
-/

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BoundedContinuousFunction
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.BiScaleUncertainty.L2Cycle
open SobolevShear EnergyCycle
set_option autoImplicit false

/-- The normalized integral autocorrelation of the actual real L² source. -/
def correlation (f : Velocity) (x : ℝ) : ℝ := autocorr f x / autocorr f 0

/-- Origin mass is the actual squared Hilbert norm. -/
theorem mass_eq_norm_sq (f : Velocity) : autocorr f 0 = ‖f‖ ^ 2 := by
  rw [RHTower.autocorr_eq_inner_physicalTranslation, physicalTranslation_zero,
    real_inner_self_eq_norm_sq]

/-- Every nonzero L² source has normalized origin value one. -/
theorem correlation_zero (f : Velocity) (hf : f ≠ 0) : correlation f 0 = 1 := by
  unfold correlation
  apply div_self
  rw [mass_eq_norm_sq]
  exact (sq_pos_of_pos (norm_pos_iff.mpr hf)).ne'

theorem correlation_neg (f : Velocity) (x : ℝ) : correlation f (-x) = correlation f x := by
  unfold correlation
  rw [autocorr_neg]

/-- Cauchy--Schwarz and the translation isometry prove the unit envelope. -/
theorem abs_correlation_le_one (f : Velocity) (x : ℝ) : |correlation f x| ≤ 1 := by
  by_cases hm : autocorr f 0 = 0
  · simp only [correlation, hm, div_zero, abs_zero, zero_le_one]
  · have hp : 0 < autocorr f 0 := by
      rw [mass_eq_norm_sq] at hm ⊢
      exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm hm)
    rw [correlation, abs_div, abs_of_pos hp]
    apply (div_le_one hp).mpr
    rw [RHTower.autocorr_eq_inner_physicalTranslation, mass_eq_norm_sq]
    simpa only [Real.norm_eq_abs, physicalTranslation_norm, pow_two] using
      norm_inner_le_norm (𝕜 := ℝ) f (physicalTranslation x f)

/-- Strong continuity of the actual translation orbit gives continuous normalized correlation. -/
theorem continuous_correlation (f : Velocity) : Continuous (correlation f) := by
  have h := Continuous.inner (𝕜 := ℝ)
    (continuous_const : Continuous (fun _ : ℝ => f)) (continuous_physicalTranslation f)
  have hc : Continuous (autocorr f) :=
    h.congr (fun x => (RHTower.autocorr_eq_inner_physicalTranslation f x).symm)
  exact hc.div_const _

/-- The normalized source correlation as an actual bounded continuous function. -/
def complexCorrelation (f : Velocity) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => (correlation f x : ℂ))
    (Complex.continuous_ofReal.comp (continuous_correlation f))
    1 (fun x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_correlation_le_one f x)

/-- Passing from a square-integrable representative to its Hilbert class preserves every sample. -/
theorem correlation_toLp {f : ℝ → ℝ} (hf : MemLp f 2 volume) (x : ℝ) :
    correlation (hf.toLp f) x = autocorr f x / autocorr f 0 := by
  unfold correlation
  rw [RHTower.autocorr_congr_ae hf.coeFn_toLp x, RHTower.autocorr_congr_ae hf.coeFn_toLp 0]

/-- Literal products of normalized source correlations, restricted to closed cycles. -/
def value (f : Velocity) (l : List ℝ) : ℝ :=
  if l.sum = 0 then (l.map (correlation f)).prod else 0

theorem value_pair (f : Velocity) (x : ℝ) : value f [x, -x] = correlation f x ^ 2 := by
  simp [value, correlation_neg, pow_two]

theorem value_spoke (f : Velocity) (n : ℕ) (x : ℝ) :
    value f (spoke n x) = correlation f x * correlation f (x / ((n : ℝ) + 1)) ^ (n + 1) := by
  rw [value, if_pos (spoke_sum n x)]
  simp [spoke, correlation_neg]

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The maximum actual pair discrepancy over the finite net. -/
def pairError (f g : Velocity) (z : ι → ℝ) (n : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : ι =>
    |value f (finiteNetCycle z n (true, i)) - value g (finiteNetCycle z n (true, i))|)

/-- The maximum actual spoke discrepancy over the same finite net. -/
def spokeError (f g : Velocity) (z : ι → ℝ) (n : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : ι =>
    |value f (finiteNetCycle z n (false, i)) - value g (finiteNetCycle z n (false, i))|)

/-- Exact collar conditioning at each sample follows from source-derived unit bounds. -/
theorem sample_recovery (f g : Velocity) (z : ι → ℝ) {R ρ κ : ℝ}
    (hκ : 0 < κ) (n : ℕ) (hn : R ≤ ((n : ℝ) + 1) * ρ)
    (hz : ∀ i, |z i| ≤ R)
    (hf : ∀ t, |t| ≤ ρ → κ ≤ correlation f t)
    (hg : ∀ t, |t| ≤ ρ → κ ≤ correlation g t) (i : ι) :
    |correlation f (z i) - correlation g (z i)| ≤
      (spokeError f g z n + ((n : ℝ) + 1) * pairError f g z n / (2 * κ)) / κ ^ (n + 1) := by
  have hp : 0 < (n : ℝ) + 1 := by positivity
  have hy : |z i / ((n : ℝ) + 1)| ≤ ρ := by
    rw [abs_div, abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    simpa only [mul_comm] using (hz i).trans hn
  have hb := scalar_cycle_recovery (a := correlation f (z i)) hκ (hf _ hy) (hg _ hy)
    (abs_correlation_le_one f _) (abs_correlation_le_one g _) (abs_correlation_le_one g (z i)) (n + 1)
  have hpair := Finset.le_sup' (s := Finset.univ) (fun j : ι =>
    |value f (finiteNetCycle z n (true, j)) - value g (finiteNetCycle z n (true, j))|)
    (Finset.mem_univ i)
  have hspoke := Finset.le_sup' (s := Finset.univ) (fun j : ι =>
    |value f (finiteNetCycle z n (false, j)) - value g (finiteNetCycle z n (false, j))|)
    (Finset.mem_univ i)
  change |value f [z i / ((n : ℝ) + 1), -(z i / ((n : ℝ) + 1))] -
    value g [z i / ((n : ℝ) + 1), -(z i / ((n : ℝ) + 1))]| ≤ pairError f g z n at hpair
  change |value f (spoke n (z i)) - value g (spoke n (z i))| ≤ spokeError f g z n at hspoke
  rw [value_pair, value_pair] at hpair
  rw [value_spoke, value_spoke] at hspoke
  simp only [Nat.cast_add, Nat.cast_one] at hb
  apply hb.trans
  apply div_le_div_of_nonneg_right _ (pow_pos hκ (n + 1)).le
  exact add_le_add hspoke (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpair hp.le) (mul_pos (by norm_num) hκ).le)

/-- The full L² controlled class satisfies the exact arbitrary-net uniform recovery estimate. -/
theorem global_recovery_norm (f g : Velocity) (z : ι → ℝ)
    {R η ρ κ : ℝ} (hη : 0 ≤ η) (hκ : 0 < κ)
    (n : ℕ) (hn : R ≤ ((n : ℝ) + 1) * ρ)
    (hz : ∀ i, |z i| ≤ R)
    (hnet : ∀ x : ℝ, |x| ≤ R → ∃ i, |x - z i| ≤ η)
    (hf : ∀ t, |t| ≤ ρ → κ ≤ correlation f t)
    (hg : ∀ t, |t| ≤ ρ → κ ≤ correlation g t)
    (ω : ℝ → ℝ) (hω : MonotoneOn ω (Set.Ici 0))
    (hωf : ∀ x y, |correlation f x - correlation f y| ≤ ω |x - y|)
    (hωg : ∀ x y, |correlation g x - correlation g y| ≤ ω |x - y|)
    (hsf : ∀ x, R < |x| → correlation f x = 0)
    (hsg : ∀ x, R < |x| → correlation g x = 0) :
    ‖complexCorrelation f - complexCorrelation g‖ ≤
      (spokeError f g z n + ((n : ℝ) + 1) * pairError f g z n / (2 * κ)) / κ ^ (n + 1) +
        2 * ω η := by
  have hm := sample_recovery f g z hκ n hn hz hf hg
  apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
  intro x
  change ‖(correlation f x : ℂ) - (correlation g x : ℂ)‖ ≤ _
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  by_cases hx : |x| ≤ R
  · obtain ⟨i, hi⟩ := hnet x hx
    have hfi := (hωf x (z i)).trans (hω (abs_nonneg (x - z i)) hη hi)
    have hgi := (hωg x (z i)).trans (hω (abs_nonneg (x - z i)) hη hi)
    have hsample := hm i
    have ht : |correlation f x - correlation g x| ≤
        |correlation f x - correlation f (z i)| + |correlation f (z i) - correlation g (z i)| +
          |correlation g x - correlation g (z i)| := by
      calc
        _ = |(correlation f x - correlation f (z i)) +
            (correlation f (z i) - correlation g (z i)) -
            (correlation g x - correlation g (z i))| := by congr 1; ring
        _ ≤ _ := (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    linarith only [ht, hsample, hfi, hgi]
  · rw [hsf x (lt_of_not_ge hx), hsg x (lt_of_not_ge hx), sub_self, abs_zero]
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hω0 : 0 ≤ ω 0 := by simpa only [sub_self, abs_zero] using hωf 0 0
    exact add_nonneg ((abs_nonneg _).trans (hm i))
      (mul_nonneg (by norm_num) (hω0.trans (hω (by simp) hη hη)))

/-- Actual fitting residual against any array of real observations. -/
def dataResidual (f : Velocity) (z : ι → ℝ) (n : ℕ) (a : Bool × ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => |value f (finiteNetCycle z n i) - a i|)

theorem discrepancy_le_residual_sum (f g : Velocity) (z : ι → ℝ) (n : ℕ)
    (a : Bool × ι → ℝ) (i : Bool × ι) :
    |value f (finiteNetCycle z n i) - value g (finiteNetCycle z n i)| ≤
      dataResidual f z n a + dataResidual g z n a := by
  calc
    _ = |(value f (finiteNetCycle z n i) - a i) -
        (value g (finiteNetCycle z n i) - a i)| := by congr 1; ring
    _ ≤ _ := (abs_sub _ _).trans (add_le_add
      (Finset.le_sup' (fun j : Bool × ι => |value f (finiteNetCycle z n j) - a j|) (Finset.mem_univ i))
      (Finset.le_sup' (fun j : Bool × ι => |value g (finiteNetCycle z n j) - a j|) (Finset.mem_univ i)))

/-- The same arbitrary-data estimate holds on the complete L² source domain. -/
theorem recovery_from_measured_array (f g : Velocity) (z : ι → ℝ)
    {R η ρ κ : ℝ} (hη : 0 ≤ η) (hκ : 0 < κ)
    (n : ℕ) (hn : R ≤ ((n : ℝ) + 1) * ρ)
    (hz : ∀ i, |z i| ≤ R)
    (hnet : ∀ x : ℝ, |x| ≤ R → ∃ i, |x - z i| ≤ η)
    (hf : ∀ t, |t| ≤ ρ → κ ≤ correlation f t)
    (hg : ∀ t, |t| ≤ ρ → κ ≤ correlation g t)
    (ω : ℝ → ℝ) (hω : MonotoneOn ω (Set.Ici 0))
    (hωf : ∀ x y, |correlation f x - correlation f y| ≤ ω |x - y|)
    (hωg : ∀ x y, |correlation g x - correlation g y| ≤ ω |x - y|)
    (hsf : ∀ x, R < |x| → correlation f x = 0)
    (hsg : ∀ x, R < |x| → correlation g x = 0) (a : Bool × ι → ℝ) :
    ‖complexCorrelation f - complexCorrelation g‖ ≤
      (1 + ((n : ℝ) + 1) / (2 * κ)) * (dataResidual f z n a + dataResidual g z n a) /
        κ ^ (n + 1) + 2 * ω η := by
  have hp : pairError f g z n ≤ dataResidual f z n a + dataResidual g z n a := by
    apply Finset.sup'_le
    intro i _
    exact discrepancy_le_residual_sum f g z n a (true, i)
  have hs : spokeError f g z n ≤ dataResidual f z n a + dataResidual g z n a := by
    apply Finset.sup'_le
    intro i _
    exact discrepancy_le_residual_sum f g z n a (false, i)
  apply (global_recovery_norm f g z hη hκ n hn hz hnet hf hg ω hω hωf hωg hsf hsg).trans
  apply add_le_add _ le_rfl
  apply div_le_div_of_nonneg_right _ (pow_pos hκ (n + 1)).le
  calc
    _ ≤ (dataResidual f z n a + dataResidual g z n a) +
        ((n : ℝ) + 1) * (dataResidual f z n a + dataResidual g z n a) / (2 * κ) :=
      add_le_add hs (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (by positivity)) (mul_pos (by norm_num) hκ).le)
    _ = _ := by ring

end GaloisForLFunctions.BiScaleUncertainty.L2Cycle
