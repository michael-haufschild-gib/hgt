import GaloisForLFunctions.BiScaleUncertainty.ClosedCycleScalarRecovery
import GaloisForLFunctions.BiScaleUncertainty.NyquistCriticalSourceQuantitative

/-!
# Finite closed-cycle recovery on controlled actual sources

Separate maxima retain the noise in pair and spoke observations. The exact
positive-collar conditioning extends across a finite mesh by the prescribed
modulus, and support control extends the bound to every real lag.
-/

noncomputable section
open MeasureTheory Set
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.BiScaleUncertainty.EnergyCycle
set_option autoImplicit false
variable {E : ℝ}

/-- The largest literal pair discrepancy on the specified mesh. -/
def pairMeshError (f g : LevyEnergySource E) (R η : ℝ) (n : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : Fin (meshLength R η) =>
    let y := meshPoint R η i / ((n : ℝ) + 1)
    |value f [y, -y] - value g [y, -y]|)

/-- The largest literal spoke discrepancy on the specified mesh. -/
def spokeMeshError (f g : LevyEnergySource E) (R η : ℝ) (n : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : Fin (meshLength R η) =>
    |value f (spoke n (meshPoint R η i)) - value g (spoke n (meshPoint R η i))|)

theorem pair_discrepancy_le_meshError (f g : LevyEnergySource E) (R η : ℝ) (n : ℕ)
    (i : Fin (meshLength R η)) :
    let y := meshPoint R η i / ((n : ℝ) + 1)
    |value f [y, -y] - value g [y, -y]| ≤ pairMeshError f g R η n := by
  dsimp only
  unfold pairMeshError
  exact Finset.le_sup' (fun j : Fin (meshLength R η) =>
    let y := meshPoint R η j / ((n : ℝ) + 1)
    |value f [y, -y] - value g [y, -y]|) (Finset.mem_univ i)

theorem spoke_discrepancy_le_meshError (f g : LevyEnergySource E) (R η : ℝ) (n : ℕ)
    (i : Fin (meshLength R η)) :
    |value f (spoke n (meshPoint R η i)) - value g (spoke n (meshPoint R η i))| ≤
      spokeMeshError f g R η n := by
  unfold spokeMeshError
  exact Finset.le_sup' (fun j : Fin (meshLength R η) =>
    |value f (spoke n (meshPoint R η j)) - value g (spoke n (meshPoint R η j))|)
    (Finset.mem_univ i)

theorem pairMeshError_nonneg (f g : LevyEnergySource E) (R η : ℝ) (n : ℕ) :
    0 ≤ pairMeshError f g R η n :=
  (abs_nonneg _).trans (pair_discrepancy_le_meshError f g R η n 0)

theorem spokeMeshError_nonneg (f g : LevyEnergySource E) (R η : ℝ) (n : ℕ) :
    0 ≤ spokeMeshError f g R η n :=
  (abs_nonneg _).trans (spoke_discrepancy_le_meshError f g R η n 0)

/-- Every mesh node has the exact separate-noise collar recovery bound. -/
theorem controlled_mesh_recovery (f g : LevyEnergySource E) {R η ρ κ : ℝ}
    (hR : 0 ≤ R) (hη : 0 < η) (hκ : 0 < κ) (n : ℕ)
    (hn : R ≤ ((n : ℝ) + 1) * ρ)
    (hf : ∀ t, |t| ≤ ρ → κ ≤ f.correlation t)
    (hg : ∀ t, |t| ≤ ρ → κ ≤ g.correlation t)
    (i : Fin (meshLength R η)) :
    |f.correlation (meshPoint R η i) - g.correlation (meshPoint R η i)| ≤
      (spokeMeshError f g R η n + ((n : ℝ) + 1) * pairMeshError f g R η n / (2 * κ)) /
        κ ^ (n + 1) := by
  have hp : 0 < (n : ℝ) + 1 := by positivity
  have hy : |meshPoint R η i / ((n : ℝ) + 1)| ≤ ρ := by
    rw [abs_div, abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    simpa only [mul_comm] using (meshPoint_mem hR hη i).trans hn
  apply (correlation_recovery_of_collar f g n _ hκ (hf _ hy) (hg _ hy)).trans
  apply div_le_div_of_nonneg_right _ (pow_pos hκ (n + 1)).le
  exact add_le_add (spoke_discrepancy_le_meshError f g R η n i)
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pair_discrepancy_le_meshError f g R η n i) hp.le)
      (mul_pos (by norm_num) hκ).le)

/-- A mesh-value bound extends to the entire window at a cost of two prescribed modulus errors. -/
theorem window_error_le_of_mesh_error (f g : LevyEnergySource E) {R η A ω : ℝ}
    (hη : 0 < η)
    (hmesh : ∀ i : Fin (meshLength R η),
      |f.correlation (meshPoint R η i) - g.correlation (meshPoint R η i)| ≤ A)
    (hωf : ∀ x y, |x - y| ≤ η → |f.correlation x - f.correlation y| ≤ ω)
    (hωg : ∀ x y, |x - y| ≤ η → |g.correlation x - g.correlation y| ≤ ω)
    {x : ℝ} (hx : |x| ≤ R) : |f.correlation x - g.correlation x| ≤ A + 2 * ω := by
  obtain ⟨i, hi⟩ := mesh_covers hη hx
  have hm := hmesh i
  have hfi := hωf x (meshPoint R η i) hi.le
  have hgi := hωg x (meshPoint R η i) hi.le
  have ht : |f.correlation x - g.correlation x| ≤
      |f.correlation x - f.correlation (meshPoint R η i)| +
      |f.correlation (meshPoint R η i) - g.correlation (meshPoint R η i)| +
      |g.correlation x - g.correlation (meshPoint R η i)| := by
    calc
      _ = |(f.correlation x - f.correlation (meshPoint R η i)) +
          (f.correlation (meshPoint R η i) - g.correlation (meshPoint R η i)) -
          (g.correlation x - g.correlation (meshPoint R η i))| := by congr 1; ring
      _ ≤ _ := (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  linarith only [ht, hm, hfi, hgi]

/-- Mesh interpolation incurs exactly two modulus errors, including interval endpoints. -/
theorem controlled_window_recovery (f g : LevyEnergySource E) {R η ρ κ : ℝ}
    (hR : 0 ≤ R) (hη : 0 < η) (hκ : 0 < κ) (n : ℕ)
    (hn : R ≤ ((n : ℝ) + 1) * ρ)
    (hf : ∀ t, |t| ≤ ρ → κ ≤ f.correlation t)
    (hg : ∀ t, |t| ≤ ρ → κ ≤ g.correlation t)
    (ω : ℝ → ℝ)
    (hωf : ∀ x y, |x - y| ≤ η → |f.correlation x - f.correlation y| ≤ ω η)
    (hωg : ∀ x y, |x - y| ≤ η → |g.correlation x - g.correlation y| ≤ ω η)
    {x : ℝ} (hx : |x| ≤ R) :
    |f.correlation x - g.correlation x| ≤
      (spokeMeshError f g R η n + ((n : ℝ) + 1) * pairMeshError f g R η n / (2 * κ)) /
        κ ^ (n + 1) + 2 * ω η :=
  window_error_le_of_mesh_error f g hη
    (controlled_mesh_recovery f g hR hη hκ n hn hf hg) hωf hωg hx

/-- Compact correlation support extends the exact finite-mesh bound to all real lags. -/
theorem controlled_global_recovery (f g : LevyEnergySource E) {R η ρ κ : ℝ}
    (hR : 0 ≤ R) (hη : 0 < η) (hκ : 0 < κ) (n : ℕ)
    (hn : R ≤ ((n : ℝ) + 1) * ρ)
    (hf : ∀ t, |t| ≤ ρ → κ ≤ f.correlation t)
    (hg : ∀ t, |t| ≤ ρ → κ ≤ g.correlation t)
    (ω : ℝ → ℝ)
    (hωf : ∀ x y, |x - y| ≤ η → |f.correlation x - f.correlation y| ≤ ω η)
    (hωg : ∀ x y, |x - y| ≤ η → |g.correlation x - g.correlation y| ≤ ω η)
    (hsf : ∀ x, R < |x| → f.correlation x = 0)
    (hsg : ∀ x, R < |x| → g.correlation x = 0) (x : ℝ) :
    |f.correlation x - g.correlation x| ≤
      (spokeMeshError f g R η n + ((n : ℝ) + 1) * pairMeshError f g R η n / (2 * κ)) /
        κ ^ (n + 1) + 2 * ω η := by
  by_cases hx : |x| ≤ R
  · exact controlled_window_recovery f g hR hη hκ n hn hf hg ω hωf hωg hx
  · rw [hsf x (lt_of_not_ge hx), hsg x (lt_of_not_ge hx), sub_self, abs_zero]
    have hω : 0 ≤ ω η := by
      simpa only [sub_self, abs_zero] using hωf 0 0 (by simpa using hη.le)
    exact add_nonneg (div_nonneg
      (add_nonneg (spokeMeshError_nonneg f g R η n)
        (div_nonneg (mul_nonneg (by positivity) (pairMeshError_nonneg f g R η n))
          (mul_pos (by norm_num) hκ).le)) (pow_pos hκ (n + 1)).le)
      (mul_nonneg (by norm_num) hω)

/-- The pointwise reconstruction bound is exactly a global uniform norm bound. -/
theorem controlled_global_recovery_norm (f g : LevyEnergySource E) {R η ρ κ : ℝ}
    (hR : 0 ≤ R) (hη : 0 < η) (hκ : 0 < κ) (n : ℕ)
    (hn : R ≤ ((n : ℝ) + 1) * ρ)
    (hf : ∀ t, |t| ≤ ρ → κ ≤ f.correlation t)
    (hg : ∀ t, |t| ≤ ρ → κ ≤ g.correlation t)
    (ω : ℝ → ℝ)
    (hωf : ∀ x y, |x - y| ≤ η → |f.correlation x - f.correlation y| ≤ ω η)
    (hωg : ∀ x y, |x - y| ≤ η → |g.correlation x - g.correlation y| ≤ ω η)
    (hsf : ∀ x, R < |x| → f.correlation x = 0)
    (hsg : ∀ x, R < |x| → g.correlation x = 0) :
    ‖f.complexCorrelation - g.complexCorrelation‖ ≤
      (spokeMeshError f g R η n + ((n : ℝ) + 1) * pairMeshError f g R η n / (2 * κ)) /
        κ ^ (n + 1) + 2 * ω η := by
  apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
  intro x
  change ‖(f.correlation x : ℂ) - (g.correlation x : ℂ)‖ ≤ _
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact controlled_global_recovery f g hR hη hκ n hn hf hg ω hωf hωg hsf hsg x

/-- Every two nonzero compact smooth sources inhabit a common actual energy class. -/
theorem exists_common_levyEnergySource (f g : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hg : ContDiff ℝ 2 (g : ℝ → ℝ))
    (hfn : f ≠ 0) (hgn : g ≠ 0) :
    ∃ E : ℝ, ∃ F G : LevyEnergySource E,
      F.source = f ∧ G.source = g ∧
      F.correlation = nyquistNormalizedCorrelation f ∧
      G.correlation = nyquistNormalizedCorrelation g := by
  let E := max (normalizedArchEnergy f) (normalizedArchEnergy g)
  let F : LevyEnergySource E := ⟨f, hf, nyquistSourceMass_pos f hfn, le_max_left _ _⟩
  let G : LevyEnergySource E := ⟨g, hg, nyquistSourceMass_pos g hgn, le_max_right _ _⟩
  exact ⟨E, F, G, rfl, rfl, rfl, rfl⟩

end GaloisForLFunctions.BiScaleUncertainty.EnergyCycle
