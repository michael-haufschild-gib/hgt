import GaloisForLFunctions.RHTower.CompactGaussianWindowModeSynthesis
import GaloisForLFunctions.RHTower.CompactGaussianWindowFluctuation
import Mathlib.Data.Fintype.EquivFin

open MeasureTheory Filter Topology Finset Complex Metric
noncomputable section
namespace RHTower
open SteinhausModel

/-- The actual joint retained/free compact target event, with a closed error threshold. -/
def compactGaussianWindowTargetEvent (c : ℂ) (r : ℝ) (f : ℂ → ℂ) (ε : ℝ)
    (N Y L : ℕ) (tau : ℝ) : Set (Omega × Omega) :=
  {q | ∀ s ∈ closedBall c r,
    ‖(∑ p ∈ largePrimes N Y, charFactor 1 (q.2 p) *
      compactGaussianNormalizedPrimeChannel s N p tau (L / p) q.1) - f s‖ ≤ ε}

/-- Every literal normalized column is continuous in the retained phase. -/
theorem continuous_compactGaussianNormalizedPrimeChannel_phase
    (s : ℂ) (N p tau : ℝ) (L : ℕ) :
    Continuous (compactGaussianNormalizedPrimeChannel s N p tau L) := by
  have hco : Continuous (truncatedFullGaussianCofactor s (N / p) L) := by
    unfold truncatedFullGaussianCofactor
    exact continuous_finsetSum _ (fun n _ =>
      ((continuous_steinhausCharacter (n + 1)).mul_const _).mul_const _)
  unfold compactGaussianNormalizedPrimeChannel normalizedTruncatedGaussianCofactorChannel
  exact (((hco.mul_const _).const_mul _).const_mul _).div_const _

/-- Simultaneous control at every spectral point is a closed joint phase event;
there is no selection or uncountable measurable-intersection premise. -/
theorem isClosed_compactGaussianWindowTargetEvent
    (c : ℂ) (r : ℝ) (f : ℂ → ℂ) (ε : ℝ) (N Y L : ℕ) (tau : ℝ) :
    IsClosed (compactGaussianWindowTargetEvent c r f ε N Y L tau) := by
  simp only [compactGaussianWindowTargetEvent, Set.setOf_forall]
  apply isClosed_iInter
  intro s
  apply isClosed_iInter
  intro _hs
  apply isClosed_le _ continuous_const
  apply Continuous.norm
  apply Continuous.sub (g := fun _ => f s) _ continuous_const
  exact continuous_finsetSum _ (fun p _ =>
    ((continuous_charFactor 1).comp ((continuous_apply p).comp continuous_snd)).mul
      ((continuous_compactGaussianNormalizedPrimeChannel_phase s N p tau (L / p)).comp continuous_fst))

/-- The same canonical event is jointly measurable in retained and free phases. -/
theorem measurableSet_compactGaussianWindowTargetEvent
    (c : ℂ) (r : ℝ) (f : ℂ → ℂ) (ε : ℝ) (N Y L : ℕ) (tau : ℝ) :
    MeasurableSet (compactGaussianWindowTargetEvent c r f ε N Y L tau) :=
  (isClosed_compactGaussianWindowTargetEvent c r f ε N Y L tau).measurableSet

private theorem sum_enum_compactWindow {F : Type*} [AddCommMonoid F]
    (S : Finset ℕ) (f : ℕ → F) :
    (∑ i : Fin S.card, f (S.equivFin.symm i).val) = ∑ p ∈ S, f p :=
  (S.equivFin.symm.sum_comp (fun p : S => f p)).trans (Finset.sum_coe_sort S f)

/-- Every finite Gaussian target catalogue has a canonical compact free-window
section of arbitrarily small logarithmic probability cost, uniformly over a
prescribed-prefix retained cell, height and all later literal cutoffs. -/
theorem exists_compactGaussianWindow_mode_target_mass
    (S : Finset ℕ) (ω : Omega) (B0 : ℕ) {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 < κ)
    {c : ℂ} {r ρ : ℝ} (hρ : 0 < ρ) (hrρ : r < ρ)
    (hc0 : 0 < c.re - ρ) (hc1 : c.re + ρ < 1)
    {k : ℕ} (hk : 0 < k) (t : Fin k → ℝ) (γ : Fin k → ℂ) :
    ∃ ω' : Omega, (∀ p ∈ S, ω' p = ω p) ∧ ∃ B D : ℕ, ∃ δ : ℝ,
      B0 ≤ B ∧ 0 < δ ∧
      ∀ᶠ N : ℕ in atTop, ∀ tau : ℝ, ∀ η : Omega,
        (∀ n ∈ Icc 1 B, ‖X n η - X n ω'‖ < δ) → ∀ L : ℕ, N * D ≤ L →
        (1 / 4 : ℝ) * Real.exp (-(2 * κ * Real.log N)) ≤
          steinhausMeasure.real {ξ | (η, ξ) ∈ compactGaussianWindowTargetEvent c r
            (fun s => ∑ i, γ i * smoothAFEGaussianKernel (s + (t i : ℂ) * I))
            ε N (N / (2 * (B + 1))) L tau} := by
  classical
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨ω', hp, B, D, δ, hB, hδ, hsynthesis⟩ :=
    exists_compactGaussianWindow_mode_synthesis S ω B0 hhalf hκ hρ hrρ hc0 hc1 hk t γ
  refine ⟨ω', hp, B, D, δ, hB, hδ, ?_⟩
  have hwindow := eventually_compactGaussianWindow_original_fluctuation c hρ hrρ hc0.le
    hhalf (show 0 < 2 * (B + 1) by omega)
  filter_upwards [hsynthesis, hwindow] with N hsyn hfluctN
  intro tau η hcell L hL
  obtain ⟨μ, _, hμ, hcost, hmean⟩ := hsyn tau
  let W := largePrimes N (N / (2 * (B + 1)))
  let p : Fin W.card → ℕ := fun i => (W.equivFin.symm i).val
  have hinj : Function.Injective p := Subtype.val_injective.comp W.equivFin.symm.injective
  obtain ⟨E, _, hprob, hfluct⟩ := hfluctN tau L η p hinj
    (fun i => (W.equivFin.symm i).property) (fun i => μ (p i)) (fun i => hμ (p i))
  have hcostEnum : (∑ i, ‖μ (p i)‖ ^ 2) ≤ κ * Real.log N :=
    (sum_enum_compactWindow W (fun q => ‖μ q‖ ^ 2)).trans_le hcost
  have hprob' : (1 / 4 : ℝ) * Real.exp (-(2 * κ * Real.log N)) ≤ steinhausMeasure.real E := by
    refine (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)).trans hprob
    nlinarith
  refine hprob'.trans (measureReal_mono ?_)
  intro ξ hξ s hs
  have hfl : ‖∑ q ∈ W, (charFactor 1 (ξ q) - μ q) *
      compactGaussianNormalizedPrimeChannel s N q tau (L / q) η‖ < ε / 2 := by
    have h := hfluct ξ hξ s hs
    rw [show (∑ i, (charFactor 1 (ξ (p i)) - μ (p i)) *
        compactGaussianNormalizedPrimeChannel s N (p i) tau (L / p i) η) =
        ∑ q ∈ W, (charFactor 1 (ξ q) - μ q) *
          compactGaussianNormalizedPrimeChannel s N q tau (L / q) η from
      sum_enum_compactWindow W (fun q : ℕ => (charFactor 1 (ξ q) - μ q) *
        compactGaussianNormalizedPrimeChannel s N q tau (L / q) η)] at h
    exact h
  have hm := hmean η hcell L hL s hs
  change ‖(∑ q ∈ W, charFactor 1 (ξ q) *
      compactGaussianNormalizedPrimeChannel s N q tau (L / q) η) -
      ∑ i, γ i * smoothAFEGaussianKernel (s + (t i : ℂ) * I)‖ ≤ ε
  have heq : (∑ q ∈ W, charFactor 1 (ξ q) *
      compactGaussianNormalizedPrimeChannel s N q tau (L / q) η) -
      ∑ i, γ i * smoothAFEGaussianKernel (s + (t i : ℂ) * I) =
      (∑ q ∈ W, (charFactor 1 (ξ q) - μ q) *
        compactGaussianNormalizedPrimeChannel s N q tau (L / q) η) +
      ((∑ q ∈ W, μ q * compactGaussianNormalizedPrimeChannel s N q tau (L / q) η) -
        ∑ i, γ i * smoothAFEGaussianKernel (s + (t i : ℂ) * I)) := by
    simp only [sub_mul, sum_sub_distrib]
    ring
  rw [heq]
  exact (norm_add_le _ _).trans (by linarith)

end RHTower
