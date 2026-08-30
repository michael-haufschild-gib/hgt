import GaloisForLFunctions.HTGeometry.BoundedRandomEntireTail
import GaloisForLFunctions.HTGeometry.OneDimTranslationJetPacket

/-!
# The tail of the random entire series as a continuous family of sources

A clamped coefficient family with factorial decay gives a series that converges locally uniformly in
the pair `(sequence, point)`, so it depends continuously on the sequence.  Applying this to the
shifted coefficients makes the tail of the random series a continuous family of entire sources, and
its jet packets are therefore continuous — hence measurable — in the shifted coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 1000000 in
/-- A clamped series with factorial-decaying weights is jointly continuous. -/
theorem continuous_clampedSeries_uncurry (α : ℕ → ℂ)
    (hα : ∀ n, ‖α n‖ ≤ 1 / ((Nat.factorial n : ℕ) : ℝ)) :
    Continuous (fun q : (ℕ → ℂ) × ℂ => ∑' n : ℕ, clampComplexSquare (q.1 n) * α n * q.2 ^ n) := by
  rw [continuous_iff_continuousAt]
  intro q₀
  set R : ℝ := ‖q₀.2‖ + 1 with hR
  have hRpos : 0 < R := by positivity
  set s : Set ((ℕ → ℂ) × ℂ) := Set.univ ×ˢ Metric.ball (0 : ℂ) R with hs
  have hsopen : IsOpen s := isOpen_univ.prod Metric.isOpen_ball
  have hmem : q₀ ∈ s := ⟨Set.mem_univ _, by
    simp only [Metric.mem_ball, dist_zero_right, hR]
    linarith⟩
  have hbound : ∀ n : ℕ, ∀ q ∈ s,
      ‖clampComplexSquare (q.1 n) * α n * q.2 ^ n‖ ≤ 4 * (R ^ n / ((Nat.factorial n : ℕ) : ℝ)) := by
    intro n q hq
    have hqR : ‖q.2‖ ≤ R := le_of_lt (by simpa [Metric.mem_ball] using hq.2)
    have hfac : (0 : ℝ) < ((Nat.factorial n : ℕ) : ℝ) := by positivity
    rw [norm_mul, norm_mul, norm_pow]
    calc ‖clampComplexSquare (q.1 n)‖ * ‖α n‖ * ‖q.2‖ ^ n
        ≤ 4 * (1 / ((Nat.factorial n : ℕ) : ℝ)) * R ^ n := by
          refine mul_le_mul (mul_le_mul (norm_clampComplexSquare_le_four _) (hα n)
            (norm_nonneg _) (by norm_num)) (pow_le_pow_left₀ (norm_nonneg _) hqR n)
            (by positivity) (by positivity)
      _ = 4 * (R ^ n / ((Nat.factorial n : ℕ) : ℝ)) := by ring
  have hcont : ContinuousOn (fun q : (ℕ → ℂ) × ℂ =>
      ∑' n : ℕ, clampComplexSquare (q.1 n) * α n * q.2 ^ n) s := by
    refine continuousOn_tsum (fun n => ?_) ?_ hbound
    · have h1 : Continuous (fun q : (ℕ → ℂ) × ℂ => clampComplexSquare (q.1 n)) :=
        continuous_clampComplexSquare.comp ((continuous_apply n).comp continuous_fst)
      have h2 : Continuous (fun q : (ℕ → ℂ) × ℂ => q.2 ^ n) := continuous_snd.pow n
      exact ((h1.mul continuous_const).mul h2).continuousOn
    · exact (Real.summable_pow_div_factorial R).mul_left 4
  exact hcont.continuousAt (hsopen.mem_nhds hmem)

theorem continuous_boundedRandomEntireTail_uncurry (N : ℕ) :
    Continuous (fun q : (ℕ → ℂ) × ℂ => boundedRandomEntireTail N q.1 q.2) := by
  have hα : ∀ n : ℕ, ‖(1 : ℂ) / ((4 : ℂ) * ((Nat.factorial (n + N) : ℕ) : ℂ))‖
      ≤ 1 / ((Nat.factorial n : ℕ) : ℝ) := by
    intro n
    have hfac : (0 : ℝ) < ((Nat.factorial n : ℕ) : ℝ) := by positivity
    have hfacN : (0 : ℝ) < ((Nat.factorial (n + N) : ℕ) : ℝ) := by positivity
    have hle : ((Nat.factorial n : ℕ) : ℝ) ≤ ((Nat.factorial (n + N) : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_le (Nat.le_add_right n N)
    rw [norm_div, norm_one, norm_mul, Complex.norm_natCast, show ‖(4 : ℂ)‖ = 4 by norm_num]
    rw [div_le_div_iff₀ (by positivity) hfac]
    nlinarith
  have hval : (fun q : (ℕ → ℂ) × ℂ => boundedRandomEntireTail N q.1 q.2)
      = fun q : (ℕ → ℂ) × ℂ => q.2 ^ N *
        ∑' n : ℕ, clampComplexSquare (q.1 n)
          * ((1 : ℂ) / ((4 : ℂ) * ((Nat.factorial (n + N) : ℕ) : ℂ))) * q.2 ^ n := by
    funext q
    rw [boundedRandomEntireTail_eq, entireOfCoeffs]
    congr 1
    refine tsum_congr fun n => ?_
    rw [randomTailCoeff]
    ring
  rw [hval]
  exact (continuous_snd.pow N).mul (continuous_clampedSeries_uncurry _ hα)

/-- The tail of the random entire series as a one-coordinate source. -/
def randomEntireTailSource (N : ℕ) (y : ℕ → ℂ) : MultivariateEntire 1 :=
  oneDimMultivariateEntireOfDifferentiable (boundedRandomEntireTail N y)
    (differentiable_boundedRandomEntireTail N y)

set_option maxHeartbeats 1000000 in
theorem continuous_randomEntireTailSource (N : ℕ) :
    Continuous (fun y : ℕ → ℂ => randomEntireTailSource N y) := by
  set cm : (ℕ → ℂ) → C(Fin 1 → ℂ, ℂ) := fun y => (randomEntireTailSource N y).1 with hcm
  have huncurry : Continuous (Function.uncurry fun y z => (cm y) z) := by
    have h : (Function.uncurry fun (y : ℕ → ℂ) (z : Fin 1 → ℂ) => (cm y) z)
        = fun q : (ℕ → ℂ) × (Fin 1 → ℂ) => boundedRandomEntireTail N q.1 (q.2 0) := by
      funext q
      rfl
    rw [h]
    exact (continuous_boundedRandomEntireTail_uncurry N).comp
      (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd))
  exact continuous_induced_rng.2 (ContinuousMap.continuous_of_continuous_uncurry cm huncurry)

end

end GaloisForLFunctions.HTGeometry
