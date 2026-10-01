import GaloisForLFunctions.RHTower.ReflectedCompactCorrection
import GaloisForLFunctions.RHTower.HolomorphicDiscFiniteCatalogue

open Complex Filter Topology Set Metric
noncomputable section
namespace RHTower
open SteinhausModel

/-- The literal target after dividing out the common row and retaining every
term of the original correction. -/
def reflectedCompactReferenceTarget (f : ℂ → ℂ) (N tau : ℝ) (ω : Omega) (s : ℂ) : ℂ :=
  (reflectedCompactGaussianRow s N tau)⁻¹ *
    (f s - steinhausCompactReflectedCorrection (s + (tau : ℂ) * I) N ω)

private theorem closedBall_subset_openStrip {c : ℂ} {r : ℝ}
    (hc0 : 0 < c.re - r) (hc1 : c.re + r < 1) :
    closedBall c r ⊆ {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  intro s hs
  have hre0 : |s.re - c.re| ≤ dist s c := by
    simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s - c)
  have hre : |s.re - c.re| ≤ r := hre0.trans hs
  exact ⟨by linarith [(abs_le.mp hre).1], by linarith [(abs_le.mp hre).2]⟩

/-- Every reference target is holomorphic on the original outer disc. -/
theorem differentiableOn_reflectedCompactReferenceTarget
    {f : ℂ → ℂ} {c : ℂ} {r N : ℝ}
    (hf : DifferentiableOn ℂ f (closedBall c r))
    (hc0 : 0 < c.re - r) (hc1 : c.re + r < 1) (hN : 0 < N)
    (tau : ℝ) (ω : Omega) :
    DifferentiableOn ℂ (reflectedCompactReferenceTarget f N tau ω) (closedBall c r) := by
  have hsub := closedBall_subset_openStrip hc0 hc1
  have hrow := ((differentiableOn_reflectedCompactGaussianRow_and_inv hN tau).2).mono hsub
  have hmap : MapsTo (fun s : ℂ => s + (tau : ℂ) * I) (closedBall c r)
      {z : ℂ | 0 < z.re ∧ z.re < 1} := by
    intro s hs
    simpa using hsub hs
  have hcorr := (differentiableOn_steinhausCompactReflectedCorrection hN ω).comp
    (differentiable_id.add_const ((tau : ℂ) * I)).differentiableOn hmap
  exact hrow.mul (hf.sub hcorr)

/-- A fixed holomorphic target yields one bound for all reference phases and
all sufficiently large physical conductor windows. -/
theorem exists_norm_reflectedCompactReferenceTarget_le_disc
    {f : ℂ → ℂ} (c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hf : DifferentiableOn ℂ f (closedBall c r))
    (hc0 : 1 / 2 < c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ tau ∈ Icc (N : ℝ) (2 * N),
      ∀ s ∈ closedBall c r, ∀ ω : Omega,
        ‖reflectedCompactReferenceTarget f N tau ω s‖ ≤ C := by
  obtain ⟨A, hA⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨B, hB, hrow⟩ := exists_reflectedCompactGaussianRow_disc_bounds c hr hc0.le hc1
  obtain ⟨D, hD, hcorr⟩ := exists_norm_steinhausCompactReflectedCorrection_le_disc c hr hc0 hc1
  refine ⟨B * (|A| + D), mul_nonneg hB.le (add_nonneg (abs_nonneg A) hD), ?_⟩
  filter_upwards [hrow, hcorr] with N hrowN hcorrN
  intro tau htau s hs ω
  have hdiff : ‖f s - steinhausCompactReflectedCorrection (s + (tau : ℂ) * I) N ω‖ ≤ |A| + D :=
    (norm_sub_le _ _).trans (add_le_add ((hA s hs).trans (le_abs_self A)) (hcorrN tau htau s hs ω))
  unfold reflectedCompactReferenceTarget
  rw [norm_mul]
  exact mul_le_mul (hrowN tau htau s hs).2 hdiff (norm_nonneg _) hB.le

/-- One finite collection of actual holomorphic reference targets approximates
the complete moving family on any smaller disc. The catalogue precedes all
later phase-cell and free-window choices. -/
theorem exists_finite_reflectedCompactReferenceTarget_catalogue
    {f : ℂ → ℂ} (c : ℂ) {r ρ : ℝ} (hrho : 0 ≤ ρ) (hrρ : r < ρ)
    (hf : DifferentiableOn ℂ f (closedBall c ρ))
    (hc0 : 1 / 2 < c.re - ρ) (hc1 : c.re + ρ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : Finset (ℂ → ℂ),
      (∀ g ∈ G, DifferentiableOn ℂ g (closedBall c ρ)) ∧
      ∀ᶠ N : ℕ in atTop, ∀ tau ∈ Icc (N : ℝ) (2 * N), ∀ ω : Omega,
        ∃ g ∈ G, ∀ s ∈ closedBall c r,
          ‖reflectedCompactReferenceTarget f N tau ω s - g s‖ < ε := by
  classical
  obtain ⟨C, _, hbd⟩ := exists_norm_reflectedCompactReferenceTarget_le_disc c hrho hf hc0 hc1
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hbd
  let J := {q : ℕ × ℝ × Omega // max N₀ 1 ≤ q.1 ∧ q.2.1 ∈ Icc (q.1 : ℝ) (2 * q.1)}
  let F : J → ℂ → ℂ := fun q => reflectedCompactReferenceTarget f q.1.1 q.1.2.1 q.1.2.2
  have hF (q : J) : DifferentiableOn ℂ (F q) (closedBall c ρ) := by
    have hpos : (0 : ℝ) < q.1.1 := by
      exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one ((le_max_right N₀ 1).trans q.2.1)
    exact differentiableOn_reflectedCompactReferenceTarget hf (by linarith) hc1 hpos _ _
  have hFC (q : J) (s : ℂ) (hs : s ∈ ball c ρ) : ‖F q s‖ ≤ C :=
    hN₀ q.1.1 ((le_max_left N₀ 1).trans q.2.1) q.1.2.1 q.2.2 s
      (ball_subset_closedBall hs) q.1.2.2
  obtain ⟨T, hT⟩ := exists_finite_holomorphic_disc_catalogue F hrρ
    (fun q => (hF q).mono ball_subset_closedBall) hFC hε
  refine ⟨T.image F, ?_, ?_⟩
  · intro g hg
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hg
    exact hF q
  · filter_upwards [eventually_ge_atTop (max N₀ 1)] with N hN
    intro tau htau ω
    let q : J := ⟨(N, tau, ω), hN, htau⟩
    obtain ⟨j, hj, happ⟩ := hT q
    exact ⟨F j, Finset.mem_image.mpr ⟨j, hj, rfl⟩, happ⟩

end RHTower
