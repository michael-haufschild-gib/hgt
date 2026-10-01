import GaloisForLFunctions.RHTower.CompactGaussianWindowModeTarget
import GaloisForLFunctions.RHTower.SmoothAFECompactGaussianDensity

open MeasureTheory Filter Topology Finset Complex Metric
noncomputable section
namespace RHTower
open SteinhausModel

/-- Every larger-disc holomorphic target is reached by the literal normalized
free-window sum on the whole inner disc, at arbitrarily small logarithmic
original-law cost and within a cell preserving any prescribed finite prefix. -/
theorem exists_compactGaussianWindow_holomorphic_target_mass
    (S : Finset ℕ) (ω : Omega) (B0 : ℕ) {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 < κ)
    {c : ℂ} {r ρ : ℝ} (hr : 0 ≤ r) (hrρ : r < ρ)
    (hc0 : 0 < c.re - ρ) (hc1 : c.re + ρ < 1)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (closedBall c ρ)) :
    ∃ ω' : Omega, (∀ p ∈ S, ω' p = ω p) ∧ ∃ B D : ℕ, ∃ δ : ℝ,
      B0 ≤ B ∧ 0 < δ ∧
      ∀ᶠ N : ℕ in atTop, ∀ tau : ℝ, ∀ η : Omega,
        (∀ n ∈ Icc 1 B, ‖X n η - X n ω'‖ < δ) → ∀ L : ℕ, N * D ≤ L →
        (1 / 4 : ℝ) * Real.exp (-(2 * κ * Real.log N)) ≤
          steinhausMeasure.real {ξ | (η, ξ) ∈ compactGaussianWindowTargetEvent c r
            f ε N (N / (2 * (B + 1))) L tau} := by
  classical
  have hρ : 0 < ρ := lt_of_le_of_lt hr hrρ
  have hrc : r < c.re := by linarith
  let g : C(closedBall c r, ℂ) := ⟨fun z => f z,
    (hf.continuousOn.mono (closedBall_subset_closedBall hrρ.le)).restrict⟩
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨a, ha⟩ := exists_finite_compactGaussianModes_approximation c hr hrc hrρ hf g
    (fun _ => rfl) hhalf
  let U : Finset ℝ := insert 0 a.support
  let t : Fin U.card → ℝ := fun i => (U.equivFin.symm i).val
  let γ : Fin U.card → ℂ := fun i => a (t i)
  have hk : 0 < U.card := card_pos.mpr ⟨0, mem_insert_self _ _⟩
  have hkernel (u : ℝ) (z : closedBall c r) :
      compactGaussianCauchyKernel (closedBall c r) ((u : ℂ) * I) z =
        smoothAFEGaussianKernel ((z : ℂ) + (u : ℂ) * I) := by
    apply compactGaussianCauchyKernel_apply
    intro hx
    have hdist : dist (-((u : ℂ) * I)) c ≤ r := hx
    have hre : (-((u : ℂ) * I)).re = 0 := by simp
    have habs : |(-((u : ℂ) * I)).re - c.re| ≤ dist (-((u : ℂ) * I)) c := by
      simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (-((u : ℂ) * I) - c)
    rw [hre] at habs
    have hh := (abs_le.mp (habs.trans hdist)).1
    linarith
  have happ (s : ℂ) (hs : s ∈ closedBall c r) :
      ‖f s - ∑ i, γ i * smoothAFEGaussianKernel (s + (t i : ℂ) * I)‖ < ε / 2 := by
    have h := ((g - a.sum (fun u b => b •
      compactGaussianCauchyKernel (closedBall c r) ((u : ℂ) * I))).norm_coe_le_norm ⟨s, hs⟩).trans_lt ha
    have heval : (a.sum (fun u b => b •
        compactGaussianCauchyKernel (closedBall c r) ((u : ℂ) * I))) ⟨s, hs⟩ =
        ∑ u ∈ a.support, a u * smoothAFEGaussianKernel (s + (u : ℂ) * I) := by
      simp only [Finsupp.sum, ContinuousMap.sum_apply, ContinuousMap.smul_apply, hkernel, smul_eq_mul]
    rw [ContinuousMap.sub_apply, heval] at h
    have hext : (∑ u ∈ a.support, a u * smoothAFEGaussianKernel (s + (u : ℂ) * I)) =
        ∑ u ∈ U, a u * smoothAFEGaussianKernel (s + (u : ℂ) * I) :=
      sum_subset (subset_insert _ _) (fun u _ hu => by rw [Finsupp.notMem_support_iff.mp hu, zero_mul])
    have henum : (∑ i, γ i * smoothAFEGaussianKernel (s + (t i : ℂ) * I)) =
        ∑ u ∈ U, a u * smoothAFEGaussianKernel (s + (u : ℂ) * I) :=
      (U.equivFin.symm.sum_comp (fun u : U => a u * smoothAFEGaussianKernel (s + (u.val : ℂ) * I))).trans
        (Finset.sum_coe_sort U (fun u => a u * smoothAFEGaussianKernel (s + (u : ℂ) * I)))
    rw [hext, ← henum] at h
    exact h
  obtain ⟨ω', hp, B, D, δ, hB, hδ, hmass⟩ :=
    exists_compactGaussianWindow_mode_target_mass S ω B0 hhalf hκ hρ hrρ hc0 hc1 hk t γ
  refine ⟨ω', hp, B, D, δ, hB, hδ, ?_⟩
  filter_upwards [hmass] with N hmassN
  intro tau η hcell L hL
  refine (hmassN tau η hcell L hL).trans (measureReal_mono ?_)
  intro ξ hξ s hs
  have hmode := hξ s hs
  have htarget := happ s hs
  let v := ∑ p ∈ largePrimes N (N / (2 * (B + 1))), charFactor 1 (ξ p) *
    compactGaussianNormalizedPrimeChannel s N p tau (L / p) η
  let q := ∑ i, γ i * smoothAFEGaussianKernel (s + (t i : ℂ) * I)
  change ‖v - f s‖ ≤ ε
  have htri := norm_add_le (v - q) (q - f s)
  rw [sub_add_sub_cancel, norm_sub_rev q (f s)] at htri
  exact htri.trans (by dsimp only [v, q]; linarith)

end RHTower
