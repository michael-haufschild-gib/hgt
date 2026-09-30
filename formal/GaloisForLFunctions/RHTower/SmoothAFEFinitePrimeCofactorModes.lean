import GaloisForLFunctions.RHTower.SteinhausFinitePrimeCofactorModes
import GaloisForLFunctions.RHTower.SmoothAFECutoffBounds

/-!
# Gaussian smoothing of prescribed finite-prime cofactor modes

The literal Gaussian cutoff tends to one as its positive scale tends to zero. Each finite
cofactor prefix therefore converges to its hard-cutoff vector. A single one-sided neighborhood
of zero works for every prefix in a finite family of separated blocks, preserving all prescribed
Cauchy modes and their arbitrary mean-weighted length budgets.

The smoothing scale may depend on the constructed blocks. No uniform moving-height estimate,
literal prime-channel Gram bound, target law, or recurrence theorem is asserted here.
-/

noncomputable section
open Filter Topology Finset
namespace RHTower

/-- The normalized finite cofactor vector with the literal Gaussian AFE cutoff. -/
def smoothCofactorNodeVector {J : ℕ} (s : Fin J → ℂ) (r : ℝ) (N : ℕ)
    (omega : SteinhausModel.Omega) : Fin J → ℂ := fun j =>
  (∑ n ∈ Icc 1 N, smoothAFECutoff (r * ((n : ℝ) / N)) *
    SteinhausModel.X n omega * (n : ℂ) ^ (s j - 1)) * (N : ℂ) ^ (-s j)

/-- Remove the common coherent phase and prefix mean from a smoothed cofactor vector. -/
def relativeSmoothCofactorMode {J : ℕ} (s : Fin J → ℂ) (t : ℝ) (A : ℂ)
    (r : ℝ) (N : ℕ) (omega : SteinhausModel.Omega) : Fin J → ℂ :=
  A⁻¹ • ((N : ℂ) ^ (-((t : ℂ) * Complex.I)) • smoothCofactorNodeVector s r N omega)

private theorem tendsto_cutoff_scaled_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun r : ℝ => smoothAFECutoff (r * c)) (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨K, _, hK⟩ := exists_norm_smoothAFECutoff_sub_one_le_rpow (δ := 1) one_pos
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hzero : Tendsto (fun r : ℝ => smoothAFECutoff (r * c) - 1) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun r => K * (r * c))
    · filter_upwards [show ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r from self_mem_nhdsWithin] with r hr
      simpa only [Real.rpow_one] using hK (mul_pos hr hc)
    · simpa using (hr.mul_const c).const_mul K
  simpa using hzero.add_const 1

/-- Each literal finite cofactor prefix is the small-smoothing-parameter limit of
its Gaussian-cutoff version. -/
theorem tendsto_smoothCofactorNodeVector_zero
    {J : ℕ} (s : Fin J → ℂ) (N : ℕ) (omega : SteinhausModel.Omega) :
    Tendsto (fun r => smoothCofactorNodeVector s r N omega) (𝓝[>] 0)
      (𝓝 (cofactorNodeVector s N omega)) := by
  apply tendsto_pi_nhds.mpr
  intro j
  by_cases hN : N = 0
  · subst N
    simp [smoothCofactorNodeVector, cofactorNodeVector]
  · have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hN)
    have hsum := tendsto_finsetSum (Icc 1 N) (fun n hn =>
      ((tendsto_cutoff_scaled_zero (c := (n : ℝ) / N) (div_pos
        (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1)) hNpos)).mul_const
        (SteinhausModel.X n omega)).mul_const ((n : ℂ) ^ (s j - 1)))
    simpa only [smoothCofactorNodeVector, cofactorNodeVector, one_mul] using
      hsum.mul_const ((N : ℂ) ^ (-s j))

/-- Prescribed coherent modes survive every sufficiently small positive Gaussian smoothing
scale, uniformly across all integer prefixes in the separated cofactor blocks. -/
theorem exists_prescribed_smooth_cofactor_mode_blocks
    {J : ℕ} (s : Fin J → ℂ) (hs : ∀ j, 0 < (s j).re)
    (hs1 : ∀ j, (s j).re < 1) (S : Finset ℕ)
    (omega : SteinhausModel.Omega) (B : ℕ) (K ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (t : Fin k → ℝ) :
    ∃ omega' : SteinhausModel.Omega, (∀ p ∈ S, omega' p = omega p) ∧
      ∃ M : Fin k → ℕ, ∃ A : Fin k → ℂ, ∃ r₀ : ℝ, 0 < r₀ ∧
        (∀ i j, i < j → 2 * M i < M j) ∧
        ∀ i, B ≤ M i ∧ A i ≠ 0 ∧ K ≤ (M i : ℝ) * ‖A i‖ ^ 2 ∧
          ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ L : ℕ, M i ≤ L → L ≤ 2 * M i →
            ‖relativeSmoothCofactorMode s (t i) (A i) r L omega' - cofactorCauchyMode s (t i)‖ < ε := by
  classical
  obtain ⟨omega', hp, M, A, hsep, hblocks⟩ :=
    exists_prescribed_cofactor_mode_blocks s hs hs1 S omega B K (ε / 2) (by positivity) k t
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ i : Fin k, ∀ L : Fin (2 * M i + 1),
      ‖relativeSmoothCofactorMode s (t i) (A i) r L omega' -
        relativeCofactorMode s (t i) (A i) L omega'‖ < ε / 2 := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro L
    have hlim := (tendsto_const_nhds (x := (A i)⁻¹)).smul
      ((tendsto_const_nhds (x := (L.val : ℂ) ^ (-((t i : ℂ) * Complex.I)))).smul
        (tendsto_smoothCofactorNodeVector_zero s L omega'))
    change Tendsto (fun r => relativeSmoothCofactorMode s (t i) (A i) r L omega')
      (𝓝[>] 0) (𝓝 (relativeCofactorMode s (t i) (A i) L omega')) at hlim
    have h := hlim.eventually (Metric.ball_mem_nhds _ (show 0 < ε / 2 by positivity))
    simpa only [dist_eq_norm] using h
  obtain ⟨r₀, hr₀, hrsmall⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hsmall
  refine ⟨omega', hp, M, A, r₀, hr₀, hsep, ?_⟩
  intro i
  refine ⟨(hblocks i).1, (hblocks i).2.1, (hblocks i).2.2.1, ?_⟩
  intro r hr hrle L hlo hhi
  have h1 := hrsmall ⟨hr, hrle⟩ i ⟨L, by omega⟩
  have h2 := (hblocks i).2.2.2 L hlo hhi
  calc
    _ ≤ ‖relativeSmoothCofactorMode s (t i) (A i) r L omega' -
        relativeCofactorMode s (t i) (A i) L omega'‖ +
        ‖relativeCofactorMode s (t i) (A i) L omega' - cofactorCauchyMode s (t i)‖ := by
      simpa only [dist_eq_norm] using dist_triangle
        (relativeSmoothCofactorMode s (t i) (A i) r L omega')
        (relativeCofactorMode s (t i) (A i) L omega') (cofactorCauchyMode s (t i))
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := by ring

end RHTower
