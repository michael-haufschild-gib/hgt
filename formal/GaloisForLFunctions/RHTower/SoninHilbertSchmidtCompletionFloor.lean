import GaloisForLFunctions.RHTower.SoninFourierChannelFamilyClosed
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact

/-!
# How large a completion's channels must be

A Hilbert--Schmidt operator's image is bounded by its Hilbert--Schmidt norm, so a completion whose
channels have Hilbert--Schmidt energies growing more slowly than the scale contributes a sublinear
sequence and fails.

Read against the slope threshold this is a size requirement rather than an exclusion: a completion
that restores the floor must have channels whose Hilbert--Schmidt norm exceeds a definite positive
multiple of the scale, infinitely often.  Every element of the principal-relative ideal is
Hilbert--Schmidt, so this is the size any ideal-valued completion would have to reach.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology InnerProduct InnerProductSpace

/-- A Hilbert--Schmidt operator's image is bounded by its Hilbert--Schmidt norm. -/
theorem norm_apply_le_hsNorm_mul {T : evenSubspace →L[ℂ] evenSubspace}
    (hT : IsHilbertSchmidt T) (v : evenSubspace) : ‖T v‖ ≤ hsNorm T * ‖v‖ :=
  le_trans (T.le_opNorm v) (mul_le_mul_of_nonneg_right (opNorm_le_hsNorm hT) (norm_nonneg v))

/-- **A completion whose Hilbert--Schmidt energies grow sublinearly fails.** -/
theorem not_bddBelow_soninCompletedPacketValueVar_of_sublinear_hsNorm (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (a b c q : ℝ) (hbc : b < c) (ha : 0 < a) (hab : a < b) (hb : 0 < b) (haq : a < q)
    (hqb : 2 * q ≤ b) (B : ℝ → ℝ) (hsub : Tendsto (fun r : ℝ => B r / r) atTop (𝓝 0)) :
    ∃ (κ : ℝ) (Nstart : ℕ) (hp : ∀ i : ℕ, 1 < soninShellCutScale b c (Nstart + i) κ),
      ∀ (v : ℕ → evenSubspace) (C : ℕ → (evenSubspace →L[ℂ] evenSubspace)),
        (∀ i, IsHilbertSchmidt (C i)) → (∀ i, ‖v i‖ ≤ 1) →
        (∀ i, hsNorm (C i) ≤ B (soninShellCutScale b c (Nstart + i) κ)) →
        ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
          M ≤ soninCompletedPacketValueVar s a b c
            (fun i => soninShellCutScale b c (Nstart + i) κ) hp
            (fun i => (⟪v i, C i (v i)⟫_ℂ).re) := by
  obtain ⟨κ, Nstart, hp, hmain⟩ :=
    not_bddBelow_soninCompletedPacketValueVar_of_sublinear_channel N₀ hN₀ a b c q hbc ha hab hb
      haq hqb B zero_le_one hsub
  refine ⟨κ, Nstart, hp, fun v C hHS hv hB => hmain v C hv fun i => ?_⟩
  refine le_trans (norm_apply_le_hsNorm_mul (hHS i) (v i)) ?_
  have hnn : (0 : ℝ) ≤ hsNorm (C i) := hsNorm_nonneg (C i)
  calc hsNorm (C i) * ‖v i‖ ≤ hsNorm (C i) * 1 := mul_le_mul_of_nonneg_left (hv i) hnn
    _ = hsNorm (C i) := mul_one _
    _ ≤ B (soninShellCutScale b c (Nstart + i) κ) := hB i

/-- **The schedule's eventual shortfall against a linear cap of half the energy slope.** -/
theorem exists_slope_schedule_eventually_add_le_hsNormSq (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (a b c q : ℝ) (hbc : b < c) (ha : 0 < a) (hab : a ≤ b) (hb : 0 < b) (haq : a < q)
    (hqb : 2 * q ≤ b) :
    ∃ (s κ : ℝ) (Nstart : ℕ) (hp : ∀ i : ℕ, 1 < soninShellCutScale b c (Nstart + i) κ),
      0 < s ∧ (∀ i : ℕ, c < soninShellCutScale b c (Nstart + i) κ * a) ∧
        ∀ᶠ i : ℕ in atTop, s * soninShellCutScale b c (Nstart + i) κ + 1 ≤
          hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c
            (soninShellCutScale b c (Nstart + i) κ) (hp i)) := by
  obtain ⟨κ, Nstart, hp, hκ, hcp, henergy⟩ :=
    exists_scale_sequence_of_schedule N₀ hN₀ a b c q hbc ha hab hb haq hqb
  set Dis : ℝ := 2 * hsNormSq (evenSoninProjectionCorrection b) +
    hsNormSq (evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) with hDis
  set slope : ℝ := (c - b) / (8 * κ) with hslope
  have hslopepos : 0 < slope := by
    have : (0 : ℝ) < c - b := by linarith
    rw [hslope]
    positivity
  refine ⟨slope / 2, κ, Nstart, hp, by positivity, hcp, ?_⟩
  have hadd : Tendsto (fun i : ℕ => Nstart + i) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat Nstart
  have hdiv : Tendsto (fun i : ℕ => soninShellCutScale b c (Nstart + i) κ) atTop atTop :=
    (tendsto_soninShellCutScale_atTop b c hbc hκ).comp hadd
  filter_upwards [hdiv.eventually_ge_atTop ((1 + 36 * Dis) / (slope / 2))] with i hbig
  have hlin : ((Nstart + i : ℕ) : ℝ) / 4 =
      slope * soninShellCutScale b c (Nstart + i) κ := by
    have hmul := soninShellCutScale_mul_slope b c hbc
      (show 0 < Nstart + i by
        rcases Nat.eq_zero_or_pos (Nstart + i) with h0 | hpos
        · exfalso
          have h1 := hp i
          rw [h0, soninShellCutScale] at h1
          norm_num at h1
        · exact hpos) hκ
    rw [hslope]
    calc ((Nstart + i : ℕ) : ℝ) / 4
        = ((c - b) / (2 * κ) * soninShellCutScale b c (Nstart + i) κ) / 4 := by rw [hmul]
      _ = (c - b) / (8 * κ) * soninShellCutScale b c (Nstart + i) κ := by ring
  have hthr : 1 + 36 * Dis ≤ slope / 2 * soninShellCutScale b c (Nstart + i) κ := by
    have hx := (div_le_iff₀ (half_pos hslopepos)).mp hbig
    rwa [mul_comm (soninShellCutScale b c (Nstart + i) κ) (slope / 2)] at hx
  have hsplit : slope / 2 * soninShellCutScale b c (Nstart + i) κ +
      slope / 2 * soninShellCutScale b c (Nstart + i) κ =
      slope * soninShellCutScale b c (Nstart + i) κ := by ring
  have hE := henergy i
  rw [hlin] at hE
  linarith [hthr, hsplit, hE]

/-- **A completion's Hilbert--Schmidt energy must reach a definite slope.**  If every channel's
Hilbert--Schmidt norm stays below a fixed positive multiple of the scale, the floor is lost. -/
theorem not_bddBelow_soninCompletedPacketValueVar_of_slope_hsNorm (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (a b c q : ℝ) (hbc : b < c) (ha : 0 < a) (hab : a < b) (hb : 0 < b) (haq : a < q)
    (hqb : 2 * q ≤ b) :
    ∃ (s κ : ℝ) (Nstart : ℕ) (hp : ∀ i : ℕ, 1 < soninShellCutScale b c (Nstart + i) κ),
      0 < s ∧ ∀ (v : ℕ → evenSubspace) (C : ℕ → (evenSubspace →L[ℂ] evenSubspace)),
        (∀ i, IsHilbertSchmidt (C i)) → (∀ i, ‖v i‖ ≤ 1) →
        (∀ᶠ i : ℕ in atTop, hsNorm (C i) ≤ s * soninShellCutScale b c (Nstart + i) κ) →
        ¬ ∃ M : ℝ, ∀ t : Finset ℕ,
          M ≤ soninCompletedPacketValueVar t a b c
            (fun i => soninShellCutScale b c (Nstart + i) κ) hp
            (fun i => (⟪v i, C i (v i)⟫_ℂ).re) := by
  obtain ⟨s, κ, Nstart, hp, hs, hcp, hshort⟩ :=
    exists_slope_schedule_eventually_add_le_hsNormSq N₀ hN₀ a b c q hbc ha hab.le hb haq hqb
  refine ⟨s, κ, Nstart, hp, hs, fun v C hHS hv hB => ?_⟩
  refine not_bddBelow_soninCompletedPacketValueVar_of_shortfall ha hab hbc
    (fun i => soninShellCutScale b c (Nstart + i) κ) hp hcp _ 1 one_pos ?_
  filter_upwards [hshort, hB] with i hi hBi
  have h1 : (⟪v i, C i (v i)⟫_ℂ).re ≤ ‖(⟪v i, C i (v i)⟫_ℂ)‖ := Complex.re_le_norm _
  have h2 : ‖(⟪v i, C i (v i)⟫_ℂ)‖ ≤ ‖v i‖ * ‖C i (v i)‖ := norm_inner_le_norm _ _
  have h3 : ‖v i‖ * ‖C i (v i)‖ ≤ 1 * (hsNorm (C i) * 1) :=
    mul_le_mul (hv i) (le_trans (norm_apply_le_hsNorm_mul (hHS i) (v i))
      (mul_le_mul_of_nonneg_left (hv i) (hsNorm_nonneg (C i)))) (norm_nonneg _) zero_le_one
  have h4 : (1 : ℝ) * (hsNorm (C i) * 1) ≤ s * soninShellCutScale b c (Nstart + i) κ := by
    rw [one_mul, mul_one]
    exact hBi
  have hcontrib : (⟪v i, C i (v i)⟫_ℂ).re ≤ s * soninShellCutScale b c (Nstart + i) κ :=
    le_trans (le_trans (le_trans h1 h2) h3) h4
  linarith [hi, hcontrib]

/-- **A surviving completion is large.**  If the floor is restored, some channel's Hilbert--Schmidt
norm exceeds a fixed positive multiple of the scale at arbitrarily late steps. -/
theorem frequently_slope_lt_hsNorm_of_bddBelow (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (a b c q : ℝ) (hbc : b < c) (ha : 0 < a) (hab : a < b) (hb : 0 < b) (haq : a < q)
    (hqb : 2 * q ≤ b) :
    ∃ (s κ : ℝ) (Nstart : ℕ) (hp : ∀ i : ℕ, 1 < soninShellCutScale b c (Nstart + i) κ),
      0 < s ∧ ∀ (v : ℕ → evenSubspace) (C : ℕ → (evenSubspace →L[ℂ] evenSubspace)),
        (∀ i, IsHilbertSchmidt (C i)) → (∀ i, ‖v i‖ ≤ 1) →
        (∃ M : ℝ, ∀ t : Finset ℕ,
          M ≤ soninCompletedPacketValueVar t a b c
            (fun i => soninShellCutScale b c (Nstart + i) κ) hp
            (fun i => (⟪v i, C i (v i)⟫_ℂ).re)) →
        ∃ᶠ i : ℕ in atTop, s * soninShellCutScale b c (Nstart + i) κ < hsNorm (C i) := by
  obtain ⟨s, κ, Nstart, hp, hs, hmain⟩ :=
    not_bddBelow_soninCompletedPacketValueVar_of_slope_hsNorm N₀ hN₀ a b c q hbc ha hab hb haq hqb
  refine ⟨s, κ, Nstart, hp, hs, fun v C hHS hv hfloor => ?_⟩
  by_contra hcon
  have hle : ∀ᶠ i : ℕ in atTop,
      hsNorm (C i) ≤ s * soninShellCutScale b c (Nstart + i) κ :=
    (Filter.not_frequently.mp hcon).mono fun i h => not_lt.mp h
  exact hmain v C hHS hv hle hfloor

end RHTower

