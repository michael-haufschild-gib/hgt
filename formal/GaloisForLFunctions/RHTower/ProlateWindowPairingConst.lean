import GaloisForLFunctions.RHTower.ProlateWindowMassLimit

/-!
# Window pairings against a fixed weight

`tendsto_prolateWindowMass` and `tendsto_prolateWindowPairing` compare a prolate family with itself
or with a second prolate family.  What the ladder pin needs instead is the pairing against a *fixed*
continuous weight — the Hermite function at a rung.  The proof is the same Grönwall envelope: on the
window the profile is within `oscWindowEnvelope` of the limit profile, so the pairing differs from
the limiting pairing by at most that envelope times the fixed weight's window mass.
-/

noncomputable section

open Set Filter Topology MeasureTheory

namespace RHTower

/-- **Window pairings against a fixed weight converge.** -/
theorem tendsto_prolateWindowPairing_const {ι : Type*} {L : Filter ι}
    {mu c : ι → ℝ} {K B m : ℝ} {u u' u'' : ι → ℝ → ℝ} {g : ℝ → ℝ}
    (hK : 0 < K) (hg : Continuous g)
    (hu : ∀ i x, HasDerivAt (u i) (u' i x) x) (hu' : ∀ i x, HasDerivAt (u' i) (u'' i x) x)
    (heu : ∀ i, Function.Even (u i))
    (hev : ∀ᶠ i in L, 0 < c i ∧ 2 * K ^ 2 ≤ c i ∧
      (∀ x ∈ Icc (0 : ℝ) K, u'' i x = rescaledProlateP (c i) (mu i) x * u i x
        + rescaledProlateQ (c i) x * u' i x) ∧
      (∀ x ∈ Icc (0 : ℝ) K, max |u i x| |u' i x| ≤ B) ∧ u i 0 = 1 ∧ u' i 0 = 0)
    (hmu : Tendsto mu L (𝓝 m)) (hc : Tendsto c L atTop) :
    Tendsto (fun i => ∫ x in (-K)..K, u i x * g x) L
      (𝓝 (∫ x in (-K)..K, oscProfile m x * g x)) := by
  have hKK : (-K : ℝ) ≤ K := by linarith
  set G : ℝ := ∫ x in (-K)..K, |g x| with hGdef
  have hG0 : 0 ≤ G := by
    rw [hGdef]
    exact intervalIntegral.integral_nonneg hKK fun x _ => abs_nonneg _
  have hgint : IntervalIntegrable g volume (-K) K := hg.intervalIntegrable _ _
  -- the pairing difference is controlled by the Grönwall envelope
  have hdiff : ∀ᶠ i in L,
      ‖(∫ x in (-K)..K, u i x * g x) - ∫ x in (-K)..K, oscProfile m x * g x‖
        ≤ oscWindowEnvelope (c i) (mu i) m K B * G := by
    filter_upwards [hev] with i hi
    obtain ⟨hcpos, hcK, hequ, hBi, h0, h0'⟩ := hi
    have hcu : Continuous (u i) := Differentiable.continuous fun x => (hu i x).differentiableAt
    have hdist0 : ∀ x ∈ Icc (0 : ℝ) K,
        |u i x - oscProfile m x| ≤ oscWindowEnvelope (c i) (mu i) m K B := by
      intro x hx
      exact le_trans (le_max_left _ _)
        (prolateProfile_window_osc_dist_le (m := m) hK hcK (hu i) (hu' i) hequ hBi h0 h0' x hx)
    have hdist : ∀ x ∈ Icc (-K) K,
        |u i x - oscProfile m x| ≤ oscWindowEnvelope (c i) (mu i) m K B :=
      abs_sub_le_of_even_window' (heu i) (even_oscProfile m) hdist0
    have hsub : (∫ x in (-K)..K, u i x * g x) - ∫ x in (-K)..K, oscProfile m x * g x
        = ∫ x in (-K)..K, (u i x - oscProfile m x) * g x := by
      have hI1 : IntervalIntegrable (fun x : ℝ => u i x * g x) volume (-K) K :=
        (hcu.mul hg).intervalIntegrable _ _
      have hI2 : IntervalIntegrable (fun x : ℝ => oscProfile m x * g x) volume (-K) K :=
        ((continuous_oscProfile m).mul hg).intervalIntegrable _ _
      have hs := intervalIntegral.integral_sub hI1 hI2
      rw [← hs]
      refine intervalIntegral.integral_congr fun x _ => ?_
      ring
    rw [hsub, Real.norm_eq_abs]
    have habs := intervalIntegral.abs_integral_le_integral_abs
      (f := fun x : ℝ => (u i x - oscProfile m x) * g x) (μ := volume) hKK
    refine le_trans habs ?_
    have hmono : (∫ x in (-K)..K, |(u i x - oscProfile m x) * g x|)
        ≤ ∫ x in (-K)..K, oscWindowEnvelope (c i) (mu i) m K B * |g x| := by
      refine intervalIntegral.integral_mono_on hKK
        (((hcu.sub (continuous_oscProfile m)).mul hg).abs.intervalIntegrable _ _)
        ((continuous_const.mul hg.abs).intervalIntegrable _ _) fun x hx => ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hdist x hx) (abs_nonneg _)
    rw [intervalIntegral.integral_const_mul] at hmono
    exact hmono
  have henv : Tendsto (fun i => oscWindowEnvelope (c i) (mu i) m K B * G) L (𝓝 0) := by
    have h := (tendsto_oscWindowEnvelope (K := K) (B := B) hmu hc).mul_const G
    simpa using h
  have hzero := squeeze_zero_norm' hdiff henv
  have := hzero.add_const (∫ x in (-K)..K, oscProfile m x * g x)
  simpa using this

end RHTower

end
