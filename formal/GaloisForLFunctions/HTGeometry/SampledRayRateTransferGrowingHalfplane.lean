import GaloisForLFunctions.HTGeometry.SampledRayRateTransferHalfplane

/-!
# Growing-order ray rate transfer for half-plane analytic functions

The growing-order transfer of `SampledRayRateTransfer` with the global entirety hypothesis weakened
to analyticity on a right half-plane, exactly as `SampledRayRateTransferHalfplane` weakens the
fixed-order one: the smooth-bump window estimate is insensitive to the derivative order, so the
`⌊cR⌋ + 1` bookkeeping goes through verbatim.
-/

noncomputable section

namespace HTGeometry

open Set

/-- **Growing-order half-plane ray rate transfer**: window-sampled exponential decay at the growing
derivative order `⌊cR⌋ + 1` propagates to exponential decay along the ray, with rate loss `6c`, for
a function analytic only on a right half-plane `{Re > T}`.  This is the transfer applicable to
Lambert-type transforms, which are analytic only where their exponential test is contractive. -/
theorem norm_le_ray_of_sampled_decay_halfplane
    {T : ℝ} {H : ℂ → ℂ} (hH : ∀ t : ℝ, T < t → AnalyticAt ℂ H (t : ℂ))
    {R₀ δ K c σ C σ' : ℝ} (hTR₀ : T < R₀)
    (hδ : 0 < δ) (hK : 0 ≤ K) (hc : 0 < c) (hC : 0 ≤ C) (hσ'0 : 0 ≤ σ')
    (hσ' : σ' + 6 * c ≤ σ)
    (hder : ∀ R : ℝ, R₀ ≤ R → ∀ x ∈ Set.Icc R (R + 1),
      ‖iteratedDeriv (⌊c * R⌋₊ + 1) H (x : ℂ)‖ ≤ K * Real.exp (-(δ * R)))
    (hnodes : ∀ R : ℝ, R₀ ≤ R → ∃ s : Finset ℝ,
      s.card = ⌊c * R⌋₊ + 1 ∧ ↑s ⊆ Set.Icc R (R + 1) ∧
      (∀ t ∈ s, ∀ u ∈ s, t ≠ u →
        1 / (4 * ((⌊c * R⌋₊ : ℝ) + 1)) ≤ |t - u|) ∧
      (∀ t ∈ s, ‖H (t : ℂ)‖ ≤ C * Real.exp (-(σ * R)))) :
    ∃ C' R₁ : ℝ, ∀ x : ℝ, R₁ ≤ x →
      ‖H (x : ℂ)‖ ≤ C' * Real.exp (-(σ' * x)) := by
  set L : ℝ := Real.log (2 * K + 1) with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have h2K : 2 * K ≤ Real.exp L := by
    rw [hLdef, Real.exp_log (by linarith : (0:ℝ) < 2 * K + 1)]
    linarith
  refine ⟨2 * C * Real.exp (6 + σ') + 1,
    max (R₀ + 1)
      (max (Real.exp (σ' / c + 2) / c) ((σ' + L) / c) + 1), ?_⟩
  intro x hx
  set R : ℝ := x - 1 with hR
  have hxR : x = R + 1 := by rw [hR]; ring
  have hRR₀ : R₀ ≤ R := by
    have h := le_trans (le_max_left _ _) hx
    rw [hR]
    linarith
  have hmaxT : max (Real.exp (σ' / c + 2) / c) ((σ' + L) / c) ≤ R := by
    have h := le_trans (le_max_right _ _) hx
    rw [hR]
    linarith
  have hcR1 : Real.exp (σ' / c + 2) ≤ c * R := by
    have h1 : Real.exp (σ' / c + 2) / c ≤ R :=
      le_trans (le_max_left _ _) hmaxT
    rw [div_le_iff₀ hc] at h1
    linarith [h1]
  have hcR2 : σ' + L ≤ c * R := by
    have h1 : (σ' + L) / c ≤ R := le_trans (le_max_right _ _) hmaxT
    rw [div_le_iff₀ hc] at h1
    linarith [h1]
  have hcR0 : 0 < c * R := lt_of_lt_of_le (Real.exp_pos _) hcR1
  have hR0 : 0 < R := by nlinarith
  set N : ℕ := ⌊c * R⌋₊ with hNdef
  have hNle : (N : ℝ) ≤ c * R := Nat.floor_le hcR0.le
  have hNge : c * R ≤ (N : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  obtain ⟨s, hcard, hsub, hsep, hsamp⟩ := hnodes R hRR₀
  have hxmem : x ∈ Set.Icc R (R + 1) := by
    rw [hR]
    constructor <;> linarith
  have hwin := norm_le_window_of_sampled_halfplane hH hcard
    (lt_of_lt_of_le hTR₀ hRR₀) hsub hsep
    (hder R hRR₀) (by positivity) hsamp hxmem
  -- interpolant term
  have hA : 2 * Real.exp (6 * ((N : ℝ) + 1)) * (C * Real.exp (-(σ * R)))
      ≤ 2 * C * Real.exp (6 + σ') * Real.exp (-(σ' * x)) := by
    have h6 : 6 * ((N : ℝ) + 1) ≤ 6 * (c * R) + 6 := by linarith
    calc 2 * Real.exp (6 * ((N : ℝ) + 1)) * (C * Real.exp (-(σ * R)))
        = 2 * C * Real.exp (6 * ((N : ℝ) + 1) + -(σ * R)) := by
          rw [Real.exp_add]
          ring
      _ ≤ 2 * C * Real.exp ((6 + σ') + -(σ' * x)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.exp_le_exp.2
          rw [hxR]
          nlinarith [mul_nonneg hR0.le
            (by linarith : (0:ℝ) ≤ σ - (σ' + 6 * c))]
      _ = 2 * C * Real.exp (6 + σ') * Real.exp (-(σ' * x)) := by
          rw [Real.exp_add]
          ring
  -- remainder term
  have hB : 2 * (K * Real.exp (-(δ * R)) / (N + 1).factorial)
      ≤ Real.exp (-(σ' * x)) := by
    have hsup := one_div_factorial_le_superexp (n := N + 1) (by omega)
    push_cast at hsup
    have hlogcR : σ' / c + 2 ≤ Real.log (c * R) := by
      rw [← Real.log_exp (σ' / c + 2)]
      exact Real.log_le_log (Real.exp_pos _) hcR1
    have hlogN : Real.log (c * R) ≤ Real.log ((N : ℝ) + 1) :=
      Real.log_le_log hcR0 hNge
    have hfac1 : σ' / c + 1 ≤ Real.log ((N : ℝ) + 1) - 1 := by linarith
    have hfac0 : (0:ℝ) ≤ σ' / c + 1 := by positivity
    have hprod : σ' * R + (σ' + L)
        ≤ ((N : ℝ) + 1) * (Real.log ((N : ℝ) + 1) - 1) := by
      have h1 : (c * R) * (σ' / c + 1)
          ≤ ((N : ℝ) + 1) * (Real.log ((N : ℝ) + 1) - 1) :=
        mul_le_mul hNge hfac1 hfac0 (by positivity)
      have h2 : (c * R) * (σ' / c + 1) = σ' * R + c * R := by
        field_simp
      rw [h2] at h1
      linarith
    have hkey : σ' * x + L
        ≤ ((N : ℝ) + 1) * (Real.log ((N : ℝ) + 1) - 1) + δ * R := by
      rw [hxR]
      have hδR : 0 ≤ δ * R := by positivity
      nlinarith [hprod]
    calc 2 * (K * Real.exp (-(δ * R)) / (N + 1).factorial)
        = (2 * K) * Real.exp (-(δ * R)) * ((1:ℝ) / (N + 1).factorial) := by
          ring
      _ ≤ Real.exp L * Real.exp (-(δ * R))
          * Real.exp (-(((N : ℝ) + 1) * (Real.log ((N : ℝ) + 1) - 1))) := by
          apply mul_le_mul _ hsup (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right h2K (Real.exp_nonneg _)
      _ = Real.exp (L + -(δ * R)
          + -(((N : ℝ) + 1) * (Real.log ((N : ℝ) + 1) - 1))) := by
          rw [Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (-(σ' * x)) := by
          apply Real.exp_le_exp.2
          linarith [hkey]
  calc ‖H (x : ℂ)‖
      ≤ 2 * Real.exp (6 * ((N : ℝ) + 1)) * (C * Real.exp (-(σ * R)))
        + 2 * (K * Real.exp (-(δ * R)) / (N + 1).factorial) := hwin
    _ ≤ 2 * C * Real.exp (6 + σ') * Real.exp (-(σ' * x))
        + Real.exp (-(σ' * x)) := add_le_add hA hB
    _ = (2 * C * Real.exp (6 + σ') + 1) * Real.exp (-(σ' * x)) := by ring

end HTGeometry
