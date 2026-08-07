import GaloisForLFunctions.RHTower.SoninChannelAnnulusBound
import GaloisForLFunctions.RHTower.SoninFourierChannelFamilyClosed

/-!
# The Burnol conductor cannot restore the completed lower floor

The conductor is the logarithm of position plus the logarithm of frequency, each read on its own
geometric tower and each free to take whatever height it likes at every step.  Against the source
packets the two halves fail for opposite reasons and neither failure rescues the other.

The position half is bounded outright: the packets live inside a fixed outer radius, so only the
finitely many layers below that radius contribute and every higher layer cancels between its two
cutoffs.  The frequency half does grow — the packets' carrier runs with the scale even though their
support does not — but only logarithmically, because a tall tower buys nothing against a rapidly
decaying spectrum.

A constant plus a logarithm is sublinear, while the coupling energy grows linearly in the scale.  So
the sum is defeated exactly as each half is, and the conductor is closed as a completion at every
pair of height schedules.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology InnerProduct InnerProductSpace

/-- **The full Burnol conductor channel.**  The logarithm of position and the logarithm of
frequency, each truncated at its own tower height. -/
def evenBurnolConductorChannel (a r : ℝ) (np nf : ℕ) : evenSubspace →L[ℂ] evenSubspace :=
  evenLogShellChannel a r np + evenFourierLogShellChannel a r nf

theorem evenBurnolConductorChannel_apply (a r : ℝ) (np nf : ℕ) (w : evenSubspace) :
    evenBurnolConductorChannel a r np nf w =
      evenLogShellChannel a r np w + evenFourierLogShellChannel a r nf w := rfl

/-- The frequency half is self-adjoint: it is the position half conjugated by the self-adjoint
even Fourier transform. -/
theorem adjoint_evenFourierLogShellChannel (a r : ℝ) (n : ℕ) :
    ContinuousLinearMap.adjoint (evenFourierLogShellChannel a r n) =
      evenFourierLogShellChannel a r n := by
  rw [evenFourierLogShellChannel, adjoint_mul_clm, adjoint_mul_clm,
    adjoint_evenFourierTransform, adjoint_evenLogShellChannel, mul_assoc]

/-- The conductor is self-adjoint, both halves being so. -/
theorem adjoint_evenBurnolConductorChannel (a r : ℝ) (np nf : ℕ) :
    ContinuousLinearMap.adjoint (evenBurnolConductorChannel a r np nf) =
      evenBurnolConductorChannel a r np nf := by
  rw [evenBurnolConductorChannel, map_add, adjoint_evenLogShellChannel,
    adjoint_evenFourierLogShellChannel]

/-- The conductor's size is at most the sum of its two halves' sizes. -/
theorem norm_evenBurnolConductorChannel_apply_le (a r : ℝ) (np nf : ℕ) (w : evenSubspace) :
    ‖evenBurnolConductorChannel a r np nf w‖ ≤
      ‖evenLogShellChannel a r np w‖ + ‖evenFourierLogShellChannel a r nf w‖ := by
  rw [evenBurnolConductorChannel_apply]
  exact norm_add_le _ _

/-- **The excluded class is closed under sums.**  Two channel families, each dominated on the
packets by a sublinear cap, assemble into one that is again dominated by a sublinear cap, so the
completion built from their sum has no floor either.  The conductor is the instance where one
summand is the position channel and the other the frequency channel. -/
theorem not_bddBelow_soninCompletedPacketValueVar_of_sublinear_channel_add
    (N₀ : ℕ) (hN₀ : 1 ≤ N₀) (a b c q : ℝ) (hbc : b < c) (ha : 0 < a) (hab : a < b) (hb : 0 < b)
    (haq : a < q) (hqb : 2 * q ≤ b) (B₁ B₂ : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hsub₁ : Tendsto (fun r : ℝ => B₁ r / r) atTop (𝓝 0))
    (hsub₂ : Tendsto (fun r : ℝ => B₂ r / r) atTop (𝓝 0)) :
    ∃ (κ : ℝ) (Nstart : ℕ) (hp : ∀ i : ℕ, 1 < soninShellCutScale b c (Nstart + i) κ),
      ∀ (v : ℕ → evenSubspace) (C D : ℕ → (evenSubspace →L[ℂ] evenSubspace)),
        (∀ i, ‖v i‖ ≤ W) →
        (∀ i, ‖C i (v i)‖ ≤ B₁ (soninShellCutScale b c (Nstart + i) κ)) →
        (∀ i, ‖D i (v i)‖ ≤ B₂ (soninShellCutScale b c (Nstart + i) κ)) →
        ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
          M ≤ soninCompletedPacketValueVar s a b c
            (fun i => soninShellCutScale b c (Nstart + i) κ) hp
            (fun i => (⟪v i, (C i + D i) (v i)⟫_ℂ).re) := by
  have hsum : Tendsto (fun r : ℝ => (B₁ r + B₂ r) / r) atTop (𝓝 0) := by
    have h := hsub₁.add hsub₂
    rw [add_zero] at h
    exact h.congr fun r => by rw [← add_div]
  obtain ⟨κ, Nstart, hp, hmain⟩ :=
    not_bddBelow_soninCompletedPacketValueVar_of_sublinear_channel N₀ hN₀ a b c q hbc ha hab hb
      haq hqb _ hW hsum
  refine ⟨κ, Nstart, hp, fun v C D hv hC hD => ?_⟩
  refine hmain v (fun i => C i + D i) hv fun i => ?_
  exact le_trans (norm_add_le _ _) (add_le_add (hC i) (hD i))

/-- **Terminal no-go for the Burnol weld.**  No completion assembled from the full Burnol
conductor — logarithm of position plus logarithm of frequency, at *any* pair of height schedules —
restores the lower floor of the completed packet channel.

The hypotheses are the schedule's own: the sub-annuli sit inside the shell, their carriers stay
proportional to the scale, half-width times carrier stays bounded below, and the packet norms stay
bounded.  The two heights are arbitrary and independent. -/
theorem not_bddBelow_soninCompletedPacketValueVar_burnolConductorFamily
    (N₀ : ℕ) (hN₀ : 1 ≤ N₀) (a b c q : ℝ) (hbc : b < c) (ha : 0 < a) (hab : a < b) (hb : 0 < b)
    (haq : a < q) (hqb : 2 * q ≤ b)
    {Nd : ℕ} (hNd : 2 ≤ Nd) {a₀ r₀ : ℝ} (ha₀ : 0 < a₀) (hr₀ : 1 < r₀)
    {Q c₀ W : ℝ} (hQ : 0 < Q) (hc₀ : 0 < c₀) (hW : 0 ≤ W) :
    ∃ (κ : ℝ) (Nstart : ℕ) (hp : ∀ i : ℕ, 1 < soninShellCutScale b c (Nstart + i) κ),
      ∀ (heightP heightF : ℕ → ℕ) (m δ w : ℕ → ℝ) (hδ : ∀ i, 0 < δ i),
        (∀ i, 0 ≤ m i) → (∀ i, m i + δ i ≤ c) →
        (∀ i, 0 < w i) → (∀ i, 1 ≤ 2 * w i) →
        (∀ i, |soninScaledPacketMean (m i) (δ i) (2 * Real.pi * w i)| ≤ 1) →
        (∀ i, w i ≤ Q * soninShellCutScale b c (Nstart + i) κ) →
        (∀ i, c₀ ≤ δ i * (2 * w i)) →
        (∀ i, ‖soninScaledPacketEven (m i) (δ i) (2 * Real.pi * w i) (hδ i)‖ ≤ W) →
        ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
          M ≤ soninCompletedPacketValueVar s a b c
            (fun i => soninShellCutScale b c (Nstart + i) κ) hp
            (fun i => (⟪soninScaledPacketEven (m i) (δ i) (2 * Real.pi * w i) (hδ i),
              evenBurnolConductorChannel a₀ r₀ (heightP i) (heightF i)
                (soninScaledPacketEven (m i) (δ i) (2 * Real.pi * w i) (hδ i))⟫_ℂ).re) := by
  obtain ⟨Kc, hKc0, hKc⟩ :=
    exists_norm_evenFourierLogShellChannel_soninScaledPacketEven_le_carrier Nd hNd
  obtain ⟨C₁, hC₁0, hC₁⟩ :=
    exists_bound_norm_evenLogShellChannel_of_annulus a₀ r₀ c ha₀ hr₀ (hb.trans hbc)
  have hr₀0 : (0 : ℝ) < r₀ := lt_trans zero_lt_one hr₀
  have hNR : (2 : ℝ) ≤ (Nd : ℝ) := by exact_mod_cast hNd
  have hden : (0 : ℝ) < (2 * Nd : ℝ) - 1 := by linarith
  have hrp1 : (1 : ℝ) < r₀ ^ (2 * Nd - 2) := one_lt_pow₀ hr₀ (by omega)
  have hgap : (0 : ℝ) < 1 - (r₀ ^ (2 * Nd - 2))⁻¹ := by
    have := inv_lt_one_of_one_lt₀ hrp1
    linarith
  have hCf0 : (0 : ℝ) ≤
      8 * Kc / (((2 * Nd : ℝ) - 1) * (1 - (r₀ ^ (2 * Nd - 2))⁻¹)) := by positivity
  have hCconst0 : (0 : ℝ) ≤
      8 * Kc / (((2 * Nd : ℝ) - 1) * (1 - (r₀ ^ (2 * Nd - 2))⁻¹)) / c₀ ^ (2 * Nd - 2) := by
    positivity
  -- the frequency half's logarithmic slot is nonnegative and sublinear
  have hF0 : ∀ r : ℝ, 0 ≤ |Real.log a₀| + Real.log (max a₀ (2 * r₀ * Q * r)) := by
    intro r
    have h1 : Real.log a₀ ≤ Real.log (max a₀ (2 * r₀ * Q * r)) :=
      Real.log_le_log ha₀ (le_max_left _ _)
    have h2 : -|Real.log a₀| ≤ Real.log a₀ := neg_abs_le _
    linarith
  have hFsub : Tendsto
      (fun r : ℝ => (|Real.log a₀| + Real.log (max a₀ (2 * r₀ * Q * r))) / r) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => |Real.log a₀| / r) atTop (𝓝 0) :=
      Filter.Tendsto.const_div_atTop tendsto_id _
    have hKpos : (0 : ℝ) < 2 * r₀ * Q := by positivity
    have h2 := h1.add
      (GaloisForLFunctions.HTGeometry.tendsto_log_max_div_atTop (A := a₀) hKpos)
    rw [add_zero] at h2
    exact h2.congr fun r => by ring
  have hBsub : Tendsto (fun r : ℝ => Real.sqrt
      ((|Real.log a₀| + Real.log (max a₀ (2 * r₀ * Q * r))) ^ 2 * W ^ 2 +
        8 * Kc / (((2 * Nd : ℝ) - 1) * (1 - (r₀ ^ (2 * Nd - 2))⁻¹)) /
          c₀ ^ (2 * Nd - 2)) / r) atTop (𝓝 0) :=
    GaloisForLFunctions.HTGeometry.tendsto_sqrt_sq_mul_add_div_atTop hF0 hFsub hW hCconst0
  -- the position half only adds a constant, which is sublinear on its own
  have hSumSub : Tendsto (fun r : ℝ => (C₁ * W + Real.sqrt
      ((|Real.log a₀| + Real.log (max a₀ (2 * r₀ * Q * r))) ^ 2 * W ^ 2 +
        8 * Kc / (((2 * Nd : ℝ) - 1) * (1 - (r₀ ^ (2 * Nd - 2))⁻¹)) /
          c₀ ^ (2 * Nd - 2))) / r) atTop (𝓝 0) := by
    have hconst : Tendsto (fun r : ℝ => C₁ * W / r) atTop (𝓝 0) :=
      Filter.Tendsto.const_div_atTop tendsto_id _
    have h := hconst.add hBsub
    rw [add_zero] at h
    exact h.congr fun r => by rw [← add_div]
  obtain ⟨κ, Nstart, hpsc, hmain⟩ :=
    not_bddBelow_soninCompletedPacketValueVar_of_sublinear_channel N₀ hN₀ a b c q hbc ha hab hb
      haq hqb _ hW hSumSub
  refine ⟨κ, Nstart, hpsc, ?_⟩
  intro heightP heightF m δ w hδ hm hmc hwpos hw1 hmean hwQ hprod hnorm
  refine hmain (fun i => soninScaledPacketEven (m i) (δ i) (2 * Real.pi * w i) (hδ i))
    (fun i => evenBurnolConductorChannel a₀ r₀ (heightP i) (heightF i)) hnorm ?_
  intro i
  set ψ : evenSubspace :=
    soninScaledPacketEven (m i) (δ i) (2 * Real.pi * w i) (hδ i) with hψ
  -- the position half: the packet sits inside the shell's outer radius
  have hinside : evenIndicatorCutoff c ψ = ψ :=
    evenIndicatorCutoff_soninScaledPacketEven_eq_self (m i) (δ i) (2 * Real.pi * w i) (hδ i)
      (hm i) c (hmc i)
  have hpos : ‖evenLogShellChannel a₀ r₀ (heightP i) ψ‖ ≤ C₁ * W := by
    refine le_trans (hC₁ (heightP i) ψ hinside) ?_
    exact mul_le_mul_of_nonneg_left (hnorm i) hC₁0
  -- the frequency half: the schedule's own reduction
  have hfreq : ‖evenFourierLogShellChannel a₀ r₀ (heightF i) ψ‖ ≤ Real.sqrt
      ((|Real.log a₀| +
          Real.log (max a₀ (2 * r₀ * Q * soninShellCutScale b c (Nstart + i) κ))) ^ 2 * W ^ 2 +
        8 * Kc / (((2 * Nd : ℝ) - 1) * (1 - (r₀ ^ (2 * Nd - 2))⁻¹)) /
          c₀ ^ (2 * Nd - 2)) := by
    refine le_trans
      (hKc a₀ r₀ ha₀ hr₀ (heightF i) (m i) (δ i) (w i) (hδ i) (hwpos i) (hw1 i) (hmean i))
      (Real.sqrt_le_sqrt ?_)
    have hpos₁ : (0 : ℝ) < max a₀ (r₀ * (2 * w i)) := lt_of_lt_of_le ha₀ (le_max_left _ _)
    have hone₁ : (1 : ℝ) ≤ max a₀ (r₀ * (2 * w i)) := by
      have : (1 : ℝ) ≤ r₀ * (2 * w i) := by nlinarith [hw1 i, hr₀.le]
      exact le_trans this (le_max_right _ _)
    have hlognn : (0 : ℝ) ≤ Real.log (max a₀ (r₀ * (2 * w i))) := Real.log_nonneg hone₁
    have hmaxle : max |Real.log a₀| |Real.log (max a₀ (r₀ * (2 * w i)))| ≤
        |Real.log a₀| + Real.log (max a₀ (r₀ * (2 * w i))) := by
      rw [abs_of_nonneg hlognn]
      exact max_le (le_add_of_nonneg_right hlognn) (le_add_of_nonneg_left (abs_nonneg _))
    have hargle : r₀ * (2 * w i) ≤ 2 * r₀ * Q * soninShellCutScale b c (Nstart + i) κ := by
      have := hwQ i
      nlinarith [hr₀0, this]
    have hmaxmono : max a₀ (r₀ * (2 * w i)) ≤
        max a₀ (2 * r₀ * Q * soninShellCutScale b c (Nstart + i) κ) :=
      max_le_max le_rfl hargle
    have hlogmono : Real.log (max a₀ (r₀ * (2 * w i))) ≤
        Real.log (max a₀ (2 * r₀ * Q * soninShellCutScale b c (Nstart + i) κ)) :=
      Real.log_le_log hpos₁ hmaxmono
    have hLle : max |Real.log a₀| |Real.log (max a₀ (r₀ * (2 * w i)))| ≤
        |Real.log a₀| +
          Real.log (max a₀ (2 * r₀ * Q * soninShellCutScale b c (Nstart + i) κ)) := by
      linarith
    have hLnn : (0 : ℝ) ≤ max |Real.log a₀| |Real.log (max a₀ (r₀ * (2 * w i)))| :=
      le_trans (abs_nonneg _) (le_max_left _ _)
    have hsq₁ : max |Real.log a₀| |Real.log (max a₀ (r₀ * (2 * w i)))| ^ 2 ≤
        (|Real.log a₀| +
          Real.log (max a₀ (2 * r₀ * Q * soninShellCutScale b c (Nstart + i) κ))) ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_self_le_mul_self hLnn hLle
    have hsq₂ : ‖ψ‖ ^ 2 ≤ W ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_self_le_mul_self (norm_nonneg _) (hnorm i)
    have hpartA : max |Real.log a₀| |Real.log (max a₀ (r₀ * (2 * w i)))| ^ 2 * ‖ψ‖ ^ 2 ≤
        (|Real.log a₀| +
          Real.log (max a₀ (2 * r₀ * Q * soninShellCutScale b c (Nstart + i) κ))) ^ 2 * W ^ 2 :=
      mul_le_mul hsq₁ hsq₂ (sq_nonneg _) (sq_nonneg _)
    have hc₀p : (0 : ℝ) < c₀ ^ (2 * Nd - 2) := pow_pos hc₀ (2 * Nd - 2)
    have hprodp : c₀ ^ (2 * Nd - 2) ≤ (δ i * (2 * w i)) ^ (2 * Nd - 2) :=
      pow_le_pow_left₀ hc₀.le (hprod i) (2 * Nd - 2)
    have hpartB : 8 * Kc / (((2 * Nd : ℝ) - 1) * (1 - (r₀ ^ (2 * Nd - 2))⁻¹)) *
        ((δ i * (2 * w i)) ^ (2 * Nd - 2))⁻¹ ≤
        8 * Kc / (((2 * Nd : ℝ) - 1) * (1 - (r₀ ^ (2 * Nd - 2))⁻¹)) / c₀ ^ (2 * Nd - 2) := by
      rw [div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ hCf0
      exact inv_anti₀ hc₀p hprodp
    linarith
  exact le_trans (norm_evenBurnolConductorChannel_apply_le a₀ r₀ (heightP i) (heightF i) ψ)
    (add_le_add hpos hfreq)

/-- **The schedule's two scale conditions are simultaneously satisfiable**, so the no-go is not
vacuous.  Under the tied schedule the half-width times the scale is the schedule constant, so a
carrier proportional to the scale makes the half-width times carrier constant as well: the carrier
runs while the support shrinks, at exactly compensating rates. -/
theorem exists_carrier_halfwidth_schedule (b c κ q : ℝ) (hbc : b < c) (hκ : 0 < κ) (hq : 0 < q)
    (Nstart : ℕ) (hstart : 0 < Nstart) :
    ∃ δ w : ℕ → ℝ, (∀ i, 0 < δ i) ∧ (∀ i, 0 < w i) ∧
      (∀ i, w i ≤ q * soninShellCutScale b c (Nstart + i) κ) ∧
      (∀ i, 2 * q * κ ≤ δ i * (2 * w i)) := by
  refine ⟨fun i => soninShellCutWidth b c (Nstart + i),
    fun i => q * soninShellCutScale b c (Nstart + i) κ, fun i => ?_, fun i => ?_,
    fun i => le_rfl, fun i => ?_⟩
  · exact soninShellCutWidth_pos b c hbc (by omega)
  · exact mul_pos hq (soninShellCutScale_pos b c hbc (by omega) hκ)
  · have hmul := soninShellCutWidth_mul_scale b c hbc (N := Nstart + i) (by omega) κ
    have heq : soninShellCutWidth b c (Nstart + i) *
        (2 * (q * soninShellCutScale b c (Nstart + i) κ)) = 2 * q * κ := by
      rw [show soninShellCutWidth b c (Nstart + i) *
          (2 * (q * soninShellCutScale b c (Nstart + i) κ)) =
          2 * q * (soninShellCutWidth b c (Nstart + i) *
            soninShellCutScale b c (Nstart + i) κ) from by ring, hmul]
    exact heq.ge

end RHTower
