import GaloisForLFunctions.RHTower.XiShiftedStrictFrontierAllContactArithmeticSource

/-!
# Strict-frontier bounded-gauge obstruction

A positive-order admission contact cannot be removed by a gauge bounded on its right germ.
More sharply, any gauge normalizing the newborn admission norm to a finite value has singular
order fixed by the Padé contact order.  This converts integer logarithmic residue from a contact
label into an obstruction to bounded trivialization.  It remains local: excluding cofinally many
such contacts requires a global arithmetic estimate not proved here.
-/

open Filter Set Topology

namespace RHTower

noncomputable section

/-- A finite nonzero normalization of an order-`d` contact forces the gauge's exact scaled limit.
This is the local algebraic content of contact holonomy as singular gauge order. -/
theorem tendsto_scaledGauge_of_contact_normalization
    {N g : ℝ → ℝ} {d : ℕ} {C L : ℝ}
    (hC : C ≠ 0)
    (hcontact : Tendsto (fun u : ℝ => N u / u ^ d)
      (𝓝[>] (0 : ℝ)) (𝓝 C))
    (hnormalize : Tendsto (fun u : ℝ => g u * N u)
      (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (fun u : ℝ => u ^ d * g u)
      (𝓝[>] (0 : ℝ)) (𝓝 (L / C)) := by
  have hdiv := hnormalize.div hcontact hC
  have hqne : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), N u / u ^ d ≠ 0 :=
    hcontact.eventually (isOpen_ne.mem_nhds hC)
  have heq : (fun u : ℝ => (g u * N u) / (N u / u ^ d)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun u : ℝ => u ^ d * g u) := by
    filter_upwards [hqne] with u hu
    have hN : N u ≠ 0 := by
      intro hNu
      simp [hNu] at hu
    field_simp
  exact hdiv.congr' heq

/-- A bounded gauge cannot turn a positive-order vanishing contact into a nonzero finite limit. -/
theorem boundedGauge_normalized_contact_limit_eq_zero
    {N g : ℝ → ℝ} {d : ℕ} {C L : ℝ}
    (hd : 0 < d)
    (hcontact : Tendsto (fun u : ℝ => N u / u ^ d)
      (𝓝[>] (0 : ℝ)) (𝓝 C))
    (hg : IsBoundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ)) (norm ∘ g))
    (hnormalize : Tendsto (fun u : ℝ => g u * N u)
      (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    L = 0 := by
  have hid : Tendsto (fun u : ℝ => u) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hpow : Tendsto (fun u : ℝ => u ^ d) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [zero_pow (Nat.ne_of_gt hd)] using hid.pow d
  have hN : Tendsto N (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hmul := hpow.mul hcontact
    have heq : (fun u : ℝ => u ^ d * (N u / u ^ d)) =ᶠ[𝓝[>] (0 : ℝ)] N := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact mul_div_cancel₀ (N u) (pow_ne_zero d hu.ne')
    have hprod : Tendsto (fun u : ℝ => u ^ d * (N u / u ^ d))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 * C)) := hmul
    simpa only [zero_mul] using hprod.congr' heq
  have hzero : Tendsto (fun u : ℝ => g u * N u)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [smul_eq_mul] using hg.smul_tendsto_zero hN
  exact tendsto_nhds_unique hnormalize hzero

/-- At a shifted-Xi strict frontier, every germ-bounded gauge leaves the newborn admission
coordinate at zero. -/
theorem xiShiftedStrictFrontier_boundedGauge_normalizedAdmissionLimit_eq_zero
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hd : 0 < d)
    (hzero : ∀ k < 2 * (n + 2) + d,
      xiShiftedStrictFrontierPadeDefect n k = 0)
    {g : ℝ → ℝ} {L : ℝ}
    (hg : IsBoundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ)) (norm ∘ g))
    (hnormalize : Tendsto
      (fun u : ℝ => g u * xiShiftedCanonicalAdmissionNorm
        (xiShiftedHigherBlockTerminalFrontier (n + 1) + u) (n + 2))
      (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    L = 0 := by
  exact boundedGauge_normalized_contact_limit_eq_zero hd
    (tendsto_xiShiftedStrictFrontierAdmissionNorm_div_pow_at_contact
      hne hstrict hd hzero) hg hnormalize

/-- Exact singular order of every gauge normalizing a shifted-Xi strict-frontier admission
contact.  Contact multiplicity is therefore the gauge's forced pole order. -/
theorem tendsto_xiShiftedStrictFrontier_scaledGauge_of_normalizedAdmission
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hd : 0 < d)
    (hzero : ∀ k < 2 * (n + 2) + d,
      xiShiftedStrictFrontierPadeDefect n k = 0)
    (hsigned : 0 < (-1 : ℝ) ^ d *
      xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d))
    {g : ℝ → ℝ} {L : ℝ}
    (hnormalize : Tendsto
      (fun u : ℝ => g u * xiShiftedCanonicalAdmissionNorm
        (xiShiftedHigherBlockTerminalFrontier (n + 1) + u) (n + 2))
      (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (fun u : ℝ => u ^ d * g u)
      (𝓝[>] (0 : ℝ))
      (𝓝 (L / ((-1 : ℝ) ^ d * (Nat.choose (2 * (n + 2) + d) d : ℝ) *
        xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d)))) := by
  have hchoose : 0 < (Nat.choose (2 * (n + 2) + d) d : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : d ≤ 2 * (n + 2) + d)
  have hcoefficient :
      (-1 : ℝ) ^ d * (Nat.choose (2 * (n + 2) + d) d : ℝ) *
          xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d) ≠ 0 := by
    have hpos : 0 < (-1 : ℝ) ^ d * (Nat.choose (2 * (n + 2) + d) d : ℝ) *
        xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d) := by
      calc
        (-1 : ℝ) ^ d * (Nat.choose (2 * (n + 2) + d) d : ℝ) *
            xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d) =
            (Nat.choose (2 * (n + 2) + d) d : ℝ) *
              ((-1 : ℝ) ^ d *
                xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d)) := by ring
        _ > 0 := mul_pos hchoose hsigned
    exact hpos.ne'
  exact tendsto_scaledGauge_of_contact_normalization hcoefficient
    (tendsto_xiShiftedStrictFrontierAdmissionNorm_div_pow_at_contact
      hne hstrict hd hzero) hnormalize

/-- Every gauge producing a nonzero finite normalization at a shifted-Xi strict frontier is
unbounded on the right germ. -/
theorem xiShiftedStrictFrontier_normalizingGauge_not_bounded
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hd : 0 < d)
    (hzero : ∀ k < 2 * (n + 2) + d,
      xiShiftedStrictFrontierPadeDefect n k = 0)
    {g : ℝ → ℝ} {L : ℝ} (hL : L ≠ 0)
    (hnormalize : Tendsto
      (fun u : ℝ => g u * xiShiftedCanonicalAdmissionNorm
        (xiShiftedHigherBlockTerminalFrontier (n + 1) + u) (n + 2))
      (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    ¬IsBoundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ)) (norm ∘ g) := by
  intro hg
  exact hL (xiShiftedStrictFrontier_boundedGauge_normalizedAdmissionLimit_eq_zero
    hne hstrict hd hzero hg hnormalize)

end

end RHTower
