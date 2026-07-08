import GaloisForLFunctions.RHTower.WindowLadder
import GaloisForLFunctions.RHTower.AnnealWindowRelation
import GaloisForLFunctions.U0.U0KummerBranch

/-!
# The windowed deck reading of the height certificates

Local analytic `n`-th roots of ξ exist on the two slit charts around EVERY point: the charts are
star-convex (hence simply connected), they exclude their center, and on a small enough ball the
center is the only possible ξ-zero, so ξ is nonvanishing on the charts and the Kummer branch
applies.  Consequently the deck class of ξ at a zero is always realized by actual roots, and the
height-window certificate becomes EQUIVALENT to the triviality of the deck classes at the window's
finitely many zeros: the ladder rung on a bounded box is a finite conjunction of local monodromy
conditions, each attached to one zero and readable from any pair of chart roots.

The holography theorem closes the circle in the other direction: UNDER the certificate, the deck
class value at level `2^{k+1}` of any reflection-closed configuration enclosed in a line-centered window
equals `exp(2πi·L/2^{k+1})` with `L` the on-line order sum — the certificate forces every boundary
loop to read pure critical-line data, the off-line (box) contribution being killed mod `2^{k+1}`.
-/

namespace RHTower

open Complex Set Metric

/-! ## The slit charts are simply connected -/

/-- The right slit chart is simply connected: star-convex about the half-radius point on the slit
axis, intersected with the convex ball. -/
theorem isSimplyConnected_chartR (a : ℂ) {R : ℝ} (hR : 0 < R) :
    IsSimplyConnected (chartR a R) := by
  have hmem := center_mem_chartR a hR
  have hstar : StarConvex ℝ (a + ((R / 2 : ℝ) : ℂ)) (chartR a R) :=
    (starConvex_slitChartR a (by positivity : (0:ℝ) < R / 2)).inter
      ((convex_ball a R).starConvex hmem.2)
  haveI : ContractibleSpace (chartR a R) := hstar.contractibleSpace ⟨_, hmem⟩
  exact SimplyConnectedSpace.ofContractible _

/-- The left slit chart is simply connected. -/
theorem isSimplyConnected_chartL (a : ℂ) {R : ℝ} (hR : 0 < R) :
    IsSimplyConnected (chartL a R) := by
  have hmem := center_mem_chartL a hR
  have hstar : StarConvex ℝ (a - ((R / 2 : ℝ) : ℂ)) (chartL a R) :=
    (starConvex_slitChartL a (by positivity : (0:ℝ) < R / 2)).inter
      ((convex_ball a R).starConvex hmem.2)
  haveI : ContractibleSpace (chartL a R) := hstar.contractibleSpace ⟨_, hmem⟩
  exact SimplyConnectedSpace.ofContractible _

/-! ## ξ is nonvanishing on small charts, so chart roots exist -/

/-- On a small enough ball the center is the only possible ξ-zero; the slit charts exclude the
center, so ξ is nonvanishing on both charts at every radius below the peel radius. -/
theorem xi_ne_zero_on_charts (ρ₀ : ℂ) :
    ∃ R₀ > 0, ∀ R : ℝ, 0 < R → R ≤ R₀ →
      (∀ z ∈ chartR ρ₀ R, xi z ≠ 0) ∧ (∀ z ∈ chartL ρ₀ R, xi z ≠ 0) := by
  obtain ⟨R₀, hR₀, h, hhan, hh0, hfact⟩ := xi_peel_ball ρ₀
  refine ⟨R₀, hR₀, ?_⟩
  intro R hR hRle
  have hball : ball ρ₀ R ⊆ ball ρ₀ R₀ := ball_subset_ball hRle
  constructor
  · rintro z ⟨hslit, hzball⟩ hz0
    have hzb : z ∈ ball ρ₀ R₀ := hball hzball
    have hne : z - ρ₀ ≠ 0 := by
      intro h0
      rw [Set.mem_setOf_eq, h0] at hslit
      simp [Complex.mem_slitPlane_iff] at hslit
    rw [hfact z hzb] at hz0
    exact absurd hz0 (mul_ne_zero (pow_ne_zero _ hne) (hh0 z hzb))
  · rintro z ⟨hslit, hzball⟩ hz0
    have hzb : z ∈ ball ρ₀ R₀ := hball hzball
    have hne : z - ρ₀ ≠ 0 := by
      intro h0
      have hz : ρ₀ - z = 0 := by
        rw [sub_eq_zero.mp h0, sub_self]
      rw [Set.mem_setOf_eq, hz] at hslit
      simp [Complex.mem_slitPlane_iff] at hslit
    rw [hfact z hzb] at hz0
    exact absurd hz0 (mul_ne_zero (pow_ne_zero _ hne) (hh0 z hzb))

/-- **Chart roots of ξ exist at every level around every point**: at every radius below the peel
radius, both slit charts carry analytic `n`-th roots of ξ. -/
theorem xi_exists_chart_roots (ρ₀ : ℂ) :
    ∃ R₀ > 0, ∀ R : ℝ, 0 < R → R ≤ R₀ → ∀ n : ℕ, 0 < n →
      (∃ G₁, AnalyticOnNhd ℂ G₁ (chartR ρ₀ R) ∧ ∀ z ∈ chartR ρ₀ R, G₁ z ^ n = xi z) ∧
      (∃ G₂, AnalyticOnNhd ℂ G₂ (chartL ρ₀ R) ∧ ∀ z ∈ chartL ρ₀ R, G₂ z ^ n = xi z) := by
  obtain ⟨R₀, hR₀, hne⟩ := xi_ne_zero_on_charts ρ₀
  refine ⟨R₀, hR₀, ?_⟩
  intro R hR hRle n hn
  obtain ⟨hneR, hneL⟩ := hne R hR hRle
  constructor
  · obtain ⟨χ, hχan, -, hχpow⟩ := U0KummerBranch.exists_analyticOnNhd_pow_eq
      (isOpen_chartR ρ₀ R) (isSimplyConnected_chartR ρ₀ hR) (xi_analyticOnNhd _) hneR hn.ne'
    exact ⟨χ, hχan, hχpow⟩
  · obtain ⟨χ, hχan, -, hχpow⟩ := U0KummerBranch.exists_analyticOnNhd_pow_eq
      (isOpen_chartL ρ₀ R) (isSimplyConnected_chartL ρ₀ hR) (xi_analyticOnNhd _) hneL hn.ne'
    exact ⟨χ, hχan, hχpow⟩

/-! ## Certificate ⟺ windowed deck triviality -/

/-- **Certificate ⟺ deck triviality across the window.**  The level-`k` height-`T` certificate
holds iff at every box-window zero there are arbitrarily small radii carrying chart roots of ξ at
level `2^k` with trivial deck class.  Root existence is unconditional (`xi_exists_chart_roots`),
so both directions have content: the certificate produces the trivial classes, and any family of
trivial classes forces the divisibilities.  The rung on a bounded box is a finite conjunction of
local monodromy conditions. -/
theorem windowCertificate_iff_deck_trivial (k : ℕ) (T : ℝ) :
    WindowCertificate k T ↔
      ∀ ρ ∈ boxZeros T, ∃ R₀ > 0, ∀ R : ℝ, 0 < R → R ≤ R₀ →
        ∃ G₁ G₂, AnalyticOnNhd ℂ G₁ (chartR ρ R) ∧ AnalyticOnNhd ℂ G₂ (chartL ρ R) ∧
          (∀ z ∈ chartR ρ R, G₁ z ^ 2 ^ k = xi z) ∧
          (∀ z ∈ chartL ρ R, G₂ z ^ 2 ^ k = xi z) ∧
          deckClass G₁ G₂ (ρ + ((R / 2 : ℝ) : ℂ) * I) (ρ - ((R / 2 : ℝ) : ℂ) * I) = 1 := by
  constructor
  · intro hc ρ hρ
    obtain ⟨R₁, hR₁, hroots⟩ := xi_exists_chart_roots ρ
    obtain ⟨R₂, hR₂, hclass⟩ := xi_deckClass_eq_one_iff_ladder_dvd ρ k
    refine ⟨min R₁ R₂, lt_min hR₁ hR₂, ?_⟩
    intro R hR hRle
    obtain ⟨⟨G₁, hG₁an, hG₁pow⟩, G₂, hG₂an, hG₂pow⟩ :=
      hroots R hR (le_trans hRle (min_le_left R₁ R₂)) (2 ^ k) (pow_pos two_pos k)
    refine ⟨G₁, G₂, hG₁an, hG₂an, hG₁pow, hG₂pow, ?_⟩
    exact (hclass hR (le_trans hRle (min_le_right R₁ R₂))
      hG₁an hG₂an hG₁pow hG₂pow).mpr (hc ρ hρ)
  · intro h ρ hρ
    obtain ⟨R₀, hR₀, hdata⟩ := h ρ hρ
    obtain ⟨R₂, hR₂, hclass⟩ := xi_deckClass_eq_one_iff_ladder_dvd ρ k
    have hRmin : 0 < min R₀ R₂ := lt_min hR₀ hR₂
    obtain ⟨G₁, G₂, hG₁an, hG₂an, hG₁pow, hG₂pow, hone⟩ :=
      hdata (min R₀ R₂) hRmin (min_le_left R₀ R₂)
    exact (hclass hRmin (min_le_right R₀ R₂) hG₁an hG₂an hG₁pow hG₂pow).mp hone

/-- Deck triviality across the window is equivalent to the full family of reflection-closed
subwindow congruences.  This ties the deck reading to the per-subconfiguration refinement that
the total window DISC sum cannot see. -/
theorem windowDeckTrivial_iff_subWindow_congruences (k : ℕ) (T : ℝ) :
    (∀ ρ ∈ boxZeros T, ∃ R₀ > 0, ∀ R : ℝ, 0 < R → R ≤ R₀ →
        ∃ G₁ G₂, AnalyticOnNhd ℂ G₁ (chartR ρ R) ∧ AnalyticOnNhd ℂ G₂ (chartL ρ R) ∧
          (∀ z ∈ chartR ρ R, G₁ z ^ 2 ^ k = xi z) ∧
          (∀ z ∈ chartL ρ R, G₂ z ^ 2 ^ k = xi z) ∧
          deckClass G₁ G₂ (ρ + ((R / 2 : ℝ) : ℂ) * I)
            (ρ - ((R / 2 : ℝ) : ℂ) * I) = 1) ↔
      ∀ t : Finset ℂ, ↑t ⊆ stripZeros T → (∀ z ∈ t, lineReflect z ∈ t) →
        (∑ ρ ∈ t, (analyticOrderAt xi ρ).toNat ≡
          ∑ ρ ∈ t.filter (fun ρ => ρ.re = 1 / 2),
            (analyticOrderAt xi ρ).toNat [MOD 2 ^ (k + 1)]) := by
  rw [← windowCertificate_iff_deck_trivial, windowCertificate_iff_subWindow_congruences]

/-- Rung `k` as windowed deck triviality at every height. -/
theorem rhLadder_iff_forall_deck_trivial (k : ℕ) :
    RHLadder k ↔
      ∀ T : ℝ, ∀ ρ ∈ boxZeros T, ∃ R₀ > 0, ∀ R : ℝ, 0 < R → R ≤ R₀ →
        ∃ G₁ G₂, AnalyticOnNhd ℂ G₁ (chartR ρ R) ∧ AnalyticOnNhd ℂ G₂ (chartL ρ R) ∧
          (∀ z ∈ chartR ρ R, G₁ z ^ 2 ^ k = xi z) ∧
          (∀ z ∈ chartL ρ R, G₂ z ^ 2 ^ k = xi z) ∧
          deckClass G₁ G₂ (ρ + ((R / 2 : ℝ) : ℂ) * I) (ρ - ((R / 2 : ℝ) : ℂ) * I) = 1 := by
  rw [rhLadder_iff_forall_windowCertificate]
  exact forall_congr' fun T => windowCertificate_iff_deck_trivial k T

/-- RH as the totality of windowed deck trivialities over all levels and heights. -/
theorem rh_iff_forall_deck_trivial :
    RiemannHypothesis ↔
      ∀ (k : ℕ) (T : ℝ), ∀ ρ ∈ boxZeros T, ∃ R₀ > 0, ∀ R : ℝ, 0 < R → R ≤ R₀ →
        ∃ G₁ G₂, AnalyticOnNhd ℂ G₁ (chartR ρ R) ∧ AnalyticOnNhd ℂ G₂ (chartL ρ R) ∧
          (∀ z ∈ chartR ρ R, G₁ z ^ 2 ^ k = xi z) ∧
          (∀ z ∈ chartL ρ R, G₂ z ^ 2 ^ k = xi z) ∧
          deckClass G₁ G₂ (ρ + ((R / 2 : ℝ) : ℂ) * I) (ρ - ((R / 2 : ℝ) : ℂ) * I) = 1 := by
  rw [rh_iff_forall_windowCertificate]
  exact forall₂_congr fun k T => windowCertificate_iff_deck_trivial k T

/-! ## Holography: under the certificate every boundary loop reads pure line data -/

/-- **The holography of the certificate.**  Under the height-`T` level-`k` certificate, the deck
class value at level `2^{k+1}` of any reflection-closed ξ-configuration from the strip window, enclosed
in a line-centered annular chart pair, equals `exp(2πi·L/2^{k+1})` where `L` is the on-line order
sum: the certificate kills the off-line contribution mod `2^{k+1}` (each box order is divisible by
`2^k` and off-line zeros enter doubled), so the boundary loop reads pure critical-line data. -/
theorem xi_deckClass_line_holography {k : ℕ} {T : ℝ} (hc : WindowCertificate k T)
    {t : Finset ℂ} {m : ℂ → ℕ} {h G₁ G₂ : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hsub : ↑t ⊆ stripZeros T)
    (hm : ∀ z ∈ t, (m z : ℕ∞) = analyticOrderAt xi z)
    (hclosed : ∀ z ∈ t, lineReflect z ∈ t)
    (hρ : ∀ z ∈ t, ‖z - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, xi z = (∏ w ∈ t, (z - w) ^ m w) * h z)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ 2 ^ (k + 1) = xi z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ 2 ^ (k + 1) = xi z) :
    deckClass G₁ G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)
      = exp (2 * (Real.pi : ℂ) * I *
          ((∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z : ℕ) : ℂ) / ((2 ^ (k + 1) : ℕ) : ℂ)) := by
  classical
  have hmrefl : ∀ z ∈ t, m (lineReflect z) = m z := by
    intro z hz
    have h1 : analyticOrderAt xi (lineReflect z) = analyticOrderAt xi z :=
      xi_orderAt_lineReflect z
    have h2 := hm _ (hclosed z hz)
    rw [h1, ← hm z hz] at h2
    exact Nat.cast_inj.mp h2
  have hID := window_identity hclosed hmrefl
  have hN : 2 ^ k ∣ ∑ z ∈ t.filter (fun z => 1 / 2 < z.re), m z := by
    refine Finset.dvd_sum ?_
    intro z hz
    rw [Finset.mem_filter] at hz
    have hbox : z ∈ boxZeros T := mem_boxZeros_of_stripZeros_right (hsub hz.1) hz.2
    have hdvd := hc z hbox
    rw [← hm z hz.1] at hdvd
    exact natCast_dvd_natCast_of_enat (pow_ne_zero k two_ne_zero) hdvd
  obtain ⟨c, hcN⟩ := hN
  have hcount := deckClass_multi_zero t (fun z => z) m h0 hrR
    (pow_pos two_pos (k + 1)) hρ hh hh0 hfact hG₁ hG₂ hpG₁ hpG₂
  rw [hcount]
  have hsumcast : (∑ z ∈ t, (m z : ℂ)) = ((∑ z ∈ t, m z : ℕ) : ℂ) := by
    push_cast
    ring
  have hDnat : ∑ z ∈ t, m z
      = (∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z) + 2 ^ (k + 1) * c := by
    rw [hID, hcN, pow_succ']
    ring
  rw [hsumcast, hDnat]
  have h2k : (((2 : ℕ) ^ (k + 1) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero (k + 1) (two_ne_zero)
  have hsplit : 2 * (Real.pi : ℂ) * I *
        (((∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z) + 2 ^ (k + 1) * c : ℕ) : ℂ)
        / ((2 ^ (k + 1) : ℕ) : ℂ)
      = 2 * (Real.pi : ℂ) * I *
          ((∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z : ℕ) : ℂ) / ((2 ^ (k + 1) : ℕ) : ℂ)
        + (c : ℂ) * (2 * (Real.pi : ℂ) * I) := by
    field_simp
    push_cast
    ring
  rw [hsplit, Complex.exp_add]
  have hexpc : Complex.exp ((c : ℂ) * (2 * (Real.pi : ℂ) * I)) = 1 := by
    rw [Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]
  rw [hexpc, mul_one]

end RHTower
