import GaloisForLFunctions.HTGeometry.FactorialFockInfiniteRadius
import GaloisForLFunctions.RHTower.ExplicitPoleNoExtension

/-!
# Simple poles force factorial Fock jet divergence

The general factorial-Fock law says that a cofinally bounded raw jet has an entire germ extension.
The `NoExtensionAt` infrastructure says that a genuine boundary pole cannot admit such an extension.
Analytic uniqueness on the punctured complex plane joins the two: the finite raw-jet factorial
energies of a simple reciprocal pole are unbounded at every regular base point.

This is the concrete parent-theory model for Gamma-clock pole criteria.  It does not construct the
time-one prime seam or its arithmetic pole.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- The reciprocal simple pole is analytic throughout its punctured plane. -/
theorem analyticOnNhd_simplePoleAt_compl_singleton (b : ℂ) :
    AnalyticOnNhd ℂ (simplePoleAt b) ({b}ᶜ : Set ℂ) := by
  intro z hz
  have hne : z - b ≠ 0 := sub_ne_zero.mpr (by simpa using hz)
  rw [show simplePoleAt b =
    (fun _ : ℂ => 1) / (id - fun _ : ℂ => b) by rfl]
  exact analyticAt_const.div (analyticAt_id.sub analyticAt_const) hne

/-- Multiplying the reciprocal pole by its nonvanishing exponential partner preserves analyticity
on the punctured plane. -/
theorem analyticOnNhd_expOverSimplePole_compl_singleton (b : ℂ) :
    AnalyticOnNhd ℂ (expOverSimplePole b) ({b}ᶜ : Set ℂ) := by
  intro z hz
  exact (analyticOnNhd_simplePoleAt_compl_singleton b z hz).mul analyticAt_id.cexp

/-- A simple pole admits no entire function agreeing with its germ at any regular base point. -/
theorem simplePoleAt_no_entire_germ_extension_of_ne
    {a b : ℂ} (hab : a ≠ b) :
    ¬ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g Set.univ ∧
      Filter.EventuallyEq (nhds a) (simplePoleAt b) g := by
  apply no_entire_germ_extension_of_noExtensionAt
    (analyticOnNhd_simplePoleAt_compl_singleton b)
  · exact (isConnected_compl_singleton_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num) b).isPreconnected
  · simpa using hab
  · exact simplePoleAt_noExtensionAt b

/-- The exponential partner cannot turn the reciprocal pole germ into an entire germ. -/
theorem expOverSimplePole_no_entire_germ_extension_of_ne
    {a b : ℂ} (hab : a ≠ b) :
    ¬ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g Set.univ ∧
      Filter.EventuallyEq (nhds a) (expOverSimplePole b) g := by
  apply no_entire_germ_extension_of_noExtensionAt
    (analyticOnNhd_expOverSimplePole_compl_singleton b)
  · exact (isConnected_compl_singleton_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num) b).isPreconnected
  · simpa using hab
  · exact expOverSimplePole_noExtensionAt b

/-- **Boundary obstruction/factorial-Fock law.**  If an analytic function on a preconnected
continuation domain has a `NoExtensionAt` boundary point, then its finite raw-jet factorial
energies are unbounded at every point of the domain.  This subsumes the concrete pole law below
and turns the boundary Prop directly into a cofinal clock conclusion. -/
theorem exists_rawJetFactorialFockPartialEnergy_gt_of_noExtensionAt
    {Φ : ℂ → ℂ} {Ω : Set ℂ} {a b : ℂ}
    (hΦ : AnalyticOnNhd ℂ Φ Ω) (hΩ : IsPreconnected Ω)
    (ha : a ∈ Ω) (hno : NoExtensionAt Φ Ω b) (C : ℝ) :
    ∃ N, C < ∑ n ∈ Finset.range N,
      ‖iteratedDeriv n Φ a‖ ^ (2 : ℕ) / n.factorial := by
  exact
    GaloisForLFunctions.HTGeometry.exists_rawJetFactorialFockPartialEnergy_gt_of_no_entire_extension
      (hΦ a ha) (no_entire_germ_extension_of_noExtensionAt hΦ hΩ ha hno) C

/-- **Simple-pole factorial-Fock divergence.**  At every point away from its pole, the finite
factorial raw-jet energies of `1 / (z - b)` exceed every proposed bound. -/
theorem exists_simplePoleAt_rawJetFactorialFockPartialEnergy_gt
    {a b : ℂ} (hab : a ≠ b) (C : ℝ) :
    ∃ N, C < ∑ n ∈ Finset.range N,
      ‖iteratedDeriv n (simplePoleAt b) a‖ ^ (2 : ℕ) / n.factorial := by
  apply exists_rawJetFactorialFockPartialEnergy_gt_of_noExtensionAt
    (analyticOnNhd_simplePoleAt_compl_singleton b)
  · exact (isConnected_compl_singleton_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num) b).isPreconnected
  · simpa using hab
  · exact simplePoleAt_noExtensionAt b

/-- **No-healing factorial-Fock divergence.**  Multiplication by the nonvanishing entire
exponential column does not restore bounded factorial raw-jet energy to a reciprocal pole. -/
theorem exists_expOverSimplePole_rawJetFactorialFockPartialEnergy_gt
    {a b : ℂ} (hab : a ≠ b) (C : ℝ) :
    ∃ N, C < ∑ n ∈ Finset.range N,
      ‖iteratedDeriv n (expOverSimplePole b) a‖ ^ (2 : ℕ) / n.factorial := by
  apply exists_rawJetFactorialFockPartialEnergy_gt_of_noExtensionAt
    (analyticOnNhd_expOverSimplePole_compl_singleton b)
  · exact (isConnected_compl_singleton_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num) b).isPreconnected
  · simpa using hab
  · exact expOverSimplePole_noExtensionAt b

end


end RHTower
