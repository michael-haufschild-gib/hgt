/-
# The weak-cut delayed plateau without a gate-model hypothesis

The delayed-plateau theorem was stated relative to a gate alphabet with a uniform synthesis
certificate for the decoupled orbit.  The universal two-level synthesis cap supplies exactly such an
alphabet on any finite register, with cap twice the dimension, so the certificate is a theorem about
an explicit alphabet rather than a hypothesis.

Main results:
* `card_finiteQubitConfiguration_fin` — the register dimension.
* `exists_weakCut_delayed_plateau_synthesized` — **the delayed plateau with the alphabet built in**.
-/
import GaloisForLFunctions.HTGeometry.UniversalSynthesisCertificate
import GaloisForLFunctions.HTGeometry.WeakCutDelayedPlateau

open Finset MeasureTheory Matrix Filter Set Metric
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry

set_option linter.unusedSectionVars false

theorem card_finiteQubitConfiguration_fin (n : ℕ) :
    Fintype.card (FiniteQubitConfiguration (Fin n)) = 2 ^ n := by
  simp only [FiniteQubitConfiguration, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

set_option maxHeartbeats 1000000 in
/-- **The weak-cut delayed plateau, with the gate model supplied.**  For every tolerance there is a
finite alphabet and a reference state for which the split synthesis cap is twice the register
dimension, the cap survives the whole prescribed delay, the evolution is hard at every instant of
arbitrarily late windows, and the orbit returns arbitrarily close to the seed. -/
theorem exists_weakCut_delayed_plateau_synthesized (k : ℕ) {a b : ℕ} (hab : a + b = k + 3)
    {eta eps : ℝ} (heta : 0 < eta) (hmargin : eta < eps) (edge : Fin (k + 2))
    {L : ℝ} (hL : (eps - eta) / 3 ≤ L)
    {epsn epsw : ℝ} (hepsn : 0 ≤ epsn) (hgap : epsn < epsw) (hepsw : epsw < 1)
    {r : ℕ} (hr : 1 ≤ r)
    (hscale : 16 * (4 / ((Fintype.card (Fin a → Bool) : ℝ) * Fintype.card (Fin b → Bool)))
      / (1 - epsw ^ 2) ^ 2 ≤ 1 / (2 * r))
    {C : Type} [Fintype C] [Nonempty C]
    (Z : C → (FiniteQubitConfiguration (Fin (k + 3)) → ℂ))
    (hZ : ∀ κ, finiteComplexInner (Z κ) (Z κ) = 1)
    {M : ℝ} (hM : 1 < M) {s : ℕ} (hcardC : (Fintype.card C : ℝ) ≤ M ^ (s + 1))
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2)
    (W : ℝ)
    (hW : ((plateauGridCount W ((epsw - epsn) /
        Real.sqrt (Fintype.card (PathLabel (k + 1)))) : ℕ) : ℝ) *
      (2 : ℝ) ^ (-((r : ℝ) / 2)) < 1) :
    ∃ (Γ : Type)
      (act : Γ → EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (k + 3))) →
        EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (k + 3))))
      (chi : EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (k + 3))))
      (c : (MonLe (Fin a) 3 → ZMod 8) × (MonLe (Fin b) 3 → ZMod 8))
      (v : sphere (0 : PathShell (k + 1)) 1),
      (∀ t : ℝ, 0 ≤ t → t ≤ L →
        approxComplexity act chi eps (orbitState (pathHamiltonian (v : PathShell (k + 1)))
          (eucVec (cubicProductSeed k hab c)) t) ≤ 2 * 2 ^ (k + 3))
      ∧ (∀ A : ℝ, ∃ t₀, A < t₀ ∧ ∀ u ∈ Set.Icc t₀ (t₀ + W),
          u ∉ metricEasySet (pathHamiltonian (v : PathShell (k + 1)))
            (cubicProductSeed k hab c) epsn Z)
      ∧ (∀ ρ : ℝ, 0 < ρ → ∀ A : ℝ, ∃ s' : ℝ, A < s' ∧ 1 - ρ ≤ ‖finiteComplexInner
          (unitaryEvolution (pathHamiltonian (v : PathShell (k + 1))) s' *ᵥ
            cubicProductSeed k hab c) (cubicProductSeed k hab c)‖) := by
  classical
  obtain ⟨Γ, act, chi, hcertUniv⟩ :=
    exists_orbit_synthesis_certificate (FiniteQubitConfiguration (Fin (k + 3))) heta
  have hcard := card_finiteQubitConfiguration_fin (k + 3)
  have hcert : ∀ c : (MonLe (Fin a) 3 → ZMod 8) × (MonLe (Fin b) 3 → ZMod 8),
      ∀ u : PathShell (k + 1), ∀ s' : ℝ, ∃ w : List Γ, w.length ≤ 2 * 2 ^ (k + 3) ∧
        dist (orbitState (pathHamiltonianCut u edge) (eucVec (cubicProductSeed k hab c)) s')
          (wordAct act w chi) ≤ eta := by
    intro c u s'
    obtain ⟨w, hwlen, hwdist⟩ := hcertUniv (pathHamiltonianCut u edge)
      (isSelfAdjoint_pathHamiltonianCut u edge) (eucVec (cubicProductSeed k hab c))
      (norm_eucVec_eq_one (finiteComplexInner_cubicProductSeed k hab c)) s'
    exact ⟨w, by rw [← hcard]; exact hwlen, hwdist⟩
  obtain ⟨c, v, h1, h2, h3⟩ := exists_weakCut_delayed_plateau k hab act chi hmargin edge hcert
    hL hepsn hgap hepsw hr hscale Z hZ hM hcardC hs W hW
  exact ⟨Γ, act, chi, c, v, h1, h2, h3⟩

end GaloisForLFunctions.HTGeometry

end
