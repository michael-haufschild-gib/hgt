/-
# The root-limit modulus lemma (P3)

The analytic core of the connected-case root-limit route — the step that **bypasses branch
coherence**.  Suppose points `z_k → w` approach a frontier point `w` from a region where an assumed
relation `∑_{i∈s} a_i(z)·X^i` has a root `val_k = φ(z_k)` whose modulus tends to `1` (the Böttcher
modulus `e^{G(z_k)} → e^{G(w)} = 1` on the Julia set).  Then, with the coefficients `a_i` merely
continuous at `w`, the fibre polynomial at `w` has a root of modulus exactly `1`.

No single-valued branch of `φ` through `w` is used — only that each `z_k` supplies *some* root and
that the moduli converge.  Bolzano–Weierstrass extracts a convergent subsequence of the roots; the
limit inherits modulus `1` and, by continuity of the coefficients, annihilates the limiting fibre
polynomial.  Axiom-clean.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.MetricSpace.Bounded

open Set Topology Filter

namespace Bottcher

/-- **Root-limit modulus lemma.**  Let `z_k → w`, and for each `k` let `val_k` be a root of the
fibre polynomial `∑_{i∈s} a_i(z_k)·X^i` with `‖val_k‖ = M_k → 1`.  If every coefficient `a_i`
(`i ∈ s`) is continuous at `w`, then the limiting fibre polynomial `∑_{i∈s} a_i(w)·X^i` has a root
of modulus `1`. -/
theorem exists_modulus_one_root_of_root_limit {s : Finset ℕ} {a : ℕ → ℂ → ℂ} {w : ℂ}
    {z val : ℕ → ℂ} {M : ℕ → ℝ}
    (hz : Tendsto z atTop (𝓝 w))
    (hcont : ∀ i ∈ s, ContinuousAt (a i) w)
    (hroot : ∀ k, ∑ i ∈ s, a i (z k) * (val k) ^ i = 0)
    (hmod : ∀ k, ‖val k‖ = M k)
    (hM : Tendsto M atTop (𝓝 1)) :
    ∃ x : ℂ, ‖x‖ = 1 ∧ ∑ i ∈ s, a i w * x ^ i = 0 := by
  classical
  -- the roots are bounded: `‖val k‖ = M k` and `M` converges
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ k, ‖val k‖ ≤ C := by
    obtain ⟨C, hC⟩ := (hM.isBoundedUnder_le).bddAbove_range
    refine ⟨max C 1, fun k => ?_⟩
    rw [hmod k]
    exact le_trans (hC ⟨k, rfl⟩) (le_max_left _ _)
  have hmem : ∀ k, val k ∈ Metric.closedBall (0 : ℂ) C := by
    intro k; rw [Metric.mem_closedBall, dist_zero_right]; exact hC k
  -- Bolzano–Weierstrass: a convergent subsequence of roots
  obtain ⟨x, _hxcl, ψ, hψmono, hψlim⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_closedBall) hmem
  refine ⟨x, ?_, ?_⟩
  · -- modulus of the limit is `1`
    have h1 : Tendsto (fun j => ‖val (ψ j)‖) atTop (𝓝 ‖x‖) :=
      (continuous_norm.continuousAt).tendsto.comp hψlim
    have h2 : Tendsto (fun j => ‖val (ψ j)‖) atTop (𝓝 1) := by
      have : Tendsto (fun j => M (ψ j)) atTop (𝓝 1) := hM.comp hψmono.tendsto_atTop
      simpa [hmod] using this
    exact tendsto_nhds_unique h1 h2
  · -- the limit annihilates the limiting fibre polynomial
    have hzψ : Tendsto (fun j => z (ψ j)) atTop (𝓝 w) := hz.comp hψmono.tendsto_atTop
    have hterm : ∀ i ∈ s,
        Tendsto (fun j => a i (z (ψ j)) * (val (ψ j)) ^ i) atTop (𝓝 (a i w * x ^ i)) := by
      intro i _hi
      have hai : Tendsto (fun j => a i (z (ψ j))) atTop (𝓝 (a i w)) :=
        ((hcont i _hi).tendsto).comp hzψ
      have hpow : Tendsto (fun j => (val (ψ j)) ^ i) atTop (𝓝 (x ^ i)) :=
        (hψlim.pow i)
      exact hai.mul hpow
    have hsum : Tendsto (fun j => ∑ i ∈ s, a i (z (ψ j)) * (val (ψ j)) ^ i) atTop
        (𝓝 (∑ i ∈ s, a i w * x ^ i)) :=
      tendsto_finsetSum s hterm
    have hzero : Tendsto (fun j => ∑ i ∈ s, a i (z (ψ j)) * (val (ψ j)) ^ i) atTop (𝓝 0) := by
      simp only [hroot]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hsum hzero

end Bottcher
