/-
# Convergence of the fixed-point iteration (Theorem 2.2)

A nonexpansive, quasi-α-firmly nonexpansive self-map of a *proper* metric space with a fixed
point has convergent Picard iterates.  Finite-dimensional Hadamard manifolds are proper, so
this covers the statement of the source; no curvature hypothesis is used in the proof.

The argument is the standard three-step one: Fejér monotonicity gives asymptotic regularity
`d(T x_n, x_n) → 0` from the quasi-firm inequality alone; properness produces a cluster point;
asymptotic regularity plus nonexpansiveness makes it a fixed point; Fejér monotonicity upgrades
subsequential to full convergence.
-/
import GaloisForLFunctions.HTGeometry.HadamardLipschitz.QuasiFirm
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace GaloisForLFunctions.HTGeometry.HadamardLipschitz

open Filter Topology

variable {X : Type*} [MetricSpace X]

/-- **Theorem 2.2.**  On a proper metric space, the Picard iterates of a nonexpansive map
satisfying the quasi-firm inequality at a fixed point `p` converge to a fixed point of `T`. -/
theorem tendsto_iterate_of_quasiFirmAt [ProperSpace X] (T : X → X)
    (hne : ∀ x y : X, dist (T x) (T y) ≤ dist x y) (p : X) (_hp : T p = p) {ξ : ℝ} (hξ : 0 < ξ)
    (hqf : QuasiFirmAt T p ξ) (x₀ : X) :
    ∃ q : X, T q = q ∧ Tendsto (fun n => T^[n] x₀) atTop (𝓝 q) := by
  set u : ℕ → X := fun n => T^[n] x₀ with hu
  have hsucc : ∀ n, u (n + 1) = T (u n) := by
    intro n; simp [hu, Function.iterate_succ_apply']
  set a : ℕ → ℝ := fun n => dist (u n) p ^ 2 with ha
  set e : ℕ → ℝ := fun n => dist (u (n + 1)) (u n) with he
  have hastep : ∀ n, a (n + 1) ≤ a n - ξ * e n ^ 2 := by
    intro n
    have := hqf (u n)
    simpa [ha, he, hsucc n] using this
  have hanonneg : ∀ n, 0 ≤ a n := fun n => by positivity
  have haanti : Antitone a := by
    refine antitone_nat_of_succ_le fun n => ?_
    nlinarith [hastep n, sq_nonneg (e n), hξ]
  have habdd : BddBelow (Set.range a) := ⟨0, by rintro _ ⟨n, rfl⟩; exact hanonneg n⟩
  have hatend : Tendsto a atTop (𝓝 (⨅ n, a n)) := tendsto_atTop_ciInf haanti habdd
  have hdiff : Tendsto (fun n => (a n - a (n + 1)) / ξ) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => a (n + 1)) atTop (𝓝 (⨅ n, a n)) :=
      hatend.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n => a n - a (n + 1)) atTop (𝓝 0) := by
      simpa using hatend.sub h1
    simpa using h2.div_const ξ
  have hesq : Tendsto (fun n => e n ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => sq_nonneg _) (fun n => ?_) hdiff
    rw [le_div_iff₀ hξ]
    nlinarith [hastep n]
  have hetend : Tendsto e atTop (𝓝 0) := by
    have hc : Tendsto (fun n => Real.sqrt (e n ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp hesq
    rw [Real.sqrt_zero] at hc
    refine hc.congr fun n => ?_
    exact Real.sqrt_sq dist_nonneg
  -- boundedness of the orbit
  have hball : ∀ n, u n ∈ Metric.closedBall p (dist (u 0) p) := by
    intro n
    have h1 : a n ≤ a 0 := haanti (Nat.zero_le n)
    have h2 : 0 ≤ dist (u n) p := dist_nonneg
    have h3 : 0 ≤ dist (u 0) p := dist_nonneg
    simp only [Metric.mem_closedBall]
    nlinarith [h1, h2, h3]
  obtain ⟨q, -, φ, hφ, hφtend⟩ :=
    (isCompact_closedBall p (dist (u 0) p)).tendsto_subseq hball
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  -- `q` is a fixed point
  have hfix : T q = q := by
    have hmaj : ∀ k, dist (T q) q ≤ 2 * dist (u (φ k)) q + e (φ k) := by
      intro k
      calc dist (T q) q ≤ dist (T q) (T (u (φ k))) + dist (T (u (φ k))) q :=
            dist_triangle _ _ _
        _ ≤ dist q (u (φ k)) + (dist (T (u (φ k))) (u (φ k)) + dist (u (φ k)) q) := by
            gcongr
            · exact hne q (u (φ k))
            · exact dist_triangle _ _ _
        _ = 2 * dist (u (φ k)) q + e (φ k) := by
            rw [dist_comm q (u (φ k)), he]
            simp only [← hsucc (φ k)]
            ring
    have hlim : Tendsto (fun k => 2 * dist (u (φ k)) q + e (φ k)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k => dist (u (φ k)) q) atTop (𝓝 0) :=
        tendsto_iff_dist_tendsto_zero.mp hφtend
      have h2 : Tendsto (fun k => e (φ k)) atTop (𝓝 0) := hetend.comp hφtop
      simpa using (h1.const_mul 2).add h2
    have : dist (T q) q ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hmaj)
    exact dist_le_zero.mp this
  -- upgrade to convergence of the whole sequence
  refine ⟨q, hfix, ?_⟩
  have hanti' : Antitone fun n => dist (u n) q := by
    refine antitone_nat_of_succ_le fun n => ?_
    rw [hsucc n]
    have := hne (u n) q
    rwa [hfix] at this
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendsto_atTop] at hφtend
  obtain ⟨K, hK⟩ := hφtend ε hε
  refine ⟨φ K, fun n hn => ?_⟩
  exact lt_of_le_of_lt (hanti' hn) (hK K le_rfl)

/-- **Theorem 2.2**, phrased with `QuasiFirmlyNonexpansive`. -/
theorem tendsto_iterate_of_quasiFirmlyNonexpansive [ProperSpace X] (T : X → X)
    (hne : ∀ x y : X, dist (T x) (T y) ≤ dist x y) {α : ℝ}
    (hT : QuasiFirmlyNonexpansive T α) (x₀ : X) :
    ∃ q : X, T q = q ∧ Tendsto (fun n => T^[n] x₀) atTop (𝓝 q) := by
  obtain ⟨p, hp⟩ := hT.exists_fixed
  exact tendsto_iterate_of_quasiFirmAt T hne p hp
    (quasiFirmCoeff α hT.alpha_pos hT.alpha_lt_one) (hT.firm p hp) x₀

end GaloisForLFunctions.HTGeometry.HadamardLipschitz
