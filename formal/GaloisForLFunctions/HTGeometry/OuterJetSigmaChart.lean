import GaloisForLFunctions.HTGeometry.CayleyOuterJetChart
import GaloisForLFunctions.HTGeometry.JetObservationGenericity
import GaloisForLFunctions.HTGeometry.DiscreteJetObservationLocallySurjective
import GaloisForLFunctions.HTGeometry.CayleyOuterFamilyGauge

/-!
# The Cayley outer chart on a packet of several nodes

A packet indexed by pairs (node, jet order) is the product, over the nodes, of the packets at each
node.  Applying the Cayley outer chart at every node is therefore a finite product of maps each of
which carries neighbourhoods to neighbourhoods, so the whole chart does too.

This is the form in which the chart meets the jet packets of a Cauchy transform, which are indexed
exactly this way.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Currying a packet indexed by (node, order) pairs into a family of packets. -/
def sigmaCurryHomeomorph {ι : Type*} (m : ι → ℕ) :
    ((Σ i, Fin (m i + 1)) → ℂ) ≃ₜ (∀ i, Fin (m i + 1) → ℂ) where
  toFun y := fun i k => y ⟨i, k⟩
  invFun z := fun t => z t.1 t.2
  left_inv y := by
    funext t
    cases t
    rfl
  right_inv z := by
    funext i k
    rfl
  continuous_toFun := by
    refine continuous_pi fun i => continuous_pi fun k => ?_
    exact continuous_apply _
  continuous_invFun := by
    refine continuous_pi fun t => ?_
    exact (continuous_apply t.2).comp (continuous_apply t.1)

/-- The Cayley outer chart applied at every node of a packet. -/
def outerJetSigma {ι : Type*} (m : ι → ℕ) (y : (Σ i, Fin (m i + 1)) → ℂ) :
    (Σ i, Fin (m i + 1)) → ℂ :=
  fun t => chiJetPacket (m t.1) (fun k => y ⟨t.1, k⟩) t.2

/-- **The multi-node Cayley outer chart carries neighbourhoods to neighbourhoods.** -/
theorem outerJetSigma_image_mem_nhds {ι : Type*} [Fintype ι] {m : ι → ℕ}
    {y : (Σ i, Fin (m i + 1)) → ℂ} (hy : ∀ i, y ⟨i, 0⟩ + Complex.I ≠ 0)
    {N : Set ((Σ i, Fin (m i + 1)) → ℂ)} (hN : N ∈ nhds y) :
    outerJetSigma m '' N ∈ nhds (outerJetSigma m y) := by
  classical
  set e := sigmaCurryHomeomorph m with he
  have h1 : e '' N ∈ nhds (e y) := e.isOpenMap.image_mem_nhds hN
  have h2 : (fun z : ∀ i, Fin (m i + 1) → ℂ => fun i => chiJetPacket (m i) (z i)) '' (e '' N)
      ∈ nhds fun i => chiJetPacket (m i) (e y i) := by
    refine pi_image_mem_nhds (e y) (fun i M hM => ?_) h1
    exact chiJetPacket_image_mem_nhds (hy i) hM
  have h3 := e.symm.isOpenMap.image_mem_nhds h2
  have himg : e.symm '' ((fun z : ∀ i, Fin (m i + 1) → ℂ => fun i => chiJetPacket (m i) (z i)) ''
      (e '' N)) = outerJetSigma m '' N := by
    rw [← Set.image_comp, ← Set.image_comp]
    rfl
  have hval : e.symm (fun i => chiJetPacket (m i) (e y i)) = outerJetSigma m y := rfl
  rw [himg, hval] at h3
  exact h3

/-! ## The outer jet observation of the mass parameter -/

/-- **The outer jet packet is a locally surjective observation of the mass parameter.**  The Cauchy
jet packet already is, by mass controllability, and the Cayley outer chart carries neighbourhoods to
neighbourhoods because its zeroth entries never meet `-i` above the real axis. -/
theorem locallySurjective_outerJetObservation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℂ) (hnodesinj : Function.Injective nodes) (hupper : ∀ i, 0 < (nodes i).im)
    (m : ι → ℕ) (x : ℕ → ℝ) (hx : Function.Injective x) {ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n)
    (hε : Summable ε) :
    LocallySurjectiveObservation fun u : MassParameter =>
      outerJetSigma m
        (discreteJetPacket nodes (fun i => m i + 1) x fun n => ε n * Real.exp (u n)) := by
  intro u N hN
  have hbase := locallySurjective_discreteJetObservation nodes hnodesinj hupper
    (fun i => m i + 1) x hx hεpos hε u N hN
  haveI := isFiniteMeasure_countableWeightedDirac (x := x)
    (fun n => (mul_pos (hεpos n) (Real.exp_pos _)).le)
    (summable_expParameter (fun n => (hεpos n).le) hε u)
  have hy : ∀ i, discreteJetPacket nodes (fun i => m i + 1) x
      (fun n => ε n * Real.exp (u n)) ⟨i, 0⟩ + Complex.I ≠ 0 := by
    intro i
    have hzero : discreteJetPacket nodes (fun i => m i + 1) x
        (fun n => ε n * Real.exp (u n)) ⟨i, 0⟩
        = cauchyTransform (_root_.HTGeometry.countableWeightedDirac
            (fun n => ε n * Real.exp (u n)) x) (nodes i) := by
      simp [discreteJetPacket]
    rw [hzero]
    exact add_I_ne_zero_of_im_nonneg (im_cauchyTransform_nonneg _ (hupper i))
  have hstep := outerJetSigma_image_mem_nhds (m := m) hy hbase
  rwa [← Set.image_comp] at hstep

end

end GaloisForLFunctions.HTGeometry
