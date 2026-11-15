import GaloisForLFunctions.RepresentationLifting.Descent.SemilinearInvariantSpan
import Mathlib.Algebra.BigOperators.Field

/-!
# Trace-one averaging for semilinear actions

Artin independence makes the scalar orbit trace nonzero. Dividing an element
by its nonzero invariant trace produces trace one in every characteristic.
Weighted averaging then lifts invariant vectors through equivariant
surjections and makes every additive semilinear one-cocycle a coboundary.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open scoped BigOperators
variable (G L : Type*) [Group G] [Fintype G] [Field L]
  [MulSemiringAction G L] [FaithfulSMul G L]

omit [FaithfulSMul G L] in
theorem scalarOrbitTrace_fixed (a : L) (g : G) :
    g • (∑ h : G, h • a) = ∑ h : G, h • a := by
  rw [Finset.smul_sum]
  simp only [smul_smul]
  exact Fintype.sum_equiv (Equiv.mulLeft g)
    (fun h : G => (g * h) • a) (fun h : G => h • a) (fun _ => rfl)

/-- A faithful finite field action admits a scalar of orbit trace one. -/
theorem exists_scalarOrbitTrace_one : ∃ a : L, ∑ g : G, g • a = 1 := by
  classical
  have hn : ∃ b : L, (∑ g : G, g • b) ≠ 0 := by
    by_contra h
    push Not at h
    have hs : (∑ g : G, (1 : L) • (fun b : L => g • b)) = 0 := by
      ext b
      simpa only [Finset.sum_apply, Pi.smul_apply, one_smul, Pi.zero_apply] using h b
    have hz : (1 : L) = 0 :=
      (linearIndependent_iff'.mp (faithfulScalarAction_linearIndependent G L))
        Finset.univ (fun _ : G => (1 : L)) hs 1 (Finset.mem_univ 1)
    exact one_ne_zero hz
  obtain ⟨b, hb⟩ := hn
  refine ⟨b / (∑ h : G, h • b), ?_⟩
  have hdiv (g : G) : g • (b / (∑ h : G, h • b)) =
      (g • b) / (∑ h : G, h • b) := by
    change (MulSemiringAction.toRingHom G L g) (b / (∑ h : G, h • b)) = _
    rw [map_div₀]
    change (g • b) / (g • (∑ h : G, h • b)) = _
    rw [scalarOrbitTrace_fixed]
  simp only [hdiv, ← Finset.sum_div]
  exact div_self hb

variable (V W : Type*) [AddCommGroup V] [Module L V] [DistribMulAction G V]
  [SMulDistribClass G L V] [AddCommGroup W] [Module L W] [DistribMulAction G W]
  [SMulDistribClass G L W]

omit [SMulDistribClass G L W] in
/-- An invariant target vector has an invariant lift through every equivariant surjection. -/
theorem semilinear_surjective_fixed_lift (f : V →ₗ[L] W)
    (hf : Function.Surjective f) (he : ∀ (g : G) (v : V), f (g • v) = g • f v)
    (w : W) (hw : ∀ g : G, g • w = w) :
    ∃ v : V, (∀ g : G, g • v = v) ∧ f v = w := by
  obtain ⟨a, ha⟩ := exists_scalarOrbitTrace_one G L
  obtain ⟨v, hv⟩ := hf w
  refine ⟨∑ g : G, (g • a) • (g • v), weightedOrbitSum_fixed G L V a v, ?_⟩
  rw [map_sum]
  simp only [map_smul, he, hv, hw]
  rw [← Finset.sum_smul, ha, one_smul]

include L in
/-- Additive Hilbert 90 for every semilinear module, with an explicit weighted-sum coboundary. -/
theorem semilinear_oneCocycle_principal (c : G → V)
    (hc : ∀ g h, c (g * h) = c g + g • c h) :
    ∃ v : V, ∀ g : G, g • v - v = c g := by
  obtain ⟨a, ha⟩ := exists_scalarOrbitTrace_one G L
  let b : V := ∑ h : G, (h • a) • c h
  have hb (g : G) : g • b = b - c g := by
    have hc' (h : G) : g • c h = c (g * h) - c g := by
      rw [hc]
      abel
    have hs : (∑ h : G, ((g * h) • a) • c (g * h)) = b :=
      Fintype.sum_equiv (Equiv.mulLeft g)
        (fun h : G => ((g * h) • a) • c (g * h))
        (fun h : G => (h • a) • c h) (fun _ => rfl)
    have ht : (∑ h : G, (g * h) • a) = 1 :=
      (Fintype.sum_equiv (Equiv.mulLeft g)
        (fun h : G => (g * h) • a) (fun h : G => h • a) (fun _ => rfl)).trans ha
    change g • (∑ h : G, (h • a) • c h) = _
    rw [Finset.smul_sum]
    simp only [smul_distrib_smul, smul_smul, hc', smul_sub, Finset.sum_sub_distrib]
    rw [hs, ← Finset.sum_smul, ht, one_smul]
  refine ⟨-b, fun g => ?_⟩
  rw [smul_neg, hb]
  abel

end GaloisForLFunctions.RepresentationLifting
