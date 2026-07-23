import GaloisForLFunctions.HTGeometry.CofiniteTailHilbertReconstruction

/-!
# Cofinite Hilbert reconstruction for finite geometric families

A finite weighted geometric family has columns

`e ↦ weight i * node i ^ e`.

Its ordinary Vandermonde rank only detects distinct nodes and nonzero column weights. Cofinite
reconstruction is sharper: deleting the initial coordinates also forces every node to be nonzero.
This file packages that exact tail phase and feeds it directly into the universal cofinite Hilbert
reconstruction interface.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Finite family of weighted geometric sequences on the natural-number coordinate tail. -/
def finiteWeightedGeometricFamily
    {ι : Type*} (weight node : ι → ℂ) : ι → ℕ → ℂ :=
  fun i e => weight i * node i ^ e

/-- **Exact geometric tail classification.** A finite weighted geometric family remains
independent after every finite coordinate deletion exactly when its nodes are distinct, every
column weight is nonzero, and no node is zero. -/
theorem tailCoefficientIndependent_finiteWeightedGeometricFamily_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight node : ι → ℂ) :
    TailCoefficientIndependent (finiteWeightedGeometricFamily weight node) ↔
      Function.Injective node ∧
        (∀ i, weight i ≠ 0) ∧
        ∀ i, node i ≠ 0 := by
  constructor
  · intro htail
    have hli : LinearIndependent ℂ (finiteWeightedGeometricFamily weight node) :=
      htail.linearIndependent _
    have hweight : ∀ i, weight i ≠ 0 := by
      intro i hi
      apply hli.ne_zero i
      funext e
      simp [finiteWeightedGeometricFamily, hi]
    have hbare : LinearIndependent ℂ (fun i e => node i ^ e) := by
      let u : ι → ℂˣ := fun i => Units.mk0 (weight i) (hweight i)
      have hscaled := hli.units_smul (fun i => (u i)⁻¹)
      change LinearIndependent ℂ
        (fun i => (↑((u i)⁻¹) : ℂ) •
          finiteWeightedGeometricFamily weight node i) at hscaled
      rw [show
        (fun i => (↑((u i)⁻¹) : ℂ) •
          finiteWeightedGeometricFamily weight node i) =
          (fun i e => node i ^ e) by
        funext i e
        simp [finiteWeightedGeometricFamily, u, Pi.smul_apply,
          smul_eq_mul, hweight i]]
        at hscaled
      exact hscaled
    refine ⟨?_, hweight, ?_⟩
    · intro i j hij
      apply hbare.injective
      funext e
      change node i ^ e = node j ^ e
      rw [hij]
    · have hcompl := htail.linearIndependent_on_compl
          (finiteWeightedGeometricFamily weight node) ({0} : Set ℕ)
          (Set.finite_singleton 0)
      intro i hi
      apply hcompl.ne_zero i
      funext e
      have he : (e : ℕ) ≠ 0 := by
        simpa using e.property
      simp [finiteWeightedGeometricFamily, hi, he]
  · rintro ⟨hnode, hweight, hnode0⟩
    intro c hsupp
    obtain ⟨M, hM⟩ := hsupp.exists_le
    let K := M + 1
    let v : ι → ℂ := fun i => c i * weight i * node i ^ K
    have hvMoments : ∀ e : Fin (Fintype.card ι),
        ∑ i, v i * node i ^ (e : ℕ) = 0 := by
      intro e
      have houtside :
          K + (e : ℕ) ∉
            {k | ∑ i, c i *
              finiteWeightedGeometricFamily weight node i k ≠ 0} := by
        intro hmem
        have hle := hM _ hmem
        dsimp [K] at hle
        omega
      have hzero :
          ∑ i, c i *
            finiteWeightedGeometricFamily weight node i (K + (e : ℕ)) = 0 :=
        not_ne_iff.mp houtside
      simpa [finiteWeightedGeometricFamily, v, pow_add, mul_assoc] using hzero
    let eqv := Fintype.equivFin ι
    let nodeFin : Fin (Fintype.card ι) → ℂ := fun k => node (eqv.symm k)
    let vFin : Fin (Fintype.card ι) → ℂ := fun k => v (eqv.symm k)
    have hnodeFin : Function.Injective nodeFin :=
      hnode.comp eqv.symm.injective
    have hvFinMoments : ∀ e : Fin (Fintype.card ι),
        ∑ k, vFin k * nodeFin k ^ (e : ℕ) = 0 := by
      intro e
      calc
        ∑ k, vFin k * nodeFin k ^ (e : ℕ) =
            ∑ i, v i * node i ^ (e : ℕ) := by
          exact eqv.symm.sum_comp
            (fun i => v i * node i ^ (e : ℕ))
        _ = 0 := hvMoments e
    have hvFinZero : vFin = 0 :=
      Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hnodeFin hvFinMoments
    funext i
    have hvi : v i = 0 := by
      have hi := congrFun hvFinZero (eqv i)
      simpa [vFin, eqv] using hi
    have hfactor : weight i * node i ^ K ≠ 0 :=
      mul_ne_zero (hweight i) (pow_ne_zero _ (hnode0 i))
    apply (mul_eq_zero.mp ?_).resolve_right hfactor
    simpa [v, mul_assoc] using hvi

/-- **Universal cofinite geometric Hilbert phase.** Complete square recovery, strict evaluation
Gram geometry, and positive evaluation volume survive every finite coordinate deletion exactly
under the distinct/nonzero weighted-node conditions. -/
theorem cofiniteEvaluationHilbertReconstruction_finiteWeightedGeometricFamily_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight node : ι → ℂ) :
    CofiniteEvaluationHilbertReconstruction
        (finiteWeightedGeometricFamily weight node) ↔
      Function.Injective node ∧
        (∀ i, weight i ≠ 0) ∧
        ∀ i, node i ≠ 0 := by
  rw [cofiniteEvaluationHilbertReconstruction_iff_tailCoefficientIndependent,
    tailCoefficientIndependent_finiteWeightedGeometricFamily_iff]

end

end GaloisForLFunctions.HTGeometry
