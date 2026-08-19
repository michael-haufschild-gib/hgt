/-
# One endpoint-complete extension step

Attaching a qubit to an old system with a simple real spectrum and a Hermitian endpoint channel
that sees every ordered pair produces, at every sufficiently small nonzero coupling, a new system
which again has a simple real spectrum and whose canonical eigenvectors are pairwise visible from
the attached qubit.  The new endpoint channel is then read off from the new eigenvectors, so the
whole data set propagates.

Main results:
* `layerSplitMatrix`, `isHermitian_layerSplitMatrix` — the split Hamiltonian at a real coupling.
* `exists_layerSplitBranch` — analytic eigenvalue branches at zero coupling.
* `exists_layerSplit_endpointComplete_step` — **one complete extension step**.
-/
import GaloisForLFunctions.HTGeometry.LayerGermEndpointCompleteness
import GaloisForLFunctions.HTGeometry.HermitianCoveringProbe
import GaloisForLFunctions.HTGeometry.ExtensionStepQuadraticOrbit
import GaloisForLFunctions.HTGeometry.LayerSplitPhysicalRealization
import GaloisForLFunctions.HTGeometry.HermitianLocalSpectralObserverLaw
import GaloisForLFunctions.HTGeometry.GeneralParametricEigenbranch

open Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

omit [Fintype A] [DecidableEq A] in
/-- Scaling the attachment operator scales the cross perturbation. -/
theorem smul_layerCrossPerturbation (c : ℂ) (M : Matrix A A ℂ) :
    c • layerCrossPerturbation M = layerCrossPerturbation (c • M) := by
  refine Matrix.ext fun x y => ?_
  by_cases h : x.2 = y.2
  · simp [layerCrossPerturbation, h]
  · simp [layerCrossPerturbation, h]

/-- The split Hamiltonian at a real level shift and a real coupling. -/
def layerSplitMatrix (E : A → ℝ) (z t : ℝ) (M : Matrix A A ℂ) :
    Matrix (A × Bool) (A × Bool) ℂ :=
  Matrix.diagonal (layerSplitEnergy (fun a => ((E a : ℝ) : ℂ)) ((z : ℝ) : ℂ)) +
    ((t : ℝ) : ℂ) • layerCrossPerturbation M

/-- The split Hamiltonian is Hermitian. -/
theorem isHermitian_layerSplitMatrix (E : A → ℝ) (z t : ℝ) {M : Matrix A A ℂ}
    (hM : M.IsHermitian) : (layerSplitMatrix E z t M).IsHermitian := by
  rw [layerSplitMatrix, smul_layerCrossPerturbation]
  refine isHermitian_layerSplit (fun a => ?_) ?_ (hM.smul (Complex.conj_ofReal t))
  · exact Complex.conj_ofReal (E a)
  · exact Complex.conj_ofReal z

/-- The split family is analytic in the coupling. -/
theorem analyticAt_layerSplitFamily (E : A → ℂ) (z : ℂ) (M : Matrix A A ℂ) :
    AnalyticAt ℂ (fun g : ℂ => Matrix.diagonal (layerSplitEnergy E z) +
      g • layerCrossPerturbation M) 0 := by
  refine analyticAt_matrix_of_entries fun i j => ?_
  have hfun : (fun g : ℂ => (Matrix.diagonal (layerSplitEnergy E z) +
      g • layerCrossPerturbation M) i j)
      = fun g : ℂ => Matrix.diagonal (layerSplitEnergy E z) i j +
        g * layerCrossPerturbation M i j := by
    funext g
    simp [Matrix.add_apply]
  rw [hfun]
  exact analyticAt_const.add (analyticAt_id.mul analyticAt_const)

/-- **Analytic eigenvalue branches of the split family at zero coupling.** -/
theorem exists_layerSplitBranch {E : A → ℂ} {z : ℂ}
    (hinj : Function.Injective (layerSplitEnergy E z)) (M : Matrix A A ℂ) (x : A × Bool) :
    ∃ branch : ℂ → ℂ, AnalyticAt ℂ branch 0 ∧ branch 0 = layerSplitEnergy E z x ∧
      ∀ᶠ g in 𝓝 (0 : ℂ), matrixCharpolyRelation
        (Matrix.diagonal (layerSplitEnergy E z) + g • layerCrossPerturbation M, branch g) = 0 := by
  refine analyticMatrixFamily_eigenvalueBranch (analyticAt_layerSplitFamily E z M)
    (layerSplitEnergy E z) hinj ?_ x
  simp

omit [DecidableEq A] in
/-- A real level shift avoiding every ordered energy difference. -/
theorem exists_real_admissible_split_shift (E : A → ℝ) :
    ∃ z : ℝ, ∀ α β : A, ((z : ℝ) : ℂ) ≠ ((E β : ℝ) : ℂ) - ((E α : ℝ) : ℂ) := by
  have hfin : (Set.range fun p : A × A => E p.2 - E p.1).Finite := Set.finite_range _
  obtain ⟨z, hz⟩ := hfin.infinite_compl.nonempty
  refine ⟨z, fun α β hcon => hz ⟨(α, β), ?_⟩⟩
  have : ((z : ℝ) : ℂ) = ((E β - E α : ℝ) : ℂ) := by
    rw [hcon]; push_cast; ring
  exact (Complex.ofReal_injective this).symm

/-- The germ read coordinatewise. -/
theorem layerGerm_apply (E : A → ℂ) (z : ℂ) (M : Matrix A A ℂ) (branch : ℂ → ℂ)
    (x : A × Bool) (t : ℝ) (y : A × Bool) :
    layerGerm E z M branch x t y =
      affineEigenbranchAdjugateColumn (layerSplitEnergy E z) (layerCrossPerturbation M) branch x
        ((t : ℝ) : ℂ) y := rfl

/-- **One endpoint-complete extension step.**  From a simple real spectrum and a Hermitian
endpoint channel seeing every ordered pair, attaching one qubit at a suitable real level shift
and a suitable small nonzero real coupling produces a Hermitian system with a simple real
spectrum whose canonical eigenvectors are pairwise visible from the attached qubit. -/
theorem exists_layerSplit_endpointComplete_step
    {E : A → ℝ} (hE : Function.Injective E)
    {M : Matrix A A ℂ} (hMherm : M.IsHermitian) (hM : ∀ α β : A, α ≠ β → M β α ≠ 0) :
    ∃ (z t : ℝ) (E' : (A × Bool) → ℝ) (ψ : (A × Bool) → (A × Bool → ℂ)),
      t ≠ 0 ∧ Function.Injective E' ∧
      (layerSplitMatrix E z t M).IsHermitian ∧
      (∀ x, (layerSplitMatrix E z t M) *ᵥ (ψ x) = ((E' x : ℝ) : ℂ) • ψ x) ∧
      (∀ x, ψ x ≠ 0) ∧
      (∀ p : (A × Bool) × (A × Bool), p.1 ≠ p.2 →
        layerReducedTransition (ψ p.1) (ψ p.2) ≠ 0) := by
  classical
  obtain ⟨z, hz⟩ := exists_real_admissible_split_shift E
  have hEcInj : Function.Injective (fun a => ((E a : ℝ) : ℂ)) := by
    intro a b h
    exact hE (Complex.ofReal_injective h)
  have hinj : Function.Injective
      (layerSplitEnergy (fun a => ((E a : ℝ) : ℂ)) ((z : ℝ) : ℂ)) :=
    injective_layerSplitEnergy hEcInj hz
  choose branch hban hbase hroot using fun x => exists_layerSplitBranch hinj M x
  have hpull : ∀ P : ℂ → Prop, (∀ᶠ g in 𝓝 (0 : ℂ), P g) →
      ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), P ((s : ℝ) : ℂ) := by
    intro P h
    have hc : ContinuousAt (fun s : ℝ => ((s : ℝ) : ℂ)) 0 :=
      Complex.continuous_ofReal.continuousAt
    have h0 : ∀ᶠ g in 𝓝 ((fun s : ℝ => ((s : ℝ) : ℂ)) 0), P g := by simpa using h
    exact hc.eventually h0
  have hC1 := eventually_forall_layerGerm_endpoint_ne_zero hinj hM branch hban hbase hroot
  have hC3 : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), ∀ x : A × Bool, matrixCharpolyRelation
      (Matrix.diagonal (layerSplitEnergy (fun a => ((E a : ℝ) : ℂ)) ((z : ℝ) : ℂ)) +
        ((s : ℝ) : ℂ) • layerCrossPerturbation M, branch x ((s : ℝ) : ℂ)) = 0 :=
    Filter.eventually_all.mpr fun x => hpull _ (hroot x)
  have hC5 : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), ∀ x : A × Bool, ∀ i : A × Bool,
      (branch x ((s : ℝ) : ℂ) -
          layerSplitEnergy (fun a => ((E a : ℝ) : ℂ)) ((z : ℝ) : ℂ) i) *
        affineEigenbranchAdjugateColumn
          (layerSplitEnergy (fun a => ((E a : ℝ) : ℂ)) ((z : ℝ) : ℂ))
          (layerCrossPerturbation M) (branch x) x ((s : ℝ) : ℂ) i -
        ((s : ℝ) : ℂ) * ∑ j, layerCrossPerturbation M i j *
          affineEigenbranchAdjugateColumn
            (layerSplitEnergy (fun a => ((E a : ℝ) : ℂ)) ((z : ℝ) : ℂ))
            (layerCrossPerturbation M) (branch x) x ((s : ℝ) : ℂ) j = 0 :=
    Filter.eventually_all.mpr fun x => hpull _
      (affineEigenbranchAdjugateColumn_relation _ (layerCrossPerturbation M) (branch x) x
        (hroot x))
  have hC2 : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), ∀ p : (A × Bool) × (A × Bool), p.1 ≠ p.2 →
      branch p.1 ((s : ℝ) : ℂ) ≠ branch p.2 ((s : ℝ) : ℂ) := by
    refine Filter.eventually_all.mpr fun p => ?_
    by_cases hp : p.1 = p.2
    · exact Filter.Eventually.of_forall fun s hs => absurd hp hs
    · have hd : ContinuousAt (fun g : ℂ => branch p.1 g - branch p.2 g) 0 :=
        ((hban p.1).continuousAt).sub ((hban p.2).continuousAt)
      have hne0 : (fun g : ℂ => branch p.1 g - branch p.2 g) 0 ≠ 0 := by
        simp only [hbase]
        exact sub_ne_zero.mpr fun hc => hp (hinj hc)
      have hev := hpull _ (hd.eventually_ne hne0)
      filter_upwards [hev] with s hs _
      exact sub_ne_zero.mp hs
  have hC4 : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), ∀ x : A × Bool,
      layerGerm (fun a => ((E a : ℝ) : ℂ)) ((z : ℝ) : ℂ) M (branch x) x s x ≠ 0 := by
    refine Filter.eventually_all.mpr fun x => ?_
    have hcont : ContinuousAt (fun s : ℝ =>
        layerGerm (fun a => ((E a : ℝ) : ℂ)) ((z : ℝ) : ℂ) M (branch x) x s x) 0 :=
      (hasDerivAt_layerGerm (fun a => ((E a : ℝ) : ℂ)) ((z : ℝ) : ℂ) M x (hban x) x).continuousAt
    have hval : (fun s : ℝ =>
        layerGerm (fun a => ((E a : ℝ) : ℂ)) ((z : ℝ) : ℂ) M (branch x) x s x) 0 ≠ 0 := by
      simp only
      rw [layerGerm_zero _ _ M (hbase x) x, if_pos rfl]
      exact layerGapProduct_ne_zero hinj x
    exact hcont.eventually_ne hval
  obtain ⟨t, hone, htwo, hthree, hfour, hfive, htne⟩ :
      ∃ t : ℝ, (∀ p : (A × Bool) × (A × Bool), p.1 ≠ p.2 →
          layerReducedTransition
            (layerGerm (fun a => ((E a : ℝ) : ℂ)) ((z : ℝ) : ℂ) M (branch p.1) p.1 t)
            (layerGerm (fun a => ((E a : ℝ) : ℂ)) ((z : ℝ) : ℂ) M (branch p.2) p.2 t) ≠ 0) ∧
        (∀ p : (A × Bool) × (A × Bool), p.1 ≠ p.2 →
          branch p.1 ((t : ℝ) : ℂ) ≠ branch p.2 ((t : ℝ) : ℂ)) ∧
        (∀ x : A × Bool, matrixCharpolyRelation
          (Matrix.diagonal (layerSplitEnergy (fun a => ((E a : ℝ) : ℂ)) ((z : ℝ) : ℂ)) +
            ((t : ℝ) : ℂ) • layerCrossPerturbation M, branch x ((t : ℝ) : ℂ)) = 0) ∧
        (∀ x : A × Bool,
          layerGerm (fun a => ((E a : ℝ) : ℂ)) ((z : ℝ) : ℂ) M (branch x) x t x ≠ 0) ∧
        (∀ x : A × Bool, ∀ i : A × Bool,
          (branch x ((t : ℝ) : ℂ) -
              layerSplitEnergy (fun a => ((E a : ℝ) : ℂ)) ((z : ℝ) : ℂ) i) *
            affineEigenbranchAdjugateColumn
              (layerSplitEnergy (fun a => ((E a : ℝ) : ℂ)) ((z : ℝ) : ℂ))
              (layerCrossPerturbation M) (branch x) x ((t : ℝ) : ℂ) i -
            ((t : ℝ) : ℂ) * ∑ j, layerCrossPerturbation M i j *
              affineEigenbranchAdjugateColumn
                (layerSplitEnergy (fun a => ((E a : ℝ) : ℂ)) ((z : ℝ) : ℂ))
                (layerCrossPerturbation M) (branch x) x ((t : ℝ) : ℂ) j = 0) ∧ t ≠ 0 := by
    have hcomb := hC1.and ((hC2.and (hC3.and (hC4.and hC5))).filter_mono nhdsWithin_le_nhds)
    obtain ⟨t, ⟨h1, h2, h3, h4, h5⟩, hne⟩ := (hcomb.and self_mem_nhdsWithin).exists
    exact ⟨t, h1, h2, h3, h4, h5, hne⟩
  have hherm : (Matrix.diagonal (layerSplitEnergy (fun a => ((E a : ℝ) : ℂ)) ((z : ℝ) : ℂ)) +
      ((t : ℝ) : ℂ) • layerCrossPerturbation M).IsHermitian :=
    isHermitian_layerSplitMatrix E z t hMherm
  have hcast : ∀ x : A × Bool,
      (((branch x ((t : ℝ) : ℂ)).re : ℝ) : ℂ) = branch x ((t : ℝ) : ℂ) := by
    intro x
    have him : (branch x ((t : ℝ) : ℂ)).im = 0 :=
      matrixCharpolyRelation_im_eq_zero_of_isHermitian _ hherm _ (hthree x)
    apply Complex.ext <;> simp [him]
  refine ⟨z, t, fun x => (branch x ((t : ℝ) : ℂ)).re,
    fun x => layerGerm (fun a => ((E a : ℝ) : ℂ)) ((z : ℝ) : ℂ) M (branch x) x t,
    htne, ?_, isHermitian_layerSplitMatrix E z t hMherm, ?_, ?_, hone⟩
  · intro x y hxy
    by_contra hne
    refine htwo (x, y) hne ?_
    have hstep := congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) hxy
    simp only at hstep
    rwa [hcast x, hcast y] at hstep
  · intro x
    funext i
    have h5 := hfive x i
    have hsm : ((((t : ℝ) : ℂ) • layerCrossPerturbation M) *ᵥ
        (layerGerm (fun a => ((E a : ℝ) : ℂ)) ((z : ℝ) : ℂ) M (branch x) x t)) i
        = ((t : ℝ) : ℂ) * ∑ j, layerCrossPerturbation M i j *
            affineEigenbranchAdjugateColumn
              (layerSplitEnergy (fun a => ((E a : ℝ) : ℂ)) ((z : ℝ) : ℂ))
              (layerCrossPerturbation M) (branch x) x ((t : ℝ) : ℂ) j := by
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, layerGerm_apply]
    show ((layerSplitMatrix E z t M) *ᵥ
      (layerGerm (fun a => ((E a : ℝ) : ℂ)) ((z : ℝ) : ℂ) M (branch x) x t)) i = _
    rw [layerSplitMatrix, Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal, hsm,
      Pi.smul_apply, smul_eq_mul, hcast x]
    simp only [layerGerm_apply]
    linear_combination -h5
  · intro x hcon
    exact hfour x (by simpa using congrFun hcon x)

end

end GaloisForLFunctions.HTGeometry
