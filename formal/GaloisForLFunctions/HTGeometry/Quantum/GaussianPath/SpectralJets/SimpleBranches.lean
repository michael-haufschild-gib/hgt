import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.LinearPencil
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BranchEvaluation
import GaloisForLFunctions.HTGeometry.RealParameterEndpointIntersection
import GaloisForLFunctions.HTGeometry.HermitianInertia

/-! # Analytic branches and polynomial derivative rows at a simple Hermitian spectrum -/
open MvPolynomial Matrix Set Filter Topology
open scoped Matrix.Norms.Elementwise
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
variable {n D : ℕ} {R : Type*} [CommRing R]

private theorem spectral_partial (p : MvPolynomial (Option (Fin n)) ℂ) (x : Fin n → ℂ) (y : ℂ) :
    HasDerivAt (fun u => eval (fun o : Option (Fin n) => o.elim u x) p)
      (eval (fun o : Option (Fin n) => o.elim y x) (pderiv none p)) y := by
  let v (u : ℂ) (o : Option (Fin n)) := o.elim u x
  let d (o : Option (Fin n)) : ℂ := o.elim 1 (fun _ => 0)
  have hv : HasDerivAt v d y := by
    apply hasDerivAt_pi.mpr
    intro o
    cases o with
    | none => exact hasDerivAt_id _
    | some i => exact hasDerivAt_const _ _
  simpa [v,d,Fintype.sum_option] using hasDerivAt_mvPolynomial_eval_comp p hv

/-- The entries in a row of the ordinary (uncleared) determinant. -/
def rowValue (w : Option (List (Fin n))) (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℂ) : ℂ :=
  w.elim 1 (fun v => mixed v f x)

theorem row_eval (p : MvPolynomial (Option (Fin n)) ℂ) (L : ℕ)
    (w : Option (List (Fin n))) (hw : ∀ v ∈ w, v.length ≤ L)
    (f : (Fin n → ℂ) → ℂ) {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hz : ∀ x ∈ U, onRoot p f x = 0)
    (hs : ∀ x ∈ U, onRoot (pderiv none p) f x ≠ 0) (x : Fin n → ℂ) (hx : x ∈ U) :
    onRoot (jetRow p L w) f x = rowValue w f x * (onRoot (pderiv none p) f x)^(2*L) := by
  cases w with
  | none => simp [jetRow,onRoot,rowValue]
  | some w =>
    have h := onRoot_numerator p f hU hd hz hs w x hx
    change _ = mixed w f x * _
    have hL : 2*L = 2*(L-w.length)+2*w.length := by
      rw [← Nat.mul_add,Nat.sub_add_cancel (hw w rfl)]
    simp only [onRoot] at h ⊢
    rw [jetRow,cleared,map_mul,map_pow,h,hL,pow_add]
    ring

/-- At any simple Hermitian specialization the integral detector evaluates
to the squared mixed-derivative determinant times the common column factors.
The same local eigenbranches work for every order and every row choice. -/
theorem simple_pencil_branch_detector (A : Fin n → Matrix (Fin D) (Fin D) R)
    (φ : R →+* ℂ) (x : Fin n → ℂ)
    (hH : (∑ a, x a • (A a).map φ).IsHermitian) (hsimple : Function.Injective hH.eigenvalues) :
    let H := fun z : Fin n → ℂ => ∑ a, z a • (A a).map φ
    let p := map φ (characteristic A)
    ∃ f : Fin D → (Fin n → ℂ) → ℂ,
      (∀ j, AnalyticAt ℂ (f j) x ∧ f j x = (hH.eigenvalues j : ℂ) ∧
        ∀ᶠ z in 𝓝 x, matrixCharpolyRelation (H z,f j z) = 0) ∧
      (∀ j, onRoot (pderiv none p) (f j) x ≠ 0) ∧
      ∀ (L : ℕ) (rows : Fin D → Option (List (Fin n))),
        (∀ j v, v ∈ rows j → v.length ≤ L) →
        eval₂Hom φ x (jetGram A L rows) =
          ((Matrix.of fun i j => rowValue (rows i) (f j) x).det *
            ∏ j, (onRoot (pderiv none p) (f j) x)^(2*L))^2 := by
  classical
  intro H p
  let E (j : Fin D) := (hH.eigenvalues j : ℂ)
  have hinj : Function.Injective E := Complex.ofReal_injective.comp hsimple
  let V : Matrix (Fin D) (Fin D) ℂ := hH.eigenvectorUnitary
  have hu : Vᴴ*V=1 := (Unitary.mem_iff.mp hH.eigenvectorUnitary.2).1
  have hd : Vᴴ * H x * V = Matrix.diagonal E := conjTranspose_mul_mul_eigenvectorUnitary hH
  choose f hfa hfE hfz using exists_analyticBranches_linearFamily (fun a => (A a).map φ) x hu E hinj hd
  have hchar (z : Fin n → ℂ) (y : ℂ) : eval (fun o : Option (Fin n) => o.elim y z) p =
      matrixCharpolyRelation (H z,y) := by
    rw [show p = map φ (characteristic A) from rfl,eval_map]
    exact eval_characteristic A φ z y
  have hsep (j : Fin D) : onRoot (pderiv none p) (f j) x ≠ 0 := by
    have hp := spectral_partial p x (f j x)
    have hpoly : (fun y => eval (fun o : Option (Fin n) => o.elim y x) p) =
        fun y => (H x).charpoly.eval y := by
      funext y
      exact (hchar x y).trans (Matrix.eval_charpoly (H x) y).symm
    rw [hpoly] at hp
    have he := hp.unique (Polynomial.hasDerivAt (H x).charpoly (f j x))
    have hseparable : (H x).charpoly.Separable := by
      rw [hH.charpoly_eq]
      exact Polynomial.separable_prod_X_sub_C_iff.mpr hinj
    have hz : (H x).charpoly.eval (f j x) = 0 := by
      rw [hfE j,hH.charpoly_eq,Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [E])
    unfold onRoot
    rw [he]
    simpa using hseparable.eval₂_derivative_ne_zero (RingHom.id ℂ) (by simpa using hz)
  refine ⟨f,fun j => ⟨hfa j,hfE j,hfz j⟩,hsep,?_⟩
  intro L rows hw
  have htr (k : ℕ) : eval₂Hom φ x ((pencil A)^k).trace = ∑ j, E j^k := by
    rw [← trace_mapMatrix,map_pow,eval_pencil]
    exact trace_pow_eq_sum_eigenvalues_pow hH k
  rw [jetGram,eval_gram _ φ x E htr]
  let B := Matrix.of fun i j => rowValue (rows i) (f j) x
  let s (j : Fin D) := (onRoot (pderiv none p) (f j) x)^(2*L)
  have he : (Matrix.of fun i j => eval₂ φ (fun o : Option (Fin n) => o.elim (E j) x)
      (jetRow (characteristic A) L (rows i))) = B * Matrix.diagonal s := by
    ext i j
    rw [Matrix.mul_diagonal]
    change eval₂ φ _ _ = rowValue (rows i) (f j) x * s j
    rw [← hfE j,← eval_map,jetRow_map]
    have hroot : ∀ᶠ z in 𝓝 x, onRoot p (f j) z = 0 := by
      filter_upwards [hfz j] with z hz
      exact (hchar z (f j z)).trans hz
    have hc : ContinuousAt (onRoot (pderiv none p) (f j)) x := by
      apply (contDiff_mvPolynomial_eval _).continuous.continuousAt.comp
      apply continuousAt_pi.mpr
      intro o
      cases o with
      | none => exact (hfa j).continuousAt
      | some a => exact (continuous_apply a).continuousAt
    have hnonzero := hc.eventually_ne (hsep j)
    obtain ⟨U,hU,hUopen,hx⟩ := mem_nhds_iff.mp
      (((hfa j).eventually_analyticAt.and hroot).and hnonzero)
    exact row_eval p L (rows i) (hw i) (f j) hUopen
      (fun y hy => (hU hy).1.1.differentiableAt.differentiableWithinAt)
      (fun y hy => (hU hy).1.2) (fun y hy => (hU hy).2) x hx
  rw [he,Matrix.det_mul,Matrix.det_diagonal]

#print axioms simple_pencil_branch_detector
end
end GaloisForLFunctions.HTGeometry.SpectralJets
