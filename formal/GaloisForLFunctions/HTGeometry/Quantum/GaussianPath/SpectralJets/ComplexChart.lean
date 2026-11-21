import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SimpleBranches
import GaloisForLFunctions.HTGeometry.RootPacketPowerSum
import GaloisForLFunctions.HTGeometry.SpectralDiscriminantPolynomial

/-! # Cleared determinants throughout a complex chart of simple spectra -/
open MvPolynomial Matrix Set Filter Metric Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
variable {n D : ℕ} {R : Type*} [CommRing R]

/-- A simple Hermitian specialization has a ball of distinct analytic roots on which
all characteristic root derivatives are nonzero. -/
theorem exists_simple_pencil_ball (A : Fin n → Matrix (Fin D) (Fin D) R)
    (φ : R →+* ℂ) (x : Fin n → ℂ) (hH : (∑ a, x a • (A a).map φ).IsHermitian)
    (hS : Function.Injective hH.eigenvalues) :
    ∃ r > 0, ∃ f : Fin D → (Fin n → ℂ) → ℂ,
      (∀ j, AnalyticOnNhd ℂ (f j) (ball x r)) ∧
      (∀ z ∈ ball x r, Function.Injective fun j => f j z) ∧
      (∀ z ∈ ball x r, ∀ j, matrixCharpolyRelation (∑ a, z a • (A a).map φ,f j z) = 0) ∧
      (∀ z ∈ ball x r, ∀ j, onRoot (pderiv none (map φ (characteristic A))) (f j) z ≠ 0) := by
  obtain ⟨f,hf,hn,_⟩ := simple_pencil_branch_detector A φ x hH hS
  have h₁ (j) : ∀ᶠ z in 𝓝 x, AnalyticAt ℂ (f j) z ∧
      matrixCharpolyRelation (∑ a, z a • (A a).map φ,f j z) = 0 ∧
      onRoot (pderiv none (map φ (characteristic A))) (f j) z ≠ 0 := by
    have hc : ContinuousAt (onRoot (pderiv none (map φ (characteristic A))) (f j)) x := by
      apply (contDiff_mvPolynomial_eval _).continuous.continuousAt.comp
      apply continuousAt_pi.mpr
      intro o
      cases o with
      | none => exact (hf j).1.continuousAt
      | some i => exact (continuous_apply i).continuousAt
    exact (hf j).1.eventually_analyticAt.and ((hf j).2.2.and (hc.eventually_ne (hn j)))
  have h₂ (i j : Fin D) : ∀ᶠ z in 𝓝 x, i ≠ j → f i z ≠ f j z := by
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => (h hij).elim
    have hne : f i x ≠ f j x := by rw [(hf i).2.1,(hf j).2.1]; exact fun h => hij (hS (Complex.ofReal_injective h))
    have h := ((hf i).1.continuousAt.sub (hf j).1.continuousAt).eventually_ne (sub_ne_zero.mpr hne)
    exact h.mono fun _ he _ => sub_ne_zero.mp he
  have hnear := (eventually_all.mpr h₁).and (eventually_all.mpr fun i => eventually_all.mpr (h₂ i))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨r,hr,f,fun j z hz => ((hball hz).1 j).1,?_,fun z hz j => ((hball hz).1 j).2.1,
    fun z hz j => ((hball hz).1 j).2.2⟩
  intro z hz i j hij
  by_contra h
  exact (hball hz).2 i j h hij

/-- A real specialization of the same pencil, with the complex generators named
separately from their integral representatives. -/
theorem exists_simple_real_pencil_ball (A : Fin n → Matrix (Fin D) (Fin D) R)
    (φ : R →+* ℂ) (P : Fin n → Matrix (Fin D) (Fin D) ℂ) (hm : (fun a => (A a).map φ) = P)
    (θ : Fin n → ℝ) (hH : (spectralEnsembleMatrix P θ).IsHermitian)
    (hs : Function.Injective hH.eigenvalues) :
    let x := fun i => (θ i : ℂ)
    ∃ r > 0, ∃ f : Fin D → (Fin n → ℂ) → ℂ,
      (∀ j, AnalyticOnNhd ℂ (f j) (ball x r)) ∧
      (∀ z ∈ ball x r, Function.Injective fun j => f j z) ∧
      (∀ z ∈ ball x r, ∀ j, matrixCharpolyRelation (∑ a, z a • P a,f j z) = 0) ∧
      (∀ z ∈ ball x r, ∀ j, onRoot (pderiv none (map φ (characteristic A))) (f j) z ≠ 0) := by
  subst P
  exact exists_simple_pencil_ball A φ _ hH hs

/-- The evaluation formula for a full root packet works at non-Hermitian as well
as Hermitian points in a complex chart. -/
theorem eval_jetGram_on_chart (A : Fin n → Matrix (Fin D) (Fin D) R) (φ : R →+* ℂ)
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (f : Fin D → (Fin n → ℂ) → ℂ)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) U) (hi : ∀ z ∈ U, Function.Injective fun j => f j z)
    (hroot : ∀ z ∈ U, ∀ j, matrixCharpolyRelation (∑ a, z a • (A a).map φ,f j z) = 0)
    (hs : ∀ z ∈ U, ∀ j, onRoot (pderiv none (map φ (characteristic A))) (f j) z ≠ 0)
    {x : Fin n → ℂ} (hx : x ∈ U) (L : ℕ) (rows : Fin D → Option (List (Fin n)))
    (hw : ∀ i v, v ∈ rows i → v.length ≤ L) :
    eval₂Hom φ x (jetGram A L rows) =
      ((Matrix.of fun i j => rowValue (rows i) (f j) x).det *
        ∏ j, (onRoot (pderiv none (map φ (characteristic A))) (f j) x)^(2*L))^2 := by
  let E (j : Fin D) := f j x
  have htr (k : ℕ) : eval₂Hom φ x ((pencil A)^k).trace = ∑ j, E j^k := by
    rw [← trace_mapMatrix,map_pow,eval_pencil]
    exact (sum_pow_rootPacket_eq_trace_pow _ E (hi x hx) (hroot x hx) k).symm
  rw [jetGram,eval_gram _ φ x E htr]
  let B := Matrix.of fun i j => rowValue (rows i) (f j) x
  let s (j : Fin D) := (onRoot (pderiv none (map φ (characteristic A))) (f j) x)^(2*L)
  have he : (Matrix.of fun i j => eval₂ φ (fun o : Option (Fin n) => o.elim (E j) x)
      (jetRow (characteristic A) L (rows i))) = B * Matrix.diagonal s := by
    ext i j
    rw [Matrix.mul_diagonal]
    change eval₂ φ _ _ = rowValue (rows i) (f j) x * s j
    rw [← eval_map,jetRow_map]
    apply row_eval _ L (rows i) (hw i) (f j) hU
      (fun z hz => (hf j z hz).differentiableAt.differentiableWithinAt) _ (fun z hz => hs z hz j) x hx
    intro z hz
    rw [onRoot,eval_map]
    exact (eval_characteristic A φ z (f j z)).trans (hroot z hz j)
  rw [he,Matrix.det_mul,Matrix.det_diagonal]

#print axioms exists_simple_pencil_ball
#print axioms eval_jetGram_on_chart
end
end GaloisForLFunctions.HTGeometry.SpectralJets
