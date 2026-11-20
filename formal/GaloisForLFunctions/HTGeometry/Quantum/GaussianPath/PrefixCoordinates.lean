import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathCoefficientMass
import GaloisForLFunctions.HTGeometry.PathChainLabelIdentification
import GaloisForLFunctions.HTGeometry.GaussianSignedPermutationInvariance

/-! # Numbered Gaussian coordinates of finite open-chain prefixes -/
open MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private def disorderIndex {n : ℕ} : PathLabel n → ℕ × PathPauliDirections
  | .inl (s,a) => (s.val,.inl a)
  | .inr (e,ab) => (e.val,.inr ab)

private theorem disorderIndex_injective (n : ℕ) : Function.Injective (disorderIndex (n := n)) := by
  intro l j h
  rcases l with ⟨a,b⟩ | ⟨a,b⟩ <;> rcases j with ⟨c,d⟩ | ⟨c,d⟩
  · have he := Prod.mk.inj h
    exact congrArg Sum.inl (Prod.ext (Fin.ext he.1) (Sum.inl.inj he.2))
  · exact nomatch congrArg Prod.snd h
  · exact nomatch congrArg Prod.snd h
  · have he := Prod.mk.inj h
    exact congrArg Sum.inr (Prod.ext (Fin.ext he.1) (Sum.inr.inj he.2))

/-- Numbering the coefficients of a finite prefix gives the product standard Gaussian law. -/
theorem gaussian_pauli_prefix_coordinates_law (n : ℕ) :
    MeasurePreserving (fun ω => fun i => pathPauliDisorderShell ω n (pathCoeffEquiv n i))
      pathPauliDisorderLaw (centredProductGaussian (Fin (Fintype.card (ChainLabel (n+2)))) 1) := by
  let f := (disorderIndex (n := n)) ∘ (pathCoeffEquiv n)
  have hf : Function.Injective f := (disorderIndex_injective n).comp (pathCoeffEquiv n).injective
  have hi := iIndepFun_infinitePi (P := fun _ : ℕ × PathPauliDirections => gaussianReal 0 1)
    (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id)
  have heval : MeasurePreserving (fun ω : PathPauliDisorder => fun i => ω (f i)) pathPauliDisorderLaw
      (centredProductGaussian (Fin (Fintype.card (ChainLabel (n+2)))) 1) := by
    refine ⟨measurable_pi_lambda _ (fun i => measurable_pi_apply _),?_⟩
    have h := (hi.precomp hf).map_fun_eq_pi_map (fun i => (measurable_pi_apply _).aemeasurable)
    change Measure.map (fun ω : PathPauliDisorder => fun i => ω (f i)) _ =
      Measure.pi (fun _ => gaussianReal 0 1)
    have hmap i : Measure.map (fun ω : PathPauliDisorder => ω (f i)) pathPauliDisorderLaw =
        gaussianReal 0 1 :=
      (measurePreserving_eval_infinitePi (fun _ : ℕ × PathPauliDirections => gaussianReal 0 1)
        (f i)).map_eq
    exact h.trans (congrArg (fun μ => Measure.pi μ) (funext hmap))
  convert heval using 1
  funext ω i
  change pathPauliDisorderShell ω n (pathCoeffEquiv n i) = ω (disorderIndex (pathCoeffEquiv n i))
  cases (pathCoeffEquiv n i) <;> rfl

#print axioms gaussian_pauli_prefix_coordinates_law
end
end GaloisForLFunctions.HTGeometry
