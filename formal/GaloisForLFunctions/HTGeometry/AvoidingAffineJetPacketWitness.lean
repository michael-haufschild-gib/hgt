import GaloisForLFunctions.HTGeometry.AffineFramePacketAvoidance
import GaloisForLFunctions.HTGeometry.AffineJetPacketWitness

/-!
# Escaping witnesses whose packet nodes avoid prescribed values

The witness base of a finite decorated pattern can be chosen to separate the packet *and* to keep
every packet node outside a prescribed finite set of values.  This is what a source that vanishes to
a fixed order at a distinguished point needs: its jet packets are nondegenerate only away from that
point.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-- **Every finite decorated pattern has a separated escaping witness whose packet avoids a
prescribed finite set of node values.** -/
theorem exists_separatedWitness_avoiding {d : ℕ} (hd : 0 < d) {Λ : Type*}
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (hframe : Function.Injective frame)
    (p : FiniteMultivariateAffineJetPattern Λ d) (Cav : Finset (Fin d → ℂ)) :
    ∃ w : SeparatedMultivariateAffinePatternWitness frame p,
      ∀ q : MultivariateAffinePatternRow p × Fin p.frameCount,
        frame (p.frameCode q.2) (w.base q.1) ∉ Cav := by
  classical
  let ε : Fin p.frameCount → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ)) := fun i => frame (p.frameCode i)
  have hε : Function.Injective fun i => ((ε i : (Fin d → ℂ) → Fin d → ℂ)) := by
    intro i j hij
    exact p.frameCode_injective (hframe (DFunLike.coe_injective hij))
  have hW : multivariateFullPatternDeterminant p.coordinateExponent p.jetExponent ≠ 0 :=
    multivariateFullPatternDeterminant_ne_zero _ _ p.decoratedExponent_injective
  obtain ⟨base, t, hsep, havoid, hne⟩ :=
    exists_base_separating_avoiding_and_eval_ne_zero hd
      (row := MultivariateAffinePatternRow p) (idx := Fin p.frameCount)
      (τ := MultivariateAffinePatternRow p × MultivariateAffinePatternJet p) ε hε Cav _ hW
  obtain ⟨P, hP⟩ := exists_mvPolynomial_affine_packet_prescribed
    (I := MultivariateAffinePatternRow p × Fin p.frameCount)
    (fun q => ε q.2) (fun q => base q.1) hsep (fun q => p.orders q.2)
    (fun q a => if h : Finsupp.degree a < p.orders q.2 then t (q.1, ⟨q.2, ⟨a, h⟩⟩) else 0)
  have hobs : multivariateAffinePatternObservationCLM frame p base
      (mvPolynomialMultivariateEntire P) = t := by
    funext x
    obtain ⟨a, ⟨i, ⟨α, hα⟩⟩⟩ := x
    have := hP (a, i) α hα
    simpa [multivariateAffinePatternObservationCLM, ε, hα] using this
  have hescape : eval (multivariateAffinePatternObservationCLM frame p base
        (mvPolynomialMultivariateEntire P))
      (multivariateCoefficientPatternDeterminant base p.coordinateExponent p.jetExponent) ≠ 0 := by
    rw [hobs, eval_multivariateCoefficientPatternDeterminant]
    rw [eval_multivariateFullPatternDeterminant p.coordinateExponent p.jetExponent base t] at hne
    exact hne
  refine ⟨{
    toMultivariateAffinePatternWitness :=
      { base := base
        source := mvPolynomialMultivariateEntire P
        escapes := hescape
        defect_interior_empty :=
          interior_continuousLinearMap_mvPolynomial_zero_eq_empty_of_witness
            (multivariateAffinePatternObservationCLM frame p base)
            (multivariateCoefficientPatternDeterminant base p.coordinateExponent
              p.jetExponent)
            (mvPolynomialMultivariateEntire P) hescape }
    packet_injective := by simpa [ε] using hsep }, ?_⟩
  intro q
  exact havoid q

/-- A chosen separated escaping witness avoiding a prescribed finite set of node values. -/
def avoidingAffineJetPacketWitness {d : ℕ} (hd : 0 < d) {Λ : Type*}
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (hframe : Function.Injective frame)
    (Cav : Finset (Fin d → ℂ)) (p : FiniteMultivariateAffineJetPattern Λ d) :
    MultivariateAffinePatternWitness frame p :=
  (exists_separatedWitness_avoiding hd frame hframe p Cav).choose.toMultivariateAffinePatternWitness

theorem avoidingAffineJetPacketWitness_packet_injective {d : ℕ} (hd : 0 < d) {Λ : Type*}
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (hframe : Function.Injective frame)
    (Cav : Finset (Fin d → ℂ)) (p : FiniteMultivariateAffineJetPattern Λ d) :
    Function.Injective
      (fun q : MultivariateAffinePatternRow p × Fin p.frameCount =>
        frame (p.frameCode q.2) ((avoidingAffineJetPacketWitness hd frame hframe Cav p).base q.1)) :=
  (exists_separatedWitness_avoiding hd frame hframe p Cav).choose.packet_injective

theorem avoidingAffineJetPacketWitness_avoids {d : ℕ} (hd : 0 < d) {Λ : Type*}
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (hframe : Function.Injective frame)
    (Cav : Finset (Fin d → ℂ)) (p : FiniteMultivariateAffineJetPattern Λ d)
    (q : MultivariateAffinePatternRow p × Fin p.frameCount) :
    frame (p.frameCode q.2)
      ((avoidingAffineJetPacketWitness hd frame hframe Cav p).base q.1) ∉ Cav :=
  (exists_separatedWitness_avoiding hd frame hframe p Cav).choose_spec q

end

end GaloisForLFunctions.HTGeometry
