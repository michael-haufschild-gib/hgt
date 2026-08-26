import GaloisForLFunctions.HTGeometry.AffineFramePacketSeparation
import GaloisForLFunctions.HTGeometry.CountableMultivariateAffineJetPattern

/-!
# Witnesses for the decorated affine jet-packet determinants

The decorated determinant of a finite pattern, taken with both the base coordinates and the jet
values as indeterminates, is a nonzero polynomial.  Multiplying it by the coordinate defects of all
packet coincidences and evaluating at a nonvanishing point selects one base which separates the
packet, and one jet vector on which the determinant does not vanish.  Affine jet-packet
surjectivity then realizes that jet vector by a polynomial source, so every determinant defect of a
noncolliding affine family carries a genuine escaping witness.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-- A decorated-pattern witness retaining the separation certificate used by Hermite
interpolation.  The older residual construction only needs the underlying escaping witness;
probabilistic applications also need to know that its finite jet packet is read at distinct
affine-image points. -/
structure SeparatedMultivariateAffinePatternWitness {d : ℕ} {Λ : Type*}
    (frame : Λ → (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (p : FiniteMultivariateAffineJetPattern Λ d)
    extends MultivariateAffinePatternWitness frame p where
  packet_injective : Function.Injective
    (fun q : MultivariateAffinePatternRow p × Fin p.frameCount =>
      frame (p.frameCode q.2) (base q.1))

/-- The decorated pattern determinant with the base coordinates as further indeterminates. -/
def multivariateFullPatternDeterminant {d : ℕ} {row σ : Type*} [Fintype row] [DecidableEq row]
    (coordinateExponent : row → Fin d →₀ ℕ) (jetExponent : row → σ →₀ ℕ) :
    MvPolynomial ((row × Fin d) ⊕ (row × σ)) ℂ :=
  (Matrix.of fun a b =>
    (coordinateExponent b).prod
        (fun i k => (X (Sum.inl (a, i)) : MvPolynomial ((row × Fin d) ⊕ (row × σ)) ℂ) ^ k) *
      (jetExponent b).prod
        (fun s k => (X (Sum.inr (a, s)) : MvPolynomial ((row × Fin d) ⊕ (row × σ)) ℂ) ^ k)).det

theorem eval_multivariateFullPatternDeterminant {d : ℕ} {row σ : Type*}
    [Fintype row] [DecidableEq row]
    (coordinateExponent : row → Fin d →₀ ℕ) (jetExponent : row → σ →₀ ℕ)
    (base : row → Fin d → ℂ) (t : row × σ → ℂ) :
    eval (Sum.elim (fun pr : row × Fin d => base pr.1 pr.2) t)
        (multivariateFullPatternDeterminant coordinateExponent jetExponent) =
      (Matrix.of fun a b => (coordinateExponent b).prod (fun i k => base a i ^ k) *
        (jetExponent b).prod (fun s k => t (a, s) ^ k) : Matrix row row ℂ).det := by
  rw [multivariateFullPatternDeterminant, RingHom.map_det]
  congr 1
  ext a b
  simp [Finsupp.prod, map_prod]

/-- The full decorated determinant of distinct decorated monomials is a nonzero polynomial. -/
theorem multivariateFullPatternDeterminant_ne_zero {d : ℕ} {row σ : Type*}
    [Fintype row] [DecidableEq row]
    (coordinateExponent : row → Fin d →₀ ℕ) (jetExponent : row → σ →₀ ℕ)
    (hpair : Function.Injective fun k => (coordinateExponent k, jetExponent k)) :
    multivariateFullPatternDeterminant coordinateExponent jetExponent ≠ 0 := by
  obtain ⟨base, target, hunit⟩ :=
    exists_fullRank_multivariateExpandedMonomial_packet coordinateExponent jetExponent hpair
  intro hzero
  have hdet : (Matrix.of fun a b => (coordinateExponent b).prod (fun i k => base a i ^ k) *
      (jetExponent b).prod (fun s k => target a s ^ k) : Matrix row row ℂ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero
  apply hdet
  rw [← eval_multivariateFullPatternDeterminant coordinateExponent jetExponent base
    (fun pr => target pr.1 pr.2), hzero, map_zero]

/-- **Every finite decorated pattern of a noncolliding affine family has a separated escaping
witness.** -/
theorem nonempty_separatedMultivariateAffinePatternWitness {d : ℕ} (hd : 0 < d) {Λ : Type*}
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (hframe : Function.Injective frame)
    (p : FiniteMultivariateAffineJetPattern Λ d) :
    Nonempty (SeparatedMultivariateAffinePatternWitness frame p) := by
  classical
  let ε : Fin p.frameCount → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ)) := fun i => frame (p.frameCode i)
  have hε : Function.Injective fun i => ((ε i : (Fin d → ℂ) → Fin d → ℂ)) := by
    intro i j hij
    exact p.frameCode_injective (hframe (DFunLike.coe_injective hij))
  have hW : multivariateFullPatternDeterminant p.coordinateExponent p.jetExponent ≠ 0 :=
    multivariateFullPatternDeterminant_ne_zero _ _ p.decoratedExponent_injective
  obtain ⟨base, t, hsep, hne⟩ :=
    exists_base_separating_and_eval_ne_zero hd
      (row := MultivariateAffinePatternRow p) (idx := Fin p.frameCount)
      (τ := MultivariateAffinePatternRow p × MultivariateAffinePatternJet p) ε hε _ hW
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
  exact ⟨{
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
    packet_injective := by simpa [ε] using hsep }⟩

/-- Backward-compatible escaping witness, obtained by forgetting the retained separation
certificate. -/
theorem nonempty_multivariateAffinePatternWitness {d : ℕ} (hd : 0 < d) {Λ : Type*}
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (hframe : Function.Injective frame)
    (p : FiniteMultivariateAffineJetPattern Λ d) :
    Nonempty (MultivariateAffinePatternWitness frame p) :=
  ⟨(nonempty_separatedMultivariateAffinePatternWitness hd frame hframe p).some.toMultivariateAffinePatternWitness⟩

end

end GaloisForLFunctions.HTGeometry
