import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.ActionZeros
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.MonomialWeights
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactContacts.CoarseVisits.DependentDates

/-! # Algebraic independence off a prescribed phase pair -/

open Set Filter Matrix MeasureTheory MvPolynomial
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
noncomputable section

/-- After normalizing by one gap, the exponential ratios on all other
levels are algebraically independent at almost every simple coupling.
The nonzero complex scale is prescribed before the draw. -/
theorem ae_independent_normalized_phases (K : Type) [Field K] [Countable K] [Algebra K ℂ]
    {n D : ℕ} {P : Fin n → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ l, (P l).IsHermitian) (hs : SpectrumEscapesRealRelations (range (spectralEnsembleMatrix P)))
    (i j : Fin D) (hij : i≠j) {χ : ℂ} (hχ : χ≠0) :
    ∀ᵐ x ∂volume, x∈simpleEnsembleLocus hP → let E := sortedEnsembleSpectrum hP x
      AlgebraicIndependent K (fun l : Outside i j => Complex.exp (χ*(((E l.val-E j)/(E i-E j):ℝ):ℂ))) := by
  classical
  let B := MvPolynomial (Outside i j) K
  letI : Countable B := AddMonoidAlgebra.coeff_injective.countable
  let z (x : Fin n → ℝ) (l : Outside i j) := Complex.exp (χ*
    (((sortedEnsembleSpectrum hP x l.val-sortedEnsembleSpectrum hP x j) /
      (sortedEnsembleSpectrum hP x i-sortedEnsembleSpectrum hP x j):ℝ):ℂ))
  have H (p : {p : B // p≠0}) : ∀ᵐ x ∂volume, x∈simpleEnsembleLocus hP → aeval (z x) p.val≠0 := by
    let L := ↥p.val.support
    let w (d : L) := monomialWeight i j d.val
    have ho (u v : L) (huv : u≠v) : ∃ l, l≠i ∧ l≠j ∧ w u l≠w v l := by
      have hdiff : ∃ l : Outside i j, u.val l≠v.val l := by
        by_contra! h
        exact huv (Subtype.ext (Finsupp.ext h))
      obtain ⟨l,hl⟩ := hdiff
      refine ⟨l.val,l.property.1,l.property.2,?_⟩
      simp only [w,monomialWeight_outside]
      exact_mod_cast hl
    let a (l : L) : ℂ := algebraMap K ℂ (p.val.coeff l.val)
    obtain ⟨l,hl⟩ := MvPolynomial.support_nonempty.mpr p.property
    have ha : ∃ d : L, a d≠0 := ⟨⟨l,hl⟩,by
      exact (map_ne_zero (algebraMap K ℂ)).mpr (MvPolynomial.mem_support_iff.mp hl)⟩
    have hn := normalized_exponential_zero_null hP hs i j hij w
      (fun l => monomialWeight_balanced i j l.val) ho hχ a ha
    have hh : ∀ᵐ x ∂volume, x ∉ {x ∈ simpleEnsembleLocus hP | ∑ u, a u*Complex.exp
        (χ*(normalizedAction (w u) (sortedEnsembleSpectrum hP x) i j:ℝ))=0} :=
      measure_eq_zero_iff_ae_notMem.mp hn
    filter_upwards [hh] with x hx hsimp he
    apply hx
    exact ⟨hsimp,(normalized_polynomial_expansion i j p.val _ χ).symm.trans he⟩
  filter_upwards [ae_all_iff.mpr H] with x hx hsimp
  intro E
  apply algebraicIndependent_iff.mpr
  intro p hp
  by_contra hn
  exact hx ⟨p,hn⟩ hsimp hp

#print axioms ae_independent_normalized_phases
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
