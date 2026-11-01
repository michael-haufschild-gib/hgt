import GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlgebraicDilationAtoms
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlgebraicDilationPolynomialCoefficients

/-! Actual logarithmic-derivative jets of distinct positive algebraic zeta dilations
have no constant-coefficient polynomial relation on any common convergence line. -/

open Finset Complex
open scoped Classical
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlgebraicDilationJetIndependence
open AlgebraicPrimeFrequency DilatedVonMangoldt DilationPrimeJets AlgebraicDilationAtoms
open DilationPolynomialPolarization AlgebraicDilationPolynomialCoefficients
noncomputable section

/-- A relation among actual dilation jets on a line of absolute convergence is the zero polynomial. -/
theorem polynomial_eq_zero_of_source_jet_line_relation {ι : Type*} [Fintype ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (ha : ∀ i, IsAlgebraic ℤ (r i))
    (hinj : Function.Injective r) (J : ℕ) (sigma : ℝ) (hs : ∀ i, 1 < r i*sigma)
    (P : MvPolynomial (ι × Fin (J+1)) ℂ)
    (hzero : ∀ t : ℝ, MvPolynomial.eval
      (fun ik => iteratedDeriv ik.2.val (source (r ik.1))
        ((sigma : ℂ)+(t : ℂ)*I)) P = 0) : P = 0 := by
  classical
  by_contra hP
  have hsupport : P.support.Nonempty := by
    by_contra hn
    exact hP (MvPolynomial.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hn))
  obtain ⟨d,hd,hmax⟩ := P.support.exists_max_image slotDegree hsupport
  let D := slotDegree d
  let b : (ι × Fin (J+1)) → PrimeAtom → ℂ := fun ik =>
    atomAmplitude (r ik.1) sigma (hr ik.1) (ha ik.1) ik.2.val
  have hb : ∀ ik, Summable fun x => ‖b ik x‖ := fun ik =>
    summable_norm_atomAmplitude (r ik.1) sigma (hr ik.1) (ha ik.1) ik.2.val (hs ik.1)
  have hseries : ∀ t : ℝ, MvPolynomial.eval
      (fun ik => expSeriesCarrier (b ik) (fun x => -atomFrequency x) t) P = 0 := by
    intro t
    have hvalues : (fun ik => expSeriesCarrier (b ik) (fun x => -atomFrequency x) t) =
        fun ik => iteratedDeriv ik.2.val (source (r ik.1))
          ((sigma : ℂ)+(t : ℂ)*I) := by
      funext ik
      exact (source_jet_line_eq_atomSeries (r ik.1) sigma (hr ik.1) (ha ik.1)
        ik.2.val (hs ik.1) t).symm
    rw [hvalues]
    exact hzero t
  have hM : polynomialMultilinear P D = 0 := by
    apply multilinearMap_eq_zero_of_distinct_primeJets r hr hinj J D _ ∅
    intro j p hp hpinj _
    let v : Fin D → PrimeAtom := fun k => ⟨⟨p k,hp k⟩,⟨r (j k),hr (j k),ha (j k)⟩⟩
    have hv : Function.Injective (fun k => (v k).1) := by
      intro k l h
      exact hpinj (congrArg Subtype.val h)
    have hm := polynomialMultilinear_eq_zero_on_atoms P b hb D
      (fun e he => hmax e he) hseries v hv
    have hrows : (fun k ik => b ik (v k)) =
        fun k => atomDecay (r (j k)) sigma ⟨p k,hp k⟩ •
          primeJetVector r J (j k) (p k) := by
      funext k ik
      exact atomAmplitude_eq_primeJet r hr ha sigma (j k) ik.1 ik.2.val ⟨p k,hp k⟩
    rw [hrows,MultilinearMap.map_smul_univ] at hm
    have hdecay : (∏ k, atomDecay (r (j k)) sigma ⟨p k,hp k⟩) ≠ 0 := by
      apply prod_ne_zero_iff.mpr
      intro k _
      exact atomDecay_ne_zero _ _ _
    exact (mul_eq_zero.mp hm).resolve_left hdecay
  exact polynomialMultilinear_ne_zero P d hd hM

/-- All finite actual logarithmic-derivative jet packets are algebraically independent
as functions on every common line of absolute convergence. -/
theorem source_jets_line_algebraicIndependent {ι : Type*} [Fintype ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (ha : ∀ i, IsAlgebraic ℤ (r i))
    (hinj : Function.Injective r) (J : ℕ) (sigma : ℝ) (hs : ∀ i, 1 < r i*sigma) :
    AlgebraicIndependent ℂ (fun ik : ι × Fin (J+1) => fun t : ℝ =>
      iteratedDeriv ik.2.val (source (r ik.1)) ((sigma : ℂ)+(t : ℂ)*I)) := by
  rw [algebraicIndependent_iff]
  intro P hP
  apply polynomial_eq_zero_of_source_jet_line_relation r hr ha hinj J sigma hs P
  intro t
  have he : ∀ Q : MvPolynomial (ι × Fin (J+1)) ℂ,
      (MvPolynomial.aeval (fun ik : ι × Fin (J+1) => fun t : ℝ =>
        iteratedDeriv ik.2.val (source (r ik.1)) ((sigma : ℂ)+(t : ℂ)*I)) Q) t =
      MvPolynomial.eval (fun ik => iteratedDeriv ik.2.val (source (r ik.1))
        ((sigma : ℂ)+(t : ℂ)*I)) Q := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C c => simp
    | add Q R hQ hR => simp [hQ,hR]
    | mul_X Q i hQ => simp [hQ]
  rw [← he P,hP]
  rfl

#print axioms polynomial_eq_zero_of_source_jet_line_relation
#print axioms source_jets_line_algebraicIndependent
end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlgebraicDilationJetIndependence
