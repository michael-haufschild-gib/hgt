import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.CircuitContacts.PolynomialWeights

/-! # Nonvanishing phase polynomials along an algebraic energy curve -/

open Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.CircuitContacts
open SelectedDates.AlgebraicCurves
noncomputable section

/-- Pairing a monomial's integral multiplicities with the energy branches
preserves algebraicity of its logarithm. -/
private theorem alg_sum {J : Type*} [Fintype J] (g : J→ℂ→ℂ)
    (hg : ∀ i, AnalyticAt ℂ (g i) 0)
    (ha : ∀ i, IsAlgebraic (RatFunc ℂ) (ofMero (g i) (hg i).meromorphicAt))
    (c : J→ℂ) (hs : MeromorphicAt (fun z => ∑ i, c i*g i z) 0) :
    IsAlgebraic (RatFunc ℂ) (ofMero _ hs) := by
  let K := (algebraicClosure (RatFunc ℂ) MeroGerm).restrictScalars ℂ
  let h (i : J) := (MeromorphicAt.const (c i) 0).mul (hg i).meromorphicAt
  apply mem_algebraicClosure_iff.mp
  change ofMero _ hs ∈ K
  rw [←sum_germs (fun i z => c i*g i z) h hs]
  apply K.sum_mem
  intro i _
  rw [←ofMero_mul,←algebraMap_complex_meroGerm]
  exact K.mul_mem (K.algebraMap_mem _) (mem_algebraicClosure_iff.mpr (ha i))

/-- No polynomial in the phases with polynomial field coefficients can
vanish on a real field interval when every nonzero integer action is
nonconstant there. The polynomial coefficients can vanish at the center. -/
theorem phase_polynomial_escape {J : Type*} [Fintype J] (g : J→ℂ→ℂ)
    (hg : ∀ i, AnalyticAt ℂ (g i) 0)
    (ha : ∀ i, IsAlgebraic (RatFunc ℂ) (ofMero (g i) (hg i).meromorphicAt))
    (hd : ∀ m : J→ℤ, m≠0 → ∀ c : ℂ, ¬((fun z => ∑ i, (m i:ℂ)*g i z) =ᶠ[𝓝[≠] 0] fun _ => c))
    (p : MvPolynomial J (Polynomial ℂ)) (hp : p≠0) :
    ∃ᶠ v : ℝ in 𝓝 0, MvPolynomial.eval₂ (Polynomial.evalRingHom (v:ℂ)) (fun i => Complex.exp (g i v)) p≠0 := by
  classical
  let f (a : p.support) (z : ℂ) := ∑ i, (a.val i:ℂ)*g i z
  have hf (a : p.support) : AnalyticAt ℂ (f a) 0 :=
    Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul (hg i)
  have hsep (a b : p.support) (hab : a≠b) (c : ℂ) :
      ¬((fun z => f a z-f b z) =ᶠ[𝓝[≠] 0] fun _ => c) := by
    let m (i : J) : ℤ := (a.val i:ℤ)-(b.val i:ℤ)
    have hm : m≠0 := by
      intro h
      apply hab
      apply Subtype.ext
      ext i
      have hi := congrFun h i
      change (a.val i:ℤ)-(b.val i:ℤ)=0 at hi
      omega
    intro he
    apply hd m hm c
    filter_upwards [he] with z hz
    simpa only [m,Int.cast_sub,Int.cast_natCast,sub_mul,Finset.sum_sub_distrib,f] using hz
  obtain ⟨i,hi⟩ := MvPolynomial.support_nonempty.mpr hp
  have h := polynomial_weight_escape f (fun a => p.coeff a.val) hf
    (fun a => alg_sum g hg ha (fun j => (a.val j:ℂ)) (hf a).meromorphicAt)
    hsep ⟨⟨i,hi⟩,MvPolynomial.mem_support_iff.mp hi⟩
  apply h.mono
  intro v hv he
  apply hv
  rw [Finset.sum_coe_sort p.support (fun a => (p.coeff a).eval (v:ℂ)*Complex.exp (∑ i, (a i:ℂ)*g i v))]
  rw [MvPolynomial.eval₂_eq'] at he
  simpa only [←Complex.exp_nat_mul,←Complex.exp_sum,Polynomial.coe_evalRingHom] using he

#print axioms phase_polynomial_escape
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.CircuitContacts
