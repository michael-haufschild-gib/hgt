import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.FieldFactor
import GaloisForLFunctions.HTGeometry.UltraproductRank

/-! # Finitely many simple-factor certificates suffice for all real specializations -/

open Polynomial Filter
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
noncomputable section
variable {A : Type*} [CommRing A]

private def germEval {I : Type*} (L : Filter I) (φ : I → A →+* ℝ) : A →+* Germ L ℝ :=
  (Germ.coeRingHom L).comp (RingHom.pi φ)

private theorem germ_eval₂ {I : Type*} (L : Filter I) (φ : I → A →+* ℝ) (y : I → ℝ) (p : A[X]) :
    p.eval₂ (germEval L φ) (y : Germ L ℝ)=((fun i => p.eval₂ (φ i) (y i)) : Germ L ℝ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [eval₂_add,hp,hq]
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun _ => (eval₂_add ..).symm
  | monomial n a =>
    rw [eval₂_monomial]
    change (Germ.coeRingHom L) (fun i => φ i a)*((Germ.coeRingHom L) y)^n=_
    rw [←map_pow,←map_mul]
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun _ => (eval₂_monomial ..).symm

private theorem germ_zero {I : Type*} (L : Filter I) (z : I → ℝ) :
    (z : Germ L ℝ)=0 ↔ ∀ᶠ i in L, z i=0 := by
  rw [←Germ.coe_zero (l:=L) (M:=ℝ),Germ.coe_eq]
  rfl

private theorem polynomial_zero_eventually {I : Type*} (L : Filter I) (φ : I → A →+* ℝ) (p : A[X])
    (h : p.map (germEval L φ)=0) : ∀ᶠ i in L, p.map (φ i)=0 := by
  have hz : germEval L φ (coefficientSquares p)=0 := by
    rw [coefficientSquares,map_sum]
    apply Finset.sum_eq_zero
    intro n _
    have hc := congrArg (fun q : (Germ L ℝ)[X] => q.coeff n) h
    simp only [coeff_map,coeff_zero] at hc
    rw [map_pow,hc,zero_pow (by decide : 2≠0)]
  exact ((germ_zero L _).mp hz).mono fun i hi => (coefficientSquares_zero_iff (φ i) p).mp hi

/-- Otherwise a root escaping each finite list gives an ultraproduct
root escaping every factor. Separability in that field supplies one
factor whose finitely many tests hold back on the original indices. -/
theorem finite_factors (p : A[X]) :
    ∃ C : Finset (FactorChoice A), ∀ (φ : A →+* ℝ) (y : ℝ), p.eval₂ φ y=0 → p.map φ≠0 →
      ∃ c∈C, c.serves p φ y := by
  classical
  by_contra! h
  choose φ y hr hn hbad using h
  let I := Finset (FactorChoice A)
  let u := Ultrafilter.of (atTop : Filter I)
  let L := (u : Filter I)
  let Φ := germEval L φ
  have he (q : A[X]) : q.eval₂ Φ (y : Germ L ℝ)=0 ↔ ∀ᶠ i in L, q.eval₂ (φ i) (y i)=0 := by
    rw [germ_eval₂,germ_zero]
  have hne (z : I → ℝ) (hz : (z : Germ L ℝ)≠0) : ∀ᶠ i in L, z i≠0 := by
    have hh : ¬∀ᶠ i in L, z i=0 := fun h => hz ((germ_zero L z).mpr h)
    exact (Ultrafilter.eventually_not (f:=u)).mpr hh
  have hpg : p.map Φ≠0 := by
    intro hp
    obtain ⟨i,hi⟩ := (polynomial_zero_eventually L φ p hp).exists
    exact hn i hi
  obtain ⟨c,hd,hR,hP,hP'⟩ := exists_factor Φ p (y : Germ L ℝ) ((he p).mpr (Eventually.of_forall hr)) hpg
  have hd' := hne (fun i => φ i c.den) hd
  have hder : ∀ᶠ i in L, c.factor.derivative.eval₂ (φ i) (y i)≠0 := by
    apply hne
    rwa [←germ_eval₂]
  have hc : ∀ᶠ i in L, c∈i :=
    ((eventually_ge_atTop ({c} : I)).filter_mono (Ultrafilter.of_le _)).mono
      fun _ hh => hh (Finset.mem_singleton_self c)
  have impossible : ∀ᶠ _i in L, False := by
    filter_upwards [hd',polynomial_zero_eventually L φ _ hR,(he _).mp hP,hder,hc] with i hd hR hp hdv hc
    exact hbad i c hc ⟨hd,hR,hp,hdv⟩
  exact impossible.exists.elim fun _ h => h

#print axioms finite_factors
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
