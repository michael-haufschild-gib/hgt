import GaloisForLFunctions.HTGeometry.DirectionalMeromorphicField
import GaloisForLFunctions.HTGeometry.RealPolynomialZeroMeasure

/-!
# Two globalisation steps

A symmetrised spectral obstruction is a finite product of analytic factors, and it descends to a
polynomial in the real Hamiltonian parameters.  Two facts turn local flatness into a global
identity:

* a finite product of functions analytic on a connected open set vanishes there only if one factor
  does -- the identity theorem as an integral-domain statement, iterated;
* a real polynomial vanishing on a nonempty open set of parameters is the zero polynomial, because
  the zero set of a nonzero real polynomial is Lebesgue-null while a nonempty open set is not.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A finite product of analytic functions is analytic. -/
theorem analyticOnNhd_finsetProd {ι : Type*} {U : Set E} {f : ι → E → ℂ} (s : Finset ι)
    (hf : ∀ i ∈ s, AnalyticOnNhd ℂ (f i) U) :
    AnalyticOnNhd ℂ (fun z => ∏ i ∈ s, f i z) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using analyticOnNhd_const (v := (1 : ℂ)) (s := U)
  | insert a s ha ih =>
      have h1 : AnalyticOnNhd ℂ (f a) U := hf a (by simp)
      have h2 := ih fun i hi => hf i (by simp [hi])
      have hfun : (fun z => ∏ i ∈ insert a s, f i z) = fun z => f a z * ∏ i ∈ s, f i z := by
        funext z
        rw [Finset.prod_insert ha]
      rw [hfun]
      exact h1.mul h2

/-- **The identity theorem for a finite product.**  If a finite product of functions analytic on a
connected open set vanishes there, some factor vanishes identically. -/
theorem exists_eqOn_zero_of_finsetProd_eqOn_zero {ι : Type*} {U : Set E} {f : ι → E → ℂ}
    (s : Finset ι) (hf : ∀ i ∈ s, AnalyticOnNhd ℂ (f i) U)
    (hU : IsPreconnected U) (hUo : IsOpen U) (hUne : U.Nonempty)
    (hprod : Set.EqOn (fun z => ∏ i ∈ s, f i z) 0 U) :
    ∃ i ∈ s, Set.EqOn (f i) 0 U := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exfalso
      obtain ⟨z, hz⟩ := hUne
      have := hprod hz
      simp at this
  | insert a s ha ih =>
      have h1 : AnalyticOnNhd ℂ (f a) U := hf a (by simp)
      have h2 : AnalyticOnNhd ℂ (fun z => ∏ i ∈ s, f i z) U :=
        analyticOnNhd_finsetProd s fun i hi => hf i (by simp [hi])
      have hsplit : Set.EqOn (fun z => f a z * ∏ i ∈ s, f i z) 0 U := by
        intro z hz
        have := hprod hz
        simpa [Finset.prod_insert ha] using this
      rcases analyticOnNhd_domain' h1 h2 hU hUo hsplit with hleft | hright
      · exact ⟨a, by simp, hleft⟩
      · obtain ⟨i, hi, hzero⟩ := ih (fun j hj => hf j (by simp [hj])) hright
        exact ⟨i, by simp [hi], hzero⟩

/-- **A real polynomial vanishing on a nonempty open set is zero.** -/
theorem realMvPolynomial_eq_zero_of_eqOn_zero_isOpen {n : ℕ} {P : MvPolynomial (Fin n) ℝ}
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hUne : U.Nonempty)
    (h : ∀ z ∈ U, MvPolynomial.eval z P = 0) : P = 0 := by
  by_contra hP
  have hnull := realMvPolynomial_zero_set_volume_fin n P hP
  have hsub : U ⊆ {x : Fin n → ℝ | MvPolynomial.eval x P = 0} := fun z hz => h z hz
  have hUnull : volume U = 0 := measure_mono_null hsub hnull
  have hUpos : 0 < volume U := hU.measure_pos volume hUne
  rw [hUnull] at hUpos
  exact lt_irrefl 0 hUpos

end

end GaloisForLFunctions.HTGeometry
