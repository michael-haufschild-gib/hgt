import GaloisForLFunctions.HTGeometry.DigammaGammaFactorialBlowUp
import GaloisForLFunctions.HTGeometry.ComplexExponentialSeriesCarrier

/-!
# A differential relation of an entire function holds everywhere

The evaluation of a differential relation along the jets of an analytic function is analytic, so if
the relation holds on a nonempty open set it holds on the whole plane -- in particular on the real
line, where the Bohr theory lives.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The jet evaluation of a relation is analytic where the function is.** -/
theorem analyticAt_jetEval {f : ℂ → ℂ} (hf : ∀ w : ℂ, AnalyticAt ℂ f w) {n : ℕ}
    (P : MvPolynomial (Fin (n + 2)) ℂ) (z : ℂ) :
    AnalyticAt ℂ (fun w => MvPolynomial.eval
      (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f w)) P) z := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => c) z)
  | add P Q hP hQ =>
      have heq : (fun w => MvPolynomial.eval
          (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f w)) (P + Q))
          = fun w => MvPolynomial.eval
              (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f w)) P
            + MvPolynomial.eval
              (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f w)) Q := by
        funext w
        simp
      rw [heq]
      exact hP.add hQ
  | mul_X P i hP =>
      have heq : (fun w => MvPolynomial.eval
          (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f w))
            (P * MvPolynomial.X i))
          = fun w => MvPolynomial.eval
              (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f w)) P
            * (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f w) :
              Fin (n + 2) → ℂ) i := by
        funext w
        simp
      rw [heq]
      refine hP.mul ?_
      induction i using Fin.cases with
      | zero =>
          simp only [Fin.cons_zero]
          exact analyticAt_id
      | succ j =>
          simp only [Fin.cons_succ]
          exact analyticAt_iteratedDeriv_of_analyticAt (hf z) (j : ℕ)

/-- **A differential relation of an entire function propagates to the whole plane.** -/
theorem jetRelation_eq_zero_of_isOpen {f : ℂ → ℂ} (hf : ∀ w : ℂ, AnalyticAt ℂ f w) {n : ℕ}
    {P : MvPolynomial (Fin (n + 2)) ℂ} {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    (hrel : ∀ z ∈ U, MvPolynomial.eval
      (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)) P = 0) :
    ∀ z : ℂ, MvPolynomial.eval
      (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)) P = 0 := by
  set E : ℂ → ℂ := fun z => MvPolynomial.eval
    (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)) P with hE
  obtain ⟨z₀, hz₀⟩ := hUne
  have han : AnalyticOnNhd ℂ E Set.univ := fun z _ => analyticAt_jetEval hf P z
  letI : NeBot (𝓝[≠] z₀) := NormedField.nhdsNE_neBot z₀
  have hlocal : ∀ᶠ z in 𝓝 z₀, E z = 0 := by
    filter_upwards [hU.mem_nhds hz₀] with z hz
    exact hrel z hz
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, E z = 0 :=
    (hlocal.filter_mono nhdsWithin_le_nhds).frequently
  intro z
  exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ z₀) hfreq (Set.mem_univ z)

/-- The entire carrier is analytic at every point. -/
theorem analyticAt_cexpSeriesCarrier {ι : Type*} {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) (z : ℂ) :
    AnalyticAt ℂ (cexpSeriesCarrier a omega) z :=
  (differentiable_cexpSeriesCarrier h).differentiableOn.analyticOnNhd isOpen_univ z
    (Set.mem_univ z)

end

end GaloisForLFunctions.HTGeometry
