import GaloisForLFunctions.HTGeometry.ProductPaletteIndependence
import GaloisForLFunctions.HTGeometry.DigammaGammaLocalHypertranscendence
import GaloisForLFunctions.HTGeometry.LogPrimeExponentialCarrier

/-!
# A hypertranscendental function has algebraically independent jet germs

Independence of a palette over the constants is exactly hypertranscendence, once both are said in the
same language.  `DifferentiallyAlgebraicOn` forbids a polynomial relation among the variable and the
jets; algebraic independence of the jet germs forbids one among the jets alone.  The second is the
special case of the first in which the variable does not occur, so a hypertranscendental analytic
function has algebraically independent jet germs.

This is the form a capacity palette consumes: the palette hypothesis of the product theorems asks for
algebraic independence of a jet family over `ℂ` inside the analytic germ ring.
-/

open Filter Topology Set Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-! ### The unit direction is the ordinary derivative -/

theorem dirFderiv_one (f : ℂ → ℂ) : dirFderiv (1 : ℂ) f = deriv f := by
  funext x
  rw [dirFderiv_apply, fderiv_apply_one_eq_deriv]

/-- The iterates of the germ derivation are the germs of the iterated derivatives. -/
theorem dirSubringDeriv_iterate_coe {V : Set ℂ} (hVo : IsOpen V) {a : analyticGermSubringOn V}
    {f : ℂ → ℂ} (hfa : (Germ.coeRingHom (𝓟 V) f) = (a : Germ (𝓟 V) ℂ)) (m : ℕ) :
    ((((dirSubringDeriv hVo (1 : ℂ))^[m] a : analyticGermSubringOn V)) : Germ (𝓟 V) ℂ)
      = ((iteratedDeriv m f : ℂ → ℂ) : Germ (𝓟 V) ℂ) := by
  induction m with
  | zero =>
      rw [Function.iterate_zero_apply, ← hfa]
      rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply', dirSubringDeriv_coe, ih, dirGermDeriv_coe, dirFderiv_one,
        iteratedDeriv_succ]

/-- The value of a jet germ at a point of the domain is the corresponding iterated derivative. -/
theorem analyticGermEval_iterate {V : Set ℂ} (hVo : IsOpen V) {z : ℂ} (hz : z ∈ V)
    {a : analyticGermSubringOn V} {f : ℂ → ℂ}
    (hfa : (Germ.coeRingHom (𝓟 V) f) = (a : Germ (𝓟 V) ℂ)) (m : ℕ) :
    analyticGermEval hz ((dirSubringDeriv hVo (1 : ℂ))^[m] a) = iteratedDeriv m f z := by
  rw [analyticGermEval_apply, dirSubringDeriv_iterate_coe hVo hfa m]
  rfl

/-! ### Evaluation is an algebra map -/

theorem analyticGermEval_comp_constGermHom {V : Set ℂ} {z : ℂ} (hz : z ∈ V) :
    (analyticGermEval hz).comp (constGermHom V) = RingHom.id ℂ := by
  ext c
  rfl

/-- Evaluating a polynomial in germs at a point is the polynomial in the values. -/
theorem analyticGermEval_aeval {V : Set ℂ} {z : ℂ} (hz : z ∈ V) {ι : Type*}
    (a : ι → analyticGermSubringOn V) (Q : MvPolynomial ι ℂ) :
    letI : Algebra ℂ (analyticGermSubringOn V) := (constGermHom V).toAlgebra
    analyticGermEval hz (MvPolynomial.aeval a Q)
      = MvPolynomial.eval (fun i => analyticGermEval hz (a i)) Q := by
  letI : Algebra ℂ (analyticGermSubringOn V) := (constGermHom V).toAlgebra
  have halg : (algebraMap ℂ (analyticGermSubringOn V)) = constGermHom V := rfl
  rw [MvPolynomial.aeval_def, halg, MvPolynomial.eval₂_comp_left (analyticGermEval hz),
    analyticGermEval_comp_constGermHom hz]
  rfl

/-! ### The bridge -/

/-- **A hypertranscendental analytic function has algebraically independent jet germs.**  A relation
among the jets alone is a differential relation in which the variable does not occur. -/
theorem algebraicIndependent_jetGerm_of_not_differentiallyAlgebraicOn
    {V : Set ℂ} (hVo : IsOpen V) {f : ℂ → ℂ}
    (hHT : ¬ DifferentiallyAlgebraicOn f V) {a : analyticGermSubringOn V}
    (hfa : (Germ.coeRingHom (𝓟 V) f) = (a : Germ (𝓟 V) ℂ)) :
    letI : Algebra ℂ (analyticGermSubringOn V) := (constGermHom V).toAlgebra
    AlgebraicIndependent ℂ fun m : ℕ => (dirSubringDeriv hVo (1 : ℂ))^[m] a := by
  letI : Algebra ℂ (analyticGermSubringOn V) := (constGermHom V).toAlgebra
  rw [algebraicIndependent_iff]
  intro Q hQ
  by_contra hQne
  obtain ⟨N, g, hginj, Q', rfl⟩ := MvPolynomial.exists_fin_rename Q
  have hQ'ne : Q' ≠ 0 := by
    intro h
    exact hQne (by rw [h, map_zero])
  classical
  set M : ℕ := Finset.univ.sup g with hM
  have hgM : ∀ i : Fin N, g i ≤ M := fun i => Finset.le_sup (Finset.mem_univ i)
  set G : Fin N → Fin (M + 2) := fun i => ⟨g i + 1, by have := hgM i; omega⟩ with hG
  have hGinj : Function.Injective G := by
    intro i j hij
    refine hginj ?_
    have := congrArg Fin.val hij
    simp only [hG] at this
    omega
  refine hHT ⟨M, MvPolynomial.rename G Q', ?_, ?_⟩
  · intro h
    exact hQ'ne (MvPolynomial.rename_injective G hGinj (by rw [h, map_zero]))
  · intro z hz
    rw [MvPolynomial.eval_rename]
    have hval : ∀ i : Fin N,
        ((Fin.cons z fun j : Fin (M + 1) => iteratedDeriv (j : ℕ) f z : Fin (M + 2) → ℂ)) (G i)
          = iteratedDeriv (g i) f z := by
      intro i
      have hsucc : G i = Fin.succ ⟨g i, by have := hgM i; omega⟩ := by
        apply Fin.ext
        simp [hG]
      rw [hsucc, Fin.cons_succ]
    have hcomp : ((Fin.cons z fun j : Fin (M + 1) => iteratedDeriv (j : ℕ) f z :
        Fin (M + 2) → ℂ) ∘ G) = fun i : Fin N => iteratedDeriv (g i) f z := funext hval
    rw [hcomp]
    -- the germ relation, evaluated at `z`
    have hQz := congrArg (analyticGermEval hz) hQ
    rw [map_zero, MvPolynomial.aeval_rename, analyticGermEval_aeval hz] at hQz
    have hjet : (fun i : Fin N =>
        analyticGermEval hz (((fun m : ℕ => (dirSubringDeriv hVo (1 : ℂ))^[m] a) ∘ g) i))
        = fun i : Fin N => iteratedDeriv (g i) f z := by
      funext i
      exact analyticGermEval_iterate hVo hz hfa (g i)
    rw [hjet] at hQz
    exact hQz

/-! ### An explicit palette -/

/-- The germ of the explicit log-prime carrier on an open set. -/
def logPrimeCarrierGerm (V : Set ℂ) : analyticGermSubringOn V :=
  ⟨((cexpSeriesCarrier logPrimeAmplitude logPrimeFrequency : ℂ → ℂ) : Germ (𝓟 V) ℂ),
    ⟨cexpSeriesCarrier logPrimeAmplitude logPrimeFrequency,
      fun z _ => analyticAt_cexpSeriesCarrier expSeriesNormallySummable_logPrime z, rfl⟩⟩

/-- **An explicit palette: the jet germs of the log-prime carrier are algebraically independent over
the constants, on every nonempty open set.** -/
theorem algebraicIndependent_jetGerm_logPrimeCarrier {V : Set ℂ} (hVo : IsOpen V)
    (hVne : V.Nonempty) :
    letI : Algebra ℂ (analyticGermSubringOn V) := (constGermHom V).toAlgebra
    AlgebraicIndependent ℂ
      fun m : ℕ => (dirSubringDeriv hVo (1 : ℂ))^[m] (logPrimeCarrierGerm V) :=
  algebraicIndependent_jetGerm_of_not_differentiallyAlgebraicOn hVo
    (not_differentiallyAlgebraicOn_cexpSeriesCarrier
      rationallyIndependentSequence_logPrimeFrequency expSeriesNormallySummable_logPrime
      infinite_support_logPrimeAmplitude hVo hVne)
    rfl

end

end GaloisForLFunctions.HTGeometry
