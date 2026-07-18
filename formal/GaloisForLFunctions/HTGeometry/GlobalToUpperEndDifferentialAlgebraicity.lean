import GaloisForLFunctions.HTGeometry.ArgumentScalingInvariance
import GaloisForLFunctions.HTGeometry.UpperEndPrimeLogJets
import GaloisForLFunctions.HTGeometry.UpperEndRationalGauge

/-!
# Global differential algebraicity descends to the upper end

An entire complex function has an actual eventual-analytic germ at the complex upper end.  This
file proves that a global algebraic differential equation for the function survives in the
upper-end meromorphic field over its faithfully embedded rational coordinate field `ℂ(z)`.

The point variable in the global equation is moved into the polynomial coefficient ring by the
existing injective `reshapeJet` map, and then embedded faithfully into `RatFunc ℂ`.  Analyticity
identifies the algebraic field jets of the upper-end element with the germs of the ordinary
iterated derivatives.  Consequently upper-end hypertranscendence implies global functional
hypertranscendence.  The final statement includes a nonzero argument rotation, using the existing
unconditional argument-scaling invariance.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set Polynomial
open scoped Differential

noncomputable section

/-- The `n`th ordinary derivative of an entire function as an actual upper-end analytic germ. -/
def entireUpperEndAnalyticJet (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) (n : ℕ) :
    upperEndAnalyticSubring :=
  ⟨Germ.coeRingHom upperEndFilter (iteratedDeriv n f),
    iteratedDeriv n f, 0,
    (analyticOnNhd_iteratedDeriv hf n).mono (subset_univ (upperTail 0)), rfl⟩

/-- An entire function as an actual upper-end meromorphic element. -/
def entireUpperEndMero (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) : upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  exact algebraMap upperEndAnalyticSubring upperEndMeroField
    (entireUpperEndAnalyticJet f hf 0)

@[simp]
theorem entireUpperEndAnalyticJet_coe (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) (n : ℕ) :
    ((entireUpperEndAnalyticJet f hf n : upperEndAnalyticSubring) :
        Germ upperEndFilter ℂ) =
      (iteratedDeriv n f : Germ upperEndFilter ℂ) :=
  rfl

/-- Ordinary differentiation advances the actual entire-function jet at the upper end. -/
theorem upperEndAnalyticDeriv_entireUpperEndAnalyticJet (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) (n : ℕ) :
    upperEndAnalyticDeriv (entireUpperEndAnalyticJet f hf n) =
      entireUpperEndAnalyticJet f hf (n + 1) := by
  apply Subtype.ext
  change (deriv (iteratedDeriv n f) : Germ upperEndFilter ℂ) =
    (iteratedDeriv (n + 1) f : Germ upperEndFilter ℂ)
  rw [iteratedDeriv_succ]

/-- Algebraic jets of the meromorphic realization are the actual ordinary derivative germs. -/
theorem differentialJet_entireUpperEndMero (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) (n : ℕ) :
    letI := isDomain_upperEndAnalyticSubring
    letI := upperEndMeroFieldDifferential
    differentialJet n (entireUpperEndMero f hf) =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (entireUpperEndAnalyticJet f hf n) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI := upperEndMeroFieldDifferential
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [differentialJet_succ, ih,
        upperEndMeroFieldDifferential_algebraMap,
        upperEndAnalyticDeriv_entireUpperEndAnalyticJet]

/-- Evaluation after `reshapeJet` is evaluation with the explicit point in slot zero. -/
theorem eval₂_reshapeJet_entireJets (f : ℂ → ℂ) (n : ℕ) (z : ℂ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom z)
        (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) (reshapeJet n P) =
      MvPolynomial.eval
        (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) P := by
  have hhom :
      (MvPolynomial.eval₂Hom (Polynomial.evalRingHom z)
          (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)).comp
          (reshapeJet n) =
        (MvPolynomial.eval
          (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) :
            MvPolynomial (Fin (n + 2)) ℂ →+* ℂ) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [reshapeJet]
    · intro i
      induction i using Fin.cases with
      | zero => simp [reshapeJet]
      | succ j => simp [reshapeJet, Fin.cons_succ]
  exact RingHom.congr_fun hhom P

/-- Polynomial-coefficient evaluation on actual analytic jets agrees with pointwise evaluation. -/
theorem upperEndAnalyticRelation_entireJets_coe (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) {m : ℕ}
    (G : MvPolynomial (Fin m) (Polynomial ℂ)) :
    ((MvPolynomial.eval₂ upperEndPolyToAnalytic
        (fun j : Fin m => entireUpperEndAnalyticJet f hf (j : ℕ)) G :
          upperEndAnalyticSubring) : Germ upperEndFilter ℂ) =
      ((fun z => MvPolynomial.eval₂ (Polynomial.evalRingHom z)
        (fun j : Fin m => iteratedDeriv (j : ℕ) f z) G) :
          Germ upperEndFilter ℂ) := by
  induction G using MvPolynomial.induction_on with
  | C p =>
      rw [MvPolynomial.eval₂_C]
      apply Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun z => by simp
  | add P Q hP hQ =>
      rw [MvPolynomial.eval₂_add]
      change
        ((MvPolynomial.eval₂ upperEndPolyToAnalytic
          (fun j : Fin m => entireUpperEndAnalyticJet f hf (j : ℕ)) P :
            upperEndAnalyticSubring) : Germ upperEndFilter ℂ) +
        ((MvPolynomial.eval₂ upperEndPolyToAnalytic
          (fun j : Fin m => entireUpperEndAnalyticJet f hf (j : ℕ)) Q :
            upperEndAnalyticSubring) : Germ upperEndFilter ℂ) = _
      rw [hP, hQ, ← Germ.coe_add]
      apply Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun z => by simp
  | mul_X P j hP =>
      rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
      change
        ((MvPolynomial.eval₂ upperEndPolyToAnalytic
          (fun k : Fin m => entireUpperEndAnalyticJet f hf (k : ℕ)) P :
            upperEndAnalyticSubring) : Germ upperEndFilter ℂ) *
          (entireUpperEndAnalyticJet f hf (j : ℕ) : Germ upperEndFilter ℂ) = _
      rw [hP, entireUpperEndAnalyticJet_coe, ← Germ.coe_mul]
      apply Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun z => by simp

/-- A global algebraic differential equation for an entire function survives in the actual
upper-end meromorphic field over the rational coordinate field `ℂ(z)`. -/
theorem differentialAlgebraicOver_entireUpperEndMero_of_differentiallyAlgebraic
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ))
    (hDA : DifferentiallyAlgebraic f) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialAlgebraicOver (RatFunc ℂ) (entireUpperEndMero f hf) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  obtain ⟨n, P, hP, hrel⟩ := hDA
  let G : MvPolynomial (Fin (n + 1)) (Polynomial ℂ) := reshapeJet n P
  let Q : MvPolynomial (Fin (n + 1)) (RatFunc ℂ) :=
    MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) G
  have hG : G ≠ 0 := by
    intro hzero
    exact hP (reshapeJet_injective n (by simpa [G] using hzero))
  have hQ : Q ≠ 0 := by
    intro hzero
    apply hG
    apply MvPolynomial.map_injective _ (RatFunc.algebraMap_injective ℂ)
    simpa [Q] using hzero
  let analyticJet : Fin (n + 1) → upperEndAnalyticSubring :=
    fun j => entireUpperEndAnalyticJet f hf (j : ℕ)
  have hanalytic :
      MvPolynomial.eval₂ upperEndPolyToAnalytic analyticJet G = 0 := by
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero]
    rw [upperEndAnalyticRelation_entireJets_coe]
    rw [← Germ.coe_zero, Germ.coe_eq]
    exact Filter.Eventually.of_forall fun z => by
      change MvPolynomial.eval₂ (Polynomial.evalRingHom z)
        (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) G = 0
      rw [show MvPolynomial.eval₂ (Polynomial.evalRingHom z)
          (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) G =
          MvPolynomial.eval
            (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) P by
        exact eval₂_reshapeJet_entireJets f n z P]
      exact hrel z
  have hmap :
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (MvPolynomial.eval₂ upperEndPolyToAnalytic analyticJet G) = 0 := by
    rw [hanalytic, map_zero]
  rw [MvPolynomial.eval₂_comp_right] at hmap
  rw [MvPolynomial.eval₂_map] at hmap
  change MvPolynomial.eval₂ upperEndPolyToMero
      (fun j => algebraMap upperEndAnalyticSubring upperEndMeroField (analyticJet j)) G = 0
    at hmap
  have hfield : MvPolynomial.aeval
      (fun j : Fin (n + 1) => differentialJet (j : ℕ) (entireUpperEndMero f hf)) Q = 0 := by
    rw [MvPolynomial.aeval_def]
    dsimp only [Q]
    rw [MvPolynomial.eval₂_map]
    change MvPolynomial.eval₂
      (upperEndRatfuncToMero.comp (algebraMap (Polynomial ℂ) (RatFunc ℂ)))
      (fun j : Fin (n + 1) => differentialJet (j : ℕ) (entireUpperEndMero f hf)) G = 0
    rw [show upperEndRatfuncToMero.comp
        (algebraMap (Polynomial ℂ) (RatFunc ℂ)) = upperEndPolyToMero by
      apply DFunLike.ext _ _
      intro p
      exact upperEndRatfuncToMero_algebraMap_polynomial p]
    rw [show (fun j : Fin (n + 1) =>
        differentialJet (j : ℕ) (entireUpperEndMero f hf)) =
        (fun j => algebraMap upperEndAnalyticSubring upperEndMeroField (analyticJet j)) by
      funext j
      exact differentialJet_entireUpperEndMero f hf (j : ℕ)]
    exact hmap
  unfold DifferentialAlgebraicOver DifferentialIndependent
  intro hindependent
  let e : Fin (n + 1) → Unit × ℕ := fun j => ((), (j : ℕ))
  have he : Function.Injective e := by
    intro i j hij
    exact Fin.ext (congrArg Prod.snd hij)
  have hrename : MvPolynomial.rename e Q ≠ 0 := fun hzero =>
    hQ (MvPolynomial.rename_injective e he hzero)
  apply hrename
  apply hindependent.eq_zero_of_aeval_eq_zero
  rw [MvPolynomial.aeval_rename]
  simpa [e, Function.comp_def] using hfield

/-- Entirety is preserved by a complex argument scaling. -/
theorem analyticOnNhd_entire_comp_const_mul {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) (c : ℂ) :
    AnalyticOnNhd ℂ (fun z => f (c * z)) (Set.univ : Set ℂ) :=
  hf.comp (analyticOnNhd_const.mul analyticOnNhd_id) (by simp)

/-- The actual rotated upper-end analytic realization of an entire function. -/
def rotatedEntireUpperEndAnalytic (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) (c : ℂ) :
    upperEndAnalyticSubring :=
  entireUpperEndAnalyticJet (fun z => f (c * z))
    (analyticOnNhd_entire_comp_const_mul hf c) 0

/-- The actual rotated upper-end meromorphic realization of an entire function. -/
def rotatedEntireUpperEndMero (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) (c : ℂ) : upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  exact algebraMap upperEndAnalyticSubring upperEndMeroField
    (rotatedEntireUpperEndAnalytic f hf c)

@[simp]
theorem rotatedEntireUpperEndAnalytic_coe (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) (c : ℂ) :
    ((rotatedEntireUpperEndAnalytic f hf c : upperEndAnalyticSubring) :
        Germ upperEndFilter ℂ) =
      ((fun z => f (c * z)) : Germ upperEndFilter ℂ) := by
  rw [rotatedEntireUpperEndAnalytic, entireUpperEndAnalyticJet_coe]
  simp only [iteratedDeriv_zero]

@[simp]
theorem rotatedEntireUpperEndMero_eq_algebraMap (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) (c : ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    rotatedEntireUpperEndMero f hf c =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (rotatedEntireUpperEndAnalytic f hf c) :=
  rfl

/-- Global differential algebraicity descends to every nontrivially rotated actual upper-end
realization. -/
theorem differentialAlgebraicOver_rotatedEntireUpperEndMero
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ))
    {c : ℂ} (hc : c ≠ 0) (hDA : DifferentiallyAlgebraic f) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialAlgebraicOver (RatFunc ℂ) (rotatedEntireUpperEndMero f hf c) := by
  simpa [rotatedEntireUpperEndMero, rotatedEntireUpperEndAnalytic,
    entireUpperEndMero] using
    differentialAlgebraicOver_entireUpperEndMero_of_differentiallyAlgebraic
      (analyticOnNhd_entire_comp_const_mul hf c)
      (hDA.comp_const_mul_uncond hc)

/-- **Upper-end-to-global hypertranscendence bridge.**  If the actual rotated upper-end realization
is hypertranscendental over `ℂ(z)`, then the original entire function is globally
hypertranscendental. -/
theorem hypertranscendental_of_rotatedEntireUpperEnd_hypertranscendentalOver
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ))
    {c : ℂ} (hc : c ≠ 0)
    (hupper :
      letI := isDomain_upperEndAnalyticSubring
      letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
      letI := upperEndMeroFieldDifferential
      HypertranscendentalOver (RatFunc ℂ) (rotatedEntireUpperEndMero f hf c)) :
    Hypertranscendental f := by
  intro hDA
  exact hupper (differentialAlgebraicOver_rotatedEntireUpperEndMero hf hc hDA)

end

end GaloisForLFunctions.HTGeometry
