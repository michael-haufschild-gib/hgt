import GaloisForLFunctions.HTGeometry.MeromorphicFractionRealization
import GaloisForLFunctions.HTGeometry.JetAtomDifferentiallyAlgebraic
import GaloisForLFunctions.HTGeometry.TripticTotalAtomSum

/-!
# The atom sum is differentially algebraic

Each jet of a line atom is a quotient of two entire functions: the base case is the theta
logarithmic derivative, and one differentiation of a quotient produces the next numerator and the
square of the denominator.  So every jet of a line atom is realized by a germ of the global
meromorphic field, and the germ inherits the jet's differential algebraicity.

The germs of the summands of the total atom sum therefore lie in the differentially algebraic
subfield, hence so does their combination, and realization carries the relation back: the canonical
normal form of the total atom sum satisfies a global algebraic differential equation.

* `exists_fraction_jetAtom`, `exists_realizesMero_jetAtom`;
* `differentiallyAlgebraic_toMeromorphicNFOn_totalAtomSum`.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero

attribute [local instance] meromorphicEllipticCompositumComplexAlgebraMero

variable {σ : ℂ}

/-- **Every jet of a line atom is a quotient of entire functions.**  The base case is the theta
logarithmic derivative; the inductive step is the quotient rule. -/
theorem exists_fraction_jetAtom (hσ : 0 < σ.im) (q : ℂ) (j : ℕ) :
    ∃ A B : ℂ → ℂ, AnalyticOnNhd ℂ A (Set.univ : Set ℂ) ∧
      AnalyticOnNhd ℂ B (Set.univ : Set ℂ) ∧ (∃ z₀ : ℂ, B z₀ ≠ 0) ∧
      ∀ z, B z ≠ 0 → jetAtom σ q j z = A z / B z := by
  induction j with
  | zero =>
      refine ⟨fun z ↦ jacobiTheta₂' (z - q) σ, fun z ↦ jacobiTheta₂ (z - q) σ, ?_, ?_, ?_, ?_⟩
      · intro z _
        exact AnalyticAt.comp (g := fun x : ℂ ↦ jacobiTheta₂' x σ) (f := fun w : ℂ ↦ w - q)
          (jacobiTheta₂'_analyticOnNhd_fst σ hσ (z - q) (Set.mem_univ _))
          (analyticAt_id.sub analyticAt_const)
      · intro z _
        exact AnalyticAt.comp (g := fun x : ℂ ↦ jacobiTheta₂ x σ) (f := fun w : ℂ ↦ w - q)
          (jacobiTheta₂_analyticOnNhd_fst σ hσ (z - q) (Set.mem_univ _))
          (analyticAt_id.sub analyticAt_const)
      · obtain ⟨w, hw⟩ := (eventually_nhdsNE_notMem_atomPoleSet hσ q 0).exists
        exact ⟨w, fun h ↦ hw ((mem_atomPoleSet_iff hσ q w).mpr h)⟩
      · intro z _
        show thetaSource σ (z - q) = jacobiTheta₂' (z - q) σ / jacobiTheta₂ (z - q) σ
        rw [thetaSource, logDeriv_apply, deriv_jacobiTheta₂_fst hσ]
  | succ k ih =>
      obtain ⟨A, B, hA, hB, ⟨z₀, hz₀⟩, hid⟩ := ih
      have hBcont : Continuous B :=
        continuous_iff_continuousAt.mpr fun z ↦ (hB z (Set.mem_univ z)).continuousAt
      have hopen : IsOpen {w : ℂ | B w ≠ 0} := hBcont.isOpen_preimage _ isOpen_compl_singleton
      have hA' : AnalyticOnNhd ℂ (deriv A) (Set.univ : Set ℂ) :=
        fun w _ ↦ (hA w (Set.mem_univ w)).deriv
      have hB' : AnalyticOnNhd ℂ (deriv B) (Set.univ : Set ℂ) :=
        fun w _ ↦ (hB w (Set.mem_univ w)).deriv
      refine ⟨deriv A * B - A * deriv B, B * B, (hA'.mul hB).sub (hA.mul hB'),
        hB.mul hB, ⟨z₀, mul_ne_zero hz₀ hz₀⟩, fun z hz ↦ ?_⟩
      have hBz : B z ≠ 0 := fun h ↦ hz (by simp [Pi.mul_apply, h])
      have heq : jetAtom σ q k =ᶠ[𝓝 z] fun w ↦ A w / B w := by
        filter_upwards [hopen.mem_nhds hBz] with w hw
        exact hid w hw
      have hdd : deriv (fun w ↦ A w / B w) z
          = (deriv A z * B z - A z * deriv B z) / B z ^ 2 :=
        deriv_fun_div (hA z (Set.mem_univ z)).differentiableAt
          (hB z (Set.mem_univ z)).differentiableAt hBz
      rw [← deriv_jetAtom σ q k, heq.deriv_eq, hdd]
      simp only [Pi.sub_apply, Pi.mul_apply, sq]

/-- A function realized by a differentially algebraic germ. -/
def RealizedDA (f : ℂ → ℂ) : Prop :=
  ∃ x : meroField (Set.univ : Set ℂ), RealizesMero x f ∧ x ∈ daOverRatFuncField

theorem RealizedDA.differentiallyAlgebraic {f : ℂ → ℂ} (h : RealizedDA f) :
    DifferentiallyAlgebraic (toMeromorphicNFOn f (Set.univ : Set ℂ)) := by
  obtain ⟨x, hx, hmem⟩ := h
  exact differentiallyAlgebraic_of_realizesMero hx ((mem_daOverRatFuncField_iff x).mp hmem)

theorem RealizedDA.const_mul {f : ℂ → ℂ} (h : RealizedDA f) (c : ℂ) :
    RealizedDA (fun z ↦ c * f z) := by
  obtain ⟨x, hx, hmem⟩ := h
  refine ⟨algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
    (constToAnalytic Set.univ c) * x, realizesMero_const_mul c hx, ?_⟩
  exact mul_mem (daOverRatFuncField.algebraMap_mem c) hmem

theorem RealizedDA.add {f g : ℂ → ℂ} (hf : RealizedDA f) (hg : RealizedDA g) :
    RealizedDA (f + g) := by
  obtain ⟨x, hx, hxmem⟩ := hf
  obtain ⟨y, hy, hymem⟩ := hg
  exact ⟨x + y, realizesMero_add hx hy, add_mem hxmem hymem⟩

theorem RealizedDA.sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (h : ∀ i ∈ s, RealizedDA (f i)) : RealizedDA (∑ i ∈ s, f i) := by
  classical
  choose x hx hmem using h
  refine ⟨∑ i ∈ s.attach, x i i.2, ?_, sum_mem fun i _ ↦ hmem i i.2⟩
  have hsum : (∑ i ∈ s, f i) = ∑ i ∈ s.attach, f i := by
    rw [Finset.sum_attach s f]
  rw [hsum]
  exact realizesMero_sum s.attach (fun i ↦ x i i.2) (fun i ↦ f i) fun i _ ↦ hx i i.2

/-- **Every jet of a line atom is realized by a differentially algebraic germ.** -/
theorem realizedDA_jetAtom (hσ : 0 < σ.im) (q : ℂ) (j : ℕ) : RealizedDA (jetAtom σ q j) := by
  obtain ⟨A, B, hA, hB, ⟨z₀, hz₀⟩, hid⟩ := exists_fraction_jetAtom hσ q j
  set a : analyticSubring (Set.univ : Set ℂ) := analyticFunctionElement A hA with hadef
  set b : analyticSubring (Set.univ : Set ℂ) := analyticFunctionElement B hB with hbdef
  have hb0 : b ≠ 0 := by
    intro h
    apply hz₀
    have hval := congrArg Subtype.val h
    rw [ZeroMemClass.coe_zero] at hval
    change ((B : ℂ → ℂ) : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) = 0 at hval
    rw [← Germ.coe_zero, Germ.coe_eq] at hval
    exact eventually_principal.mp hval z₀ (Set.mem_univ z₀)
  have hreal : RealizesMero
      (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) a /
        algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) b)
      (jetAtom σ q j) :=
    ⟨a, b, A, B, hb0, hA, hB, rfl, rfl, rfl, hid⟩
  exact ⟨_, hreal, (mem_daOverRatFuncField_iff _).mpr
    (differentialAlgebraicOver_of_realizesMero hreal
      (differentiallyAlgebraic_toMeromorphicNFOn_jetAtom σ q hσ j))⟩

/-- **The atom sum of one order in one direction is realized by a differentially algebraic
germ.** -/
theorem realizedDA_rowAtomSum (hσ : 0 < σ.im) (F : ℂ → ℂ) (τ : ℂ) (j : ℕ) (R : Finset ℂ) :
    RealizedDA (rowAtomSum F τ σ j R) := by
  classical
  have hfun : rowAtomSum F τ σ j R
      = ∑ q ∈ R, fun z ↦ (rowCoeff F τ (-((j : ℤ) + 1)) q /
          (((-1 : ℂ) ^ j * (j.factorial : ℂ)) * (lineCount σ R q : ℂ)))
        * jetAtom σ (q - thetaHalfPeriod σ) j z := by
    funext z
    simp only [rowAtomSum, Finset.sum_apply]
  rw [hfun]
  exact RealizedDA.sum R _ fun q _ ↦ (realizedDA_jetAtom hσ _ j).const_mul _

/-- **The total atom sum is realized by a differentially algebraic germ.** -/
theorem realizedDA_totalAtomSum {τ : ℂ} (hτ : 0 < τ.im) (hσ : 0 < σ.im) (F : ℂ → ℂ) (n : ℕ)
    (Rτ Rσ : ℕ → Finset ℂ) : RealizedDA (totalAtomSum F τ σ n Rτ Rσ) := by
  classical
  have hfun : totalAtomSum F τ σ n Rτ Rσ
      = (∑ j ∈ Finset.range n, rowAtomSum F τ σ j (Rτ j))
        + ∑ j ∈ Finset.range n, rowAtomSum F σ τ j (Rσ j) := by
    funext z
    simp only [totalAtomSum, Pi.add_apply, Finset.sum_apply]
  rw [hfun]
  exact (RealizedDA.sum _ _ fun j _ ↦ realizedDA_rowAtomSum hσ F τ j (Rτ j)).add
    (RealizedDA.sum _ _ fun j _ ↦ realizedDA_rowAtomSum hτ F σ j (Rσ j))

/-- **The total atom sum satisfies a global algebraic differential equation.** -/
theorem differentiallyAlgebraic_toMeromorphicNFOn_totalAtomSum {τ : ℂ} (hτ : 0 < τ.im)
    (hσ : 0 < σ.im) (F : ℂ → ℂ) (n : ℕ) (Rτ Rσ : ℕ → Finset ℂ) :
    DifferentiallyAlgebraic
      (toMeromorphicNFOn (totalAtomSum F τ σ n Rτ Rσ) (Set.univ : Set ℂ)) :=
  (realizedDA_totalAtomSum hτ hσ F n Rτ Rσ).differentiallyAlgebraic

end

end GaloisForLFunctions.HTGeometry
