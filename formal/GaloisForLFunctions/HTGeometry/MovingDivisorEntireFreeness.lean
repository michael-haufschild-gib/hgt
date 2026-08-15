import GaloisForLFunctions.HTGeometry.MovingDivisorEvenFreeness
import GaloisForLFunctions.HTGeometry.MovingDivisorEvenProduct
import GaloisForLFunctions.HTGeometry.LogDerivFamilyFreeness
import GaloisForLFunctions.HTGeometry.HerglotzFullTranslationRegularizedFreeness
import GaloisForLFunctions.HTGeometry.MovingCanonicalUpperEndDifferentialIndependence
import GaloisForLFunctions.HTGeometry.FamilyPowerGauge

/-!
# From carrier freeness to product freeness for a moving divisor

The symmetric canonical product of a moving divisor is nonvanishing off the real axis and satisfies
`E' = -(evenCarrier) E` there.  Hence the translated carrier family being relation-free forces the
translated product family, and every positive power of it, to be relation-free as well.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

open ClassicalAnalyticNevanlinnaCarrierFamily

noncomputable section

namespace MovingDivisor

variable (Dv : MovingDivisor)

/-- The odd carrier is analytic off the real axis. -/
theorem analyticAt_evenCarrierB (θ : BoundedRealSequence) {z : ℂ} (hz : z.im ≠ 0) :
    AnalyticAt ℂ (Dv.evenCarrierB θ) z := by
  have h1 := Dv.analyticAt_logDerivativeB_of_im_ne_zero θ hz
  have h2 := Dv.analyticAt_logDerivativeB_of_im_ne_zero θ (z := -z) (by simpa using hz)
  have hneg : AnalyticAt ℂ (fun w : ℂ => -w) z := by fun_prop
  exact h1.sub (h2.comp hneg)

/-- The symmetric canonical product has no zero off the real axis. -/
theorem evenCanonicalProduct_ne_zero_of_im_ne_zero (θ : ℕ → ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Dv.evenCanonicalProduct θ z ≠ 0 := by
  intro hcon
  rw [Dv.evenCanonicalProduct_eq_zero_iff θ] at hcon
  obtain ⟨n, hn | hn⟩ := hcon
  · exact hz (by rw [hn]; simp)
  · exact hz (by rw [hn]; simp)

/-- The differential equation satisfied by the symmetric canonical product off the real axis. -/
theorem deriv_evenCanonicalProduct_eq (θ : ℕ → ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    deriv (Dv.evenCanonicalProduct θ) z
      = -(Dv.evenCarrier θ z) * Dv.evenCanonicalProduct θ z := by
  have hzpos : ∀ n, z ≠ (Dv.zero θ n : ℂ) := by
    intro n hcon
    exact hz (by rw [hcon]; simp)
  have hzneg : ∀ n, z ≠ -(Dv.zero θ n : ℂ) := by
    intro n hcon
    exact hz (by rw [hcon]; simp)
  have hne := Dv.evenCanonicalProduct_ne_zero_of_im_ne_zero θ hz
  have h := Dv.neg_logDeriv_evenCanonicalProduct_eq θ hzpos hzneg
  rw [logDeriv_apply] at h
  field_simp at h
  linear_combination -h

/-- The translated symmetric products are analytic on the common upper domain. -/
theorem analyticOnNhd_evenCanonicalProduct_translate (θ : ℕ → ℝ) (h : ℂ) (U : Set ℂ) :
    AnalyticOnNhd ℂ (fun z => Dv.evenCanonicalProduct θ (z + h)) U := by
  intro z _
  have hshift : AnalyticAt ℂ (fun w : ℂ => w + h) z := by fun_prop
  exact AnalyticAt.comp (g := Dv.evenCanonicalProduct θ) (f := fun w : ℂ => w + h) (x := z)
    (Dv.evenCanonicalProduct_analytic θ (z + h) (Set.mem_univ _)) hshift

/-- The derivative of a translated symmetric product off the real axis. -/
theorem deriv_evenCanonicalProduct_translate (θ : ℕ → ℝ) (h : ℂ) {z : ℂ}
    (hz : (z + h).im ≠ 0) :
    deriv (fun w => Dv.evenCanonicalProduct θ (w + h)) z
      = -(Dv.evenCarrier θ (z + h)) * Dv.evenCanonicalProduct θ (z + h) := by
  have hE : HasDerivAt (Dv.evenCanonicalProduct θ)
      (deriv (Dv.evenCanonicalProduct θ) (z + h)) (z + h) :=
    (Dv.evenCanonicalProduct_analytic θ (z + h) (Set.mem_univ _)).differentiableAt.hasDerivAt
  have hcomp : HasDerivAt (fun w => Dv.evenCanonicalProduct θ (w + h))
      (deriv (Dv.evenCanonicalProduct θ) (z + h)) z := hE.comp_add_const z h
  rw [hcomp.deriv, Dv.deriv_evenCanonicalProduct_eq θ hz]

end MovingDivisor

/-- **Carrier freeness upgrades to product freeness.**  If the translated odd carriers of a moving
divisor admit no algebraic differential relation on the common upper domain, neither do the
translated symmetric canonical products. -/
theorem not_familyDifferentiallyAlgebraicOn_evenCanonicalProduct_translates
    (Dv : MovingDivisor) (θ : BoundedRealSequence) {m : ℕ}
    (shift : InjectiveShiftConfiguration (Fin m))
    (hcar : ¬ FamilyDifferentiallyAlgebraicOn
      (fun i z => Dv.evenCarrierB θ (z + shift.1 i)) (commonUpperTranslationDomain shift)) :
    ¬ FamilyDifferentiallyAlgebraicOn
      (fun i z => Dv.evenCanonicalProduct (θ : ℕ → ℝ) (z + shift.1 i))
      (commonUpperTranslationDomain shift) := by
  set U : Set ℂ := commonUpperTranslationDomain shift with hU
  have hUo : IsOpen U := isOpen_commonUpperTranslationDomain shift
  have hUc : IsPreconnected U := commonUpperTranslationDomain_isPreconnected shift
  have hUne : U.Nonempty := by
    obtain ⟨z, hz, -⟩ := commonUpperTranslationDomain_meets_upperTail shift 0
    exact ⟨z, hz⟩
  have him : ∀ z ∈ U, ∀ i, (z + shift.1 i).im ≠ 0 := by
    intro z hz i
    exact ne_of_gt (hz i)
  have hcarAn : ∀ i, AnalyticOnNhd ℂ (fun z => Dv.evenCarrierB θ (z + shift.1 i)) U := by
    intro i z hz
    have hshift : AnalyticAt ℂ (fun w : ℂ => w + shift.1 i) z := by fun_prop
    exact AnalyticAt.comp (g := Dv.evenCarrierB θ) (f := fun w : ℂ => w + shift.1 i) (x := z)
      (Dv.analyticAt_evenCarrierB θ (him z hz i)) hshift
  have hcarSm : ∀ z ∈ U, ∀ i,
      ContDiffAt ℂ (⊤ : ℕ∞) (fun w => Dv.evenCarrierB θ (w + shift.1 i)) z :=
    fun z hz i => (hcarAn i z hz).contDiffAt
  refine not_familyDifferentiallyAlgebraicOn_of_logDerivFamily hUo hUc hUne
    (sigma := fun i z => -(Dv.evenCarrierB θ (z + shift.1 i)))
    (fun i z hz => ((hcarAn i) z hz).neg)
    (fun i => Dv.analyticOnNhd_evenCanonicalProduct_translate _ _ U)
    (fun i z hz => Dv.evenCanonicalProduct_ne_zero_of_im_ne_zero _ (him z hz i))
    (fun i z hz => Dv.deriv_evenCanonicalProduct_translate _ _ (him z hz i))
    (not_familyDifferentiallyAlgebraicOn_neg hcarSm hcar)

/-- **Every positive power of the translated symmetric products is relation-free.** -/
theorem not_familyDifferentiallyAlgebraicOn_evenCanonicalProduct_translates_pow
    (Dv : MovingDivisor) (θ : BoundedRealSequence) {m : ℕ}
    (shift : InjectiveShiftConfiguration (Fin m)) {N : ℕ} (hN : N ≠ 0)
    (hcar : ¬ FamilyDifferentiallyAlgebraicOn
      (fun i z => Dv.evenCarrierB θ (z + shift.1 i)) (commonUpperTranslationDomain shift)) :
    ¬ FamilyDifferentiallyAlgebraicOn
      (fun i z => (Dv.evenCanonicalProduct (θ : ℕ → ℝ) (z + shift.1 i)) ^ N)
      (commonUpperTranslationDomain shift) := by
  refine not_familyDifferentiallyAlgebraicOn_pow _ hN ?_
    (not_familyDifferentiallyAlgebraicOn_evenCanonicalProduct_translates Dv θ shift hcar)
  intro z hz i
  exact (Dv.analyticOnNhd_evenCanonicalProduct_translate (θ : ℕ → ℝ) (shift.1 i)
    (commonUpperTranslationDomain shift) z hz).contDiffAt

end

end GaloisForLFunctions.HTGeometry
