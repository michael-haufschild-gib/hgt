import GaloisForLFunctions.HTGeometry.TranslateJetBlowUpData
import GaloisForLFunctions.HTGeometry.MovingCanonicalFiniteJetSubmersion

/-!
# Discharging the shift conditions

The translated jet family carries two hypotheses about the shift configuration: that the
non-distinguished jets are analytic at the sampled points, and that they do not vanish there.  Both
hold as soon as the other shifts sit strictly above the distinguished one in the imaginary direction.

The sampled points then lie in the open upper half-plane, where the log-derivative is analytic and —
being a Herglotz function of a positive discrete measure — has strictly positive imaginary part, so
it cannot vanish.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **The log-derivative has strictly positive imaginary part on the upper half-plane.**  Every term
of the series contributes `Im z / ‖ζₙ − z‖²`, all positive. -/
theorem movingCanonicalLogDerivative_im_pos (θ : BoundedRealSequence) {z : ℂ} (hz : 0 < z.im) :
    0 < (movingCanonicalLogDerivative θ z).im := by
  have hpole : ∀ n, z ≠ (movingCanonicalZero θ n : ℂ) := by
    intro n h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hsum := summable_movingCanonicalLogDerivative θ hpole
  have hterm : ∀ n : ℕ,
      ((((movingCanonicalZero θ n : ℂ) - z)⁻¹ - ((movingCanonicalZero θ n : ℂ))⁻¹).im)
        = z.im / Complex.normSq ((movingCanonicalZero θ n : ℂ) - z) := by
    intro n
    rw [Complex.sub_im, Complex.inv_im, Complex.inv_im]
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg, neg_zero,
      zero_div, sub_zero]
  have hpos : ∀ n : ℕ,
      0 < ((((movingCanonicalZero θ n : ℂ) - z)⁻¹ - ((movingCanonicalZero θ n : ℂ))⁻¹).im) := by
    intro n
    rw [hterm n]
    have hne : ((movingCanonicalZero θ n : ℂ) - z) ≠ 0 := sub_ne_zero.mpr (Ne.symm (hpole n))
    have hnorm : 0 < Complex.normSq ((movingCanonicalZero θ n : ℂ) - z) :=
      Complex.normSq_pos.mpr hne
    positivity
  have hsumim : Summable
      (fun n : ℕ => ((((movingCanonicalZero θ n : ℂ) - z)⁻¹
        - ((movingCanonicalZero θ n : ℂ))⁻¹).im)) := hsum.mapL Complex.imCLM
  rw [movingCanonicalLogDerivative, realLogDerivative, Complex.im_tsum hsum]
  refine lt_of_lt_of_le (hpos 0) ?_
  exact hsumim.le_tsum 0 fun j _ => (hpos j).le

theorem movingCanonicalLogDerivative_ne_zero_of_im_pos (θ : BoundedRealSequence) {z : ℂ}
    (hz : 0 < z.im) : movingCanonicalLogDerivative θ z ≠ 0 := by
  intro h
  have := movingCanonicalLogDerivative_im_pos θ hz
  rw [h] at this
  simp at this

/-- A translated jet is analytic wherever the translate lands in the upper half-plane. -/
theorem analyticAt_translate_jet {θ : BoundedRealSequence} (r : ℕ) (σ : ℂ) {ζ : ℂ}
    (hpos : 0 < (ζ + σ).im) :
    AnalyticAt ℂ (fun w => iteratedDeriv r (movingCanonicalLogDerivative θ) (w + σ)) ζ := by
  have hinner : AnalyticAt ℂ (fun w : ℂ => w + σ) ζ := analyticAt_id.add analyticAt_const
  have houter : AnalyticAt ℂ (iteratedDeriv r (movingCanonicalLogDerivative θ)) (ζ + σ) :=
    analyticAt_iteratedDeriv' (analyticAt_movingCanonicalLogDerivative θ hpos) r
  have hcomp : AnalyticAt ℂ
      ((iteratedDeriv r (movingCanonicalLogDerivative θ)) ∘ (fun w : ℂ => w + σ)) ζ :=
    AnalyticAt.comp (g := iteratedDeriv r (movingCanonicalLogDerivative θ))
      (f := fun w : ℂ => w + σ) houter hinner
  exact hcomp

/-- **The blow-up data, with the shift conditions discharged.**  Other shifts strictly above the
distinguished one put every sample point in the upper half-plane, where the log-derivative is
analytic and nonvanishing. -/
theorem multiBlowUpData_translateJets_of_shiftOrder {n : ℕ} (θ : BoundedRealSequence)
    (m : Fin n → ℕ) (σ : Fin n → ℂ) (k₀ : Fin n)
    (hshift : ∀ k, k ≠ k₀ → (σ k₀).im < (σ k).im)
    (hm : ∀ k, k ≠ k₀ → m k = 0) (hσ0 : (σ k₀).im = 0)
    {Z : Set ℂ} (hZ : Z.Infinite)
    (hzero : ∀ ζ ∈ Z, ∃ p : ℕ, ζ = (movingCanonicalZero θ p : ℂ) - σ k₀) :
    MultiBlowUpData upperHalfPlane
      (fun k w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) Z
      (translateJetRate m k₀) := by
  have hupperPt : ∀ ζ ∈ Z, ∀ k, k ≠ k₀ → 0 < (ζ + σ k).im := by
    intro ζ hζ k hk
    obtain ⟨p, hp⟩ := hzero ζ hζ
    have him : (ζ + σ k).im = (σ k).im - (σ k₀).im := by
      rw [hp]
      simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, zero_sub]
      ring
    rw [him]
    exact sub_pos.mpr (hshift k hk)
  have hS : ∀ ζ ∈ Z, ∀ y : ℝ, 0 < y → ζ + (y : ℂ) * Complex.I ∈ upperHalfPlane := by
    intro ζ hζ y hy
    obtain ⟨p, hp⟩ := hzero ζ hζ
    show 0 < (ζ + (y : ℂ) * Complex.I).im
    have him : (ζ + (y : ℂ) * Complex.I).im = y := by
      rw [hp]
      simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, hσ0]
      ring
    rw [him]
    exact hy
  refine multiBlowUpData_translateJets θ m σ k₀ hZ hS hzero
    (fun ζ hζ k hk => analyticAt_translate_jet (m k) (σ k) (hupperPt ζ hζ k hk))
    (fun ζ hζ k hk => ?_)
  rw [hm k hk, iteratedDeriv_zero]
  exact movingCanonicalLogDerivative_ne_zero_of_im_pos θ (hupperPt ζ hζ k hk)

theorem injective_blowUpOrder_translateJetRate {κ : Type*} {n : ℕ} (m : Fin n → ℕ) (k₀ : Fin n)
    {exponent : κ → (Fin n →₀ ℕ)} (hsep : Function.Injective fun a => exponent a k₀) :
    Function.Injective fun a => blowUpOrder (translateJetRate m k₀) (exponent a) := by
  intro a b hab
  simp only [blowUpOrder_translateJetRate] at hab
  exact hsep (Nat.eq_of_mul_eq_mul_right (Nat.succ_pos _) hab)

/-- **The translated jet box, with the shift conditions discharged.** -/
theorem linearIndependent_restrict_expandedMonomialFamily_translateJets_of_shiftOrder
    {κ : Type*} [Fintype κ] [DecidableEq κ] {n q : ℕ} (θ : BoundedRealSequence)
    (m : Fin n → ℕ) (σ : Fin n → ℂ) (k₀ : Fin n)
    (hshift : ∀ k, k ≠ k₀ → (σ k₀).im < (σ k).im)
    (hm : ∀ k, k ≠ k₀ → m k = 0) (hσ0 : (σ k₀).im = 0)
    {Z : Set ℂ} (hZ : Z.Infinite)
    (hzero : ∀ ζ ∈ Z, ∃ p : ℕ, ζ = (movingCanonicalZero θ p : ℂ) - σ k₀)
    {exponent : κ → (Fin n →₀ ℕ)}
    (hsep : Function.Injective fun a => exponent a k₀) :
    LinearIndependent ℂ (fun c : κ × Fin (q + 1) =>
      Set.restrict upperHalfPlane (expandedMonomialFamily
        (fun k w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k))
        exponent q c)) :=
  linearIndependent_restrict_expandedMonomialFamily_of_multiBlowUp
    (multiBlowUpData_translateJets_of_shiftOrder θ m σ k₀ hshift hm hσ0 hZ hzero)
    (injective_blowUpOrder_translateJetRate m k₀ hsep)

/-- **The full-rank datum for the moving canonical jets.**  A node packet in the upper half-plane,
pairwise distinct, on which the expanded evaluation map of the translated jet family is injective. -/
theorem exists_row_packet_upperHalfPlane_translateJets
    {κ row : Type*} [Fintype κ] [DecidableEq κ] [Fintype row] {n q : ℕ}
    (θ : BoundedRealSequence) (m : Fin n → ℕ) (σ : Fin n → ℂ) (k₀ : Fin n)
    (hshift : ∀ k, k ≠ k₀ → (σ k₀).im < (σ k).im)
    (hm : ∀ k, k ≠ k₀ → m k = 0) (hσ0 : (σ k₀).im = 0)
    {Z : Set ℂ} (hZ : Z.Infinite)
    (hzero : ∀ ζ ∈ Z, ∃ p : ℕ, ζ = (movingCanonicalZero θ p : ℂ) - σ k₀)
    {exponent : κ → (Fin n →₀ ℕ)}
    (hsep : Function.Injective fun a => exponent a k₀)
    (f : κ × Fin (q + 1) → row) (hf : Function.Injective f) :
    ∃ z : row → ℂ, (∀ b, 0 < (z b).im) ∧ Function.Injective z ∧
      Function.Injective (expandedDifferentialEvaluationMatrix q n z exponent
        (fun p => iteratedDeriv (m p.2) (movingCanonicalLogDerivative θ) (z p.1 + σ p.2))).mulVec :=
  exists_row_packet_upperHalfPlane_of_multiBlowUp infinite_upperHalfPlane
    (multiBlowUpData_translateJets_of_shiftOrder θ m σ k₀ hshift hm hσ0 hZ hzero)
    (injective_blowUpOrder_translateJetRate m k₀ hsep) f hf

end GaloisForLFunctions.HTGeometry
