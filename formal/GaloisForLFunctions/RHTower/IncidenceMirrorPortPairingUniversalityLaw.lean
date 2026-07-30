import GaloisForLFunctions.RHTower.IncidenceMirrorOrientation
import GaloisForLFunctions.RHTower.IncidenceRamification

/-!
# Incidence-mirror port pairing

For a functional-equation pencil whose incidence mirror is reciprocal with positive real
constant, the real critical-line incidence satisfies `r(-τ) = λ / r(τ)`.  Differentiating this
identity pairs its critical heights.  The incidence ramification criterion then pairs the
multiple-zero pencil members carried by those heights.
-/

namespace RHTower

open Complex

noncomputable section

/-- A differentiable nowhere-zero real function satisfying reciprocal reflection has a
reflection-invariant critical set. -/
theorem deriv_neg_eq_zero_iff_of_reciprocal
    (f : ℝ → ℝ) (lam : ℝ)
    (hf : Differentiable ℝ f)
    (hzero : ∀ t, f t ≠ 0)
    (hlam : lam ≠ 0)
    (hreflect : ∀ t, f (-t) = lam / f t)
    (t : ℝ) :
    deriv f (-t) = 0 ↔ deriv f t = 0 := by
  have hneg :
      HasDerivAt (fun u : ℝ => f (-u)) (-deriv f (-t)) t := by
    simpa using! (hf (-t)).hasDerivAt.scomp t (hasDerivAt_id t).neg
  have hrecip :
      HasDerivAt (fun u : ℝ => lam / f u)
        ((0 * f t - lam * deriv f t) / f t ^ 2) t :=
    (hasDerivAt_const t lam).div (hf t).hasDerivAt (hzero t)
  have heq : (fun u : ℝ => f (-u)) = fun u => lam / f u :=
    funext hreflect
  rw [heq] at hneg
  have hderiv :
      -deriv f (-t) = (0 * f t - lam * deriv f t) / f t ^ 2 :=
    hneg.unique hrecip
  constructor
  · intro hleft
    have hquot : (-lam * deriv f t) / f t ^ 2 = 0 := by
      simpa [hleft] using hderiv.symm
    have hnum : -lam * deriv f t = 0 :=
      (div_eq_zero_iff.mp hquot).resolve_right
        (pow_ne_zero 2 (hzero t))
    exact (mul_eq_zero.mp hnum).resolve_left (neg_ne_zero.mpr hlam)
  · intro hright
    have hnegZero : -deriv f (-t) = 0 := by
      simpa [hright] using hderiv
    exact neg_eq_zero.mp hnegZero

/-- The FE reciprocal mirror restricts to the exact real seam identity
`r(-τ)=λ/r(τ)`. -/
theorem seamIncidence_neg_eq_real_div
    {Λ₁ Λ₂ : ℂ → ℂ} {ε ε' : ℂ}
    (hFE₁ : ∀ s, Λ₁ (1 - s) = ε * Λ₂ s)
    (hFE₂ : ∀ s, Λ₂ (1 - s) = ε' * Λ₁ s)
    (hε : ε ≠ 0)
    (hΛ₂ : ∀ t : ℝ, Λ₂ (linePt t) ≠ 0)
    (hr₁ : ∀ t : ℝ, (Λ₁ (linePt t)).im = 0)
    (hr₂ : ∀ t : ℝ, (Λ₂ (linePt t)).im = 0)
    {lam : ℝ} (hratio : ε' / ε = (lam : ℂ))
    (t : ℝ) :
    seamIncidence Λ₁ Λ₂ (-t) = lam / seamIncidence Λ₁ Λ₂ t := by
  have hline : 1 - linePt t = linePt (-t) := by
    unfold linePt
    push_cast
    ring
  have hmirror :=
    incidence_mirror hFE₁ hFE₂ hε (hΛ₂ t)
  rw [hline, hratio] at hmirror
  have hsource :
      incidence Λ₁ Λ₂ (linePt t) =
        ((seamIncidence Λ₁ Λ₂ t : ℝ) : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa [seamIncidence] using
        incidence_im_eq_zero_on_line (hr₁ t) (hr₂ t)
  have htarget :
      incidence Λ₁ Λ₂ (linePt (-t)) =
        ((seamIncidence Λ₁ Λ₂ (-t) : ℝ) : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa [seamIncidence] using
        incidence_im_eq_zero_on_line (hr₁ (-t)) (hr₂ (-t))
  rw [hsource, htarget, ← Complex.ofReal_div] at hmirror
  exact Complex.ofReal_injective hmirror

/-- **Incidence-mirror port-pairing universality law.**  Under an analytic real-seam FE pencil
with positive-real reciprocal constant and no seam zeros of either carrier, seam values transform
reciprocally, critical heights occur in reflected pairs, and the associated order-at-least-two
pencil ports occur in the same reflected pairs. -/
theorem incidenceMirrorPortPairingUniversality
    {Λ₁ Λ₂ : ℂ → ℂ} {ε ε' : ℂ}
    (hFE₁ : ∀ s, Λ₁ (1 - s) = ε * Λ₂ s)
    (hFE₂ : ∀ s, Λ₂ (1 - s) = ε' * Λ₁ s)
    (hε : ε ≠ 0)
    (ha₁ : ∀ t : ℝ, AnalyticAt ℂ Λ₁ (linePt t))
    (ha₂ : ∀ t : ℝ, AnalyticAt ℂ Λ₂ (linePt t))
    (hΛ₁ : ∀ t : ℝ, Λ₁ (linePt t) ≠ 0)
    (hΛ₂ : ∀ t : ℝ, Λ₂ (linePt t) ≠ 0)
    (hr₁ : ∀ t : ℝ, (Λ₁ (linePt t)).im = 0)
    (hr₂ : ∀ t : ℝ, (Λ₂ (linePt t)).im = 0)
    {lam : ℝ} (hlam : 0 < lam) (hratio : ε' / ε = (lam : ℂ)) :
    (∀ t : ℝ,
      seamIncidence Λ₁ Λ₂ (-t) = lam / seamIncidence Λ₁ Λ₂ t) ∧
      (∀ t : ℝ,
        deriv (seamIncidence Λ₁ Λ₂) (-t) = 0 ↔
          deriv (seamIncidence Λ₁ Λ₂) t = 0) ∧
      ∀ t : ℝ,
        ((2 : ℕ∞) ≤ analyticOrderAt
          (pencil Λ₁ Λ₂ (incidence Λ₁ Λ₂ (linePt (-t))) 1)
          (linePt (-t)) ↔
        (2 : ℕ∞) ≤ analyticOrderAt
          (pencil Λ₁ Λ₂ (incidence Λ₁ Λ₂ (linePt t)) 1)
          (linePt t)) := by
  have hreflect : ∀ t : ℝ,
      seamIncidence Λ₁ Λ₂ (-t) = lam / seamIncidence Λ₁ Λ₂ t :=
    seamIncidence_neg_eq_real_div hFE₁ hFE₂ hε hΛ₂ hr₁ hr₂ hratio
  have hdiff : Differentiable ℝ (seamIncidence Λ₁ Λ₂) := by
    intro t
    exact (seamIncidence_analyticAt (ha₁ t) (ha₂ t) (hΛ₁ t)).differentiableAt
  have hseamZero : ∀ t : ℝ, seamIncidence Λ₁ Λ₂ t ≠ 0 := by
    intro t hzero
    have hreal :
        incidence Λ₁ Λ₂ (linePt t) =
          ((seamIncidence Λ₁ Λ₂ t : ℝ) : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa [seamIncidence] using
          incidence_im_eq_zero_on_line (hr₁ t) (hr₂ t)
    have hincidence : incidence Λ₁ Λ₂ (linePt t) = 0 := by
      rw [hreal, hzero]
      rfl
    exact hΛ₂ t ((incidence_eq_zero_iff (hΛ₁ t)).mp hincidence)
  have hcritical : ∀ t : ℝ,
      deriv (seamIncidence Λ₁ Λ₂) (-t) = 0 ↔
        deriv (seamIncidence Λ₁ Λ₂) t = 0 :=
    deriv_neg_eq_zero_iff_of_reciprocal
      (seamIncidence Λ₁ Λ₂) lam hdiff hseamZero (ne_of_gt hlam) hreflect
  refine ⟨hreflect, hcritical, ?_⟩
  intro t
  have hportNeg :=
    seam_critical_iff_port
      (ha₁ (-t)) (ha₂ (-t))
      (ha₁ (-t)).differentiableAt.hasDerivAt
      (ha₂ (-t)).differentiableAt.hasDerivAt
      (hΛ₁ (-t)) hr₁ hr₂
  have hport :=
    seam_critical_iff_port
      (ha₁ t) (ha₂ t)
      (ha₁ t).differentiableAt.hasDerivAt
      (ha₂ t).differentiableAt.hasDerivAt
      (hΛ₁ t) hr₁ hr₂
  exact hportNeg.symm.trans ((hcritical t).trans hport)

end

end RHTower
