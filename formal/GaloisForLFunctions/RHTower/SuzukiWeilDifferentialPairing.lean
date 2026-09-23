import GaloisForLFunctions.RHTower.SuzukiWeilTransformRaySeries

/-!
# The differential operator `D` of Suzuki eq. (1.8) against the exponential slope

`(D psi)(t) = i psi'(t)` (eq. 1.8).  Step 2 of the route to Lemma 3.2: the `q`-th ray coefficient of
`conj(Phat_{D psi})` collapses to a Fourier integral with the spectral point pulled out in front,

`integral of (e^{-i w t} - 1) * conj((D psi)(t)) dt  =  w * integral of e^{-i w t} conj(psi t) dt`,

so the ray `a_q / (gamma_q (z - gamma_q))` becomes `(Fourier of conj psi at -gamma_q)/(z - gamma_q)`
— exactly the shape of Suzuki eq. (3.8), and the shape `suzuki_lemma_two_one` (Su22 Lemma 2.1)
consumes.

The engine is `integral_expSlope_mul_deriv`: integration by parts over a window containing the
support, with both boundary terms killed by `psi` vanishing there, then transported back to the whole
line by `setIntegral_eq_integral_of_forall_compl_eq_zero`.  Note `deriv psi` inherits the support
bound (`deriv_eq_zero_of_supp`), since `{t | T < |t|}` is open.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section

/-! ## Integration by parts for the exponential slope -/

theorem hasDerivAt_expSlopeKernel (w : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (-(I * w * (s : ℂ))) - 1)
      (-(I * w) * Complex.exp (-(I * w * (t : ℂ)))) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => -(I * w) * ((s : ℝ) : ℂ)) (-(I * w)) t := by
    simpa using h1.const_mul (-(I * w))
  have h3 : HasDerivAt (fun s : ℝ => Complex.exp (-(I * w) * ((s : ℝ) : ℂ)))
      (Complex.exp (-(I * w) * ((t : ℝ) : ℂ)) * (-(I * w))) t := h2.cexp
  have hrw : (fun s : ℝ => Complex.exp (-(I * w * (s : ℂ))) - 1)
      = fun s : ℝ => Complex.exp (-(I * w) * ((s : ℝ) : ℂ)) - 1 := by
    funext s
    congr 2
    ring
  rw [hrw]
  have h4 := h3.sub_const 1
  have hval : Complex.exp (-(I * w) * ((t : ℝ) : ℂ)) * (-(I * w))
      = -(I * w) * Complex.exp (-(I * w * (t : ℂ))) := by
    rw [show -(I * w) * ((t : ℝ) : ℂ) = -(I * w * ((t : ℝ) : ℂ)) by ring]
    ring
  rwa [hval] at h4

theorem deriv_eq_zero_of_supp {g : ℝ → ℂ} {T : ℝ} (hsupp : ∀ t : ℝ, T < |t| → g t = 0)
    {t : ℝ} (ht : T < |t|) : deriv g t = 0 := by
  have hopen : IsOpen {s : ℝ | T < |s|} := isOpen_lt continuous_const continuous_abs
  have hev : g =ᶠ[nhds t] fun _ => 0 := by
    filter_upwards [hopen.mem_nhds ht] with s hs
    exact hsupp s hs
  rw [hev.deriv_eq]
  exact deriv_const t 0

theorem integral_eq_intervalIntegral_of_supp {f : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hsupp : ∀ t : ℝ, T < |t| → f t = 0) :
    (∫ t : ℝ, f t) = ∫ t in (-(T + 1))..(T + 1), f t := by
  have hle : -(T + 1) ≤ T + 1 := by linarith
  rw [intervalIntegral.integral_of_le hle]
  refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
  intro x hx
  refine hsupp x ?_
  by_contra hc
  push_neg at hc
  have hb := abs_le.mp hc
  exact hx ⟨by linarith [hb.1], by linarith [hb.2]⟩

theorem hasCompactSupport_of_supp {f : ℝ → ℂ} {T : ℝ}
    (hsupp : ∀ t : ℝ, T < |t| → f t = 0) : HasCompactSupport f := by
  refine HasCompactSupport.intro (K := Set.Icc (-T) T) isCompact_Icc ?_
  intro x hx
  refine hsupp x ?_
  by_contra hc
  push_neg at hc
  have hb := abs_le.mp hc
  exact hx ⟨hb.1, hb.2⟩

/-- **Integration by parts.**  For a `C¹` function of compact support,
`∫ (e^{-iwt} - 1) g'(t) dt = i w ∫ e^{-iwt} g(t) dt`. -/
theorem integral_expSlope_mul_deriv {g : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hg : ContDiff ℝ 1 g) (hsupp : ∀ t : ℝ, T < |t| → g t = 0) (w : ℂ) :
    (∫ t : ℝ, (Complex.exp (-(I * w * (t : ℂ))) - 1) * deriv g t)
      = I * w * ∫ t : ℝ, Complex.exp (-(I * w * (t : ℂ))) * g t := by
  have hle : -(T + 1) ≤ T + 1 := by linarith
  have hgd : ∀ t : ℝ, HasDerivAt g (deriv g t) t := fun t =>
    (hg.differentiable (by norm_num) t).hasDerivAt
  have hgc : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  have hkerC : Continuous (fun s : ℝ => Complex.exp (-(I * w * (s : ℂ))) - 1) := by fun_prop
  have hkerC' : Continuous (fun s : ℝ => -(I * w) * Complex.exp (-(I * w * (s : ℂ)))) := by
    fun_prop
  have hga : g (-(T + 1)) = 0 := by
    refine hsupp _ ?_
    rw [abs_neg, abs_of_nonneg (by linarith)]
    linarith
  have hgb : g (T + 1) = 0 := by
    refine hsupp _ ?_
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := -(T + 1)) (b := T + 1)
    (u := fun s : ℝ => Complex.exp (-(I * w * (s : ℂ))) - 1)
    (u' := fun s : ℝ => -(I * w) * Complex.exp (-(I * w * (s : ℂ))))
    (v := g) (v' := deriv g)
    (fun x _ => hasDerivAt_expSlopeKernel w x) (fun x _ => hgd x)
    (hkerC'.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)
  rw [hga, hgb] at hparts
  have hsupp1 : ∀ t : ℝ, T < |t| →
      (Complex.exp (-(I * w * (t : ℂ))) - 1) * deriv g t = 0 := by
    intro t ht
    rw [deriv_eq_zero_of_supp hsupp ht, mul_zero]
  have hsupp2 : ∀ t : ℝ, T < |t| →
      -(I * w) * Complex.exp (-(I * w * (t : ℂ))) * g t = 0 := by
    intro t ht
    rw [hsupp t ht, mul_zero]
  have hsupp3 : ∀ t : ℝ, T < |t| → Complex.exp (-(I * w * (t : ℂ))) * g t = 0 := by
    intro t ht
    rw [hsupp t ht, mul_zero]
  rw [integral_eq_intervalIntegral_of_supp hT hsupp1,
    integral_eq_intervalIntegral_of_supp hT hsupp3]
  have hrw : (∫ t in (-(T + 1))..(T + 1), -(I * w) * Complex.exp (-(I * w * (t : ℂ))) * g t)
      = -(I * w) * ∫ t in (-(T + 1))..(T + 1), Complex.exp (-(I * w * (t : ℂ))) * g t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  rw [hparts, hrw]
  ring

end
end RHTower

namespace RHTower
noncomputable section
open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

/-! ## Suzuki eq. (1.8): the differential operator `D` -/

/-- **Suzuki eq. (1.8).**  `(Dψ)(t) = i ψ'(t)`. -/
def suzukiD (ψ : ℝ → ℂ) (t : ℝ) : ℂ := I * deriv ψ t

theorem contDiff_conj_comp_suzukiWeilDifferentialPairing {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 1 ψ) :
    ContDiff ℝ 1 (fun t : ℝ => (starRingEnd ℂ) (ψ t)) :=
  Complex.conjCLE.toContinuousLinearMap.contDiff.comp hψ

theorem deriv_conj_comp_suzukiWeilDifferentialPairing {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 1 ψ) (t : ℝ) :
    deriv (fun s : ℝ => (starRingEnd ℂ) (ψ s)) t = (starRingEnd ℂ) (deriv ψ t) :=
  ((hψ.differentiable (by norm_num) t).hasDerivAt.star).deriv

/-- The exponential-slope pairing against `conj (Dψ)` collapses to the Fourier integral of
`conj ψ`, with the spectral point pulled out in front. -/
theorem integral_expSlope_mul_conj_D {ψ : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T) (hψ : ContDiff ℝ 1 ψ)
    (hsupp : ∀ t : ℝ, T < |t| → ψ t = 0) (w : ℂ) :
    (∫ t : ℝ, (Complex.exp (-(I * w * (t : ℂ))) - 1) * (starRingEnd ℂ) (suzukiD ψ t))
      = w * ∫ t : ℝ, Complex.exp (-(I * w * (t : ℂ))) * (starRingEnd ℂ) (ψ t) := by
  set η : ℝ → ℂ := fun t => (starRingEnd ℂ) (ψ t) with hη
  have hηC : ContDiff ℝ 1 η := contDiff_conj_comp_suzukiWeilDifferentialPairing hψ
  have hηsupp : ∀ t : ℝ, T < |t| → η t = 0 := by
    intro t ht
    simp only [hη]
    rw [hsupp t ht, map_zero]
  have hpt : ∀ t : ℝ, (starRingEnd ℂ) (suzukiD ψ t) = -I * deriv η t := by
    intro t
    simp only [suzukiD, map_mul, Complex.conj_I, hη]
    rw [deriv_conj_comp_suzukiWeilDifferentialPairing hψ t]
  have hrw : (∫ t : ℝ, (Complex.exp (-(I * w * (t : ℂ))) - 1) * (starRingEnd ℂ) (suzukiD ψ t))
      = -I * ∫ t : ℝ, (Complex.exp (-(I * w * (t : ℂ))) - 1) * deriv η t := by
    have hall : ∀ t : ℝ,
        (Complex.exp (-(I * w * (t : ℂ))) - 1) * (starRingEnd ℂ) (suzukiD ψ t)
          = -I * ((Complex.exp (-(I * w * (t : ℂ))) - 1) * deriv η t) := by
      intro t
      rw [hpt t]
      ring
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hall)
  rw [hrw, integral_expSlope_mul_deriv hT hηC hηsupp w]
  have hcoef : -I * (I * w) = w := by
    linear_combination (-w) * Complex.I_sq
  rw [← mul_assoc, hcoef]

end
end RHTower

