import GaloisForLFunctions.RHTower.Reflection

/-!
# Edge blindness of the full Xi logarithmic derivative

The completed `ξ` is real on the critical line (Schwarz reality composed with
the functional equation), and its derivative there is purely imaginary.
Consequently `Re (ξ'/ξ) ≡ 0` on the critical line wherever `ξ` does not
vanish: the full logarithmic derivative carries no real edge signal at all.
Off-critical zero pairs are invisible to it on the edge; only the relative
(strict-right) response retains a nonnegative real part with content, which is
why the divisor split is detectable exclusively through relative positivity.
-/

open Complex

namespace RHTower

noncomputable section

/-- Derivative of the Schwarz reflection of an entire function. -/
theorem deriv_conj_reflect {f : ℂ → ℂ} (hf : Differentiable ℂ f) (s : ℂ) :
    deriv (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) s =
      (starRingEnd ℂ) (deriv f ((starRingEnd ℂ) s)) := by
  have hd : HasDerivAt f (deriv f ((starRingEnd ℂ) s)) ((starRingEnd ℂ) s) :=
    (hf ((starRingEnd ℂ) s)).hasDerivAt
  have hg : HasDerivAt (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z)))
      ((starRingEnd ℂ) (deriv f ((starRingEnd ℂ) s))) s := by
    rw [hasDerivAt_iff_tendsto_slope] at hd ⊢
    have hmap : Filter.Tendsto (fun z : ℂ => (starRingEnd ℂ) z)
        (nhdsWithin s {s}ᶜ) (nhdsWithin ((starRingEnd ℂ) s)
          {(starRingEnd ℂ) s}ᶜ) := by
      apply Filter.Tendsto.inf
      · exact (Complex.continuous_conj.tendsto s)
      · rw [Filter.tendsto_principal]
        filter_upwards [Filter.mem_principal_self ({s}ᶜ : Set ℂ)] with z hz
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
        intro heq
        exact hz (star_injective heq)
    have hcont : Filter.Tendsto (starRingEnd ℂ)
        (nhds (deriv f ((starRingEnd ℂ) s)))
        (nhds ((starRingEnd ℂ) (deriv f ((starRingEnd ℂ) s)))) :=
      Complex.continuous_conj.tendsto _
    have hcomp := hcont.comp (hd.comp hmap)
    apply hcomp.congr'
    filter_upwards [Filter.univ_mem] with z _
    simp only [Function.comp_apply, slope_def_field]
    rw [← map_sub, ← map_sub, map_div₀]
    congr 1
    simp
  rw [hg.deriv]

/-- The derivative of ξ is conjugation-equivariant. -/
theorem deriv_xi_conj (s : ℂ) :
    deriv xi ((starRingEnd ℂ) s) = (starRingEnd ℂ) (deriv xi s) := by
  have hfun : (fun z => (starRingEnd ℂ) (xi ((starRingEnd ℂ) z))) = xi := by
    funext z
    rw [xi_conj]
    simp
  have h := deriv_conj_reflect xi_differentiable s
  rw [hfun] at h
  have := congrArg (starRingEnd ℂ) h
  simpa using this.symm

/-- The derivative of ξ is odd across the functional-equation reflection. -/
theorem deriv_xi_one_sub (s : ℂ) :
    deriv xi (1 - s) = -deriv xi s := by
  have hfun : (fun z : ℂ => xi (1 - z)) = xi := by
    funext z
    exact xi_one_sub z
  have h1 : deriv (fun z : ℂ => xi (1 - z)) s = -deriv xi (1 - s) := by
    rw [deriv_comp_const_sub]
  rw [hfun] at h1
  have h2 := congrArg Neg.neg h1.symm
  simpa using h2

/-- On the critical line the conjugate is the functional-equation reflection. -/
theorem conj_criticalLine (t : ℝ) :
    (starRingEnd ℂ) ((1 / 2 : ℂ) + I * (t : ℂ)) =
      1 - ((1 / 2 : ℂ) + I * (t : ℂ)) := by
  apply Complex.ext
  · norm_num [Complex.conj_re, Complex.add_re, Complex.mul_re,
      Complex.sub_re]
  · norm_num [Complex.conj_im, Complex.add_im, Complex.mul_im,
      Complex.sub_im]

/-- ξ is real on the critical line. -/
theorem xi_criticalLine_im (t : ℝ) :
    (xi ((1 / 2 : ℂ) + I * (t : ℂ))).im = 0 := by
  set s : ℂ := (1 / 2 : ℂ) + I * (t : ℂ)
  have h1 : xi s = (starRingEnd ℂ) (xi s) := by
    calc xi s = xi (1 - s) := (xi_one_sub s).symm
      _ = xi ((starRingEnd ℂ) s) := by rw [conj_criticalLine]
      _ = (starRingEnd ℂ) (xi s) := xi_conj s
  have h2 := congrArg Complex.im h1
  rw [Complex.conj_im] at h2
  linarith

/-- ξ' is purely imaginary on the critical line. -/
theorem deriv_xi_criticalLine_re (t : ℝ) :
    (deriv xi ((1 / 2 : ℂ) + I * (t : ℂ))).re = 0 := by
  set s : ℂ := (1 / 2 : ℂ) + I * (t : ℂ)
  have h1 : deriv xi s = -(starRingEnd ℂ) (deriv xi s) := by
    calc deriv xi s = (starRingEnd ℂ) (deriv xi ((starRingEnd ℂ) s)) := by
          have := deriv_xi_conj s
          have h := congrArg (starRingEnd ℂ) this
          simpa using h.symm
      _ = (starRingEnd ℂ) (deriv xi (1 - s)) := by rw [conj_criticalLine]
      _ = (starRingEnd ℂ) (-deriv xi s) := by rw [deriv_xi_one_sub]
      _ = -(starRingEnd ℂ) (deriv xi s) := by rw [map_neg]
  have h2 := congrArg Complex.re h1
  rw [Complex.neg_re, Complex.conj_re] at h2
  linarith

/-- **Edge blindness law.**  The full logarithmic derivative of ξ has
vanishing real part everywhere on the critical line where ξ does not vanish:
the complete divisor current carries no real edge signal, and the off-line
divisor split is detectable only through relative positivity. -/
theorem re_logDeriv_xi_criticalLine (t : ℝ) :
    (deriv xi ((1 / 2 : ℂ) + I * (t : ℂ)) /
      xi ((1 / 2 : ℂ) + I * (t : ℂ))).re = 0 := by
  set s : ℂ := (1 / 2 : ℂ) + I * (t : ℂ)
  rw [Complex.div_re, deriv_xi_criticalLine_re, xi_criticalLine_im]
  simp

end

end RHTower
