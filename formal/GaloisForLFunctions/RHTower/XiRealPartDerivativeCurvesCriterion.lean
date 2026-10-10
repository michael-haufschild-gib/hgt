import GaloisForLFunctions.RHTower.XiCosineShiftExceptionalPointCriterion
import GaloisForLFunctions.RHTower.XiCosineShiftNonrealZeroCount

/-!
# RH as disjointness of two real-analytic curves

On the real line the cosine producer is a real part:

  `cos(hD)Ξ(x) = Re ξ(½ + h + ix)`,   `(cos(hD)Ξ)'(x) = −Im ξ'(½ + h + ix)`

(`cosProducer_ofReal`, `deriv_cosProducer_ofReal`). This uses `ξ(1 − s) = ξ(s)` and the reality of
`ξ`, so `ξ(½ − h + ix) = conj ξ(½ + h + ix)` and `ξ'(½ − h + ix) = −conj ξ'(½ + h + ix)`. The
exceptional-point criterion (`riemannHypothesis_iff_cosProducer_no_exceptionalPoint`) becomes:

**Theorem** (`riemannHypothesis_iff_re_xi_eq_zero_imp_im_deriv_xi_ne_zero`). RH holds iff
there is no `s` with `½ < Re s < 1`, `Re ξ(s) = 0` and `Im ξ'(s) = 0`.

The two real-analytic curves `{Re ξ = 0}` and `{Im ξ' = 0}` never meet in the right half of the
critical strip. At a point of the first curve where `ξ ≠ 0`, `Im ξ' = Im ξ · Re(ξ'/ξ)`. So the
criterion asks only that the Hadamard sign `Re(ξ'/ξ)` not vanish *on the curve* `Re ξ = 0`, rather
than everywhere on `Re s > ½`: a codimension-two statement.

Where the curves do meet (`exists_offline_zero_disc_of_curve_intersection`), the intersection point
`s` lies in the closed disc centred at `½ + i Im ρ` with radius `|Re ρ − ½|`, for some zero `ρ` off
the critical line. That disc passes through `ρ` and `1 − ρ̄`.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

theorem deriv_xi_conj_eq (s : ℂ) : deriv xi ((starRingEnd ℂ) s) = (starRingEnd ℂ) (deriv xi s) := by
  have h1 := (xi_differentiable s).hasDerivAt.conj_conj
  have hfun : (⇑(starRingEnd ℂ) ∘ xi ∘ ⇑(starRingEnd ℂ)) = xi := by
    funext w; simp [Function.comp, xi_conj]
  rw [hfun] at h1
  exact h1.deriv

theorem deriv_xi_one_sub_eq (s : ℂ) : deriv xi (1 - s) = -deriv xi s := by
  have h1 : HasDerivAt (fun w => xi (1 - w)) (deriv xi (1 - s) * (-1)) s := by
    have := (xi_differentiable (1 - s)).hasDerivAt.comp s ((hasDerivAt_id s).const_sub 1)
    simpa [Function.comp_def] using this
  have hfun : (fun w => xi (1 - w)) = xi := funext xi_one_sub
  rw [hfun] at h1
  rw [h1.deriv]; ring

/-- `cos(hD)Ξ(x) = Re ξ(½ + h + ix)`. -/
theorem cosProducer_ofReal (h x : ℝ) :
    cosProducer h x = ((xi (1 / 2 + h + x * I)).re : ℂ) := by
  set s : ℂ := 1 / 2 + h + x * I with hs
  have e1 : XiC ((x : ℂ) + h * I) = (starRingEnd ℂ) (xi s) := by
    have : (1 / 2 : ℂ) + ((x : ℂ) + h * I) * I = 1 - (starRingEnd ℂ) s := by
      rw [hs]; apply Complex.ext <;> simp; ring
    rw [XiC, this, xi_one_sub, xi_conj]
  have e2 : XiC ((x : ℂ) - h * I) = xi s := by
    rw [XiC]; congr 1; rw [hs]; ring_nf; rw [Complex.I_sq]; ring
  unfold cosProducer
  rw [e1, e2, add_comm, Complex.add_conj]
  push_cast
  ring

/-- `(cos(hD)Ξ)'(x) = −Im ξ'(½ + h + ix)`. -/
theorem deriv_cosProducer_ofReal (h x : ℝ) :
    deriv (cosProducer h) x = -(((deriv xi (1 / 2 + h + x * I)).im : ℝ) : ℂ) := by
  set s : ℂ := 1 / 2 + h + x * I with hs
  have hA : HasDerivAt (cosProducer h)
      ((deriv xi (1 / 2 + ((x : ℂ) + h * I) * I) * I +
        deriv xi (1 / 2 + ((x : ℂ) - h * I) * I) * I) / 2) x := by
    have d1 := (hasDerivAt_XiC ((x : ℂ) + h * I)).comp (x : ℂ)
      ((hasDerivAt_id (x : ℂ)).add_const (h * I))
    have d2 := (hasDerivAt_XiC ((x : ℂ) - h * I)).comp (x : ℂ)
      ((hasDerivAt_id (x : ℂ)).sub_const (h * I))
    have := (d1.add d2).div_const 2
    unfold cosProducer
    simpa [Function.comp_def] using this
  have a1 : (1 / 2 : ℂ) + ((x : ℂ) + h * I) * I = 1 - (starRingEnd ℂ) s := by
    rw [hs]; apply Complex.ext <;> simp; ring
  have a2 : (1 / 2 : ℂ) + ((x : ℂ) - h * I) * I = s := by
    rw [hs]; ring_nf; rw [Complex.I_sq]; ring
  rw [hA.deriv, a1, a2, deriv_xi_one_sub_eq, deriv_xi_conj_eq]
  set d := deriv xi s
  have hd : d = (d.re : ℂ) + (d.im : ℂ) * I := (Complex.re_add_im d).symm
  have hdc : (starRingEnd ℂ) d = (d.re : ℂ) - (d.im : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hdc]
  conv_rhs => rw [show -((d.im : ℝ) : ℂ) = -((d.im : ℝ) : ℂ) from rfl]
  rw [hd]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **RH ⇔ the curves `Re ξ = 0` and `Im ξ' = 0` do not meet in `½ < Re s < 1`.** -/
theorem riemannHypothesis_iff_re_xi_eq_zero_imp_im_deriv_xi_ne_zero :
    RiemannHypothesis ↔
      ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → (xi s).re = 0 → (deriv xi s).im ≠ 0 := by
  rw [riemannHypothesis_iff_cosProducer_no_exceptionalPoint]
  constructor
  · intro hno s hs1 hs2 hre
    have hrepr : s = 1 / 2 + ((s.re - 1 / 2 : ℝ) : ℂ) + (s.im : ℂ) * I := by
      apply Complex.ext <;> simp
    have h0 : cosProducer (s.re - 1 / 2) s.im = 0 := by
      rw [cosProducer_ofReal, ← hrepr, hre]; simp
    have hd := hno (s.re - 1 / 2) (by linarith) (by linarith) s.im h0
    rw [deriv_cosProducer_ofReal, ← hrepr] at hd
    intro him
    apply hd
    rw [him]; simp
  · intro hcurve h hh hh2 x h0
    set s : ℂ := 1 / 2 + h + x * I with hs
    have hsre : s.re = 1 / 2 + h := by rw [hs]; simp
    have hre : (xi s).re = 0 := by
      rw [cosProducer_ofReal] at h0
      exact_mod_cast h0
    have him := hcurve s (by rw [hsre]; linarith) (by rw [hsre]; linarith) hre
    rw [deriv_cosProducer_ofReal]
    intro hd
    apply him
    have := neg_eq_zero.mp hd
    exact_mod_cast this

/-- **Intersections live in off-line discs.** If `½ < Re s`, `Re ξ(s) = 0` and `Im ξ'(s) = 0`, then
`ξ` has a zero `ρ` off the critical line with `Re s − ½ ≤ |Re ρ − ½|` and
`|s − (½ + i Im ρ)| ≤ |Re ρ − ½|`: `s` lies in the closed disc centred on the critical line at the
height of `ρ` and passing through `ρ` and `1 − ρ̄`. -/
theorem exists_offline_zero_disc_of_curve_intersection {s : ℂ} (hs1 : 1 / 2 < s.re)
    (hre : (xi s).re = 0) (him : (deriv xi s).im = 0) :
    ∃ ρ : ℂ, xi ρ = 0 ∧ ρ.re ≠ 1 / 2 ∧ s.re - 1 / 2 ≤ |ρ.re - 1 / 2| ∧
      ‖s - (1 / 2 + (ρ.im : ℂ) * I)‖ ≤ |ρ.re - 1 / 2| := by
  set h : ℝ := s.re - 1 / 2 with hh
  have hhpos : 0 < h := by rw [hh]; linarith
  have hrepr : s = 1 / 2 + (h : ℂ) + (s.im : ℂ) * I := by
    apply Complex.ext <;> simp [hh]
  have h0 : (XiC ((s.im : ℂ) + h * I) + XiC ((s.im : ℂ) - h * I)) / 2 = 0 := by
    have := cosProducer_ofReal h s.im
    unfold cosProducer at this
    rw [this, ← hrepr, hre]; simp
  have hd : deriv (fun z => (XiC (z + h * I) + XiC (z - h * I)) / 2) (s.im : ℂ) = 0 := by
    have := deriv_cosProducer_ofReal h s.im
    unfold cosProducer at this
    rw [this, ← hrepr, him]; simp
  obtain ⟨w, hw, hloc⟩ : ∃ w, XiC w = 0 ∧ (s.im - w.re) ^ 2 + h ^ 2 ≤ w.im ^ 2 := by
    by_contra hall
    push Not at hall
    exact deriv_cosineShiftXi_ne_zero_of_local hhpos (fun w hw => hall w hw) h0 hd
  have hre' : (1 / 2 + w * I).re - 1 / 2 = -w.im := by simp
  have hh2 : h ^ 2 ≤ w.im ^ 2 := by nlinarith [sq_nonneg (s.im - w.re)]
  refine ⟨1 / 2 + w * I, by rw [← hw, XiC], ?_, ?_, ?_⟩
  · have hwim : w.im ≠ 0 := by
      intro h0'; rw [h0'] at hh2; nlinarith
    intro hc
    apply hwim
    have : (1 / 2 + w * I).re - 1 / 2 = 0 := by rw [hc]; ring
    rw [hre'] at this
    linarith
  · rw [hre', abs_neg]
    have := sq_le_sq.mp hh2
    rwa [abs_of_pos hhpos] at this
  · have hn : ‖s - (1 / 2 + ((1 / 2 + w * I).im : ℂ) * I)‖ ^ 2 = h ^ 2 + (s.im - w.re) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [hh]; ring
    rw [hre', abs_neg]
    have hsq : ‖s - (1 / 2 + ((1 / 2 + w * I).im : ℂ) * I)‖ ^ 2 ≤ |w.im| ^ 2 := by
      rw [hn, sq_abs]; linarith
    exact (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mp hsq

end

end RHTower
