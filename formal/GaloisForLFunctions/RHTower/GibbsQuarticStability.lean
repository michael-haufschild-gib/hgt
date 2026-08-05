import Mathlib
import GaloisForLFunctions.RHTower.GibbsSectorStability

/-!
# Quartic sector stability of the squarefree Gibbs gas

The quartic Routh–Hurwitz criterion, by the conjugate-pair factorization: a root `s + it`
with `s ≥ 0` of a real quartic forces the real quadratic factor `z² − 2sz + m`
(`m = s² + t²`), and eliminating the cofactor yields the exact identity

  `a₃a₂a₁ − a₄a₁² − a₃²a₀ = −2sb·[(a₄m − c)² + a₃a₁]`,   `b = a₃ + 2sa₄ > 0`,

so the Hurwitz minor `Δ₃ > 0` forbids `s ≥ 0`.  The four-element gas satisfies the minor
at every coupling by energy injection (`A₀A₃² + A₁²A₄ < A₁A₂A₃`), so the quadruple gas is
sector-stable for all `x > 0`, and every one of its zeros contributes parity cancellation.
-/

namespace RHTower.GibbsGas

open Real

/-- **Routh–Hurwitz, degree four.**  A real quartic with positive extreme and odd
coefficients, nonnegative `a₂`, and positive Hurwitz minor `a₃a₂a₁ − a₄a₁² − a₃²a₀` has
no zero in the closed right half-plane. -/
theorem quartic_no_rhp_root (a4 a3 a2 a1 a0 : ℝ) (ha4 : 0 < a4) (ha3 : 0 < a3)
    (ha2 : 0 ≤ a2) (ha1 : 0 < a1) (ha0 : 0 < a0)
    (hH : a4 * a1^2 + a3^2 * a0 < a3 * a2 * a1)
    (z : ℂ) (hz : 0 ≤ z.re) :
    (a4:ℂ)*z^4 + (a3:ℂ)*z^3 + (a2:ℂ)*z^2 + (a1:ℂ)*z + (a0:ℂ) ≠ 0 := by
  intro hroot
  set s : ℝ := z.re with hs
  set t : ℝ := z.im with ht
  have hz' : z = (s:ℂ) + (t:ℂ) * Complex.I := by
    rw [hs, ht]
    exact (Complex.re_add_im z).symm
  rcases eq_or_ne t 0 with ht0 | ht0
  · -- real root with `s ≥ 0` is impossible: all terms nonnegative, constant positive
    rw [hz', ht0] at hroot
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at hroot
    have hreal : ((a4*s^4 + a3*s^3 + a2*s^2 + a1*s + a0 : ℝ) : ℂ) = 0 := by
      push_cast
      linear_combination hroot
    have h0 : a4*s^4 + a3*s^3 + a2*s^2 + a1*s + a0 = 0 :=
      Complex.ofReal_eq_zero.mp hreal
    nlinarith [h0, mul_nonneg ha4.le (pow_nonneg hz 4),
      mul_nonneg ha3.le (pow_nonneg hz 3), mul_nonneg ha2 (pow_nonneg hz 2),
      mul_nonneg ha1.le hz]
  · -- complex root: the conjugate-pair quadratic divides the quartic
    have ht2 : 0 < t^2 := by
      rcases lt_or_gt_of_ne ht0 with h | h
      · nlinarith
      · nlinarith
    set m : ℝ := s^2 + t^2 with hm
    have hm0 : 0 < m := by
      rw [hm]
      nlinarith [sq_nonneg s]
    set b : ℝ := a3 + 2*s*a4 with hb
    set c : ℝ := a2 + 2*s*b - a4*m with hc
    set r1 : ℝ := a1 - (b*m - 2*s*c) with hr1
    set r0 : ℝ := a0 - c*m with hr0
    have hdiv : (a4:ℂ)*z^4 + (a3:ℂ)*z^3 + (a2:ℂ)*z^2 + (a1:ℂ)*z + (a0:ℂ)
        = (z^2 - 2*(s:ℂ)*z + (m:ℂ)) * ((a4:ℂ)*z^2 + (b:ℂ)*z + (c:ℂ))
          + ((r1:ℂ)*z + (r0:ℂ)) := by
      rw [hr1, hr0, hc, hb, hm]
      push_cast
      ring
    have hq0 : z^2 - 2*(s:ℂ)*z + (m:ℂ) = 0 := by
      rw [hz', hm]
      push_cast
      linear_combination ((t:ℂ))^2 * Complex.I_sq
    have hlin : (r1:ℂ)*z + (r0:ℂ) = 0 := by
      have h := hdiv
      rw [hroot, hq0, zero_mul, zero_add] at h
      exact h.symm
    rw [hz'] at hlin
    have hIm : r1 * t = 0 := by
      have h := congrArg Complex.im hlin
      simp only [Complex.add_im, Complex.mul_im, Complex.add_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.zero_im] at h
      linear_combination h
    have hRe : r1 * s + r0 = 0 := by
      have h := congrArg Complex.re hlin
      simp only [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.zero_re] at h
      linear_combination h
    have hr1z : r1 = 0 := by
      rcases mul_eq_zero.mp hIm with h | h
      · exact h
      · exact absurd h ht0
    have hr0z : r0 = 0 := by
      rw [hr1z] at hRe
      linarith
    have hR1 : b*m - 2*s*c = a1 := by
      have h := hr1z
      rw [hr1] at h
      linarith
    have hR2 : c*m = a0 := by
      have h := hr0z
      rw [hr0] at h
      linarith
    have hb0 : 0 < b := by
      rw [hb]
      nlinarith [mul_nonneg hz ha4.le]
    have ha3eq : a3 = b - 2*s*a4 := by rw [hb]; ring
    have ha2eq : a2 = c - 2*s*b + a4*m := by rw [hc]; ring
    have hkey : a3*a2*a1 - a4*a1^2 - a3^2*a0
        = -(2*s*b*((a4*m - c)^2 + a3*a1)) := by
      rw [← hR1, ← hR2, ha3eq, ha2eq]
      ring
    have hBr : 0 ≤ (a4*m - c)^2 + a3*a1 :=
      add_nonneg (sq_nonneg _) (mul_pos ha3 ha1).le
    have hsb : 0 ≤ s*b*((a4*m - c)^2 + a3*a1) :=
      mul_nonneg (mul_nonneg hz hb0.le) hBr
    nlinarith [hkey, hsb, hH]

/-- Comparing Boltzmann pair-products by total energy. -/
theorem exp_pair_lt (u1 u2 v1 v2 : ℝ) (h : v1 + v2 < u1 + u2) :
    Real.exp (-u1) * Real.exp (-u2) < Real.exp (-v1) * Real.exp (-v2) := by
  rw [← Real.exp_add, ← Real.exp_add]
  exact Real.exp_lt_exp.mpr (by linarith)

/-- The quadruple gas in the coefficient basis. -/
theorem gibbsDiag_quadruple_expand (p q r s : ℕ)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) (x z : ℝ) :
    gibbsDiag {p, q, r, s} x z
      = Real.exp (-x)
        + (Real.exp (-((p:ℝ)*x)) + Real.exp (-((q:ℝ)*x)) + Real.exp (-((r:ℝ)*x))
            + Real.exp (-((s:ℝ)*x))) * z
        + (Real.exp (-((q:ℝ)*((p:ℝ)*x))) + Real.exp (-((r:ℝ)*((p:ℝ)*x)))
            + Real.exp (-((s:ℝ)*((p:ℝ)*x))) + Real.exp (-((r:ℝ)*((q:ℝ)*x)))
            + Real.exp (-((s:ℝ)*((q:ℝ)*x))) + Real.exp (-((s:ℝ)*((r:ℝ)*x)))) * z^2
        + (Real.exp (-((r:ℝ)*((q:ℝ)*((p:ℝ)*x)))) + Real.exp (-((s:ℝ)*((q:ℝ)*((p:ℝ)*x))))
            + Real.exp (-((s:ℝ)*((r:ℝ)*((p:ℝ)*x))))
            + Real.exp (-((s:ℝ)*((r:ℝ)*((q:ℝ)*x))))) * z^3
        + Real.exp (-((s:ℝ)*((r:ℝ)*((q:ℝ)*((p:ℝ)*x))))) * z^4 := by
  have h1 : p ∉ ({q, r, s} : Finset ℕ) := by simp [hpq, hpr, hps]
  have h2 : q ∉ ({r, s} : Finset ℕ) := by simp [hqr, hqs]
  have h3 : r ∉ ({s} : Finset ℕ) := by simp [hrs]
  rw [gibbsDiag_insert p {q, r, s} h1,
    gibbsDiag_insert q {r, s} h2, gibbsDiag_insert q {r, s} h2,
    gibbsDiag_insert r {s} h3, gibbsDiag_insert r {s} h3,
    gibbsDiag_insert r {s} h3, gibbsDiag_insert r {s} h3,
    gibbsDiag_singleton, gibbsDiag_singleton, gibbsDiag_singleton,
    gibbsDiag_singleton, gibbsDiag_singleton, gibbsDiag_singleton,
    gibbsDiag_singleton, gibbsDiag_singleton]
  ring

set_option maxHeartbeats 1600000 in
/-- **The quartic Hurwitz minor of the gas at every coupling, by energy injection**:
`A₄A₁² + A₃²A₀ < A₃A₂A₁`.  Every right-hand monomial is strictly dominated by a distinct
left-hand monomial with smaller total energy, and the two dominating families are
separated by whether the pair contains the smallest element. -/
theorem quadruple_gas_hurwitz (p q r s : ℕ) (hp : 2 ≤ p)
    (hpq : p < q) (hqr : q < r) (hrs : r < s) (x : ℝ) (hx : 0 < x) :
    Real.exp (-((s:ℝ)*((r:ℝ)*((q:ℝ)*((p:ℝ)*x)))))
        * (Real.exp (-((p:ℝ)*x)) + Real.exp (-((q:ℝ)*x)) + Real.exp (-((r:ℝ)*x))
            + Real.exp (-((s:ℝ)*x)))^2
      + (Real.exp (-((r:ℝ)*((q:ℝ)*((p:ℝ)*x)))) + Real.exp (-((s:ℝ)*((q:ℝ)*((p:ℝ)*x))))
          + Real.exp (-((s:ℝ)*((r:ℝ)*((p:ℝ)*x))))
          + Real.exp (-((s:ℝ)*((r:ℝ)*((q:ℝ)*x)))))^2 * Real.exp (-x)
      < (Real.exp (-((r:ℝ)*((q:ℝ)*((p:ℝ)*x)))) + Real.exp (-((s:ℝ)*((q:ℝ)*((p:ℝ)*x))))
          + Real.exp (-((s:ℝ)*((r:ℝ)*((p:ℝ)*x))))
          + Real.exp (-((s:ℝ)*((r:ℝ)*((q:ℝ)*x)))))
        * (Real.exp (-((q:ℝ)*((p:ℝ)*x))) + Real.exp (-((r:ℝ)*((p:ℝ)*x)))
            + Real.exp (-((s:ℝ)*((p:ℝ)*x))) + Real.exp (-((r:ℝ)*((q:ℝ)*x)))
            + Real.exp (-((s:ℝ)*((q:ℝ)*x))) + Real.exp (-((s:ℝ)*((r:ℝ)*x))))
        * (Real.exp (-((p:ℝ)*x)) + Real.exp (-((q:ℝ)*x)) + Real.exp (-((r:ℝ)*x))
            + Real.exp (-((s:ℝ)*x))) := by
  set e1 : ℝ := Real.exp (-x) with he1
  set eP : ℝ := Real.exp (-((p:ℝ)*x)) with heP
  set eQ : ℝ := Real.exp (-((q:ℝ)*x)) with heQ
  set eR : ℝ := Real.exp (-((r:ℝ)*x)) with heR
  set eS : ℝ := Real.exp (-((s:ℝ)*x)) with heS
  set ePQ : ℝ := Real.exp (-((q:ℝ)*((p:ℝ)*x))) with hePQ
  set ePR : ℝ := Real.exp (-((r:ℝ)*((p:ℝ)*x))) with hePR
  set ePS : ℝ := Real.exp (-((s:ℝ)*((p:ℝ)*x))) with hePS
  set eQR : ℝ := Real.exp (-((r:ℝ)*((q:ℝ)*x))) with heQR
  set eQS : ℝ := Real.exp (-((s:ℝ)*((q:ℝ)*x))) with heQS
  set eRS : ℝ := Real.exp (-((s:ℝ)*((r:ℝ)*x))) with heRS
  set ePQR : ℝ := Real.exp (-((r:ℝ)*((q:ℝ)*((p:ℝ)*x)))) with hePQR
  set ePQS : ℝ := Real.exp (-((s:ℝ)*((q:ℝ)*((p:ℝ)*x)))) with hePQS
  set ePRS : ℝ := Real.exp (-((s:ℝ)*((r:ℝ)*((p:ℝ)*x)))) with hePRS
  set eQRS : ℝ := Real.exp (-((s:ℝ)*((r:ℝ)*((q:ℝ)*x)))) with heQRS
  set ePQRS : ℝ := Real.exp (-((s:ℝ)*((r:ℝ)*((q:ℝ)*((p:ℝ)*x))))) with hePQRS
  -- positivity of the atoms
  have h1pos : 0 < e1 := by rw [he1]; exact Real.exp_pos _
  have hPpos : 0 < eP := by rw [heP]; exact Real.exp_pos _
  have hQpos : 0 < eQ := by rw [heQ]; exact Real.exp_pos _
  have hRpos : 0 < eR := by rw [heR]; exact Real.exp_pos _
  have hSpos : 0 < eS := by rw [heS]; exact Real.exp_pos _
  have hPQpos : 0 < ePQ := by rw [hePQ]; exact Real.exp_pos _
  have hPRpos : 0 < ePR := by rw [hePR]; exact Real.exp_pos _
  have hPSpos : 0 < ePS := by rw [hePS]; exact Real.exp_pos _
  have hQRpos : 0 < eQR := by rw [heQR]; exact Real.exp_pos _
  have hQSpos : 0 < eQS := by rw [heQS]; exact Real.exp_pos _
  have hRSpos : 0 < eRS := by rw [heRS]; exact Real.exp_pos _
  have hPQRpos : 0 < ePQR := by rw [hePQR]; exact Real.exp_pos _
  have hPQSpos : 0 < ePQS := by rw [hePQS]; exact Real.exp_pos _
  have hPRSpos : 0 < ePRS := by rw [hePRS]; exact Real.exp_pos _
  have hQRSpos : 0 < eQRS := by rw [heQRS]; exact Real.exp_pos _
  -- cast facts
  have hp' : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hq' : (2:ℝ) ≤ (q:ℝ) := by
    have : 2 ≤ q := by omega
    exact_mod_cast this
  have hr' : (2:ℝ) ≤ (r:ℝ) := by
    have : 2 ≤ r := by omega
    exact_mod_cast this
  have hs' : (2:ℝ) ≤ (s:ℝ) := by
    have : 2 ≤ s := by omega
    exact_mod_cast this
  have hp1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
  have hq1 : (0:ℝ) < (q:ℝ) - 1 := by linarith
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hq0 : (0:ℝ) < (q:ℝ) := by linarith
  have hr0 : (0:ℝ) < (r:ℝ) := by linarith
  have hs0 : (0:ℝ) < (s:ℝ) := by linarith
  have hqr1 : (0:ℝ) < (q:ℝ)*(r:ℝ) - 1 := by nlinarith
  have hqs1 : (0:ℝ) < (q:ℝ)*(s:ℝ) - 1 := by nlinarith
  have hrs1 : (0:ℝ) < (r:ℝ)*(s:ℝ) - 1 := by nlinarith
  -- the eight strict energy comparisons
  have hCA1 : e1 * ePQR < eP * eQR := by
    rw [he1, hePQR, heP, heQR]
    exact exp_pair_lt _ _ _ _ (by nlinarith [mul_pos (mul_pos hp1 hqr1) hx])
  have hCA2 : e1 * ePQS < eP * eQS := by
    rw [he1, hePQS, heP, heQS]
    exact exp_pair_lt _ _ _ _ (by nlinarith [mul_pos (mul_pos hp1 hqs1) hx])
  have hCA3 : e1 * ePRS < eP * eRS := by
    rw [he1, hePRS, heP, heRS]
    exact exp_pair_lt _ _ _ _ (by nlinarith [mul_pos (mul_pos hp1 hrs1) hx])
  have hCA4 : e1 * eQRS < eQ * eRS := by
    rw [he1, heQRS, heQ, heRS]
    exact exp_pair_lt _ _ _ _ (by nlinarith [mul_pos (mul_pos hq1 hrs1) hx])
  have hCB1 : eP * ePQRS < ePQ * ePRS := by
    rw [heP, hePQRS, hePQ, hePRS]
    exact exp_pair_lt _ _ _ _
      (by nlinarith [mul_pos (mul_pos hq1 hrs1) (mul_pos hp0 hx)])
  have hCB2 : eQ * ePQRS < ePQ * eQRS := by
    rw [heQ, hePQRS, hePQ, heQRS]
    exact exp_pair_lt _ _ _ _
      (by nlinarith [mul_pos (mul_pos hp1 hrs1) (mul_pos hq0 hx)])
  have hCB3 : eR * ePQRS < ePR * eQRS := by
    rw [heR, hePQRS, hePR, heQRS]
    exact exp_pair_lt _ _ _ _
      (by nlinarith [mul_pos (mul_pos hp1 hqs1) (mul_pos hr0 hx)])
  have hCB4 : eS * ePQRS < ePS * eQRS := by
    rw [heS, hePQRS, hePS, heQRS]
    exact exp_pair_lt _ _ _ _
      (by nlinarith [mul_pos (mul_pos hp1 hqr1) (mul_pos hs0 hx)])
  clear_value e1 eP eQ eR eS ePQ ePR ePS eQR eQS eRS ePQR ePQS ePRS eQRS ePQRS
  -- aggregated strict dominations
  have hA3pos : (0:ℝ) < ePQR + ePQS + ePRS + eQRS := by
    linarith [hPQRpos, hPQSpos, hPRSpos, hQRSpos]
  have hA1pos : (0:ℝ) < eP + eQ + eR + eS := by
    linarith [hPpos, hQpos, hRpos, hSpos]
  have hsum1 : e1*ePQR + e1*ePQS + e1*ePRS + e1*eQRS
      < eP*eQR + eP*eQS + eP*eRS + eQ*eRS := by linarith
  have hsum2 : eP*ePQRS + eQ*ePQRS + eR*ePQRS + eS*ePQRS
      < ePQ*ePRS + ePQ*eQRS + ePR*eQRS + ePS*eQRS := by linarith
  have hA : e1 * (ePQR + ePQS + ePRS + eQRS)^2
      < (eP*eQR + eP*eQS + eP*eRS + eQ*eRS) * (ePQR + ePQS + ePRS + eQRS) := by
    calc e1 * (ePQR + ePQS + ePRS + eQRS)^2
        = (e1*ePQR + e1*ePQS + e1*ePRS + e1*eQRS) * (ePQR + ePQS + ePRS + eQRS) := by
          ring
      _ < (eP*eQR + eP*eQS + eP*eRS + eQ*eRS) * (ePQR + ePQS + ePRS + eQRS) :=
          mul_lt_mul_of_pos_right hsum1 hA3pos
  have hB : (eP + eQ + eR + eS)^2 * ePQRS
      < (eP + eQ + eR + eS) * (ePQ*ePRS + ePQ*eQRS + ePR*eQRS + ePS*eQRS) := by
    calc (eP + eQ + eR + eS)^2 * ePQRS
        = (eP + eQ + eR + eS) * (eP*ePQRS + eQ*ePQRS + eR*ePQRS + eS*ePQRS) := by
          ring
      _ < (eP + eQ + eR + eS) * (ePQ*ePRS + ePQ*eQRS + ePR*eQRS + ePS*eQRS) :=
          mul_lt_mul_of_pos_left hsum2 hA1pos
  have hc1 : eP*eQR + eP*eQS + eP*eRS + eQ*eRS
      ≤ (eP + eQ + eR + eS) * (eQR + eQS + eRS) := by
    have k1 : eQ*eRS ≤ eQ*(eQR + eQS + eRS) :=
      mul_le_mul_of_nonneg_left (by linarith [hQRpos, hQSpos]) hQpos.le
    have k2 : (eP + eQ)*(eQR + eQS + eRS) ≤ (eP + eQ + eR + eS)*(eQR + eQS + eRS) :=
      mul_le_mul_of_nonneg_right (by linarith [hRpos, hSpos])
        (by linarith [hQRpos, hQSpos, hRSpos])
    calc eP*eQR + eP*eQS + eP*eRS + eQ*eRS
        = eP*(eQR + eQS + eRS) + eQ*eRS := by ring
      _ ≤ eP*(eQR + eQS + eRS) + eQ*(eQR + eQS + eRS) := by linarith [k1]
      _ = (eP + eQ)*(eQR + eQS + eRS) := by ring
      _ ≤ (eP + eQ + eR + eS)*(eQR + eQS + eRS) := k2
  have hc2 : ePQ*ePRS + ePQ*eQRS + ePR*eQRS + ePS*eQRS
      ≤ (ePQ + ePR + ePS) * (ePQR + ePQS + ePRS + eQRS) := by
    have k1 : ePRS + eQRS ≤ ePQR + ePQS + ePRS + eQRS := by
      linarith [hPQRpos, hPQSpos]
    have k2 : eQRS ≤ ePQR + ePQS + ePRS + eQRS := by
      linarith [hPQRpos, hPQSpos, hPRSpos]
    have m1 := mul_le_mul_of_nonneg_left k1 hPQpos.le
    have m2 := mul_le_mul_of_nonneg_left k2 (by linarith [hPRpos, hPSpos] :
      (0:ℝ) ≤ ePR + ePS)
    calc ePQ*ePRS + ePQ*eQRS + ePR*eQRS + ePS*eQRS
        = ePQ*(ePRS + eQRS) + (ePR + ePS)*eQRS := by ring
      _ ≤ ePQ*(ePQR + ePQS + ePRS + eQRS)
            + (ePR + ePS)*(ePQR + ePQS + ePRS + eQRS) := by linarith [m1, m2]
      _ = (ePQ + ePR + ePS)*(ePQR + ePQS + ePRS + eQRS) := by ring
  have hC : (eP*eQR + eP*eQS + eP*eRS + eQ*eRS) * (ePQR + ePQS + ePRS + eQRS)
        + (eP + eQ + eR + eS) * (ePQ*ePRS + ePQ*eQRS + ePR*eQRS + ePS*eQRS)
      ≤ (ePQR + ePQS + ePRS + eQRS)
        * (ePQ + ePR + ePS + eQR + eQS + eRS)
        * (eP + eQ + eR + eS) := by
    have h1 := mul_le_mul_of_nonneg_right hc1 hA3pos.le
    have h2 := mul_le_mul_of_nonneg_left hc2 hA1pos.le
    calc (eP*eQR + eP*eQS + eP*eRS + eQ*eRS) * (ePQR + ePQS + ePRS + eQRS)
          + (eP + eQ + eR + eS) * (ePQ*ePRS + ePQ*eQRS + ePR*eQRS + ePS*eQRS)
        ≤ ((eP + eQ + eR + eS) * (eQR + eQS + eRS)) * (ePQR + ePQS + ePRS + eQRS)
          + (eP + eQ + eR + eS)
            * ((ePQ + ePR + ePS) * (ePQR + ePQS + ePRS + eQRS)) := by
          exact add_le_add h1 h2
      _ = (ePQR + ePQS + ePRS + eQRS)
            * (ePQ + ePR + ePS + eQR + eQS + eRS)
            * (eP + eQ + eR + eS) := by ring
  calc ePQRS * (eP + eQ + eR + eS)^2
        + (ePQR + ePQS + ePRS + eQRS)^2 * e1
      = (eP + eQ + eR + eS)^2 * ePQRS
        + e1 * (ePQR + ePQS + ePRS + eQRS)^2 := by ring
    _ < (eP + eQ + eR + eS) * (ePQ*ePRS + ePQ*eQRS + ePR*eQRS + ePS*eQRS)
        + (eP*eQR + eP*eQS + eP*eRS + eQ*eRS) * (ePQR + ePQS + ePRS + eQRS) :=
        add_lt_add hB hA
    _ ≤ (ePQR + ePQS + ePRS + eQRS)
          * (ePQ + ePR + ePS + eQR + eQS + eRS)
          * (eP + eQ + eR + eS) := by
        rw [add_comm]
        exact hC

/-- **Sector stability of the quadruple gas at every coupling**: no zero in the closed
right half-plane. -/
theorem quadruple_gas_sector_stable (p q r s : ℕ) (hp : 2 ≤ p)
    (hpq : p < q) (hqr : q < r) (hrs : r < s) (x : ℝ) (hx : 0 < x)
    (z : ℂ) (hz : 0 ≤ z.re) :
    (Real.exp (-((s:ℝ)*((r:ℝ)*((q:ℝ)*((p:ℝ)*x))))) : ℂ) * z^4
      + ((Real.exp (-((r:ℝ)*((q:ℝ)*((p:ℝ)*x)))) + Real.exp (-((s:ℝ)*((q:ℝ)*((p:ℝ)*x))))
          + Real.exp (-((s:ℝ)*((r:ℝ)*((p:ℝ)*x))))
          + Real.exp (-((s:ℝ)*((r:ℝ)*((q:ℝ)*x)))) : ℝ) : ℂ) * z^3
      + ((Real.exp (-((q:ℝ)*((p:ℝ)*x))) + Real.exp (-((r:ℝ)*((p:ℝ)*x)))
          + Real.exp (-((s:ℝ)*((p:ℝ)*x))) + Real.exp (-((r:ℝ)*((q:ℝ)*x)))
          + Real.exp (-((s:ℝ)*((q:ℝ)*x))) + Real.exp (-((s:ℝ)*((r:ℝ)*x))) : ℝ) : ℂ) * z^2
      + ((Real.exp (-((p:ℝ)*x)) + Real.exp (-((q:ℝ)*x)) + Real.exp (-((r:ℝ)*x))
          + Real.exp (-((s:ℝ)*x)) : ℝ) : ℂ) * z
      + (Real.exp (-x) : ℂ) ≠ 0 := by
  have hH := quadruple_gas_hurwitz p q r s hp hpq hqr hrs x hx
  exact quartic_no_rhp_root _ _ _ _ _ (Real.exp_pos _) (by positivity) (by positivity)
    (by positivity) (Real.exp_pos _) (by linarith [hH]) z hz

/-- **The parity grading of the quadruple gas**: every zero, at every coupling,
individually contributes cancellation at the parity point. -/
theorem quadruple_gas_root_grading (p q r s : ℕ) (hp : 2 ≤ p)
    (hpq : p < q) (hqr : q < r) (hrs : r < s) (x : ℝ) (hx : 0 < x) (ζ : ℂ)
    (hroot : (Real.exp (-((s:ℝ)*((r:ℝ)*((q:ℝ)*((p:ℝ)*x))))) : ℂ) * ζ^4
      + ((Real.exp (-((r:ℝ)*((q:ℝ)*((p:ℝ)*x)))) + Real.exp (-((s:ℝ)*((q:ℝ)*((p:ℝ)*x))))
          + Real.exp (-((s:ℝ)*((r:ℝ)*((p:ℝ)*x))))
          + Real.exp (-((s:ℝ)*((r:ℝ)*((q:ℝ)*x)))) : ℝ) : ℂ) * ζ^3
      + ((Real.exp (-((q:ℝ)*((p:ℝ)*x))) + Real.exp (-((r:ℝ)*((p:ℝ)*x)))
          + Real.exp (-((s:ℝ)*((p:ℝ)*x))) + Real.exp (-((r:ℝ)*((q:ℝ)*x)))
          + Real.exp (-((s:ℝ)*((q:ℝ)*x))) + Real.exp (-((s:ℝ)*((r:ℝ)*x))) : ℝ) : ℂ) * ζ^2
      + ((Real.exp (-((p:ℝ)*x)) + Real.exp (-((q:ℝ)*x)) + Real.exp (-((r:ℝ)*x))
          + Real.exp (-((s:ℝ)*x)) : ℝ) : ℂ) * ζ
      + (Real.exp (-x) : ℂ) = 0) :
    ‖1 + ζ‖ < ‖1 - ζ‖ := by
  have hre : ζ.re < 0 := by
    by_contra hcon
    rw [not_lt] at hcon
    exact quadruple_gas_sector_stable p q r s hp hpq hqr hrs x hx ζ hcon hroot
  exact norm_one_add_lt_of_re_neg ζ hre

end RHTower.GibbsGas
