import GaloisForLFunctions.RHTower.XiEndpointExpansion

/-!
# The endpoint cancellation

The logarithmic derivative of Dunster's weight contains the difference

`x / (2 sqrt(x²-1) sqrt(x²-s))  -  1/(2 xi_s(x))`,

whose two terms each blow up like `(x-1)^{-1/2}` at the endpoint.  Their difference is bounded only
because the leading constants agree exactly, which is a statement about the second-order behaviour of
the phase and not about its two-sided bracket.

Written over a common denominator the difference is controlled by

`| x xi_s(x) - sqrt(x²-1) sqrt(x²-s) |`,

and this module bounds that numerator by `(x-1)^{3/2}`: one full power better than the size of each
term separately, which is exactly the cancellation.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

theorem two_xiEndpointFactor_one_eq (s : ℝ) :
    2 * xiEndpointFactor s 1 = Real.sqrt (2 * (1 - s)) := by
  rw [xiEndpointFactor_one, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- The endpoint value of the amplitude combination is Lipschitz, by the difference of squares. -/
theorem abs_sqrt_prod_sub_le {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hx1 : 1 ≤ x) (hx2 : x ≤ 2) :
    |Real.sqrt ((x + 1) * (x ^ (2 : ℕ) - s)) - Real.sqrt (2 * (1 - s))| ≤ 10 * (x - 1) := by
  set A : ℝ := Real.sqrt ((x + 1) * (x ^ (2 : ℕ) - s)) with hAdef
  set B : ℝ := Real.sqrt (2 * (1 - s)) with hBdef
  have hApos : 0 ≤ A := Real.sqrt_nonneg _
  have hA2 : A ^ (2 : ℕ) = (x + 1) * (x ^ (2 : ℕ) - s) := Real.sq_sqrt (by nlinarith)
  have hB2 : B ^ (2 : ℕ) = 2 * (1 - s) := Real.sq_sqrt (by linarith)
  have hB : (1 : ℝ) ≤ B := by
    rw [hBdef]
    exact Real.one_le_sqrt.mpr (by linarith)
  have hdiff : A ^ (2 : ℕ) - B ^ (2 : ℕ) = (x - 1) * (x ^ (2 : ℕ) + 2 * x + (2 - s)) := by
    rw [hA2, hB2]
    ring
  have hfac : (0 : ℝ) ≤ x - 1 := by linarith
  have hupper : A ^ (2 : ℕ) - B ^ (2 : ℕ) ≤ 10 * (x - 1) := by
    rw [hdiff]
    nlinarith [mul_nonneg hfac
      (by nlinarith [hx2, hs0] : (0 : ℝ) ≤ 10 - (x ^ (2 : ℕ) + 2 * x + (2 - s)))]
  have hlower : -(10 * (x - 1)) ≤ A ^ (2 : ℕ) - B ^ (2 : ℕ) := by
    rw [hdiff]
    nlinarith [mul_nonneg hfac
      (by nlinarith [hx1, hs1] : (0 : ℝ) ≤ x ^ (2 : ℕ) + 2 * x + (2 - s))]
  rw [abs_le]
  constructor
  · nlinarith [hlower, hApos, hB, hx1]
  · nlinarith [hupper, hApos, hB, hx1]

/-- **The endpoint cancellation.**  The numerator of the divergent difference is one full power
smaller than either of its terms. -/
theorem abs_mul_xiEndpointPhase_sub_sqrt_le {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hx1 : 1 ≤ x) (hx2 : x ≤ 2) :
    |x * xiEndpointPhase s x - Real.sqrt (x ^ (2 : ℕ) - 1) * Real.sqrt (x ^ (2 : ℕ) - s)|
      ≤ 16 * ((x - 1) * Real.sqrt (x - 1)) := by
  have hm1 : (0 : ℝ) ≤ x - 1 := by linarith
  have hp1 : (0 : ℝ) ≤ x + 1 := by linarith
  have hs : (0 : ℝ) ≤ Real.sqrt (x - 1) := Real.sqrt_nonneg _
  have hxs : (0 : ℝ) ≤ x ^ (2 : ℕ) - s := by nlinarith
  -- split the square root at the endpoint
  have hsplit : Real.sqrt (x ^ (2 : ℕ) - 1) * Real.sqrt (x ^ (2 : ℕ) - s)
      = Real.sqrt (x - 1) * Real.sqrt ((x + 1) * (x ^ (2 : ℕ) - s)) := by
    rw [show x ^ (2 : ℕ) - 1 = (x - 1) * (x + 1) by ring, Real.sqrt_mul hm1,
      Real.sqrt_mul hp1, mul_assoc]
  -- the two contributions
  have hexp := abs_xiEndpointPhase_sub_leading_le hs0 hs1 hx1
  have hlip := abs_sqrt_prod_sub_le hs0 hs1 hx1 hx2
  have hB2 : (2 : ℝ) * xiEndpointFactor s 1 = Real.sqrt (2 * (1 - s)) :=
    two_xiEndpointFactor_one_eq s
  have hBle : Real.sqrt (2 * (1 - s)) ≤ 2 := by
    have h4 : Real.sqrt (2 * (1 - s)) ^ (2 : ℕ) = 2 * (1 - s) := Real.sq_sqrt (by linarith)
    nlinarith [Real.sqrt_nonneg (2 * (1 - s)), h4, hs0]
  have hdecomp : x * xiEndpointPhase s x - Real.sqrt (x ^ (2 : ℕ) - 1) * Real.sqrt (x ^ (2 : ℕ) - s)
      = x * (xiEndpointPhase s x - 2 * xiEndpointFactor s 1 * Real.sqrt (x - 1))
        + Real.sqrt (x - 1) * (Real.sqrt (2 * (1 - s)) * x
            - Real.sqrt ((x + 1) * (x ^ (2 : ℕ) - s))) := by
    rw [hsplit, ← hB2]
    ring
  rw [hdecomp]
  refine le_trans (abs_add_le _ _) ?_
  have h1 : |x * (xiEndpointPhase s x - 2 * xiEndpointFactor s 1 * Real.sqrt (x - 1))|
      ≤ 4 * ((x - 1) * Real.sqrt (x - 1)) := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)]
    have hnn : (0 : ℝ) ≤ (x - 1) * Real.sqrt (x - 1) := by positivity
    nlinarith [hexp, hx2, hnn]
  have h2 : |Real.sqrt (x - 1) * (Real.sqrt (2 * (1 - s)) * x
        - Real.sqrt ((x + 1) * (x ^ (2 : ℕ) - s)))|
      ≤ 12 * ((x - 1) * Real.sqrt (x - 1)) := by
    rw [abs_mul, abs_of_nonneg hs]
    have hinner : |Real.sqrt (2 * (1 - s)) * x - Real.sqrt ((x + 1) * (x ^ (2 : ℕ) - s))|
        ≤ 12 * (x - 1) := by
      have hrw : Real.sqrt (2 * (1 - s)) * x - Real.sqrt ((x + 1) * (x ^ (2 : ℕ) - s))
          = Real.sqrt (2 * (1 - s)) * (x - 1)
            + (Real.sqrt (2 * (1 - s)) - Real.sqrt ((x + 1) * (x ^ (2 : ℕ) - s))) := by ring
      rw [hrw]
      refine le_trans (abs_add_le _ _) ?_
      have ha : |Real.sqrt (2 * (1 - s)) * (x - 1)| ≤ 2 * (x - 1) := by
        rw [abs_mul, abs_of_nonneg hm1, abs_of_nonneg (Real.sqrt_nonneg _)]
        nlinarith [hBle, hm1, Real.sqrt_nonneg (2 * (1 - s))]
      have hb : |Real.sqrt (2 * (1 - s)) - Real.sqrt ((x + 1) * (x ^ (2 : ℕ) - s))|
          ≤ 10 * (x - 1) := by
        rw [abs_sub_comm]
        exact hlip
      linarith
    have hnn : (0 : ℝ) ≤ Real.sqrt (x - 1) := hs
    nlinarith [hinner, hnn]
  linarith

/-- **The divergent terms cancel.**  The difference of the two `(x-1)^{-1/2}` singularities in the
logarithmic derivative of Dunster's weight is not merely bounded: it vanishes at the endpoint, at
rate `(x-1)^{1/2}`. -/
theorem abs_endpoint_logDeriv_diff_le {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hx1 : 1 < x) (hx2 : x ≤ 2) :
    |x / (2 * Real.sqrt (x ^ (2 : ℕ) - 1) * Real.sqrt (x ^ (2 : ℕ) - s))
        - 1 / (2 * xiEndpointPhase s x)| ≤ 8 * Real.sqrt (x - 1) := by
  have hm1 : (0 : ℝ) < x - 1 := by linarith
  have hu : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hv : (0 : ℝ) < x ^ (2 : ℕ) - s := by nlinarith
  have hsu : (0 : ℝ) < Real.sqrt (x ^ (2 : ℕ) - 1) := Real.sqrt_pos.mpr hu
  have hsv : (0 : ℝ) < Real.sqrt (x ^ (2 : ℕ) - s) := Real.sqrt_pos.mpr hv
  have hs1pos : (0 : ℝ) < Real.sqrt (1 - s) := Real.sqrt_pos.mpr (by linarith)
  have hbracket : Real.sqrt (1 - s) * Real.sqrt (x ^ (2 : ℕ) - 1) ≤ xiEndpointPhase s x :=
    (xiEndpointPhase_bounds hs0 (by linarith) (le_of_lt hx1)).1
  have hr : (0 : ℝ) < xiEndpointPhase s x := by
    linarith [mul_pos hs1pos hsu, hbracket]
  have hsm : (0 : ℝ) < Real.sqrt (x - 1) := Real.sqrt_pos.mpr hm1
  -- common denominator
  have hcomb : x / (2 * Real.sqrt (x ^ (2 : ℕ) - 1) * Real.sqrt (x ^ (2 : ℕ) - s))
      - 1 / (2 * xiEndpointPhase s x)
      = (x * xiEndpointPhase s x - Real.sqrt (x ^ (2 : ℕ) - 1) * Real.sqrt (x ^ (2 : ℕ) - s))
        / (2 * xiEndpointPhase s x * Real.sqrt (x ^ (2 : ℕ) - 1) * Real.sqrt (x ^ (2 : ℕ) - s)) := by
    field_simp
  -- the denominator is at least twice the endpoint distance
  have hsvge : Real.sqrt (1 - s) ≤ Real.sqrt (x ^ (2 : ℕ) - s) := Real.sqrt_le_sqrt (by nlinarith)
  have hs1s : Real.sqrt (1 - s) * Real.sqrt (1 - s) = 1 - s :=
    Real.mul_self_sqrt (by linarith)
  have huu : Real.sqrt (x ^ (2 : ℕ) - 1) * Real.sqrt (x ^ (2 : ℕ) - 1) = x ^ (2 : ℕ) - 1 :=
    Real.mul_self_sqrt hu.le
  have hden : 2 * (x - 1)
      ≤ 2 * xiEndpointPhase s x * Real.sqrt (x ^ (2 : ℕ) - 1) * Real.sqrt (x ^ (2 : ℕ) - s) := by
    have hstep : 2 * (Real.sqrt (1 - s) * Real.sqrt (x ^ (2 : ℕ) - 1)) * Real.sqrt (x ^ (2 : ℕ) - 1)
        * Real.sqrt (1 - s)
        ≤ 2 * xiEndpointPhase s x * Real.sqrt (x ^ (2 : ℕ) - 1) * Real.sqrt (x ^ (2 : ℕ) - s) := by
      gcongr
    have hval : 2 * (Real.sqrt (1 - s) * Real.sqrt (x ^ (2 : ℕ) - 1)) * Real.sqrt (x ^ (2 : ℕ) - 1)
        * Real.sqrt (1 - s) = 2 * (1 - s) * (x ^ (2 : ℕ) - 1) := by
      calc 2 * (Real.sqrt (1 - s) * Real.sqrt (x ^ (2 : ℕ) - 1)) * Real.sqrt (x ^ (2 : ℕ) - 1)
            * Real.sqrt (1 - s)
          = 2 * (Real.sqrt (1 - s) * Real.sqrt (1 - s))
              * (Real.sqrt (x ^ (2 : ℕ) - 1) * Real.sqrt (x ^ (2 : ℕ) - 1)) := by ring
        _ = 2 * (1 - s) * (x ^ (2 : ℕ) - 1) := by rw [hs1s, huu]
    rw [hval] at hstep
    nlinarith [hstep, hx1, hs1, hm1]
  have hdpos : (0 : ℝ)
      < 2 * xiEndpointPhase s x * Real.sqrt (x ^ (2 : ℕ) - 1) * Real.sqrt (x ^ (2 : ℕ) - s) := by positivity
  rw [hcomb, abs_div, abs_of_pos hdpos, div_le_iff₀ hdpos]
  have hnum := abs_mul_xiEndpointPhase_sub_sqrt_le hs0 hs1 (le_of_lt hx1) hx2
  nlinarith [hnum, hden, hsm.le, hm1.le]


/-- The regular term of the logarithmic derivative is bounded on the compact exterior range. -/
theorem abs_endpoint_logDeriv_regular_le {s x : ℝ} (hs1 : s ≤ 1 / 2)
    (hx1 : 1 < x) (hx2 : x ≤ 2) :
    |3 * x * Real.sqrt (x ^ (2 : ℕ) - 1)
        / (2 * (x ^ (2 : ℕ) - s) * Real.sqrt (x ^ (2 : ℕ) - s))| ≤ 24 := by
  have hu : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hv : (1 : ℝ) / 2 ≤ x ^ (2 : ℕ) - s := by nlinarith
  have hvpos : (0 : ℝ) < x ^ (2 : ℕ) - s := by linarith
  have hsu : Real.sqrt (x ^ (2 : ℕ) - 1) ≤ 2 := by
    have h : Real.sqrt (x ^ (2 : ℕ) - 1) ^ (2 : ℕ) = x ^ (2 : ℕ) - 1 := Real.sq_sqrt hu.le
    nlinarith [Real.sqrt_nonneg (x ^ (2 : ℕ) - 1), h, hx2, hx1]
  have hsvpos : (0 : ℝ) < Real.sqrt (x ^ (2 : ℕ) - s) := Real.sqrt_pos.mpr hvpos
  have hsv : (1 : ℝ) / 2 ≤ Real.sqrt (x ^ (2 : ℕ) - s) := by
    have h : Real.sqrt (x ^ (2 : ℕ) - s) ^ (2 : ℕ) = x ^ (2 : ℕ) - s := Real.sq_sqrt hvpos.le
    nlinarith [hsvpos, h, hv]
  have hnum : |3 * x * Real.sqrt (x ^ (2 : ℕ) - 1)| ≤ 12 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [hsu, hx2, hx1, Real.sqrt_nonneg (x ^ (2 : ℕ) - 1)]
  have hdpos : (0 : ℝ) < 2 * (x ^ (2 : ℕ) - s) * Real.sqrt (x ^ (2 : ℕ) - s) := by positivity
  have hd : (1 : ℝ) / 2 ≤ 2 * (x ^ (2 : ℕ) - s) * Real.sqrt (x ^ (2 : ℕ) - s) := by
    nlinarith [hv, hsv, hvpos, hsvpos]
  rw [abs_div, abs_of_pos hdpos, div_le_iff₀ hdpos]
  nlinarith [hnum, hd]

/-- **The logarithmic derivative of Dunster's weight is bounded on the compact exterior range.**
The two divergent terms cancel to `O((x-1)^{1/2})` and the regular term is bounded outright. -/
theorem abs_besselWeight_logDeriv_le {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hx1 : 1 < x) (hx2 : x ≤ 2) :
    |x / (2 * Real.sqrt (x ^ (2 : ℕ) - 1) * Real.sqrt (x ^ (2 : ℕ) - s))
        - 1 / (2 * xiEndpointPhase s x)
        - 3 * x * Real.sqrt (x ^ (2 : ℕ) - 1) / (2 * (x ^ (2 : ℕ) - s) * Real.sqrt (x ^ (2 : ℕ) - s))| ≤ 32 := by
  have hcancel := abs_endpoint_logDeriv_diff_le hs0 hs1 hx1 hx2
  have hreg := abs_endpoint_logDeriv_regular_le hs1 hx1 hx2
  have hsm : Real.sqrt (x - 1) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  refine le_trans (abs_sub _ _) ?_
  linarith [hcancel, hreg, hsm]


end GaloisForLFunctions.RHTower
