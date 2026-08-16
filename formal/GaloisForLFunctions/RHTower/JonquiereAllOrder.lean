import GaloisForLFunctions.RHTower.JonquiereChannel
import GaloisForLFunctions.RHTower.JonquiereExpansion

/-!
# Jonquière's expansion to every order

The boundary germ of `∑ n^{-s} e^{inθ}` splits into the singular power `Γ(1-s)(-iθ)^{s-1}` and the
convergent regular series `∑_{k ≥ 0} ζ(s-k) (iθ)^k / k!`, with an explicit remainder of order
`θ^{K+1}` after `K+1` regular terms.
-/

open Complex HurwitzZeta Filter Topology Set

namespace RHTower

/-- The `K`-th order regular part of the Jonquière expansion. -/
noncomputable def jonquiereRegPoly (s : ℂ) (K : ℕ) (θ : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (K + 1), jonquiereRegCoeff s k * ((θ : ℝ) : ℂ) ^ k

theorem jonquiereRegPoly_eq (s : ℂ) (K : ℕ) (θ : ℝ) :
    jonquiereRegPoly s K θ
      = riemannZeta s
        + ∑ j ∈ Finset.range K, jonquiereRegCoeff s (j + 1) * ((θ : ℝ) : ℂ) ^ (j + 1) := by
  rw [jonquiereRegPoly, Finset.sum_range_succ' (fun k =>
    jonquiereRegCoeff s k * ((θ : ℝ) : ℂ) ^ k) K]
  simp only [pow_zero, mul_one, jonquiereRegCoeff, Nat.cast_zero, sub_zero, pow_zero,
    Nat.factorial_zero, Nat.cast_one, div_one]
  ring

/-- The Taylor part of the shift-difference series assembles into the regular Jonquière terms. -/
theorem jonquiere_taylor_sum_eq {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (K : ℕ) {θ : ℝ}
    (hθ : 0 < θ) :
    ((2 * (Real.pi : ℂ))) ^ (-(1 - s)) * Complex.Gamma (1 - s)
        * (Complex.exp (↑Real.pi * I * (1 - s) / 2)
              * shiftZetaTaylor (θ / (2 * Real.pi)) (1 - s) K
            + Complex.exp (-↑Real.pi * I * (1 - s) / 2)
              * shiftZetaTaylor (-(θ / (2 * Real.pi))) (1 - s) K)
      = ∑ j ∈ Finset.range K, jonquiereRegCoeff s (j + 1) * ((θ : ℝ) : ℂ) ^ (j + 1) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hTr : (((2 * Real.pi : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hcast : ((2 * (Real.pi : ℂ))) = (((2 * Real.pi : ℝ)) : ℂ) := by push_cast; ring
  set a : ℝ := θ / (2 * Real.pi) with ha
  set w : ℂ := 1 - s with hw
  rw [shiftZetaTaylor, shiftZetaTaylor, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hneg : ((-a : ℝ) : ℂ) ^ (j + 1) = ((-1 : ℂ) ^ (j + 1)) * ((a : ℝ) : ℂ) ^ (j + 1) := by
    push_cast
    rw [← mul_pow]
    ring
  have hchannel := jonquiere_channel_coeff h0 h1 (j + 1)
  have hzarg : w + ((j : ℂ) + 1) = (1 - s) + (((j + 1 : ℕ) : ℂ)) := by
    rw [hw]
    push_cast
    ring
  have hsplit : (((2 * Real.pi : ℝ)) : ℂ) ^ (-(1 - s))
      = (((2 * Real.pi : ℝ)) : ℂ) ^ (-(1 - s) - (((j + 1 : ℕ) : ℂ)))
        * (((2 * Real.pi : ℝ)) : ℂ) ^ (j + 1) := by
    rw [← Complex.cpow_natCast (((2 * Real.pi : ℝ)) : ℂ) (j + 1), ← Complex.cpow_add _ _ hTr]
    congr 1
    ring
  have hpowθ : (((2 * Real.pi : ℝ)) : ℂ) ^ (j + 1) * ((a : ℝ) : ℂ) ^ (j + 1)
      = ((θ : ℝ) : ℂ) ^ (j + 1) := by
    rw [← mul_pow, ← Complex.ofReal_mul, ha]
    congr 2
    field_simp
  rw [hcast, hneg, hzarg, hsplit]
  calc (((2 * Real.pi : ℝ)) : ℂ) ^ (-(1 - s) - (((j + 1 : ℕ) : ℂ)))
        * (((2 * Real.pi : ℝ)) : ℂ) ^ (j + 1) * Complex.Gamma (1 - s)
        * (Complex.exp (↑Real.pi * I * (1 - s) / 2)
            * (shiftTaylorCoeff w (j + 1) * ((a : ℝ) : ℂ) ^ (j + 1)
              * riemannZeta ((1 - s) + ((j + 1 : ℕ) : ℂ)))
          + Complex.exp (-↑Real.pi * I * (1 - s) / 2)
            * (shiftTaylorCoeff w (j + 1) * (((-1 : ℂ) ^ (j + 1)) * ((a : ℝ) : ℂ) ^ (j + 1))
              * riemannZeta ((1 - s) + ((j + 1 : ℕ) : ℂ))))
      = ((((2 * Real.pi : ℝ)) : ℂ) ^ (-(1 - s) - (((j + 1 : ℕ) : ℂ))) * Complex.Gamma (1 - s)
          * (Complex.exp (↑Real.pi * I * (1 - s) / 2)
              + (-1 : ℂ) ^ (j + 1) * Complex.exp (-↑Real.pi * I * (1 - s) / 2))
          * shiftTaylorCoeff (1 - s) (j + 1)
          * riemannZeta ((1 - s) + ((j + 1 : ℕ) : ℂ)))
        * ((((2 * Real.pi : ℝ)) : ℂ) ^ (j + 1) * ((a : ℝ) : ℂ) ^ (j + 1)) := by
        rw [hw]
        ring
    _ = jonquiereRegCoeff s (j + 1) * ((θ : ℝ) : ℂ) ^ (j + 1) := by
        rw [hchannel, hpowθ]

/-- The `K`-th order Jonquière remainder. -/
noncomputable def jonquiereRemainderOrder (s : ℂ) (K : ℕ) (θ : ℝ) : ℂ :=
  ((2 * (Real.pi : ℂ))) ^ (-(1 - s)) * Complex.Gamma (1 - s)
    * (Complex.exp (↑Real.pi * I * (1 - s) / 2)
        * (shiftDiffSeries (θ / (2 * Real.pi)) (1 - s)
            - shiftZetaTaylor (θ / (2 * Real.pi)) (1 - s) K)
      + Complex.exp (-↑Real.pi * I * (1 - s) / 2)
        * (shiftDiffSeries (-(θ / (2 * Real.pi))) (1 - s)
            - shiftZetaTaylor (-(θ / (2 * Real.pi))) (1 - s) K))

/-- **Jonquière's expansion to every order, exact form.**  This is the card's `(3)`. -/
theorem expZeta_eq_jonquiere_order {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (K : ℕ) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi) :
    expZeta ((θ / (2 * Real.pi) : ℝ) : UnitAddCircle) s
      = jonquiereLead s * ((θ : ℝ) : ℂ) ^ (s - 1) + jonquiereRegPoly s K θ
        + jonquiereRemainderOrder s K θ := by
  rw [expZeta_eq_jonquiere h0 h1 hθ0 hθ1, jonquiereRegPoly_eq,
    ← jonquiere_taylor_sum_eq h0 h1 K hθ0, jonquiereRemainder, jonquiereRemainderOrder]
  ring

/-- The explicit constant in the `K`-th order Jonquière remainder bound. -/
noncomputable def jonquiereOrderConst (s : ℂ) (K : ℕ) : ℝ :=
  ‖((2 * (Real.pi : ℂ))) ^ (-(1 - s))‖ * ‖Complex.Gamma (1 - s)‖
    * ((‖Complex.exp (↑Real.pi * I * (1 - s) / 2)‖
        + ‖Complex.exp (-↑Real.pi * I * (1 - s) / 2)‖)
      * (shiftTaylorConst (1 - s) K
          * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 - s).re - (K : ℝ) - 1))))
    / (2 * Real.pi) ^ (K + 1)

theorem jonquiereOrderConst_nonneg (s : ℂ) (K : ℕ) : 0 ≤ jonquiereOrderConst s K := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsum : 0 ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 - s).re - (K : ℝ) - 1) :=
    tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _
  have hC : 0 ≤ shiftTaylorConst (1 - s) K := shiftTaylorConst_nonneg _ _
  rw [jonquiereOrderConst]
  positivity

/-- **The `K`-th order Jonquière remainder bound.** -/
theorem norm_jonquiereRemainderOrder_le {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (K : ℕ) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi) :
    ‖jonquiereRemainderOrder s K θ‖ ≤ jonquiereOrderConst s K * θ ^ (K + 1) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set a : ℝ := θ / (2 * Real.pi) with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : |a| ≤ 1 / 2 := by
    rw [abs_of_pos ha0, ha, div_le_iff₀ (by positivity)]
    linarith
  have ha1' : |(-a)| ≤ 1 / 2 := by rwa [abs_neg]
  set w : ℂ := 1 - s with hw
  have hwre : 0 < w.re := by rw [hw]; simp; linarith
  set M : ℝ := shiftTaylorConst w K * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-w.re - (K : ℝ) - 1)) with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    have hsum : 0 ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (-w.re - (K : ℝ) - 1) :=
      tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _
    exact mul_nonneg (shiftTaylorConst_nonneg _ _) hsum
  have hD1 : ‖shiftDiffSeries a w - shiftZetaTaylor a w K‖ ≤ M * a ^ (K + 1) := by
    have h := norm_shiftDiffSeries_sub_taylor_le K hwre ha1
    rwa [abs_of_pos ha0, ← hM] at h
  have hD2 : ‖shiftDiffSeries (-a) w - shiftZetaTaylor (-a) w K‖ ≤ M * a ^ (K + 1) := by
    have h := norm_shiftDiffSeries_sub_taylor_le K hwre ha1'
    rwa [abs_neg, abs_of_pos ha0, ← hM] at h
  set E₁ : ℂ := Complex.exp (↑Real.pi * I * w / 2) with hE₁
  set E₂ : ℂ := Complex.exp (-↑Real.pi * I * w / 2) with hE₂
  have hstep : ‖E₁ * (shiftDiffSeries a w - shiftZetaTaylor a w K)
      + E₂ * (shiftDiffSeries (-a) w - shiftZetaTaylor (-a) w K)‖
      ≤ (‖E₁‖ + ‖E₂‖) * (M * a ^ (K + 1)) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have hnn : 0 ≤ M * a ^ (K + 1) := le_trans (norm_nonneg _) hD1
    nlinarith [norm_nonneg E₁, norm_nonneg E₂, hD1, hD2]
  rw [jonquiereRemainderOrder, ← hw, ← ha, ← hE₁, ← hE₂, norm_mul, norm_mul]
  have hfin : ‖((2 * (Real.pi : ℂ))) ^ (-w)‖ * ‖Complex.Gamma w‖
      * ‖E₁ * (shiftDiffSeries a w - shiftZetaTaylor a w K)
          + E₂ * (shiftDiffSeries (-a) w - shiftZetaTaylor (-a) w K)‖
      ≤ ‖((2 * (Real.pi : ℂ))) ^ (-w)‖ * ‖Complex.Gamma w‖
        * ((‖E₁‖ + ‖E₂‖) * (M * a ^ (K + 1))) := by
    refine mul_le_mul_of_nonneg_left hstep ?_
    positivity
  refine hfin.trans ?_
  rw [jonquiereOrderConst, ← hw, ← hE₁, ← hE₂, ← hM, ha, div_pow]
  field_simp
  exact le_rfl

/-- **The all-order boundary germ of the polylogarithm.** -/
theorem norm_expZeta_sub_jonquiereRegPoly_le {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (K : ℕ)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi) :
    ‖expZeta ((θ / (2 * Real.pi) : ℝ) : UnitAddCircle) s
        - (jonquiereLead s * ((θ : ℝ) : ℂ) ^ (s - 1) + jonquiereRegPoly s K θ)‖
      ≤ jonquiereOrderConst s K * θ ^ (K + 1) := by
  rw [expZeta_eq_jonquiere_order h0 h1 K hθ0 hθ1,
    show jonquiereLead s * ((θ : ℝ) : ℂ) ^ (s - 1) + jonquiereRegPoly s K θ
      + jonquiereRemainderOrder s K θ
      - (jonquiereLead s * ((θ : ℝ) : ℂ) ^ (s - 1) + jonquiereRegPoly s K θ)
      = jonquiereRemainderOrder s K θ by ring]
  exact norm_jonquiereRemainderOrder_le h0 h1 K hθ0 hθ1

/-! ## The reflected phase, to every order -/

/-- The reflected Taylor part assembles into the regular Jonquière terms at `-θ`. -/
theorem jonquiere_taylor_sum_neg_eq {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (K : ℕ) {θ : ℝ}
    (hθ : 0 < θ) :
    ((2 * (Real.pi : ℂ))) ^ (-(1 - s)) * Complex.Gamma (1 - s)
        * (Complex.exp (↑Real.pi * I * (1 - s) / 2)
              * shiftZetaTaylor (-(θ / (2 * Real.pi))) (1 - s) K
            + Complex.exp (-↑Real.pi * I * (1 - s) / 2)
              * shiftZetaTaylor (θ / (2 * Real.pi)) (1 - s) K)
      = ∑ j ∈ Finset.range K, jonquiereRegCoeff s (j + 1) * (((-θ : ℝ)) : ℂ) ^ (j + 1) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hTr : (((2 * Real.pi : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hcast : ((2 * (Real.pi : ℂ))) = (((2 * Real.pi : ℝ)) : ℂ) := by push_cast; ring
  set a : ℝ := θ / (2 * Real.pi) with ha
  set w : ℂ := 1 - s with hw
  rw [shiftZetaTaylor, shiftZetaTaylor, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hneg : ((-a : ℝ) : ℂ) ^ (j + 1) = ((-1 : ℂ) ^ (j + 1)) * ((a : ℝ) : ℂ) ^ (j + 1) := by
    push_cast
    rw [← mul_pow]
    ring
  have hnegθ : (((-θ : ℝ)) : ℂ) ^ (j + 1) = ((-1 : ℂ) ^ (j + 1)) * ((θ : ℝ) : ℂ) ^ (j + 1) := by
    push_cast
    rw [← mul_pow]
    ring
  have hone : ((-1 : ℂ) ^ (j + 1)) * ((-1 : ℂ) ^ (j + 1)) = 1 := by
    rw [← mul_pow]
    norm_num
  have hchannel := jonquiere_channel_coeff h0 h1 (j + 1)
  have hzarg : w + ((j : ℂ) + 1) = (1 - s) + (((j + 1 : ℕ) : ℂ)) := by
    rw [hw]
    push_cast
    ring
  have hsplit : (((2 * Real.pi : ℝ)) : ℂ) ^ (-(1 - s))
      = (((2 * Real.pi : ℝ)) : ℂ) ^ (-(1 - s) - (((j + 1 : ℕ) : ℂ)))
        * (((2 * Real.pi : ℝ)) : ℂ) ^ (j + 1) := by
    rw [← Complex.cpow_natCast (((2 * Real.pi : ℝ)) : ℂ) (j + 1), ← Complex.cpow_add _ _ hTr]
    congr 1
    ring
  have hpowθ : (((2 * Real.pi : ℝ)) : ℂ) ^ (j + 1) * ((a : ℝ) : ℂ) ^ (j + 1)
      = ((θ : ℝ) : ℂ) ^ (j + 1) := by
    rw [← mul_pow, ← Complex.ofReal_mul, ha]
    congr 2
    field_simp
  rw [hcast, hneg, hnegθ, hzarg, hsplit]
  calc (((2 * Real.pi : ℝ)) : ℂ) ^ (-(1 - s) - (((j + 1 : ℕ) : ℂ)))
        * (((2 * Real.pi : ℝ)) : ℂ) ^ (j + 1) * Complex.Gamma (1 - s)
        * (Complex.exp (↑Real.pi * I * (1 - s) / 2)
            * (shiftTaylorCoeff w (j + 1) * (((-1 : ℂ) ^ (j + 1)) * ((a : ℝ) : ℂ) ^ (j + 1))
              * riemannZeta ((1 - s) + ((j + 1 : ℕ) : ℂ)))
          + Complex.exp (-↑Real.pi * I * (1 - s) / 2)
            * (shiftTaylorCoeff w (j + 1) * ((a : ℝ) : ℂ) ^ (j + 1)
              * riemannZeta ((1 - s) + ((j + 1 : ℕ) : ℂ))))
      = ((((2 * Real.pi : ℝ)) : ℂ) ^ (-(1 - s) - (((j + 1 : ℕ) : ℂ))) * Complex.Gamma (1 - s)
          * (Complex.exp (↑Real.pi * I * (1 - s) / 2)
              + (-1 : ℂ) ^ (j + 1) * Complex.exp (-↑Real.pi * I * (1 - s) / 2))
          * shiftTaylorCoeff (1 - s) (j + 1)
          * riemannZeta ((1 - s) + ((j + 1 : ℕ) : ℂ)))
        * ((((2 * Real.pi : ℝ)) : ℂ) ^ (j + 1) * ((a : ℝ) : ℂ) ^ (j + 1))
        * ((-1 : ℂ) ^ (j + 1))
        + (((2 * Real.pi : ℝ)) : ℂ) ^ (-(1 - s) - (((j + 1 : ℕ) : ℂ)))
          * (((2 * Real.pi : ℝ)) : ℂ) ^ (j + 1) * Complex.Gamma (1 - s)
          * Complex.exp (-↑Real.pi * I * (1 - s) / 2)
          * (shiftTaylorCoeff w (j + 1) * ((a : ℝ) : ℂ) ^ (j + 1)
              * riemannZeta ((1 - s) + ((j + 1 : ℕ) : ℂ)))
          * (1 - ((-1 : ℂ) ^ (j + 1)) * ((-1 : ℂ) ^ (j + 1))) := by
        rw [hw]
        ring
    _ = jonquiereRegCoeff s (j + 1) * (((-1 : ℂ) ^ (j + 1)) * ((θ : ℝ) : ℂ) ^ (j + 1)) := by
        rw [hchannel, hpowθ, hone]
        ring

/-- The `K`-th order Jonquière remainder at a reflected phase. -/
noncomputable def jonquiereRemainderOrderNeg (s : ℂ) (K : ℕ) (θ : ℝ) : ℂ :=
  ((2 * (Real.pi : ℂ))) ^ (-(1 - s)) * Complex.Gamma (1 - s)
    * (Complex.exp (↑Real.pi * I * (1 - s) / 2)
        * (shiftDiffSeries (-(θ / (2 * Real.pi))) (1 - s)
            - shiftZetaTaylor (-(θ / (2 * Real.pi))) (1 - s) K)
      + Complex.exp (-↑Real.pi * I * (1 - s) / 2)
        * (shiftDiffSeries (θ / (2 * Real.pi)) (1 - s)
            - shiftZetaTaylor (θ / (2 * Real.pi)) (1 - s) K))

/-- **Jonquière's expansion to every order at a reflected phase.** -/
theorem expZeta_neg_eq_jonquiere_order {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (K : ℕ) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi) :
    expZeta ((-(θ / (2 * Real.pi)) : ℝ) : UnitAddCircle) s
      = jonquiereLeadNeg s * ((θ : ℝ) : ℂ) ^ (s - 1) + jonquiereRegPoly s K (-θ)
        + jonquiereRemainderOrderNeg s K θ := by
  rw [expZeta_neg_eq_jonquiere h0 h1 hθ0 hθ1, jonquiereRegPoly_eq,
    ← jonquiere_taylor_sum_neg_eq h0 h1 K hθ0, jonquiereRemainderNeg, jonquiereRemainderOrderNeg]
  ring

/-- **The reflected `K`-th order Jonquière remainder bound.** -/
theorem norm_jonquiereRemainderOrderNeg_le {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (K : ℕ)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi) :
    ‖jonquiereRemainderOrderNeg s K θ‖ ≤ jonquiereOrderConst s K * θ ^ (K + 1) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set a : ℝ := θ / (2 * Real.pi) with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : |a| ≤ 1 / 2 := by
    rw [abs_of_pos ha0, ha, div_le_iff₀ (by positivity)]
    linarith
  have ha1' : |(-a)| ≤ 1 / 2 := by rwa [abs_neg]
  set w : ℂ := 1 - s with hw
  have hwre : 0 < w.re := by rw [hw]; simp; linarith
  set M : ℝ := shiftTaylorConst w K * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-w.re - (K : ℝ) - 1)) with hM
  have hD1 : ‖shiftDiffSeries a w - shiftZetaTaylor a w K‖ ≤ M * a ^ (K + 1) := by
    have h := norm_shiftDiffSeries_sub_taylor_le K hwre ha1
    rwa [abs_of_pos ha0, ← hM] at h
  have hD2 : ‖shiftDiffSeries (-a) w - shiftZetaTaylor (-a) w K‖ ≤ M * a ^ (K + 1) := by
    have h := norm_shiftDiffSeries_sub_taylor_le K hwre ha1'
    rwa [abs_neg, abs_of_pos ha0, ← hM] at h
  set E₁ : ℂ := Complex.exp (↑Real.pi * I * w / 2) with hE₁
  set E₂ : ℂ := Complex.exp (-↑Real.pi * I * w / 2) with hE₂
  have hstep : ‖E₁ * (shiftDiffSeries (-a) w - shiftZetaTaylor (-a) w K)
      + E₂ * (shiftDiffSeries a w - shiftZetaTaylor a w K)‖
      ≤ (‖E₁‖ + ‖E₂‖) * (M * a ^ (K + 1)) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have hnn : 0 ≤ M * a ^ (K + 1) := le_trans (norm_nonneg _) hD1
    nlinarith [norm_nonneg E₁, norm_nonneg E₂, hD1, hD2]
  rw [jonquiereRemainderOrderNeg, ← hw, ← ha, ← hE₁, ← hE₂, norm_mul, norm_mul]
  have hfin : ‖((2 * (Real.pi : ℂ))) ^ (-w)‖ * ‖Complex.Gamma w‖
      * ‖E₁ * (shiftDiffSeries (-a) w - shiftZetaTaylor (-a) w K)
          + E₂ * (shiftDiffSeries a w - shiftZetaTaylor a w K)‖
      ≤ ‖((2 * (Real.pi : ℂ))) ^ (-w)‖ * ‖Complex.Gamma w‖
        * ((‖E₁‖ + ‖E₂‖) * (M * a ^ (K + 1))) := by
    refine mul_le_mul_of_nonneg_left hstep ?_
    positivity
  refine hfin.trans ?_
  rw [jonquiereOrderConst, ← hw, ← hE₁, ← hE₂, ← hM, ha, div_pow]
  field_simp
  exact le_rfl

end RHTower
