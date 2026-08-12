import GaloisForLFunctions.RHTower.DeningerMeyerPeriodization
import GaloisForLFunctions.RHTower.DeningerMeyerSeminorm

/-!
# A period-uniform bound for the periodization

On one fundamental interval `0 ≤ t ≤ L` the lattice point `t + jL` is at distance at least
`(|j| - 1)L` from the origin, so the periodization is bounded by a geometric series with ratio
`e^{-L}` and no factor `e^{L}` in front.  For every period at least `log 2` this gives the bound

`‖Per_L h(t)‖ ≤ 5 q_{1,0}(h)`,

uniform in the period.  The crude estimate, which uses only `|t| ≤ L`, carries a factor `e^{L}` and
is too weak for an all-prime energy.

* `deningerLatticeDistance_ge` : **`|t + jL| ≥ (|j| - 1)L` on a fundamental interval.**
* `deningerLatticeMajorant_tsum` : the majorant sums to `Q(1 + 2/(1-r))`.
* `deningerPeriodizationSum_norm_le_period` : **the period-uniform bound.**
-/

namespace RHTower

open SchwartzMap

noncomputable section

/-! ## The lattice majorant -/

/-- The geometric lattice majorant with the fundamental-interval shift. -/
def deningerLatticeMajorant (Q r : ℝ) (j : ℤ) : ℝ := Q * r ^ (j.natAbs - 1)

theorem deningerLatticeMajorant_natCast (Q r : ℝ) (n : ℕ) :
    deningerLatticeMajorant Q r (n : ℤ) = Q * r ^ (n - 1) := by
  rw [deningerLatticeMajorant, Int.natAbs_natCast]

theorem deningerLatticeMajorant_negSucc (Q r : ℝ) (n : ℕ) :
    deningerLatticeMajorant Q r (-((n : ℤ) + 1)) = Q * r ^ n := by
  have hn : ((-((n : ℤ) + 1))).natAbs = n + 1 := by
    rw [Int.natAbs_neg]
    exact_mod_cast Int.natAbs_natCast (n + 1)
  rw [deningerLatticeMajorant, hn, Nat.add_sub_cancel]

theorem deningerLatticeMajorant_summable_nat {Q r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => deningerLatticeMajorant Q r (n : ℤ) := by
  have hgeo : Summable fun n : ℕ => Q * r ^ n := (summable_geometric_of_lt_one hr0 hr1).mul_left Q
  have hshift : Summable fun n : ℕ => deningerLatticeMajorant Q r ((n + 1 : ℕ) : ℤ) := by
    refine hgeo.congr fun n => ?_
    rw [deningerLatticeMajorant_natCast, Nat.add_sub_cancel]
  exact (summable_nat_add_iff 1).1 hshift

theorem deningerLatticeMajorant_summable_neg {Q r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => deningerLatticeMajorant Q r (-((n : ℤ) + 1)) := by
  have hgeo : Summable fun n : ℕ => Q * r ^ n := (summable_geometric_of_lt_one hr0 hr1).mul_left Q
  exact hgeo.congr fun n => (deningerLatticeMajorant_negSucc Q r n).symm

theorem deningerLatticeMajorant_summable {Q r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (deningerLatticeMajorant Q r) :=
  Summable.of_nat_of_neg_add_one (deningerLatticeMajorant_summable_nat hr0 hr1)
    (deningerLatticeMajorant_summable_neg hr0 hr1)

/-- The lattice majorant sums to `Q(1 + 2/(1-r))`. -/
theorem deningerLatticeMajorant_tsum {Q r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' j : ℤ, deningerLatticeMajorant Q r j) = Q + 2 * (Q * (1 - r)⁻¹) := by
  have hgeoval : (∑' n : ℕ, Q * r ^ n) = Q * (1 - r)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  rw [tsum_of_nat_of_neg_add_one (deningerLatticeMajorant_summable_nat hr0 hr1)
      (deningerLatticeMajorant_summable_neg hr0 hr1)]
  have hposval : (∑' n : ℕ, deningerLatticeMajorant Q r (n : ℤ)) = Q + Q * (1 - r)⁻¹ := by
    rw [(deningerLatticeMajorant_summable_nat hr0 hr1).tsum_eq_zero_add]
    have h0 : deningerLatticeMajorant Q r ((0 : ℕ) : ℤ) = Q := by
      rw [deningerLatticeMajorant_natCast]
      simp
    have htail : (fun n : ℕ => deningerLatticeMajorant Q r ((n + 1 : ℕ) : ℤ))
        = fun n : ℕ => Q * r ^ n := by
      funext n
      rw [deningerLatticeMajorant_natCast, Nat.add_sub_cancel]
    rw [h0, htail, hgeoval]
  have hnegval : (∑' n : ℕ, deningerLatticeMajorant Q r (-((n : ℤ) + 1))) = Q * (1 - r)⁻¹ := by
    have htail : (fun n : ℕ => deningerLatticeMajorant Q r (-((n : ℤ) + 1)))
        = fun n : ℕ => Q * r ^ n := funext fun n => deningerLatticeMajorant_negSucc Q r n
    rw [htail, hgeoval]
  rw [hposval, hnegval]
  ring

/-! ## The fundamental-interval estimate -/

/-- **On a fundamental interval the lattice point is at distance at least `(|j|-1)L`.** -/
theorem deningerLatticeDistance_ge {L : ℝ} (hL : 0 < L) {t : ℝ} (ht0 : 0 ≤ t) (htL : t ≤ L)
    (j : ℤ) : ((j.natAbs - 1 : ℕ) : ℝ) * L ≤ |t + (j : ℝ) * L| := by
  rcases lt_trichotomy j 0 with hj | hj | hj
  · have hjneg : (j : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hj
    have hle : t + (j : ℝ) * L ≤ 0 := by nlinarith
    rw [abs_of_nonpos hle]
    have hcastint : ((j.natAbs - 1 : ℕ) : ℤ) = -j - 1 := by omega
    have hcast : ((j.natAbs - 1 : ℕ) : ℝ) = -(j : ℝ) - 1 := by exact_mod_cast hcastint
    rw [hcast]
    nlinarith
  · subst hj
    simp
  · have hjpos : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hnn : 0 ≤ t + (j : ℝ) * L := by nlinarith
    rw [abs_of_nonneg hnn]
    have hcastint : ((j.natAbs - 1 : ℕ) : ℤ) = j - 1 := by omega
    have hcast : ((j.natAbs - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by exact_mod_cast hcastint
    rw [hcast]
    nlinarith

/-- Every lattice term is dominated by the geometric majorant. -/
theorem deningerFundamentalMajorant {h : DeningerExpSchwartz} {L : ℝ} (hL : 0 < L) {t : ℝ}
    (ht0 : 0 ≤ t) (htL : t ≤ L) (j : ℤ) :
    ‖((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (t + (j : ℝ) * L)‖
      ≤ deningerLatticeMajorant (deningerMeyerSeminormFun 1 0 h) (Real.exp (-L)) j := by
  have hw := deningerMeyerWeight_le 1 0 h (t + (j : ℝ) * L)
  rw [deningerMeyerWeight, norm_iteratedFDeriv_zero, one_mul] at hw
  have hexp : Real.exp (-|t + (j : ℝ) * L|) * Real.exp (|t + (j : ℝ) * L|) = 1 := by
    rw [← Real.exp_add]
    simp
  have h1 : ‖((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (t + (j : ℝ) * L)‖
      ≤ deningerMeyerSeminormFun 1 0 h * Real.exp (-|t + (j : ℝ) * L|) := by
    calc ‖((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (t + (j : ℝ) * L)‖
        = Real.exp (-|t + (j : ℝ) * L|)
          * (Real.exp (|t + (j : ℝ) * L|)
            * ‖((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (t + (j : ℝ) * L)‖) := by
          rw [← mul_assoc, hexp, one_mul]
      _ ≤ Real.exp (-|t + (j : ℝ) * L|) * deningerMeyerSeminormFun 1 0 h :=
          mul_le_mul_of_nonneg_left hw (Real.exp_pos _).le
      _ = deningerMeyerSeminormFun 1 0 h * Real.exp (-|t + (j : ℝ) * L|) := mul_comm _ _
  refine h1.trans ?_
  rw [deningerLatticeMajorant]
  have hgeom : Real.exp (-|t + (j : ℝ) * L|) ≤ (Real.exp (-L)) ^ (j.natAbs - 1) := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    have := deningerLatticeDistance_ge hL ht0 htL j
    nlinarith
  exact mul_le_mul_of_nonneg_left hgeom (deningerMeyerSeminormFun_nonneg 1 0 h)

/-- **The period-uniform bound.**  On a fundamental interval of a period at least `log 2`, the
periodization is at most five times the order-zero Meyer seminorm. -/
theorem deningerPeriodizationSum_norm_le_period {h : DeningerExpSchwartz} {L : ℝ}
    (hL : Real.log 2 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (htL : t ≤ L) :
    ‖deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L t‖
      ≤ 5 * deningerMeyerSeminormFun 1 0 h := by
  have hQ : 0 ≤ deningerMeyerSeminormFun 1 0 h := deningerMeyerSeminormFun_nonneg 1 0 h
  have hLpos : 0 < L := lt_of_lt_of_le (Real.log_pos one_lt_two) hL
  have hr0 : (0 : ℝ) ≤ Real.exp (-L) := (Real.exp_pos _).le
  have hrhalf : Real.exp (-L) ≤ 1 / 2 := by
    have h2 : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log two_pos, one_div]
    have hstep : Real.exp (-L) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.2 (by linarith)
    rwa [h2] at hstep
  have hr1 : Real.exp (-L) < 1 := by linarith
  have hsummable := deningerLatticeMajorant_summable
    (Q := deningerMeyerSeminormFun 1 0 h) hr0 hr1
  have hnormsum : Summable fun j : ℤ =>
      ‖((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (t + (j : ℝ) * L)‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => deningerFundamentalMajorant hLpos ht0 htL j) hsummable
  have hstep : ‖deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L t‖
      ≤ ∑' j : ℤ, deningerLatticeMajorant (deningerMeyerSeminormFun 1 0 h) (Real.exp (-L)) j := by
    refine le_trans (norm_tsum_le_tsum_norm hnormsum) ?_
    exact hnormsum.tsum_le_tsum (fun j => deningerFundamentalMajorant hLpos ht0 htL j) hsummable
  refine hstep.trans ?_
  rw [deningerLatticeMajorant_tsum hr0 hr1]
  have hinv : (1 - Real.exp (-L))⁻¹ ≤ 2 := by
    have h1 : (1 : ℝ) / 2 ≤ 1 - Real.exp (-L) := by linarith
    have h2 : (0 : ℝ) < 1 - Real.exp (-L) := by linarith
    rw [inv_le_comm₀ h2 (by norm_num)]
    linarith
  nlinarith

end

end RHTower
