import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheInversionDefectIsPositive

/-!
# The pronic dilation contraction and its threshold

Dilating a row by an integer factor contracts the pronic norm: each level `m` of the dilated row is
repeated at most `j` times, at horizons at least `jm`, and the pronic weight falls like the square
of the horizon, so

`‖v(⌊·/j⌋)‖_T ≤ √(2/j) ‖v‖_T`  (`pronicNorm_rowDilate_le`).

That is the exact quantitative form of the wall the corpus records.  The off-diagonal part of the
damped unit dilation is the sum of the dilations with weights `j^{-ε}`, so a term-by-term bound on
its contribution to the self-improving identity costs

`√2 Σ_{j ≥ 2} j^{-(ε + 1/2)} · E_T(ε)`  (`abs_pronicPairing_offDiagonalUnitDilation_le`),

and that series converges **exactly** for `ε > 1/2` (`summable_dilationSeries_iff`).  Above half
damping the route closes and reduces admission to the linear pairing alone
(`admits_of_linear_pairing_of_dilationSeries_lt_one`); below it the majorant diverges, which is why
the anti-correlation must be controlled as a *signed* quantity.
-/

open Finset RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The dilation contraction -/

/-- The dilation of a row by an integer factor. -/
def rowDilate (j : ℕ) (v : ℕ → ℝ) : ℕ → ℝ := fun n => v (n / j)

/-- **The pronic dilation contraction.**  A dilation by `j` contracts the pronic norm by `√(2/j)`. -/
theorem pronicNorm_rowDilate_le {j : ℕ} (hj : 1 ≤ j) (T : ℕ) (v : ℕ → ℝ) (hv0 : v 0 = 0) :
    pronicNorm T (rowDilate j v) ≤ Real.sqrt (2 / (j : ℝ)) * pronicNorm T v := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hsq : pronicNorm T (rowDilate j v) ^ 2 ≤ (2 / (j : ℝ)) * pronicNorm T v ^ 2 := by
    rw [pronicNorm_sq, pronicNorm_sq]
    have hmaps : ∀ n ∈ Icc 1 T, n / j ∈ range (T + 1) := by
      intro n hn
      rw [mem_Icc] at hn
      rw [mem_range]
      have := Nat.div_le_self n j
      omega
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun n => rowDilate j v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)))]
    have hfiber : ∀ m ∈ range (T + 1),
        (∑ n ∈ (Icc 1 T).filter (fun n => n / j = m),
            rowDilate j v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
          (2 / (j : ℝ)) * (if m = 0 then 0 else v m ^ 2 / ((m : ℝ) * ((m : ℝ) + 1))) := by
      intro m hm
      rcases Nat.eq_zero_or_pos m with rfl | hm1
      · have hzero : ∀ n ∈ (Icc 1 T).filter (fun n => n / j = 0),
            rowDilate j v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) = 0 := by
          intro n hn
          rw [Finset.mem_filter] at hn
          rw [rowDilate, hn.2, hv0]
          simp
        rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
        simp
      · have hmne : m ≠ 0 := by omega
        rw [if_neg hmne]
        have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
        have hjm : (0 : ℝ) < (j : ℝ) * (m : ℝ) := by positivity
        -- every horizon in the fibre is at least `j m`, so each term is small
        have hterm : ∀ n ∈ (Icc 1 T).filter (fun n => n / j = m),
            rowDilate j v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
              v m ^ 2 / (((j : ℝ) * (m : ℝ)) * (((j : ℝ) * (m : ℝ)) + 1)) := by
          intro n hn
          rw [Finset.mem_filter, mem_Icc] at hn
          have hge : j * m ≤ n := by
            rw [← hn.2]
            exact Nat.mul_div_le n j
          have hgeR : ((j : ℝ) * (m : ℝ)) ≤ (n : ℝ) := by
            have : ((j * m : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hge
            push_cast at this
            exact this
          rw [rowDilate, hn.2]
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          nlinarith
        -- the fibre has at most `j` horizons
        have hcard : ((Icc 1 T).filter (fun n => n / j = m)).card ≤ j := by
          have hsub : (Icc 1 T).filter (fun n => n / j = m) ⊆ Icc (j * m) (j * m + j - 1) := by
            intro n hn
            rw [Finset.mem_filter, mem_Icc] at hn
            rw [mem_Icc]
            have hge : j * m ≤ n := by
              rw [← hn.2]
              exact Nat.mul_div_le n j
            have hlt : n < (m + 1) * j := by
              rw [← Nat.div_lt_iff_lt_mul (by omega : 0 < j)]
              omega
            have heq : (m + 1) * j = j * m + j := by ring
            exact ⟨hge, by omega⟩
          have := Finset.card_le_card hsub
          rw [Nat.card_Icc] at this
          omega
        have hbound := Finset.sum_le_card_nsmul _ _ _ hterm
        rw [nsmul_eq_mul] at hbound
        have hcardR : (((Icc 1 T).filter (fun n => n / j = m)).card : ℝ) ≤ (j : ℝ) := by
          exact_mod_cast hcard
        have hpos : 0 ≤ v m ^ 2 / (((j : ℝ) * (m : ℝ)) * (((j : ℝ) * (m : ℝ)) + 1)) := by
          positivity
        have hstep : (((Icc 1 T).filter (fun n => n / j = m)).card : ℝ) *
            (v m ^ 2 / (((j : ℝ) * (m : ℝ)) * (((j : ℝ) * (m : ℝ)) + 1))) ≤
            (j : ℝ) * (v m ^ 2 / (((j : ℝ) * (m : ℝ)) * (((j : ℝ) * (m : ℝ)) + 1))) :=
          mul_le_mul_of_nonneg_right hcardR hpos
        have h1m : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
        have hjm1 : (j : ℝ) * ((m : ℝ) + 1) ≤ 2 * ((j : ℝ) * (m : ℝ) + 1) := by
          nlinarith [mul_le_mul_of_nonneg_left h1m hj0.le]
        have hkey : (j : ℝ) ^ 2 *
            (v m ^ 2 / (((j : ℝ) * (m : ℝ)) * (((j : ℝ) * (m : ℝ)) + 1))) ≤
            2 * (v m ^ 2 / ((m : ℝ) * ((m : ℝ) + 1))) := by
          have hL : (j : ℝ) ^ 2 *
              (v m ^ 2 / (((j : ℝ) * (m : ℝ)) * (((j : ℝ) * (m : ℝ)) + 1))) =
              ((j : ℝ) ^ 2 * v m ^ 2) / (((j : ℝ) * (m : ℝ)) * (((j : ℝ) * (m : ℝ)) + 1)) := by
            ring
          have hR : 2 * (v m ^ 2 / ((m : ℝ) * ((m : ℝ) + 1))) =
              (2 * v m ^ 2) / ((m : ℝ) * ((m : ℝ) + 1)) := by ring
          rw [hL, hR, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_right hjm1
            (mul_nonneg (mul_nonneg (sq_nonneg (v m)) hj0.le) hm0.le)]
        have hfinal : (j : ℝ) * (v m ^ 2 / (((j : ℝ) * (m : ℝ)) * (((j : ℝ) * (m : ℝ)) + 1))) ≤
            (2 / (j : ℝ)) * (v m ^ 2 / ((m : ℝ) * ((m : ℝ) + 1))) := by
          have hinv : (0 : ℝ) ≤ 1 / (j : ℝ) := by positivity
          have hmul := mul_le_mul_of_nonneg_left hkey hinv
          have hjne : (j : ℝ) ≠ 0 := hj0.ne'
          calc (j : ℝ) * (v m ^ 2 / (((j : ℝ) * (m : ℝ)) * (((j : ℝ) * (m : ℝ)) + 1)))
              = (1 / (j : ℝ)) * ((j : ℝ) ^ 2 *
                (v m ^ 2 / (((j : ℝ) * (m : ℝ)) * (((j : ℝ) * (m : ℝ)) + 1)))) := by
                field_simp
            _ ≤ (1 / (j : ℝ)) * (2 * (v m ^ 2 / ((m : ℝ) * ((m : ℝ) + 1)))) := hmul
            _ = (2 / (j : ℝ)) * (v m ^ 2 / ((m : ℝ) * ((m : ℝ) + 1))) := by ring
        linarith
    refine le_trans (Finset.sum_le_sum hfiber) ?_
    rw [← Finset.mul_sum]
    have hsplit : (∑ m ∈ range (T + 1),
        (if m = 0 then 0 else v m ^ 2 / ((m : ℝ) * ((m : ℝ) + 1)))) =
        ∑ m ∈ Icc 1 T, v m ^ 2 / ((m : ℝ) * ((m : ℝ) + 1)) := by
      have hins : (range (T + 1) : Finset ℕ) = insert 0 (Icc 1 T) := by
        ext m
        rw [mem_range, Finset.mem_insert, mem_Icc]
        omega
      rw [hins, Finset.sum_insert (by simp), if_pos rfl, zero_add]
      exact Finset.sum_congr rfl fun m hm => by
        rw [mem_Icc] at hm
        rw [if_neg (by omega : m ≠ 0)]
    rw [hsplit]
  have hA := pronicNorm_nonneg T (rowDilate j v)
  have hB := pronicNorm_nonneg T v
  have hC : 0 ≤ Real.sqrt (2 / (j : ℝ)) := Real.sqrt_nonneg _
  have hCsq : Real.sqrt (2 / (j : ℝ)) ^ 2 = 2 / (j : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hCB : 0 ≤ Real.sqrt (2 / (j : ℝ)) * pronicNorm T v := mul_nonneg hC hB
  have hAB : pronicNorm T (rowDilate j v) ^ 2 ≤
      (Real.sqrt (2 / (j : ℝ)) * pronicNorm T v) ^ 2 := by
    rw [mul_pow, hCsq]
    exact hsq
  exact (pow_le_pow_iff_left₀ hA hCB two_ne_zero).mp hAB


/-! ## §2. The off-diagonal dilation form, bounded term by term -/

theorem pronicNorm_congr {T : ℕ} {u v : ℕ → ℝ} (h : ∀ n ∈ Icc 1 T, u n = v n) :
    pronicNorm T u = pronicNorm T v := by
  unfold pronicNorm
  exact congrArg Real.sqrt (Finset.sum_congr rfl fun n hn => by rw [h n hn])

theorem pronicNorm_const_mul {T : ℕ} {c : ℝ} (hc : 0 ≤ c) (v : ℕ → ℝ) :
    pronicNorm T (fun n => c * v n) = c * pronicNorm T v := by
  have hsq : pronicNorm T (fun n => c * v n) ^ 2 = (c * pronicNorm T v) ^ 2 := by
    rw [pronicNorm_const_mul_sq, mul_pow]
  have h1 := pronicNorm_nonneg T (fun n => c * v n)
  have h2 : 0 ≤ c * pronicNorm T v := mul_nonneg hc (pronicNorm_nonneg T v)
  calc pronicNorm T (fun n => c * v n)
      = Real.sqrt (pronicNorm T (fun n => c * v n) ^ 2) := (Real.sqrt_sq h1).symm
    _ = Real.sqrt ((c * pronicNorm T v) ^ 2) := by rw [hsq]
    _ = c * pronicNorm T v := Real.sqrt_sq h2

theorem pronicNorm_sum_le (T : ℕ) (s : Finset ℕ) (w : ℕ → ℕ → ℝ) :
    pronicNorm T (fun n => ∑ j ∈ s, w j n) ≤ ∑ j ∈ s, pronicNorm T (w j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pronicNorm]
  | @insert j s hj ih =>
    have hfun : (fun n => ∑ i ∈ insert j s, w i n) =
        fun n => w j n + ∑ i ∈ s, w i n :=
      funext fun n => by rw [Finset.sum_insert hj]
    rw [hfun, Finset.sum_insert hj]
    exact (pronicNorm_add_le T (w j) (fun n => ∑ i ∈ s, w i n)).trans (by linarith)

theorem pmPowerDampedCenteredDivisorPrefix_zero (ε : ℝ) :
    pmPowerDampedCenteredDivisorPrefix ε 0 = 0 := by
  rw [pmPowerDampedCenteredDivisorPrefix_eq]
  simp

/-- **The off-diagonal dilation is bounded term by term** by the dilation series times the energy's
square root. -/
theorem pronicNorm_offDiagonalUnitDilation_le (ε : ℝ) (T : ℕ) :
    pronicNorm T (offDiagonalUnitDilation ε) ≤
      (∑ j ∈ Icc 2 T, (j : ℝ) ^ (-ε) * Real.sqrt (2 / (j : ℝ))) *
        Real.sqrt (dampedMobiusEnergy ε T) := by
  have hext : ∀ n ∈ Icc 1 T, offDiagonalUnitDilation ε n =
      ∑ j ∈ Icc 2 T, (j : ℝ) ^ (-ε) *
        rowDilate j (pmPowerDampedCenteredDivisorPrefix ε) n := by
    intro n hn
    rw [mem_Icc] at hn
    rw [offDiagonalUnitDilation]
    have hsub : (Icc 2 n : Finset ℕ) ⊆ Icc 2 T := by
      intro j hj
      rw [mem_Icc] at hj ⊢
      exact ⟨hj.1, hj.2.trans hn.2⟩
    rw [← Finset.sum_subset hsub]
    · exact Finset.sum_congr rfl fun j _ => by rw [rowDilate]
    · intro j hjT hjn
      rw [mem_Icc] at hjT hjn
      have hzero : n / j = 0 := Nat.div_eq_of_lt (by omega)
      rw [rowDilate, hzero, pmPowerDampedCenteredDivisorPrefix_zero]
      ring
  rw [pronicNorm_congr hext]
  refine (pronicNorm_sum_le T (Icc 2 T)
    (fun j n => (j : ℝ) ^ (-ε) *
      rowDilate j (pmPowerDampedCenteredDivisorPrefix ε) n)).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj1 : 1 ≤ j := by
    rw [mem_Icc] at hj
    omega
  have hrpow : (0 : ℝ) ≤ (j : ℝ) ^ (-ε) := Real.rpow_nonneg (Nat.cast_nonneg j) _
  rw [pronicNorm_const_mul hrpow, ← pronicNorm_centeredPrefix ε T, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (pronicNorm_rowDilate_le hj1 T _ (pmPowerDampedCenteredDivisorPrefix_zero ε)) hrpow

/-- The pairing with the off-diagonal dilation, bounded term by term. -/
theorem abs_pronicPairing_offDiagonalUnitDilation_le (ε : ℝ) (T : ℕ) :
    |pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (offDiagonalUnitDilation ε)| ≤
      (∑ j ∈ Icc 2 T, (j : ℝ) ^ (-ε) * Real.sqrt (2 / (j : ℝ))) * dampedMobiusEnergy ε T := by
  have hS : 0 ≤ ∑ j ∈ Icc 2 T, (j : ℝ) ^ (-ε) * Real.sqrt (2 / (j : ℝ)) :=
    Finset.sum_nonneg fun j _ => by positivity
  have hE := dampedMobiusEnergy_nonneg ε T
  have hsqrtE : Real.sqrt (dampedMobiusEnergy ε T) ^ 2 = dampedMobiusEnergy ε T :=
    Real.sq_sqrt hE
  have hnorm := pronicNorm_offDiagonalUnitDilation_le ε T
  have hcs : ∀ u : ℕ → ℝ, pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) u ≤
      Real.sqrt (dampedMobiusEnergy ε T) * pronicNorm T u := by
    intro u
    have h := sum_mul_div_le_pronicNorm T (pmPowerDampedCenteredDivisorPrefix ε) u
    rw [pronicNorm_centeredPrefix] at h
    exact h
  have hpos := hcs (offDiagonalUnitDilation ε)
  have hneg := hcs (fun n => -offDiagonalUnitDilation ε n)
  rw [pronicNorm_neg] at hneg
  have hnegeq : pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε)
      (fun n => -offDiagonalUnitDilation ε n) =
      -pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (offDiagonalUnitDilation ε) := by
    unfold pronicPairing
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hnegeq] at hneg
  have hsqrt0 : 0 ≤ Real.sqrt (dampedMobiusEnergy ε T) := Real.sqrt_nonneg _
  have hbound : Real.sqrt (dampedMobiusEnergy ε T) * pronicNorm T (offDiagonalUnitDilation ε) ≤
      (∑ j ∈ Icc 2 T, (j : ℝ) ^ (-ε) * Real.sqrt (2 / (j : ℝ))) * dampedMobiusEnergy ε T := by
    have := mul_le_mul_of_nonneg_left hnorm hsqrt0
    nlinarith [hsqrtE, hS, hsqrt0]
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-! ## §3. The threshold of the term-by-term route -/

theorem dilationSeries_term_eq {ε : ℝ} {j : ℕ} (hj : 1 ≤ j) :
    (j : ℝ) ^ (-ε) * Real.sqrt (2 / (j : ℝ)) =
      Real.sqrt 2 * (j : ℝ) ^ (-(ε + 1 / 2)) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hsplit : Real.sqrt (2 / (j : ℝ)) = Real.sqrt 2 * (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      Real.rpow_neg (le_of_lt hj0), div_eq_mul_inv]
  rw [hsplit, show -(ε + 1 / 2) = -ε + -(1 / 2 : ℝ) by ring, Real.rpow_add hj0]
  ring

/-- **Above half damping the term-by-term series converges.** -/
theorem summable_dilationSeries_of_half_lt {ε : ℝ} (hε : 1 / 2 < ε) :
    Summable (fun j : ℕ => (j : ℝ) ^ (-ε) * Real.sqrt (2 / (j : ℝ))) := by
  have hbase : Summable (fun j : ℕ => Real.sqrt 2 * (j : ℝ) ^ (-(ε + 1 / 2))) :=
    (Real.summable_nat_rpow.mpr (by linarith : -(ε + 1 / 2) < -1)).mul_left _
  refine (summable_nat_add_iff 1).mp ?_
  refine ((summable_nat_add_iff 1).mpr hbase).congr fun j => ?_
  exact (dilationSeries_term_eq (by omega : 1 ≤ j + 1)).symm

/-- **At or below half damping the term-by-term series diverges**: the majorant route stops exactly
at half damping, which is why the anti-correlation must be bounded as a signed quantity. -/
theorem not_summable_dilationSeries_of_le_half {ε : ℝ} (hε : ε ≤ 1 / 2) :
    ¬ Summable (fun j : ℕ => (j : ℝ) ^ (-ε) * Real.sqrt (2 / (j : ℝ))) := by
  intro hsum
  have hshift := (summable_nat_add_iff 1).mpr hsum
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hcongr : Summable (fun j : ℕ => Real.sqrt 2 * ((j + 1 : ℕ) : ℝ) ^ (-(ε + 1 / 2))) := by
    refine hshift.congr fun j => ?_
    exact dilationSeries_term_eq (by omega : 1 ≤ j + 1)
  have hplain : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ (-(ε + 1 / 2))) := by
    have h := hcongr.mul_left (Real.sqrt 2)⁻¹
    refine h.congr fun j => ?_
    rw [inv_mul_cancel_left₀ h2.ne']
  have hfinal : Summable (fun j : ℕ => (j : ℝ) ^ (-(ε + 1 / 2))) :=
    (summable_nat_add_iff 1).mp hplain
  have := Real.summable_nat_rpow.mp hfinal
  linarith


/-! ## §4. Above the threshold, admission reduces to the linear pairing -/

/-- **Above the threshold the anti-correlation is paid by a fraction of the energy.**  If the
partial dilation series stay below one, admission at that damping reduces to a sublinear bound on
the explicit linear pairing alone. -/
theorem admits_of_linear_pairing_of_dilationSeries_lt_one {ε κ κ' S : ℝ} (_hκ : 0 ≤ κ)
    (hκ' : 0 ≤ κ') (hS1 : S < 1)
    (hSval : ∀ T : ℕ, (∑ j ∈ Icc 2 T, (j : ℝ) ^ (-ε) * Real.sqrt (2 / (j : ℝ))) ≤ S)
    (h1 : ∀ T : ℕ, pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (inversionDefect ε) ≤
      κ * Real.sqrt (dampedMobiusEnergy ε T) + κ') :
    Admits dampedMobiusEnergy ε := by
  have hc : 0 < 1 - S := by linarith
  refine ⟨max 1 ((κ + κ') / (1 - S)) ^ 2, fun T => ?_⟩
  have hE := dampedMobiusEnergy_nonneg ε T
  have hx0 : 0 ≤ Real.sqrt (dampedMobiusEnergy ε T) := Real.sqrt_nonneg _
  have hxx : Real.sqrt (dampedMobiusEnergy ε T) ^ 2 = dampedMobiusEnergy ε T := Real.sq_sqrt hE
  have hoff := abs_pronicPairing_offDiagonalUnitDilation_le ε T
  have hSE : (∑ j ∈ Icc 2 T, (j : ℝ) ^ (-ε) * Real.sqrt (2 / (j : ℝ))) *
      dampedMobiusEnergy ε T ≤ S * dampedMobiusEnergy ε T :=
    mul_le_mul_of_nonneg_right (hSval T) hE
  have hid := dampedMobiusEnergy_eq_pairing_sub ε T
  have hkey : (1 - S) * dampedMobiusEnergy ε T ≤
      κ * Real.sqrt (dampedMobiusEnergy ε T) + κ' := by
    have habs := abs_le.mp hoff
    nlinarith [h1 T, habs.1, habs.2, hSE]
  -- a crude two-case bound suffices
  have hbound : Real.sqrt (dampedMobiusEnergy ε T) ≤ max 1 ((κ + κ') / (1 - S)) := by
    rcases le_or_gt (Real.sqrt (dampedMobiusEnergy ε T)) 1 with hle | hgt
    · exact le_trans hle (le_max_left _ _)
    · refine le_trans ?_ (le_max_right 1 ((κ + κ') / (1 - S)))
      rw [le_div_iff₀ hc]
      nlinarith [hxx, hkey, hgt]
  calc dampedMobiusEnergy ε T = Real.sqrt (dampedMobiusEnergy ε T) ^ 2 := hxx.symm
    _ ≤ max 1 ((κ + κ') / (1 - S)) ^ 2 := pow_le_pow_left₀ hx0 hbound 2

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
