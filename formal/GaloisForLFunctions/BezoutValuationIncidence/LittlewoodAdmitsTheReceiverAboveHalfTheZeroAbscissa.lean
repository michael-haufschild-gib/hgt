import GaloisForLFunctions.BezoutValuationIncidence.ReceiverBoundedInTheZeroFreeBandBelowHalfDamping
import GaloisForLFunctions.RHTower.MobiusMertensAbscissaLittlewood
import GaloisForLFunctions.RHTower.ReceiverDampingsAccumulateAboveTheZeros
import GaloisForLFunctions.RHTower.QuasiRHQuotientHeadAndFiniteContactAbscissaLaw

/-!
# Littlewood admits the receiver above half the zero abscissa

Let `Θ = zetaZeroAbscissa = sup Re ρ ∈ [½, 1]`. Littlewood's bound `|M(x)| ≤ C x^{Θ+δ}` on the
Mertens function is unconditional at `Θ` (`mobiusMertens_subpower_zetaZeroAbscissa`), and the rate
transfer `abs_weightCenteredPrefix_dampedSign_le_of_linear` turns a linear bound `|M(x)| ≤ Lx` beyond
`D` into a bound on the centred prefix `A_ε` of the damped Möbius weight `μ(d) d^{−ε}`:
`|A_ε(n)| ≤ 3 D^{1−ε} + 31 L n D^{−ε}`. With `β = Θ + δ`, `L = 2C D^{β−1}` and `D ≈ n^{1/(2−β)}` the
two terms balance at `|A_ε(n)| ≤ K n^{(1−ε)/(2−β)}`, whose exponent is below `½` exactly when
`β < 2ε`. Hence:

* `mem_receiverDampings_of_half_zetaZeroAbscissa_lt`: every damping `Θ/2 < ε ≤ ½` is admissible;
  `Ioi_half_zetaZeroAbscissa_subset_receiverDampings`.
* `receiverDampingRate_le_half_zetaZeroAbscissa`: `receiverDampingRate ≤ Θ/2`, so together with
  `zetaZeroAbscissa_le_half_add_receiverDampingRate` the rate is sandwiched,
  `Θ − ½ ≤ receiverDampingRate ≤ Θ/2` (`receiverDampingRate_sandwich`).
* `receiverDampingRate_lt_half_iff`: the signed family crosses below half damping iff `Θ < 1`, a
  zero-free strip.
* `receiverDampingRate_le_quarter_of_riemannHypothesis`: under RH every damping above `¼` is
  admissible.

The elementary transfer is pointwise and loses on the sawtooth head `Σ_{d≤n} μ(d) d^{−ε} {n/d}`;
the sharp statement `receiverDampingRate = Θ − ½` is a mean-square (Mellin–Plancherel) statement.
-/

open Finset Filter Topology Set
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open _root_.RHTower

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- The Mertens partial sum in real form. -/
theorem norm_mobiusMertensPartialSum_eq (N : ℕ) :
    ‖mobiusMertensPartialSum N‖ = |∑ e ∈ Icc 1 N, moebiusReal e| := by
  have h : mobiusMertensPartialSum N =
      ((∑ n ∈ range (N + 1), ((ArithmeticFunction.moebius n : ℤ) : ℝ) : ℝ) : ℂ) := by
    simp only [mobiusMertensPartialSum, mobiusComplexCoefficient, Complex.ofReal_sum,
      Complex.ofReal_intCast]
  rw [h, Complex.norm_real, Real.norm_eq_abs, sum_range_moebius_eq_sum_Icc_moebiusReal]

/-- A power bound `x^{β−1}` is antitone beyond `D` for `β ≤ 1`. -/
theorem rpow_sub_one_le_of_le {β : ℝ} (hβ1 : β ≤ 1) {D x : ℝ} (hD : 0 < D) (hDx : D ≤ x) :
    x ^ (β - 1) ≤ D ^ (β - 1) := by
  have hx : 0 < x := hD.trans_le hDx
  rw [show β - 1 = -(1 - β) by ring, Real.rpow_neg hx.le, Real.rpow_neg hD.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hD _) (Real.rpow_le_rpow hD.le hDx (by linarith))

/-- **Admission above half the zero abscissa.** For `Θ/2 < ε ≤ ½` the damped Möbius receiver has a
horizon-uniform budget. -/
theorem mem_receiverDampings_of_half_zetaZeroAbscissa_lt {ε : ℝ}
    (hε : zetaZeroAbscissa / 2 < ε) (hε2 : ε ≤ 1 / 2) : ε ∈ receiverDampings := by
  have hΘ := half_le_zetaZeroAbscissa
  have hΘ1 := zetaZeroAbscissa_le_one
  have hε4 : 1 / 4 ≤ ε := by linarith
  have hε0 : 0 < ε := by linarith
  -- the Littlewood exponent `β = Θ + δ` with `β < 2ε`
  set β : ℝ := (zetaZeroAbscissa + 2 * ε) / 2 with hβ
  have hβΘ : zetaZeroAbscissa < β := by rw [hβ]; linarith
  have hβ2ε : β < 2 * ε := by rw [hβ]; linarith
  have hβ1 : β ≤ 1 := by rw [hβ]; linarith
  have hεβ : ε ≤ β := by rw [hβ]; linarith
  obtain ⟨C, hC0, hC⟩ :=
    mobiusMertens_subpower_zetaZeroAbscissa (β - zetaZeroAbscissa) (by linarith)
  have hC' : ∀ N : ℕ, |∑ e ∈ Icc 1 N, moebiusReal e| ≤ C * ((N : ℝ) + 1) ^ β := by
    intro N
    have := hC N
    rwa [norm_mobiusMertensPartialSum_eq, add_sub_cancel] at this
  -- the balancing exponents
  have h2β : 0 < 2 - β := by linarith
  set a : ℝ := 1 / (2 - β) with ha
  set γ : ℝ := a * (1 - ε) with hγ
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : a ≤ 1 := by rw [ha, div_le_one h2β]; linarith
  have hγhalf : γ < 1 / 2 := by
    rw [hγ, ha, div_mul_eq_mul_div, one_mul, div_lt_iff₀ h2β]; linarith
  have hγ0 : 0 ≤ γ := by rw [hγ]; exact mul_nonneg ha0.le (by linarith)
  have hγeq : 1 + a * (β - 1 - ε) = γ := by
    rw [hγ, ha]; field_simp; ring
  -- the pointwise prefix bound
  have hpre : ∀ n : ℕ, 1 ≤ n →
      |weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n| ≤
        (3 + 124 * C) * (n : ℝ) ^ γ := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    set y : ℝ := (n : ℝ) ^ a with hy
    have hy1 : 1 ≤ y := by
      rw [hy, ← Real.one_rpow a]
      exact Real.rpow_le_rpow zero_le_one hn1 ha0.le
    have hy0 : 0 < y := by linarith
    set D : ℕ := ⌊y⌋₊ with hD
    have hD1 : 1 ≤ D := Nat.floor_pos.mpr hy1
    have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
    have hDy : (D : ℝ) ≤ y := Nat.floor_le hy0.le
    have hyD : y / 2 ≤ D := by
      have h1 := Nat.lt_floor_add_one y
      have h2 : (1 : ℝ) ≤ D := by exact_mod_cast hD1
      rw [← hD] at h1
      linarith
    have hyn : y ≤ n := by
      rw [hy]
      calc (n : ℝ) ^ a ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 ha1
        _ = n := Real.rpow_one _
    have hDn : D ≤ n := by exact_mod_cast hDy.trans hyn
    -- Littlewood beyond `D` is a linear bound with slope `L = 2C D^{β−1}`
    set L : ℝ := 2 * C * (D : ℝ) ^ (β - 1) with hL
    have hL0 : 0 ≤ L := by positivity
    have hS : ∀ x : ℕ, D ≤ x → |∑ e ∈ Icc 1 x, moebiusReal e| ≤ L * x := by
      intro x hx
      have hx0 : (0 : ℝ) < x := by exact_mod_cast (hD1.trans hx)
      have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (hD1.trans hx)
      have hDx : (D : ℝ) ≤ x := by exact_mod_cast hx
      have hβ0 : 0 ≤ β := by linarith
      have hxβ : (x : ℝ) ^ β = (x : ℝ) ^ (β - 1) * x := by
        rw [Real.rpow_sub_one hx0.ne']; field_simp
      have h2β' : (2 : ℝ) ^ β ≤ 2 := by
        calc (2 : ℝ) ^ β ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ1
          _ = 2 := Real.rpow_one 2
      calc |∑ e ∈ Icc 1 x, moebiusReal e| ≤ C * ((x : ℝ) + 1) ^ β := hC' x
        _ ≤ C * (2 * (x : ℝ)) ^ β :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by positivity) (by linarith) hβ0) hC0
        _ = C * (2 ^ β * (x : ℝ) ^ β) := by rw [Real.mul_rpow (by norm_num) hx0.le]
        _ ≤ C * (2 * (x : ℝ) ^ β) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h2β' (Real.rpow_nonneg hx0.le _)) hC0
        _ = 2 * C * ((x : ℝ) ^ (β - 1) * x) := by rw [hxβ]; ring
        _ ≤ 2 * C * ((D : ℝ) ^ (β - 1) * x) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (rpow_sub_one_le_of_le hβ1 hD0 hDx) hx0.le)
            (by positivity)
        _ = L * x := by rw [hL]; ring
    have hA := abs_weightCenteredPrefix_dampedSign_le_of_linear (s := moebiusReal) hL0 hε4 hε2
      abs_moebiusReal_le_one' hD1 hDn hS
    rw [pmPowerDampedRealWeight_eq_dampedSignWeight, dampedDensity_eq_tsum hε0]
    refine hA.trans ?_
    -- first term: `D^{1−ε} ≤ y^{1−ε} = n^γ`
    have hT1 : (D : ℝ) ^ (1 - ε) ≤ (n : ℝ) ^ γ := by
      calc (D : ℝ) ^ (1 - ε) ≤ y ^ (1 - ε) := Real.rpow_le_rpow hD0.le hDy (by linarith)
        _ = (n : ℝ) ^ γ := by rw [hy, ← Real.rpow_mul hn0.le]
    -- second term: `D^{β−1−ε} ≤ 2 y^{β−1−ε}`, hence `L n D^{−ε} ≤ 4 C n^γ`
    have hpow : (D : ℝ) ^ (β - 1 - ε) ≤ 2 * y ^ (β - 1 - ε) := by
      have hexp0 : 0 ≤ 1 + ε - β := by linarith
      have hexp1 : 1 + ε - β ≤ 1 := by linarith
      have h2e : (2 : ℝ) ^ (1 + ε - β) ≤ 2 := by
        calc (2 : ℝ) ^ (1 + ε - β) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp1
          _ = 2 := Real.rpow_one 2
      have hylow : y ^ (1 + ε - β) / 2 ≤ (D : ℝ) ^ (1 + ε - β) := by
        calc y ^ (1 + ε - β) / 2 ≤ y ^ (1 + ε - β) / 2 ^ (1 + ε - β) :=
              div_le_div_of_nonneg_left (Real.rpow_nonneg hy0.le _) (by positivity) h2e
          _ = (y / 2) ^ (1 + ε - β) := (Real.div_rpow hy0.le (by norm_num) _).symm
          _ ≤ (D : ℝ) ^ (1 + ε - β) := Real.rpow_le_rpow (by positivity) hyD hexp0
      rw [show β - 1 - ε = -(1 + ε - β) by ring, Real.rpow_neg hD0.le, Real.rpow_neg hy0.le]
      calc ((D : ℝ) ^ (1 + ε - β))⁻¹ ≤ (y ^ (1 + ε - β) / 2)⁻¹ :=
            inv_anti₀ (by positivity) hylow
        _ = 2 * (y ^ (1 + ε - β))⁻¹ := by rw [inv_div]; ring
    have hT2 : 31 * L * (n : ℝ) * (D : ℝ) ^ (-ε) ≤ 124 * C * (n : ℝ) ^ γ := by
      have hcomb : (D : ℝ) ^ (β - 1) * (D : ℝ) ^ (-ε) = (D : ℝ) ^ (β - 1 - ε) := by
        rw [← Real.rpow_add hD0]; ring_nf
      have hyγ : (n : ℝ) * y ^ (β - 1 - ε) = (n : ℝ) ^ γ := by
        rw [hy, ← Real.rpow_mul hn0.le, ← hγeq, Real.rpow_add hn0, Real.rpow_one]
      calc 31 * L * (n : ℝ) * (D : ℝ) ^ (-ε)
          = 62 * C * (n : ℝ) * ((D : ℝ) ^ (β - 1) * (D : ℝ) ^ (-ε)) := by rw [hL]; ring
        _ = 62 * C * (n : ℝ) * (D : ℝ) ^ (β - 1 - ε) := by rw [hcomb]
        _ ≤ 62 * C * (n : ℝ) * (2 * y ^ (β - 1 - ε)) := by gcongr
        _ = 124 * C * ((n : ℝ) * y ^ (β - 1 - ε)) := by ring
        _ = 124 * C * (n : ℝ) ^ γ := by rw [hyγ]
    calc 3 * (D : ℝ) ^ (1 - ε) + 31 * L * (n : ℝ) * (D : ℝ) ^ (-ε)
        ≤ 3 * (n : ℝ) ^ γ + 124 * C * (n : ℝ) ^ γ :=
          add_le_add (mul_le_mul_of_nonneg_left hT1 (by norm_num)) hT2
      _ = (3 + 124 * C) * (n : ℝ) ^ γ := by ring
  -- the receiver energy is dominated by a convergent power series
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (2 * γ - 2)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  refine ⟨hε0, (3 + 124 * C) ^ 2 * ∑' n : ℕ, (n : ℝ) ^ (2 * γ - 2), fun T => ?_⟩
  rw [← weightPronicEnergy_pmPowerDamped, weightPronicEnergy]
  calc ∑ n ∈ Icc 1 T, weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1))
      ≤ ∑ n ∈ Icc 1 T, (3 + 124 * C) ^ 2 * (n : ℝ) ^ (2 * γ - 2) := by
        refine sum_le_sum fun n hn => ?_
        have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
        have hsq : weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n ^ 2 ≤
            ((3 + 124 * C) * (n : ℝ) ^ γ) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hpre n hn1) 2
        have hpow : ((n : ℝ) ^ γ) ^ 2 / ((n : ℝ) * (n : ℝ)) = (n : ℝ) ^ (2 * γ - 2) := by
          have h1 : ((n : ℝ) ^ γ) ^ 2 = (n : ℝ) ^ (2 * γ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
            congr 1
            push_cast
            ring
          have h2 : (n : ℝ) * (n : ℝ) = (n : ℝ) ^ (2 : ℝ) := by rw [Real.rpow_two]; ring
          rw [h1, h2, Real.rpow_sub hn0 (2 * γ) 2]
        calc weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n ^ 2 /
              ((n : ℝ) * ((n : ℝ) + 1))
            ≤ ((3 + 124 * C) * (n : ℝ) ^ γ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
              div_le_div_of_nonneg_right hsq (by positivity)
          _ ≤ ((3 + 124 * C) * (n : ℝ) ^ γ) ^ 2 / ((n : ℝ) * (n : ℝ)) :=
              div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
          _ = (3 + 124 * C) ^ 2 * (((n : ℝ) ^ γ) ^ 2 / ((n : ℝ) * (n : ℝ))) := by
              rw [mul_pow]; ring
          _ = (3 + 124 * C) ^ 2 * (n : ℝ) ^ (2 * γ - 2) := by rw [hpow]
    _ = (3 + 124 * C) ^ 2 * ∑ n ∈ Icc 1 T, (n : ℝ) ^ (2 * γ - 2) := by rw [mul_sum]
    _ ≤ (3 + 124 * C) ^ 2 * ∑' n : ℕ, (n : ℝ) ^ (2 * γ - 2) :=
        mul_le_mul_of_nonneg_left
          (hsum.sum_le_tsum _ fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) (by positivity)

/-- Every damping above half the zero abscissa is admissible. -/
theorem Ioi_half_zetaZeroAbscissa_subset_receiverDampings :
    Ioi (zetaZeroAbscissa / 2) ⊆ receiverDampings := fun ε hε => by
  rcases le_or_gt ε (1 / 2) with h | h
  · exact mem_receiverDampings_of_half_zetaZeroAbscissa_lt hε h
  · exact Ici_half_subset_receiverDampings (mem_Ici.mpr h.le)

/-- **The elementary arrow.** The receiver damping rate is at most half the zero abscissa. -/
theorem receiverDampingRate_le_half_zetaZeroAbscissa :
    receiverDampingRate ≤ zetaZeroAbscissa / 2 :=
  csInf_le bddBelow_derivedSet_receiverDampings (mem_derivedSet.mpr
    (accPt_of_Ioo_subset (lt_add_one _) fun _ hx =>
      Ioi_half_zetaZeroAbscissa_subset_receiverDampings hx.1))

/-- The sandwich `Θ − ½ ≤ receiverDampingRate ≤ Θ/2`. -/
theorem receiverDampingRate_sandwich :
    zetaZeroAbscissa - 1 / 2 ≤ receiverDampingRate ∧ receiverDampingRate ≤ zetaZeroAbscissa / 2 :=
  ⟨by linarith [zetaZeroAbscissa_le_half_add_receiverDampingRate],
    receiverDampingRate_le_half_zetaZeroAbscissa⟩

/-- **Crossing below half damping is a zero-free strip.** -/
theorem receiverDampingRate_lt_half_iff : receiverDampingRate < 1 / 2 ↔ zetaZeroAbscissa < 1 := by
  constructor
  · intro h
    linarith [zetaZeroAbscissa_le_half_add_receiverDampingRate]
  · intro h
    linarith [receiverDampingRate_le_half_zetaZeroAbscissa]

/-- Under RH every damping above `¼` is admissible and the rate is at most `¼`. -/
theorem receiverDampingRate_le_quarter_of_riemannHypothesis (h : RiemannHypothesis) :
    Ioi (1 / 4 : ℝ) ⊆ receiverDampings ∧ receiverDampingRate ≤ 1 / 4 := by
  have hΘ : zetaZeroAbscissa = 1 / 2 := zetaZeroAbscissa_eq_half_iff_riemannHypothesis.mpr h
  have h4 : zetaZeroAbscissa / 2 = 1 / 4 := by rw [hΘ]; norm_num
  refine ⟨?_, ?_⟩
  · rw [← h4]; exact Ioi_half_zetaZeroAbscissa_subset_receiverDampings
  · rw [← h4]; exact receiverDampingRate_le_half_zetaZeroAbscissa

end

end GaloisForLFunctions.BezoutValuationIncidence
