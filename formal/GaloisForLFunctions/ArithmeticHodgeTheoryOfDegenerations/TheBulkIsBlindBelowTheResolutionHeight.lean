import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheBulkAtThePoleReadsTheArchimedeanGenus

/-!
# The bulk is blind below the resolution height

The zeros of height `≤ N^{2/3}` are invisible to pole-free conductor packets and give the
archimedean genus at the pole (`TheBulkIsBlindToTheLowZeros`, `TheBulkAtThePoleReadsTheArchimedeanGenus`).
Euler–Maclaurin at an arbitrary order `m` removes the growth in `|ρ|` from the explicit remainders,
so the same holds up to every height `N^θ`, `θ < 1`:

* **Euler–Maclaurin at order `m`** (`norm_zetaStripError_le_order`):
  `‖E(w, M)‖ ≤ K_m (1 + (‖w‖ + 2m + 2)^{2m+2}/M^{2m+1}) M^{−Re w}` for `‖w‖ + 2m + 2 ≤ M`; the
  bracket is bounded as soon as `‖w‖ ≤ M^{1−1/(2m+2)}`.
* **The conductor polynomial at a zero, uniformly** (`norm_conductorDirichlet_sub_horizonTerm_le_order`):
  `‖D_e(s;N) − [e = 1]N^s/s‖ ≤ 4e³(2 + 2K_m) N^{Re s − 1}`, with a constant independent of `s`, for
  `(‖s‖ + 2m + 3)^{2m+2} ≤ (N/2e)^{2m+1}`.
* **One zero** (`norm_log_div_mul_bulkLedger_sub_le_order`): the ledger entry is
  `m_ρ κ y_1²/(ρ(1−ρ))` up to `m_ρ (C₁ c/N + C₂ (|y_1| P + P²/N)/N)`, uniformly in `ρ`.
* **Every height below the resolution** (`tendsto_sum_bulkLedger_belowResolution`): for
  `0 < θ < 1` and `c_N log² N/N^{1−θ} → 0`, the zeros of height `≤ N^θ` together contribute
  `(c_N/log N) κ y_1² (2 + γ − log 4π) + o(c_N/log N)`; pole-free packets receive `o(c_N/log N)`
  (`tendsto_sum_bulkLedger_belowResolution_poleFree`).

The complete form of a fixed packet is the sum of its zero ledger; below the resolution height
`N/c` the zeros contribute only the archimedean genus at the pole. Every other part of the bulk,
its first-order count and its second-order term, is carried by the zeros of height `≳ N^{1−ε}`,
the zeros that the atoms of width `c/N` resolve.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open BezoutValuationIncidence SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  ArithmeticCastelnuovoSeveri

/-! ### Euler–Maclaurin at order `m` -/

/-- The Euler–Maclaurin coefficient `|B_{2r+2}|/(2r+2)!`. -/
noncomputable def emCoeff (r : ℕ) : ℝ := |((bernoulli (2 * r + 2) : ℚ) : ℝ)| / ((2 * r + 2).factorial : ℝ)

/-- The order-`m` Euler–Maclaurin constant `½ + Σ_{r≤m} |B_{2r+2}|/(2r+2)! + |B_{2m+2}|/(2m+2)!`. -/
noncomputable def emConst (m : ℕ) : ℝ := 1 / 2 + ∑ r ∈ range (m + 1), emCoeff r + emCoeff m

theorem emCoeff_nonneg (r : ℕ) : 0 ≤ emCoeff r := by unfold emCoeff; positivity

theorem norm_complexRisingFactor_le (w : ℂ) (j : ℕ) :
    ‖RHTower.complexRisingFactor w j‖ ≤ (‖w‖ + j) ^ j := by
  unfold RHTower.complexRisingFactor
  refine (Finset.norm_prod_le _ _).trans ?_
  calc ∏ i ∈ range j, ‖w + (i : ℂ)‖ ≤ ∏ _i ∈ range j, (‖w‖ + j) := by
        refine prod_le_prod (fun i _ => norm_nonneg _) fun i hi => ?_
        refine (norm_add_le _ _).trans ?_
        have : (i : ℝ) ≤ j := by exact_mod_cast (mem_range.mp hi).le
        simpa using this
    _ = (‖w‖ + j) ^ j := by rw [prod_const, card_range]

/-- **Euler–Maclaurin on the strip at order `m`**: for `0 < Re w`, `w ≠ 1`, `‖w‖ + 2m + 2 ≤ M`,
`‖E(w, M)‖ ≤ K_m (1 + (‖w‖ + 2m + 2)^{2m+2}/M^{2m+1}) M^{−Re w}`. -/
theorem norm_zetaStripError_le_order {w : ℂ} (hw0 : 0 < w.re) (hw1 : w ≠ 1) {M : ℕ} (hM : 1 ≤ M)
    (m : ℕ) (hwM : ‖w‖ + (2 * m + 2) ≤ M) :
    ‖RHTower.zetaStripError w M‖ ≤
      emConst m * (1 + (‖w‖ + (2 * m + 2)) ^ (2 * m + 2) / (M : ℝ) ^ (2 * m + 1)) *
        (M : ℝ) ^ (-w.re) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hEM := RHTower.norm_riemannZeta_sub_zetaEulerMaclaurinMain_le hw0 hw1 hM m
  set X := (M : ℝ) ^ (-w.re) with hX
  have hX0 : 0 < X := Real.rpow_pos_of_pos hM0 _
  have hn : 0 ≤ ‖w‖ := norm_nonneg w
  -- the remainder
  have hpowR : (M : ℝ) ^ (1 - w.re - ((2 * m + 2 : ℕ) : ℝ)) = X / (M : ℝ) ^ (2 * m + 1) := by
    rw [show 1 - w.re - ((2 * m + 2 : ℕ) : ℝ) = -w.re - ((2 * m + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_sub hM0, Real.rpow_natCast]
  have hden : 1 ≤ w.re + ((2 * m + 2 : ℕ) : ℝ) - 1 := by push_cast; linarith
  have hrem : ‖riemannZeta w - RHTower.zetaEulerMaclaurinMain m M w‖ ≤
      emCoeff m * ((‖w‖ + (2 * m + 2)) ^ (2 * m + 2) / (M : ℝ) ^ (2 * m + 1)) * X := by
    refine hEM.trans ?_
    rw [hpowR]
    have hr := norm_complexRisingFactor_le w (2 * m + 2)
    push_cast at hr
    have hMp : 0 < (M : ℝ) ^ (2 * m + 1) := by positivity
    calc emCoeff m * ‖RHTower.complexRisingFactor w (2 * m + 2)‖ *
          (X / (M : ℝ) ^ (2 * m + 1) / (w.re + ((2 * m + 2 : ℕ) : ℝ) - 1))
        ≤ emCoeff m * (‖w‖ + (2 * m + 2)) ^ (2 * m + 2) * (X / (M : ℝ) ^ (2 * m + 1) / 1) := by
          unfold emCoeff
          gcongr
      _ = _ := by ring
  -- the boundary terms
  have hbd : ‖RHTower.zetaEMBoundary m w M‖ ≤ X / 2 + (∑ r ∈ range (m + 1), emCoeff r) * X := by
    rw [RHTower.zetaEMBoundary]
    refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
    · rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hM0, Complex.neg_re]
      norm_num
      exact hX.symm
    · refine (norm_sum_le _ _).trans ?_
      rw [sum_mul]
      refine sum_le_sum fun r hr => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, Nat.abs_cast,
        RHTower.norm_complexPowerTower _ _ hM0]
      have hr1 := norm_complexRisingFactor_le w (2 * r + 1)
      have hrm : (r : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hr)
      have hle : ‖w‖ + ((2 * r + 1 : ℕ) : ℝ) ≤ M := by push_cast; linarith
      have hpw : (M : ℝ) ^ (-w.re - ((2 * r + 1 : ℕ) : ℝ)) = X / (M : ℝ) ^ (2 * r + 1) := by
        rw [Real.rpow_sub hM0, Real.rpow_natCast]
      rw [hpw]
      have hq : ‖RHTower.complexRisingFactor w (2 * r + 1)‖ / (M : ℝ) ^ (2 * r + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact hr1.trans (pow_le_pow_left₀ (by positivity) hle _)
      calc |((bernoulli (2 * r + 2) : ℚ) : ℝ)| / ((2 * r + 2).factorial : ℝ) *
            (‖RHTower.complexRisingFactor w (2 * r + 1)‖ * (X / (M : ℝ) ^ (2 * r + 1))) =
          emCoeff r * X * (‖RHTower.complexRisingFactor w (2 * r + 1)‖ / (M : ℝ) ^ (2 * r + 1)) := by
            unfold emCoeff; ring
        _ ≤ emCoeff r * X * 1 := by gcongr; exact mul_nonneg (emCoeff_nonneg r) hX0.le
        _ = emCoeff r * X := by ring
  have hid : RHTower.zetaStripError w M =
      -(riemannZeta w - RHTower.zetaEulerMaclaurinMain m M w) + RHTower.zetaEMBoundary m w M := by
    unfold RHTower.zetaStripError RHTower.zetaEulerMaclaurinMain
    push_cast
    ring
  rw [hid]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg]
  have hY : 0 ≤ (‖w‖ + (2 * m + 2)) ^ (2 * m + 2) / (M : ℝ) ^ (2 * m + 1) := by positivity
  have hS : 0 ≤ ∑ r ∈ range (m + 1), emCoeff r := sum_nonneg fun r _ => emCoeff_nonneg r
  have hcm := emCoeff_nonneg m
  unfold emConst
  set Y := (‖w‖ + (2 * m + 2)) ^ (2 * m + 2) / (M : ℝ) ^ (2 * m + 1) with hYdef
  set S := ∑ r ∈ range (m + 1), emCoeff r with hSdef
  have h1 : 0 ≤ emCoeff m * X := mul_nonneg hcm hX0.le
  have h2 : 0 ≤ (1 / 2 + S) * (Y * X) := mul_nonneg (by linarith) (mul_nonneg hY hX0.le)
  have e : (1 / 2 + S + emCoeff m) * (1 + Y) * X =
      emCoeff m * Y * X + (X / 2 + S * X) + (emCoeff m * X + (1 / 2 + S) * (Y * X)) := by ring
  rw [e]
  linarith [add_le_add hrem hbd]

theorem emConst_nonneg (m : ℕ) : 0 ≤ emConst m := by
  unfold emConst
  have h1 := sum_nonneg fun r (_ : r ∈ range (m + 1)) => emCoeff_nonneg r
  have h2 := emCoeff_nonneg m
  linarith

/-! ### The conductor polynomial at a zero, uniformly -/

/-- One divisor of the Möbius splitting at a zero, at Euler–Maclaurin order `m`. -/
theorem norm_divisorTerm_le_order {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta (1 - s) = 0) {d N : ℕ} (hd : 1 ≤ d) (m : ℕ)
    (hN : 2 * d * (‖s‖ + (2 * m + 4)) ≤ N) :
    ‖riemannZeta (1 - s) + ((((N / d : ℕ) : ℝ) : ℂ) ^ s - (((N : ℝ) / d : ℝ) : ℂ) ^ s) / s +
        RHTower.zetaStripError (1 - s) (N / d)‖ ≤
      (2 + emConst m * (1 + (‖s‖ + (2 * m + 3)) ^ (2 * m + 2) /
        ((N / d : ℕ) : ℝ) ^ (2 * m + 1))) * ((N / d : ℕ) : ℝ) ^ (s.re - 1) := by
  have hs0' : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs0; exact lt_irrefl 0 hs0
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0'
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨M, hM⟩ : ∃ M, M = N / d := ⟨_, rfl⟩
  rw [← hM]
  have hMd : (N : ℝ) < ((M : ℝ) + 1) * d := by
    have := Nat.lt_div_mul_add (a := N) (b := d) (by omega)
    rw [← hM] at this
    have h' : (N : ℝ) < ((M * d + d : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h'; linarith
  have hNd : 2 * (‖s‖ + (2 * m + 4)) ≤ (N : ℝ) / d := by rw [le_div_iff₀ hd0]; linarith
  have hlt : (N : ℝ) / d < (M : ℝ) + 1 := by rw [div_lt_iff₀ hd0]; linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hM1 : ‖s‖ + (2 * m + 3) ≤ (M : ℝ) := by linarith [norm_nonneg s]
  have hM1' : 1 ≤ M := by
    have : (1 : ℝ) ≤ M := by linarith [norm_nonneg s]
    exact_mod_cast this
  have hfl : ⌊(N : ℝ) / d⌋₊ = M := by rw [hM]; exact Nat.floor_div_eq_div N d
  have hNd1 : (1 : ℝ) ≤ (N : ℝ) / d := by linarith [norm_nonneg s]
  have hflo := RHTower.norm_cpow_natFloor_sub_cpow_le (s := s) hNd1 (by rw [hfl]; linarith)
  rw [hfl] at hflo
  have hw0 : 0 < (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hw1 : (1 : ℂ) - s ≠ 1 := fun h => hs0' (by linear_combination -h)
  have hwn : ‖(1 : ℂ) - s‖ ≤ 1 + ‖s‖ := (norm_sub_le _ _).trans (by rw [norm_one])
  have hstr := norm_zetaStripError_le_order hw0 hw1 hM1' m (by linarith)
  have hre : -(1 - s).re = s.re - 1 := by simp only [Complex.sub_re, Complex.one_re]; ring
  rw [hre] at hstr
  have hpow : (‖(1 : ℂ) - s‖ + (2 * m + 2)) ^ (2 * m + 2) ≤ (‖s‖ + (2 * m + 3)) ^ (2 * m + 2) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hMp : 0 < (M : ℝ) ^ (2 * m + 1) := by positivity
  have hY : (‖(1 : ℂ) - s‖ + (2 * m + 2)) ^ (2 * m + 2) / (M : ℝ) ^ (2 * m + 1) ≤
      (‖s‖ + (2 * m + 3)) ^ (2 * m + 2) / (M : ℝ) ^ (2 * m + 1) :=
    div_le_div_of_nonneg_right hpow hMp.le
  have hK := emConst_nonneg m
  rw [hz, zero_add]
  refine (norm_add_le _ _).trans ?_
  rw [norm_div]
  have hX : 0 ≤ (M : ℝ) ^ (s.re - 1) := by positivity
  calc ‖(((M : ℝ) : ℂ)) ^ s - (((N : ℝ) / d : ℝ) : ℂ) ^ s‖ / ‖s‖ +
        ‖RHTower.zetaStripError (1 - s) M‖
      ≤ 2 * ‖s‖ * (M : ℝ) ^ (s.re - 1) / ‖s‖ + emConst m * (1 + (‖(1 : ℂ) - s‖ + (2 * m + 2)) ^
          (2 * m + 2) / (M : ℝ) ^ (2 * m + 1)) * (M : ℝ) ^ (s.re - 1) :=
        add_le_add (div_le_div_of_nonneg_right hflo hsn.le) hstr
    _ = 2 * (M : ℝ) ^ (s.re - 1) + emConst m * (1 + (‖(1 : ℂ) - s‖ + (2 * m + 2)) ^
          (2 * m + 2) / (M : ℝ) ^ (2 * m + 1)) * (M : ℝ) ^ (s.re - 1) := by
        field_simp
    _ ≤ 2 * (M : ℝ) ^ (s.re - 1) + emConst m * (1 + (‖s‖ + (2 * m + 3)) ^ (2 * m + 2) /
          (M : ℝ) ^ (2 * m + 1)) * (M : ℝ) ^ (s.re - 1) := by gcongr
    _ = _ := by ring

/-- **The conductor polynomial at a zero, uniformly.** If `ζ(1 − s) = 0`, `0 < Re s < 1`,
`N ≥ 2e(‖s‖ + 2m + 4)` and `(‖s‖ + 2m + 3)^{2m+2} ≤ (N/2e)^{2m+1}`, then
`‖D_e(s;N) − [e = 1]N^s/s‖ ≤ 4e³(2 + 2K_m) N^{Re s − 1}`. -/
theorem norm_conductorDirichlet_sub_horizonTerm_le_order {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1) (hz : riemannZeta (1 - s) = 0) {e N : ℕ} (he : 1 ≤ e) (m : ℕ)
    (hN : 2 * e * (‖s‖ + (2 * m + 4)) ≤ N)
    (hXN : (‖s‖ + (2 * m + 3)) ^ (2 * m + 2) ≤ ((N : ℝ) / (2 * e)) ^ (2 * m + 1)) :
    ‖conductorDirichlet e N s - horizonTerm e N s‖ ≤
      4 * (e : ℝ) ^ 3 * (2 + 2 * emConst m) * (N : ℝ) ^ (s.re - 1) := by
  have hs0' : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs0; exact lt_irrefl 0 hs0
  have hrw : conductorDirichlet e N s - horizonTerm e N s =
      ∑ d ∈ e.divisors, (moebiusReal (e / d) : ℂ) * ((d : ℝ) : ℂ) ^ s *
        (riemannZeta (1 - s) + ((((N / d : ℕ) : ℝ) : ℂ) ^ s - (((N : ℝ) / d : ℝ) : ℂ) ^ s) / s +
          RHTower.zetaStripError (1 - s) (N / d)) := by
    rw [conductorDirichlet_eq, horizonTerm_eq_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun d _ => ?_
    rw [partialZeta_eq]
    field_simp
    ring
  rw [hrw]
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hN0 : (0 : ℝ) < N := by nlinarith [norm_nonneg s]
  have hσ : s.re - 1 ≤ 0 := by linarith
  have hK := emConst_nonneg m
  have hterm : ∀ d ∈ e.divisors, ‖(moebiusReal (e / d) : ℂ) * ((d : ℝ) : ℂ) ^ s *
      (riemannZeta (1 - s) + ((((N / d : ℕ) : ℝ) : ℂ) ^ s - (((N : ℝ) / d : ℝ) : ℂ) ^ s) / s +
        RHTower.zetaStripError (1 - s) (N / d))‖ ≤
      4 * (e : ℝ) ^ 2 * (2 + 2 * emConst m) * (N : ℝ) ^ (s.re - 1) := by
    intro d hd
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    have hde : d ≤ e := Nat.divisor_le hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have hdeR : (d : ℝ) ≤ e := by exact_mod_cast hde
    have hNd : 2 * d * (‖s‖ + (2 * m + 4)) ≤ (N : ℝ) := le_trans (by gcongr) hN
    have hdiv := norm_divisorTerm_le_order hs0 hs1 hz hd1 m hNd
    have hμ : ‖(moebiusReal (e / d) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_moebiusReal_le _
    have hds : ‖((d : ℝ) : ℂ) ^ s‖ ≤ e := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hd0]
      calc (d : ℝ) ^ s.re ≤ (d : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hd1) hs1.le
        _ = d := Real.rpow_one _
        _ ≤ e := hdeR
    have hMd : (N : ℝ) / (2 * e) ≤ ((N / d : ℕ) : ℝ) := by
      have h1 := Nat.lt_div_mul_add (a := N) (b := d) (by omega)
      have h1' : (N : ℝ) < (((N / d) * d + d : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h1'
      have hNd' : 2 * (‖s‖ + (2 * m + 4)) ≤ (N : ℝ) / d := by rw [le_div_iff₀ hd0]; linarith
      have hlt : (N : ℝ) / d < ((N / d : ℕ) : ℝ) + 1 := by rw [div_lt_iff₀ hd0]; linarith
      have hge1 : (1 : ℝ) ≤ ((N / d : ℕ) : ℝ) := by linarith [norm_nonneg s]
      rw [div_le_iff₀ (by positivity)]
      have : (N : ℝ) < 2 * ((N / d : ℕ) : ℝ) * d := by nlinarith
      nlinarith
    have hNpos : (0 : ℝ) < (N : ℝ) / (2 * e) := by positivity
    have hM : ((N / d : ℕ) : ℝ) ^ (s.re - 1) ≤ 2 * e * (N : ℝ) ^ (s.re - 1) := by
      refine (Real.rpow_le_rpow_of_nonpos hNpos hMd hσ).trans ?_
      rw [div_eq_mul_inv, Real.mul_rpow hN0.le (by positivity), Real.inv_rpow (by positivity),
        ← Real.rpow_neg (by positivity), mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      calc (2 * (e : ℝ)) ^ (-(s.re - 1)) ≤ (2 * (e : ℝ)) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = 2 * e := Real.rpow_one _
    have hY : (‖s‖ + (2 * m + 3)) ^ (2 * m + 2) / ((N / d : ℕ) : ℝ) ^ (2 * m + 1) ≤ 1 := by
      rw [div_le_one (pow_pos (lt_of_lt_of_le hNpos hMd) _)]
      exact hXN.trans (pow_le_pow_left₀ hNpos.le hMd _)
    have hdiv' : ‖riemannZeta (1 - s) + ((((N / d : ℕ) : ℝ) : ℂ) ^ s -
        (((N : ℝ) / d : ℝ) : ℂ) ^ s) / s + RHTower.zetaStripError (1 - s) (N / d)‖ ≤
        (2 + 2 * emConst m) * (2 * e * (N : ℝ) ^ (s.re - 1)) := by
      refine hdiv.trans ?_
      have h2 : 2 + emConst m * (1 + (‖s‖ + (2 * m + 3)) ^ (2 * m + 2) /
          ((N / d : ℕ) : ℝ) ^ (2 * m + 1)) ≤ 2 + 2 * emConst m := by nlinarith
      exact mul_le_mul h2 hM (by positivity) (by positivity)
    rw [norm_mul, norm_mul]
    calc ‖(moebiusReal (e / d) : ℂ)‖ * ‖((d : ℝ) : ℂ) ^ s‖ *
          ‖riemannZeta (1 - s) + ((((N / d : ℕ) : ℝ) : ℂ) ^ s - (((N : ℝ) / d : ℝ) : ℂ) ^ s) / s +
            RHTower.zetaStripError (1 - s) (N / d)‖
        ≤ 1 * e * ((2 + 2 * emConst m) * (2 * e * (N : ℝ) ^ (s.re - 1))) := by
          gcongr
      _ ≤ 4 * (e : ℝ) ^ 2 * (2 + 2 * emConst m) * (N : ℝ) ^ (s.re - 1) := by
          have : 0 ≤ (2 + 2 * emConst m) * (N : ℝ) ^ (s.re - 1) := by positivity
          nlinarith
  refine (norm_sum_le _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [sum_const, nsmul_eq_mul]
  have hcard : (e.divisors.card : ℝ) ≤ e := by exact_mod_cast Nat.card_divisors_le_self e
  calc (e.divisors.card : ℝ) * (4 * (e : ℝ) ^ 2 * (2 + 2 * emConst m) * (N : ℝ) ^ (s.re - 1)) ≤
        e * (4 * (e : ℝ) ^ 2 * (2 + 2 * emConst m) * (N : ℝ) ^ (s.re - 1)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

/-- The packet constant at order `m`: `Σ_{e∈E} |y_e/√φ(e)| · 4e³(2 + 2K_m)`. -/
def packetConstOrder (E : Finset ℕ) (y : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ e ∈ E, |y e / Real.sqrt e.totient| * (4 * (e : ℝ) ^ 3 * (2 + 2 * emConst m))

theorem packetConstOrder_nonneg (E : Finset ℕ) (y : ℕ → ℝ) (m : ℕ) :
    0 ≤ packetConstOrder E y m := by
  unfold packetConstOrder
  have := emConst_nonneg m
  exact sum_nonneg fun e _ => by positivity

/-- **A packet at a zero, uniformly**: `‖√log N · D_x(γ_s) − y_1 N^s/s‖ ≤ P_m N^{Re s − 1}`. -/
theorem norm_dirichletPoly_packet_sub_pole_le_order {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta (1 - s) = 0) {E : Finset ℕ} (hE : ∀ e ∈ E, 1 ≤ e) {L : ℕ}
    (hL : ∀ e ∈ E, e ≤ L) (y : ℕ → ℝ) (m : ℕ) {N : ℕ}
    (hN : 2 * L * (‖s‖ + (2 * m + 4)) ≤ N)
    (hXN : (‖s‖ + (2 * m + 3)) ^ (2 * m + 2) ≤ ((N : ℝ) / (2 * L)) ^ (2 * m + 1))
    (hlog : 0 < Real.log N) :
    ‖((Real.sqrt (Real.log N) : ℝ) : ℂ) * dirichletPoly N (packetWeights E y N) (gammaOf s) -
        (poleCoefficient E y : ℂ) * (((N : ℝ) : ℂ) ^ s / s)‖ ≤
      packetConstOrder E y m * (N : ℝ) ^ (s.re - 1) := by
  have hsq : ((Real.sqrt (Real.log N) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hlog).ne'
  rw [dirichletPoly_packetWeights, ← mul_assoc, mul_inv_cancel₀ hsq, one_mul]
  have hpole : (poleCoefficient E y : ℂ) =
      if 1 ∈ E then ((y 1 / Real.sqrt (Nat.totient 1) : ℝ) : ℂ) else 0 := by
    unfold poleCoefficient
    split_ifs <;> simp
  have hsum := sum_mul_horizonTerm E (fun e => ((y e / Real.sqrt e.totient : ℝ) : ℂ)) N s
  beta_reduce at hsum
  rw [hpole, ← hsum, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  unfold packetConstOrder
  rw [Finset.sum_mul]
  refine sum_le_sum fun e he => ?_
  have heL : (e : ℝ) ≤ L := by exact_mod_cast hL e he
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast hE e he
  have hNe : 2 * e * (‖s‖ + (2 * m + 4)) ≤ (N : ℝ) := by
    refine le_trans ?_ hN
    gcongr
  have hXe : (‖s‖ + (2 * m + 3)) ^ (2 * m + 2) ≤ ((N : ℝ) / (2 * e)) ^ (2 * m + 1) := by
    refine hXN.trans (pow_le_pow_left₀ (by positivity) ?_ _)
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by positivity) (by linarith)
  have hb := norm_conductorDirichlet_sub_horizonTerm_le_order hs0 hs1 hz (hE e he) m hNe hXe
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |y e / Real.sqrt e.totient| * ‖conductorDirichlet e N s - horizonTerm e N s‖ ≤
        |y e / Real.sqrt e.totient| * (4 * (e : ℝ) ^ 3 * (2 + 2 * emConst m) *
          (N : ℝ) ^ (s.re - 1)) := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := by ring

/-! ### One zero, uniformly -/

/-- **One zero, uniformly in its height.** For a nontrivial zero `ρ` with `N ≥ 2L(‖ρ‖ + 2m + 5)`,
`(‖ρ‖ + 2m + 4)^{2m+2} ≤ (N/2L)^{2m+1}` and `c(‖ρ‖ + 1) ≤ N`:
`‖(log N/c) W_ρ/∫g² − m_ρ κ y_1²/(ρ(1−ρ))‖ ≤ m_ρ (C₁ c/N + C₂ (|y_1| P_m + P_m²/N)/N)`. -/
theorem norm_log_div_mul_bulkLedger_sub_le_order {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {E : Finset ℕ}
    (hE : ∀ e ∈ E, 1 ≤ e) {L : ℕ} (hL : ∀ e ∈ E, e ≤ L) (y : ℕ → ℝ) (m : ℕ) {ρ : ℂ}
    (hρ : ρ ∈ zetaZeroConfig.carrier) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN2 : 2 ≤ N)
    (hNL : 2 * L * (‖ρ‖ + (2 * m + 5)) ≤ N)
    (hXN : (‖ρ‖ + (2 * m + 4)) ^ (2 * m + 2) ≤ ((N : ℝ) / (2 * L)) ^ (2 * m + 1))
    (hcN : c * (‖ρ‖ + 1) ≤ N) :
    ‖((Real.log N / c : ℝ) : ℂ) * bulkLedger zetaZeroConfig φ E y c N ρ -
        (zetaZeroConfig.mult ρ : ℂ) * (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) *
          (((poleCoefficient E y ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ)))‖ ≤
      zetaZeroConfig.mult ρ *
        (2 * (Real.exp 1 + 1) * (∫ u, |φ u|) ^ 2 * poleCoefficient E y ^ 2 / (∫ u, φ u ^ 2) *
            (c / N) +
          (2 * Real.exp 1 + 3) * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2) *
            ((|poleCoefficient E y| * packetConstOrder E y m +
              packetConstOrder E y m ^ 2 / N) / N)) := by
  obtain ⟨hζ, hβ0, hβ1⟩ : riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 := ⟨hρ.1, hρ.2.1, hρ.2.2⟩
  have hz1 : riemannZeta (1 - ρ) = 0 :=
    RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hζ hβ0 hβ1
  obtain ⟨hρ3, hρ3'⟩ := three_lt_norm_of_mem hρ
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [log_div_mul_bulkLedger zetaZeroConfig hφ hφc hφ2 E y hc (by omega) ρ]
  -- the atom factors
  have hw0 : 0 < c / N := div_pos hc hN0
  have hz₁n : ‖((c / N : ℝ) : ℂ) * gammaOf ρ‖ ≤ c / N * (‖ρ‖ + 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw0]
    exact mul_le_mul_of_nonneg_left (norm_gammaOf_le ρ) hw0.le
  have hz₂n : ‖((c / N : ℝ) : ℂ) * conj (gammaOf ρ)‖ ≤ c / N * (‖ρ‖ + 1) := by
    rw [norm_mul, Complex.norm_conj, ← norm_mul]; exact hz₁n
  have hw1 : c / N * (‖ρ‖ + 1) ≤ 1 := by rw [div_mul_eq_mul_div, div_le_one hN0]; exact hcN
  have ha₀n : ‖((∫ u, φ u : ℝ) : ℂ)‖ ≤ ∫ u, |φ u| := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_integral_le_integral_abs
  have hI₁0 : 0 ≤ ∫ u, |φ u| := integral_nonneg fun u => abs_nonneg _
  have hF₂n : ‖conj (paperFT (cx φ) (((c / N : ℝ) : ℂ) * conj (gammaOf ρ)))‖ ≤
      (∫ u, |φ u|) * Real.exp 1 := by
    rw [Complex.norm_conj]; exact norm_paperFT_profile_le hφ hφsupp (hz₂n.trans hw1)
  have hd₁ : ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * gammaOf ρ) - ((∫ u, φ u : ℝ) : ℂ)‖ ≤
      2 * (c / N * (‖ρ‖ + 1)) * ∫ u, |φ u| :=
    (norm_paperFT_sub_integral_le hφ hφsupp (hz₁n.trans hw1)).trans (by gcongr)
  have hd₂ : ‖conj (paperFT (cx φ) (((c / N : ℝ) : ℂ) * conj (gammaOf ρ))) -
      ((∫ u, φ u : ℝ) : ℂ)‖ ≤ 2 * (c / N * (‖ρ‖ + 1)) * ∫ u, |φ u| := by
    have e : conj (paperFT (cx φ) (((c / N : ℝ) : ℂ) * conj (gammaOf ρ))) - ((∫ u, φ u : ℝ) : ℂ) =
        conj (paperFT (cx φ) (((c / N : ℝ) : ℂ) * conj (gammaOf ρ)) - ((∫ u, φ u : ℝ) : ℂ)) := by
      rw [map_sub, Complex.conj_ofReal]
    rw [e, Complex.norm_conj]
    exact (norm_paperFT_sub_integral_le hφ hφsupp (hz₂n.trans hw1)).trans (by gcongr)
  have hδ := norm_atom_product_sub_le hF₂n ha₀n hd₁ hd₂
  -- the Dirichlet factors
  have hn1 : ‖(1 : ℂ) - ρ‖ ≤ 1 + ‖ρ‖ := (norm_sub_le _ _).trans (by rw [norm_one])
  have hX₁ := norm_dirichletPoly_packet_sub_pole_le_order hβ0 hβ1 hz1 hE hL y m (N := N)
    (by nlinarith [norm_nonneg ρ])
    (le_trans (pow_le_pow_left₀ (by positivity) (by linarith) _) hXN) hlog
  have hre1 : 0 < (1 - ρ).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hre2 : (1 - ρ).re < 1 := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hX₂ := norm_dirichletPoly_packet_sub_pole_le_order hre1 hre2
    (by rw [sub_sub_cancel]; exact hζ) hE hL y m (N := N)
    (by nlinarith [norm_nonneg ρ, norm_nonneg ((1 : ℂ) - ρ)])
    (le_trans (pow_le_pow_left₀ (by positivity) (by linarith) _) hXN) hlog
  have hσ2 : (1 - ρ).re - 1 = -ρ.re := by simp only [Complex.sub_re, Complex.one_re]; ring
  rw [hσ2] at hX₂
  have hNC : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  have hB : ((Real.log N / N : ℝ) : ℂ) * (dirichletPoly N (packetWeights E y N) (gammaOf ρ) *
      dirichletPoly N (packetWeights E y N) (gammaOf (1 - ρ))) =
      (((Real.sqrt (Real.log N) : ℝ) : ℂ) * dirichletPoly N (packetWeights E y N) (gammaOf ρ)) *
        (((Real.sqrt (Real.log N) : ℝ) : ℂ) *
          dirichletPoly N (packetWeights E y N) (gammaOf (1 - ρ))) / ((N : ℝ) : ℂ) := by
    have hSS : ((Real.sqrt (Real.log N) : ℝ) : ℂ) * ((Real.sqrt (Real.log N) : ℝ) : ℂ) =
        ((Real.log N : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hlog.le]
    rw [show ((Real.log N / N : ℝ) : ℂ) = ((Real.log N : ℝ) : ℂ) / ((N : ℝ) : ℂ) by push_cast; ring,
      ← hSS]
    field_simp
  rw [hB]
  generalize ((Real.sqrt (Real.log N) : ℝ) : ℂ) *
    dirichletPoly N (packetWeights E y N) (gammaOf ρ) = X₁ at hX₁ ⊢
  generalize ((Real.sqrt (Real.log N) : ℝ) : ℂ) *
    dirichletPoly N (packetWeights E y N) (gammaOf (1 - ρ)) = X₂ at hX₂ ⊢
  generalize paperFT (cx φ) (((c / N : ℝ) : ℂ) * gammaOf ρ) = F₁ at hδ ⊢
  generalize conj (paperFT (cx φ) (((c / N : ℝ) : ℂ) * conj (gammaOf ρ))) = F₂ at hδ ⊢
  generalize hP : packetConstOrder E y m = P at hX₁ hX₂ ⊢
  generalize hp : poleCoefficient E y = p at hX₁ hX₂ ⊢
  have hP0 : 0 ≤ P := hP ▸ packetConstOrder_nonneg E y m
  -- `B − L`
  have hρ0 : ρ ≠ 0 := fun h => by rw [h, norm_zero] at hρ3; linarith
  have hρ1 : (1 : ℂ) - ρ ≠ 0 := fun h => by rw [h, norm_zero] at hρ3'; linarith
  have hNN : ((N : ℝ) : ℂ) ^ ρ * ((N : ℝ) : ℂ) ^ (1 - ρ) = ((N : ℝ) : ℂ) := by
    rw [← Complex.cpow_add _ _ hNC, add_sub_cancel, Complex.cpow_one]
  have hHH : ((p : ℂ) * (((N : ℝ) : ℂ) ^ ρ / ρ)) * ((p : ℂ) * (((N : ℝ) : ℂ) ^ (1 - ρ) / (1 - ρ))) =
      ((N : ℝ) : ℂ) * (((p ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))) := by
    calc ((p : ℂ) * (((N : ℝ) : ℂ) ^ ρ / ρ)) * ((p : ℂ) * (((N : ℝ) : ℂ) ^ (1 - ρ) / (1 - ρ))) =
          (p : ℂ) ^ 2 * (((N : ℝ) : ℂ) ^ ρ * ((N : ℝ) : ℂ) ^ (1 - ρ)) * (ρ⁻¹ * (1 - ρ)⁻¹) := by
          ring
      _ = (p : ℂ) ^ 2 * ((N : ℝ) : ℂ) * (ρ⁻¹ * (1 - ρ)⁻¹) := by rw [hNN]
      _ = ((N : ℝ) : ℂ) * (((p ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))) := by
          rw [div_eq_mul_inv, mul_inv]; push_cast; ring
  have hBL := mul_div_sub_eq (X₁ := X₁) (X₂ := X₂) hNC hHH
  have hNρ : ‖((N : ℝ) : ℂ) ^ ρ‖ = (N : ℝ) ^ ρ.re := Complex.norm_cpow_eq_rpow_re_of_pos hN0 _
  have hNρ' : ‖((N : ℝ) : ℂ) ^ (1 - ρ)‖ = (N : ℝ) ^ (1 - ρ.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN0]; simp
  have hpow1 : (N : ℝ) ^ ρ.re * (N : ℝ) ^ (-ρ.re) = 1 := by
    rw [← Real.rpow_add hN0, add_neg_cancel, Real.rpow_zero]
  have hpow2 : (N : ℝ) ^ (1 - ρ.re) * (N : ℝ) ^ (ρ.re - 1) = 1 := by
    rw [← Real.rpow_add hN0, show 1 - ρ.re + (ρ.re - 1) = 0 by ring, Real.rpow_zero]
  have hpow3 : (N : ℝ) ^ (ρ.re - 1) * (N : ℝ) ^ (-ρ.re) = (N : ℝ)⁻¹ := by
    rw [← Real.rpow_add hN0, show ρ.re - 1 + -ρ.re = -1 by ring, Real.rpow_neg_one]
  have ht1 : ‖(p : ℂ) * (((N : ℝ) : ℂ) ^ ρ / ρ) *
      (X₂ - (p : ℂ) * (((N : ℝ) : ℂ) ^ (1 - ρ) / (1 - ρ)))‖ ≤ |p| * P / 3 := by
    rw [norm_mul, norm_mul, norm_div, hNρ, Complex.norm_real, Real.norm_eq_abs]
    calc |p| * ((N : ℝ) ^ ρ.re / ‖ρ‖) *
          ‖X₂ - (p : ℂ) * (((N : ℝ) : ℂ) ^ (1 - ρ) / (1 - ρ))‖ ≤
          |p| * ((N : ℝ) ^ ρ.re / ‖ρ‖) * (P * (N : ℝ) ^ (-ρ.re)) :=
          mul_le_mul_of_nonneg_left hX₂ (by positivity)
      _ = |p| * P / ‖ρ‖ * ((N : ℝ) ^ ρ.re * (N : ℝ) ^ (-ρ.re)) := by ring
      _ ≤ |p| * P / 3 := by
          rw [hpow1, mul_one]
          exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hρ3.le
  have ht2 : ‖(X₁ - (p : ℂ) * (((N : ℝ) : ℂ) ^ ρ / ρ)) *
      ((p : ℂ) * (((N : ℝ) : ℂ) ^ (1 - ρ) / (1 - ρ)))‖ ≤ |p| * P / 3 := by
    rw [norm_mul, norm_mul, norm_div, hNρ', Complex.norm_real, Real.norm_eq_abs]
    calc ‖X₁ - (p : ℂ) * (((N : ℝ) : ℂ) ^ ρ / ρ)‖ *
          (|p| * ((N : ℝ) ^ (1 - ρ.re) / ‖(1 : ℂ) - ρ‖)) ≤
          (P * (N : ℝ) ^ (ρ.re - 1)) * (|p| * ((N : ℝ) ^ (1 - ρ.re) / ‖(1 : ℂ) - ρ‖)) :=
          mul_le_mul_of_nonneg_right hX₁ (by positivity)
      _ = |p| * P / ‖(1 : ℂ) - ρ‖ * ((N : ℝ) ^ (1 - ρ.re) * (N : ℝ) ^ (ρ.re - 1)) := by ring
      _ ≤ |p| * P / 3 := by
          rw [hpow2, mul_one]
          exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hρ3'.le
  have ht3 : ‖(X₁ - (p : ℂ) * (((N : ℝ) : ℂ) ^ ρ / ρ)) *
      (X₂ - (p : ℂ) * (((N : ℝ) : ℂ) ^ (1 - ρ) / (1 - ρ)))‖ ≤ P ^ 2 / N := by
    rw [norm_mul]
    calc _ ≤ (P * (N : ℝ) ^ (ρ.re - 1)) * (P * (N : ℝ) ^ (-ρ.re)) :=
          mul_le_mul hX₁ hX₂ (norm_nonneg _) (by positivity)
      _ = P ^ 2 * ((N : ℝ) ^ (ρ.re - 1) * (N : ℝ) ^ (-ρ.re)) := by ring
      _ = P ^ 2 / N := by rw [hpow3]; ring
  have hEB : ‖X₁ * X₂ / ((N : ℝ) : ℂ) - ((p ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))‖ ≤
      (|p| * P + P ^ 2 / N) / N := by
    rw [hBL, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN0]
    refine div_le_div_of_nonneg_right ?_ hN0.le
    refine (norm_add₃_le).trans ?_
    have : 0 ≤ |p| * P := by positivity
    linarith
  -- `‖L‖` against the overlap
  have hLn : ‖((p ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))‖ ≤ p ^ 2 / (‖ρ‖ * ‖(1 : ℂ) - ρ‖) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul]
  have hmul : 3 * ‖ρ‖ ≤ ‖ρ‖ * ‖(1 : ℂ) - ρ‖ := by
    have := mul_le_mul_of_nonneg_right hρ3'.le (norm_nonneg ρ)
    linarith [mul_comm ‖(1 : ℂ) - ρ‖ ‖ρ‖]
  have hr1 : (‖ρ‖ + 1) / (‖ρ‖ * ‖(1 : ℂ) - ρ‖) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hwL : c / N * (‖ρ‖ + 1) * ‖((p ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))‖ ≤ c / N * p ^ 2 := by
    calc c / N * (‖ρ‖ + 1) * ‖((p ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))‖ ≤
          c / N * (‖ρ‖ + 1) * (p ^ 2 / (‖ρ‖ * ‖(1 : ℂ) - ρ‖)) :=
          mul_le_mul_of_nonneg_left hLn (by positivity)
      _ = c / N * p ^ 2 * ((‖ρ‖ + 1) / (‖ρ‖ * ‖(1 : ℂ) - ρ‖)) := by ring
      _ ≤ c / N * p ^ 2 * 1 := mul_le_mul_of_nonneg_left hr1 (by positivity)
      _ = c / N * p ^ 2 := by ring
  -- assemble
  have hI0 : (0 : ℝ) < ∫ u, φ u ^ 2 := hφ2
  have hICne : ((∫ u, φ u ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hI0.ne'
  have hmain : (zetaZeroConfig.mult ρ : ℂ) * (F₁ * F₂) / ((∫ u, φ u ^ 2 : ℝ) : ℂ) *
        (X₁ * X₂ / ((N : ℝ) : ℂ)) - (zetaZeroConfig.mult ρ : ℂ) *
        (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) * (((p ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))) =
      (zetaZeroConfig.mult ρ : ℂ) / ((∫ u, φ u ^ 2 : ℝ) : ℂ) *
        ((F₁ * F₂ - ((∫ u, φ u : ℝ) : ℂ) * ((∫ u, φ u : ℝ) : ℂ)) * (X₁ * X₂ / ((N : ℝ) : ℂ)) +
          ((∫ u, φ u : ℝ) : ℂ) * ((∫ u, φ u : ℝ) : ℂ) *
            (X₁ * X₂ / ((N : ℝ) : ℂ) - ((p ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ)))) := by
    push_cast
    field_simp
    ring
  rw [hmain, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hI0]
  have hcore := norm_ledger_core_le hδ ha₀n hEB
  set δ₀ := 2 * (Real.exp 1 + 1) * (∫ u, |φ u|) ^ 2 * (c / N * (‖ρ‖ + 1)) with hδ₀
  have hδ₀1 : δ₀ ≤ 2 * (Real.exp 1 + 1) * (∫ u, |φ u|) ^ 2 :=
    mul_le_of_le_one_right (by positivity) hw1
  have hδL : δ₀ * ‖((p ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))‖ ≤
      2 * (Real.exp 1 + 1) * (∫ u, |φ u|) ^ 2 * (c / N * p ^ 2) := by
    rw [hδ₀, mul_assoc]
    exact mul_le_mul_of_nonneg_left hwL (by positivity)
  have hEB0 : 0 ≤ (|p| * P + P ^ 2 / N) / N := by positivity
  have hm0' : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  have hfin : δ₀ * ‖((p ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))‖ + (δ₀ + (∫ u, |φ u|) ^ 2) *
      ((|p| * P + P ^ 2 / N) / N) ≤
      2 * (Real.exp 1 + 1) * (∫ u, |φ u|) ^ 2 * (c / N * p ^ 2) +
        (2 * Real.exp 1 + 3) * (∫ u, |φ u|) ^ 2 * ((|p| * P + P ^ 2 / N) / N) := by
    have h1 : δ₀ + (∫ u, |φ u|) ^ 2 ≤ (2 * Real.exp 1 + 3) * (∫ u, |φ u|) ^ 2 := by linarith
    exact add_le_add hδL (mul_le_mul_of_nonneg_right h1 hEB0)
  calc (zetaZeroConfig.mult ρ : ℝ) / (∫ u, φ u ^ 2) *
        ‖(F₁ * F₂ - ((∫ u, φ u : ℝ) : ℂ) * ((∫ u, φ u : ℝ) : ℂ)) * (X₁ * X₂ / ((N : ℝ) : ℂ)) +
          ((∫ u, φ u : ℝ) : ℂ) * ((∫ u, φ u : ℝ) : ℂ) *
            (X₁ * X₂ / ((N : ℝ) : ℂ) - ((p ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ)))‖ ≤
        (zetaZeroConfig.mult ρ : ℝ) / (∫ u, φ u ^ 2) *
          (2 * (Real.exp 1 + 1) * (∫ u, |φ u|) ^ 2 * (c / N * p ^ 2) +
            (2 * Real.exp 1 + 3) * (∫ u, |φ u|) ^ 2 * ((|p| * P + P ^ 2 / N) / N)) :=
        mul_le_mul_of_nonneg_left (hcore.trans hfin) (by positivity)
    _ = _ := by ring

/-! ### Every height below the resolution -/

/-- The error of all zeros up to height `T = N^θ` at one level `N`, under explicit size conditions
on `N`: `≤ K(C₁ + C₂|y_1|P + C₂P²) c log² N/N^{1−θ}`. -/
theorem norm_sum_ledger_sub_le_of_height {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {E : Finset ℕ}
    (hE : ∀ e ∈ E, 1 ≤ e) {L : ℕ} (hL : ∀ e ∈ E, e ≤ L) (hL1 : (1 : ℝ) ≤ L) (y : ℕ → ℝ) (m : ℕ)
    {θ a : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (ha : a = ((2 * m + 1 : ℕ) : ℝ) - θ * (2 * m + 2))
    {K T₀ : ℝ} (hK : 0 ≤ K) (hT₀ : 3 ≤ T₀)
    (hcount : ∀ T : ℝ, T₀ ≤ T → ∑ ρ ∈ (RHTower.lowZeros_finite T).toFinset,
      (zetaZeroConfig.mult ρ : ℝ) ≤ K * (T * Real.log T ^ 2))
    {C₁ C₂ P : ℝ}
    (hC₁ : C₁ = 2 * (Real.exp 1 + 1) * (∫ u, |φ u|) ^ 2 * poleCoefficient E y ^ 2 /
      (∫ u, φ u ^ 2))
    (hC₂ : C₂ = (2 * Real.exp 1 + 3) * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2))
    (hP : P = packetConstOrder E y m) {c : ℝ} (hc1 : 1 ≤ c) {N : ℕ}
    (hTN : max T₀ (2 * m + 5) ≤ (N : ℝ) ^ θ) (hθN : (N : ℝ) ^ (θ - 1) < 1 / (4 * L))
    (hNL : 4 * (L : ℝ) * (2 * m + 6) + 3 ≤ N)
    (hNa : (2 : ℝ) ^ (2 * m + 2) * (2 * L) ^ (2 * m + 1) ≤ (N : ℝ) ^ a)
    (hcθ : c * (N : ℝ) ^ θ / N < 1 / 4) :
    ‖∑ ρ ∈ (RHTower.lowZeros_finite ((N : ℝ) ^ θ)).toFinset,
      (((Real.log N / c : ℝ) : ℂ) * bulkLedger zetaZeroConfig φ E y c N ρ -
        (zetaZeroConfig.mult ρ : ℂ) * (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) *
          (((poleCoefficient E y ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))))‖ ≤
      K * (C₁ + C₂ * |poleCoefficient E y| * P + C₂ * P ^ 2) *
        (c * Real.log N ^ 2 / (N : ℝ) ^ (1 - θ)) := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hI₁0 : 0 ≤ ∫ u, |φ u| := integral_nonneg fun u => abs_nonneg _
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  have hP0 : 0 ≤ P := hP ▸ packetConstOrder_nonneg E y m
  obtain ⟨T, hTdef⟩ : ∃ T, T = (N : ℝ) ^ θ := ⟨_, rfl⟩
  rw [← hTdef] at hTN hcθ ⊢
  have hTT₀ : T₀ ≤ T := (le_max_left _ _).trans hTN
  have hTm : (2 * m + 5 : ℝ) ≤ T := (le_max_right _ _).trans hTN
  have hT3 : 3 ≤ T := hT₀.trans hTT₀
  have hL0 : (0 : ℝ) ≤ 4 * (L : ℝ) * (2 * m + 6) := by positivity
  have hN0 : (0 : ℝ) < N := by linarith
  have hN2 : 2 ≤ N := by
    have : (2 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hc0 : 0 < c := by linarith
  have hTN4 : T * (4 * L) ≤ N := by
    have hTe : T = (N : ℝ) ^ (θ - 1) * N := by
      rw [hTdef, Real.rpow_sub hN0, Real.rpow_one]; field_simp
    have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * L)).mp hθN
    rw [hTe]
    have h2 : (N : ℝ) ^ (θ - 1) * (4 * L) * N ≤ 1 * N :=
      mul_le_mul_of_nonneg_right h.le hN0.le
    linarith [mul_comm ((N : ℝ) ^ (θ - 1)) (N : ℝ), mul_assoc ((N : ℝ) ^ (θ - 1)) (4 * (L : ℝ)) N,
      mul_assoc ((N : ℝ) ^ (θ - 1)) (N : ℝ) (4 * (L : ℝ)), mul_comm (4 * (L : ℝ)) (N : ℝ)]
  have hcT4 : c * T * 4 ≤ N := by
    have h := (div_lt_iff₀ hN0).mp hcθ
    linarith
  have hTp : T ^ (2 * m + 2) = (N : ℝ) ^ (θ * ((2 * m + 2 : ℕ) : ℝ)) := by
    rw [hTdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
  have hNp : (N : ℝ) ^ (2 * m + 1) = (N : ℝ) ^ (θ * ((2 * m + 2 : ℕ) : ℝ)) * (N : ℝ) ^ a := by
    rw [← Real.rpow_add hN0, ha, ← Real.rpow_natCast]
    congr 1; push_cast; ring
  have hX0 : 0 ≤ (N : ℝ) ^ (θ * ((2 * m + 2 : ℕ) : ℝ)) := by positivity
  have hXN : (T + (2 * m + 5)) ^ (2 * m + 2) ≤ ((N : ℝ) / (2 * L)) ^ (2 * m + 1) := by
    calc (T + (2 * m + 5)) ^ (2 * m + 2) ≤ (2 * T) ^ (2 * m + 2) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = 2 ^ (2 * m + 2) * (N : ℝ) ^ (θ * ((2 * m + 2 : ℕ) : ℝ)) := by rw [mul_pow, hTp]
      _ ≤ (N : ℝ) ^ (θ * ((2 * m + 2 : ℕ) : ℝ)) * (N : ℝ) ^ a / (2 * L) ^ (2 * m + 1) := by
          rw [le_div_iff₀ (by positivity)]
          have h := mul_le_mul_of_nonneg_left hNa hX0
          linarith
      _ = ((N : ℝ) / (2 * L)) ^ (2 * m + 1) := by rw [div_pow, hNp]
  have hper : ∀ ρ ∈ (RHTower.lowZeros_finite T).toFinset,
      ‖((Real.log N / c : ℝ) : ℂ) * bulkLedger zetaZeroConfig φ E y c N ρ -
        (zetaZeroConfig.mult ρ : ℂ) * (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) *
          (((poleCoefficient E y ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ)))‖ ≤
      zetaZeroConfig.mult ρ * (C₁ * (c / N) +
        C₂ * ((|poleCoefficient E y| * P + P ^ 2 / N) / N)) := by
    intro ρ hρ
    have hρ' := (RHTower.lowZeros_finite _).mem_toFinset.mp hρ
    have hnorm := norm_le_of_mem_lowZeros hρ'
    have hNLρ : 2 * L * (‖ρ‖ + (2 * m + 5)) ≤ (N : ℝ) := by
      have h1 : 2 * (L : ℝ) * (‖ρ‖ + (2 * m + 5)) ≤ 2 * L * ((1 + T) + (2 * m + 5)) := by gcongr
      have h2 : 2 * (L : ℝ) * ((1 + T) + (2 * m + 5)) =
          T * (4 * L) / 2 + 4 * (L : ℝ) * (2 * m + 6) / 2 := by ring
      linarith
    have hXρ : (‖ρ‖ + (2 * m + 4)) ^ (2 * m + 2) ≤ ((N : ℝ) / (2 * L)) ^ (2 * m + 1) :=
      le_trans (pow_le_pow_left₀ (by positivity) (by linarith) _) hXN
    have hcNρ : c * (‖ρ‖ + 1) ≤ N := by
      have h1 : c * (‖ρ‖ + 1) ≤ c * ((1 + T) + 1) := by gcongr
      have h2 : c * ((1 + T) + 1) ≤ c * T * 4 := by nlinarith
      linarith
    have h := norm_log_div_mul_bulkLedger_sub_le_order hφ hφsupp hφ2 hE hL y m hρ'.1 hc0 hN2
      hNLρ hXρ hcNρ
    rw [← hC₁, ← hC₂, ← hP] at h
    exact h
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hlogT : Real.log T ^ 2 ≤ Real.log N ^ 2 := by
    have h1 : Real.log T = θ * Real.log N := by rw [hTdef, Real.log_rpow hN0]
    have h2 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have h3 : Real.log T ≤ Real.log N := by
      rw [h1]; exact mul_le_of_le_one_left hlogN hθ1.le
    exact pow_le_pow_left₀ h2 h3 2
  have hB : C₁ * (c / N) + C₂ * ((|poleCoefficient E y| * P + P ^ 2 / N) / N) ≤
      c * (C₁ + C₂ * |poleCoefficient E y| * P + C₂ * P ^ 2) / N := by
    have hN1 : (1 : ℝ) ≤ N := by linarith
    have hP2 : P ^ 2 / N ≤ P ^ 2 := div_le_self (by positivity) hN1
    have h1 : C₂ * ((|poleCoefficient E y| * P + P ^ 2 / N) / N) ≤
        C₂ * ((|poleCoefficient E y| * P + P ^ 2) / N) := by gcongr
    have h2 : C₂ * ((|poleCoefficient E y| * P + P ^ 2) / N) ≤
        c * (C₂ * ((|poleCoefficient E y| * P + P ^ 2) / N)) :=
      le_mul_of_one_le_left (by positivity) hc1
    have e : c * (C₁ + C₂ * |poleCoefficient E y| * P + C₂ * P ^ 2) / N =
        C₁ * (c / N) + c * (C₂ * ((|poleCoefficient E y| * P + P ^ 2) / N)) := by ring
    rw [e]
    linarith
  refine (norm_sum_le _ _).trans ((sum_le_sum hper).trans ?_)
  rw [← sum_mul]
  have hBnn : 0 ≤ C₁ * (c / N) + C₂ * ((|poleCoefficient E y| * P + P ^ 2 / N) / N) := by
    positivity
  have hNθ : (N : ℝ) ^ (1 - θ) = N / T := by rw [hTdef, Real.rpow_sub hN0, Real.rpow_one]
  have hT0 : 0 < T := by linarith
  calc (∑ ρ ∈ (RHTower.lowZeros_finite T).toFinset, (zetaZeroConfig.mult ρ : ℝ)) *
        (C₁ * (c / N) + C₂ * ((|poleCoefficient E y| * P + P ^ 2 / N) / N)) ≤
      (K * (T * Real.log T ^ 2)) * (c * (C₁ + C₂ * |poleCoefficient E y| * P + C₂ * P ^ 2) / N) :=
      mul_le_mul (hcount _ hTT₀) hB hBnn (by positivity)
    _ ≤ (K * (T * Real.log N ^ 2)) *
        (c * (C₁ + C₂ * |poleCoefficient E y| * P + C₂ * P ^ 2) / N) := by gcongr
    _ = K * (C₁ + C₂ * |poleCoefficient E y| * P + C₂ * P ^ 2) *
        (c * Real.log N ^ 2 / (N : ℝ) ^ (1 - θ)) := by
      rw [hNθ]
      field_simp

/-- **Every height below the resolution.** For `0 < θ < 1` and every overlap schedule with
`c_N ≥ 1`, `c_N log² N/N^{1−θ} → 0`, the zeros of height `≤ N^θ` together contribute
`(c_N/log N) κ y_1² (2 + γ − log 4π) + o(c_N/log N)` to the normalized complete form of every
conductor packet. -/
theorem tendsto_sum_bulkLedger_belowResolution {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {E : Finset ℕ}
    (hE : ∀ e ∈ E, 1 ≤ e) (y : ℕ → ℝ) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {c : ℕ → ℝ}
    (hc1 : ∀ N, 1 ≤ c N)
    (hcN : Tendsto (fun N : ℕ => c N * Real.log N ^ 2 / (N : ℝ) ^ (1 - θ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑ ρ ∈ (RHTower.lowZeros_finite ((N : ℝ) ^ θ)).toFinset,
      ((Real.log N / c N : ℝ) : ℂ) * bulkLedger zetaZeroConfig φ E y (c N) N ρ) atTop
      (𝓝 (((((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * poleCoefficient E y ^ 2 *
        RHTower.poleSharpConstant : ℝ) : ℂ))) := by
  obtain ⟨K, T₀, hK, hT₀, hcount⟩ := exists_sum_mult_lowZeros_le
  obtain ⟨L, hLdef⟩ : ∃ L, L = ∑ e ∈ E, e + 1 := ⟨_, rfl⟩
  have hL : ∀ e ∈ E, e ≤ L := fun e he => by
    have := Finset.single_le_sum (f := fun e : ℕ => e) (fun _ _ => Nat.zero_le _) he
    omega
  have hL1 : (1 : ℝ) ≤ L := by
    have : 1 ≤ L := by omega
    exact_mod_cast this
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌈1 / (1 - θ)⌉₊ := ⟨_, rfl⟩
  have hmθ : 1 ≤ (m : ℝ) * (1 - θ) := by
    have h := Nat.le_ceil (1 / (1 - θ))
    rw [← hm, div_le_iff₀ (by linarith)] at h
    exact h
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ((2 * m + 1 : ℕ) : ℝ) - θ * (2 * m + 2) := ⟨_, rfl⟩
  have ha0 : 0 < a := by
    have : a = 2 * ((m : ℝ) * (1 - θ)) + 1 - 2 * θ := by rw [ha]; push_cast; ring
    rw [this]; linarith
  obtain ⟨C₁, hC₁⟩ : ∃ C, C = 2 * (Real.exp 1 + 1) * (∫ u, |φ u|) ^ 2 * poleCoefficient E y ^ 2 /
      (∫ u, φ u ^ 2) := ⟨_, rfl⟩
  obtain ⟨C₂, hC₂⟩ : ∃ C, C = (2 * Real.exp 1 + 3) * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2) :=
    ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ q, q = packetConstOrder E y m := ⟨_, rfl⟩
  have hNat := tendsto_natCast_atTop_atTop (R := ℝ)
  have hT : Tendsto (fun N : ℕ => (N : ℝ) ^ θ) atTop atTop := (tendsto_rpow_atTop hθ0).comp hNat
  have hNa : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop := (tendsto_rpow_atTop ha0).comp hNat
  have hθN : Tendsto (fun N : ℕ => (N : ℝ) ^ (θ - 1)) atTop (𝓝 0) := by
    rw [show θ - 1 = -(1 - θ) by ring]
    exact (tendsto_rpow_neg_atTop (show 0 < 1 - θ by linarith)).comp hNat
  have hcθ : Tendsto (fun N : ℕ => c N * (N : ℝ) ^ θ / N) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun N => by have := hc1 N; positivity) ?_ hcN
    filter_upwards [eventually_ge_atTop 3] with N hN
    have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : (0 : ℝ) < N := by linarith
    have hlog : 1 ≤ Real.log N := by
      rw [Real.le_log_iff_exp_le hN0]
      have := Real.exp_one_lt_d9
      linarith
    have e : c N * (N : ℝ) ^ θ / N = c N / (N : ℝ) ^ (1 - θ) := by
      rw [Real.rpow_sub hN0, Real.rpow_one]; field_simp
    rw [e]
    have hl2 : 1 ≤ Real.log N ^ 2 := by nlinarith
    exact div_le_div_of_nonneg_right (le_mul_of_one_le_right (by linarith [hc1 N]) hl2)
      (by positivity)
  have hbound : Tendsto (fun N : ℕ => K * (C₁ + C₂ * |poleCoefficient E y| * P + C₂ * P ^ 2) *
      (c N * Real.log N ^ 2 / (N : ℝ) ^ (1 - θ))) atTop (𝓝 0) := by
    simpa using hcN.const_mul (K * (C₁ + C₂ * |poleCoefficient E y| * P + C₂ * P ^ 2))
  have hL4 : (0 : ℝ) < 1 / (4 * L) := by positivity
  have hev := (((((hT.eventually (eventually_ge_atTop (max T₀ (2 * m + 5)))).and
    (hθN.eventually (gt_mem_nhds hL4))).and
    (eventually_ge_atTop (⌈4 * (L : ℝ) * (2 * m + 6)⌉₊ + 3))).and
    (hNa.eventually (eventually_ge_atTop ((2 : ℝ) ^ (2 * m + 2) * (2 * L) ^ (2 * m + 1))))).and
    (hcθ.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))))
  have htarget := (tendsto_sum_lowZeros_mult_div hT).const_mul
    ((((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) * ((poleCoefficient E y ^ 2 : ℝ) : ℂ))
  obtain ⟨err, herr⟩ : ∃ f : ℕ → ℂ, f = fun (N : ℕ) =>
      ∑ ρ ∈ (RHTower.lowZeros_finite ((N : ℝ) ^ θ)).toFinset,
      (((Real.log N / c N : ℝ) : ℂ) * bulkLedger zetaZeroConfig φ E y (c N) N ρ -
        (zetaZeroConfig.mult ρ : ℂ) * (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) *
          (((poleCoefficient E y ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ)))) := ⟨_, rfl⟩
  have herr0 : Tendsto err atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hev] with N ⟨⟨⟨⟨hTN, hθN'⟩, hNL⟩, hNa'⟩, hcθ'⟩
    have hNL' : 4 * (L : ℝ) * (2 * m + 6) + 3 ≤ N := by
      have h1 := Nat.le_ceil (4 * (L : ℝ) * (2 * m + 6))
      have h2 : ((⌈4 * (L : ℝ) * (2 * m + 6)⌉₊ + 3 : ℕ) : ℝ) ≤ N := by exact_mod_cast hNL
      push_cast at h2; linarith
    rw [herr]
    exact norm_sum_ledger_sub_le_of_height hφ hφsupp hφ2 hE hL hL1 y m hθ0 hθ1 ha hK hT₀ hcount
      hC₁ hC₂ hP (hc1 N) hTN hθN' hNL' hNa' hcθ'
  have hsplit : ∀ N : ℕ, ∑ ρ ∈ (RHTower.lowZeros_finite ((N : ℝ) ^ θ)).toFinset,
      ((Real.log N / c N : ℝ) : ℂ) * bulkLedger zetaZeroConfig φ E y (c N) N ρ =
      (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) * ((poleCoefficient E y ^ 2 : ℝ) : ℂ) *
        ∑ ρ ∈ (RHTower.lowZeros_finite ((N : ℝ) ^ θ)).toFinset,
          (zetaZeroConfig.mult ρ : ℂ) / (ρ * (1 - ρ)) + err N := by
    intro N
    rw [herr, Finset.mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun ρ _ => ?_
    ring
  have hlim := htarget.add herr0
  rw [add_zero, tsum_mult_div_zero_mul_one_sub_eq] at hlim
  have hval : (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) * ((poleCoefficient E y ^ 2 : ℝ) : ℂ) *
      (RHTower.poleSharpConstant : ℂ) = ((((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * poleCoefficient E y ^ 2 *
        RHTower.poleSharpConstant : ℝ) : ℂ) := by push_cast; ring
  rw [hval] at hlim
  exact hlim.congr fun N => (hsplit N).symm

/-- **Pole-free packets are blind below the resolution height.** For `0 < θ < 1`,
`c_N log² N/N^{1−θ} → 0` and `y_1 = 0`, the zeros of height `≤ N^θ` contribute `o(c_N/log N)`. -/
theorem tendsto_sum_bulkLedger_belowResolution_poleFree {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {E : Finset ℕ}
    (hE : ∀ e ∈ E, 1 ≤ e) {y : ℕ → ℝ} (hpole : poleCoefficient E y = 0) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    (hcN : Tendsto (fun N : ℕ => c N * Real.log N ^ 2 / (N : ℝ) ^ (1 - θ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑ ρ ∈ (RHTower.lowZeros_finite ((N : ℝ) ^ θ)).toFinset,
      ((Real.log N / c N : ℝ) : ℂ) * bulkLedger zetaZeroConfig φ E y (c N) N ρ) atTop (𝓝 0) := by
  have h := tendsto_sum_bulkLedger_belowResolution hφ hφsupp hφ2 hE y hθ0 hθ1 hc1 hcN
  rw [hpole] at h
  simpa using h

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
