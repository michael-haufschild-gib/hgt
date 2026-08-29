import GaloisForLFunctions.RHTower.Sieve.HarmonicLogWindowThirdMoment

/-!
# Harmonic logarithmic window moments at every order

The Barban--Vehov / Selberg diagonal analysis needs the asymptotic

`∑_{d ≤ X} (log d)^m / d = (log X)^{m+1}/(m+1) + O_m(1)`

for **every** natural `m`, not only for the orders `0,1,2,3` treated separately elsewhere in this
directory.  The single missing ingredient is antitonicity of the Abel weight `(log t)^m / t`, which
holds beyond `exp m`; the natural threshold `4^m` is used because `log 4 > 1`.

Everything else is the already-general sum--integral comparison
`abs_harmonicLogWindowMoment_sub_integral_le`.
-/

open Finset MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- `log 4 > 1`, the elementary fact making `4 ^ m` an admissible antitonicity threshold. -/
theorem one_le_log_four : (1 : ℝ) ≤ Real.log 4 := by
  have hexp : Real.exp 1 < 4 :=
    lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h := (Real.lt_log_iff_exp_lt (show (0 : ℝ) < 4 by norm_num)).2 hexp
  linarith

/-- Beyond `4 ^ m` the logarithm exceeds `m`. -/
theorem le_log_of_pow_four_le {m : ℕ} {x : ℝ} (hx : ((4 ^ m : ℕ) : ℝ) ≤ x) :
    (m : ℝ) ≤ Real.log x := by
  have hpow : ((4 ^ m : ℕ) : ℝ) = (4 : ℝ) ^ m := by push_cast; ring
  have hxpos : (0 : ℝ) < (4 : ℝ) ^ m := by positivity
  have hmono : Real.log ((4 : ℝ) ^ m) ≤ Real.log x := by
    refine Real.log_le_log hxpos ?_
    rw [← hpow]; exact hx
  rw [Real.log_pow] at hmono
  have hm : (m : ℝ) * 1 ≤ (m : ℝ) * Real.log 4 :=
    mul_le_mul_of_nonneg_left one_le_log_four (Nat.cast_nonneg m)
  linarith

/-- **The Abel weight `(log t)^m / t` is antitone beyond `4 ^ m`.** -/
theorem antitoneOn_logPowDivId_pow_four (m : ℕ) :
    AntitoneOn (RHTower.logPowDivId m) (Set.Ici ((4 ^ m : ℕ) : ℝ)) := by
  have hthr : (1 : ℝ) ≤ ((4 ^ m : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_pow m 4 (by norm_num)
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · intro x hx
    have hxge : ((4 ^ m : ℕ) : ℝ) ≤ x := hx
    exact (RHTower.hasDerivAt_logPowDivId m
      (by linarith)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hxge : ((4 ^ m : ℕ) : ℝ) < x := hx
    exact (RHTower.hasDerivAt_logPowDivId m
      (by linarith)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hxge : ((4 ^ m : ℕ) : ℝ) ≤ x := le_of_lt hx
    have hxpos : (0 : ℝ) < x := by linarith
    have hlog : (m : ℝ) ≤ Real.log x := le_log_of_pow_four_le hxge
    have hlognn : (0 : ℝ) ≤ Real.log x :=
      le_trans (Nat.cast_nonneg m) hlog
    rw [(RHTower.hasDerivAt_logPowDivId m hxpos).deriv, RHTower.derivLogPowDivId]
    refine div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg x)
    match m with
    | 0 => norm_num
    | (k + 1) =>
        have hk : ((k : ℝ) + 1) ≤ Real.log x := by exact_mod_cast hlog
        have hpow : (0 : ℝ) ≤ Real.log x ^ k := pow_nonneg hlognn k
        have hmul : ((k : ℝ) + 1) * Real.log x ^ k ≤ Real.log x * Real.log x ^ k :=
          mul_le_mul_of_nonneg_right hk hpow
        have hcast : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by push_cast; ring
        have hsub : (k + 1) - 1 = k := by omega
        rw [hcast, hsub, pow_succ]
        nlinarith [hmul]

/-- Sum--integral comparison for the `m`-th harmonic logarithmic window moment, at every order. -/
theorem abs_harmonicLogWindowMoment_sub_primitive_le (m : ℕ)
    {A B : ℕ} (hA : 4 ^ m ≤ A) (hAB : A ≤ B) :
    |harmonicLogWindowMoment m A B -
        (harmonicLogMomentPrimitive m ((B + 1 : ℕ) : ℝ) -
          harmonicLogMomentPrimitive m ((A + 1 : ℕ) : ℝ))| ≤
      RHTower.logPowDivId m ((A + 1 : ℕ) : ℝ) := by
  have hstep : (4 ^ m : ℕ) ≤ A + 1 := le_trans hA (Nat.le_succ A)
  have hcast : ((4 ^ m : ℕ) : ℝ) ≤ ((A + 1 : ℕ) : ℝ) := by exact_mod_cast hstep
  have hanti : AntitoneOn (RHTower.logPowDivId m) (Set.Ici ((A + 1 : ℕ) : ℝ)) := by
    refine (antitoneOn_logPowDivId_pow_four m).mono ?_
    intro x hx
    have hxge : ((A + 1 : ℕ) : ℝ) ≤ x := hx
    exact le_trans hcast hxge
  have h := abs_harmonicLogWindowMoment_sub_integral_le m hAB hanti
  have hab : (((A + 1 : ℕ) : ℝ)) ≤ (((B + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.add_le_add_right hAB 1
  rw [intervalIntegral_logPowDivId m (by positivity) hab] at h
  refine h.trans ?_
  have hBone : (1 : ℝ) ≤ ((B + 1 : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
    push_cast
    linarith
  have hnn : 0 ≤ RHTower.logPowDivId m ((B + 1 : ℕ) : ℝ) := by
    rw [RHTower.logPowDivId]
    exact div_nonneg (pow_nonneg (Real.log_nonneg hBone) m) (by linarith)
  linarith

/-- **Every harmonic logarithmic prefix differs from its main term by one fixed constant.** -/
theorem exists_abs_harmonicLogWindowMoment_zero_sub_primitive_le (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 4 ^ m ≤ N →
      |harmonicLogWindowMoment m 0 N -
          harmonicLogMomentPrimitive m ((N + 1 : ℕ) : ℝ)| ≤ C := by
  refine ⟨|harmonicLogWindowMoment m 0 (4 ^ m) -
      harmonicLogMomentPrimitive m (((4 ^ m : ℕ) + 1 : ℕ) : ℝ)| +
      RHTower.logPowDivId m (((4 ^ m : ℕ) + 1 : ℕ) : ℝ), ?_, ?_⟩
  · have hone : (1 : ℝ) ≤ (((4 ^ m : ℕ) + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left 1 (4 ^ m)
    have hnn : 0 ≤ RHTower.logPowDivId m (((4 ^ m : ℕ) + 1 : ℕ) : ℝ) := by
      rw [RHTower.logPowDivId]
      exact div_nonneg (pow_nonneg (Real.log_nonneg hone) m) (by linarith)
    exact add_nonneg (abs_nonneg _) hnn
  · intro N hN
    have hsplit := harmonicLogWindowMoment_add m (A := 0) (B := 4 ^ m) (C := N)
      (Nat.zero_le _) hN
    have htail := abs_harmonicLogWindowMoment_sub_primitive_le m
      (A := 4 ^ m) (B := N) le_rfl hN
    calc
      |harmonicLogWindowMoment m 0 N -
          harmonicLogMomentPrimitive m ((N + 1 : ℕ) : ℝ)|
          = |(harmonicLogWindowMoment m 0 (4 ^ m) -
              harmonicLogMomentPrimitive m (((4 ^ m : ℕ) + 1 : ℕ) : ℝ)) +
            (harmonicLogWindowMoment m (4 ^ m) N -
              (harmonicLogMomentPrimitive m ((N + 1 : ℕ) : ℝ) -
                harmonicLogMomentPrimitive m (((4 ^ m : ℕ) + 1 : ℕ) : ℝ)))| := by
            rw [← hsplit]
            ring_nf
      _ ≤ |harmonicLogWindowMoment m 0 (4 ^ m) -
              harmonicLogMomentPrimitive m (((4 ^ m : ℕ) + 1 : ℕ) : ℝ)| +
            |harmonicLogWindowMoment m (4 ^ m) N -
              (harmonicLogMomentPrimitive m ((N + 1 : ℕ) : ℝ) -
                harmonicLogMomentPrimitive m (((4 ^ m : ℕ) + 1 : ℕ) : ℝ))| :=
          abs_add_le _ _
      _ ≤ _ := add_le_add le_rfl htail

/-- **The `m`-th harmonic logarithmic moment at a fixed dilation has coefficient `1/(m+1)`.** -/
theorem tendsto_harmonicLogWindowMoment_natDiv_div_log_pow
    (m : ℕ) {c : ℕ} (hc : 0 < c) :
    Tendsto (fun N : ℕ =>
      harmonicLogWindowMoment m 0 (N / c) / Real.log N ^ (m + 1))
      atTop (𝓝 (1 / ((m : ℝ) + 1))) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_abs_harmonicLogWindowMoment_zero_sub_primitive_le m
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hscale : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (m + 1)) atTop atTop :=
    (tendsto_pow_atTop (n := m + 1) (by omega)).comp hlog
  have hdiv : ∀ N : ℕ, 4 ^ m * c ≤ N → 4 ^ m ≤ N / c := by
    intro N hN
    exact (Nat.le_div_iff_mul_le hc).2 hN
  have herr : Tendsto (fun N : ℕ =>
      (harmonicLogWindowMoment m 0 (N / c) -
        harmonicLogMomentPrimitive m ((N / c + 1 : ℕ) : ℝ)) /
          Real.log N ^ (m + 1)) atTop (𝓝 0) := by
    have hmaj : Tendsto (fun N : ℕ => C / Real.log N ^ (m + 1)) atTop (𝓝 0) :=
      hscale.const_div_atTop C
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop (4 ^ m * c)]
      with N hN2 hNc
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hlogN (m + 1))]
    exact div_le_div_of_nonneg_right (hbound (N / c) (hdiv N hNc))
      (pow_nonneg hlogN.le (m + 1))
  have hratio := tendsto_log_natDiv_add_one_div_log_one hc
  have hmain : Tendsto (fun N : ℕ =>
      harmonicLogMomentPrimitive m ((N / c + 1 : ℕ) : ℝ) /
        Real.log N ^ (m + 1)) atTop (𝓝 (1 / ((m : ℝ) + 1))) := by
    have h := (hratio.pow (m + 1)).div_const ((m : ℝ) + 1)
    rw [one_pow] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlogN : Real.log (N : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hN)).ne'
    rw [harmonicLogMomentPrimitive, div_pow, div_div, div_div]
    ring_nf
  have hadd := herr.add hmain
  rw [zero_add] at hadd
  refine hadd.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  ring

end

end RHTower.Sieve
