import GaloisForLFunctions.RHTower.CommonProfileAnchorResponseMobius
import GaloisForLFunctions.RHTower.PrimeSquareMobiusDensityFracture
import GaloisForLFunctions.BiScaleUncertainty.SieveCoordinateSupNorm
import GaloisForLFunctions.RHTower.ZeroLatticeDepthNyquistLaw
import GaloisForLFunctions.TransThresholdPairCorrelation.ParitySensitiveRamanujanStabilizerTransfer

/-!
# Exact Poisson rows for the odd-conductor stabilizer

For a compactly supported C² window, the complete signed Ramanujan row equals
its spatial dual minus the zero-lag diagonal. Möbius inversion identifies the
dual with primitive lattice samples, so nonnegative windows give nonnegative
corrections. Exact negative cancellation holds precisely when all active
primitive samples vanish; the support horizon `qb ≤ πm` is sufficient,
including equality at the boundary.
-/

noncomputable section
open Complex MeasureTheory Real Filter Topology
open Zeta23

namespace GaloisForLFunctions.TransThresholdPairCorrelation

private theorem paperFT_re_eq_cosTransform {Ω : ℝ → ℝ}
    (hΩ : Continuous Ω) (hcpt : HasCompactSupport Ω) (θ : ℝ) :
    (paperFT (fun u => (Ω u : ℂ)) (θ : ℂ)).re = cosTransform Ω θ := by
  have hc : Integrable (fun u => Ω u * Real.cos (u * θ)) :=
    (hΩ.mul (by fun_prop)).integrable_of_hasCompactSupport hcpt.mul_right
  have hs : Integrable (fun u => Ω u * Real.sin (u * θ)) :=
    (hΩ.mul (by fun_prop)).integrable_of_hasCompactSupport hcpt.mul_right
  have he (u : ℝ) : (Ω u : ℂ) * Complex.exp (I * (θ : ℂ) * (u : ℂ)) =
      ((Ω u * Real.cos (u * θ) : ℝ) : ℂ) + I * ((Ω u * Real.sin (u * θ) : ℝ) : ℂ) := by
    rw [show I * (θ : ℂ) * (u : ℂ) = ((u * θ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  have hadd : (∫ u : ℝ, ((Ω u * Real.cos (u * θ) : ℝ) : ℂ) +
      I * ((Ω u * Real.sin (u * θ) : ℝ) : ℂ)) =
      (∫ u : ℝ, ((Ω u * Real.cos (u * θ) : ℝ) : ℂ)) +
        ∫ u : ℝ, I * ((Ω u * Real.sin (u * θ) : ℝ) : ℂ) :=
    integral_add hc.ofReal (hs.ofReal.const_mul I)
  unfold paperFT cosTransform
  simp_rw [he]
  rw [hadd, integral_const_mul,
    integral_complex_ofReal, integral_complex_ofReal]
  simp

private theorem cosTransform_neg (Ω : ℝ → ℝ) (θ : ℝ) :
    cosTransform Ω (-θ) = cosTransform Ω θ := by
  simp only [cosTransform, mul_neg, Real.cos_neg]

private theorem hasSum_cosTransform_positive_lattice {Ω : ℝ → ℝ} {A L : ℝ}
    (hL : 0 < L) (hΩ : ContDiff ℝ 2 Ω)
    (hsupp : ∀ u, Ω u ≠ 0 → |u| ≤ A) :
    HasSum (fun n : ℕ => cosTransform Ω (((n : ℝ) + 1) * (2 * π / L)))
      ((L * (∑' k : ℤ, Ω ((k : ℝ) * L)) - cosTransform Ω 0) / 2) := by
  have hcpt : HasCompactSupport Ω := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (-A) A) isCompact_Icc ?_
    intro u hu
    exact abs_le.mp (hsupp u hu)
  have hC : ContDiff ℝ 2 (fun u => (Ω u : ℂ)) := Complex.ofRealCLM.contDiff.comp hΩ
  have hsp : ∀ u, (Ω u : ℂ) ≠ 0 → |u| ≤ A := by
    intro u hu
    apply hsupp u
    simpa only [ne_eq, Complex.ofReal_eq_zero] using hu
  have hFT := RHTower.hasSum_paperFT_lattice hL hC hsp
  have hr := Complex.reCLM.hasSum hFT
  change HasSum (fun k : ℤ => (paperFT (fun u => (Ω u : ℂ))
    (((k : ℝ) * (2 * π / L) : ℝ) : ℂ)).re)
    (((L : ℂ) * ∑' k : ℤ, (Ω ((k : ℝ) * L) : ℂ)).re) at hr
  simp only [paperFT_re_eq_cosTransform hΩ.continuous hcpt,
    ← Complex.ofReal_tsum, ← Complex.ofReal_mul, Complex.ofReal_re] at hr
  have hn := hr.nat_add_neg
  rw [← hasSum_nat_add_iff' 1] at hn
  simp only [Finset.sum_range_one, Int.cast_natCast, Int.cast_neg,
    Int.cast_add, Int.cast_one, Nat.cast_add, Nat.cast_one, Nat.cast_zero, Int.cast_zero, zero_mul,
    neg_mul, cosTransform_neg, ← two_mul] at hn
  have hh := hn.div_const 2
  have hfun : (fun n : ℕ => 2 * cosTransform Ω (((n : ℝ) + 1) * (2 * π / L)) / 2) =
      (fun n : ℕ => cosTransform Ω (((n : ℝ) + 1) * (2 * π / L))) := by
    funext n
    ring
  have hval : (L * (∑' k : ℤ, Ω ((k : ℝ) * L)) + cosTransform Ω 0 - 2 * cosTransform Ω 0) / 2 =
      (L * (∑' k : ℤ, Ω ((k : ℝ) * L)) - cosTransform Ω 0) / 2 := by ring
  rw [hfun, hval] at hh
  exact hh

private theorem sum_Icc_one_eq_shifted_range (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, f n) = ∑ n ∈ Finset.range N, f (n + 1) := by
  symm
  apply Finset.sum_bij (fun n _ => n + 1)
  · intro n hn
    simp only [Finset.mem_range] at hn
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro a _ b _ he
    omega
  · intro b hb
    have hb := Finset.mem_Icc.mp hb
    exact ⟨b - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro n _
    rfl

private theorem tendsto_Icc_of_positive_hasSum {f : ℕ → ℝ} {S : ℝ}
    (h : HasSum (fun n : ℕ => f (n + 1)) S) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n) atTop (𝓝 S) := by
  simpa only [sum_Icc_one_eq_shifted_range] using h.tendsto_sum_nat

private theorem sum_evenShift_ramanujan_divisor {q : ℕ} (hq : q % 2 = 1)
    (F : ℕ → ℝ) (R : ℕ) :
    (∑ r ∈ Finset.Icc 1 R,
      GaloisForLFunctions.BezoutValuationIncidence.ramanujanLagCoefficient q (2 * r) * F r) =
      ∑ d ∈ q.divisors,
        GaloisForLFunctions.BezoutValuationIncidence.moebiusReal (q / d) * (d : ℝ) *
          ∑ r ∈ Finset.Icc 1 (R / d), F (d * r) := by
  simp only [ramanujanLagCoefficient_odd_two_mul hq]
  simp only [GaloisForLFunctions.BezoutValuationIncidence.ramanujanLagCoefficient,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  rw [← RHTower.sum_Icc_dvd_reindex d R hd0 F, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> ring

private theorem tendsto_nat_div_atTop {d : ℕ} (hd : 0 < d) :
    Tendsto (fun R : ℕ => R / d) atTop atTop := by
  refine tendsto_atTop.2 fun n => ?_
  filter_upwards [eventually_ge_atTop (n * d)] with R hR
  exact (Nat.le_div_iff_mul_le hd).mpr hR

/-- The spatial dual of one odd Ramanujan conductor. -/
def ramanujanSpatialDual (q : ℕ) (Ω : ℝ → ℝ) (m : ℝ) : ℝ :=
  ∑ d ∈ q.divisors,
    GaloisForLFunctions.BezoutValuationIncidence.moebiusReal (q / d) *
      (∑' k : ℤ, Ω ((k : ℝ) * (π * m / (d : ℝ))))

private theorem hasSum_cosTransform_multiples {Ω : ℝ → ℝ} {A m : ℝ}
    (hm : 0 < m) (hΩ : ContDiff ℝ 2 Ω) (hsupp : ∀ u, Ω u ≠ 0 → |u| ≤ A)
    {d : ℕ} (hd : 0 < d) :
    HasSum (fun n : ℕ => cosTransform Ω (((2 * (d * (n + 1)) : ℕ) : ℝ) / m))
      (((π * m / (d : ℝ)) * (∑' k : ℤ, Ω ((k : ℝ) * (π * m / (d : ℝ)))) -
        cosTransform Ω 0) / 2) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h := hasSum_cosTransform_positive_lattice (L := π * m / d) (by positivity) hΩ hsupp
  have he : (fun n : ℕ => cosTransform Ω (((n : ℝ) + 1) * (2 * π / (π * m / d)))) =
      (fun n : ℕ => cosTransform Ω (((2 * (d * (n + 1)) : ℕ) : ℝ) / m)) := by
    funext n
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero, hm.ne', hdR.ne']
  rw [he] at h
  exact h

private theorem moebius_divisor_totient (q : ℕ) (hq : 1 ≤ q) :
    (∑ d ∈ q.divisors,
      GaloisForLFunctions.BezoutValuationIncidence.moebiusReal (q / d) * (d : ℝ)) =
      (q.totient : ℝ) := by
  have h := ramanujanLagCoefficient_of_dvd (q := q) (h := 0) hq (dvd_zero q)
  simpa only [GaloisForLFunctions.BezoutValuationIncidence.ramanujanLagCoefficient,
    dvd_zero, ite_true] using h

/-- The complete signed odd-conductor row equals its finite spatial dual minus
its zero-lag diagonal. Compact C² support ensures absolute summability. -/
theorem ramanujan_evenShift_hasSum_dual {Ω : ℝ → ℝ} {A m : ℝ} {q : ℕ}
    (hm : 0 < m) (hΩ : ContDiff ℝ 2 Ω) (hsupp : ∀ u, Ω u ≠ 0 → |u| ≤ A)
    (hq : q % 2 = 1) :
    HasSum (fun n : ℕ =>
      GaloisForLFunctions.BezoutValuationIncidence.ramanujanLagCoefficient q (2 * (n + 1)) *
        cosTransform Ω (((2 * (n + 1) : ℕ) : ℝ) / m))
      ((π * m * ramanujanSpatialDual q Ω m - (q.totient : ℝ) * cosTransform Ω 0) / 2) := by
  let F : ℕ → ℝ := fun r => cosTransform Ω (((2 * r : ℕ) : ℝ) / m)
  have hF : Summable (fun n : ℕ => F (n + 1)) := by
    simpa only [Nat.one_mul] using (hasSum_cosTransform_multiples hm hΩ hsupp (d := 1) (by omega)).summable
  have hrow : Summable (fun n : ℕ =>
      GaloisForLFunctions.BezoutValuationIncidence.ramanujanLagCoefficient q (2 * (n + 1)) *
        F (n + 1)) := by
    apply (hF.norm.mul_left (q.totient : ℝ)).of_norm_bounded
    intro n
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (GaloisForLFunctions.BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient q _)
      (norm_nonneg _)
  have hlim (d : ℕ) (hd : d ∈ q.divisors) :
      Tendsto (fun R : ℕ =>
        GaloisForLFunctions.BezoutValuationIncidence.moebiusReal (q / d) * (d : ℝ) *
          ∑ r ∈ Finset.Icc 1 (R / d), F (d * r)) atTop
        (𝓝 (GaloisForLFunctions.BezoutValuationIncidence.moebiusReal (q / d) * (d : ℝ) *
          (((π * m / (d : ℝ)) * (∑' k : ℤ, Ω ((k : ℝ) * (π * m / (d : ℝ)))) -
            cosTransform Ω 0) / 2))) := by
    have hd0 := Nat.pos_of_mem_divisors hd
    have h := tendsto_Icc_of_positive_hasSum (f := fun r => F (d * r))
      (hasSum_cosTransform_multiples hm hΩ hsupp hd0)
    exact (h.comp (tendsto_nat_div_atTop hd0)).const_mul _
  have hsum := tendsto_finsetSum q.divisors hlim
  have hval : (∑ d ∈ q.divisors,
        GaloisForLFunctions.BezoutValuationIncidence.moebiusReal (q / d) * (d : ℝ) *
          (((π * m / (d : ℝ)) * (∑' k : ℤ, Ω ((k : ℝ) * (π * m / (d : ℝ)))) -
            cosTransform Ω 0) / 2)) =
      (π * m * ramanujanSpatialDual q Ω m - (q.totient : ℝ) * cosTransform Ω 0) / 2 := by
    calc
      _ = ∑ d ∈ q.divisors,
          (π * m * (GaloisForLFunctions.BezoutValuationIncidence.moebiusReal (q / d) *
              (∑' k : ℤ, Ω ((k : ℝ) * (π * m / (d : ℝ))))) -
            (GaloisForLFunctions.BezoutValuationIncidence.moebiusReal (q / d) * (d : ℝ)) *
              cosTransform Ω 0) / 2 := by
        refine Finset.sum_congr rfl fun d hd => ?_
        have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
        field_simp [hdR]
      _ = _ := by
        rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
          moebius_divisor_totient q (by omega)]
        rfl
  rw [hval] at hsum
  have hsum' : Tendsto (fun R : ℕ =>
      ∑ r ∈ Finset.Icc 1 R,
        GaloisForLFunctions.BezoutValuationIncidence.ramanujanLagCoefficient q (2 * r) * F r)
      atTop (𝓝 ((π * m * ramanujanSpatialDual q Ω m -
        (q.totient : ℝ) * cosTransform Ω 0) / 2)) := by
    apply hsum.congr'
    exact Eventually.of_forall fun R => (sum_evenShift_ramanujan_divisor hq F R).symm
  have hnatural := tendsto_Icc_of_positive_hasSum
    (f := fun r => GaloisForLFunctions.BezoutValuationIncidence.ramanujanLagCoefficient q (2 * r) * F r)
    hrow.hasSum
  have he := tendsto_nhds_unique hnatural hsum'
  rw [← he]
  exact hrow.hasSum


/-- The full spatial correction for the finite odd-conductor stabilizer. -/
def stabilizerSpatialDual (Q : ℕ) (Ω : ℝ → ℝ) (m : ℝ) : ℝ :=
  ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q % 2 = 1),
    (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) * ramanujanSpatialDual q Ω m

/-- The absolutely convergent complete linear row of the parity stabilizer. -/
def stabilizerLinearRow (Q : ℕ) (Ω : ℝ → ℝ) (m : ℝ) : ℝ :=
  ∑' n : ℕ, parityStabilizerWeight Q (2 * (n + 1)) *
    cosTransform Ω (((2 * (n + 1) : ℕ) : ℝ) / m)

/-- Exact Poisson decomposition at a fixed conductor cutoff: the signed row
is its spatial correction minus the odd reciprocal-totient diagonal. -/
theorem parityStabilizer_hasSum_dual {Ω : ℝ → ℝ} {A m : ℝ} (Q : ℕ)
    (hm : 0 < m) (hΩ : ContDiff ℝ 2 Ω) (hsupp : ∀ u, Ω u ≠ 0 → |u| ≤ A) :
    HasSum (fun n : ℕ => parityStabilizerWeight Q (2 * (n + 1)) *
      cosTransform Ω (((2 * (n + 1) : ℕ) : ℝ) / m))
      (π * m * stabilizerSpatialDual Q Ω m - cosTransform Ω 0 *
        ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q % 2 = 1),
          RHTower.Sieve.sqfreeTotientInv q) := by
  let s := (Finset.Icc 1 Q).filter (fun q => q % 2 = 1)
  have hqsum (q : ℕ) (hq : q ∈ s) :=
    (ramanujan_evenShift_hasSum_dual hm hΩ hsupp (Finset.mem_filter.mp hq).2).mul_left
      (2 * (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)))
  have h := hasSum_sum hqsum
  have hf : (fun n : ℕ => ∑ q ∈ s,
      2 * (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
        (GaloisForLFunctions.BezoutValuationIncidence.ramanujanLagCoefficient q (2 * (n + 1)) *
          cosTransform Ω (((2 * (n + 1) : ℕ) : ℝ) / m))) =
      (fun n : ℕ => parityStabilizerWeight Q (2 * (n + 1)) *
        cosTransform Ω (((2 * (n + 1) : ℕ) : ℝ) / m)) := by
    funext n
    simp only [parityStabilizerWeight, Finset.mul_sum, Finset.sum_mul, s, mul_assoc]
  have hv : (∑ q ∈ s,
      2 * (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
        ((π * m * ramanujanSpatialDual q Ω m - (q.totient : ℝ) * cosTransform Ω 0) / 2)) =
      π * m * stabilizerSpatialDual Q Ω m - cosTransform Ω 0 *
        ∑ q ∈ s, RHTower.Sieve.sqfreeTotientInv q := by
    calc _ = ∑ q ∈ s,
        (π * m * ((RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
          ramanujanSpatialDual q Ω m) - cosTransform Ω 0 * RHTower.Sieve.sqfreeTotientInv q) := by
          refine Finset.sum_congr rfl fun q hq => ?_
          have hq0 : 0 < q := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
          have hp : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq0).ne'
          field_simp [hp]
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; rfl
  rw [hf, hv] at h
  exact h

/-- The complete signed row retains the spatial dual for a fixed cutoff. -/
theorem stabilizerLinearRow_eq_dual {Ω : ℝ → ℝ} {A m : ℝ} (Q : ℕ)
    (hm : 0 < m) (hΩ : ContDiff ℝ 2 Ω) (hsupp : ∀ u, Ω u ≠ 0 → |u| ≤ A) :
    stabilizerLinearRow Q Ω m = π * m * stabilizerSpatialDual Q Ω m - cosTransform Ω 0 *
      ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q % 2 = 1),
        RHTower.Sieve.sqfreeTotientInv q :=
  (parityStabilizer_hasSum_dual Q hm hΩ hsupp).tsum_eq

private theorem window_right_endpoint_zero {Ω : ℝ → ℝ} {a b : ℝ}
    (hcont : Continuous Ω) (hsupp : ∀ u, u ∉ Set.Icc a b → Ω u = 0) : Ω b = 0 := by
  have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hseq : Tendsto (fun n : ℕ => b + 1 / ((n : ℝ) + 1)) atTop (𝓝 b) := by
    simpa using tendsto_const_nhds.add h1
  have hlim := hcont.continuousAt.tendsto.comp hseq
  have he : (fun n : ℕ => Ω (b + 1 / ((n : ℝ) + 1))) = fun _ => 0 := by
    funext n
    apply hsupp
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    simp only [Set.mem_Icc]
    intro h
    linarith [h.2]
  rw [Function.comp_def, he] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

private theorem window_lattice_zero {Ω : ℝ → ℝ} {a b L : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbL : b ≤ L) (hcont : Continuous Ω)
    (hsupp : ∀ u, u ∉ Set.Icc a b → Ω u = 0) (k : ℤ) : Ω ((k : ℝ) * L) = 0 := by
  have hL : 0 < L := lt_of_lt_of_le (lt_of_lt_of_le ha hab) hbL
  by_cases hk : k ≤ 0
  · apply hsupp
    have hkR : (k : ℝ) ≤ 0 := by exact_mod_cast hk
    have hz := mul_nonpos_of_nonpos_of_nonneg hkR hL.le
    simp only [Set.mem_Icc]
    intro h
    linarith [h.1]
  · have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have hb : b ≤ (k : ℝ) * L := hbL.trans (by nlinarith)
    rcases hb.eq_or_lt with he | he
    · rw [← he]
      exact window_right_endpoint_zero hcont hsupp
    · apply hsupp
      simp only [Set.mem_Icc]
      intro h
      linarith [h.2]

/-- The spatial dual vanishes through the exact support horizon `qb ≤ πm`.
Continuity includes equality at the boundary. -/
theorem ramanujanSpatialDual_eq_zero_of_horizon {Ω : ℝ → ℝ} {a b m : ℝ} {q : ℕ}
    (ha : 0 < a) (hab : a ≤ b) (horizon : (q : ℝ) * b ≤ π * m)
    (hcont : Continuous Ω) (hsupp : ∀ u, u ∉ Set.Icc a b → Ω u = 0) :
    ramanujanSpatialDual q Ω m = 0 := by
  apply Finset.sum_eq_zero
  intro d hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  have hdq : (d : ℝ) ≤ q := by exact_mod_cast Nat.divisor_le hd
  have hbL : b ≤ π * m / d := by
    rw [le_div_iff₀ hd0]
    calc b * (d : ℝ) = d * b := mul_comm _ _
         _ ≤ q * b := mul_le_mul_of_nonneg_right hdq (le_trans ha.le hab)
         _ ≤ π * m := horizon
  simp only [window_lattice_zero ha hab hbL hcont hsupp, tsum_zero, mul_zero]

/-- A fixed odd-conductor packet has no spatial correction when its largest
conductor lies within the support horizon. -/
theorem stabilizerSpatialDual_eq_zero_of_horizon {Ω : ℝ → ℝ} {a b m : ℝ} (Q : ℕ)
    (ha : 0 < a) (hab : a ≤ b) (horizon : (Q : ℝ) * b ≤ π * m)
    (hcont : Continuous Ω) (hsupp : ∀ u, u ∉ Set.Icc a b → Ω u = 0) :
    stabilizerSpatialDual Q Ω m = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  have hqQ : (q : ℝ) ≤ Q := by
    exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2
  rw [ramanujanSpatialDual_eq_zero_of_horizon ha hab
    ((mul_le_mul_of_nonneg_right hqQ (le_trans ha.le hab)).trans horizon) hcont hsupp, mul_zero]

/-- Exact negative Ward–Mertens row through the sharp Poisson horizon. -/
theorem stabilizerLinearRow_eq_neg_of_horizon {Ω : ℝ → ℝ} {a b m : ℝ} (Q : ℕ)
    (ha : 0 < a) (hab : a ≤ b) (hm : 0 < m) (horizon : (Q : ℝ) * b ≤ π * m)
    (hΩ : ContDiff ℝ 2 Ω) (hsupp : ∀ u, u ∉ Set.Icc a b → Ω u = 0) :
    stabilizerLinearRow Q Ω m = -cosTransform Ω 0 *
      ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q % 2 = 1),
        RHTower.Sieve.sqfreeTotientInv q := by
  have hsp : ∀ u, Ω u ≠ 0 → |u| ≤ b := by
    intro u hu
    have hmem : u ∈ Set.Icc a b := by by_contra h; exact hu (hsupp u h)
    rw [abs_of_nonneg (ha.le.trans hmem.1)]
    exact hmem.2
  rw [stabilizerLinearRow_eq_dual Q hm hΩ hsp,
    stabilizerSpatialDual_eq_zero_of_horizon Q ha hab horizon hΩ.continuous hsupp]
  ring

private theorem summable_spatial_lattice {Ω : ℝ → ℝ} {A L : ℝ}
    (hL : 0 < L) (hsupp : ∀ u, Ω u ≠ 0 → |u| ≤ A) :
    Summable (fun k : ℤ => Ω ((k : ℝ) * L)) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc ⌈-A / L⌉ ⌊A / L⌋)
  intro k hk
  by_contra hn
  have hab := abs_le.mp (hsupp ((k : ℝ) * L) hn)
  apply hk
  exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr ((div_le_iff₀ hL).mpr hab.1),
    Int.le_floor.mpr ((le_div_iff₀ hL).mpr hab.2)⟩

private theorem real_tsum_coprime_eq_divisors {q : ℕ} (hq : q ≠ 0)
    (F : ℤ → ℝ) (hF : Summable F) :
    (∑' n : ℤ, if n.natAbs.Coprime q then F n else 0) =
      ∑ d ∈ q.divisors, GaloisForLFunctions.BezoutValuationIncidence.moebiusReal d *
        ∑' n : ℤ, F (n * d) := by
  have hC := (Complex.ofRealCLM.hasSum hF.hasSum).summable
  have h := _root_.RHTower.tsum_coprime_eq_sum_divisors_moebius hq
    (fun n : ℤ => (F n : ℂ)) hC
  have hif : (fun n : ℤ => if n.natAbs.Coprime q then (F n : ℂ) else 0) =
      (fun n : ℤ => ((if n.natAbs.Coprime q then F n else 0 : ℝ) : ℂ)) := by
    funext n
    split_ifs <;> rfl
  rw [hif, ← Complex.ofReal_tsum] at h
  have he (d : ℕ) : ((ArithmeticFunction.moebius d : ℤ) : ℂ) * ∑' n : ℤ, (F (n * d) : ℂ) =
      ((GaloisForLFunctions.BezoutValuationIncidence.moebiusReal d * ∑' n : ℤ, F (n * d) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_tsum, Complex.ofReal_mul]
    rfl
  simp_rw [he] at h
  rw [← Complex.ofReal_sum] at h
  exact Complex.ofReal_injective h

private theorem sum_complementary_divisors (q : ℕ) (F : ℕ → ℝ) :
    (∑ d ∈ q.divisors, F d) = ∑ d ∈ q.divisors, F (q / d) := by
  have hmem (d : ℕ) (hd : d ∈ q.divisors) : q / d ∈ q.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd),
      Nat.ne_zero_of_mem_divisors hd⟩
  have hinv (d : ℕ) (hd : d ∈ q.divisors) : q / (q / d) = d := by
    apply mul_right_cancel₀ (Nat.pos_of_mem_divisors (hmem d hd)).ne'
    rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors (hmem d hd)),
      Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
  refine Finset.sum_nbij' (fun d => q / d) (fun d => q / d) hmem hmem hinv hinv ?_
  intro d hd
  rw [hinv d hd]

/-- The spatial dual is the sum over primitive lattice samples. -/
theorem ramanujanSpatialDual_eq_primitive {Ω : ℝ → ℝ} {A m : ℝ} {q : ℕ}
    (hm : 0 < m) (hq : 0 < q) (hsupp : ∀ u, Ω u ≠ 0 → |u| ≤ A) :
    ramanujanSpatialDual q Ω m =
      ∑' n : ℤ, if n.natAbs.Coprime q then Ω ((n : ℝ) * (π * m / q)) else 0 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hs := summable_spatial_lattice (L := π * m / q) (by positivity) hsupp
  rw [real_tsum_coprime_eq_divisors hq.ne' _ hs, ramanujanSpatialDual,
    sum_complementary_divisors q]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdvd := Nat.dvd_of_mem_divisors hd
  have hd0 := Nat.pos_of_mem_divisors hd
  have hc0 : 0 < q / d := Nat.div_pos (Nat.divisor_le hd) hd0
  have hinv : q / (q / d) = d := by
    apply mul_right_cancel₀ hc0.ne'
    rw [Nat.div_mul_cancel (Nat.div_dvd_of_dvd hdvd), Nat.mul_div_cancel' hdvd]
  rw [hinv]
  congr 1
  apply tsum_congr
  intro n
  congr 1
  push_cast
  have hprod : ((q / d : ℕ) : ℝ) * (d : ℝ) = (q : ℝ) := by
    exact_mod_cast Nat.div_mul_cancel hdvd
  have hcR : ((q / d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hc0.ne'
  field_simp [hcR, hqR.ne']
  rw [← hprod]
  ring

/-- A nonnegative window has a nonnegative spatial correction at every conductor. -/
theorem ramanujanSpatialDual_nonneg {Ω : ℝ → ℝ} {A m : ℝ} {q : ℕ}
    (hm : 0 < m) (hq : 0 < q) (hsupp : ∀ u, Ω u ≠ 0 → |u| ≤ A)
    (hΩ : ∀ u, 0 ≤ Ω u) : 0 ≤ ramanujanSpatialDual q Ω m := by
  rw [ramanujanSpatialDual_eq_primitive hm hq hsupp]
  apply tsum_nonneg
  intro n
  split_ifs
  · exact hΩ _
  · exact le_rfl

/-- Equality in the spatial lower bound means that every primitive sample vanishes. -/
theorem ramanujanSpatialDual_eq_zero_iff {Ω : ℝ → ℝ} {A m : ℝ} {q : ℕ}
    (hm : 0 < m) (hq : 0 < q) (hsupp : ∀ u, Ω u ≠ 0 → |u| ≤ A)
    (hΩ : ∀ u, 0 ≤ Ω u) :
    ramanujanSpatialDual q Ω m = 0 ↔
      ∀ n : ℤ, n.natAbs.Coprime q → Ω ((n : ℝ) * (π * m / q)) = 0 := by
  rw [ramanujanSpatialDual_eq_primitive hm hq hsupp]
  let F : ℤ → ℝ := fun n => if n.natAbs.Coprime q then Ω ((n : ℝ) * (π * m / q)) else 0
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hs0 := summable_spatial_lattice (L := π * m / q) (by positivity) hsupp
  have hs : Summable F := by
    simpa only [F, Set.indicator_apply, Set.mem_setOf_eq] using
      hs0.indicator {n : ℤ | n.natAbs.Coprime q}
  have hn : ∀ n, 0 ≤ F n := by
    intro n
    dsimp only [F]
    split_ifs
    · exact hΩ _
    · exact le_rfl
  constructor
  · intro hz
    have hf := (hasSum_zero_iff_of_nonneg hn).mp (hz ▸ hs.hasSum)
    intro n hcop
    have he := congrFun hf n
    simpa only [F, if_pos hcop, Pi.zero_apply] using he
  · intro hz
    have he : F = fun _ => 0 := by
      funext n
      dsimp only [F]
      split_ifs with hcop
      · exact hz n hcop
      · rfl
    change (∑' n, F n) = 0
    rw [he, tsum_zero]

/-- Nonnegative windows give a nonnegative correction for every finite cutoff. -/
theorem stabilizerSpatialDual_nonneg {Ω : ℝ → ℝ} {A m : ℝ} (Q : ℕ)
    (hm : 0 < m) (hsupp : ∀ u, Ω u ≠ 0 → |u| ≤ A) (hΩ : ∀ u, 0 ≤ Ω u) :
    0 ≤ stabilizerSpatialDual Q Ω m := by
  apply Finset.sum_nonneg
  intro q hq
  exact mul_nonneg (div_nonneg (RHTower.Sieve.sqfreeTotientInv_nonneg q) (Nat.cast_nonneg _))
    (ramanujanSpatialDual_nonneg hm (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1 hsupp hΩ)

/-- The negative odd-conductor diagonal is a lower bound for the complete signed
row, with equality through the Poisson horizon. -/
theorem neg_odd_diagonal_le_stabilizerLinearRow {Ω : ℝ → ℝ} {A m : ℝ} (Q : ℕ)
    (hm : 0 < m) (hΩ : ContDiff ℝ 2 Ω) (hsupp : ∀ u, Ω u ≠ 0 → |u| ≤ A)
    (hn : ∀ u, 0 ≤ Ω u) :
    -cosTransform Ω 0 * (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q % 2 = 1),
      RHTower.Sieve.sqfreeTotientInv q) ≤ stabilizerLinearRow Q Ω m := by
  rw [stabilizerLinearRow_eq_dual Q hm hΩ hsupp]
  have hdual := mul_nonneg (mul_nonneg Real.pi_pos.le hm.le)
    (stabilizerSpatialDual_nonneg Q hm hsupp hn)
  linarith

/-- Every primitive sample is bounded by the full nonnegative spatial dual. -/
theorem primitive_sample_le_ramanujanSpatialDual {Ω : ℝ → ℝ} {A m : ℝ} {q : ℕ}
    (hm : 0 < m) (hq : 0 < q) (hsupp : ∀ u, Ω u ≠ 0 → |u| ≤ A)
    (hΩ : ∀ u, 0 ≤ Ω u) (n : ℤ) (hn : n.natAbs.Coprime q) :
    Ω ((n : ℝ) * (π * m / q)) ≤ ramanujanSpatialDual q Ω m := by
  rw [ramanujanSpatialDual_eq_primitive hm hq hsupp]
  let F : ℤ → ℝ := fun j => if j.natAbs.Coprime q then Ω ((j : ℝ) * (π * m / q)) else 0
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hs0 := summable_spatial_lattice (L := π * m / q) (by positivity) hsupp
  have hs : Summable F := by
    simpa only [F, Set.indicator_apply, Set.mem_setOf_eq] using
      hs0.indicator {j : ℤ | j.natAbs.Coprime q}
  have hnonneg (j : ℤ) : 0 ≤ F j := by
    dsimp only [F]
    split_ifs
    · exact hΩ _
    · exact le_rfl
  have h := hs.le_tsum n (fun j _ => hnonneg j)
  simpa only [F, if_pos hn] using h

/-- Exact negative cancellation occurs precisely when every primitive sample at
an active squarefree odd conductor vanishes. -/
theorem stabilizerLinearRow_eq_neg_iff {Ω : ℝ → ℝ} {A m : ℝ} (Q : ℕ)
    (hm : 0 < m) (hΩ : ContDiff ℝ 2 Ω) (hsupp : ∀ u, Ω u ≠ 0 → |u| ≤ A)
    (hn : ∀ u, 0 ≤ Ω u) :
    stabilizerLinearRow Q Ω m = -cosTransform Ω 0 *
      (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q) ↔
      ∀ q ∈ (Finset.Icc 1 Q).filter (fun q => q % 2 = 1), Squarefree q →
        ∀ n : ℤ, n.natAbs.Coprime q → Ω ((n : ℝ) * (π * m / q)) = 0 := by
  let s := (Finset.Icc 1 Q).filter (fun q => q % 2 = 1)
  have hqpos (q : ℕ) (hq : q ∈ s) : 0 < q :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
  have hnonneg (q : ℕ) (hq : q ∈ s) :
      0 ≤ (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) * ramanujanSpatialDual q Ω m :=
    mul_nonneg (div_nonneg (RHTower.Sieve.sqfreeTotientInv_nonneg q) (Nat.cast_nonneg _))
      (ramanujanSpatialDual_nonneg hm (hqpos q hq) hsupp hn)
  rw [stabilizerLinearRow_eq_dual Q hm hΩ hsupp]
  constructor
  · intro he
    have hπm : 0 < π * m := mul_pos Real.pi_pos hm
    have hzprod : π * m * stabilizerSpatialDual Q Ω m = 0 := by linarith
    have hz := (mul_eq_zero.mp hzprod).resolve_left hπm.ne'
    intro q hq hsf
    have hterm := Finset.single_le_sum hnonneg hq
    change _ ≤ stabilizerSpatialDual Q Ω m at hterm
    rw [hz] at hterm
    have heq := le_antisymm hterm (hnonneg q hq)
    have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (hqpos q hq)
    have hw : 0 < RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ) := by
      rw [RHTower.Sieve.sqfreeTotientInv_apply, if_pos hsf]
      positivity
    have hd := (mul_eq_zero.mp heq).resolve_left hw.ne'
    exact (ramanujanSpatialDual_eq_zero_iff hm (hqpos q hq) hsupp hn).mp hd
  · intro he
    have hz : stabilizerSpatialDual Q Ω m = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      by_cases hsf : Squarefree q
      · rw [(ramanujanSpatialDual_eq_zero_iff hm (hqpos q hq) hsupp hn).mpr (he q hq hsf), mul_zero]
      · rw [RHTower.Sieve.sqfreeTotientInv_apply, if_neg hsf, zero_div, zero_mul]
    rw [hz]
    ring
end GaloisForLFunctions.TransThresholdPairCorrelation
