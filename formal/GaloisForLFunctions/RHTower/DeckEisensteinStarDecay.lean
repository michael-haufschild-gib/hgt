import GaloisForLFunctions.RHTower.SelbergEisensteinCriticalLine
import GaloisForLFunctions.HTGeometry.BesselArgumentDerivative

/-!
# Uniform decay of the continued non-constant part

For `s` in a closed ball inside the continuation domain `W` and `y ≥ y₀ > 0`, the Bessel terms of
the continued non-constant part of `E_∞(σz, s)` satisfy
`|term_n(z, s)| ≤ C |n|^{k+2} e^{-2π y|n|/N}`, with `C` uniform in `s` and in `y ≥ y₀`: the powers
`Y^s (|n|/Y)^{s-1/2}` from the Bessel form combine with `√(1/Y)` from the Bessel envelope to
`|n|^{Re s - 1/2}`, and `e^{|ν|²/(2a)}` is largest at the smallest `a`.  Hence
`|E^*_σ(z, s)| ≤ A e^{-π y/N}` uniformly, and `E^*_σ(·, s)` is continuous.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Metric
open scoped MatrixGroups

namespace GaloisForLFunctions.RHTower.DeckPointPair

open SelbergEisensteinStarCriticalLine SelbergEisensteinCoefficientSeries SelbergKernelBessel
  SelbergMoebiusUnitClassL SelbergPoincareContinuation

noncomputable section

variable (N : ℕ) [NeZero N] (σ : SL(2, ℤ))

/-- The combined power `Y^σ (|n|/Y)^{σ-1/2} √(1/Y) = |n|^{σ-1/2}`. -/
theorem rpow_mul_rpow_div_mul_sqrt {Y : ℝ} (hY : 0 < Y) {n : ℝ} (hn : 0 < n) (σ' : ℝ) :
    Y ^ σ' * (n / Y) ^ (σ' - 1 / 2) * Real.sqrt (2 * Real.pi / (2 * Real.pi * Y)) = n ^ (σ' - 1 / 2) := by
  have hsq : Real.sqrt (2 * Real.pi / (2 * Real.pi * Y)) = Y ^ (-(1 / 2 : ℝ)) := by
    rw [show 2 * Real.pi / (2 * Real.pi * Y) = Y⁻¹ by field_simp, Real.sqrt_eq_rpow,
      Real.inv_rpow hY.le, Real.rpow_neg hY.le]
  rw [hsq, Real.div_rpow hn.le hY.le]
  field_simp
  rw [← Real.rpow_add hY]
  congr 1
  ring

/-- **Uniform bound for the Bessel terms** on a closed ball in `W` and for `y/N ≥ Y₀`. -/
theorem exists_norm_termX_le_uniform {s₀ : ℂ} {r : ℝ} (hr : 0 < r) (hcb : closedBall s₀ r ⊆ Wset N)
    {Y₀ : ℝ} (hY₀ : 0 < Y₀) :
    ∃ C : ℝ, ∃ k : ℕ, 0 ≤ C ∧ ∀ s ∈ closedBall s₀ r, ∀ z : ℍ, Y₀ ≤ z.im / N → ∀ n : ℤ,
      ‖termX N σ n s z‖ ≤ C * (n.natAbs : ℝ) ^ (k + 2) * Real.exp (-(2 * Real.pi * (z.im / N)) * n.natAbs) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  set f1 : ℂ → ℂ := fun s => 2 * (Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hf1 : Continuous f1 := (Differentiable.continuous (fun s =>
    ((differentiableAt_id.const_cpow (Or.inl hpi)).const_mul 2).mul (Complex.differentiable_one_div_Gamma s)))
  obtain ⟨B1, hB1⟩ := (isCompact_closedBall s₀ r).exists_bound_of_continuousOn hf1.continuousOn
  have hB1n : 0 ≤ B1 := (norm_nonneg _).trans (hB1 s₀ (mem_closedBall_self hr.le))
  set f2 : ℂ → ℝ := fun s => ∑ u : (ZMod N)ˣ, ‖LU N u (2 * s)‖
  have hf2 : ContinuousOn f2 (closedBall s₀ r) := by
    intro s hs
    obtain ⟨_, h1, h2⟩ := hcb hs
    refine ContinuousAt.continuousWithinAt ?_
    refine tendsto_finsetSum _ (fun u _ => ?_)
    exact ((differentiableAt_LU_of N u h1 h2).comp s (differentiableAt_id.const_mul 2)).continuousAt.norm
  obtain ⟨B2, hB2⟩ := (isCompact_closedBall s₀ r).exists_bound_of_continuousOn hf2
  have hB2' : ∀ s ∈ closedBall s₀ r, f2 s ≤ B2 := fun s hs => (le_abs_self _).trans (hB2 s hs)
  have hB2n : 0 ≤ B2 := (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans (hB2' s₀ (mem_closedBall_self hr.le))
  set k : ℕ := ⌈|s₀.re + r - 1 / 2|⌉₊
  set R := ‖s₀‖ + r + 1 / 2
  set E1 := Real.exp (R ^ 2 / (2 * (2 * Real.pi * Y₀)))
  refine ⟨B1 * E1 * (B2 * 2), k, by positivity, fun s hs z hz n => ?_⟩
  have hs0 : 0 < s.re := (hcb hs).1
  have hsre : s.re ≤ s₀.re + r := by
    have h := Complex.abs_re_le_norm (s - s₀)
    rw [mem_closedBall, dist_eq_norm] at hs
    simp only [Complex.sub_re] at h
    have := (abs_le.1 (h.trans hs)).2
    linarith
  set Y := z.im / N
  have hY : 0 < Y := div_pos z.im_pos (by linarith)
  by_cases hn : n = 0
  · simp [termX, hn]
  simp only [termX, if_neg hn]
  have hEN : ‖Complex.exp (-s * (Real.log N : ℂ))‖ ≤ 1 := by
    have := norm_exp_neg_mul_log (s := s) (σ := 0) hN1 hs0.le
    rwa [neg_zero, Real.rpow_zero] at this
  have hex : ‖Complex.exp (2 * Real.pi * Complex.I * n * z.re / N)‖ = 1 := norm_cexp_two_pi_I_div _ _ _
  have hnpos : (0 : ℝ) < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have habs : |(n : ℝ)| = (n.natAbs : ℝ) := by simp [Nat.cast_natAbs]
  have hK : ‖kerBessel Y s n‖ ≤ B1 * E1 * ((n.natAbs : ℝ) ^ k * Real.exp (-(2 * Real.pi * Y) * n.natAbs)) := by
    unfold kerBessel
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY,
      Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hnpos hY)]
    have e2 : ‖2 * (Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹‖ ≤ B1 := hB1 s hs
    have e4 := norm_bessel_le hY hn (ν := s - 1 / 2) (R := R) (by
      rw [mem_closedBall, dist_eq_norm] at hs
      calc ‖s - 1 / 2‖ ≤ ‖s‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
        _ ≤ ‖s₀‖ + r + 1 / 2 := by
          have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
          have h1 : ‖s‖ ≤ ‖s₀‖ + ‖s - s₀‖ := by
            have := norm_add_le s₀ (s - s₀); simpa using this
          linarith)
    have hre : (s - 1 / 2).re = s.re - 1 / 2 := by simp
    rw [hre]
    have hE : Real.exp (R ^ 2 / (2 * (2 * Real.pi * Y))) ≤ E1 := by
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_left (sq_nonneg R) (by positivity)
      nlinarith [Real.pi_pos]
    have hpow : (n.natAbs : ℝ) ^ (s.re - 1 / 2) ≤ (n.natAbs : ℝ) ^ k := by
      rw [← Real.rpow_natCast]
      refine Real.rpow_le_rpow_of_exponent_le (habs ▸ hn1) ?_
      have := Nat.le_ceil |s₀.re + r - 1 / 2|
      have := le_abs_self (s₀.re + r - 1 / 2)
      linarith
    have hcomb := rpow_mul_rpow_div_mul_sqrt hY hnpos s.re
    rw [habs] at hcomb e4
    rw [habs]
    calc Y ^ s.re * ‖2 * (Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹‖ * ((n.natAbs : ℝ) / Y) ^ (s.re - 1 / 2) *
          ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder (2 * Real.pi * Y * (n.natAbs : ℝ)) (s - 1 / 2)‖
        ≤ Y ^ s.re * B1 * ((n.natAbs : ℝ) / Y) ^ (s.re - 1 / 2) *
          (Real.exp (-(2 * Real.pi * Y * (n.natAbs : ℝ))) *
            (Real.exp (R ^ 2 / (2 * (2 * Real.pi * Y))) * Real.sqrt (2 * Real.pi / (2 * Real.pi * Y)))) := by
          gcongr
      _ = B1 * Real.exp (R ^ 2 / (2 * (2 * Real.pi * Y))) *
          (Y ^ s.re * ((n.natAbs : ℝ) / Y) ^ (s.re - 1 / 2) * Real.sqrt (2 * Real.pi / (2 * Real.pi * Y))) *
          Real.exp (-(2 * Real.pi * Y * (n.natAbs : ℝ))) := by ring
      _ = B1 * Real.exp (R ^ 2 / (2 * (2 * Real.pi * Y))) * (n.natAbs : ℝ) ^ (s.re - 1 / 2) *
          Real.exp (-(2 * Real.pi * Y) * (n.natAbs : ℝ)) := by rw [hcomb]; ring_nf
      _ ≤ B1 * E1 * ((n.natAbs : ℝ) ^ k * Real.exp (-(2 * Real.pi * Y) * n.natAbs)) := by
          have := Real.exp_pos (-(2 * Real.pi * Y) * (n.natAbs : ℝ))
          have h0 : 0 ≤ (n.natAbs : ℝ) ^ (s.re - 1 / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
          calc B1 * Real.exp (R ^ 2 / (2 * (2 * Real.pi * Y))) * (n.natAbs : ℝ) ^ (s.re - 1 / 2) *
                Real.exp (-(2 * Real.pi * Y) * (n.natAbs : ℝ))
              ≤ B1 * E1 * (n.natAbs : ℝ) ^ k * Real.exp (-(2 * Real.pi * Y) * (n.natAbs : ℝ)) := by
                gcongr
            _ = _ := by ring
  have hD : ‖Dn N σ n s‖ ≤ B2 * (2 * (n.natAbs : ℝ) ^ 2) :=
    (norm_Dn_le_sq N σ n hs0.le).trans (mul_le_mul_of_nonneg_right (hB2' s hs) (by positivity))
  rw [norm_mul, norm_mul, norm_mul, hex, mul_one]
  calc ‖Complex.exp (-s * (Real.log N : ℂ))‖ * ‖kerBessel Y s n‖ * ‖Dn N σ n s‖
      ≤ 1 * (B1 * E1 * ((n.natAbs : ℝ) ^ k * Real.exp (-(2 * Real.pi * Y) * n.natAbs))) *
          (B2 * (2 * (n.natAbs : ℝ) ^ 2)) := by gcongr
    _ = _ := by rw [pow_add]; ring

omit [NeZero N] in
theorem summable_natAbs_pow_mul_exp (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => (n.natAbs : ℝ) ^ k * Real.exp (-c * n.natAbs) := by
  have hbase := Real.summable_pow_mul_exp_neg_nat_mul k (r := c) hc
  refine Summable.of_nat_of_neg ?_ ?_
  · refine hbase.congr fun m => ?_
    simp only [Int.natAbs_natCast]
  · refine hbase.congr fun m => ?_
    simp only [Int.natAbs_neg, Int.natAbs_natCast]

/-- **Exponential decay of the continued non-constant part**, uniformly on a closed ball in `W`:
`|E^*_σ(z, s)| ≤ A e^{-π y/N}` for `y/N ≥ Y₀`. -/
theorem exists_norm_EstarExt_le {s₀ : ℂ} {r : ℝ} (hr : 0 < r) (hcb : closedBall s₀ r ⊆ Wset N)
    {Y₀ : ℝ} (hY₀ : 0 < Y₀) :
    ∃ A, 0 ≤ A ∧ ∀ s ∈ closedBall s₀ r, ∀ z : ℍ, Y₀ ≤ z.im / N →
      ‖EstarExt N σ s z‖ ≤ A * Real.exp (-(Real.pi * (z.im / N))) := by
  obtain ⟨C, k, hC, hT⟩ := exists_norm_termX_le_uniform N σ hr hcb hY₀
  have hS := summable_natAbs_pow_mul_exp (k + 2) (c := Real.pi * Y₀) (by positivity)
  refine ⟨C * ∑' n : ℤ, (n.natAbs : ℝ) ^ (k + 2) * Real.exp (-(Real.pi * Y₀) * n.natAbs),
    mul_nonneg hC (tsum_nonneg fun n => by positivity), fun s hs z hz => ?_⟩
  set Y := z.im / N
  have hY : 0 < Y := hY₀.trans_le hz
  have hpt : ∀ n : ℤ, ‖termX N σ n s z‖ ≤ Real.exp (-(Real.pi * Y)) *
      (C * ((n.natAbs : ℝ) ^ (k + 2) * Real.exp (-(Real.pi * Y₀) * n.natAbs))) := by
    intro n
    refine (hT s hs z hz n).trans ?_
    by_cases hn : n = 0
    · subst hn; simp
    have hn1 : (1 : ℝ) ≤ n.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hn
    have hexp : Real.exp (-(2 * Real.pi * Y) * n.natAbs) ≤
        Real.exp (-(Real.pi * Y)) * Real.exp (-(Real.pi * Y₀) * n.natAbs) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : Real.pi * Y ≤ Real.pi * Y * n.natAbs := le_mul_of_one_le_right (by positivity) hn1
      have h2 : Real.pi * Y₀ * n.natAbs ≤ Real.pi * Y * n.natAbs := by gcongr
      nlinarith
    calc C * (n.natAbs : ℝ) ^ (k + 2) * Real.exp (-(2 * Real.pi * Y) * n.natAbs)
        ≤ C * (n.natAbs : ℝ) ^ (k + 2) * (Real.exp (-(Real.pi * Y)) *
            Real.exp (-(Real.pi * Y₀) * n.natAbs)) := by gcongr
      _ = _ := by ring
  have hsum : Summable fun n : ℤ => Real.exp (-(Real.pi * Y)) *
      (C * ((n.natAbs : ℝ) ^ (k + 2) * Real.exp (-(Real.pi * Y₀) * n.natAbs))) :=
    (hS.mul_left C).mul_left _
  unfold EstarExt
  refine (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hpt hsum)).trans ?_
  refine (Summable.tsum_le_tsum hpt (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hpt hsum)
    hsum).trans (le_of_eq ?_)
  rw [tsum_mul_left, tsum_mul_left]
  ring

/-! ## Continuity in the space variable -/

omit [NeZero N] in
theorem continuousOn_kerBessel {s : ℂ} {ξ : ℝ} (hξ : ξ ≠ 0) :
    ContinuousOn (fun Y : ℝ => kerBessel Y s ξ) (Ioi 0) := by
  have hξ' : 0 < |ξ| := abs_pos.mpr hξ
  intro Y hY
  have hY0 : 0 < Y := hY
  unfold kerBessel
  have h1 : ContinuousAt (fun Y : ℝ => ((Y : ℝ) : ℂ) ^ s) Y :=
    (Complex.continuous_ofReal.continuousAt).cpow continuousAt_const (Or.inl (by simpa using hY0))
  have h3 : ContinuousAt (fun Y : ℝ => (((|ξ| / Y : ℝ)) : ℂ) ^ (s - 1 / 2)) Y := by
    refine (Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.div continuousAt_id hY0.ne')).cpow
      continuousAt_const (Or.inl ?_)
    simpa using div_pos hξ' hY0
  have h4 : ContinuousAt (fun Y : ℝ =>
      GaloisForLFunctions.HTGeometry.modifiedBesselKOrder (2 * Real.pi * Y * |ξ|) (s - 1 / 2)) Y := by
    have hs : 0 < 2 * Real.pi * Y * |ξ| := by positivity
    have h := (RHTower.d4BM_hasDerivAt_modifiedBesselKOrder_argument hs (s - 1 / 2)).continuousAt
    have h2 : ContinuousAt (fun Y : ℝ => 2 * Real.pi * Y * |ξ|) Y := by fun_prop
    exact ContinuousAt.comp (g := fun q : ℝ =>
      GaloisForLFunctions.HTGeometry.modifiedBesselKOrder q (s - 1 / 2)) h h2
  exact (((h1.mul continuousAt_const).mul h3).mul h4).continuousWithinAt

theorem continuous_EstarExt {s : ℂ} (hs : s ∈ Wset N) : Continuous fun z : ℍ => EstarExt N σ s z := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_Wset N) s hs
  have hcb : closedBall s (ε / 2) ⊆ Wset N :=
    (closedBall_subset_ball (by linarith)).trans hball
  refine continuous_iff_continuousAt.2 fun z₀ => ?_
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set Y₀ := z₀.im / N / 2
  have hY₀ : 0 < Y₀ := by positivity
  obtain ⟨C, k, hC, hT⟩ := exists_norm_termX_le_uniform N σ (half_pos hε) hcb hY₀
  set U := {z : ℍ | Y₀ < z.im / N}
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_im.div_const _)
  have hz₀ : z₀ ∈ U := by
    show Y₀ < z₀.im / N
    have : 0 < z₀.im / N := by positivity
    simp only [Y₀]; linarith
  have hcont : ContinuousOn (fun z : ℍ => ∑' n : ℤ, termX N σ n s z) U := by
    refine continuousOn_tsum (u := fun n : ℤ => C * (n.natAbs : ℝ) ^ (k + 2) *
      Real.exp (-(2 * Real.pi * Y₀) * n.natAbs)) (fun n => ?_) ?_ (fun n z hz => ?_)
    · refine Continuous.continuousOn ?_
      unfold termX
      by_cases hn : n = 0
      · simp only [if_pos hn]; exact continuous_const
      simp only [if_neg hn]
      have hker : Continuous fun z : ℍ => kerBessel (z.im / N) s n := by
        refine (continuousOn_kerBessel (by exact_mod_cast hn)).comp_continuous
          (continuous_im.div_const _) fun z => ?_
        show 0 < z.im / N
        positivity
      refine ((continuous_const.mul hker).mul ?_).mul continuous_const
      refine Complex.continuous_exp.comp ?_
      exact (continuous_const.mul (Complex.continuous_ofReal.comp continuous_re)).div_const _
    · have := (summable_natAbs_pow_mul_exp (k + 2) (c := 2 * Real.pi * Y₀) (by positivity)).mul_left C
      refine this.congr fun n => ?_
      ring
    · refine (hT s (mem_closedBall_self (half_pos hε).le) z (le_of_lt hz) n).trans ?_
      have hz' : Y₀ < z.im / N := hz
      gcongr
  exact (hcont.continuousAt (hU.mem_nhds hz₀))

end

end GaloisForLFunctions.RHTower.DeckPointPair
