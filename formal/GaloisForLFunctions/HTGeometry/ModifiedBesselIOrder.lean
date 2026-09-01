import GaloisForLFunctions.HTGeometry.LocallyUniformMTest
import GaloisForLFunctions.RHTower.DeBrangesExplicitGammaGauge

/-!
# Modified Bessel I as an entire function of complex order

This module constructs `I_ν(s)` from its reciprocal-Gamma series for every positive real `s`.
The proof establishes local normal convergence by an eventual uniform ratio `1/2`, proves the
standard order recurrence, and phase-twists it into the same companion recurrence as `K_ν(s)`.
Exact positive real parts at orders zero and one supply the later fundamental-matrix determinant.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Set Complex

noncomputable section

def modifiedBesselIOrderCoreTerm (a : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ((a : ℂ) ^ (2 * n) / (n.factorial : ℂ)) *
    reciprocalGammaEntire (z + (n + 1 : ℕ))

theorem modifiedBesselIOrderCoreTerm_succ_mul (a : ℝ) (n : ℕ) (z : ℂ) :
    modifiedBesselIOrderCoreTerm a (n + 1) z *
        ((n + 1 : ℕ) * (z + (n + 1 : ℕ))) =
      (a : ℂ) ^ 2 * modifiedBesselIOrderCoreTerm a n z := by
  have hgamma := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one
    (z + (n + 1 : ℕ))
  change reciprocalGammaEntire (z + (n + 1 : ℕ)) =
      (z + (n + 1 : ℕ)) * reciprocalGammaEntire ((z + (n + 1 : ℕ)) + 1) at hgamma
  rw [modifiedBesselIOrderCoreTerm, modifiedBesselIOrderCoreTerm]
  rw [show ((n + 1).factorial : ℂ) = (n + 1 : ℕ) * (n.factorial : ℂ) by
    simp [Nat.factorial_succ]]
  rw [show z + ((n + 1 + 1 : ℕ) : ℂ) = (z + (n + 1 : ℕ)) + 1 by push_cast; ring]
  rw [hgamma]
  have hn : ((n.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp
  ring

theorem modifiedBesselIOrderCoreTerm_eventually_half (a : ℝ) (x : ℂ) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ z ∈ Metric.ball x 1,
      ‖modifiedBesselIOrderCoreTerm a (n + 1) z‖ ≤
        (1 / 2 : ℝ) * ‖modifiedBesselIOrderCoreTerm a n z‖ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (‖x‖ + 1 + |a| + 1))
  refine ⟨N, fun n hn z hz => ?_⟩
  by_cases ha : a = 0
  · subst a
    have hzero : modifiedBesselIOrderCoreTerm 0 (n + 1) z = 0 := by
      simp [modifiedBesselIOrderCoreTerm, show 2 * (n + 1) ≠ 0 by omega]
    rw [hzero, norm_zero]
    positivity
  have hdist : dist z x < 1 := Metric.mem_ball.mp hz
  have hznorm : ‖z‖ < ‖x‖ + 1 := by
    calc
      ‖z‖ ≤ ‖z - x‖ + ‖x‖ := by
        simpa [sub_add_cancel] using norm_add_le (z - x) x
      _ < ‖x‖ + 1 := by rw [dist_eq_norm] at hdist; linarith
  have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnlarge : 2 * (‖x‖ + 1 + |a| + 1) < (n + 1 : ℕ) := by
    exact lt_of_lt_of_le hN (by exact_mod_cast Nat.le_succ_of_le hn)
  have hnabs : 2 * |a| < ((n + 1 : ℕ) : ℝ) := by linarith [norm_nonneg x, abs_nonneg a]
  have hshift : |a| < ‖z + (n + 1 : ℕ)‖ := by
    have htri := norm_sub_le (z + (n + 1 : ℕ)) z
    have hcast : ‖((n + 1 : ℕ) : ℂ)‖ = ((n + 1 : ℕ) : ℝ) := by
      rw [Complex.norm_natCast]
    rw [show z + (n + 1 : ℕ) - z = ((n + 1 : ℕ) : ℂ) by ring, hcast] at htri
    linarith
  have hapos : 0 < |a| := abs_pos.mpr ha
  have hD : 0 < ((n + 1 : ℕ) : ℝ) * ‖z + (n + 1 : ℕ)‖ :=
    mul_pos (by positivity) (lt_trans hapos hshift)
  have hDlarge : 2 * |a| ^ 2 < ((n + 1 : ℕ) : ℝ) * ‖z + (n + 1 : ℕ)‖ := by
    nlinarith [abs_nonneg a]
  have hid := congrArg norm (modifiedBesselIOrderCoreTerm_succ_mul a n z)
  have hncast : ‖(((n + 1 : ℕ) : ℂ))‖ = ((n + 1 : ℕ) : ℝ) := by
    rw [Complex.norm_natCast]
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] at hid
  rw [hncast] at hid
  have hnext : ‖modifiedBesselIOrderCoreTerm a (n + 1) z‖ =
      |a| ^ 2 * ‖modifiedBesselIOrderCoreTerm a n z‖ /
        (((n + 1 : ℕ) : ℝ) * ‖z + (n + 1 : ℕ)‖) := by
    exact (eq_div_iff hD.ne').2 hid
  rw [hnext]
  apply (div_le_iff₀ hD).2
  have ht := norm_nonneg (modifiedBesselIOrderCoreTerm a n z)
  nlinarith

theorem continuous_modifiedBesselIOrderCoreTerm (a : ℝ) (n : ℕ) :
    Continuous (modifiedBesselIOrderCoreTerm a n) := by
  change Continuous (fun z : ℂ =>
    ((a : ℂ) ^ (2 * n) / (n.factorial : ℂ)) *
      reciprocalGammaEntire (z + (n + 1 : ℕ)))
  exact continuous_const.mul
    (contDiff_reciprocalGammaEntire.continuous.comp
      (continuous_id.add continuous_const))

theorem summableLocallyUniformlyOn_modifiedBesselIOrderCoreTerm (a : ℝ) :
    SummableLocallyUniformlyOn (modifiedBesselIOrderCoreTerm a) Set.univ := by
  apply summableLocallyUniformlyOn_of_locally_bounded
  intro x _
  obtain ⟨N, hhalf⟩ := modifiedBesselIOrderCoreTerm_eventually_half a x
  let head : ℂ → ℝ := fun z =>
    ∑ n ∈ Finset.range (N + 1), ‖modifiedBesselIOrderCoreTerm a n z‖
  let C : ℝ := head x + 1
  have hhead_cont : Continuous head := by
    dsimp [head]
    exact continuous_finsetSum _ fun n _ =>
      (continuous_modifiedBesselIOrderCoreTerm a n).norm
  have hhead_nonneg : ∀ z, 0 ≤ head z := by
    intro z
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hCpos : 0 < C := by dsimp [C]; linarith [hhead_nonneg x]
  let t : Set ℂ := Metric.ball x 1 ∩ {z | head z < C}
  have ht : t ∈ 𝓝 x := by
    apply inter_mem (Metric.ball_mem_nhds x zero_lt_one)
    exact (isOpen_lt hhead_cont continuous_const).mem_nhds (by simp [C])
  refine ⟨t, by simpa [nhdsWithin_univ] using ht,
    (fun n => if n < N then C else C * (1 / 2 : ℝ) ^ (n - N)), ?_, ?_⟩
  · rw [← summable_nat_add_iff N]
    simpa using (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left C
  intro n y hy
  have hyball : y ∈ Metric.ball x 1 := hy.1
  have hyhead : head y < C := hy.2
  have hseed : ‖modifiedBesselIOrderCoreTerm a N y‖ ≤ C := by
    calc
      ‖modifiedBesselIOrderCoreTerm a N y‖ ≤ head y := by
        dsimp [head]
        exact Finset.single_le_sum
          (f := fun i : ℕ => ‖modifiedBesselIOrderCoreTerm a i y‖)
          (fun i _ => norm_nonneg _)
          (Finset.mem_range.mpr (Nat.lt_succ_self N))
      _ ≤ C := hyhead.le
  have htail : ∀ d : ℕ,
      ‖modifiedBesselIOrderCoreTerm a (N + d) y‖ ≤ C * (1 / 2 : ℝ) ^ d := by
    intro d
    induction d with
    | zero => simpa using hseed
    | succ d ih =>
        calc
          ‖modifiedBesselIOrderCoreTerm a (N + (d + 1)) y‖ =
              ‖modifiedBesselIOrderCoreTerm a ((N + d) + 1) y‖ := by ring_nf
          _ ≤ (1 / 2 : ℝ) * ‖modifiedBesselIOrderCoreTerm a (N + d) y‖ :=
            hhalf (N + d) (Nat.le_add_right N d) y hyball
          _ ≤ (1 / 2 : ℝ) * (C * (1 / 2 : ℝ) ^ d) := by
            exact mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = C * (1 / 2 : ℝ) ^ (d + 1) := by rw [pow_succ]; ring
  change ‖modifiedBesselIOrderCoreTerm a n y‖ ≤
    if n < N then C else C * (1 / 2 : ℝ) ^ (n - N)
  split_ifs with hn
  · calc
      ‖modifiedBesselIOrderCoreTerm a n y‖ ≤ head y := by
        dsimp [head]
        exact Finset.single_le_sum
          (f := fun i : ℕ => ‖modifiedBesselIOrderCoreTerm a i y‖)
          (fun i _ => norm_nonneg _)
          (Finset.mem_range.mpr (lt_trans hn (Nat.lt_succ_self N)))
      _ ≤ C := hyhead.le
  · have hNn : N ≤ n := Nat.le_of_not_gt hn
    simpa [Nat.add_sub_of_le hNn] using htail (n - N)

def modifiedBesselIOrderCore (a : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, modifiedBesselIOrderCoreTerm a n z

theorem differentiable_modifiedBesselIOrderCoreTerm (a : ℝ) (n : ℕ) :
    Differentiable ℂ (modifiedBesselIOrderCoreTerm a n) := by
  change Differentiable ℂ (fun z : ℂ =>
    ((a : ℂ) ^ (2 * n) / (n.factorial : ℂ)) *
      reciprocalGammaEntire (z + (n + 1 : ℕ)))
  exact (differentiable_const (c :=
      ((a : ℂ) ^ (2 * n) / (n.factorial : ℂ)))).mul
    ((contDiff_reciprocalGammaEntire.differentiable (by simp)).comp
      (differentiable_id.add_const _))

theorem analyticOnNhd_modifiedBesselIOrderCore (a : ℝ) :
    AnalyticOnNhd ℂ (modifiedBesselIOrderCore a) Set.univ := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  have hsum := summableLocallyUniformlyOn_modifiedBesselIOrderCoreTerm a
  have hconv : TendstoLocallyUniformlyOn
      (fun s : Finset ℕ => fun z => ∑ n ∈ s, modifiedBesselIOrderCoreTerm a n z)
      (modifiedBesselIOrderCore a) atTop Set.univ := by
    rw [← hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn]
    exact hsum.hasSumLocallyUniformlyOn
  have hpartials : ∀ s : Finset ℕ,
      DifferentiableOn ℂ
        (fun z => ∑ n ∈ s, modifiedBesselIOrderCoreTerm a n z) Set.univ := by
    intro s
    apply Differentiable.differentiableOn
    induction s using Finset.induction with
    | empty => simp
    | @insert i s hi ih =>
        intro z
        rw [show (fun w => ∑ n ∈ insert i s, modifiedBesselIOrderCoreTerm a n w) =
            fun w => modifiedBesselIOrderCoreTerm a i w +
              ∑ n ∈ s, modifiedBesselIOrderCoreTerm a n w by
          funext w
          exact Finset.sum_insert hi]
        exact (differentiable_modifiedBesselIOrderCoreTerm a i z).add (ih z)
  rw [← differentiableOn_univ]
  exact hconv.differentiableOn (Eventually.of_forall hpartials) isOpen_univ

theorem modifiedBesselIOrderCoreTerm_zero_sub_one (a : ℝ) (z : ℂ) :
    modifiedBesselIOrderCoreTerm a 0 (z - 1) =
      z * modifiedBesselIOrderCoreTerm a 0 z := by
  have hgamma := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one z
  change reciprocalGammaEntire z = z * reciprocalGammaEntire (z + 1) at hgamma
  simpa [modifiedBesselIOrderCoreTerm] using hgamma

theorem modifiedBesselIOrderCoreTerm_succ_sub_one (a : ℝ) (n : ℕ) (z : ℂ) :
    modifiedBesselIOrderCoreTerm a (n + 1) (z - 1) =
      z * modifiedBesselIOrderCoreTerm a (n + 1) z +
        (a : ℂ) ^ 2 * modifiedBesselIOrderCoreTerm a n (z + 1) := by
  have hgamma := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one
    (z + (n + 1 : ℕ))
  change reciprocalGammaEntire (z + (n + 1 : ℕ)) =
      (z + (n + 1 : ℕ)) * reciprocalGammaEntire ((z + (n + 1 : ℕ)) + 1) at hgamma
  simp only [modifiedBesselIOrderCoreTerm]
  rw [show z - 1 + ((n + 1 + 1 : ℕ) : ℂ) = z + (n + 1 : ℕ) by push_cast; ring,
    show z + ((n + 1 + 1 : ℕ) : ℂ) = (z + (n + 1 : ℕ)) + 1 by push_cast; ring,
    show z + 1 + ((n + 1 : ℕ) : ℂ) = (z + (n + 1 : ℕ)) + 1 by push_cast; ring,
    show ((n + 1).factorial : ℂ) = (n + 1 : ℕ) * (n.factorial : ℂ) by
      simp [Nat.factorial_succ], hgamma]
  have hn : ((n.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp
  ring

theorem sum_modifiedBesselIOrderCoreTerm_sub_one (a : ℝ) (z : ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), modifiedBesselIOrderCoreTerm a n (z - 1)) =
      z * (∑ n ∈ Finset.range (N + 1), modifiedBesselIOrderCoreTerm a n z) +
        (a : ℂ) ^ 2 *
          (∑ n ∈ Finset.range N, modifiedBesselIOrderCoreTerm a n (z + 1)) := by
  induction N with
  | zero => simpa using modifiedBesselIOrderCoreTerm_zero_sub_one a z
  | succ N ih =>
      nth_rewrite 1 [Finset.sum_range_succ]
      nth_rewrite 2 [Finset.sum_range_succ]
      nth_rewrite 3 [Finset.sum_range_succ]
      rw [ih, modifiedBesselIOrderCoreTerm_succ_sub_one]
      ring

theorem modifiedBesselIOrderCore_sub_one (a : ℝ) (z : ℂ) :
    modifiedBesselIOrderCore a (z - 1) =
      z * modifiedBesselIOrderCore a z +
        (a : ℂ) ^ 2 * modifiedBesselIOrderCore a (z + 1) := by
  have hsummable (w : ℂ) : Summable (fun n => modifiedBesselIOrderCoreTerm a n w) :=
    (summableLocallyUniformlyOn_modifiedBesselIOrderCoreTerm a).summable (Set.mem_univ w)
  have hsucc : Tendsto (fun N : ℕ => N + 1) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with N hN
    omega
  have hleft : Tendsto
      (fun N => ∑ n ∈ Finset.range (N + 1), modifiedBesselIOrderCoreTerm a n (z - 1))
      atTop (𝓝 (modifiedBesselIOrderCore a (z - 1))) := by
    exact (hsummable (z - 1)).hasSum.tendsto_sum_nat.comp hsucc
  have hmid : Tendsto
      (fun N => ∑ n ∈ Finset.range (N + 1), modifiedBesselIOrderCoreTerm a n z)
      atTop (𝓝 (modifiedBesselIOrderCore a z)) := by
    exact (hsummable z).hasSum.tendsto_sum_nat.comp hsucc
  have hright : Tendsto
      (fun N => ∑ n ∈ Finset.range N, modifiedBesselIOrderCoreTerm a n (z + 1))
      atTop (𝓝 (modifiedBesselIOrderCore a (z + 1))) :=
    (hsummable (z + 1)).hasSum.tendsto_sum_nat
  have hzlim : Tendsto (fun _ : ℕ => z) atTop (𝓝 z) := tendsto_const_nhds
  have halim : Tendsto (fun _ : ℕ => (a : ℂ) ^ 2) atTop (𝓝 ((a : ℂ) ^ 2)) :=
    tendsto_const_nhds
  have hcombined : Tendsto
      (fun N => z * (∑ n ∈ Finset.range (N + 1), modifiedBesselIOrderCoreTerm a n z) +
        (a : ℂ) ^ 2 *
          (∑ n ∈ Finset.range N, modifiedBesselIOrderCoreTerm a n (z + 1)))
      atTop (𝓝 (z * modifiedBesselIOrderCore a z +
        (a : ℂ) ^ 2 * modifiedBesselIOrderCore a (z + 1))) :=
    (hzlim.mul hmid).add (halim.mul hright)
  have heq :
      (fun N => ∑ n ∈ Finset.range (N + 1), modifiedBesselIOrderCoreTerm a n (z - 1)) =
        fun N => z * (∑ n ∈ Finset.range (N + 1), modifiedBesselIOrderCoreTerm a n z) +
          (a : ℂ) ^ 2 *
            (∑ n ∈ Finset.range N, modifiedBesselIOrderCoreTerm a n (z + 1)) := by
    funext N
    exact sum_modifiedBesselIOrderCoreTerm_sub_one a z N
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hcombined

/-- Modified Bessel `I` as an entire function of order, at positive real argument. -/
def modifiedBesselIOrder (s : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (z * Real.log (s / 2)) * modifiedBesselIOrderCore (s / 2) z

theorem analyticOnNhd_modifiedBesselIOrder (s : ℝ) :
    AnalyticOnNhd ℂ (modifiedBesselIOrder s) Set.univ := by
  change AnalyticOnNhd ℂ (fun z =>
    Complex.exp (z * Real.log (s / 2)) * modifiedBesselIOrderCore (s / 2) z) Set.univ
  exact (analyticOnNhd_id.mul analyticOnNhd_const).cexp.mul
    (analyticOnNhd_modifiedBesselIOrderCore (s / 2))

theorem modifiedBesselIOrder_recurrence {s : ℝ} (hs : 0 < s) (z : ℂ) :
    modifiedBesselIOrder s (z + 1) =
      modifiedBesselIOrder s (z - 1) -
        ((2 : ℂ) * z / s) * modifiedBesselIOrder s z := by
  let a : ℝ := s / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hsa : (s : ℂ) = 2 * (a : ℂ) := by dsimp [a]; push_cast; ring
  have hexpLog : Complex.exp (Real.log a) = (a : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log ha]
  have hplus : Complex.exp ((z + 1) * Real.log a) =
      Complex.exp (z * Real.log a) * (a : ℂ) := by
    rw [show (z + 1) * (Real.log a : ℂ) =
      z * Real.log a + Real.log a by ring, Complex.exp_add, hexpLog]
  have hminus : Complex.exp ((z - 1) * Real.log a) * (a : ℂ) =
      Complex.exp (z * Real.log a) := by
    rw [← hexpLog, ← Complex.exp_add]
    congr 1
    ring
  have hminus' : (a : ℂ) * Complex.exp (Real.log a * (z - 1)) =
      Complex.exp (z * Real.log a) := by
    rw [mul_comm (a : ℂ), mul_comm (Real.log a : ℂ) (z - 1)]
    exact hminus
  have hcore := modifiedBesselIOrderCore_sub_one a z
  rw [modifiedBesselIOrder, modifiedBesselIOrder, modifiedBesselIOrder]
  change Complex.exp ((z + 1) * Real.log a) * modifiedBesselIOrderCore a (z + 1) =
    Complex.exp ((z - 1) * Real.log a) * modifiedBesselIOrderCore a (z - 1) -
      (2 * z / s) * (Complex.exp (z * Real.log a) * modifiedBesselIOrderCore a z)
  rw [hplus, hcore]
  field_simp [ha0, hs0]
  rw [hsa]
  field_simp [ha0]
  rw [hminus']
  ring

theorem reciprocalGammaEntire_nat_succ (n : ℕ) :
    reciprocalGammaEntire ((n + 1 : ℕ) : ℂ) = ((n.factorial : ℕ) : ℂ)⁻¹ := by
  induction n with
  | zero => simp [reciprocalGammaEntire]
  | succ n ih =>
      have hgamma := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one
        (((n + 1 : ℕ) : ℂ))
      change reciprocalGammaEntire ((n + 1 : ℕ) : ℂ) =
        ((n + 1 : ℕ) : ℂ) * reciprocalGammaEntire (((n + 1 : ℕ) : ℂ) + 1) at hgamma
      have hn1 : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      have hsolve : reciprocalGammaEntire (((n + 1 : ℕ) : ℂ) + 1) =
          reciprocalGammaEntire ((n + 1 : ℕ) : ℂ) / ((n + 1 : ℕ) : ℂ) := by
        apply (eq_div_iff hn1).2
        rw [mul_comm]
        exact hgamma.symm
      rw [show (((n + 1 + 1 : ℕ) : ℂ)) = (((n + 1 : ℕ) : ℂ) + 1) by push_cast; ring,
        hsolve, ih]
      rw [Nat.factorial_succ]
      push_cast
      field_simp

theorem modifiedBesselIOrderCoreTerm_zero_eq (a : ℝ) (n : ℕ) :
    modifiedBesselIOrderCoreTerm a n 0 =
      ((a ^ (2 * n) / n.factorial / n.factorial : ℝ) : ℂ) := by
  rw [modifiedBesselIOrderCoreTerm]
  rw [show (0 : ℂ) + (n + 1 : ℕ) = (((n + 1 : ℕ) : ℂ)) by simp,
    reciprocalGammaEntire_nat_succ]
  push_cast
  ring

theorem modifiedBesselIOrderCoreTerm_one_eq (a : ℝ) (n : ℕ) :
    modifiedBesselIOrderCoreTerm a n 1 =
      ((a ^ (2 * n) / n.factorial / (n + 1).factorial : ℝ) : ℂ) := by
  rw [modifiedBesselIOrderCoreTerm]
  rw [show (1 : ℂ) + (n + 1 : ℕ) = (((n + 1 + 1 : ℕ) : ℂ)) by push_cast; ring,
    reciprocalGammaEntire_nat_succ (n + 1)]
  push_cast
  ring

theorem modifiedBesselIOrderCore_zero_re_pos (a : ℝ) :
    0 < (modifiedBesselIOrderCore a 0).re := by
  have hsumC : Summable (fun n => modifiedBesselIOrderCoreTerm a n 0) :=
    (summableLocallyUniformlyOn_modifiedBesselIOrderCoreTerm a).summable (Set.mem_univ 0)
  have hsumRe : Summable (fun n => (modifiedBesselIOrderCoreTerm a n 0).re) := by
    refine Summable.of_norm_bounded hsumC.norm fun n => ?_
    simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm
      (modifiedBesselIOrderCoreTerm a n 0)
  have hnonneg : ∀ n, 0 ≤ (modifiedBesselIOrderCoreTerm a n 0).re := by
    intro n
    rw [modifiedBesselIOrderCoreTerm_zero_eq]
    simp only [Complex.ofReal_re]
    have hpow : 0 ≤ a ^ (2 * n) := by
      rw [show 2 * n = n + n by omega, pow_add]
      exact mul_self_nonneg _
    exact div_nonneg (div_nonneg hpow (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hone : (1 : ℝ) ≤ ∑' n, (modifiedBesselIOrderCoreTerm a n 0).re := by
    simpa [modifiedBesselIOrderCoreTerm_zero_eq] using
      hsumRe.le_tsum 0 (fun n _ => hnonneg n)
  have hre := Complex.reCLM.map_tsum hsumC
  change (modifiedBesselIOrderCore a 0).re =
    ∑' n, (modifiedBesselIOrderCoreTerm a n 0).re at hre
  rw [hre]
  linarith

theorem modifiedBesselIOrderCore_one_re_pos (a : ℝ) :
    0 < (modifiedBesselIOrderCore a 1).re := by
  have hsumC : Summable (fun n => modifiedBesselIOrderCoreTerm a n 1) :=
    (summableLocallyUniformlyOn_modifiedBesselIOrderCoreTerm a).summable (Set.mem_univ 1)
  have hsumRe : Summable (fun n => (modifiedBesselIOrderCoreTerm a n 1).re) := by
    refine Summable.of_norm_bounded hsumC.norm fun n => ?_
    simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm
      (modifiedBesselIOrderCoreTerm a n 1)
  have hnonneg : ∀ n, 0 ≤ (modifiedBesselIOrderCoreTerm a n 1).re := by
    intro n
    rw [modifiedBesselIOrderCoreTerm_one_eq]
    simp only [Complex.ofReal_re]
    have hpow : 0 ≤ a ^ (2 * n) := by
      rw [show 2 * n = n + n by omega, pow_add]
      exact mul_self_nonneg _
    exact div_nonneg (div_nonneg hpow (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hone : (1 : ℝ) ≤ ∑' n, (modifiedBesselIOrderCoreTerm a n 1).re := by
    simpa [modifiedBesselIOrderCoreTerm_one_eq] using
      hsumRe.le_tsum 0 (fun n _ => hnonneg n)
  have hre := Complex.reCLM.map_tsum hsumC
  change (modifiedBesselIOrderCore a 1).re =
    ∑' n, (modifiedBesselIOrderCoreTerm a n 1).re at hre
  rw [hre]
  linarith

theorem modifiedBesselIOrder_zero_re_pos {s : ℝ} (_hs : 0 < s) :
    0 < (modifiedBesselIOrder s 0).re := by
  rw [modifiedBesselIOrder]
  simpa using modifiedBesselIOrderCore_zero_re_pos (s / 2)

theorem modifiedBesselIOrder_one_re_pos {s : ℝ} (hs : 0 < s) :
    0 < (modifiedBesselIOrder s 1).re := by
  have ha : 0 < s / 2 := by positivity
  have hexpLog : Complex.exp (Real.log (s / 2)) = ((s / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log ha]
  rw [modifiedBesselIOrder]
  simp only [one_mul, hexpLog, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  exact mul_pos ha (modifiedBesselIOrderCore_one_re_pos (s / 2))

/-- Phase twist converting the standard `I` recurrence to the `K` companion recurrence. -/
def modifiedBesselIOrderPhase (s : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (z * ((Real.pi : ℂ) * Complex.I)) * modifiedBesselIOrder s z

theorem analyticOnNhd_modifiedBesselIOrderPhase (s : ℝ) :
    AnalyticOnNhd ℂ (modifiedBesselIOrderPhase s) Set.univ := by
  change AnalyticOnNhd ℂ (fun z =>
    Complex.exp (z * ((Real.pi : ℂ) * Complex.I)) * modifiedBesselIOrder s z) Set.univ
  exact (analyticOnNhd_id.mul analyticOnNhd_const).cexp.mul
    (analyticOnNhd_modifiedBesselIOrder s)

theorem modifiedBesselIOrderPhase_recurrence {s : ℝ} (hs : 0 < s) (z : ℂ) :
    modifiedBesselIOrderPhase s (z + 1) =
      modifiedBesselIOrderPhase s (z - 1) +
        ((2 : ℂ) * z / s) * modifiedBesselIOrderPhase s z := by
  let p : ℂ := (Real.pi : ℂ) * Complex.I
  have hp : Complex.exp p = -1 := by
    dsimp [p]
    rw [Complex.exp_mul_I]
    simp
  have hnp : Complex.exp (-p) = -1 := by
    rw [Complex.exp_neg, hp]
    norm_num
  have hplus : Complex.exp ((z + 1) * p) = -Complex.exp (z * p) := by
    rw [show (z + 1) * p = z * p + p by ring, Complex.exp_add, hp]
    ring
  have hminus : Complex.exp ((z - 1) * p) = -Complex.exp (z * p) := by
    rw [show (z - 1) * p = z * p + (-p) by ring, Complex.exp_add, hnp]
    ring
  have hI := modifiedBesselIOrder_recurrence hs z
  rw [modifiedBesselIOrderPhase, modifiedBesselIOrderPhase,
    modifiedBesselIOrderPhase]
  change Complex.exp ((z + 1) * p) * modifiedBesselIOrder s (z + 1) =
    Complex.exp ((z - 1) * p) * modifiedBesselIOrder s (z - 1) +
      (2 * z / s) * (Complex.exp (z * p) * modifiedBesselIOrder s z)
  rw [hplus, hminus, hI]
  ring

end

end GaloisForLFunctions.HTGeometry
