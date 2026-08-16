import GaloisForLFunctions.RHTower.HarmonicTriangularProjection

/-!
# The weighted floor family and its critical exponent threshold

For `θ ≥ 0` the weighted floor transform is `Q_θ = T_{n^{-θ}} R`.  The weights `d^{-θ}` and
`μ(d) d^{-θ}` are Dirichlet inverses for every `θ`, so the transform is always exactly invertible:

`R(N) = ∑_{d ≤ N} μ(d) d^{-θ} Q_θ(⌊N/d⌋)`.

Stability of that inversion in the critical topology has a sharp threshold at `θ = 1/2`.  Above the
threshold a square-root bound transfers in both directions with the absolutely convergent majorant
`∑ d^{-θ-1/2-ε}`.  Below it, the model profile `√N` already shows the transform is unbounded after
critical normalization, so the transform cannot be a stable coordinate there.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The weighted pair -/

/-- The power weight `d^{-θ}`. -/
def powerWeight (theta : ℝ) (d : ℕ) : ℝ := (d : ℝ) ^ (-theta)

/-- The Möbius power weight `μ(d) d^{-θ}`. -/
def moebiusPowerWeight (theta : ℝ) (d : ℕ) : ℝ :=
  (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-theta)

/-- **(24.25) The two weighted families are Dirichlet inverse for every exponent.** -/
theorem dirichletConv_moebiusPower_power (theta : ℝ) {n : ℕ} (hn : n ≠ 0) :
    dirichletConv (moebiusPowerWeight theta) (powerWeight theta) n = unitWeight n := by
  classical
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hterm : ∀ d ∈ n.divisors,
      moebiusPowerWeight theta d * powerWeight theta (n / d)
        = (n : ℝ) ^ (-theta) * (ArithmeticFunction.moebius d : ℝ) := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    have hmul : d * (n / d) = n := Nat.mul_div_cancel' hd.1
    have hcast : (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
      rw [← Nat.cast_mul, hmul]
    rw [moebiusPowerWeight, powerWeight, ← hcast,
      Real.mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg _)]
    ring
  rw [dirichletConv, Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hint := sum_divisors_moebius n
  have hreal : ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)
      = ((if n = 1 then (1 : ℤ) else 0 : ℤ) : ℝ) := by
    rw [← hint]
    push_cast
    rfl
  rw [hreal, unitWeight]
  by_cases h1 : n = 1
  · subst h1
    norm_num
  · simp [h1]

/-- **(24.25) The weighted floor transform is exactly invertible for every exponent.** -/
theorem floorTransform_moebiusPower_power (theta : ℝ) (f : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    floorTransform (moebiusPowerWeight theta) (floorTransform (powerWeight theta) f) N = f N := by
  classical
  have hcomp := floorTransform_comp (moebiusPowerWeight theta) (powerWeight theta) f N
  have hfun : floorTransform (dirichletConv (moebiusPowerWeight theta) (powerWeight theta)) f N
      = floorTransform unitWeight f N := by
    rw [floorTransform, floorTransform]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_Icc] at hd
    rw [dirichletConv_moebiusPower_power theta (show d ≠ 0 by omega)]
  rw [hcomp, hfun, floorTransform_unitWeight f hN]

/-! ## Stability above the threshold -/

theorem abs_powerWeight_le {theta : ℝ} {d : ℕ} (hd : 1 ≤ d) :
    |powerWeight theta d| ≤ (d : ℝ) ^ (-theta) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [powerWeight, abs_of_nonneg (Real.rpow_nonneg hdpos.le _)]

theorem abs_moebiusPowerWeight_le {theta : ℝ} {d : ℕ} (hd : 1 ≤ d) :
    |moebiusPowerWeight theta d| ≤ (d : ℝ) ^ (-theta) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
    have hint := ArithmeticFunction.abs_moebius_le_one (n := d)
    have hcast : |(ArithmeticFunction.moebius d : ℝ)|
        = ((|ArithmeticFunction.moebius d| : ℤ) : ℝ) := by
      push_cast
      rfl
    rw [hcast]
    exact_mod_cast hint
  rw [moebiusPowerWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg hdpos.le _)]
  calc |(ArithmeticFunction.moebius d : ℝ)| * (d : ℝ) ^ (-theta)
      ≤ 1 * (d : ℝ) ^ (-theta) :=
        mul_le_mul_of_nonneg_right hmu (Real.rpow_nonneg hdpos.le _)
    _ = (d : ℝ) ^ (-theta) := one_mul _

/-- **(24.26) The weighted transform of a critically bounded profile.** -/
theorem abs_floorTransform_le_of_powerBound {w Q : ℕ → ℝ} {C ε theta : ℝ} (hC : 0 ≤ C)
    (hε : 0 ≤ ε) (_htheta : 0 ≤ theta)
    (hw : ∀ d : ℕ, 1 ≤ d → |w d| ≤ (d : ℝ) ^ (-theta))
    (hQ : ∀ M : ℕ, 1 ≤ M → |Q M| ≤ C * (M : ℝ) ^ (1 / 2 + ε)) {N : ℕ} (hN : 1 ≤ N) :
    |floorTransform w Q N|
      ≤ C * (N : ℝ) ^ (1 / 2 + ε)
          * ∑ d ∈ Finset.Icc 1 N, (d : ℝ) ^ (-(theta + 1 / 2 + ε)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [floorTransform]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  obtain ⟨hd1, hdN⟩ := hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have hquot : 1 ≤ N / d := (Nat.one_le_div_iff hd1).2 hdN
  have hQd := hQ (N / d) hquot
  have hcast : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
  have hrp : ((N / d : ℕ) : ℝ) ^ (1 / 2 + ε) ≤ ((N : ℝ) / (d : ℝ)) ^ (1 / 2 + ε) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hcast (by linarith)
  have hsplit : ((N : ℝ) / (d : ℝ)) ^ (1 / 2 + ε)
      = (N : ℝ) ^ (1 / 2 + ε) * ((d : ℝ) ^ (1 / 2 + ε))⁻¹ := by
    rw [Real.div_rpow hNpos.le hdpos.le]
    ring
  have hpow : (d : ℝ) ^ (-theta) * ((d : ℝ) ^ (1 / 2 + ε))⁻¹
      = (d : ℝ) ^ (-(theta + 1 / 2 + ε)) := by
    rw [← Real.rpow_neg hdpos.le, ← Real.rpow_add hdpos]
    congr 1
    ring
  calc |w d * Q (N / d)| = |w d| * |Q (N / d)| := abs_mul _ _
    _ ≤ (d : ℝ) ^ (-theta) * (C * ((N / d : ℕ) : ℝ) ^ (1 / 2 + ε)) :=
        mul_le_mul (hw d hd1) hQd (abs_nonneg _) (Real.rpow_nonneg hdpos.le _)
    _ ≤ (d : ℝ) ^ (-theta) * (C * ((N : ℝ) / (d : ℝ)) ^ (1 / 2 + ε)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrp hC)
          (Real.rpow_nonneg hdpos.le _)
    _ = C * (N : ℝ) ^ (1 / 2 + ε) * ((d : ℝ) ^ (-theta) * ((d : ℝ) ^ (1 / 2 + ε))⁻¹) := by
        rw [hsplit]
        ring
    _ = C * (N : ℝ) ^ (1 / 2 + ε) * (d : ℝ) ^ (-(theta + 1 / 2 + ε)) := by rw [hpow]

theorem summable_powerMajorant {theta ε : ℝ} (h : 1 / 2 < theta + ε) :
    Summable (fun d : ℕ => (d : ℝ) ^ (-(theta + 1 / 2 + ε))) := by
  have hstep : Summable (fun d : ℕ => ((d : ℝ) ^ (theta + 1 / 2 + ε))⁻¹) :=
    Real.summable_nat_rpow_inv.2 (by linarith)
  refine hstep.congr fun d => ?_
  rw [Real.rpow_neg (Nat.cast_nonneg d)]

theorem abs_floorTransform_le_tsum_powerMajorant {w Q : ℕ → ℝ} {C ε theta : ℝ} (hC : 0 ≤ C)
    (hε : 0 ≤ ε) (htheta : 0 ≤ theta) (hcrit : 1 / 2 < theta + ε)
    (hw : ∀ d : ℕ, 1 ≤ d → |w d| ≤ (d : ℝ) ^ (-theta))
    (hQ : ∀ M : ℕ, 1 ≤ M → |Q M| ≤ C * (M : ℝ) ^ (1 / 2 + ε)) {N : ℕ} (hN : 1 ≤ N) :
    |floorTransform w Q N|
      ≤ (C * ∑' d : ℕ, (d : ℝ) ^ (-(theta + 1 / 2 + ε))) * (N : ℝ) ^ (1 / 2 + ε) := by
  have hsum := summable_powerMajorant hcrit
  have hle : ∑ d ∈ Finset.Icc 1 N, (d : ℝ) ^ (-(theta + 1 / 2 + ε))
      ≤ ∑' d : ℕ, (d : ℝ) ^ (-(theta + 1 / 2 + ε)) :=
    Summable.sum_le_tsum _ (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) _) hsum
  have hbase := abs_floorTransform_le_of_powerBound hC hε htheta hw hQ hN
  have hNrpow : (0 : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hstep := mul_le_mul_of_nonneg_left hle (mul_nonneg hC hNrpow)
  refine hbase.trans (hstep.trans (le_of_eq ?_))
  ring

/-- **(24.27) Above the threshold the forward transform preserves the critical exponent.** -/
theorem abs_floorTransform_power_le {Q : ℕ → ℝ} {C ε theta : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (htheta : 0 ≤ theta) (hcrit : 1 / 2 < theta + ε)
    (hQ : ∀ M : ℕ, 1 ≤ M → |Q M| ≤ C * (M : ℝ) ^ (1 / 2 + ε)) {N : ℕ} (hN : 1 ≤ N) :
    |floorTransform (powerWeight theta) Q N|
      ≤ (C * ∑' d : ℕ, (d : ℝ) ^ (-(theta + 1 / 2 + ε))) * (N : ℝ) ^ (1 / 2 + ε) :=
  abs_floorTransform_le_tsum_powerMajorant hC hε htheta hcrit
    (fun _ hd => abs_powerWeight_le hd) hQ hN

/-- **(24.27) Above the threshold the inverse transform preserves the critical exponent.** -/
theorem abs_floorTransform_moebiusPower_le {Q : ℕ → ℝ} {C ε theta : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (htheta : 0 ≤ theta) (hcrit : 1 / 2 < theta + ε)
    (hQ : ∀ M : ℕ, 1 ≤ M → |Q M| ≤ C * (M : ℝ) ^ (1 / 2 + ε)) {N : ℕ} (hN : 1 ≤ N) :
    |floorTransform (moebiusPowerWeight theta) Q N|
      ≤ (C * ∑' d : ℕ, (d : ℝ) ^ (-(theta + 1 / 2 + ε))) * (N : ℝ) ^ (1 / 2 + ε) :=
  abs_floorTransform_le_tsum_powerMajorant hC hε htheta hcrit
    (fun _ hd => abs_moebiusPowerWeight_le hd) hQ hN

/-! ## Sharpness of the threshold -/

/-- The model profile `f(M) = √M`. -/
def sqrtProfile (M : ℕ) : ℝ := Real.sqrt M

theorem model_lower_eq {M : ℕ} (hM : 1 ≤ M) (theta x : ℝ) :
    (M : ℝ) * ((M : ℝ) ^ (-theta) * (x / (Real.sqrt 2 * Real.sqrt M)))
      = x / Real.sqrt 2 * (M : ℝ) ^ (1 / 2 - theta) := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hs : Real.sqrt (M : ℝ) = (M : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  have hsne : ((M : ℝ) ^ ((1 : ℝ) / 2)) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hMpos _)
  have h2ne : Real.sqrt 2 ≠ 0 := by positivity
  have hsqrtM : Real.sqrt (M : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hMpos)
  have hcomb1 : (M : ℝ) * (M : ℝ) ^ (-theta) = (M : ℝ) ^ (1 - theta) := by
    nth_rewrite 1 [show (M : ℝ) = (M : ℝ) ^ (1 : ℝ) from (Real.rpow_one _).symm]
    rw [← Real.rpow_add hMpos]
    congr 1
  have hcomb2 : (M : ℝ) ^ (1 / 2 - theta) * (M : ℝ) ^ ((1 : ℝ) / 2) = (M : ℝ) ^ (1 - theta) := by
    rw [← Real.rpow_add hMpos]
    congr 1
    ring
  have hLHS : (M : ℝ) * ((M : ℝ) ^ (-theta) * (x / (Real.sqrt 2 * Real.sqrt M)))
      = (M : ℝ) * (M : ℝ) ^ (-theta) * x / (Real.sqrt 2 * Real.sqrt M) := by ring
  have hRHS : x / Real.sqrt 2 * (M : ℝ) ^ (1 / 2 - theta)
      = (M : ℝ) ^ (1 / 2 - theta) * Real.sqrt M * x / (Real.sqrt 2 * Real.sqrt M) := by
    field_simp
  rw [hLHS, hRHS, hs, hcomb1, hcomb2]

/-- **(24.28) Below the threshold the model profile already blows up after critical
normalization.** -/
theorem model_lower_le_floorTransform_sqrtProfile {theta : ℝ} (htheta : 0 ≤ theta) {N : ℕ}
    (hN : 2 ≤ N) :
    Real.sqrt N / Real.sqrt 2 * ((N / 2 : ℕ) : ℝ) ^ (1 / 2 - theta)
      ≤ floorTransform (powerWeight theta) sqrtProfile N := by
  set M := N / 2 with hMdef
  have hM1 : 1 ≤ M := (Nat.one_le_div_iff (by norm_num)).2 hN
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hMN : M ≤ N := Nat.div_le_self N 2
  have hterm : ∀ d ∈ Finset.Icc 1 M,
      (M : ℝ) ^ (-theta) * (Real.sqrt N / (Real.sqrt 2 * Real.sqrt M))
        ≤ powerWeight theta d * sqrtProfile (N / d) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    obtain ⟨hd1, hdM⟩ := hd
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    have hdMR : (d : ℝ) ≤ (M : ℝ) := by exact_mod_cast hdM
    have hq1 : 1 ≤ N / d := (Nat.one_le_div_iff hd1).2 (le_trans hdM hMN)
    have hqR : (1 : ℝ) ≤ ((N / d : ℕ) : ℝ) := by exact_mod_cast hq1
    have hlt : (N : ℝ) < (d : ℝ) * (((N / d : ℕ) : ℝ) + 1) := by
      exact_mod_cast Nat.lt_mul_div_succ N hd1
    have hkey : (N : ℝ) ≤ 2 * (d : ℝ) * ((N / d : ℕ) : ℝ) := by nlinarith
    have hlow : (N : ℝ) / (2 * (d : ℝ)) ≤ ((N / d : ℕ) : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hsqrt : Real.sqrt ((N : ℝ) / (2 * (d : ℝ))) ≤ sqrtProfile (N / d) := by
      rw [sqrtProfile]
      exact Real.sqrt_le_sqrt hlow
    have hsplit : Real.sqrt ((N : ℝ) / (2 * (d : ℝ)))
        = Real.sqrt N / (Real.sqrt 2 * Real.sqrt d) := by
      rw [Real.sqrt_div (Nat.cast_nonneg N), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hA : (M : ℝ) ^ (-theta) ≤ (d : ℝ) ^ (-theta) :=
      Real.rpow_le_rpow_of_nonpos hdpos hdMR (by linarith)
    have hB : Real.sqrt N / (Real.sqrt 2 * Real.sqrt M)
        ≤ Real.sqrt N / (Real.sqrt 2 * Real.sqrt d) := by
      refine div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) ?_
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdMR) (Real.sqrt_nonneg 2)
    calc (M : ℝ) ^ (-theta) * (Real.sqrt N / (Real.sqrt 2 * Real.sqrt M))
        ≤ (d : ℝ) ^ (-theta) * (Real.sqrt N / (Real.sqrt 2 * Real.sqrt d)) :=
          mul_le_mul hA hB (by positivity) (Real.rpow_nonneg hdpos.le _)
      _ ≤ powerWeight theta d * sqrtProfile (N / d) := by
          rw [powerWeight]
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hdpos.le _)
          rw [← hsplit]
          exact hsqrt
  have hsub : Finset.Icc 1 M ⊆ Finset.Icc 1 N := by
    intro d hd
    rw [Finset.mem_Icc] at hd ⊢
    exact ⟨hd.1, le_trans hd.2 hMN⟩
  have hnonneg : ∀ d ∈ Finset.Icc 1 N, d ∉ Finset.Icc 1 M →
      0 ≤ powerWeight theta d * sqrtProfile (N / d) := by
    intro d hd _
    rw [Finset.mem_Icc] at hd
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd.1
    exact mul_nonneg (Real.rpow_nonneg hdpos.le _) (Real.sqrt_nonneg _)
  calc Real.sqrt N / Real.sqrt 2 * (M : ℝ) ^ (1 / 2 - theta)
      = (M : ℝ) * ((M : ℝ) ^ (-theta) * (Real.sqrt N / (Real.sqrt 2 * Real.sqrt M))) :=
        (model_lower_eq hM1 theta (Real.sqrt N)).symm
    _ = ∑ _d ∈ Finset.Icc 1 M,
          (M : ℝ) ^ (-theta) * (Real.sqrt N / (Real.sqrt 2 * Real.sqrt M)) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ ≤ ∑ d ∈ Finset.Icc 1 M, powerWeight theta d * sqrtProfile (N / d) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ d ∈ Finset.Icc 1 N, powerWeight theta d * sqrtProfile (N / d) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
    _ = floorTransform (powerWeight theta) sqrtProfile N := rfl

/-- **(24.28) Sharpness: below the critical exponent the weighted floor transform of the model
profile is unbounded after critical normalization.** -/
theorem not_bounded_normalized_floorTransform_sqrtProfile {theta : ℝ} (htheta : 0 ≤ theta)
    (hlt : theta < 1 / 2) :
    ¬ ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      floorTransform (powerWeight theta) sqrtProfile N ≤ C * Real.sqrt N := by
  rintro ⟨C, hC⟩
  have hexp : (0 : ℝ) < 1 / 2 - theta := by linarith
  have htend : Filter.Tendsto (fun K : ℕ => (K : ℝ) ^ (1 / 2 - theta))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop
  obtain ⟨K, hKgt, hK1⟩ :=
    ((htend.eventually_gt_atTop (C * Real.sqrt 2)).and (Filter.eventually_ge_atTop 1)).exists
  have hN2 : 2 ≤ 2 * K := by omega
  have hdiv : (2 * K) / 2 = K := Nat.mul_div_cancel_left K (by norm_num)
  have hlow := model_lower_le_floorTransform_sqrtProfile (theta := theta) htheta hN2
  rw [hdiv] at hlow
  have hchain : Real.sqrt (2 * K : ℕ) / Real.sqrt 2 * (K : ℝ) ^ (1 / 2 - theta)
      ≤ C * Real.sqrt (2 * K : ℕ) := le_trans hlow (hC (2 * K) hN2)
  have hNpos : (0 : ℝ) < Real.sqrt ((2 * K : ℕ) : ℝ) := by
    refine Real.sqrt_pos.2 ?_
    have : (0 : ℕ) < 2 * K := by omega
    exact_mod_cast this
  have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hchain' : Real.sqrt ((2 * K : ℕ) : ℝ) * (K : ℝ) ^ (1 / 2 - theta) / Real.sqrt 2
      ≤ C * Real.sqrt ((2 * K : ℕ) : ℝ) := by
    calc Real.sqrt ((2 * K : ℕ) : ℝ) * (K : ℝ) ^ (1 / 2 - theta) / Real.sqrt 2
        = Real.sqrt ((2 * K : ℕ) : ℝ) / Real.sqrt 2 * (K : ℝ) ^ (1 / 2 - theta) := by ring
      _ ≤ C * Real.sqrt ((2 * K : ℕ) : ℝ) := hchain
  rw [div_le_iff₀ h2] at hchain'
  have hrew : C * Real.sqrt ((2 * K : ℕ) : ℝ) * Real.sqrt 2
      = Real.sqrt ((2 * K : ℕ) : ℝ) * (C * Real.sqrt 2) := by ring
  rw [hrew] at hchain'
  have hfin := le_of_mul_le_mul_left hchain' hNpos
  linarith

/-- **(24.28) Above the threshold the model profile stays critically bounded.** -/
theorem floorTransform_sqrtProfile_le {theta : ℝ} (htheta : 0 ≤ theta) (hcrit : 1 / 2 < theta)
    {N : ℕ} (hN : 1 ≤ N) :
    floorTransform (powerWeight theta) sqrtProfile N
      ≤ (∑' d : ℕ, (d : ℝ) ^ (-(theta + 1 / 2 + (0 : ℝ)))) * (N : ℝ) ^ (1 / 2 + (0 : ℝ)) := by
  have hQ : ∀ M : ℕ, 1 ≤ M → |sqrtProfile M| ≤ 1 * (M : ℝ) ^ (1 / 2 + (0 : ℝ)) := by
    intro M _
    rw [sqrtProfile, abs_of_nonneg (Real.sqrt_nonneg _), one_mul, Real.sqrt_eq_rpow]
    norm_num
  have hmain := abs_floorTransform_le_tsum_powerMajorant (w := powerWeight theta)
    (Q := sqrtProfile) (C := 1) (ε := 0) (theta := theta) zero_le_one le_rfl htheta
    (by linarith) (fun _ hd => abs_powerWeight_le hd) hQ hN
  rw [one_mul] at hmain
  exact le_trans (le_abs_self _) hmain

/-- The leading term already gives the matching lower bound. -/
theorem sqrt_le_floorTransform_sqrtProfile (theta : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    Real.sqrt N ≤ floorTransform (powerWeight theta) sqrtProfile N := by
  have hmem : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.2 ⟨le_rfl, hN⟩
  have hnn : ∀ d ∈ Finset.Icc 1 N, 0 ≤ powerWeight theta d * sqrtProfile (N / d) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd.1
    exact mul_nonneg (Real.rpow_nonneg hdpos.le _) (Real.sqrt_nonneg _)
  have hterm : powerWeight theta 1 * sqrtProfile (N / 1) = Real.sqrt N := by
    rw [powerWeight, sqrtProfile, Nat.div_one, Nat.cast_one, Real.one_rpow, one_mul]
  rw [floorTransform]
  calc Real.sqrt N = powerWeight theta 1 * sqrtProfile (N / 1) := hterm.symm
    _ ≤ ∑ d ∈ Finset.Icc 1 N, powerWeight theta d * sqrtProfile (N / d) :=
        Finset.single_le_sum hnn hmem

end

end RHTower
