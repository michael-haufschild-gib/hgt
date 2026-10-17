import GaloisForLFunctions.RHTower.NullRayDilationSpectral

/-!
# Criticality of the twisted-arc null ray under node dilation

Let `G₀ = Σ_j w_j F_j ⋆ F̃_j` be the null ray of a null family (`NullFamily`), for instance the
twisted-arc family of the twisted minimum principle (`exists_nullFamily_xiShiftedGamma`).  It is
prime-blind at every `log n`, so `G₀(·/t)` is prime-blind at the dilated nodes `t log n`, and its
spectral density `t R(tr)` is nonnegative (`nullRay_div_eq_stripTest`, `dil_nullDensity_ofReal`).
Let `a(t)` be the pole and archimedean energy of `G₀(·/t)` (`dilatedEnergy`; by `nullRay_div_eq`,
`G₀(·/t) = (1/t) Σ_j w_j F_{j,t} ⋆ F̃_{j,t}` with `F_{j,t} = F_j(·/t)`).

**Theorem** (`NullFamily.dilatedEnergy_one`, `NullFamily.hasDerivAt_dilatedEnergy`).  `a(1) = 0` and
`a′(1) = −2S` with `S = Σ_n Λ(n) n^{−1/2} log n · G₀′(log n)` (`nullRaySlope`).

**Corollary** (`NullFamily.dilatedEnergy_neg`).  If `S ≠ 0`, then `a(t) < 0` for every `t` close to
`1` with `(t − 1) S > 0`: the null ray breaks positivity of the dilated blind cone on one side of
`t = 1`, the side being fixed by the sign of `S`.

**Proof.**  By the explicit formula of the decay class (`archPoleEnergy_eq_re_W_add_abelPrimePairing`),
for `3/4 ≤ t ≤ 17/16` one has `a(t) = Z(t) + P(t)` (`dilatedEnergy_eq`) with the zero side
`Z(t) = (1/t) Σ_j w_j Re W(F_{j,t}, F_{j,t})` and the prime side
`P(t) = 2 Σ_n Λ(n) n^{−1/2} G₀(log n / t)`.  The transform of `F_{j,t}` at a zero is `t Φ_j(tγ_ρ)`, which
vanishes at `t = 1`; a Cauchy estimate for `(zΦ_j)′` and the mean value theorem give
`(1 + |Re γ|)|tΦ_j(tγ)| ≤ |t − 1| B C_j` (`norm_dil_le_of_zero`), so `|Z(t)| ≤ K (t − 1)²` and
`Z′(1) = 0`.  The prime side is differentiated termwise with `|G₀′(y)| ≤ K e^{−9|y|/8}`; it vanishes at
`t = 1` by blindness and has derivative `−2S` there.
-/

open Complex MeasureTheory Set Filter Topology Zeta23 Asymptotics Metric
open scoped ComplexConjugate Nat

noncomputable section

namespace RHTower.NullRayDilation

open WeilOneSided WeilSpectral EvenSector

variable {Φ : ℕ → ℂ → ℂ} {w : ℕ → ℝ} {ε : ℝ} {c : ℕ → ℝ}

/-! ## The dilated energy and the criticality number -/

/-- The pole and archimedean energy `a(t)` of the dilated null ray `G₀(·/t)`. -/
def dilatedEnergy (Φ : ℕ → ℂ → ℂ) (w : ℕ → ℝ) (t : ℝ) : ℝ :=
  1 / t * ∑' j, w j * archPoleEnergy (stripTest (dil t (Φ j)))

/-- The criticality number `S = Σ_n Λ(n) n^{−1/2} log n · G₀′(log n)`. -/
def nullRaySlope (Φ : ℕ → ℂ → ℂ) (w : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n * Real.log n *
    deriv (nullRay Φ w) (Real.log n)

/-- `G₀(·/t) = (1/t) Σ_j w_j F_{j,t} ⋆ F̃_{j,t}`. -/
theorem nullRay_div_eq (Φ : ℕ → ℂ → ℂ) (w : ℕ → ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    nullRay Φ w (x / t) =
      1 / t * ∑' j, w j * crossCorr (stripTest (dil t (Φ j))) (stripTest (dil t (Φ j))) x := by
  unfold nullRay
  simp_rw [crossCorr_stripTest_dil _ ht]
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [mul_left_comm (w j), ← mul_assoc, one_div, inv_mul_cancel₀ ht.ne', one_mul]

/-- The dilated null ray is the strip test of the dilated density. -/
theorem NullFamily.nullRay_div_eq_stripTest (hN : NullFamily Φ w ε c) {t : ℝ} (ht : 0 < t)
    (x : ℝ) : nullRay Φ w (x / t) = stripTest (dil t (nullDensity Φ w)) x := by
  rw [hN.nullRay_eq_stripTest, stripTest_dil _ ht]

/-- The dilated density is `t Σ_j w_j |Φ_j(tr)|² ≥ 0` on the real line. -/
theorem dil_nullDensity_ofReal (Φ : ℕ → ℂ → ℂ) (w : ℕ → ℝ) (t r : ℝ) :
    dil t (nullDensity Φ w) r = ((t * ∑' j, w j * ‖Φ j ((t * r : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
  unfold dil
  rw [show (t : ℂ) * (r : ℂ) = ((t * r : ℝ) : ℂ) by push_cast; ring, nullDensity_ofReal,
    ← ofReal_mul]

/-- The dilated null ray is blind at the dilated nodes `t log n`. -/
theorem NullFamily.nullRay_dilated_node (hN : NullFamily Φ w ε c) {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn : 2 ≤ n) : nullRay Φ w (t * Real.log n / t) = 0 := by
  rw [mul_div_cancel_left₀ _ ht.ne']
  exact hN.nullRay_log hn

/-! ## The window `3/4 ≤ t ≤ 17/16` -/

theorem NullFamily.stripDecay_dil_window (hN : NullFamily Φ w ε c) (j : ℕ) {t : ℝ}
    (ht : t ∈ Icc (3 / 4 : ℝ) (17 / 16)) :
    StripDecay (dil t (Φ j)) (9 / 8) (ε / 2) (2 * c j) := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hε := hN.rate
  have hc := hN.const_nonneg j
  refine stripDecay_mono (stripDecay_dil (hN.strip j) ht0) ?_ (by norm_num) ?_ ?_
  · rw [le_div_iff₀ ht0]; nlinarith [ht.2]
  · nlinarith [ht.1]
  · nlinarith [ht.2]

theorem vonMangoldt_ite_div (n : ℕ) :
    (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0) =
      (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n := by
  split_ifs with h
  · rfl
  · interval_cases n <;> simp

theorem abs_vonMangoldt_le (n : ℕ) (_ : 2 ≤ n) :
    |(ArithmeticFunction.vonMangoldt n : ℝ)| ≤ 1 * Real.sqrt n * (1 + Real.log n) := by
  rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, one_mul]
  have hlog : ArithmeticFunction.vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  have hl0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hs : 1 ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]; exact_mod_cast (by omega : 1 ≤ n)
  nlinarith

/-- The prime pairing of the autocorrelation is its Abel form for tests decaying faster than
`e^{−|x|}`. -/
theorem atomPairing_eq_abelPrimePairing_of_decay {F : ℝ → ℝ} (hE : ExpDecayTest F) {C b : ℝ}
    (hb : 1 < b) (hC : 0 ≤ C) (hdec : ∀ x, |F x| ≤ C * Real.exp (-(b * |x|))) :
    atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (crossCorr F F) =
      abelPrimePairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) F :=
  tendsto_nhds_unique (tendsto_atomPairing_truncTest_of_growth abs_vonMangoldt_le hE hb hC hdec)
    (tendsto_atomPairing_truncTest_abelPrimePairing hE (A := 7)
      (fun N => abs_primeWeightPartialSum_vonMangoldt_le N))

/-- **The explicit formula for a dilated member of the family.** -/
theorem NullFamily.archPoleEnergy_dil_eq (hN : NullFamily Φ w ε c) (j : ℕ) {t : ℝ}
    (ht : t ∈ Icc (3 / 4 : ℝ) (17 / 16)) :
    archPoleEnergy (stripTest (dil t (Φ j))) =
      (zetaZeroConfig.W (fun u => (stripTest (dil t (Φ j)) u : ℂ))
        (fun u => (stripTest (dil t (Φ j)) u : ℂ))).re +
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
        (2 * t * crossCorr (stripTest (Φ j)) (stripTest (Φ j)) (Real.log n / t)) := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hs := hN.stripDecay_dil_window j ht
  have hε2 : 0 < ε / 2 := by linarith [hN.rate]
  have hE := expDecayTest_stripTest (by norm_num : (1 / 2 : ℝ) < 9 / 8) hε2 hs
  obtain ⟨-, hC', hdec⟩ := decayBound_stripTest (by norm_num : (1 / 2 : ℝ) < 9 / 8) hε2 hs
  have hdec' : ∀ x, |stripTest (dil t (Φ j)) x| ≤
      2 * c j * stripDecayConst (9 / 8) (ε / 2) * Real.exp (-(9 / 8 * |x|)) := fun x => by
    have hx := (hdec x).1
    rwa [show (1 / 2 : ℝ) + (9 / 8 - 1 / 2) = 9 / 8 by ring] at hx
  rw [archPoleEnergy_eq_re_W_add_abelPrimePairing hE,
    ← atomPairing_eq_abelPrimePairing_of_decay hE (by norm_num : (1 : ℝ) < 9 / 8) hC' hdec']
  congr 1
  unfold atomPairing
  refine tsum_congr fun n => ?_
  rw [vonMangoldt_ite_div n, crossCorr_self_neg, crossCorr_stripTest_dil _ ht0]
  ring

/-! ## Elementary bounds -/

theorem exp_neg_mul_abs_log_div_le {a t : ℝ} (ha : 0 ≤ a) (ht : t ∈ Icc (3 / 4 : ℝ) (17 / 16))
    {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-(a * |Real.log n / t|)) ≤ (n : ℝ) ^ (-(16 * a / 17)) := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hl0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  rw [abs_of_nonneg (div_nonneg hl0 ht0.le), Real.rpow_def_of_pos hn0]
  refine Real.exp_le_exp.mpr ?_
  have h1 : 16 / 17 * Real.log n ≤ Real.log n / t := by
    rw [le_div_iff₀ ht0]; nlinarith [ht.2]
  nlinarith

theorem vonMangoldt_div_sqrt_le (n : ℕ) :
    (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n ≤ Real.log n * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.sqrt_eq_rpow, Real.rpow_neg hn0.le, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log
    (inv_nonneg.mpr (Real.rpow_nonneg hn0.le _))

theorem vonMangoldt_div_sqrt_nonneg (n : ℕ) :
    0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

theorem rpow_mul_rpow_le_three_halves {n : ℕ} (hn : 1 ≤ n) {b : ℝ} (hb : 1 ≤ b) :
    (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-b) ≤ (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [← Real.rpow_add (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)

theorem log_sq_le (n : ℕ) : Real.log n ^ 2 ≤ 64 * (n : ℝ) ^ (1 / 4 : ℝ) := by
  have hl0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have h := Real.log_le_rpow_div (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) < 1 / 8)
  have h8 : Real.log n ≤ 8 * (n : ℝ) ^ (1 / 8 : ℝ) := by
    rw [div_eq_mul_inv] at h; norm_num at h; linarith
  have hsq : ((n : ℝ) ^ (1 / 8 : ℝ)) ^ 2 = (n : ℝ) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]; norm_num
  calc Real.log n ^ 2 ≤ (8 * (n : ℝ) ^ (1 / 8 : ℝ)) ^ 2 := pow_le_pow_left₀ hl0 h8 2
    _ = 64 * (n : ℝ) ^ (1 / 4 : ℝ) := by rw [mul_pow, hsq]; norm_num

/-! ## The prime side -/

/-- The prime side `P(t) = 2 Σ_n Λ(n) n^{−1/2} G₀(log n / t)`. -/
def primePart (Φ : ℕ → ℂ → ℂ) (w : ℕ → ℝ) (t : ℝ) : ℝ :=
  2 * ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
    nullRay Φ w (Real.log n / t)

/-- The joint majorant of the prime side. -/
theorem NullFamily.abs_term_le (hN : NullFamily Φ w ε c) (j n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (3 / 4 : ℝ) (17 / 16)) :
    |(ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
        crossCorr (stripTest (Φ j)) (stripTest (Φ j)) (Real.log n / t)| ≤
      c j ^ 2 * invConst (2 * ε) * ((1 + Real.log n) * (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
  have hK := invConst_nonneg (2 * ε)
  have hl0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 := by simp
    rw [h0, zero_div, zero_mul, abs_zero]
    have h1 : (0 : ℝ) ≤ ((0 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by simp) _
    exact mul_nonneg (mul_nonneg (sq_nonneg _) hK) (mul_nonneg (by linarith) h1)
  have hcc := abs_crossCorr_stripTest_le hN.rate (hN.strip j) (hN.sym j) (Real.log n / t)
  have he := exp_neg_mul_abs_log_div_le (a := 5 / 4) (by norm_num) ht hn
  have hp := rpow_mul_rpow_le_three_halves hn (b := 16 * (5 / 4) / 17) (by norm_num)
  have hv := vonMangoldt_div_sqrt_le n
  have hv0 := vonMangoldt_div_sqrt_nonneg n
  have hr0 : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hr1 : 0 ≤ (n : ℝ) ^ (-(16 * (5 / 4) / 17 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  rw [abs_mul, abs_of_nonneg hv0]
  calc (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
        |crossCorr (stripTest (Φ j)) (stripTest (Φ j)) (Real.log n / t)|
      ≤ (Real.log n * (n : ℝ) ^ (-(1 / 2 : ℝ))) *
          (c j ^ 2 * invConst (2 * ε) * (n : ℝ) ^ (-(16 * (5 / 4) / 17 : ℝ))) := by
        refine mul_le_mul hv (hcc.trans ?_) (abs_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left he (by positivity)
    _ = c j ^ 2 * invConst (2 * ε) * (Real.log n *
          ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(16 * (5 / 4) / 17 : ℝ)))) := by ring
    _ ≤ c j ^ 2 * invConst (2 * ε) * ((1 + Real.log n) * (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h3 : 0 ≤ (n : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
        calc Real.log n * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(16 * (5 / 4) / 17 : ℝ)))
            ≤ Real.log n * (n : ℝ) ^ (-(3 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hp hl0
          _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) h3

theorem summable_one_add_log_mul_three_halves :
    Summable fun n : ℕ => (1 + Real.log n) * (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
  summable_one_add_log_mul_rpow (by norm_num)

/-! ## The zero side vanishes to second order -/

/-- Cauchy estimate for `(zΨ)′` inside the strip. -/
theorem norm_deriv_mul_self_le {Ψ : ℂ → ℂ} {ε C : ℝ} (hε : 0 ≤ ε) (hΨ : StripDecay Ψ (5 / 4) ε C)
    {z : ℂ} (hz : |z.im| ≤ 17 / 32) :
    ‖deriv (fun u => u * Ψ u) z‖ ≤
      2 * ((|z.re| + 2) * (C * (Real.exp (ε / 2) * Real.exp (-(ε * |z.re|))))) := by
  have hC := hΨ.const_nonneg (by norm_num)
  have hR : (0 : ℝ) < 1 / 2 := by norm_num
  have hmem : ∀ u ∈ closedBall z (1 / 2),
      |u.im| ≤ 5 / 4 ∧ |z.re| - 1 / 2 ≤ |u.re| ∧ ‖u‖ ≤ |z.re| + 2 := by
    intro u hu
    rw [mem_closedBall, dist_eq_norm] at hu
    have h1 := Complex.abs_im_le_norm (u - z)
    have h2 := Complex.abs_re_le_norm (u - z)
    rw [Complex.sub_im] at h1
    rw [Complex.sub_re] at h2
    have h3 := Complex.norm_le_abs_re_add_abs_im u
    have a1 := abs_sub_abs_le_abs_sub u.im z.im
    have a2 := abs_sub_abs_le_abs_sub z.re u.re
    have a3 := abs_sub_abs_le_abs_sub u.re z.re
    rw [abs_sub_comm] at a2
    refine ⟨?_, by linarith, ?_⟩
    · linarith
    · linarith
  have hdiff : DifferentiableOn ℂ (fun u => u * Ψ u) (closure (ball z (1 / 2))) := by
    rw [closure_ball z hR.ne']
    intro u hu
    exact (differentiableAt_id.mul (hΨ.diff u (hmem u hu).1)).differentiableWithinAt
  have hb : ∀ u ∈ sphere z (1 / 2), ‖u * Ψ u‖ ≤
      (|z.re| + 2) * (C * (Real.exp (ε / 2) * Real.exp (-(ε * |z.re|)))) := by
    intro u hu
    obtain ⟨h1, h2, h3⟩ := hmem u (sphere_subset_closedBall hu)
    rw [norm_mul]
    refine mul_le_mul h3 ((hΨ.bound u h1).trans ?_) (norm_nonneg _) (by positivity)
    refine mul_le_mul_of_nonneg_left ?_ hC
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdiff.diffContOnCl hb
  refine this.trans (le_of_eq ?_)
  ring

/-- `(1 + x)² e^{−εx} ≤ 2 + 4/ε²`. -/
theorem one_add_sq_mul_exp_le {ε x : ℝ} (hε : 0 < ε) (hx : 0 ≤ x) :
    (1 + x) ^ 2 * Real.exp (-(ε * x)) ≤ 2 + 4 / ε ^ 2 := by
  have hq := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ ε * x)
  have he1 : 1 ≤ Real.exp (ε * x) := Real.one_le_exp (by positivity)
  have hx2 : x ^ 2 ≤ 2 / ε ^ 2 * Real.exp (ε * x) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [Real.exp_pos (ε * x)]
  have hsq : (1 + x) ^ 2 ≤ (2 + 4 / ε ^ 2) * Real.exp (ε * x) :=
    calc (1 + x) ^ 2 ≤ 2 + 2 * x ^ 2 := by nlinarith [sq_nonneg (1 - x)]
      _ ≤ 2 * Real.exp (ε * x) + 2 * (2 / ε ^ 2 * Real.exp (ε * x)) := by linarith
      _ = (2 + 4 / ε ^ 2) * Real.exp (ε * x) := by ring
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  exact hsq

/-- The dilation constant `B(ε) = 6 e^{ε/2} (2 + 4/ε²)`. -/
def dilConst (ε : ℝ) : ℝ := 6 * Real.exp (ε / 2) * (2 + 4 / ε ^ 2)

theorem dilConst_nonneg (ε : ℝ) : 0 ≤ dilConst ε := by
  unfold dilConst; positivity

/-- **Second-order vanishing at a zero.**  If `Ψ(γ) = 0` with `|Im γ| ≤ 1/2`, then
`(1 + |Re γ|) |tΨ(tγ)| ≤ |t − 1| B(ε) C` for `3/4 ≤ t ≤ 17/16`. -/
theorem norm_dil_le_of_zero {Ψ : ℂ → ℂ} {ε C : ℝ} (hε : 0 < ε) (hΨ : StripDecay Ψ (5 / 4) ε C)
    {γ : ℂ} (hγ : |γ.im| ≤ 1 / 2) (h0 : Ψ γ = 0) {t : ℝ} (ht : t ∈ Icc (3 / 4 : ℝ) (17 / 16)) :
    (1 + |γ.re|) * ‖(t : ℂ) * Ψ (t * γ)‖ ≤ |t - 1| * (dilConst ε * C) := by
  have hC := hΨ.const_nonneg (by norm_num)
  set K : ℂ → ℂ := fun u => u * Ψ u with hK
  set g : ℝ → ℂ := fun s => (s : ℂ) * Ψ (s * γ) with hg
  set D : ℝ := dilConst ε * C / (1 + |γ.re|) with hD
  have hγ1 : 0 < 1 + |γ.re| := by positivity
  have him : ∀ s ∈ Icc (3 / 4 : ℝ) (17 / 16), |((s : ℂ) * γ).im| ≤ 17 / 32 := by
    intro s hs
    have hs0 : 0 < s := by linarith [hs.1]
    rw [show ((s : ℂ) * γ).im = s * γ.im by simp, abs_mul, abs_of_pos hs0]
    nlinarith [hs.2, abs_nonneg γ.im]
  -- the derivative of `g`
  have hderiv : ∀ s ∈ Icc (3 / 4 : ℝ) (17 / 16), HasDerivAt g (deriv K (s * γ)) s := by
    intro s hs
    have hΨd := hΨ.diff _ ((him s hs).trans (by norm_num))
    have hKd : HasDerivAt K (1 * Ψ (s * γ) + (s * γ) * deriv Ψ (s * γ)) (s * γ) :=
      (hasDerivAt_id ((s : ℂ) * γ)).mul hΨd.hasDerivAt
    have h1 : HasDerivAt (fun u : ℂ => Ψ (u * γ)) (deriv Ψ (s * γ) * (1 * γ)) (s : ℂ) :=
      hΨd.hasDerivAt.comp (s : ℂ) ((hasDerivAt_id (s : ℂ)).mul_const γ)
    have he : HasDerivAt (fun u : ℂ => u * Ψ (u * γ))
        (1 * Ψ (s * γ) + (s : ℂ) * (deriv Ψ (s * γ) * (1 * γ))) (s : ℂ) :=
      (hasDerivAt_id (s : ℂ)).mul h1
    rw [hKd.deriv]
    convert he.comp_ofReal using 1
    ring
  -- the bound on the derivative
  have hbound : ∀ s ∈ Icc (3 / 4 : ℝ) (17 / 16), ‖deriv K (s * γ)‖ ≤ D := by
    intro s hs
    have hs0 : 0 < s := by linarith [hs.1]
    have hc := norm_deriv_mul_self_le hε.le hΨ (him s hs)
    set x : ℝ := |((s : ℂ) * γ).re| with hx
    have hx0 : 0 ≤ x := abs_nonneg _
    have hxe : x = s * |γ.re| := by
      rw [hx, show ((s : ℂ) * γ).re = s * γ.re by simp, abs_mul, abs_of_pos hs0]
    have hre : 1 + |γ.re| ≤ 4 / 3 * (1 + x) := by nlinarith [hs.1, abs_nonneg γ.re]
    have hq := one_add_sq_mul_exp_le hε hx0
    have hE : 0 ≤ Real.exp (ε / 2) := (Real.exp_pos _).le
    rw [hD, le_div_iff₀ hγ1]
    calc ‖deriv K (s * γ)‖ * (1 + |γ.re|)
        ≤ (2 * ((x + 2) * (C * (Real.exp (ε / 2) * Real.exp (-(ε * x)))))) *
            (4 / 3 * (1 + x)) :=
          mul_le_mul hc hre hγ1.le (by positivity)
      _ ≤ 16 / 3 * C * Real.exp (ε / 2) * ((1 + x) ^ 2 * Real.exp (-(ε * x))) := by
          have hP : 0 ≤ C * Real.exp (ε / 2) * Real.exp (-(ε * x)) := by positivity
          have e1 : 2 * ((x + 2) * (C * (Real.exp (ε / 2) * Real.exp (-(ε * x))))) *
              (4 / 3 * (1 + x)) = 8 / 3 * (x + 2) * (1 + x) *
                (C * Real.exp (ε / 2) * Real.exp (-(ε * x))) := by ring
          have e2 : 16 / 3 * C * Real.exp (ε / 2) * ((1 + x) ^ 2 * Real.exp (-(ε * x))) =
              16 / 3 * (1 + x) ^ 2 * (C * Real.exp (ε / 2) * Real.exp (-(ε * x))) := by ring
          rw [e1, e2]
          refine mul_le_mul_of_nonneg_right ?_ hP
          nlinarith
      _ ≤ 16 / 3 * C * Real.exp (ε / 2) * (2 + 4 / ε ^ 2) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
      _ ≤ dilConst ε * C := by
          unfold dilConst
          have : 0 ≤ C * Real.exp (ε / 2) * (2 + 4 / ε ^ 2) := by positivity
          nlinarith
  have hg1 : g 1 = 0 := by simp [hg, h0]
  have hD0 : 0 ≤ D := by rw [hD]; exact div_nonneg (mul_nonneg (dilConst_nonneg ε) hC) hγ1.le
  -- the mean value theorem
  have hmvt : ‖g t‖ ≤ D * |t - 1| := by
    rcases le_total 1 t with h | h
    · have := norm_image_sub_le_of_norm_deriv_le_segment' (f := g)
        (f' := fun s => deriv K (s * γ)) (a := 1) (b := t) (C := D)
        (fun s hs => (hderiv s ⟨by linarith [hs.1], by linarith [hs.2, ht.2]⟩).hasDerivWithinAt)
        (fun s hs => hbound s ⟨by linarith [hs.1], by linarith [hs.2, ht.2]⟩) t ⟨h, le_rfl⟩
      rw [hg1, sub_zero] at this
      rwa [abs_of_nonneg (by linarith)]
    · have := norm_image_sub_le_of_norm_deriv_le_segment' (f := g)
        (f' := fun s => deriv K (s * γ)) (a := t) (b := 1) (C := D)
        (fun s hs => (hderiv s ⟨by linarith [hs.1, ht.1], by linarith [hs.2]⟩).hasDerivWithinAt)
        (fun s hs => hbound s ⟨by linarith [hs.1, ht.1], by linarith [hs.2]⟩) 1 ⟨h, le_rfl⟩
      rw [hg1, zero_sub, norm_neg] at this
      rwa [abs_of_nonpos (by linarith), neg_sub]
  calc (1 + |γ.re|) * ‖(t : ℂ) * Ψ (t * γ)‖ = (1 + |γ.re|) * ‖g t‖ := rfl
    _ ≤ (1 + |γ.re|) * (D * |t - 1|) := mul_le_mul_of_nonneg_left hmvt hγ1.le
    _ = |t - 1| * (dilConst ε * C) := by rw [hD]; field_simp

/-- **The zero side of a dilated member is quadratically small.** -/
theorem NullFamily.norm_W_dil_le (hN : NullFamily Φ w ε c) (j : ℕ) {t : ℝ}
    (ht : t ∈ Icc (3 / 4 : ℝ) (17 / 16)) :
    ‖zetaZeroConfig.W (fun u => (stripTest (dil t (Φ j)) u : ℂ))
        (fun u => (stripTest (dil t (Φ j)) u : ℂ))‖ ≤
      5 / 4 * zetaInvSqSum * (|t - 1| * (dilConst ε * c j)) ^ 2 := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hε := hN.rate
  have hft : ∀ z : ℂ, |z.im| < 1 / 2 →
      paperFT (fun u => (stripTest (dil t (Φ j)) u : ℂ)) z = t * Φ j (t * z) := fun z hz =>
    paperFT_stripTest_dil (by norm_num) hε (hN.strip j) (hN.sym j) ht0 (by
      rw [lt_div_iff₀ ht0]; nlinarith [abs_nonneg z.im, ht.2])
  refine norm_W_le_of_zero_bound
    (mul_nonneg (abs_nonneg _) (mul_nonneg (dilConst_nonneg ε) (hN.const_nonneg j))) fun ρ => ?_
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hstrip : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := ⟨hmem.2.1, hmem.2.2⟩
  have hIm : |(gammaOf (ρ : ℂ)).im| < 1 / 2 := WeilEF.abs_gammaOf_im_lt hstrip
  have hre : (gammaOf (ρ : ℂ)).re = (ρ : ℂ).im := WeilEF.gammaOf_re _
  set ρ' : zetaZeroConfig.carrier := ⟨reflect (ρ : ℂ), zeta_reflect_zero _ hmem⟩
  have hg : gammaOf (ρ' : ℂ) = (starRingEnd ℂ) (gammaOf (ρ : ℂ)) := by
    show gammaOf (reflect (ρ : ℂ)) = _
    unfold gammaOf reflect
    apply Complex.ext
    · simp
    · simp; ring
  constructor
  · rw [hft _ hIm, ← hre]
    exact norm_dil_le_of_zero hε (hN.strip j) hIm.le (hN.zero j ρ) ht
  · have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| < 1 / 2 := by
      rw [Complex.conj_im, abs_neg]; exact hIm
    rw [hft _ hIm']
    have := norm_dil_le_of_zero hε (hN.strip j) (hg ▸ hIm'.le) (hN.zero j ρ') ht
    rwa [hg, Complex.conj_re, hre] at this

/-- The zero side `Z(t) = (1/t) Σ_j w_j Re W(F_{j,t}, F_{j,t})`. -/
def zeroPart (Φ : ℕ → ℂ → ℂ) (w : ℕ → ℝ) (t : ℝ) : ℝ :=
  1 / t * ∑' j, w j * (zetaZeroConfig.W (fun u => (stripTest (dil t (Φ j)) u : ℂ))
    (fun u => (stripTest (dil t (Φ j)) u : ℂ))).re

theorem NullFamily.abs_term_W_le (hN : NullFamily Φ w ε c) (j : ℕ) {t : ℝ}
    (ht : t ∈ Icc (3 / 4 : ℝ) (17 / 16)) :
    |w j * (zetaZeroConfig.W (fun u => (stripTest (dil t (Φ j)) u : ℂ))
        (fun u => (stripTest (dil t (Φ j)) u : ℂ))).re| ≤
      5 / 4 * zetaInvSqSum * dilConst ε ^ 2 * (t - 1) ^ 2 * (w j * c j ^ 2) := by
  rw [abs_mul, abs_of_nonneg (hN.weight j)]
  calc w j * |(zetaZeroConfig.W (fun u => (stripTest (dil t (Φ j)) u : ℂ))
        (fun u => (stripTest (dil t (Φ j)) u : ℂ))).re|
      ≤ w j * (5 / 4 * zetaInvSqSum * (|t - 1| * (dilConst ε * c j)) ^ 2) :=
        mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (hN.norm_W_dil_le j ht))
          (hN.weight j)
    _ = _ := by rw [mul_pow, mul_pow, sq_abs]; ring

theorem NullFamily.summable_W (hN : NullFamily Φ w ε c) {t : ℝ}
    (ht : t ∈ Icc (3 / 4 : ℝ) (17 / 16)) :
    Summable fun j => w j * (zetaZeroConfig.W (fun u => (stripTest (dil t (Φ j)) u : ℂ))
      (fun u => (stripTest (dil t (Φ j)) u : ℂ))).re :=
  Summable.of_norm_bounded (hN.summable.mul_left _) fun j => by
    rw [Real.norm_eq_abs]; exact hN.abs_term_W_le j ht

theorem NullFamily.abs_zeroPart_le (hN : NullFamily Φ w ε c) {t : ℝ}
    (ht : t ∈ Icc (3 / 4 : ℝ) (17 / 16)) :
    |zeroPart Φ w t| ≤
      4 / 3 * (5 / 4 * zetaInvSqSum * dilConst ε ^ 2 * familyMass w c) * (t - 1) ^ 2 := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hZ := zetaInvSqSum_nonneg
  have hM := hN.mass_nonneg
  have hs := hN.summable_W ht
  have habs : |∑' j, w j * (zetaZeroConfig.W (fun u => (stripTest (dil t (Φ j)) u : ℂ))
      (fun u => (stripTest (dil t (Φ j)) u : ℂ))).re| ≤
      5 / 4 * zetaInvSqSum * dilConst ε ^ 2 * (t - 1) ^ 2 * familyMass w c := by
    rw [← Real.norm_eq_abs]
    refine (norm_tsum_le_tsum_norm hs.norm).trans ?_
    rw [familyMass, ← tsum_mul_left]
    exact hs.norm.tsum_le_tsum (fun j => by rw [Real.norm_eq_abs]; exact hN.abs_term_W_le j ht)
      (hN.summable.mul_left _)
  unfold zeroPart
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / t)]
  have h1t : 1 / t ≤ 4 / 3 := by rw [div_le_iff₀ ht0]; linarith [ht.1]
  have hC : 0 ≤ 5 / 4 * zetaInvSqSum * dilConst ε ^ 2 * (t - 1) ^ 2 * familyMass w c := by
    have := dilConst_nonneg ε
    positivity
  calc 1 / t * |∑' j, w j * (zetaZeroConfig.W (fun u => (stripTest (dil t (Φ j)) u : ℂ))
        (fun u => (stripTest (dil t (Φ j)) u : ℂ))).re|
      ≤ 4 / 3 * (5 / 4 * zetaInvSqSum * dilConst ε ^ 2 * (t - 1) ^ 2 * familyMass w c) :=
        mul_le_mul h1t habs (abs_nonneg _) (by norm_num)
    _ = _ := by ring

/-! ## The decomposition `a = Z + P` -/

theorem NullFamily.dilatedEnergy_eq (hN : NullFamily Φ w ε c) {t : ℝ}
    (ht : t ∈ Icc (3 / 4 : ℝ) (17 / 16)) :
    dilatedEnergy Φ w t = zeroPart Φ w t + primePart Φ w t := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hK := invConst_nonneg (2 * ε)
  set X : ℕ → ℕ → ℝ := fun j n => w j * ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
    (2 * t * crossCorr (stripTest (Φ j)) (stripTest (Φ j)) (Real.log n / t))) with hX
  set u : ℕ → ℝ := fun n => (1 + Real.log n) * (n : ℝ) ^ (-(3 / 2 : ℝ)) with hu
  have hu0 : ∀ n, 0 ≤ u n := fun n => by
    have := Real.log_natCast_nonneg n
    have := Real.rpow_nonneg (Nat.cast_nonneg n) (-(3 / 2 : ℝ))
    positivity
  have hXb : ∀ j n, |X j n| ≤ (w j * c j ^ 2) * (2 * t * invConst (2 * ε) * u n) := by
    intro j n
    have h := hN.abs_term_le j n ht
    have e : X j n = 2 * t * w j * ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
        crossCorr (stripTest (Φ j)) (stripTest (Φ j)) (Real.log n / t)) := by
      simp only [hX]; ring
    rw [e, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * t),
      abs_of_nonneg (hN.weight j)]
    calc 2 * t * w j * |(ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
          crossCorr (stripTest (Φ j)) (stripTest (Φ j)) (Real.log n / t)|
        ≤ 2 * t * w j * (c j ^ 2 * invConst (2 * ε) * u n) :=
          mul_le_mul_of_nonneg_left h (by have := hN.weight j; positivity)
      _ = _ := by ring
  have hjoint : Summable (Function.uncurry X) := by
    refine Summable.of_norm_bounded ((hN.summable.mul_of_nonneg
      (summable_one_add_log_mul_three_halves.mul_left (2 * t * invConst (2 * ε)))
      (fun j => mul_nonneg (hN.weight j) (sq_nonneg _))
      (fun n => by have := hu0 n; positivity))) fun p => ?_
    rw [Real.norm_eq_abs]
    exact hXb p.1 p.2
  have hrow : ∀ j, Summable (X j) := fun j =>
    Summable.of_norm_bounded
      (summable_one_add_log_mul_three_halves.mul_left ((w j * c j ^ 2) * (2 * t * invConst (2 * ε))))
      fun n => by
        rw [Real.norm_eq_abs]; refine (hXb j n).trans (le_of_eq ?_); simp only [hu]; ring
  have hP : Summable fun j => ∑' n, X j n := by
    refine Summable.of_norm_bounded
      (hN.summable.mul_right (2 * t * invConst (2 * ε) * ∑' n, u n)) fun j => ?_
    rw [Real.norm_eq_abs]
    calc |∑' n, X j n| ≤ ∑' n, |X j n| := by
          rw [← Real.norm_eq_abs]
          refine (norm_tsum_le_tsum_norm (hrow j).norm).trans (le_of_eq ?_)
          simp [Real.norm_eq_abs]
      _ ≤ ∑' n, (w j * c j ^ 2) * (2 * t * invConst (2 * ε) * u n) :=
          (hrow j).abs.tsum_le_tsum (hXb j)
            ((summable_one_add_log_mul_three_halves.mul_left _).mul_left _)
      _ = w j * c j ^ 2 * (2 * t * invConst (2 * ε) * ∑' n, u n) := by
          rw [tsum_mul_left, tsum_mul_left]
  have e1 : ∀ j, w j * archPoleEnergy (stripTest (dil t (Φ j))) =
      w j * (zetaZeroConfig.W (fun u => (stripTest (dil t (Φ j)) u : ℂ))
        (fun u => (stripTest (dil t (Φ j)) u : ℂ))).re + ∑' n, X j n := fun j => by
    rw [hN.archPoleEnergy_dil_eq j ht, mul_add, ← tsum_mul_left]
  unfold dilatedEnergy
  rw [tsum_congr e1, (hN.summable_W ht).tsum_add hP, mul_add]
  congr 1
  rw [← hjoint.tsum_comm]
  unfold primePart
  have e2 : ∀ n, ∑' j, X j n = 2 * t * ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
      nullRay Φ w (Real.log n / t)) := fun n => by
    simp only [hX]
    unfold nullRay
    rw [← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    ring
  rw [tsum_congr e2, tsum_mul_left]
  field_simp

/-! ## The derivatives at `t = 1` -/

theorem NullFamily.zeroPart_one (hN : NullFamily Φ w ε c) : zeroPart Φ w 1 = 0 := by
  have := hN.abs_zeroPart_le (t := 1) ⟨by norm_num, by norm_num⟩
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
  exact abs_nonpos_iff.mp this

theorem NullFamily.primePart_one (hN : NullFamily Φ w ε c) : primePart Φ w 1 = 0 := by
  unfold primePart
  refine (congrArg (2 * ·) ((tsum_congr fun n => ?_).trans tsum_zero)).trans (mul_zero 2)
  rw [div_one]
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  · rw [hN.nullRay_log hn, mul_zero]

theorem NullFamily.hasDerivAt_zeroPart (hN : NullFamily Φ w ε c) :
    HasDerivAt (zeroPart Φ w) 0 1 := by
  set M := 4 / 3 * (5 / 4 * zetaInvSqSum * dilConst ε ^ 2 * familyMass w c)
  rw [hasDerivAt_iff_isLittleO]
  simp only [hN.zeroPart_one, sub_zero, smul_zero]
  have hO : (fun t => zeroPart Φ w t) =O[𝓝 1] (fun t : ℝ => ‖t - 1‖ ^ 2) := by
    refine IsBigO.of_bound M ?_
    filter_upwards [Icc_mem_nhds (by norm_num : (3 / 4 : ℝ) < 1) (by norm_num : (1 : ℝ) < 17 / 16)]
      with t ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
      abs_of_nonneg (sq_nonneg (t - 1))]
    exact hN.abs_zeroPart_le ht
  exact hO.trans_isLittleO (isLittleO_pow_sub_sub (1 : ℝ) one_lt_two)

theorem NullFamily.hasDerivAt_primePart (hN : NullFamily Φ w ε c) :
    HasDerivAt (primePart Φ w) (-2 * nullRaySlope Φ w) 1 := by
  obtain ⟨K, hK0, hK⟩ := hN.exists_abs_deriv_nullRay_le
  set U : Set ℝ := Ioo (3 / 4) (17 / 16) with hU
  set vm : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n with hvm
  set g : ℕ → ℝ → ℝ := fun n t => vm n * nullRay Φ w (Real.log n / t) with hg
  set g' : ℕ → ℝ → ℝ := fun n t =>
    vm n * (deriv (nullRay Φ w) (Real.log n / t) * (Real.log n * -(t ^ 2)⁻¹)) with hg'
  have hd : ∀ n, ∀ t ∈ U, HasDerivAt (g n) (g' n t) t := by
    intro n t ht
    have ht0 : t ≠ 0 := by have := ht.1; positivity
    have h1 : HasDerivAt (fun s : ℝ => Real.log n / s) (Real.log n * -(t ^ 2)⁻¹) t := by
      have := (hasDerivAt_inv ht0).const_mul (Real.log n)
      simpa only [div_eq_mul_inv] using this
    have h2 : HasDerivAt (nullRay Φ w) (deriv (nullRay Φ w) (Real.log n / t))
        (Real.log n / t) := (hN.hasDerivAt_nullRay _).differentiableAt.hasDerivAt
    exact (h2.comp t h1).const_mul (vm n)
  set u : ℕ → ℝ := fun n => 16 / 9 * K * 64 * (n : ℝ) ^ (-(5 / 4 : ℝ)) with hu
  have hus : Summable u :=
    (Real.summable_nat_rpow.mpr (by norm_num : -(5 / 4 : ℝ) < -1)).mul_left _
  have hb : ∀ n, ∀ t ∈ U, ‖g' n t‖ ≤ u n := by
    intro n t ht
    have htI : t ∈ Icc (3 / 4 : ℝ) (17 / 16) := ⟨ht.1.le, ht.2.le⟩
    have ht0 : 0 < t := by linarith [ht.1]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0 : (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 := by simp
      simp only [hg', hvm, hu, h0, zero_div, zero_mul, norm_zero]
      have h1 : (0 : ℝ) ≤ ((0 : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)) := Real.rpow_nonneg (by simp) _
      have : (0 : ℝ) ≤ 16 / 9 * K * 64 := by positivity
      exact mul_nonneg this h1
    have hl0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hv := vonMangoldt_div_sqrt_le n
    have hv0 := vonMangoldt_div_sqrt_nonneg n
    have he := exp_neg_mul_abs_log_div_le (a := 9 / 8) (by norm_num) htI hn
    have hp := rpow_mul_rpow_le_three_halves hn (b := 16 * (9 / 8) / 17) (by norm_num)
    have ht2 : (t ^ 2)⁻¹ ≤ 16 / 9 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith [ht.1]
    have hr0 : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hr1 : 0 ≤ (n : ℝ) ^ (-(16 * (9 / 8) / 17 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hr2 : 0 ≤ (n : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hlsq := log_sq_le n
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hcomb : (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (-(3 / 2 : ℝ)) = (n : ℝ) ^ (-(5 / 4 : ℝ)) := by
      rw [← Real.rpow_add (by linarith)]; norm_num
    have hD : |deriv (nullRay Φ w) (Real.log n / t)| ≤ K * (n : ℝ) ^ (-(16 * (9 / 8) / 17 : ℝ)) :=
      (hK _).trans (mul_le_mul_of_nonneg_left he hK0)
    simp only [hg', hvm, hu, Real.norm_eq_abs, abs_mul, abs_neg, abs_inv,
      abs_of_nonneg hv0, abs_of_nonneg hl0, abs_of_nonneg (sq_nonneg t)]
    calc (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
          (|deriv (nullRay Φ w) (Real.log n / t)| * (Real.log n * (t ^ 2)⁻¹))
        ≤ (Real.log n * (n : ℝ) ^ (-(1 / 2 : ℝ))) *
            ((K * (n : ℝ) ^ (-(16 * (9 / 8) / 17 : ℝ))) * (Real.log n * (16 / 9))) := by
          refine mul_le_mul hv (mul_le_mul hD (mul_le_mul_of_nonneg_left ht2 hl0)
            (by positivity) (by positivity)) (by positivity) (by positivity)
      _ = 16 / 9 * K * (Real.log n ^ 2 *
            ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(16 * (9 / 8) / 17 : ℝ)))) := by ring
      _ ≤ 16 / 9 * K * (64 * (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul hlsq hp (by positivity) (by positivity)
      _ = 16 / 9 * K * 64 * (n : ℝ) ^ (-(5 / 4 : ℝ)) := by rw [mul_assoc 64, hcomb]; ring
  have hU1 : (1 : ℝ) ∈ U := ⟨by norm_num, by norm_num⟩
  have hg0 : Summable fun n => g n 1 := by
    refine summable_zero.congr fun n => ?_
    simp only [hg, hvm, div_one]
    rcases lt_or_ge n 2 with hn | hn
    · interval_cases n <;> simp
    · rw [hN.nullRay_log hn, mul_zero]
  have hsum := hasDerivAt_tsum_of_isPreconnected hus isOpen_Ioo isPreconnected_Ioo hd hb hU1 hg0 hU1
  have hval : ∑' n, g' n 1 = -nullRaySlope Φ w := by
    unfold nullRaySlope
    rw [← tsum_neg]
    refine tsum_congr fun n => ?_
    simp only [hg', hvm, div_one, one_pow, inv_one]
    ring
  have h2 := hsum.const_mul 2
  rw [hval, show (2 : ℝ) * -nullRaySlope Φ w = -2 * nullRaySlope Φ w by ring] at h2
  exact h2

/-! ## The criticality law -/

theorem NullFamily.dilatedEnergy_eventuallyEq (hN : NullFamily Φ w ε c) :
    dilatedEnergy Φ w =ᶠ[𝓝 1] fun t => zeroPart Φ w t + primePart Φ w t := by
  filter_upwards [Icc_mem_nhds (by norm_num : (3 / 4 : ℝ) < 1) (by norm_num : (1 : ℝ) < 17 / 16)]
    with t ht
  exact hN.dilatedEnergy_eq ht

/-- **The null ray has zero energy at `t = 1`.** -/
theorem NullFamily.dilatedEnergy_one (hN : NullFamily Φ w ε c) : dilatedEnergy Φ w 1 = 0 := by
  rw [hN.dilatedEnergy_eq ⟨by norm_num, by norm_num⟩, hN.zeroPart_one, hN.primePart_one,
    add_zero]

/-- **The criticality law**: `a′(1) = −2S`. -/
theorem NullFamily.hasDerivAt_dilatedEnergy (hN : NullFamily Φ w ε c) :
    HasDerivAt (dilatedEnergy Φ w) (-2 * nullRaySlope Φ w) 1 := by
  have h := hN.hasDerivAt_zeroPart.add hN.hasDerivAt_primePart
  rw [zero_add] at h
  exact h.congr_of_eventuallyEq hN.dilatedEnergy_eventuallyEq

/-- **The null ray breaks the dilated cone on one side of `t = 1`.**  If `S ≠ 0`, then `a(t) < 0`
for every `t` close to `1` with `(t − 1) S > 0`. -/
theorem NullFamily.dilatedEnergy_neg (hN : NullFamily Φ w ε c) (hS : nullRaySlope Φ w ≠ 0) :
    ∃ δ > 0, ∀ t : ℝ, |t - 1| < δ → 0 < (t - 1) * nullRaySlope Φ w →
      dilatedEnergy Φ w t < 0 := by
  set S := nullRaySlope Φ w with hSdef
  have hd := hN.hasDerivAt_dilatedEnergy
  rw [hasDerivAt_iff_tendsto_slope] at hd
  have hS2 : 0 < |S| := abs_pos.mpr hS
  have hev := (Metric.tendsto_nhds.mp hd) |S| hS2
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hδ'⟩ := hev
  refine ⟨δ, hδ, fun t htδ hts => ?_⟩
  have ht1 : t ≠ 1 := by rintro rfl; simp at hts
  have hP := hδ' (by rwa [Real.dist_eq]) ht1
  rw [slope_def_field, hN.dilatedEnergy_one, sub_zero, Real.dist_eq] at hP
  set q := dilatedEnergy Φ w t / (t - 1) with hq
  have hqS : q * S < 0 := by
    have h := abs_lt.mp hP
    rcases lt_or_gt_of_ne hS with h' | h'
    · rw [abs_of_neg h'] at h; nlinarith
    · rw [abs_of_pos h'] at h; nlinarith
  have ht1' : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have he : dilatedEnergy Φ w t = q * (t - 1) := by rw [hq]; field_simp
  rw [he]
  by_contra hcon
  have h1 : 0 ≤ q * (t - 1) * S ^ 2 := mul_nonneg (not_lt.mp hcon) (sq_nonneg S)
  have h2 : q * (t - 1) * S ^ 2 = (q * S) * ((t - 1) * S) := by ring
  nlinarith [mul_neg_of_neg_of_pos hqS hts]

/-! ## The twisted-arc null family -/

/-- **The twisted-arc family of the twisted minimum principle is a null family.** -/
theorem exists_nullFamily_xiShiftedGamma :
    ∃ w c : ℕ → ℝ, NullFamily xiShiftedGamma w xiShiftedGammaRate c ∧ 0 < w 0 := by
  obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_twArc_annihilating twistedArcMinimumPrinciple_holds
  set ν : Measure ArcParam := (μ : Measure ArcParam) with hν
  have hmom : ∀ j, 0 ≤ twArcEvenMoment ν (fun _ => 1) j := twArcEvenMoment_one_nonneg μ
  have hblind0 : ∀ n : ℕ, ∫ u, (fun _ : ArcParam => (1 : ℝ)) u * twArcMoment n u ∂ν = 0 :=
    fun n => by simpa using hμ n
  set w : ℕ → ℝ := fun j => arcGammaWeight (twArcEvenMoment ν (fun _ => 1) j) j with hw_def
  have hw : ∀ j, 0 ≤ w j := fun j => arcGammaWeight_nonneg (hmom j) j
  have hw0 : 0 < w 0 := by
    simp only [hw_def, arcGammaWeight]
    exact div_pos (mul_pos (by positivity) (twArcEvenMoment_one_zero_pos μ))
      (by exact_mod_cast Nat.factorial_pos _)
  have hsumw : Summable fun j => w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2 :=
    summable_arcGammaWeight hmom
      (twArcEvenMoment_le (ν := ν) (g := fun _ => 1) (B := 1) fun _ => by norm_num)
  have hblindInt := shiftedGamma_blind_of_twistedArc (B := 1) measurable_const
    (fun _ => by norm_num) hblind0 hmom
  obtain ⟨C, hC, hs⟩ := exists_stripDecay_xiShiftedGamma_wide
  refine ⟨w, fun j => C * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j),
    ⟨xiShiftedGammaRate_pos, hs, hw, ?_, xiShiftedGamma_neg_conj, ?_, ?_⟩, hw0⟩
  · exact (hsumw.mul_left (C ^ 2)).congr fun j => by ring
  · intro j ρ
    have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
    have hIm : |(gammaOf (ρ : ℂ)).im| < 1 / 2 := WeilEF.abs_gammaOf_im_lt ⟨hmem.2.1, hmem.2.2⟩
    rw [← paperFT_xiShiftedGammaTest j (by linarith)]
    exact paperFT_xiShiftedGammaTest_gammaOf j ρ
  · intro n hn
    have e : ∀ j, w j * crossCorr (stripTest (xiShiftedGamma j)) (stripTest (xiShiftedGamma j))
        (Real.log n) = 1 / (2 * Real.pi) *
          (w j * ∫ r : ℝ, ‖xiShiftedGamma j r‖ ^ 2 * Real.cos (r * Real.log n)) := fun j => by
      rw [show stripTest (xiShiftedGamma j) = xiShiftedGammaTest j from rfl,
        crossCorr_xiShiftedGammaTest]
      ring
    simp_rw [e]
    rw [tsum_mul_left, hblindInt n hn, mul_zero]

/-- **The criticality law for the twisted-arc null ray.**  For the null ray `G₀` of the twisted
minimum principle: `G₀(·/t)` is blind at `t log n` with nonnegative spectral density, its energy
`a(t)` vanishes at `t = 1` with `a′(1) = −2S`, and if `S ≠ 0` then `a(t) < 0` on the side
`(t − 1) S > 0` of `t = 1`. -/
theorem twistedArc_nullRay_criticality :
    ∃ w c : ℕ → ℝ, NullFamily xiShiftedGamma w xiShiftedGammaRate c ∧ 0 < w 0 ∧
      (∀ t : ℝ, 0 < t → ∀ n : ℕ, 2 ≤ n → nullRay xiShiftedGamma w (t * Real.log n / t) = 0) ∧
      dilatedEnergy xiShiftedGamma w 1 = 0 ∧
      HasDerivAt (dilatedEnergy xiShiftedGamma w) (-2 * nullRaySlope xiShiftedGamma w) 1 ∧
      (nullRaySlope xiShiftedGamma w ≠ 0 → ∃ δ > 0, ∀ t : ℝ, |t - 1| < δ →
        0 < (t - 1) * nullRaySlope xiShiftedGamma w → dilatedEnergy xiShiftedGamma w t < 0) := by
  obtain ⟨w, c, hN, hw0⟩ := exists_nullFamily_xiShiftedGamma
  exact ⟨w, c, hN, hw0, fun t ht n hn => hN.nullRay_dilated_node ht hn, hN.dilatedEnergy_one,
    hN.hasDerivAt_dilatedEnergy, hN.dilatedEnergy_neg⟩

end RHTower.NullRayDilation

end
