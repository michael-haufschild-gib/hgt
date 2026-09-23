import GaloisForLFunctions.HTGeometry.GammaShiftLadderPolynomial
import GaloisForLFunctions.HTGeometry.GammaStirlingLadder
import GaloisForLFunctions.HTGeometry.GammaStirlingTelescopeThreshold

/-!
# The shifted Stirling ladder at every finite order

`ψ(s+μ) = log s - ∑_{m<M} d_m(μ) s^{-(m+1)} + O(‖s‖^{-(M+1)})` uniformly on `Re s > 0`,
`‖s‖ ≥ max(2, 2‖μ‖+2)`, for every `M` and every `μ`.

The four hand-built signature data (`GammaShiftSignature{,Two,Three,Four}`) are the cases
`M = 1,2,3,4`.  Section 5 of `finite-archimedean-gamma-product-boundary-law` needs all of them:
the residue at `s^{-m}` of `∑_k e_k ψ(s+λ_k)` is `∑_k e_k` times a universal polynomial in `λ_k`
of degree `m`, so `rr` consecutive residues determine the power sums `∑_k e_k λ_k^j` and hence,
by Vandermonde on distinct `λ_k`, the exponent vector itself.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

/-- The rational part of the one-step difference of the shifted ladder defect. -/
def shiftLadderRatPart (mu : ℂ) (M : ℕ) (u : ℂ) : ℂ :=
  ∑ m ∈ Finset.range M, shiftLadderCoeff mu m * u ^ (m + 1) * (((1 + u) ^ (m + 1))⁻¹ - 1)

/-- The order-`M` shifted ladder defect. -/
def shiftLadderDefect (mu : ℂ) (M : ℕ) (s : ℂ) : ℂ :=
  Complex.digamma (s + mu) - Complex.log s
    + ∑ m ∈ Finset.range M, shiftLadderCoeff mu m / s ^ (m + 1)

theorem shiftLadderRatPart_succ (mu : ℂ) (M : ℕ) (u : ℂ) :
    shiftLadderRatPart mu (M + 1) u
      = shiftLadderRatPart mu M u
        + shiftLadderCoeff mu M * u ^ (M + 1) * (((1 + u) ^ (M + 1))⁻¹ - 1) :=
  Finset.sum_range_succ _ _

/-- **The shifted ladder polynomial is the cleared numerator of the one-step difference.** -/
theorem shiftLadderPoly_eval (mu : ℂ) : ∀ (M : ℕ) {u : ℂ}, 1 + u ≠ 0 → 1 + mu * u ≠ 0 →
    (shiftLadderPoly mu M).eval u
      = (1 + u) ^ M * (1 + mu * u)
          * (shiftLadderRatPart mu M u + (u / (1 + mu * u) - (u - taylorTail M u))) := by
  intro M
  induction M with
  | zero =>
      intro u _ hmu
      simp only [shiftLadderPoly, shiftLadderRatPart, taylorTail, Finset.range_zero,
        Finset.sum_empty, pow_zero, one_mul, sub_zero, Polynomial.eval_mul, Polynomial.eval_neg,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, zero_add]
      field_simp
      ring
  | succ M ih =>
      intro u hu hmu
      have hp : ((1 : ℂ) + u) ^ (M + 1) ≠ 0 := pow_ne_zero _ hu
      have hsign : ((-1 : ℂ)) ^ (M + 1) = -((-1 : ℂ) ^ M) := by rw [pow_succ]; ring
      have hsign2 : ((-1 : ℂ)) ^ (M + 2) = (-1 : ℂ) ^ M := by rw [pow_add]; norm_num
      rw [shiftLadderPoly_succ]
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
      rw [ih hu hmu, taylorTail_succ, shiftLadderRatPart_succ, hsign, hsign2]
      field_simp
      ring

/-- The divided form of the identity above. -/
theorem shiftLadderPoly_eval_div (mu : ℂ) (M : ℕ) {u : ℂ} (hu : 1 + u ≠ 0)
    (hmu : 1 + mu * u ≠ 0) :
    (shiftLadderPoly mu M).eval u / (1 + u) ^ M / (1 + mu * u)
      = shiftLadderRatPart mu M u + (u / (1 + mu * u) - (u - taylorTail M u)) := by
  have hp : ((1 : ℂ) + u) ^ M ≠ 0 := pow_ne_zero _ hu
  have hgen : ∀ a b X : ℂ, a ≠ 0 → b ≠ 0 → a * b * X / a / b = X := by
    intro a b X ha hb
    field_simp
  rw [shiftLadderPoly_eval mu M hu hmu]
  exact hgen _ _ _ hp hmu

/-- Beyond `2‖μ‖` the shifted argument never hits a pole of the digamma function. -/
theorem shift_ne_neg_natCast {mu s : ℂ} (hs : 0 < s.re) (hnorm : 2 * ‖mu‖ < ‖s‖) (m : ℕ) :
    s + mu ≠ -(m : ℂ) := by
  intro h
  have hsval : s = -(m : ℂ) - mu := by linear_combination h
  have hre : s.re = -(m : ℝ) - mu.re := by
    rw [hsval]
    simp
  have hmure : -mu.re ≤ ‖mu‖ := by
    have h1 := Complex.re_le_norm (-mu)
    rwa [Complex.neg_re, norm_neg] at h1
  have hmlt : (m : ℝ) < ‖mu‖ := by
    have : (0 : ℝ) < -(m : ℝ) - mu.re := by rw [← hre]; exact hs
    linarith
  have hnorms : ‖s‖ ≤ (m : ℝ) + ‖mu‖ := by
    rw [hsval]
    refine le_trans (norm_sub_le _ _) ?_
    simp
  linarith

theorem shiftLadderDefect_step (mu : ℂ) (M : ℕ) {s : ℂ} (hs : 0 < s.re)
    (hnorm : 2 * ‖mu‖ < ‖s‖) :
    shiftLadderDefect mu M (s + 1) - shiftLadderDefect mu M s
      = shiftLadderRatPart mu M (1 / s)
        + ((1 / s) / (1 + mu * (1 / s)) - Complex.log (1 + 1 / s)) := by
  have hz0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  have hz1 : s + 1 ≠ 0 := by
    intro h
    have hre : (s + 1).re = 0 := by rw [h]; simp
    rw [Complex.add_re, Complex.one_re] at hre
    linarith
  have hsmu : s + mu ≠ 0 := by
    have := shift_ne_neg_natCast hs hnorm 0
    simpa using this
  have hdig : Complex.digamma (s + mu + 1) = Complex.digamma (s + mu) + (s + mu)⁻¹ :=
    Complex.digamma_apply_add_one (s + mu) (fun m => shift_ne_neg_natCast hs hnorm m)
  have hcast : s + 1 + mu = s + mu + 1 := by ring
  have hterm : ∀ m : ℕ,
      shiftLadderCoeff mu m / (s + 1) ^ (m + 1) - shiftLadderCoeff mu m / s ^ (m + 1)
        = shiftLadderCoeff mu m * (1 / s) ^ (m + 1) * ((((1 : ℂ) + 1 / s) ^ (m + 1))⁻¹ - 1) := by
    intro m
    have hu1 : (1 : ℂ) + 1 / s = (s + 1) / s := by field_simp
    rw [hu1, div_pow, div_pow, one_pow]
    have hzp : s ^ (m + 1) ≠ 0 := pow_ne_zero _ hz0
    have hz1p : (s + 1) ^ (m + 1) ≠ 0 := pow_ne_zero _ hz1
    field_simp
  have hsum : (∑ m ∈ Finset.range M, shiftLadderCoeff mu m / (s + 1) ^ (m + 1))
      - (∑ m ∈ Finset.range M, shiftLadderCoeff mu m / s ^ (m + 1))
      = shiftLadderRatPart mu M (1 / s) := by
    rw [shiftLadderRatPart, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ => hterm m
  have hrat : (1 / s) / (1 + mu * (1 / s)) = (s + mu)⁻¹ := by
    field_simp
  have hlog := log_add_one_sub_log hs
  rw [shiftLadderDefect, shiftLadderDefect, hcast, hdig, hrat]
  rw [← hsum, ← hlog]
  ring


/-- **The one-step difference of the shifted ladder defect is `O(‖s‖^{-(M+2)})`.** -/
theorem exists_norm_shiftLadderDefect_step_le (mu : ℂ) (M : ℕ) :
    ∃ K R : ℝ, 0 ≤ K ∧ 2 ≤ R ∧ ∀ s : ℂ, 0 < s.re → R ≤ ‖s‖ →
      ‖shiftLadderDefect mu M (s + 1) - shiftLadderDefect mu M s‖ ≤ K / ‖s‖ ^ (M + 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_polyEval_div_pow_le_of_dvd (X_pow_dvd_shiftLadderPoly mu M) M
  refine ⟨2 * C + 1, max 2 (2 * ‖mu‖ + 2), by linarith, le_max_left _ _, fun s hs hR => ?_⟩
  have h2 : (2 : ℝ) ≤ ‖s‖ := le_trans (le_max_left _ _) hR
  have hmu2 : 2 * ‖mu‖ + 2 ≤ ‖s‖ := le_trans (le_max_right _ _) hR
  have hmunorm : 2 * ‖mu‖ < ‖s‖ := by linarith
  have hspos : (0 : ℝ) < ‖s‖ := by linarith
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hspos; simp at hspos
  have hunorm : ‖(1 : ℂ) / s‖ = 1 / ‖s‖ := by rw [norm_div, norm_one]
  have huhalf : ‖(1 : ℂ) / s‖ ≤ 1 / 2 := by
    rw [hunorm, div_le_div_iff₀ hspos (by norm_num : (0:ℝ) < 2)]
    linarith
  have hmuhalf : ‖mu * ((1 : ℂ) / s)‖ ≤ 1 / 2 := by
    rw [norm_mul, hunorm]
    rw [mul_one_div, div_le_div_iff₀ hspos (by norm_num : (0:ℝ) < 2)]
    linarith
  have hu1 : (1 : ℂ) + 1 / s ≠ 0 := by
    intro h
    have hb := one_half_le_norm_one_add huhalf
    rw [h, norm_zero] at hb
    linarith
  have hmulow : (1 : ℝ) / 2 ≤ ‖1 + mu * ((1 : ℂ) / s)‖ := by
    have hb := norm_sub_le ((1 : ℂ) + mu * (1 / s)) (mu * (1 / s))
    rw [add_sub_cancel_right, norm_one] at hb
    linarith
  have hmu1 : (1 : ℂ) + mu * (1 / s) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hmulow
    linarith
  have hev := shiftLadderPoly_eval_div mu M hu1 hmu1
  have hsplit : shiftLadderDefect mu M (s + 1) - shiftLadderDefect mu M s
      = (shiftLadderPoly mu M).eval (1 / s) / (1 + 1 / s) ^ M / (1 + mu * (1 / s))
        + (((1 / s) - taylorTail M (1 / s)) - Complex.log (1 + 1 / s)) := by
    rw [shiftLadderDefect_step mu M hs hmunorm, hev]
    ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have hb1 : ‖(shiftLadderPoly mu M).eval (1 / s) / (1 + 1 / s) ^ M / (1 + mu * (1 / s))‖
      ≤ 2 * C * ‖(1 : ℂ) / s‖ ^ (M + 2) := by
    rw [norm_div]
    have hnum := hC (1 / s) huhalf
    have hpos : (0 : ℝ) < ‖1 + mu * ((1 : ℂ) / s)‖ := by linarith
    rw [div_le_iff₀ hpos]
    have hnn : (0 : ℝ) ≤ C * ‖(1 : ℂ) / s‖ ^ (M + 2) := by positivity
    nlinarith [hnum, hmulow, hnn]
  have hb2 : ‖((1 / s) - taylorTail M (1 / s)) - Complex.log (1 + 1 / s)‖
      ≤ ‖(1 : ℂ) / s‖ ^ (M + 2) := by
    rw [taylorTail_eq, ← norm_neg]
    have hneg : -((∑ j ∈ Finset.range (M + 2), (-1 : ℂ) ^ (j + 1) * (1 / s) ^ j / (j : ℂ))
        - Complex.log (1 + 1 / s))
        = Complex.log (1 + 1 / s)
          - ∑ j ∈ Finset.range (M + 2), (-1 : ℂ) ^ (j + 1) * (1 / s) ^ j / (j : ℂ) := by
      ring
    rw [hneg]
    exact norm_log_one_add_sub_taylor_le' huhalf (by omega)
  have hpow : ‖(1 : ℂ) / s‖ ^ (M + 2) = 1 / ‖s‖ ^ (M + 2) := by
    rw [hunorm, div_pow, one_pow]
  rw [hpow] at hb1 hb2
  have hid : 2 * C * (1 / ‖s‖ ^ (M + 2)) + 1 / ‖s‖ ^ (M + 2)
      = (2 * C + 1) / ‖s‖ ^ (M + 2) := by
    field_simp
  linarith [hb1, hb2, hid.le, hid.symm.le]

theorem tendsto_shiftLadderDefect_shift_zero (mu : ℂ) (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => shiftLadderDefect mu M (s + (n : ℂ))) atTop (nhds 0) := by
  have hmure : -mu.re ≤ ‖mu‖ := by
    have h1 := Complex.re_le_norm (-mu)
    rwa [Complex.neg_re, norm_neg] at h1
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (‖mu‖ + 1)
  have hw : 0 ≤ (s + mu + (n₀ : ℂ)).re := by
    rw [Complex.add_re, Complex.add_re, Complex.natCast_re]
    linarith
  have hdsd0 := tendsto_digammaStirlingDefect_shift_zero hw
  have hdsd : Tendsto (fun n : ℕ => digammaStirlingDefect (s + mu + (n : ℂ))) atTop (nhds 0) := by
    refine (Filter.tendsto_add_atTop_iff_nat n₀).mp ?_
    refine hdsd0.congr (fun n => ?_)
    congr 1
    push_cast
    ring
  have hhalf : Tendsto (fun n : ℕ => (1 : ℂ) / (2 * (s + mu + (n : ℂ)))) atTop (nhds 0) := by
    refine (tendsto_div_pow_add_natCast (s + mu) (1 / 2) 0).congr (fun n => ?_)
    simp only [mul_inv, div_eq_mul_inv]
    ring
  have hsum : Tendsto (fun n : ℕ =>
      ∑ m ∈ Finset.range M, shiftLadderCoeff mu m / (s + (n : ℂ)) ^ (m + 1)) atTop (nhds 0) := by
    have h := tendsto_finsetSum (Finset.range M)
      (fun m (_ : m ∈ Finset.range M) => tendsto_div_pow_add_natCast s (shiftLadderCoeff mu m) m)
    simpa using h
  have hquot : Tendsto (fun n : ℕ => (1 : ℂ) + mu / (s + (n : ℂ))) atTop (nhds 1) := by
    have h : Tendsto (fun n : ℕ => mu / (s + (n : ℂ))) atTop (nhds 0) := by
      simpa using tendsto_div_pow_add_natCast s mu 0
    simpa using (tendsto_const_nhds (x := (1 : ℂ)) (f := atTop (α := ℕ))).add h
  have hlogq : Tendsto (fun n : ℕ => Complex.log (1 + mu / (s + (n : ℂ)))) atTop (nhds 0) := by
    have hcont : ContinuousAt Complex.log 1 := continuousAt_clog (by simp)
    have h := hcont.tendsto.comp hquot
    rw [Complex.log_one] at h
    exact h
  have hlogdiff : Tendsto
      (fun n : ℕ => Complex.log (s + mu + (n : ℂ)) - Complex.log (s + (n : ℂ)))
      atTop (nhds 0) := by
    refine hlogq.congr' ?_
    have hev : ∀ᶠ n : ℕ in atTop, ((n : ℝ) > ‖mu‖ + 1) := by
      have : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      exact this.eventually_gt_atTop _
    filter_upwards [hev] with n hn
    have hre1 : 0 < (s + mu + (n : ℂ)).re := by
      rw [Complex.add_re, Complex.add_re, Complex.natCast_re]
      linarith
    have hre2 : 0 < (s + (n : ℂ)).re := by
      rw [Complex.add_re, Complex.natCast_re]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hne : s + (n : ℂ) ≠ 0 := by
      intro h
      rw [h] at hre2
      simp at hre2
    rw [log_sub_log_of_re_pos hre1 hre2]
    congr 1
    field_simp
    ring
  have hcomb := ((hdsd.sub hhalf).add hlogdiff).add hsum
  simp only [sub_zero, add_zero] at hcomb
  refine hcomb.congr (fun n => ?_)
  rw [digammaStirlingDefect, shiftLadderDefect]
  ring

/-- **The shifted Stirling ladder at every finite order.** -/
theorem exists_norm_shiftLadderDefect_le (mu : ℂ) (M : ℕ) :
    ∃ K R : ℝ, 0 ≤ K ∧ 2 ≤ R ∧ ∀ s : ℂ, 0 < s.re → R ≤ ‖s‖ →
      ‖shiftLadderDefect mu M s‖ ≤ K / ‖s‖ ^ (M + 1) := by
  obtain ⟨K, R, hK0, hR, hstep⟩ := exists_norm_shiftLadderDefect_step_le mu M
  refine ⟨3 * K, R, by linarith, hR, fun s hs hRs => ?_⟩
  exact norm_le_of_step_bound_ge hK0 hR (fun w hw hwR => hstep w hw hwR) hs hRs
    (tendsto_shiftLadderDefect_shift_zero mu M hs)

/-- The shifted ladder in expanded form. -/
theorem exists_norm_digamma_shift_ladder_expansion_le (mu : ℂ) (M : ℕ) :
    ∃ K R : ℝ, 0 ≤ K ∧ 2 ≤ R ∧ ∀ s : ℂ, 0 < s.re → R ≤ ‖s‖ →
      ‖Complex.digamma (s + mu)
          - (Complex.log s - ∑ m ∈ Finset.range M, shiftLadderCoeff mu m / s ^ (m + 1))‖
        ≤ K / ‖s‖ ^ (M + 1) := by
  obtain ⟨K, R, hK0, hR, hb⟩ := exists_norm_shiftLadderDefect_le mu M
  refine ⟨K, R, hK0, hR, fun s hs hRs => ?_⟩
  have h := hb s hs hRs
  rw [shiftLadderDefect] at h
  convert h using 2
  ring

/-- **A vertical finite difference removes the logarithmic digamma growth.**
On the right half-plane, the unit imaginary translate of digamma is uniformly
`O(‖s‖⁻¹)`.  Unlike the horizontal ladder step, this is the source-side estimate
needed when a height difference is used to remove the archimedean `log |t|` mode. -/
theorem exists_norm_digamma_vertical_unit_shift_le :
    ∃ K R : ℝ, 0 ≤ K ∧ 2 ≤ R ∧ ∀ s : ℂ, 0 < s.re → R ≤ ‖s‖ →
      ‖(s + Complex.I).digamma - s.digamma‖ ≤ K / ‖s‖ := by
  obtain ⟨C, R, hC, hR, hbound⟩ := exists_norm_digamma_shift_ladder_expansion_le 0 0
  refine ⟨3 * C + 2, 2 * R, by linarith, by linarith, fun s hs hsize => ?_⟩
  have hsR : R ≤ ‖s‖ := by linarith
  have hs2 : (2 : ℝ) ≤ ‖s‖ := le_trans hR hsR
  have hspos : 0 < ‖s‖ := by linarith
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, norm_zero] at hspos
    linarith
  have hshiftre : 0 < (s + Complex.I).re := by
    rw [Complex.add_re, Complex.I_re]
    simpa using hs
  have htriangle := norm_sub_le (s + Complex.I) Complex.I
  have hsub : s + Complex.I - Complex.I = s := by ring
  rw [hsub, Complex.norm_I] at htriangle
  have hhalf : ‖s‖ / 2 ≤ ‖s + Complex.I‖ := by linarith
  have hshiftR : R ≤ ‖s + Complex.I‖ := by linarith
  have hshiftpos : 0 < ‖s + Complex.I‖ := lt_of_lt_of_le (by linarith : 0 < R) hshiftR
  have hbase : ‖s.digamma - Complex.log s‖ ≤ C / ‖s‖ := by
    simpa using hbound s hs hsR
  have hbaseShift : ‖(s + Complex.I).digamma - Complex.log (s + Complex.I)‖
      ≤ C / ‖s + Complex.I‖ := by
    simpa using hbound (s + Complex.I) hshiftre hshiftR
  have hshiftdiv : C / ‖s + Complex.I‖ ≤ 2 * C / ‖s‖ := by
    apply (div_le_div_iff₀ hshiftpos hspos).mpr
    have hnonneg : 0 ≤ C * (2 * ‖s + Complex.I‖ - ‖s‖) :=
      mul_nonneg hC (by linarith)
    nlinarith
  have hu : ‖Complex.I / s‖ = 1 / ‖s‖ := by
    rw [norm_div, Complex.norm_I]
  have huhalf : ‖Complex.I / s‖ ≤ 1 / 2 := by
    rw [hu]
    apply (div_le_iff₀ hspos).mpr
    linarith
  have hlogeq : Complex.log (s + Complex.I) - Complex.log s
      = Complex.log (1 + Complex.I / s) := by
    rw [log_sub_log_of_re_pos hshiftre hs]
    congr 1
    field_simp
  have hrem := norm_log_one_add_sub_taylor_le' huhalf (n := 2) (by omega)
  have hrem' : ‖Complex.log (1 + Complex.I / s) - Complex.I / s‖ ≤ ‖Complex.I / s‖ ^ (2 : ℕ) := by
    simpa [Finset.sum_range_succ] using hrem
  have hlog : ‖Complex.log (s + Complex.I) - Complex.log s‖ ≤ 2 / ‖s‖ := by
    rw [hlogeq]
    calc
      ‖Complex.log (1 + Complex.I / s)‖ =
          ‖(Complex.log (1 + Complex.I / s) - Complex.I / s) + Complex.I / s‖ := by
            congr 1
            ring
      _ ≤ ‖Complex.log (1 + Complex.I / s) - Complex.I / s‖ + ‖Complex.I / s‖ :=
        norm_add_le _ _
      _ ≤ ‖Complex.I / s‖ ^ (2 : ℕ) + ‖Complex.I / s‖ := by gcongr
      _ ≤ 2 / ‖s‖ := by
        rw [hu]
        have hq0 : 0 ≤ 1 / ‖s‖ := by positivity
        have hq1 : 1 / ‖s‖ ≤ 1 := by
          apply (div_le_one₀ hspos).mpr
          linarith
        have hqmul : (1 / ‖s‖) * (1 / ‖s‖) ≤ (1 / ‖s‖) * 1 :=
          mul_le_mul_of_nonneg_left hq1 hq0
        calc
          (1 / ‖s‖) ^ (2 : ℕ) + 1 / ‖s‖ ≤ 1 / ‖s‖ + 1 / ‖s‖ := by
            gcongr
            simpa [pow_two] using hqmul
          _ = 2 / ‖s‖ := by ring
  have hdecomp : (s + Complex.I).digamma - s.digamma =
      ((s + Complex.I).digamma - Complex.log (s + Complex.I)) +
        (Complex.log (s + Complex.I) - Complex.log s) +
          (Complex.log s - s.digamma) := by ring
  rw [hdecomp]
  have hbaseNeg : ‖Complex.log s - s.digamma‖ ≤ C / ‖s‖ := by
    rw [show Complex.log s - s.digamma = -(s.digamma - Complex.log s) by ring, norm_neg]
    exact hbase
  calc
    ‖((s + Complex.I).digamma - Complex.log (s + Complex.I)) +
        (Complex.log (s + Complex.I) - Complex.log s) + (Complex.log s - s.digamma)‖
        ≤ ‖((s + Complex.I).digamma - Complex.log (s + Complex.I)) +
              (Complex.log (s + Complex.I) - Complex.log s)‖ + ‖Complex.log s - s.digamma‖ :=
          norm_add_le _ _
    _ ≤ ‖(s + Complex.I).digamma - Complex.log (s + Complex.I)‖ +
            ‖Complex.log (s + Complex.I) - Complex.log s‖ + ‖Complex.log s - s.digamma‖ := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left (norm_add_le ((s + Complex.I).digamma - Complex.log (s + Complex.I))
              (Complex.log (s + Complex.I) - Complex.log s)) ‖Complex.log s - s.digamma‖
    _ ≤ C / ‖s + Complex.I‖ + 2 / ‖s‖ + C / ‖s‖ := by
      exact add_le_add (add_le_add hbaseShift hlog) hbaseNeg
    _ ≤ (3 * C + 2) / ‖s‖ := by
      calc
        C / ‖s + Complex.I‖ + 2 / ‖s‖ + C / ‖s‖
            ≤ 2 * C / ‖s‖ + 2 / ‖s‖ + C / ‖s‖ := by gcongr
        _ = (3 * C + 2) / ‖s‖ := by
          field_simp
          ring

end

end GaloisForLFunctions.HTGeometry
