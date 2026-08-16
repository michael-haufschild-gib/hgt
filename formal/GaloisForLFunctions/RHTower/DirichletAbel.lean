import GaloisForLFunctions.RHTower.HurwitzZetaSmallShift

/-!
# Abel summation of a Dirichlet series with bounded partial sums

A Dirichlet series whose coefficient partial sums are bounded converges for `Re s > 0`, and its
value is an **absolutely** convergent series obtained by summation by parts.  That series is
analytic in `s` on the whole half plane, which is what makes the identity theorem available.
-/

open Complex HurwitzZeta MeasureTheory Set Filter Topology

namespace RHTower

/-- Partial sums of a coefficient sequence. -/
noncomputable def coeffPartial (c : ℕ → ℂ) (k : ℕ) : ℂ := ∑ j ∈ Finset.range k, c j

/-- The Abel-summed Dirichlet series. -/
noncomputable def abelDirichlet (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑' k : ℕ, coeffPartial c (k + 1)
    * (((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-s))

/-- The termwise bound for the Abel-summed series. -/
theorem norm_abelTerm_le {c : ℕ → ℂ} {B : ℝ} (hB : ∀ k, ‖coeffPartial c k‖ ≤ B) {s : ℂ}
    (hs : 0 < s.re) (k : ℕ) :
    ‖coeffPartial c (k + 1)
        * (((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-s))‖
      ≤ (B * ‖s‖) * (((k : ℝ) + 1) ^ (-s.re - 1)) := by
  have hx : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hstep := norm_cpow_shift_sub_le_of_nonneg (x := (k : ℝ) + 1) (b := 1) hx zero_le_one hs
  have hcast : (((k : ℝ) + 1 + 1 : ℝ)) = ((k : ℝ) + 2) := by ring
  rw [hcast, mul_one] at hstep
  have hsub : ‖((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-s)‖
      ≤ ‖s‖ * ((k : ℝ) + 1) ^ (-s.re - 1) := by
    rw [← norm_neg]
    have : -(((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-s))
        = ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-s) - ((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) := by ring
    rw [this]
    exact hstep
  rw [norm_mul]
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hnn : (0 : ℝ) ≤ ((k : ℝ) + 1) ^ (-s.re - 1) := Real.rpow_nonneg hx.le _
  calc ‖coeffPartial c (k + 1)‖
        * ‖((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-s)‖
      ≤ B * (‖s‖ * ((k : ℝ) + 1) ^ (-s.re - 1)) :=
        mul_le_mul (hB _) hsub (norm_nonneg _) hB0
    _ = (B * ‖s‖) * (((k : ℝ) + 1) ^ (-s.re - 1)) := by ring

theorem summable_abelTerm {c : ℕ → ℂ} {B : ℝ} (hB : ∀ k, ‖coeffPartial c k‖ ≤ B) {s : ℂ}
    (hs : 0 < s.re) :
    Summable (fun k : ℕ => coeffPartial c (k + 1)
      * (((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-s))) := by
  refine Summable.of_norm ?_
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_abelTerm_le hB hs)
    ((summable_shiftMajorant hs).mul_left _)

/-- **Summation by parts for a Dirichlet series.** -/
theorem sum_eq_abelPartial (c : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-s) * c i)
      = (((n : ℝ)) : ℂ) ^ (-s) * coeffPartial c n
        + ∑ k ∈ Finset.range (n - 1), coeffPartial c (k + 1)
            * (((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-s)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [coeffPartial]
  · have hby := Finset.sum_range_by_parts (f := fun i : ℕ => (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-s))
      (g := c) n
    simp only [smul_eq_mul] at hby
    rw [hby]
    have hcast : (((n - 1 : ℕ) : ℝ) + 1 : ℝ) = (n : ℝ) := by
      have h1 : (1 : ℕ) ≤ n := hn
      rw [Nat.cast_sub h1]
      push_cast
      ring
    rw [hcast]
    have hsum : (∑ i ∈ Finset.range (n - 1),
        (((((i + 1 : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-s))
          * coeffPartial c (i + 1))
        = -∑ k ∈ Finset.range (n - 1), coeffPartial c (k + 1)
            * (((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-s)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hc2 : ((((i + 1 : ℕ) : ℝ) + 1 : ℝ)) = ((i : ℝ) + 2) := by push_cast; ring
      rw [hc2]
      simp only [coeffPartial]
      ring
    simp only [coeffPartial] at hsum ⊢
    rw [hsum]
    ring

/-- **A Dirichlet series with bounded partial sums converges for `Re s > 0`.** -/
theorem tendsto_abelDirichlet {c : ℕ → ℂ} {B : ℝ} (hB : ∀ k, ‖coeffPartial c k‖ ≤ B) {s : ℂ}
    (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-s) * c i)
      atTop (𝓝 (abelDirichlet c s)) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hsum := summable_abelTerm hB hs
  have hhead : Tendsto (fun n : ℕ => (((n : ℝ)) : ℂ) ^ (-s) * coeffPartial c n)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hmaj : Tendsto (fun n : ℕ => B * ((n : ℝ) ^ (-s.re))) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop
      have := h.const_mul B
      rw [mul_zero] at this
      exact this
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hmaj
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
    have hre : (-s).re = -s.re := by simp
    rw [hre]
    have hnn : (0 : ℝ) ≤ (n : ℝ) ^ (-s.re) := Real.rpow_nonneg hnpos.le _
    calc (n : ℝ) ^ (-s.re) * ‖coeffPartial c n‖ ≤ (n : ℝ) ^ (-s.re) * B :=
          mul_le_mul_of_nonneg_left (hB n) hnn
      _ = B * (n : ℝ) ^ (-s.re) := by ring
  have htail : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n - 1), coeffPartial c (k + 1)
      * (((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-s)))
      atTop (𝓝 (abelDirichlet c s)) := by
    rw [abelDirichlet]
    exact (hsum.hasSum.tendsto_sum_nat).comp (tendsto_sub_atTop_nat 1)
  have := hhead.add htail
  rw [zero_add] at this
  refine this.congr fun n => ?_
  exact (sum_eq_abelPartial c s n).symm

/-- Each Abel term is entire in the exponent. -/
theorem differentiable_abelTerm (c : ℕ → ℂ) (k : ℕ) :
    Differentiable ℂ (fun s : ℂ => coeffPartial c (k + 1)
      * (((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-s))) := by
  have h1 : ((((k : ℝ) + 1 : ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have h2 : ((((k : ℝ) + 2 : ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  intro s
  refine DifferentiableAt.const_mul ?_ _
  exact (DifferentiableAt.const_cpow differentiableAt_id.neg (Or.inl h1)).sub
    (DifferentiableAt.const_cpow differentiableAt_id.neg (Or.inl h2))

/-- **The Abel-summed Dirichlet series is analytic on the right half plane.** -/
theorem differentiableAt_abelDirichlet {c : ℕ → ℂ} {B : ℝ} (hB : ∀ k, ‖coeffPartial c k‖ ≤ B)
    {s₀ : ℂ} (hs₀ : 0 < s₀.re) :
    DifferentiableAt ℂ (fun s : ℂ => abelDirichlet c s) s₀ := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  set r : ℝ := s₀.re / 2 with hrdef
  have hr : 0 < r := by positivity
  set U : Set ℂ := Metric.ball s₀ r with hUdef
  have hU : IsOpen U := Metric.isOpen_ball
  have hmemU : s₀ ∈ U := Metric.mem_ball_self hr
  have hfacts : ∀ s ∈ U, r ≤ s.re ∧ ‖s‖ ≤ ‖s₀‖ + r := by
    intro s hs
    have hdist : ‖s - s₀‖ < r := by
      rw [hUdef] at hs
      simpa [Complex.dist_eq] using hs
    have hre : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
      simpa using Complex.abs_re_le_norm (s - s₀)
    have h1 : |s.re - s₀.re| < r := lt_of_le_of_lt hre hdist
    have h2 := (abs_lt.1 h1).1
    refine ⟨by rw [hrdef] at *; linarith, ?_⟩
    have : ‖s‖ ≤ ‖s - s₀‖ + ‖s₀‖ := by
      simpa using norm_add_le (s - s₀) s₀
    linarith
  set u : ℕ → ℝ := fun k => (B * (‖s₀‖ + r)) * (((k : ℝ) + 1) ^ (-r - 1)) with hudef
  have hu : Summable u := (summable_shiftMajorant (w := (r : ℂ)) (by simpa using hr)).mul_left _
  have hle : ∀ k : ℕ, ∀ s ∈ U, ‖coeffPartial c (k + 1)
      * (((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-s))‖ ≤ u k := by
    intro k s hs
    obtain ⟨hre1, hnorm⟩ := hfacts s hs
    have hsre : 0 < s.re := lt_of_lt_of_le hr hre1
    have hstep := norm_abelTerm_le hB hsre k
    refine hstep.trans ?_
    rw [hudef]
    have hx : (1 : ℝ) ≤ (k : ℝ) + 1 := by simp [Nat.cast_nonneg]
    have hpow : ((k : ℝ) + 1) ^ (-s.re - 1) ≤ ((k : ℝ) + 1) ^ (-r - 1) :=
      Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    have hnn : (0 : ℝ) ≤ ((k : ℝ) + 1) ^ (-r - 1) := Real.rpow_nonneg (by positivity) _
    have hA : B * ‖s‖ ≤ B * (‖s₀‖ + r) := mul_le_mul_of_nonneg_left hnorm hB0
    calc (B * ‖s‖) * (((k : ℝ) + 1) ^ (-s.re - 1))
        ≤ (B * ‖s‖) * (((k : ℝ) + 1) ^ (-r - 1)) := by
          refine mul_le_mul_of_nonneg_left hpow ?_
          positivity
      _ ≤ (B * (‖s₀‖ + r)) * (((k : ℝ) + 1) ^ (-r - 1)) :=
          mul_le_mul_of_nonneg_right hA hnn
  have hdiffOn := differentiableOn_tsum_of_summable_norm hu
    (fun k => (differentiable_abelTerm c k).differentiableOn) hU hle
  exact hdiffOn.differentiableAt (hU.mem_nhds hmemU)

/-- Partial sums of a unimodular geometric progression are bounded. -/
theorem norm_coeffPartial_geom_le {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (k : ℕ) :
    ‖coeffPartial (fun j : ℕ => z ^ (j + 1)) k‖ ≤ 2 / ‖1 - z‖ := by
  have hzne : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hnorm : ‖1 - z‖ = ‖z - 1‖ := by rw [← norm_neg]; congr 1; ring
  have hval : coeffPartial (fun j : ℕ => z ^ (j + 1)) k = z * ((z ^ k - 1) / (z - 1)) := by
    rw [coeffPartial]
    have : ∀ j : ℕ, z ^ (j + 1) = z * z ^ j := fun j => by ring
    simp_rw [this]
    rw [← Finset.mul_sum, geom_sum_eq hz1]
  rw [hval, norm_mul, hz, one_mul, norm_div, hnorm]
  have hnum : ‖z ^ k - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, hz, one_pow, norm_one]
    norm_num
  have hden : 0 < ‖z - 1‖ := norm_pos_iff.mpr hzne
  exact div_le_div_of_nonneg_right hnum hden.le

/-! ## Identification with the exponential zeta function -/

/-- The boundary Dirichlet coefficients. -/
noncomputable def expCoeff (a : ℝ) : ℕ → ℂ := fun j => Complex.exp (2 * ↑Real.pi * I * a) ^ (j + 1)

theorem norm_coeffPartial_expCoeff_le {a : ℝ} (ha : Complex.exp (2 * ↑Real.pi * I * a) ≠ 1)
    (k : ℕ) :
    ‖coeffPartial (expCoeff a) k‖ ≤ 2 / ‖1 - Complex.exp (2 * ↑Real.pi * I * a)‖ := by
  have hz : ‖Complex.exp (2 * ↑Real.pi * I * (a : ℝ))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (2 * ↑Real.pi * I * (a : ℝ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero]
  exact norm_coeffPartial_geom_le hz ha k

/-- In the convergent regime the Abel sum is the exponential zeta value. -/
theorem abelDirichlet_eq_expZeta_of_one_lt_re {a : ℝ}
    (ha : Complex.exp (2 * ↑Real.pi * I * a) ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    abelDirichlet (expCoeff a) s = expZeta ((a : ℝ) : UnitAddCircle) s := by
  have hs0 : 0 < s.re := by linarith
  have hsne : s ≠ 0 := by
    intro hcon
    rw [hcon] at hs
    simp only [Complex.zero_re] at hs
    linarith
  have hsum := hasSum_expZeta_of_one_lt_re a hs
  have hzero : Complex.exp (2 * ↑Real.pi * I * a * (0 : ℕ)) / ((0 : ℕ) : ℂ) ^ s = 0 := by
    simp [Complex.zero_cpow hsne]
  have hshift : HasSum (fun i : ℕ =>
      Complex.exp (2 * ↑Real.pi * I * a * ((i + 1 : ℕ) : ℂ)) / (((i + 1 : ℕ) : ℂ)) ^ s)
      (expZeta ((a : ℝ) : UnitAddCircle) s) := by
    refine (hasSum_nat_add_iff
      (f := fun n : ℕ => Complex.exp (2 * ↑Real.pi * I * a * (n : ℂ)) / ((n : ℂ)) ^ s) 1).mpr ?_
    simp only [Finset.sum_range_one, Nat.cast_zero]
    rw [show Complex.exp (2 * ↑Real.pi * I * ↑a * 0) / (0 : ℂ) ^ s = 0 by
      simp [Complex.zero_cpow hsne]]
    simpa using hsum
  have hterm : ∀ i : ℕ,
      Complex.exp (2 * ↑Real.pi * I * a * ((i + 1 : ℕ) : ℂ)) / (((i + 1 : ℕ) : ℂ)) ^ s
        = (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-s) * expCoeff a i := by
    intro i
    rw [expCoeff, ← Complex.exp_nat_mul]
    have hcast : (((i : ℝ) + 1 : ℝ) : ℂ) = (((i + 1 : ℕ) : ℂ)) := by push_cast; ring
    rw [hcast, Complex.cpow_neg]
    have hexp : Complex.exp (2 * ↑Real.pi * I * ↑a * ((i + 1 : ℕ) : ℂ))
        = Complex.exp (((i + 1 : ℕ) : ℂ) * (2 * ↑Real.pi * I * ↑a)) := by
      congr 1
      ring
    rw [hexp, div_eq_mul_inv]
    ring
  have hlim1 : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
      (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-s) * expCoeff a i) atTop
      (𝓝 (expZeta ((a : ℝ) : UnitAddCircle) s)) :=
    (hshift.congr_fun fun i => (hterm i).symm).tendsto_sum_nat
  have hlim2 := tendsto_abelDirichlet (norm_coeffPartial_expCoeff_le ha) hs0
  exact tendsto_nhds_unique hlim2 hlim1

/-- **The boundary Dirichlet series is the exponential zeta function on the right half plane.** -/
theorem abelDirichlet_eq_expZeta {a : ℝ} (ha0 : ((a : ℝ) : UnitAddCircle) ≠ 0)
    (ha : Complex.exp (2 * ↑Real.pi * I * a) ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    abelDirichlet (expCoeff a) s = expZeta ((a : ℝ) : UnitAddCircle) s := by
  set F : ℂ → ℂ := fun s => abelDirichlet (expCoeff a) s
    - expZeta ((a : ℝ) : UnitAddCircle) s with hFdef
  have hF : DifferentiableOn ℂ F {w : ℂ | 0 < w.re} := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (differentiableAt_abelDirichlet (norm_coeffPartial_expCoeff_le ha) hz).sub
      (differentiable_expZeta_of_ne_zero ha0 z)
  have hFan : AnalyticOnNhd ℂ F {w : ℂ | 0 < w.re} := hF.analyticOnNhd isOpen_reGT_zero
  have hmem2 : (2 : ℂ) ∈ {w : ℂ | 0 < w.re} := by norm_num
  have hnhds : {w : ℂ | 1 < w.re} ∈ nhds (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hev : F =ᶠ[nhds (2 : ℂ)] 0 := by
    filter_upwards [hnhds] with z hz
    rw [hFdef]
    simp only [Pi.zero_apply]
    rw [abelDirichlet_eq_expZeta_of_one_lt_re ha hz, sub_self]
  have hzero := hFan.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_reGT_zero hmem2 hev
  have := hzero hs
  rw [hFdef] at this
  simp only [Pi.zero_apply] at this
  linear_combination this

end RHTower
