import GaloisForLFunctions.RHTower.MaassConstantTermWronskian
import GaloisForLFunctions.RHTower.SelbergMaassStripGap
import GaloisForLFunctions.HTGeometry.CirclePoincareWirtinger

/-!
# No even level-one cusp form with eigenvalue `1/4`

Let `W(x + iy) = Σ_{n≥1} h_n √y K₀(2πny) cos(2πnx)` (`cosSeries h`) with coefficients of polynomial
growth.  If `W(−1/z) = W(z)`, then every `h_n` vanishes (`coeff_eq_zero_of_invS`).

This is Roelcke's argument for `SL₂(ℤ)` at the eigenvalue `λ = 1/4`, made explicit through the
Fourier–Bessel expansion.

* **Energy identity.**  For the potential `P = |W|²`, `ΔP = 2|∇W|² − |W|²/(2y²)`.  Green's formula
  for the `S`- and `T`-invariant potential on the truncated modular domain leaves only the top
  flux, which decays like `e^{−2πY}` (`ModularInversionGreen.area_laplacian_eq_top_of_invariant`).
  Hence `4E = M`, with `E = ∫_F |∇W|² dx dy` and `M = ∫_F |W|² y⁻² dx dy`.
* **Two-cell bound.**  `y²|∇W|²` is `S`-invariant (`ModularInversionGreen.gradDensity_invS`), so
  the strip `|x| ≤ 1/2, y ≥ √3/2` carries at most `2E` (`integral_strip_le_twice`).
* **Wirtinger.**  `W` has zero mean on every horizontal line, so
  `∫|∂ₓW|² dx ≥ 4π² ∫|W|² dx` there.  Since `y² ≥ 3/4` on the cell, the strip carries at least
  `4π² · (3/4) M = 3π² M`.
* So `3π² M ≤ 2E = M/2`, which forces `M = 0`; then `W` vanishes on a horizontal line, and the
  orthogonality of the cosines gives `h_n √y K₀(2πny) = 0`, hence `h_n = 0`.
-/

open Complex Set Filter MeasureTheory
open scoped ContDiff Topology

noncomputable section

namespace RHTower.MaassLevelOneCuspVanishing

open MaassAxisContinuation MaassBesselSeries BesselKZero ModularInversionGreen
  MaassConstantTermWronskian
open GaloisForLFunctions.RHTower.SelbergMaassMean GaloisForLFunctions.RHTower.SelbergMaassTraceEnergy
  GaloisForLFunctions.RHTower.SelbergMaassTraceStokes GaloisForLFunctions.RHTower.SelbergModularDomainSlices
  GaloisForLFunctions.RHTower.SelbergModularPotentialGreen
  GaloisForLFunctions.RHTower.SelbergMaassFullCurvatureBudget
  GaloisForLFunctions.RHTower.SelbergMaassStripGap

variable {h : ℕ → ℂ}

/-! ## Positivity of `K₀` -/

theorem kMoment_pos (j : ℕ) {r : ℝ} (hr : 0 < r) : 0 < kMoment j r := by
  rw [kMoment_eq, setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall (kIntegrand_nonneg j r)) (integrableOn_kIntegrand j hr)]
  have hs : Function.support (kIntegrand j r) ∩ Ioi 0 = Ioi 0 := by
    ext t
    simp only [mem_inter_iff, Function.mem_support, mem_Ioi]
    refine ⟨fun h => h.2, fun ht => ⟨?_, ht⟩⟩
    unfold kIntegrand
    exact (mul_pos (pow_pos (Real.cosh_pos t) j) (Real.exp_pos _)).ne'
  rw [hs, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

theorem yPart_pos {n : ℕ} (hn : 1 ≤ n) {y : ℝ} (hy : 0 < y) : 0 < yPart (1 / 2) 0 0 n y := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold yPart
  simp only [pow_zero, one_mul]
  exact mul_pos (Real.rpow_pos_of_pos hy _) (kMoment_pos 0 (by positivity))

/-! ## Orthogonality of the cosines on a period -/

theorem integral_cos_two_pi_int {k : ℤ} (hk : k ≠ 0) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), Real.cos (2 * Real.pi * k * x) = 0 := by
  have hc : 2 * Real.pi * (k : ℝ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (by exact_mod_cast hk)
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos,
    show 2 * Real.pi * (k : ℝ) * (1 / 2) = k * Real.pi by ring,
    show 2 * Real.pi * (k : ℝ) * (-(1 / 2)) = -(k * Real.pi) by ring, Real.sin_neg,
    Real.sin_int_mul_pi]
  simp

theorem integral_cos_two_pi_zero :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), Real.cos (2 * Real.pi * ((0 : ℤ) : ℝ) * x) = 1 := by
  simp
  norm_num

theorem integral_cos_mul_cos (a m : ℕ) (ha : 1 ≤ a) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        Real.cos (2 * Real.pi * (a : ℝ) * x) * Real.cos (2 * Real.pi * (m : ℝ) * x) =
      if a = m then 1 / 2 else 0 := by
  have hpt : ∀ x : ℝ, Real.cos (2 * Real.pi * (a : ℝ) * x) * Real.cos (2 * Real.pi * (m : ℝ) * x) =
      (1 / 2) * Real.cos (2 * Real.pi * (((a : ℤ) - m : ℤ) : ℝ) * x) +
        (1 / 2) * Real.cos (2 * Real.pi * (((a : ℤ) + m : ℤ) : ℝ) * x) := by
    intro x
    push_cast
    rw [show 2 * Real.pi * ((a : ℝ) - m) * x = 2 * Real.pi * a * x - 2 * Real.pi * m * x by ring,
      show 2 * Real.pi * ((a : ℝ) + m) * x = 2 * Real.pi * a * x + 2 * Real.pi * m * x by ring,
      Real.cos_sub, Real.cos_add]
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hsum : ((a : ℤ) + m) ≠ 0 := by omega
  rw [integral_cos_two_pi_int hsum, mul_zero, add_zero]
  split_ifs with hm
  · subst hm
    rw [show ((a : ℤ) - a) = 0 by ring, integral_cos_two_pi_zero]
    ring
  · have hdiff : ((a : ℤ) - m) ≠ 0 := by omega
    rw [integral_cos_two_pi_int hdiff, mul_zero]

/-! ## Fourier coefficients of the Bessel series on a horizontal line -/

theorem point_re (x y : ℝ) : (point x y).re = x := by simp [point]

theorem sterm_point (n : ℕ) (x y : ℝ) :
    sterm h (1 / 2) 0 0 false n (point x y) =
      h (n + 1) * ((yPart (1 / 2) 0 0 (n + 1) y * Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x) :
        ℝ) : ℂ) := by
  simp only [sterm, bterm, xPart, trigFun, Bool.false_eq_true, ↓reduceIte, point_re, point_im]

/-- **Termwise cosine coefficients:** on the line `Im z = y`,
`∫ W(x + iy) cos(2πmx) dx = Σ_n h_{n+1} √y K₀(2π(n+1)y) ∫ cos(2π(n+1)x) cos(2πmx) dx`. -/
theorem integral_cosSeries_mul_cos (hh : PolyGrowth h) (m : ℕ) {y : ℝ} (hy : 0 < y) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), cosSeries h (point x y) * (Real.cos (2 * Real.pi * m * x) : ℂ) =
      ∑' n, h (n + 1) * (yPart (1 / 2) 0 0 (n + 1) y : ℂ) *
        ((∫ x in (-(1 / 2 : ℝ))..(1 / 2), Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x) *
          Real.cos (2 * Real.pi * m * x) : ℝ) : ℂ) := by
  obtain ⟨u, hu, hbd⟩ := norm_sterm_le hh (1 / 2) 0 0 false (y₂ := y) hy
  set F : ℕ → ℝ → ℂ := fun n x =>
    sterm h (1 / 2) 0 0 false n (point x y) * (Real.cos (2 * Real.pi * m * x) : ℂ) with hF
  have hterm : ∀ n, (∫ x in (-(1 / 2 : ℝ))..(1 / 2), F n x) =
      h (n + 1) * (yPart (1 / 2) 0 0 (n + 1) y : ℂ) *
        ((∫ x in (-(1 / 2 : ℝ))..(1 / 2), Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x) *
          Real.cos (2 * Real.pi * m * x) : ℝ) : ℂ) := by
    intro n
    have hpt : ∀ x, F n x = h (n + 1) * (yPart (1 / 2) 0 0 (n + 1) y : ℂ) *
        ((Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x) * Real.cos (2 * Real.pi * m * x) : ℝ) :
          ℂ) := by
      intro x
      rw [hF]
      simp only
      rw [sterm_point]
      push_cast
      ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (F := F) (f := fun x => cosSeries h (point x y) * (Real.cos (2 * Real.pi * m * x) : ℂ))
    (a := -(1 / 2 : ℝ)) (b := 1 / 2) (μ := volume) (fun n _ => u n)
    (fun n => (Continuous.aestronglyMeasurable (by
      rw [hF]
      simp only [sterm_point]
      fun_prop)))
    (fun n => Eventually.of_forall fun x _ => by
      rw [hF]
      simp only
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 := hbd n (point x y) (by rw [point_im]) (by rw [point_im])
      calc ‖sterm h (1 / 2) 0 0 false n (point x y)‖ * |Real.cos (2 * Real.pi * m * x)|
          ≤ u n * 1 := mul_le_mul h1 (Real.abs_cos_le_one _) (abs_nonneg _)
            ((norm_nonneg _).trans h1)
        _ = u n := mul_one _)
    (Eventually.of_forall fun _ _ => hu)
    (intervalIntegrable_const)
    (Eventually.of_forall fun x _ => by
      have hz : 0 < (point x y).im := by rw [point_im]; exact hy
      exact ((summable_sterm hh (1 / 2) 0 0 false hz).hasSum.mul_right _))
  rw [← hsum.tsum_eq]
  exact tsum_congr hterm

/-- `W` has zero mean on every horizontal line. -/
theorem integral_cosSeries_eq_zero (hh : PolyGrowth h) {y : ℝ} (hy : 0 < y) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), cosSeries h (point x y) = 0 := by
  have h0 := integral_cosSeries_mul_cos hh 0 hy
  simp only [Nat.cast_zero, mul_zero, zero_mul, Real.cos_zero, ofReal_one, mul_one] at h0
  rw [h0]
  refine (tsum_congr fun n => ?_).trans tsum_zero
  have hc := integral_cos_mul_cos (n + 1) 0 (Nat.succ_le_succ (Nat.zero_le n))
  simp only [Nat.cast_zero, mul_zero, zero_mul, Real.cos_zero, mul_one,
    Nat.succ_ne_zero, ↓reduceIte] at hc
  rw [hc]
  simp

/-- **Coefficient extraction:** `∫ W(x + iy) cos(2πmx) dx = h_m √y K₀(2πmy) / 2` for `m ≥ 1`. -/
theorem integral_cosSeries_mul_cos_eq (hh : PolyGrowth h) {m : ℕ} (hm : 1 ≤ m) {y : ℝ}
    (hy : 0 < y) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), cosSeries h (point x y) * (Real.cos (2 * Real.pi * m * x) : ℂ) =
      h m * (yPart (1 / 2) 0 0 m y : ℂ) * (1 / 2) := by
  rw [integral_cosSeries_mul_cos hh m hy]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [tsum_eq_single k (fun n hn => by
    rw [integral_cos_mul_cos (n + 1) (k + 1) (Nat.succ_le_succ (Nat.zero_le n)),
      if_neg (by omega)]
    simp)]
  rw [integral_cos_mul_cos (k + 1) (k + 1) (Nat.succ_le_succ (Nat.zero_le k)), if_pos rfl]
  push_cast
  ring

/-! ## The potential `|W|²` -/

theorem contDiffOn_cosSeries (hh : PolyGrowth h) : ContDiffOn ℝ ∞ (cosSeries h) upper :=
  contDiffOn_of_mem_besselSpan hh (seriesOf_mem h (1 / 2, 0, 0, false))

theorem cosSeries_add_one (z : ℂ) : cosSeries h (z + 1) = cosSeries h z := by
  have h1 := maassFun_add_one (g := h) 0 0 z
  simp only [maassFun, constTerm, zero_mul, add_zero] at h1
  exact mul_left_cancel₀ (by norm_num : (4 : ℂ) ≠ 0) h1

/-- The potential `|W|²`. -/
def pot (h : ℕ → ℂ) (w : ℂ) : ℝ := Complex.normSq (cosSeries h w)

theorem contDiffOn_pot (hh : PolyGrowth h) : ContDiffOn ℝ 2 (pot h) {z : ℂ | 0 < z.im} := by
  have hW : ContDiffOn ℝ 2 (cosSeries h) upper := contDiffOn_infty.mp (contDiffOn_cosSeries hh) 2
  have hr := Complex.reCLM.contDiff.comp_contDiffOn hW
  have hi := Complex.imCLM.contDiff.comp_contDiffOn hW
  refine ((hr.mul hr).add (hi.mul hi)).congr fun w _ => ?_
  simp [pot, Complex.normSq_apply]

theorem dir_eq_dirD (v : ℂ) (F : ℂ → ℂ) : dir v F = dirD v F := rfl

/-- **`Δ|W|² = 2|∇W|² − |W|²/(2y²)`.** -/
theorem realLaplacian_pot (hh : PolyGrowth h) {z : ℂ} (hz : 0 < z.im) :
    realLaplacian (pot h) z =
      2 * gradDensity (cosSeries h) z - Complex.normSq (cosSeries h z) / (2 * z.im ^ 2) := by
  have hzU : z ∈ upper := hz
  have hf : ContDiffAt ℝ 2 (cosSeries h) z :=
    contDiffAt_infty.mp ((contDiffOn_cosSeries hh).contDiffAt (isOpen_upper.mem_nhds hzU)) 2
  have hq := quarterDefect_cosSeries hh hz
  unfold quarterDefect at hq
  rw [Complex.real_smul] at hq
  have hsum : dir 1 (dir 1 (cosSeries h)) z + dir I (dir I (cosSeries h)) z =
      -((quarterWeight z : ℂ) * cosSeries h z) := by
    simp only [dir_eq_dirD]
    linear_combination hq
  have hre : (dir 1 (dir 1 (cosSeries h)) z * (starRingEnd ℂ) (cosSeries h z)).re +
      (dir I (dir I (cosSeries h)) z * (starRingEnd ℂ) (cosSeries h z)).re =
        -(quarterWeight z * Complex.normSq (cosSeries h z)) := by
    rw [← Complex.add_re, ← add_mul, hsum, neg_mul, mul_assoc, Complex.mul_conj,
      ← Complex.ofReal_mul, Complex.neg_re, Complex.ofReal_re]
  unfold realLaplacian
  rw [show pot h = fun w => Complex.normSq (cosSeries h w) from rfl, normSq_second_dir hf 1,
    normSq_second_dir hf I]
  have hg : gradDensity (cosSeries h) z =
      Complex.normSq (dir 1 (cosSeries h) z) + Complex.normSq (dir I (cosSeries h) z) := rfl
  have hk : 2 * (quarterWeight z * Complex.normSq (cosSeries h z)) =
      Complex.normSq (cosSeries h z) / (2 * z.im ^ 2) := by
    unfold quarterWeight
    field_simp
    ring
  rw [hg]
  linear_combination 2 * hre - hk

theorem abs_currentAt_pot_le (hh : PolyGrowth h) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    |currentAt (pot h) I x Y| ≤
      2 * (‖dirD I (cosSeries h) (point x Y)‖ * ‖cosSeries h (point x Y)‖) := by
  have hp : point x Y ∈ upper := by show 0 < (point x Y).im; rw [point_im]; exact hY
  have hd := differentiableAt_of_contDiffOn (contDiffOn_cosSeries hh) hp
  unfold currentAt
  rw [show pot h = fun w => Complex.normSq (cosSeries h w) from rfl, normSq_dir hd, abs_mul,
    abs_two]
  refine mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ?_) (by norm_num)
  rw [norm_mul, Complex.norm_conj]
  rfl

/-! ## Planar densities on the comparison rectangle -/

/-- `|∇W|²` in planar coordinates. -/
def gradF (h : ℕ → ℂ) (p : ℝ × ℝ) : ℝ := gradDensity (cosSeries h) (point p.1 p.2)

/-- `|W|²` in planar coordinates. -/
def sqF (h : ℕ → ℂ) (p : ℝ × ℝ) : ℝ := Complex.normSq (cosSeries h (point p.1 p.2))

/-- `|W|²/y²` in planar coordinates. -/
def massF (h : ℕ → ℂ) (p : ℝ × ℝ) : ℝ := sqF h p / p.2 ^ 2

/-- `|∂ₓW|²` in planar coordinates. -/
def dxF (h : ℕ → ℂ) (p : ℝ × ℝ) : ℝ := Complex.normSq (dirD 1 (cosSeries h) (point p.1 p.2))

theorem gradF_nonneg (p : ℝ × ℝ) : 0 ≤ gradF h p := gradDensity_nonneg _ _
theorem sqF_nonneg (p : ℝ × ℝ) : 0 ≤ sqF h p := Complex.normSq_nonneg _
theorem massF_nonneg (p : ℝ × ℝ) : 0 ≤ massF h p := div_nonneg (sqF_nonneg p) (sq_nonneg _)
theorem dxF_nonneg (p : ℝ × ℝ) : 0 ≤ dxF h p := Complex.normSq_nonneg _

theorem dxF_le_gradF (p : ℝ × ℝ) : dxF h p ≤ gradF h p :=
  le_add_of_nonneg_right (Complex.normSq_nonneg _)

/-- The open half-plane `y > 0` in planar coordinates. -/
def halfPlane : Set (ℝ × ℝ) := {p | 0 < p.2}

theorem rectangle_subset_halfPlane : rectangle ⊆ halfPlane := fun _ hp =>
  (arcFloor_pos).trans_le hp.2

theorem fullDomain_subset_rectangle : fullDomain ⊆ rectangle := fun _ hp =>
  ⟨hp.1, (arcFloor_le_arcHeight hp.1).trans hp.2⟩

theorem continuousOn_comp_point {V : ℂ → ℂ} (hV : ContinuousOn V upper) :
    ContinuousOn (fun p : ℝ × ℝ => V (point p.1 p.2)) halfPlane :=
  hV.comp (by unfold point; fun_prop) (fun p hp => by
    show 0 < (point p.1 p.2).im; rw [point_im]; exact hp)

theorem continuousOn_planar (hh : PolyGrowth h) :
    ContinuousOn (gradF h) halfPlane ∧ ContinuousOn (sqF h) halfPlane ∧
      ContinuousOn (massF h) halfPlane ∧ ContinuousOn (dxF h) halfPlane := by
  have hW := contDiffOn_cosSeries hh
  have c0 := continuousOn_comp_point hW.continuousOn
  have c1 := continuousOn_comp_point (contDiffOn_dirD hW 1).continuousOn
  have cI := continuousOn_comp_point (contDiffOn_dirD hW I).continuousOn
  have hn := Complex.continuous_normSq
  have hsq : ContinuousOn (sqF h) halfPlane := hn.comp_continuousOn c0
  refine ⟨(hn.comp_continuousOn c1).add (hn.comp_continuousOn cI), hsq, ?_,
    hn.comp_continuousOn c1⟩
  exact hsq.div (continuous_snd.pow 2).continuousOn fun p hp => pow_ne_zero 2 (ne_of_gt hp)

/-- The dominating density `e^{−2πy}` is integrable on the rectangle. -/
theorem integrableOn_exp_rectangle :
    IntegrableOn (fun p : ℝ × ℝ => Real.exp (-(2 * Real.pi) * p.2)) rectangle := by
  have hy : IntegrableOn (fun y : ℝ => Real.exp (-(2 * Real.pi) * y)) (Ici arcFloor) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr (exp_neg_integrableOn_Ioi arcFloor Real.two_pi_pos)
  have hx : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Icc (-(1 / 2 : ℝ)) (1 / 2))) :=
    integrable_const 1
  have hp := hx.mul_prod hy
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hp
  simpa only [one_mul, IntegrableOn, rectangle] using hp

theorem exists_planar_bound (hh : PolyGrowth h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ rectangle,
      gradF h p ≤ C * Real.exp (-(2 * Real.pi) * p.2) ∧
      sqF h p ≤ C * Real.exp (-(2 * Real.pi) * p.2) ∧
      massF h p ≤ C * Real.exp (-(2 * Real.pi) * p.2) ∧
      dxF h p ≤ C * Real.exp (-(2 * Real.pi) * p.2) := by
  obtain ⟨K, hK, hdec⟩ := exists_cosSeries_decay hh
  refine ⟨4 * K ^ 2, by positivity, fun p hp => ?_⟩
  have hy : 1 / 2 ≤ p.2 := (arcFloor_gt_half.le).trans hp.2
  have hy0 : 0 < p.2 := by linarith
  obtain ⟨b₀, b₁, bI⟩ := hdec (point p.1 p.2) (by rw [point_im]; exact hy)
  rw [point_im] at b₀ b₁ bI
  set e := Real.exp (-(Real.pi * p.2)) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hee : e ^ 2 = Real.exp (-(2 * Real.pi) * p.2) := by
    rw [he, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have sq_le : ∀ w : ℂ, ‖w‖ ≤ K * e → Complex.normSq w ≤ K ^ 2 * Real.exp (-(2 * Real.pi) * p.2) := by
    intro w hw
    rw [Complex.normSq_eq_norm_sq, ← hee, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hw 2
  have h0 := sq_le _ b₀
  have h1 := sq_le _ b₁
  have hI := sq_le _ bI
  have hE0 := (Real.exp_pos (-(2 * Real.pi) * p.2)).le
  have hK2 : 0 ≤ K ^ 2 * Real.exp (-(2 * Real.pi) * p.2) := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Complex.normSq (fderiv ℝ (cosSeries h) (point p.1 p.2) 1) +
      Complex.normSq (fderiv ℝ (cosSeries h) (point p.1 p.2) I) ≤ _
    have := h1; have := hI
    simp only [dirD] at h1 hI
    nlinarith
  · show Complex.normSq (cosSeries h (point p.1 p.2)) ≤ _
    nlinarith
  · unfold massF
    rw [div_le_iff₀ (by positivity)]
    have hy2 : 1 / 4 ≤ p.2 ^ 2 := by nlinarith
    calc sqF h p ≤ K ^ 2 * Real.exp (-(2 * Real.pi) * p.2) := h0
      _ ≤ 4 * K ^ 2 * Real.exp (-(2 * Real.pi) * p.2) * p.2 ^ 2 := by nlinarith
  · show Complex.normSq (dirD 1 (cosSeries h) (point p.1 p.2)) ≤ _
    nlinarith

theorem integrableOn_of_bound {F : ℝ × ℝ → ℝ} (hc : ContinuousOn F halfPlane)
    (hn : ∀ p, 0 ≤ F p) {C : ℝ}
    (hb : ∀ p ∈ rectangle, F p ≤ C * Real.exp (-(2 * Real.pi) * p.2)) :
    IntegrableOn F rectangle := by
  refine Integrable.mono' (integrableOn_exp_rectangle.const_mul C)
    ((hc.mono rectangle_subset_halfPlane).aestronglyMeasurable rectangle_measurable) ?_
  refine (ae_restrict_iff' rectangle_measurable).mpr (Eventually.of_forall fun p hp => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hn p)]
  exact hb p hp

theorem integrableOn_planar (hh : PolyGrowth h) :
    IntegrableOn (gradF h) rectangle ∧ IntegrableOn (sqF h) rectangle ∧
      IntegrableOn (massF h) rectangle ∧ IntegrableOn (dxF h) rectangle := by
  obtain ⟨C, -, hC⟩ := exists_planar_bound hh
  obtain ⟨c₁, c₂, c₃, c₄⟩ := continuousOn_planar hh
  exact ⟨integrableOn_of_bound c₁ gradF_nonneg (fun p hp => (hC p hp).1),
    integrableOn_of_bound c₂ sqF_nonneg (fun p hp => (hC p hp).2.1),
    integrableOn_of_bound c₃ massF_nonneg (fun p hp => (hC p hp).2.2.1),
    integrableOn_of_bound c₄ dxF_nonneg (fun p hp => (hC p hp).2.2.2)⟩

/-! ## The energy identity `4E = M` -/

theorem energy_identity (hh : PolyGrowth h)
    (hS : ∀ z : ℂ, 0 < z.im → cosSeries h (invS z) = cosSeries h z) :
    4 * ∫ p in fullDomain, gradF h p = ∫ p in fullDomain, massF h p := by
  obtain ⟨iG, -, iM, -⟩ := integrableOn_planar hh
  have iGf := iG.mono_set fullDomain_subset_rectangle
  have iMf := iM.mono_set fullDomain_subset_rectangle
  set lap : ℝ × ℝ → ℝ := fun p => 2 * gradF h p - massF h p / 2 with hlap
  have ilap : IntegrableOn lap fullDomain := (iGf.const_mul 2).sub (iMf.div_const 2)
  have hPT : ∀ w : ℂ, 0 < w.im → pot h (w + 1) = pot h w := fun w _ => by
    simp only [pot, cosSeries_add_one]
  have hPS : ∀ w : ℂ, 0 < w.im → pot h (invS w) = pot h w := fun w hw => by
    simp only [pot, hS w hw]
  have hgreen : ∀ Y : ℝ, 1 ≤ Y → (∫ p in domain Y, lap p) =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2), currentAt (pot h) I x Y := by
    intro Y hY
    rw [← area_laplacian_eq_top_of_invariant (pot h) (contDiffOn_pot hh) hPT hPS hY]
    refine setIntegral_congr_fun (isCompact_domain Y).measurableSet (fun p hp => ?_)
    have hp0 : 0 < (point p.1 p.2).im := by rw [point_im]; linarith [hp.1.2.1]
    simp only [hlap, realLaplacian_pot hh hp0, gradF, massF, sqF, point_im]
    ring
  obtain ⟨K, hK, hdec⟩ := exists_cosSeries_decay hh
  have hexp : Tendsto (fun Y : ℝ => Real.exp (-(2 * Real.pi) * Y)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith [Real.two_pi_pos]))
  have hlim := hexp.const_mul (2 * K ^ 2)
  rw [mul_zero] at hlim
  have htop : Tendsto (fun Y => ∫ x in (-(1 / 2 : ℝ))..(1 / 2), currentAt (pot h) I x Y) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
    refine (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := 2 * K ^ 2 * Real.exp (-(2 * Real.pi) * Y)) (fun x _ => ?_)).trans
      (le_of_eq (by norm_num))
    rw [Real.norm_eq_abs]
    refine (abs_currentAt_pot_le hh x (by linarith)).trans ?_
    obtain ⟨b₀, -, bI⟩ := hdec (point x Y) (by rw [point_im]; linarith)
    rw [point_im] at b₀ bI
    have he : Real.exp (-(Real.pi * Y)) * Real.exp (-(Real.pi * Y)) =
        Real.exp (-(2 * Real.pi) * Y) := by rw [← Real.exp_add]; ring_nf
    calc 2 * (‖dirD I (cosSeries h) (point x Y)‖ * ‖cosSeries h (point x Y)‖)
        ≤ 2 * ((K * Real.exp (-(Real.pi * Y))) * (K * Real.exp (-(Real.pi * Y)))) := by
          gcongr
      _ = 2 * K ^ 2 * Real.exp (-(2 * Real.pi) * Y) := by rw [← he]; ring
  have heq : (fun Y => ∫ p in domain Y, lap p) =ᶠ[atTop]
      (fun Y => ∫ x in (-(1 / 2 : ℝ))..(1 / 2), currentAt (pot h) I x Y) :=
    (eventually_ge_atTop 1).mono fun Y hY => hgreen Y hY
  have h0 : ∫ p in fullDomain, lap p = 0 :=
    tendsto_nhds_unique ((full_integral_tendsto ilap).congr' heq) htop
  rw [hlap, integral_sub (iGf.const_mul 2) (iMf.div_const 2), integral_const_mul,
    integral_div] at h0
  linarith

/-! ## Wirtinger on a horizontal line -/

theorem line_wirtinger (hh : PolyGrowth h) {y : ℝ} (hy : 0 < y) :
    4 * Real.pi ^ 2 * ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), sqF h (x, y) ≤
      ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), dxF h (x, y) := by
  set f : ℝ → ℂ := fun x => cosSeries h (point x y) with hf
  set f' : ℝ → ℂ := fun x => dirD 1 (cosSeries h) (point x y) with hf'
  have hW := contDiffOn_cosSeries hh
  have hpU : ∀ x, point x y ∈ upper := fun x => by
    show 0 < (point x y).im; rw [point_im]; exact hy
  have hderiv : ∀ x ∈ uIcc (-(1 / 2 : ℝ)) (1 / 2), HasDerivAt f (f' x) x := fun x _ =>
    (differentiableAt_of_contDiffOn hW (hpU x)).hasFDerivAt.comp_hasDerivAt x (point_horizontal x y)
  have hcont : ContinuousOn f' (uIcc (-(1 / 2 : ℝ)) (1 / 2)) :=
    ((contDiffOn_dirD hW 1).continuousOn.comp_continuous (by unfold point; fun_prop)
      hpU).continuousOn
  have hper : f (1 / 2) = f (-(1 / 2)) := by
    simp only [hf]
    rw [show point (1 / 2) y = point (-(1 / 2)) y + 1 by simp only [point]; push_cast; ring,
      cosSeries_add_one]
  have hw := GaloisForLFunctions.HTGeometry.wirtinger_intervalIntegral
    (by norm_num : (-(1 / 2 : ℝ)) < 1 / 2) hderiv hcont hper
  have hmean : ∫ x in (-(1 / 2 : ℝ))..(1 / 2), f x = 0 := integral_cosSeries_eq_zero hh hy
  have hba : (1 / 2 : ℝ) - -(1 / 2) = 1 := by norm_num
  simp only [hba, inv_one, one_mul, one_smul, hmean, norm_zero] at hw
  have key : ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ‖f x‖ ^ 2 ≤
      (1 / (2 * Real.pi)) ^ 2 * ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ‖f' x‖ ^ 2 := by
    simpa using hw
  have e1 : ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), sqF h (x, y) =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ‖f x‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num), integral_Icc_eq_integral_Ioc]
    simp only [sqF, hf, Complex.normSq_eq_norm_sq]
  have e2 : ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), dxF h (x, y) =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ‖f' x‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num), integral_Icc_eq_integral_Ioc]
    simp only [dxF, hf', Complex.normSq_eq_norm_sq]
  rw [e1, e2]
  calc 4 * Real.pi ^ 2 * ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ‖f x‖ ^ 2
      ≤ 4 * Real.pi ^ 2 * ((1 / (2 * Real.pi)) ^ 2 *
          ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ‖f' x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ‖f' x‖ ^ 2 := by
        field_simp
        ring

/-! ## The mass vanishes -/

theorem point_re_im (z : UpperHalfPlane) : point z.re z.im = (z : ℂ) := by
  apply Complex.ext <;> simp [point]

theorem coe_S_smul (z : UpperHalfPlane) :
    ((ModularGroup.S • z : UpperHalfPlane) : ℂ) = invS (z : ℂ) := by
  rw [UpperHalfPlane.modular_S_smul]
  simp [invS, inv_neg]

theorem mass_eq_zero (hh : PolyGrowth h)
    (hS : ∀ z : ℂ, 0 < z.im → cosSeries h (invS z) = cosSeries h z) :
    ∫ p in fullDomain, massF h p = 0 := by
  obtain ⟨iG, iSq, iM, iDx⟩ := integrableOn_planar hh
  have hE := energy_identity hh hS
  set E := ∫ p in fullDomain, gradF h p with hEdef
  set M := ∫ p in fullDomain, massF h p with hMdef
  have hM0 : 0 ≤ M := setIntegral_nonneg fullDomain_measurable (fun p _ => massF_nonneg p)
  by_cases hE0 : E = 0
  · rw [← hE, hE0, mul_zero]
  set u : UpperHalfPlane → ℝ := fun z => z.im ^ 2 * gradF h (z.re, z.im) with hu
  have hcell : ∫ z in ModularGroup.fd, u z = E :=
    GaloisForLFunctions.RHTower.SelbergMaassCellCurvature.integral_height_sq_cell (gradF h)
  have hstrip : ∫ z in GaloisForLFunctions.RHTower.SelbergModularStripComparison.strip, u z =
      ∫ p in rectangle, gradF h p := integral_height_sq_strip (gradF h)
  have hint : IntegrableOn u ModularGroup.fd :=
    Integrable.of_integral_ne_zero (by rw [hcell]; exact hE0)
  have hinv : ∀ z : UpperHalfPlane, u (ModularGroup.S • z) = u z := by
    intro z
    have hz := z.im_pos
    simp only [hu, gradF, point_re_im]
    rw [show (ModularGroup.S • z).im = ((ModularGroup.S • z : UpperHalfPlane) : ℂ).im from rfl,
      coe_S_smul]
    exact gradDensity_invS hz (differentiableAt_of_contDiffOn (contDiffOn_cosSeries hh)
      (invS_mem_upper hz)) hS
  have hle := GaloisForLFunctions.RHTower.SelbergModularStripComparison.integral_strip_le_twice
    hint (fun z => mul_nonneg (sq_nonneg _) (gradF_nonneg _)) hinv
  rw [hstrip, hcell] at hle
  have hdx : ∫ p in rectangle, dxF h p ≤ ∫ p in rectangle, gradF h p :=
    setIntegral_mono_on iDx iG rectangle_measurable (fun p _ => dxF_le_gradF p)
  have hwir : 4 * Real.pi ^ 2 * ∫ p in rectangle, sqF h p ≤ ∫ p in rectangle, dxF h p := by
    rw [rectangle_integral iSq, rectangle_integral iDx, ← integral_const_mul]
    exact setIntegral_mono_on ((rectangle_slices_integrable iSq).const_mul _)
      (rectangle_slices_integrable iDx) measurableSet_Ici
      (fun y hy => line_wirtinger hh (arcFloor_pos.trans_le hy))
  have hsq : ∫ p in fullDomain, sqF h p ≤ ∫ p in rectangle, sqF h p :=
    setIntegral_mono_set iSq (Eventually.of_forall fun p => sqF_nonneg p)
      (Eventually.of_forall fullDomain_subset_rectangle)
  have hmass : (3 / 4) * M ≤ ∫ p in fullDomain, sqF h p := by
    rw [hMdef, ← integral_const_mul]
    refine setIntegral_mono_on ((iM.mono_set fullDomain_subset_rectangle).const_mul _)
      (iSq.mono_set fullDomain_subset_rectangle) fullDomain_measurable (fun p hp => ?_)
    have hy : arcFloor ≤ p.2 := (fullDomain_subset_rectangle hp).2
    have hy2 : 3 / 4 ≤ p.2 ^ 2 := by
      have := arcFloor_sq
      nlinarith [arcFloor_pos]
    have hs := sqF_nonneg (h := h) p
    unfold massF
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have hπ : 3 < Real.pi := Real.pi_gt_three
  have h4 : 4 * Real.pi ^ 2 * ((3 / 4) * M) ≤ 4 * Real.pi ^ 2 * ∫ p in fullDomain, sqF h p :=
    mul_le_mul_of_nonneg_left hmass (by positivity)
  have h5 : 4 * Real.pi ^ 2 * ∫ p in fullDomain, sqF h p ≤
      4 * Real.pi ^ 2 * ∫ p in rectangle, sqF h p :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have hchain : 3 * Real.pi ^ 2 * M ≤ M / 2 := by
    have e1 : 4 * Real.pi ^ 2 * ((3 / 4) * M) = 3 * Real.pi ^ 2 * M := by ring
    linarith [hle, hdx, hwir, h4, h5, hE]
  have hp2 : 9 ≤ Real.pi ^ 2 := by nlinarith
  have h27 : 27 * M ≤ 3 * Real.pi ^ 2 * M := by
    have := mul_le_mul_of_nonneg_right hp2 hM0
    linarith
  apply le_antisymm _ hM0
  linarith

/-! ## The coefficients vanish -/

/-- **No even level-one cusp form with eigenvalue `1/4`:** an `S`-invariant Bessel cosine series
with coefficients of polynomial growth vanishes identically. -/
theorem coeff_eq_zero_of_invS (hh : PolyGrowth h)
    (hS : ∀ z : ℂ, 0 < z.im → cosSeries h (invS z) = cosSeries h z) {m : ℕ} (hm : 1 ≤ m) :
    h m = 0 := by
  have hM := mass_eq_zero hh hS
  obtain ⟨-, -, iM, -⟩ := integrableOn_planar hh
  have hae := (setIntegral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun p => massF_nonneg p) (iM.mono_set fullDomain_subset_rectangle)).mp hM
  set U : Set (ℝ × ℝ) := Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Ioo 1 2 with hUdef
  have hU : U ⊆ fullDomain := fun p hp =>
    ⟨Ioo_subset_Icc_self hp.1, (arcHeight_le_one (Ioo_subset_Icc_self hp.1)).trans hp.2.1.le⟩
  have hUo : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hcU : ContinuousOn (massF h) U :=
    (continuousOn_planar hh).2.2.1.mono (fun p hp => show 0 < p.2 by linarith [hp.2.1])
  have heq := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset hU hae) hUo hcU
    continuous_zero.continuousOn
  have hzero : ∀ x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2), cosSeries h (point x (3 / 2)) = 0 := by
    intro x hx
    have h1 := heq (show (x, (3 / 2 : ℝ)) ∈ U from ⟨hx, by norm_num, by norm_num⟩)
    simp only [massF, sqF, Pi.zero_apply] at h1
    rw [div_eq_zero_iff, or_iff_left (by norm_num)] at h1
    exact Complex.normSq_eq_zero.mp h1
  have hcont : ContinuousOn (fun x : ℝ => cosSeries h (point x (3 / 2)))
      (Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
    ((contDiffOn_cosSeries hh).continuousOn.comp_continuous (by unfold point; fun_prop)
      (fun x => show 0 < (point x (3 / 2)).im by rw [point_im]; norm_num)).continuousOn
  have hzero' : EqOn (fun x : ℝ => cosSeries h (point x (3 / 2))) (fun _ => 0)
      (Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
    EqOn.of_subset_closure (fun x hx => hzero x hx) hcont continuousOn_const Ioo_subset_Icc_self
      (by rw [closure_Ioo (by norm_num)])
  have hint := integral_cosSeries_mul_cos_eq hh hm (by norm_num : (0 : ℝ) < 3 / 2)
  have hint0 : ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
      cosSeries h (point x (3 / 2)) * (Real.cos (2 * Real.pi * m * x) : ℂ) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) (fun x hx => ?_)]
    · simp
    rw [uIcc_of_le (by norm_num)] at hx
    show cosSeries h (point x (3 / 2)) * (Real.cos (2 * Real.pi * m * x) : ℂ) = 0
    have hx0 : cosSeries h (point x (3 / 2)) = 0 := hzero' hx
    rw [hx0, zero_mul]
  rw [hint0] at hint
  have hy := yPart_pos hm (by norm_num : (0 : ℝ) < 3 / 2)
  have hprod : h m * (yPart (1 / 2) 0 0 m (3 / 2) : ℂ) = 0 := by
    linear_combination (-2 : ℂ) * hint
  rcases mul_eq_zero.mp hprod with h0 | h0
  · exact h0
  · exact absurd h0 (by exact_mod_cast hy.ne')

end RHTower.MaassLevelOneCuspVanishing
