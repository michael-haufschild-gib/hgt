import GaloisForLFunctions.RHTower.RiemannKernelCuspSeries

/-!
# Riemann's kernel on the strip `|Im z| < π/4`

For a real polynomial `R` the complex cusp series

  `S_R(z) = Σ_{n≥1} e^{z/2} R(n²e^{2z}) e^{−πn²e^{2z}}`

converges locally uniformly on the strip `|Im z| < π/4`, where `Re e^{2z} = e^{2 Re z}cos(2 Im z) > 0`.
It is holomorphic there (`differentiableAt_cseries`) and equals the real cusp series on `ℝ`.
`Φ(z) = S_R(z)` with `R = 4π²X² − 6πX` is the holomorphic extension of Riemann's kernel
(`kernelC_ofReal`).  By the identity theorem, the real evenness `Φ(−u) = Φ(u)` persists on the strip
(`kernelC_neg`).

For `Re z ≥ 0` and `|Im z| ≤ c < π/4` each term is at most `B K e^{Re z/2} e^{−a n² e^{2 Re z}}`
with `a = (π/2)cos 2c`.  Summing the geometric tail gives the super-exponential bound
`e^{Re z/2 − a e^{2 Re z}}`; evenness transfers it to `Re z ≤ 0`.  The result is
`|Φ(z)| ≤ C_r e^{−r|Re z|}` on every closed substrip, for every `r ≥ 0`
(`exists_norm_kernelC_le`).
-/

open Complex Filter Topology Set Polynomial
open scoped Real

namespace RHTower.KernelStrip

noncomputable section

/-! ## The complex cusp series -/

/-- One complex cusp term `e^{z/2} R(n²e^{2z}) e^{−πn²e^{2z}}`. -/
def cterm (R : ℝ[X]) (n : ℕ) (z : ℂ) : ℂ :=
  cexp (z / 2) * aeval ((n : ℂ) ^ 2 * cexp (2 * z)) R *
    cexp (-(π : ℂ) * ((n : ℂ) ^ 2 * cexp (2 * z)))

/-- The complex cusp series `S_R(z) = Σ_{n≥1} e^{z/2} R(n²e^{2z}) e^{−πn²e^{2z}}`. -/
def cseries (R : ℝ[X]) (z : ℂ) : ℂ := ∑' n : ℕ, cterm R (n + 1) z

/-- Riemann's kernel on the strip. -/
def kernelC (z : ℂ) : ℂ := cseries riemannCuspPoly z

theorem aeval_ofReal (R : ℝ[X]) (x : ℝ) : aeval (x : ℂ) R = ((R.eval x : ℝ) : ℂ) := by
  have h := Polynomial.aeval_algebraMap_apply ℂ x R
  simpa [Polynomial.coe_aeval_eq_eval] using h

theorem cterm_ofReal (R : ℝ[X]) (n : ℕ) (u : ℝ) : cterm R n u = (cuspTerm R n u : ℂ) := by
  have h1 : (n : ℂ) ^ 2 * cexp (2 * (u : ℂ)) = (((n : ℝ) ^ 2 * Real.exp (2 * u) : ℝ) : ℂ) := by
    push_cast; ring
  rw [cterm, cuspTerm, h1, aeval_ofReal]
  push_cast
  ring_nf

theorem cseries_ofReal (R : ℝ[X]) (u : ℝ) : cseries R u = (cuspSeries R u : ℂ) := by
  rw [cseries, cuspSeries, Complex.ofReal_tsum]
  exact tsum_congr fun n => cterm_ofReal R (n + 1) u

theorem kernelC_ofReal (u : ℝ) : kernelC u = riemannPhiKernel u := by
  rw [kernelC, cseries_ofReal, riemannPhiKernel_eq_cuspSeries]

theorem differentiable_cterm (R : ℝ[X]) (n : ℕ) : Differentiable ℂ (cterm R n) := by
  intro z
  unfold cterm
  have hp : Differentiable ℂ (fun w : ℂ => aeval w R) := Polynomial.differentiable_aeval R
  fun_prop

/-! ## Term bounds -/

theorem norm_aeval_le (R : ℝ[X]) (w : ℂ) :
    ‖aeval w R‖ ≤ polyAbsBound R * (1 + ‖w‖) ^ R.natDegree := by
  rw [aeval_eq_sum_range]
  refine (norm_sum_le _ _).trans ?_
  unfold polyAbsBound
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [norm_smul, norm_pow, Real.norm_eq_abs]
  have hj' : j ≤ R.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hw := norm_nonneg w
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc ‖w‖ ^ j ≤ (1 + ‖w‖) ^ j := pow_le_pow_left₀ hw (by linarith) j
    _ ≤ (1 + ‖w‖) ^ R.natDegree := pow_le_pow_right₀ (by linarith) hj'

/-- `(1+t)^d e^{−2at} ≤ (d!/a^d) e^a e^{−at}`. -/
theorem one_add_pow_mul_exp_le (d : ℕ) {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    (1 + t) ^ d * Real.exp (-(2 * a * t)) ≤
      d.factorial / a ^ d * Real.exp a * Real.exp (-(a * t)) := by
  have h := Real.pow_div_factorial_le_exp (a * (1 + t)) (by positivity) d
  rw [div_le_iff₀ (by positivity), mul_pow] at h
  have hf : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
  have had : 0 < a ^ d := pow_pos ha d
  have h2 : (1 + t) ^ d ≤ d.factorial / a ^ d * Real.exp (a * (1 + t)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ had]
    nlinarith
  have e : Real.exp (a * (1 + t)) * Real.exp (-(2 * a * t)) = Real.exp a * Real.exp (-(a * t)) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  calc (1 + t) ^ d * Real.exp (-(2 * a * t))
      ≤ d.factorial / a ^ d * Real.exp (a * (1 + t)) * Real.exp (-(2 * a * t)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = d.factorial / a ^ d * Real.exp a * Real.exp (-(a * t)) := by
        rw [mul_assoc, e]; ring

theorem re_neg_pi_mul (n : ℕ) (z : ℂ) :
    (-(π : ℂ) * ((n : ℂ) ^ 2 * cexp (2 * z))).re =
      -(π * ((n : ℝ) ^ 2 * Real.exp (2 * z.re))) * Real.cos (2 * z.im) := by
  have e : -(π : ℂ) * ((n : ℂ) ^ 2 * cexp (2 * z)) =
      ((-(π * (n : ℝ) ^ 2) : ℝ) : ℂ) * cexp (2 * z) := by push_cast; ring
  rw [e, Complex.re_ofReal_mul, Complex.exp_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    sub_zero, add_zero]
  ring

/-- The constant `(d!/a^d) e^a · Σ|coeff|` of the term bound. -/
def termConst (R : ℝ[X]) (a : ℝ) : ℝ :=
  polyAbsBound R * (R.natDegree.factorial / a ^ R.natDegree * Real.exp a)

theorem termConst_nonneg (R : ℝ[X]) {a : ℝ} (ha : 0 < a) : 0 ≤ termConst R a := by
  unfold termConst
  have := polyAbsBound_nonneg R
  positivity

/-- **Term bound.** If `2a ≤ π cos(2 Im z)` with `a > 0`, then
`|e^{z/2}R(n²e^{2z})e^{−πn²e^{2z}}| ≤ B_R K e^{Re z/2} e^{−a n² e^{2 Re z}}`. -/
theorem norm_cterm_le (R : ℝ[X]) (n : ℕ) {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : 2 * a ≤ π * Real.cos (2 * z.im)) :
    ‖cterm R n z‖ ≤ termConst R a * Real.exp (z.re / 2) *
      Real.exp (-(a * ((n : ℝ) ^ 2 * Real.exp (2 * z.re)))) := by
  set t : ℝ := (n : ℝ) ^ 2 * Real.exp (2 * z.re) with ht
  have ht0 : 0 ≤ t := by positivity
  have hw : ‖(n : ℂ) ^ 2 * cexp (2 * z)‖ = t := by
    rw [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_exp]
    simp [ht]
  have h1 : ‖cexp (z / 2)‖ = Real.exp (z.re / 2) := by
    rw [Complex.norm_exp]; simp
  have h2 : ‖aeval ((n : ℂ) ^ 2 * cexp (2 * z)) R‖ ≤ polyAbsBound R * (1 + t) ^ R.natDegree := by
    rw [← hw]; exact norm_aeval_le R _
  have h3 : ‖cexp (-(π : ℂ) * ((n : ℂ) ^ 2 * cexp (2 * z)))‖ ≤ Real.exp (-(2 * a * t)) := by
    rw [Complex.norm_exp, re_neg_pi_mul]
    apply Real.exp_le_exp.mpr
    have : 2 * a * t ≤ π * t * Real.cos (2 * z.im) := by nlinarith
    rw [← ht]; nlinarith
  have h4 := one_add_pow_mul_exp_le R.natDegree ha ht0
  have hB := polyAbsBound_nonneg R
  rw [cterm, norm_mul, norm_mul, h1]
  calc Real.exp (z.re / 2) * ‖aeval ((n : ℂ) ^ 2 * cexp (2 * z)) R‖ *
        ‖cexp (-(π : ℂ) * ((n : ℂ) ^ 2 * cexp (2 * z)))‖
      ≤ Real.exp (z.re / 2) * (polyAbsBound R * (1 + t) ^ R.natDegree) *
          Real.exp (-(2 * a * t)) := by gcongr
    _ = Real.exp (z.re / 2) * polyAbsBound R * ((1 + t) ^ R.natDegree * Real.exp (-(2 * a * t))) := by
        ring
    _ ≤ Real.exp (z.re / 2) * polyAbsBound R *
          (R.natDegree.factorial / a ^ R.natDegree * Real.exp a * Real.exp (-(a * t))) := by gcongr
    _ = termConst R a * Real.exp (z.re / 2) * Real.exp (-(a * t)) := by
        unfold termConst; ring

/-! ## Holomorphy on the strip -/

/-- `e^{u/2}e^{−a(n+1)²e^{2u}} ≤ (1 + 2/a) e^{−(a/2)(n+1)e^{2v}}` for `u > v`. -/
theorem exp_half_mul_exp_le {a : ℝ} (ha : 0 < a) (n : ℕ) {u v : ℝ} (huv : v ≤ u) :
    Real.exp (u / 2) * Real.exp (-(a * (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)))) ≤
      (1 + 2 / a) * Real.exp (-(a / 2 * Real.exp (2 * v) * ((n + 1 : ℕ) : ℝ))) := by
  set s := Real.exp (2 * u) with hs
  have hs0 : 0 < s := Real.exp_pos _
  have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hhalf : Real.exp (u / 2) ≤ 1 + s := by
    rcases le_or_gt u 0 with hu | hu
    · have : Real.exp (u / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
    · have : Real.exp (u / 2) ≤ s := Real.exp_le_exp.mpr (by linarith)
      linarith
  have hlin : 1 + s ≤ (1 + 2 / a) * Real.exp (a / 2 * s) := by
    have h1 := Real.add_one_le_exp (a / 2 * s)
    have h2 : (1 : ℝ) ≤ Real.exp (a / 2 * s) := Real.one_le_exp (by positivity)
    have h3 : s ≤ 2 / a * Real.exp (a / 2 * s) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ ha]; nlinarith
    nlinarith
  have hsv : Real.exp (2 * v) ≤ s := Real.exp_le_exp.mpr (by linarith)
  have hexp : a / 2 * s - a * (((n + 1 : ℕ) : ℝ) ^ 2 * s) ≤
      -(a / 2 * Real.exp (2 * v) * ((n + 1 : ℕ) : ℝ)) := by
    have hsq : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
    have h1 : a / 2 * Real.exp (2 * v) * ((n + 1 : ℕ) : ℝ) ≤ a / 2 * s * ((n + 1 : ℕ) : ℝ) ^ 2 := by
      have := mul_le_mul hsv hsq (by positivity) hs0.le
      nlinarith
    have h2 : a / 2 * s ≤ a / 2 * s * ((n + 1 : ℕ) : ℝ) ^ 2 :=
      le_mul_of_one_le_right (by positivity) (by nlinarith)
    linarith
  calc Real.exp (u / 2) * Real.exp (-(a * (((n + 1 : ℕ) : ℝ) ^ 2 * s)))
      ≤ (1 + 2 / a) * Real.exp (a / 2 * s) * Real.exp (-(a * (((n + 1 : ℕ) : ℝ) ^ 2 * s))) :=
        mul_le_mul_of_nonneg_right (hhalf.trans hlin) (Real.exp_pos _).le
    _ = (1 + 2 / a) * Real.exp (a / 2 * s - a * (((n + 1 : ℕ) : ℝ) ^ 2 * s)) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ (1 + 2 / a) * Real.exp (-(a / 2 * Real.exp (2 * v) * ((n + 1 : ℕ) : ℝ))) := by
        gcongr

theorem summable_exp_neg_mul_succ {b : ℝ} (hb : 0 < b) :
    Summable fun n : ℕ => Real.exp (-(b * ((n + 1 : ℕ) : ℝ))) := by
  have h := summable_cuspTerm_bound 0 hb
  refine h.congr fun n => ?_
  simp only [pow_zero, one_mul, neg_mul]

/-- `cos(2y) ≥ cos(2c)` for `|y| ≤ c ≤ π/2`. -/
theorem cos_two_mul_ge {c y : ℝ} (hc : c ≤ π / 2) (hy : |y| ≤ c) :
    Real.cos (2 * c) ≤ Real.cos (2 * y) := by
  rw [← Real.cos_abs (2 * y), abs_mul, abs_two]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)

theorem differentiableOn_cseries (R : ℝ[X]) {c v : ℝ} (hc0 : 0 ≤ c) (hc : c < π / 4) :
    DifferentiableOn ℂ (cseries R) {w : ℂ | |w.im| < c ∧ v < w.re} := by
  have hπ := Real.pi_pos
  set κ := Real.cos (2 * c)
  have hκ : 0 < κ := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  set a := π * κ / 2 with ha
  have ha0 : 0 < a := by positivity
  have hopen : IsOpen {w : ℂ | |w.im| < c ∧ v < w.re} :=
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_re)
  refine differentiableOn_tsum_of_summable_norm
    (u := fun n : ℕ => termConst R a * ((1 + 2 / a) *
      Real.exp (-(a / 2 * Real.exp (2 * v) * ((n + 1 : ℕ) : ℝ)))))
    ((summable_exp_neg_mul_succ (by positivity)).mul_left _ |>.mul_left _)
    (fun n => (differentiable_cterm R (n + 1)).differentiableOn) hopen (fun n w hw => ?_)
  have hcos : 2 * a ≤ π * Real.cos (2 * w.im) := by
    have := cos_two_mul_ge (c := c) (y := w.im) (by linarith) hw.1.le
    rw [ha]; nlinarith
  have h1 := norm_cterm_le R (n + 1) ha0 hcos
  have h2 := exp_half_mul_exp_le ha0 n hw.2.le
  have hK := termConst_nonneg R ha0
  calc ‖cterm R (n + 1) w‖ ≤ termConst R a * Real.exp (w.re / 2) *
        Real.exp (-(a * (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * w.re)))) := h1
    _ = termConst R a * (Real.exp (w.re / 2) *
        Real.exp (-(a * (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * w.re))))) := by ring
    _ ≤ termConst R a * ((1 + 2 / a) *
        Real.exp (-(a / 2 * Real.exp (2 * v) * ((n + 1 : ℕ) : ℝ)))) :=
        mul_le_mul_of_nonneg_left h2 hK

/-- **Holomorphy.**  The complex cusp series is holomorphic on `|Im z| < π/4`. -/
theorem differentiableAt_cseries (R : ℝ[X]) {z : ℂ} (hz : |z.im| < π / 4) :
    DifferentiableAt ℂ (cseries R) z := by
  set c := (|z.im| + π / 4) / 2
  have hc : c < π / 4 := by simp only [c]; linarith
  have hmem : z ∈ {w : ℂ | |w.im| < c ∧ z.re - 1 < w.re} :=
    ⟨by simp only [c]; linarith, by linarith⟩
  have hopen : IsOpen {w : ℂ | |w.im| < c ∧ z.re - 1 < w.re} :=
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_re)
  exact ((differentiableOn_cseries R (v := z.re - 1) (by positivity) hc) z hmem).differentiableAt
    (hopen.mem_nhds hmem)

theorem differentiableAt_kernelC {z : ℂ} (hz : |z.im| < π / 4) : DifferentiableAt ℂ kernelC z :=
  differentiableAt_cseries riemannCuspPoly hz

/-! ## Evenness on the strip -/

/-- The strip `|Im z| < π/4`, as an intersection of half-planes. -/
def strip : Set ℂ := {w : ℂ | w.im < π / 4} ∩ {w : ℂ | -(π / 4) < w.im}

theorem mem_strip {z : ℂ} : z ∈ strip ↔ |z.im| < π / 4 := by
  simp only [strip, Set.mem_inter_iff, Set.mem_setOf_eq, abs_lt]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem isOpen_strip : IsOpen strip :=
  (isOpen_lt Complex.continuous_im continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_im)

/-- **Evenness.** `Φ(−z) = Φ(z)` on `|Im z| < π/4`. -/
theorem kernelC_neg {z : ℂ} (hz : |z.im| < π / 4) : kernelC (-z) = kernelC z := by
  have hf : DifferentiableOn ℂ kernelC strip := fun w hw =>
    (differentiableAt_kernelC (mem_strip.mp hw)).differentiableWithinAt
  have hg : DifferentiableOn ℂ (fun w => kernelC (-w)) strip := fun w hw => by
    have h : |(-w).im| < π / 4 := by rw [Complex.neg_im, abs_neg]; exact mem_strip.mp hw
    exact ((differentiableAt_kernelC h).comp w differentiableAt_id.neg).differentiableWithinAt
  have hconv : Convex ℝ strip := (convex_halfSpace_im_lt _).inter (convex_halfSpace_im_gt _)
  have h0 : (0 : ℂ) ∈ strip := mem_strip.mpr (by simp [Real.pi_pos])
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), (fun w => kernelC (-w)) w = kernelC w := by
    set u : ℕ → ℂ := fun k => ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) with hu
    have hlim : Tendsto u atTop (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have h : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have h2 := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp h
        rw [Complex.ofReal_zero] at h2
        exact h2
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hu]
        intro h
        have h' : (1 / ((k : ℝ) + 1) : ℝ) = 0 := by exact_mod_cast h
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    refine hlim.frequently (Frequently.of_forall fun k => ?_)
    simp only [hu]
    rw [← Complex.ofReal_neg, kernelC_ofReal, kernelC_ofReal, riemannPhiKernel_neg]
  have heq := (hg.analyticOnNhd isOpen_strip).eqOn_of_preconnected_of_frequently_eq
    (hf.analyticOnNhd isOpen_strip) hconv.isPreconnected h0 hfreq
  exact heq (mem_strip.mpr hz)

/-! ## Decay -/

/-- `e^{u/2 − a e^{2u}} ≤ e^{(r+½)²/(8a)} e^{−ru}` for `u ≥ 0`. -/
theorem exp_half_sub_le {a r u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    Real.exp (u / 2) * Real.exp (-(a * Real.exp (2 * u))) ≤
      Real.exp ((r + 1 / 2) ^ 2 / (8 * a)) * Real.exp (-(r * u)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := Real.pow_div_factorial_le_exp (2 * u) (by linarith) 2
  norm_num at h
  have hq : (r + 1 / 2) * u - 2 * a * u ^ 2 ≤ (r + 1 / 2) ^ 2 / (8 * a) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (4 * a * u - (r + 1 / 2))]
  have h2 : 2 * a * u ^ 2 ≤ a * Real.exp (2 * u) := by nlinarith
  linarith

/-- For `Re z ≥ 0` and `|Im z| ≤ c < π/4`: `|S_R(z)| ≤ C e^{Re z/2 − a e^{2 Re z}}`. -/
theorem norm_cseries_le_of_re_nonneg (R : ℝ[X]) {c : ℝ} (hc : c < π / 4) {z : ℂ}
    (hz : |z.im| ≤ c) (hre : 0 ≤ z.re) :
    ‖cseries R z‖ ≤ termConst R (π * Real.cos (2 * c) / 2) /
        (1 - Real.exp (-(π * Real.cos (2 * c) / 2))) *
      (Real.exp (z.re / 2) * Real.exp (-(π * Real.cos (2 * c) / 2 * Real.exp (2 * z.re)))) := by
  have hπ := Real.pi_pos
  have hc0 : 0 ≤ c := (abs_nonneg _).trans hz
  set κ := Real.cos (2 * c)
  have hκ : 0 < κ := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  set a := π * κ / 2 with ha
  have ha0 : 0 < a := by positivity
  have hcos : 2 * a ≤ π * Real.cos (2 * z.im) := by
    have := cos_two_mul_ge (c := c) (y := z.im) (by linarith) hz
    rw [ha]; nlinarith
  set s := Real.exp (2 * z.re) with hs
  have hs1 : 1 ≤ s := Real.one_le_exp (by linarith)
  set q := Real.exp (-(a * s)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by nlinarith)
  have hea : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hqlt : q < 1 := hq1.trans_lt hea
  have hK := termConst_nonneg R ha0
  -- termwise bound by a geometric series
  have hterm : ∀ n : ℕ, ‖cterm R (n + 1) z‖ ≤
      termConst R a * Real.exp (z.re / 2) * (q * q ^ n) := by
    intro n
    refine (norm_cterm_le R (n + 1) ha0 hcos).trans ?_
    have hn1 : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      nlinarith
    have hpow : q * q ^ n = Real.exp (-(a * s * ((n + 1 : ℕ) : ℝ))) := by
      rw [← pow_succ', hq, ← Real.exp_nat_mul]; push_cast; ring_nf
    rw [hpow]
    have hx : a * s * ((n + 1 : ℕ) : ℝ) ≤ a * (((n + 1 : ℕ) : ℝ) ^ 2 * s) := by
      have := mul_le_mul_of_nonneg_left hn1 (by positivity : (0 : ℝ) ≤ a * s)
      linarith
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
  have hgeom : Summable fun n : ℕ => termConst R a * Real.exp (z.re / 2) * (q * q ^ n) :=
    ((summable_geometric_of_lt_one hq0 hqlt).mul_left q).mul_left _
  have hnorm : Summable fun n : ℕ => ‖cterm R (n + 1) z‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hgeom
  have hsum : ∑' n : ℕ, termConst R a * Real.exp (z.re / 2) * (q * q ^ n) =
      termConst R a * Real.exp (z.re / 2) * (q * (1 - q)⁻¹) := by
    rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hq0 hqlt]
  calc ‖cseries R z‖ ≤ ∑' n : ℕ, ‖cterm R (n + 1) z‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, termConst R a * Real.exp (z.re / 2) * (q * q ^ n) :=
        Summable.tsum_le_tsum hterm hnorm hgeom
    _ = termConst R a * Real.exp (z.re / 2) * (q * (1 - q)⁻¹) := hsum
    _ ≤ termConst R a * Real.exp (z.re / 2) * (q * (1 - Real.exp (-a))⁻¹) := by
        gcongr
    _ = termConst R a / (1 - Real.exp (-a)) * (Real.exp (z.re / 2) * q) := by
        rw [div_eq_mul_inv]; ring

/-- **Decay.**  For `0 ≤ c < π/4` and `r ≥ 0` there is `C` with `|Φ(z)| ≤ C e^{−r|Re z|}` whenever
`|Im z| ≤ c`. -/
theorem exists_norm_kernelC_le {c : ℝ} (hc : c < π / 4) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ c → ‖kernelC z‖ ≤ C * Real.exp (-(r * |z.re|)) := by
  have hπ := Real.pi_pos
  set a := π * Real.cos (2 * c) / 2 with ha
  by_cases hc0 : c < 0
  · refine ⟨0, le_rfl, fun z hz => ?_⟩
    exact absurd ((abs_nonneg _).trans hz) (not_le.mpr hc0)
  push Not at hc0
  have hκ : 0 < Real.cos (2 * c) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have ha0 : 0 < a := by positivity
  have hea : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  set C := termConst riemannCuspPoly a / (1 - Real.exp (-a)) *
    Real.exp ((r + 1 / 2) ^ 2 / (8 * a)) with hC
  have hC0 : 0 ≤ C := by
    have := termConst_nonneg riemannCuspPoly ha0
    have : 0 < 1 - Real.exp (-a) := by linarith
    positivity
  have hpos : ∀ z : ℂ, |z.im| ≤ c → 0 ≤ z.re →
      ‖kernelC z‖ ≤ C * Real.exp (-(r * |z.re|)) := by
    intro z hz hre
    have h1 := norm_cseries_le_of_re_nonneg riemannCuspPoly hc hz hre
    have h2 := exp_half_sub_le (r := r) ha0 hre
    have hk : 0 ≤ termConst riemannCuspPoly a / (1 - Real.exp (-a)) := by
      have := termConst_nonneg riemannCuspPoly ha0
      have : 0 < 1 - Real.exp (-a) := by linarith
      positivity
    rw [abs_of_nonneg hre]
    calc ‖kernelC z‖ ≤ termConst riemannCuspPoly a / (1 - Real.exp (-a)) *
          (Real.exp (z.re / 2) * Real.exp (-(a * Real.exp (2 * z.re)))) := h1
      _ ≤ termConst riemannCuspPoly a / (1 - Real.exp (-a)) *
          (Real.exp ((r + 1 / 2) ^ 2 / (8 * a)) * Real.exp (-(r * z.re))) :=
          mul_le_mul_of_nonneg_left h2 hk
      _ = C * Real.exp (-(r * z.re)) := by rw [hC]; ring
  refine ⟨C, hC0, fun z hz => ?_⟩
  rcases le_or_gt 0 z.re with hre | hre
  · exact hpos z hz hre
  · have hz' : |(-z).im| ≤ c := by rw [Complex.neg_im, abs_neg]; exact hz
    have hlt : |z.im| < π / 4 := lt_of_le_of_lt hz hc
    have h := hpos (-z) hz' (by rw [Complex.neg_re]; linarith)
    rw [kernelC_neg hlt, Complex.neg_re, abs_neg] at h
    exact h

end

end RHTower.KernelStrip
