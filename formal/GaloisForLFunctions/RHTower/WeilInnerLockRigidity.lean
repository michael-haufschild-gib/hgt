import GaloisForLFunctions.RHTower.WeilLockPhasePositivity

/-!
# Inner locks are trivial

Let `G` be a Herglotz producer for the weights `lam` with lower-line lock

`G(1 − s) = V(s) G(s)`,  `s = ½ + 2iτ`,  `τ < 0`,

where `V` is holomorphic on a strip neighbourhood `½ − δ < Re s < ½ + δ`, `Im s < 0`, of the lower
critical line.

**Theorem** (`inner_lock_rigidity`).  If `|V| ≤ 1` on the left half `½ − δ < Re s < ½` of that
neighbourhood, then `lam(n) = Λ(n)` for all `n ≥ 2`, and the Riemann hypothesis holds.

**Proof.**
* Near a boundary non-zero `b` of `G`, a continuous logarithm `L` of `G` reaches the line, and the
  real structure `G(s̄) = conj G(s)` turns the lock into `V = e^{−2i Im L}` on the line.  Put
  `ℓ = log(V/V(b))`, so `ℓ' (b) = V'(b)/V(b)`.
* On the line `ℓ(½ − 2ix) = i(w(x) − w(x₀))` with `w = −2 Im L`.  So `Re ℓ` vanishes there, giving
  `Im ℓ'(b) = 0`.  Positivity makes `w` nondecreasing (`boundary_phase_antitone`), giving
  `Re ℓ'(b) ≤ 0`.
* `Re ℓ = log |V| ≤ 0` to the left of the line and `= 0` at `b`, giving `Re ℓ'(b) ≥ 0`.
* Hence `V'(b) = 0` at every boundary non-zero.  These are dense (`exists_ne_zero_mem_Ioo`) and
  `V'` is continuous, so `V` is constant on the lower line, and `phase_lock_rigidity` applies.

Positivity orients every lock: its phase `arg V(½ + iy)` is nonincreasing in `y`, while an inner
factor to the left of the line has nondecreasing phase.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity

noncomputable section

/-- The lock is unimodular at every boundary non-zero of the producer. -/
theorem norm_lock_eq_one_of_ne_zero {lam : ℕ → ℝ} {Φ G V : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = V (lineS τ) * G (lineS τ))
    {x : ℝ} (hx : 0 < x) (hG0 : G (vpt (1 / 2) x) ≠ 0) : ‖V (vpt (1 / 2) x)‖ = 1 := by
  have hre : (1 / 2 : ℝ) ≤ (vpt (1 / 2) x).re := by simp
  have hconj : 1 - vpt (1 / 2) x = conj (vpt (1 / 2) x) := by
    rw [← lineS_neg_eq_vpt, one_sub_lineS_eq_conj]
  have hl := hlock (-x) (by linarith)
  rw [lineS_neg_eq_vpt, hconj, G_conj hsl hid hGc hGd hG2 hre] at hl
  have hn := congrArg norm hl
  rw [Complex.norm_conj, norm_mul] at hn
  have hGn : 0 < ‖G (vpt (1 / 2) x)‖ := norm_pos_iff.mpr hG0
  nlinarith [norm_nonneg (V (vpt (1 / 2) x))]

/-- **At a boundary non-zero of the producer an inner lock is stationary.** -/
theorem deriv_inner_lock_eq_zero {lam : ℕ → ℝ} {Φ G V : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {δ : ℝ} (hδ : 0 < δ)
    (hVd : ∀ s : ℂ, 1 / 2 - δ < s.re → s.re < 1 / 2 + δ → s.im < 0 → DifferentiableAt ℂ V s)
    (hVin : ∀ s : ℂ, 1 / 2 - δ < s.re → s.re < 1 / 2 → s.im < 0 → ‖V s‖ ≤ 1)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = V (lineS τ) * G (lineS τ))
    {x₀ : ℝ} (hx₀ : 0 < x₀) (hG0 : G (vpt (1 / 2) x₀) ≠ 0) :
    deriv V (vpt (1 / 2) x₀) = 0 := by
  have hpi := Real.pi_pos
  have hG20 : G 2 ≠ 0 := G_ne_zero hΦd hGd hG2 (by norm_num : (1 / 2 : ℝ) < (2 : ℂ).re)
  obtain ⟨P, hP, hPG⟩ := exists_log_producer hΦd hGd
  set b : ℂ := vpt (1 / 2) x₀ with hb
  have hbre : (1 / 2 : ℝ) ≤ b.re := by simp [hb]
  have hbim : b.im = -(2 * x₀) := by simp [hb, vpt]
  obtain ⟨r, hr0, L, hLc, hGL, hLP⟩ := exists_local_log hGc hGd hP hPG hbre hG0
  -- the lock on the line near `b`, through the boundary logarithm
  set w : ℝ → ℝ := fun x => -2 * (L (vpt (1 / 2) x)).im with hw
  have hVline : ∀ x : ℝ, 0 < x → vpt (1 / 2) x ∈ Metric.ball b r →
      V (vpt (1 / 2) x) = cexp ((w x : ℂ) * I) := by
    intro x hx hxb
    have hre : (1 / 2 : ℝ) ≤ (vpt (1 / 2) x).re := by simp
    have hGx := hGL _ hxb hre
    have hconj : 1 - vpt (1 / 2) x = conj (vpt (1 / 2) x) := by
      rw [← lineS_neg_eq_vpt, one_sub_lineS_eq_conj]
    have hl := hlock (-x) (by linarith)
    rw [lineS_neg_eq_vpt, hconj, G_conj hsl hid hGc hGd hG2 hre, hGx, map_mul,
      ← Complex.exp_conj, hG2, bigG_two_conj, ← hG2] at hl
    have e1 : conj (L (vpt (1 / 2) x)) = L (vpt (1 / 2) x) + (w x : ℂ) * I := by
      apply Complex.ext <;> simp [hw]; ring
    rw [e1, Complex.exp_add] at hl
    have hne : G 2 * cexp (L (vpt (1 / 2) x)) ≠ 0 := mul_ne_zero hG20 (Complex.exp_ne_zero _)
    apply mul_right_cancel₀ hne
    linear_combination -hl
  have hb_ball : b ∈ Metric.ball b r := Metric.mem_ball_self hr0
  have hVb : V b = cexp ((w x₀ : ℂ) * I) := hVline x₀ hx₀ hb_ball
  have hVb0 : V b ≠ 0 := by rw [hVb]; exact Complex.exp_ne_zero _
  have hVbn : ‖V b‖ = 1 := by rw [hVb]; exact Complex.norm_exp_ofReal_mul_I _
  -- the logarithm of the normalized lock
  set ℓ : ℂ → ℂ := fun s => Complex.log (V s / V b) with hℓ
  set D : ℂ := deriv V b / V b with hD
  have hbD : DifferentiableAt ℂ V b := hVd b (by rw [hb]; simp; linarith)
    (by rw [hb]; simp; linarith) (by rw [hbim]; linarith)
  have hℓd : HasDerivAt ℓ D b := by
    have h1 : HasDerivAt (fun s => V s / V b) (deriv V b / V b) b :=
      hbD.hasDerivAt.div_const (V b)
    have h2 := h1.clog (by rw [div_self hVb0]; exact Complex.one_mem_slitPlane)
    rwa [div_self hVb0, div_one] at h2
  have hℓb : ℓ b = 0 := by simp only [hℓ, div_self hVb0, Complex.log_one]
  -- `ℓ` on the line
  have hvc : Continuous fun x : ℝ => vpt (1 / 2) x := by unfold vpt; fun_prop
  have hball_ev : ∀ᶠ x in 𝓝 x₀, vpt (1 / 2) x ∈ Metric.ball b r :=
    (hvc.tendsto x₀) (Metric.isOpen_ball.mem_nhds hb_ball)
  have hwc : Tendsto w (𝓝 x₀) (𝓝 (w x₀)) := by
    have hS : b ∈ Metric.ball b r ∩ {s : ℂ | 1 / 2 ≤ s.re} := ⟨hb_ball, hbre⟩
    have ht : Tendsto (fun x : ℝ => vpt (1 / 2) x) (𝓝 x₀)
        (𝓝[Metric.ball b r ∩ {s : ℂ | 1 / 2 ≤ s.re}] b) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hvc.tendsto x₀, ?_⟩
      filter_upwards [hball_ev] with x hx
      exact ⟨hx, by simp⟩
    have hL := (hLc b hS).tendsto.comp ht
    exact ((Complex.continuous_im.tendsto _).comp hL).const_mul (-2)
  have hpi_ev : ∀ᶠ x in 𝓝 x₀, |w x - w x₀| < Real.pi := by
    have := Metric.tendsto_nhds.mp hwc Real.pi hpi
    filter_upwards [this] with x hx
    rwa [Real.dist_eq] at hx
  have hline_ev : ∀ᶠ x in 𝓝 x₀, ℓ (vpt (1 / 2) x) = ((w x - w x₀ : ℝ) : ℂ) * I := by
    filter_upwards [hball_ev, hpi_ev, Ioi_mem_nhds hx₀] with x hxb hxpi hxpos
    have hratio : V (vpt (1 / 2) x) / V b = cexp (((w x - w x₀ : ℝ) : ℂ) * I) := by
      rw [hVline x hxpos hxb, hVb, ← Complex.exp_sub]
      congr 1
      push_cast
      ring
    simp only [hℓ]
    rw [hratio]
    apply Complex.log_exp
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, mul_one]
      linarith [(abs_lt.mp hxpi).1]
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, mul_one]
      linarith [(abs_lt.mp hxpi).2]
  have hm : HasDerivAt (fun x : ℝ => ℓ (vpt (1 / 2) x)) (D * (-2 * I)) x₀ := by
    have h := hℓd.comp x₀ (hasDerivAt_vpt (1 / 2) x₀)
    exact h
  have hslope_m : Tendsto (slope (fun x : ℝ => ℓ (vpt (1 / 2) x)) x₀) (𝓝[≠] x₀)
      (𝓝 (D * (-2 * I))) := hasDerivAt_iff_tendsto_slope.mp hm
  -- the real part vanishes along the line: `Im D = 0`
  have hDim : D.im = 0 := by
    have hre := (Complex.continuous_re.tendsto _).comp hslope_m
    have hev : ∀ᶠ x in 𝓝[≠] x₀,
        (fun _ : ℝ => (0 : ℝ)) x =
          (Complex.re ∘ slope (fun x : ℝ => ℓ (vpt (1 / 2) x)) x₀) x := by
      filter_upwards [nhdsWithin_le_nhds hline_ev] with x hx
      simp only [Function.comp_apply, slope_def_module]
      rw [hx, ← hb, hℓb]
      simp
    have h0 := tendsto_nhds_unique hre (tendsto_const_nhds.congr' hev)
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im] at h0
    norm_num at h0
    linarith
  -- positivity: the imaginary part is nondecreasing along the line, so `Re D ≤ 0`
  have hDre_le : D.re ≤ 0 := by
    have him : Tendsto (Complex.im ∘ slope (fun x : ℝ => ℓ (vpt (1 / 2) x)) x₀) (𝓝[>] x₀)
        (𝓝 (D * (-2 * I)).im) := ((Complex.continuous_im.tendsto _).comp hslope_m).mono_left
      (nhdsWithin_mono _ fun z (hz : x₀ < z) => ne_of_gt hz)
    have hge : 0 ≤ (D * (-2 * I)).im := by
      refine ge_of_tendsto him ?_
      filter_upwards [nhdsWithin_le_nhds hline_ev, nhdsWithin_le_nhds hball_ev,
        self_mem_nhdsWithin] with x hx hxb hxgt
      have hxx : x₀ < x := hxgt
      have hmono := boundary_phase_antitone hP hΦre hLc hLP hxx.le hb_ball hxb
      have hwx : w x₀ ≤ w x := by simp only [hw]; linarith
      simp only [Function.comp_apply, slope_def_module]
      rw [hx, ← hb, hℓb]
      simp only [sub_zero, Complex.real_smul,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      have hinv : 0 ≤ (x - x₀)⁻¹ := inv_nonneg.mpr (by linarith)
      have hd : 0 ≤ w x - w x₀ := by linarith
      norm_num
      positivity
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im] at hge
    norm_num at hge
    linarith
  -- the inner side: `log |V| ≤ 0` to the left of the line, so `Re D ≥ 0`
  have hpt : (((1 / 2 : ℝ) : ℂ) + (b.im : ℂ) * I) = b := by
    apply Complex.ext <;> simp [hb, vpt]
  have hk : HasDerivAt (fun σ : ℝ => ℓ ((σ : ℂ) + (b.im : ℂ) * I)) D (1 / 2) := by
    have h1 : HasDerivAt (fun σ : ℝ => (σ : ℂ) + (b.im : ℂ) * I) 1 (1 / 2) := by
      simpa using ((hasDerivAt_id (1 / 2 : ℝ)).ofReal_comp).add_const ((b.im : ℂ) * I)
    have h2 : HasDerivAt ℓ D (((1 / 2 : ℝ) : ℂ) + (b.im : ℂ) * I) := by
      rw [hpt]; exact hℓd
    have h3 := h2.comp (1 / 2 : ℝ) h1
    rw [mul_one] at h3
    exact h3
  have hDre_ge : 0 ≤ D.re := by
    have hre : Tendsto (Complex.re ∘ slope (fun σ : ℝ => ℓ ((σ : ℂ) + (b.im : ℂ) * I)) (1 / 2))
        (𝓝[<] (1 / 2)) (𝓝 D.re) := ((Complex.continuous_re.tendsto _).comp
      (hasDerivAt_iff_tendsto_slope.mp hk)).mono_left
      (nhdsWithin_mono _ fun z (hz : z < 1 / 2) => ne_of_lt hz)
    refine ge_of_tendsto hre ?_
    filter_upwards [Ioo_mem_nhdsLT (show 1 / 2 - δ < 1 / 2 by linarith)] with σ hσ
    have h0 : ℓ (((1 / 2 : ℝ) : ℂ) + (b.im : ℂ) * I) = 0 := by rw [hpt, hℓb]
    have hlog : (ℓ ((σ : ℂ) + (b.im : ℂ) * I)).re ≤ 0 := by
      simp only [hℓ, Complex.log_re, norm_div, hVbn, div_one]
      apply Real.log_nonpos (norm_nonneg _)
      apply hVin
      · simp; linarith [hσ.1]
      · simp; linarith [hσ.2]
      · simp [hbim]; linarith
    have hinv : (σ - 1 / 2)⁻¹ ≤ 0 := inv_nonpos.mpr (by linarith [hσ.2])
    simp only [Function.comp_apply, slope_def_module, h0, sub_zero, Complex.real_smul,
      Complex.re_ofReal_mul]
    exact mul_nonneg_of_nonpos_of_nonpos hinv hlog
  have hD0 : D = 0 := Complex.ext (by simp; linarith) (by simpa using hDim)
  have : deriv V b = D * V b := by rw [hD, div_mul_cancel₀ _ hVb0]
  rw [this, hD0, zero_mul]

/-- **Inner locks are trivial.**  Let `G` be a Herglotz producer for the weights `lam` with
lower-line lock `G(1 − s) = V(s) G(s)`, `s = ½ + 2iτ`, `τ < 0`, where `V` is holomorphic on the strip
neighbourhood `½ − δ < Re s < ½ + δ`, `Im s < 0`, of the lower critical line and `|V| ≤ 1` on its
left half.  Then `lam(n) = Λ(n)` for all `n ≥ 2`, and the Riemann hypothesis holds. -/
theorem inner_lock_rigidity {lam : ℕ → ℝ} {Φ G V : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {δ : ℝ} (hδ : 0 < δ)
    (hVd : ∀ s : ℂ, 1 / 2 - δ < s.re → s.re < 1 / 2 + δ → s.im < 0 → DifferentiableAt ℂ V s)
    (hVin : ∀ s : ℂ, 1 / 2 - δ < s.re → s.re < 1 / 2 → s.im < 0 → ‖V s‖ ≤ 1)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = V (lineS τ) * G (lineS τ)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
  have hG20 : G 2 ≠ 0 := G_ne_zero hΦd hGd hG2 (by norm_num : (1 / 2 : ℝ) < (2 : ℂ).re)
  obtain ⟨P, hP, hPG⟩ := exists_log_producer hΦd hGd
  set D : Set ℂ := {s : ℂ | 1 / 2 - δ < s.re ∧ s.re < 1 / 2 + δ ∧ s.im < 0} with hDdef
  have hDo : IsOpen D := by
    have h1 : IsOpen {s : ℂ | 1 / 2 - δ < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2 : IsOpen {s : ℂ | s.re < 1 / 2 + δ} := isOpen_lt Complex.continuous_re continuous_const
    have h3 : IsOpen {s : ℂ | s.im < 0} := isOpen_lt Complex.continuous_im continuous_const
    convert (h1.inter h2).inter h3 using 1
    ext s
    simp [hDdef, and_assoc]
  have hVD : DifferentiableOn ℂ V D := fun s hs =>
    (hVd s hs.1 hs.2.1 hs.2.2).differentiableWithinAt
  have hdV : ContinuousOn (deriv V) D := (hVD.deriv hDo).continuousOn
  have hvc : Continuous fun x : ℝ => vpt (1 / 2) x := by unfold vpt; fun_prop
  have hvD : ∀ x : ℝ, 0 < x → vpt (1 / 2) x ∈ D := fun x hx =>
    ⟨by simp; linarith, by simp; linarith, by simp [vpt]; linarith⟩
  -- the derivative of the lock vanishes on the whole lower line
  have hzero : ∀ x : ℝ, 0 < x → deriv V (vpt (1 / 2) x) = 0 := by
    intro x hx
    by_contra hne
    have hc : ContinuousAt (fun y : ℝ => deriv V (vpt (1 / 2) y)) x :=
      (hdV.continuousAt (hDo.mem_nhds (hvD x hx))).comp hvc.continuousAt
    obtain ⟨ε, hε0, hε⟩ := Metric.eventually_nhds_iff.mp
      ((hc.eventually_ne hne).and (Ioi_mem_nhds hx))
    obtain ⟨y, hy1, hy2, hGy⟩ := exists_ne_zero_mem_Ioo hsl hΦd hΦre hidT hGc hGd hG2 hG20 hP hPG
      (show x - ε < x + ε by linarith)
    have hyx : dist y x < ε := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    obtain ⟨hne', hy0⟩ := hε hyx
    exact hne' (deriv_inner_lock_eq_zero hsl hΦd hΦre hidT hGc hGd hG2 hδ hVd hVin hlock
      (show 0 < y from hy0) hGy)
  -- hence the lock is constant on the lower line
  have hconst : ∀ x : ℝ, 0 < x → V (vpt (1 / 2) x) = V (vpt (1 / 2) 1) := by
    intro x hx
    have hderiv : ∀ y : ℝ, 0 < y →
        HasDerivAt (fun y : ℝ => V (vpt (1 / 2) y)) (deriv V (vpt (1 / 2) y) * (-2 * I)) y :=
      fun y hy => (hVd _ (hvD y hy).1 (hvD y hy).2.1 (hvD y hy).2.2).hasDerivAt.comp y
        (hasDerivAt_vpt (1 / 2) y)
    refine isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun y hy => (hderiv y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => ?_) (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr one_pos)
    rw [(hderiv y hy).deriv, hzero y hy, zero_mul]
    rfl
  -- the constant is unimodular
  set κ : ℂ := V (vpt (1 / 2) 1) with hκ
  obtain ⟨y₁, hy₁, -, hGy₁⟩ := exists_ne_zero_mem_Ioo hsl hΦd hΦre hidT hGc hGd hG2 hG20 hP hPG
    (show (0 : ℝ) < 1 by norm_num)
  have hκ0 : κ ≠ 0 := by
    have hn := norm_lock_eq_one_of_ne_zero hsl hidT hGc hGd hG2 hlock hy₁ hGy₁
    rw [hconst y₁ hy₁] at hn
    intro h
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  refine phase_lock_rigidity hsl hΦd hΦre hid hGc hGd hG2 le_rfl (inv_ne_zero hκ0)
    (fun y hy => ?_)
  have hl := hlock (-(y / 2)) (by linarith)
  rw [lineS_neg_eq_vpt, hconst (y / 2) (by linarith)] at hl
  have e1 : vpt (1 / 2) (y / 2) = 1 / 2 - (y : ℂ) * I := by unfold vpt; push_cast; ring
  have e2 : (1 : ℂ) - (1 / 2 - (y : ℂ) * I) = 1 / 2 + (y : ℂ) * I := by ring
  rw [e1, e2] at hl
  rw [hl, ← mul_assoc, inv_mul_cancel₀ hκ0, one_mul]

end

end AbelianTwist

end RHTower
