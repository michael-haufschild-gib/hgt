import GaloisForLFunctions.RHTower.WeilAlmostPeriodicLockRigidity

/-!
# The positivity law for lock phases

Let `G` be a Herglotz producer for the weights `lam` with lower-line lock

`G(1 − s) = κ₀ e^{iθ(x)} G(s)`,  `s = ½ − 2ix`, `x > 0`,

for a continuous real phase `θ`.

**Positivity law** (`local_phase_monotone`, `deriv_lock_phase_nonneg`).  `θ` is nondecreasing
near every `x₀ > 0` with `G(½ − 2ix₀) ≠ 0`.  If `θ` is `C¹`, then `θ' ≥ 0` on `(0, ∞)`.

**Theorem** (`lock_phase_rigidity`).  A `C¹` lock phase with `θ(x) ≤ K x^α` for `x ≥ 1`, for
some `α < 1`, forces `lam(n) = Λ(n)` for `n ≥ 2` and RH.  Monotonicity is not assumed; the
positivity law supplies it.

**Proof.**
* Near a boundary non-zero, `G = G(2) e^{L}` with `L` continuous up to the line, and the real
  structure `G(s̄) = conj G(s)` turns the lock into `e^{i(−2 Im L − θ)} = κ₀`.  A continuous
  integer-valued function on an interval is constant, so `θ = −2 Im L + const` there.  The boundary
  phase `−2 Im L(½ − 2ix)` is nondecreasing because `Re Φ ≥ 0` (`boundary_phase_antitone`).
* The real structure gives non-zeros at `±B` for arbitrarily large `B`.  Between them the zeros on
  the line are Lebesgue-null (`ae_ne_zero_of_ends`), so non-zeros are dense.  `θ' ≥ 0` holds there,
  and by continuity everywhere.
* Then `θ` is monotone of power growth `α < 1`, and the monotone twist theorem
  (`abelian_twist_power_rigidity`) applies.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ComplexConjugate

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity

noncomputable section

/-- **A continuous integer-valued function on an interval is constant.** -/
theorem int_valued_const {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hk : ∀ x ∈ Icc a b, ∃ n : ℤ, f x = n) : f b = f a := by
  have h1 := int_valued_add_antitone (g := fun _ => 0) hab hf (fun _ _ _ _ _ => le_rfl)
    (fun x hx => by simpa using hk x hx)
  have h2 := int_valued_add_antitone (f := fun x => -f x) (g := fun _ => 0) hab hf.neg
    (fun _ _ _ _ _ => le_rfl) (fun x hx => by
      obtain ⟨n, hn⟩ := hk x hx
      exact ⟨-n, by simp [hn]⟩)
  simp only [add_zero] at h1 h2
  linarith

theorem vpt_neg_eq_conj (x : ℝ) : vpt (1 / 2) (-x) = conj (vpt (1 / 2) x) := by
  apply Complex.ext <;> simp [vpt]

/-- **The positivity law, local form.**  Near a boundary non-zero the lock phase is nondecreasing. -/
theorem local_phase_monotone {lam : ℕ → ℝ} {Φ G P : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    (hG20 : G 2 ≠ 0)
    (hP : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt P (Φ s) s)
    (hPG : ∀ s : ℂ, 1 / 2 < s.re → G s = G 2 * cexp (P s))
    {θ : ℝ → ℝ} (hθ : Continuous θ) {κ₀ : ℂ}
    (hlock : ∀ x : ℝ, 0 < x → G (1 - vpt (1 / 2) x) = κ₀ * cexp ((θ x : ℂ) * I) * G (vpt (1 / 2) x))
    {x₀ : ℝ} (hx₀ : 0 < x₀) (hG0 : G (vpt (1 / 2) x₀) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x x' : ℝ, x₀ - δ < x → x ≤ x' → x' < x₀ + δ → θ x ≤ θ x' := by
  have hpi := Real.pi_pos
  obtain ⟨r, hr0, L, hLc, hGL, hLP⟩ :=
    exists_local_log hGc hGd hP hPG (b := vpt (1 / 2) x₀) (by simp) hG0
  set δ : ℝ := min (r / 4) (x₀ / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  have hinball : ∀ x, x₀ - δ < x → x < x₀ + δ → vpt (1 / 2) x ∈ Metric.ball (vpt (1 / 2) x₀) r := by
    intro x h1 h2
    rw [Metric.mem_ball, dist_vpt]
    have : |x - x₀| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
    have : δ ≤ r / 4 := min_le_left _ _
    linarith
  have hpos : ∀ x, x₀ - δ < x → 0 < x := by
    intro x h1
    have : δ ≤ x₀ / 2 := min_le_right _ _
    linarith
  have hphase : ∀ x, x₀ - δ < x → x < x₀ + δ →
      cexp ((((-2 * (L (vpt (1 / 2) x)).im - θ x) : ℝ) : ℂ) * I) = κ₀ := by
    intro x h1 h2
    have hb := hinball x h1 h2
    have hre : (1 / 2 : ℝ) ≤ (vpt (1 / 2) x).re := by simp
    have hG := hGL _ hb hre
    have hconj : 1 - vpt (1 / 2) x = conj (vpt (1 / 2) x) := by
      rw [← lineS_neg_eq_vpt, one_sub_lineS_eq_conj]
    have hl := hlock x (hpos x h1)
    rw [hconj, G_conj hsl hid hGc hGd hG2 hre, hG, map_mul, ← Complex.exp_conj, hG2,
      bigG_two_conj, ← hG2] at hl
    have hcancel : cexp (conj (L (vpt (1 / 2) x))) =
        κ₀ * cexp ((θ x : ℂ) * I) * cexp (L (vpt (1 / 2) x)) := by
      apply mul_left_cancel₀ hG20
      linear_combination hl
    have e1 : conj (L (vpt (1 / 2) x)) = L (vpt (1 / 2) x) +
        (((-2 * (L (vpt (1 / 2) x)).im : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp; ring
    rw [e1, Complex.exp_add] at hcancel
    have hne : cexp (L (vpt (1 / 2) x)) ≠ 0 := Complex.exp_ne_zero _
    have h3 : cexp ((((-2 * (L (vpt (1 / 2) x)).im : ℝ) : ℂ) * I)) = κ₀ * cexp ((θ x : ℂ) * I) := by
      apply mul_left_cancel₀ hne; linear_combination hcancel
    have e2 : ((((-2 * (L (vpt (1 / 2) x)).im - θ x) : ℝ) : ℂ) * I) =
        (((-2 * (L (vpt (1 / 2) x)).im : ℝ) : ℂ) * I) - ((θ x : ℂ) * I) := by push_cast; ring
    rw [e2, Complex.exp_sub, h3]
    field_simp
  set c₀ : ℝ := -2 * (L (vpt (1 / 2) x₀)).im - θ x₀ with hc₀
  have hκ := hphase x₀ (by linarith) (by linarith)
  have hκne : κ₀ ≠ 0 := by rw [← hκ]; exact Complex.exp_ne_zero _
  set f : ℝ → ℝ := fun x => (-2 * (L (vpt (1 / 2) x)).im - θ x - c₀) / (2 * Real.pi) with hf
  have hint : ∀ x, x₀ - δ < x → x < x₀ + δ → ∃ n : ℤ, f x = n := by
    intro x h1 h2
    have h := hphase x h1 h2
    have h' : cexp (((((-2 * (L (vpt (1 / 2) x)).im - θ x) - c₀) : ℝ) : ℂ) * I) = 1 := by
      rw [show (((((-2 * (L (vpt (1 / 2) x)).im - θ x) - c₀) : ℝ) : ℂ) * I) =
          ((((-2 * (L (vpt (1 / 2) x)).im - θ x)) : ℝ) : ℂ) * I - ((c₀ : ℝ) : ℂ) * I by
        push_cast; ring, Complex.exp_sub, h, hκ, div_self hκne]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h'
    refine ⟨n, ?_⟩
    have hn' := congrArg Complex.im hn
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_add, Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat,
      Complex.im_ofNat] at hn'
    have e2 : (2 * (Real.pi : ℂ)).re = 2 * Real.pi := by simp
    rw [e2] at hn'
    simp only [hf]
    field_simp
    linarith
  have hfc : ∀ a b, x₀ - δ < a → b < x₀ + δ → ContinuousOn f (Icc a b) := by
    intro a b ha hb x hx
    have hx1 : x₀ - δ < x := lt_of_lt_of_le ha hx.1
    have hx2 : x < x₀ + δ := lt_of_le_of_lt hx.2 hb
    have hmem : vpt (1 / 2) x ∈ Metric.ball (vpt (1 / 2) x₀) r ∩ {s : ℂ | 1 / 2 ≤ s.re} :=
      ⟨hinball x hx1 hx2, by simp⟩
    have hv : ContinuousWithinAt (fun y : ℝ => vpt (1 / 2) y) (Icc a b) x := by
      unfold vpt; fun_prop
    have hmaps : MapsTo (fun y : ℝ => vpt (1 / 2) y) (Icc a b)
        (Metric.ball (vpt (1 / 2) x₀) r ∩ {s : ℂ | 1 / 2 ≤ s.re}) := fun y hy =>
      ⟨hinball y (lt_of_lt_of_le ha hy.1) (lt_of_le_of_lt hy.2 hb), by simp⟩
    have hL' := (hLc _ hmem).comp hv hmaps
    exact ((((Complex.continuous_im.continuousWithinAt.comp hL' (mapsTo_univ _ _)).const_mul
      (-2)).sub hθ.continuousWithinAt).sub continuousWithinAt_const).div_const _
  refine ⟨δ, hδ0, fun x x' h1 hxx h2 => ?_⟩
  have hconst := int_valued_const hxx (hfc x x' h1 h2)
    (fun y hy => hint y (by linarith [hy.1]) (by linarith [hy.2]))
  have hph := boundary_phase_antitone hP hΦre hLc hLP hxx (hinball x h1 (by linarith))
    (hinball x' (by linarith) h2)
  simp only [hf] at hconst
  rw [div_left_inj' (by positivity)] at hconst
  linarith

/-- Non-zeros of a producer are dense on the lower critical line. -/
theorem exists_ne_zero_mem_Ioo {lam : ℕ → ℝ} {Φ G P : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    (hG20 : G 2 ≠ 0)
    (hP : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt P (Φ s) s)
    (hPG : ∀ s : ℂ, 1 / 2 < s.re → G s = G 2 * cexp (P s))
    {a b : ℝ} (hab : a < b) : ∃ y : ℝ, a < y ∧ y < b ∧ G (vpt (1 / 2) y) ≠ 0 := by
  obtain ⟨B, hBb, hB0, hGB⟩ := exists_ne_zero_beyond hsl hΦd hΦre hid hGc hGd hG2 (max b (-a))
  have hGB' : G (vpt (1 / 2) (-B)) ≠ 0 := by
    rw [vpt_neg_eq_conj, G_conj hsl hid hGc hGd hG2 (by simp)]
    exact (map_ne_zero _).mpr hGB
  have hae := ae_ne_zero_of_ends hΦd hΦre hGc hGd hG20 hP hPG (by linarith) hGB' hGB
  rw [ae_restrict_iff' measurableSet_Ioo] at hae
  have hnull : volume {x : ℝ | x ∈ Ioo (-B) B → G (vpt (1 / 2) x) ≠ 0}ᶜ = 0 := by
    rw [← ae_iff.mp hae]; rfl
  obtain ⟨y, hy, hay, hyb⟩ : ∃ y ∈ {x : ℝ | x ∈ Ioo (-B) B → G (vpt (1 / 2) x) ≠ 0}, a < y ∧ y < b := by
    by_contra h
    have hsub : Ioo a b ⊆ {x : ℝ | x ∈ Ioo (-B) B → G (vpt (1 / 2) x) ≠ 0}ᶜ :=
      fun y hy hyY => h ⟨y, hyY, hy.1, hy.2⟩
    have h0 := measure_mono_null hsub hnull
    rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
    linarith
  have hB1 := le_max_left b (-a)
  have hB2 := le_max_right b (-a)
  exact ⟨y, hay, hyb, hy ⟨by linarith, by linarith⟩⟩

/-- **The positivity law.**  A `C¹` lock phase has `θ' ≥ 0` on `(0, ∞)`. -/
theorem deriv_lock_phase_nonneg {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {θ : ℝ → ℝ} (hθd : Differentiable ℝ θ) (hθc : Continuous (deriv θ)) {κ₀ : ℂ}
    (hlock : ∀ x : ℝ, 0 < x → G (1 - vpt (1 / 2) x) = κ₀ * cexp ((θ x : ℂ) * I) * G (vpt (1 / 2) x))
    {x : ℝ} (hx : 0 < x) : 0 ≤ deriv θ x := by
  have hG20 : G 2 ≠ 0 := G_ne_zero hΦd hGd hG2 (by norm_num : (1 / 2 : ℝ) < (2 : ℂ).re)
  obtain ⟨P, hP, hPG⟩ := exists_log_producer hΦd hGd
  by_contra hneg
  push Not at hneg
  obtain ⟨r, hr0, hr⟩ := Metric.continuousAt_iff.mp hθc.continuousAt (-deriv θ x) (by linarith)
  set r' : ℝ := min r (x / 2) with hr'
  have hr'0 : 0 < r' := lt_min hr0 (by linarith)
  obtain ⟨y, hy1, hy2, hGy⟩ := exists_ne_zero_mem_Ioo hsl hΦd hΦre hid hGc hGd hG2 hG20 hP hPG
    (show x - r' < x + r' by linarith)
  have hy0 : 0 < y := by have := min_le_right r (x / 2); linarith
  have hdy : deriv θ y < 0 := by
    have hd : dist y x < r := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [min_le_left r (x / 2)]
    have := hr hd
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.2]
  obtain ⟨δ, hδ0, hmono⟩ := local_phase_monotone hsl hΦre hid hGc hGd hG2 hG20 hP hPG
    hθd.continuous hlock hy0 hGy
  have hslope : Tendsto (slope θ y) (𝓝[>] y) (𝓝 (deriv θ y)) :=
    (hasDerivAt_iff_tendsto_slope.mp (hθd y).hasDerivAt).mono_left
      (nhdsWithin_mono _ fun z (hz : y < z) => ne_of_gt hz)
  have hge : 0 ≤ deriv θ y := by
    refine ge_of_tendsto hslope ?_
    filter_upwards [Ioo_mem_nhdsGT (show y < y + δ by linarith)] with z hz
    rw [slope_def_field]
    apply div_nonneg _ (by linarith [hz.1])
    linarith [hmono y z (by linarith) hz.1.le hz.2]
  linarith

/-- **Lock-phase rigidity.**  Let `G` be a Herglotz producer for the weights `lam` with lower-line
lock `G(1 − s) = κ₀ e^{iθ(−τ)} G(s)`, `s = ½ + 2iτ`, `τ < 0`, where `θ` is `C¹` and
`θ(x) ≤ K x^α` for `x ≥ 1`, for some `α < 1`.  Then `θ` is nondecreasing on `[0, ∞)`,
`lam(n) = Λ(n)` for all `n ≥ 2`, and RH holds. -/
theorem lock_phase_rigidity {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {θ : ℝ → ℝ} (hθd : Differentiable ℝ θ) (hθc : Continuous (deriv θ))
    (hgrowth : ∃ α K : ℝ, α < 1 ∧ ∀ x : ℝ, 1 ≤ x → θ x ≤ K * x ^ α) {κ₀ : ℂ}
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = κ₀ * cexp ((θ (-τ) : ℂ) * I) * G (lineS τ)) :
    MonotoneOn θ (Ici 0) ∧ (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧
      RiemannHypothesis := by
  have hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
  have hlock' : ∀ x : ℝ, 0 < x → G (1 - vpt (1 / 2) x) =
      κ₀ * cexp ((θ x : ℂ) * I) * G (vpt (1 / 2) x) := by
    intro x hx
    have h := hlock (-x) (by linarith)
    rwa [neg_neg, lineS_neg_eq_vpt] at h
  have hmono : MonotoneOn θ (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hθd.continuous.continuousOn
      hθd.differentiableOn fun x hx => ?_
    rw [interior_Ici] at hx
    exact deriv_lock_phase_nonneg hsl hΦd hΦre hidT hGc hGd hG2 hθd hθc hlock' hx
  set C : ℝ → ℝ := fun x => θ (max x 0) with hC
  have hCm : Monotone C := fun a b hab =>
    hmono (show (0 : ℝ) ≤ max a 0 from le_max_right _ _) (show (0 : ℝ) ≤ max b 0 from le_max_right _ _)
      (max_le_max hab le_rfl)
  obtain ⟨α, K, hα1, hθK⟩ := hgrowth
  have hCg : ∃ α K : ℝ, α < 1 ∧ ∀ x : ℝ, 1 ≤ x → C x ≤ K * x ^ α :=
    ⟨α, K, hα1, fun x hx => by
      simp only [hC, max_eq_left (show (0 : ℝ) ≤ x by linarith)]; exact hθK x hx⟩
  refine ⟨hmono, abelian_twist_power_rigidity hsl hΦd hΦre hid hGc hGd hG2 hCm hCg
    (κ₀ := κ₀) (β₀ := 1) fun τ hτ => ?_⟩
  rw [hlock τ hτ]
  simp only [hC, one_mul, max_eq_left (show (0 : ℝ) ≤ -τ by linarith)]

end

end AbelianTwist

end RHTower
