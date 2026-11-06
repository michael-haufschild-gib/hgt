import GaloisForLFunctions.RHTower.ZetaInverseWideHorizontal
import GaloisForLFunctions.RHTower.ZetaOneLineUniformLower
import GaloisForLFunctions.RHTower.WindingXiCircle
import GaloisForLFunctions.HTGeometry.RectangleResidueTheorem
import GaloisForLFunctions.HTGeometry.GammaStripSharpDecay
import GaloisForLFunctions.PNTPlus.ZetaConj

/-!
# The contour of the inverse of Xi

Let `P` be analytic on the strip `-A ≤ Re u ≤ 0`, `A ≥ 1`, with Gaussian decay in `Im u`. This module
shifts the line integral of `Q(u) = P(u)/ξ(1 + 2u)` from `Re u = 0` to `Re u = -A`.

`(2π)⁻¹ (∫_{Re u = 0} Q - ∫_{Re u = -A} Q) = lim_k ∑_{|Im u| ≤ T_k/2} Res_u Q`,

where the sum runs over the zeros of `ξ(1 + 2u)` at the good heights `T_k` of
`exists_seq_zeta_inv_horizontal`. Multiplicities are unrestricted because the residue is the order-one
Laurent coefficient. At a simple zero that coefficient is `P(p)/D'(p)` with `D(u) = ξ(1 + 2u)`.

The inputs are `1/ξ = (2/(s(s-1))) Γ_ℝ(s)⁻¹ ζ(s)⁻¹`, the sharp bound for `1/Γ` on strips, and the bound
for `1/ζ` on the good heights, on the line `Re s = 1` and left of the strip. All of these are polynomial
times `e^{π|Im s|/4}`, which the Gaussian beats.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower HTGeometry

/-! ### Elementary comparisons -/

/-- A polynomial times an exponential is dominated by any Gaussian. -/
theorem exists_one_add_pow_mul_exp_le_gaussian (K : ℕ) {b c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x → (1 + x) ^ K * Real.exp (b * x) ≤ C * Real.exp (c * x ^ 2) := by
  refine ⟨(K.factorial : ℝ) * Real.exp (1 + (b + 1) ^ 2 / (4 * c)), by positivity, fun x hx => ?_⟩
  have h1 : (1 + x) ^ K ≤ (K.factorial : ℝ) * Real.exp (1 + x) := by
    have h := Real.pow_div_factorial_le_exp (1 + x) (by linarith) K
    have hfac : (0 : ℝ) < K.factorial := by positivity
    rw [div_le_iff₀ hfac] at h
    linarith [mul_comm (Real.exp (1 + x)) (K.factorial : ℝ)]
  have hquad : 1 + x + b * x ≤ 1 + (b + 1) ^ 2 / (4 * c) + c * x ^ 2 := by
    have hsq : 0 ≤ (2 * c * x - (b + 1)) ^ 2 / (4 * c) := by positivity
    have hexp : (2 * c * x - (b + 1)) ^ 2 / (4 * c) =
        c * x ^ 2 - (b + 1) * x + (b + 1) ^ 2 / (4 * c) := by
      field_simp
      ring
    rw [hexp] at hsq
    linarith
  calc (1 + x) ^ K * Real.exp (b * x)
      ≤ ((K.factorial : ℝ) * Real.exp (1 + x)) * Real.exp (b * x) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = (K.factorial : ℝ) * Real.exp (1 + x + b * x) := by
        rw [mul_assoc, ← Real.exp_add]
    _ ≤ (K.factorial : ℝ) * Real.exp (1 + (b + 1) ^ 2 / (4 * c) + c * x ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hquad) (by positivity)
    _ = (K.factorial : ℝ) * Real.exp (1 + (b + 1) ^ 2 / (4 * c)) * Real.exp (c * x ^ 2) := by
        rw [Real.exp_add (1 + (b + 1) ^ 2 / (4 * c))]
        ring

/-- A continuous function with a Gaussian tail is integrable. -/
theorem integrable_of_continuous_of_gaussian_tail {f : ℝ → ℂ} (hf : Continuous f) {R C c : ℝ}
    (hc : 0 < c) (h : ∀ x : ℝ, R ≤ |x| → ‖f x‖ ≤ C * Real.exp (-c * x ^ 2)) : Integrable f := by
  set R' := max R 0 with hR'
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -R') (b := R')).exists_bound_of_continuousOn hf.continuousOn
  have hg : Integrable fun x : ℝ =>
      (max M 0 * Real.exp (c * R' ^ 2) + max C 0) * Real.exp (-c * x ^ 2) :=
    (integrable_exp_neg_mul_sq hc).const_mul _
  refine hg.mono' hf.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have hE : 0 < Real.exp (-c * x ^ 2) := Real.exp_pos _
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hER : 0 < Real.exp (c * R' ^ 2) := Real.exp_pos _
  rcases le_or_gt |x| R' with hx | hx
  · have hmem : x ∈ Icc (-R') R' := abs_le.mp hx
    have h1 : ‖f x‖ ≤ max M 0 := (hM x hmem).trans (le_max_left _ _)
    have hsq : x ^ 2 ≤ R' ^ 2 := by
      have := sq_le_sq' (abs_le.mp hx).1 (abs_le.mp hx).2
      exact this
    have h2 : 1 ≤ Real.exp (c * R' ^ 2) * Real.exp (-c * x ^ 2) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      nlinarith
    calc ‖f x‖ ≤ max M 0 * 1 := by rwa [mul_one]
      _ ≤ max M 0 * (Real.exp (c * R' ^ 2) * Real.exp (-c * x ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 hM0
      _ ≤ (max M 0 * Real.exp (c * R' ^ 2) + max C 0) * Real.exp (-c * x ^ 2) := by
          nlinarith [mul_nonneg hC0 hE.le]
  · have hRx : R ≤ |x| := (le_max_left _ _).trans hx.le
    calc ‖f x‖ ≤ C * Real.exp (-c * x ^ 2) := h x hRx
      _ ≤ max C 0 * Real.exp (-c * x ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hE.le
      _ ≤ (max M 0 * Real.exp (c * R' ^ 2) + max C 0) * Real.exp (-c * x ^ 2) := by
          nlinarith [mul_nonneg (mul_nonneg hM0 hER.le) hE.le]

/-! ### The inverse of Xi -/

/-- `ξ(s) = (s(s-1)/2) Γ_ℝ(s) ζ(s)` off the real axis. -/
theorem xi_eq_factor {s : ℂ} (him : s.im ≠ 0) :
    xi s = s * (s - 1) / 2 * (Complex.Gammaℝ s * riemannZeta s) := by
  have hs0 : s ≠ 0 := fun h => him (by rw [h]; simp)
  have hs1 : s ≠ 1 := fun h => him (by rw [h]; simp)
  have hG : Complex.Gammaℝ s ≠ 0 := by
    rw [Complex.Gammaℝ_def]
    refine mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast Real.pi_ne_zero))) ?_
    refine Complex.Gamma_ne_zero fun m hm => him ?_
    have := congrArg Complex.im hm
    simp at this
    linarith
  rw [xi_eq_half_mul hs0 hs1, riemannZeta_def_of_ne_zero hs0]
  field_simp

/-- **The inverse of Xi in a strip.**  `1/ξ` is bounded by a polynomial times `e^{π|Im s|/4}` times
`1/ζ`. -/
theorem exists_norm_inv_xi_le (α β : ℝ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ s : ℂ, α ≤ s.re → s.re ≤ β → 2 ≤ |s.im| →
      ‖(xi s)⁻¹‖ ≤ C * (1 + |s.im|) ^ N * Real.exp (Real.pi * |s.im| / 4) * ‖(riemannZeta s)⁻¹‖ := by
  obtain ⟨C₀, N, hC₀, hΓ⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_norm_inv_Gamma_strip (α / 2) (β / 2)
  refine ⟨2 * Real.pi ^ (β / 2) * C₀, N, by positivity, fun s h1 h2 h3 => ?_⟩
  have him : s.im ≠ 0 := fun h => by
    rw [h] at h3
    norm_num at h3
  have hre : (s / 2).re = s.re / 2 := by simp
  have him2 : (s / 2).im = s.im / 2 := by simp
  have habs : |(s / 2).im| = |s.im| / 2 := by
    rw [him2, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hΓs := hΓ (s / 2) (by rw [hre]; linarith) (by rw [hre]; linarith) (by rw [habs]; linarith)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- the kinematic factor
  have hkin : ‖(s * (s - 1) / 2)⁻¹‖ ≤ 2 := by
    have h1' : 1 ≤ ‖s‖ := by
      have := Complex.abs_im_le_norm s
      linarith
    have h2' : 1 ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1)
      simp only [Complex.sub_im, Complex.one_im, sub_zero] at this
      linarith
    rw [norm_inv, norm_div, norm_mul]
    have hprod : 1 ≤ ‖s‖ * ‖s - 1‖ := by nlinarith
    simp only [Complex.norm_ofNat]
    rw [inv_div]
    calc 2 / (‖s‖ * ‖s - 1‖) ≤ 2 / 1 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hprod
      _ = 2 := by norm_num
  -- the archimedean factor
  have hpow : ‖((Real.pi : ℂ) ^ (-s / 2))⁻¹‖ ≤ Real.pi ^ (β / 2) := by
    rw [norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos hpi]
    have hreS : (-s / 2).re = -(s.re / 2) := by simp; ring
    rw [hreS, Real.rpow_neg hpi.le, inv_inv]
    exact Real.rpow_le_rpow_of_exponent_le
      (by linarith [Real.pi_gt_three]) (by linarith)
  have hgamma : ‖(Complex.Gammaℝ s)⁻¹‖ ≤
      Real.pi ^ (β / 2) * (C₀ * (1 + |s.im|) ^ N * Real.exp (Real.pi * |s.im| / 4)) := by
    rw [Complex.Gammaℝ_def, mul_inv, norm_mul]
    refine mul_le_mul hpow ?_ (norm_nonneg _) (by positivity)
    refine hΓs.trans ?_
    have hexpEq : Real.pi * |(s / 2).im| / 2 = Real.pi * |s.im| / 4 := by
      rw [habs]
      ring
    rw [hexpEq]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    refine mul_le_mul_of_nonneg_left ?_ hC₀
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ N
    rw [habs]
    linarith [abs_nonneg s.im]
  rw [xi_eq_factor him, mul_inv, mul_inv, norm_mul, norm_mul]
  have hz := norm_nonneg (riemannZeta s)⁻¹
  have hG := norm_nonneg (Complex.Gammaℝ s)⁻¹
  calc ‖(s * (s - 1) / 2)⁻¹‖ * (‖(Complex.Gammaℝ s)⁻¹‖ * ‖(riemannZeta s)⁻¹‖)
      ≤ 2 * ((Real.pi ^ (β / 2) * (C₀ * (1 + |s.im|) ^ N * Real.exp (Real.pi * |s.im| / 4))) *
          ‖(riemannZeta s)⁻¹‖) := by
        refine mul_le_mul hkin ?_ (by positivity) (by norm_num)
        exact mul_le_mul_of_nonneg_right hgamma hz
    _ = 2 * Real.pi ^ (β / 2) * C₀ * (1 + |s.im|) ^ N * Real.exp (Real.pi * |s.im| / 4) *
          ‖(riemannZeta s)⁻¹‖ := by ring

/-- **The inverse of zeta on the line `Re s = 1`** grows at most polynomially. -/
theorem exists_norm_inv_zeta_one_line :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, t ≠ 0 →
      ‖(riemannZeta (1 + (t : ℂ) * I))⁻¹‖ ≤ K * (1 + |t|) ^ 11 := by
  obtain ⟨K, hK, hb⟩ := exists_uniform_upper_bound_inv_riemannZeta
  refine ⟨K * Real.exp 1 ^ 11, by positivity, fun t ht => ?_⟩
  have hne : (1 : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact ht this
  have hzne : riemannZeta (1 + (t : ℂ) * I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp)
  have hcont : ContinuousAt (fun σ : ℝ => ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * I))⁻¹‖) 1 := by
    have hinner : ContinuousAt (fun σ : ℝ => (σ : ℂ) + (t : ℂ) * I) 1 := by fun_prop
    have hz : ContinuousAt (fun σ : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * I)) 1 := by
      refine ContinuousAt.comp (f := fun σ : ℝ => (σ : ℂ) + (t : ℂ) * I) (g := riemannZeta) ?_ hinner
      have : ((1 : ℝ) : ℂ) + (t : ℂ) * I ≠ 1 := by simpa using hne
      exact (differentiableAt_riemannZeta this).continuousAt
    refine (hz.inv₀ ?_).norm
    simpa using hzne
  have hlim : Tendsto (fun σ : ℝ => ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * I))⁻¹‖) (𝓝[>] 1)
      (𝓝 ‖(riemannZeta (((1 : ℝ) : ℂ) + (t : ℂ) * I))⁻¹‖) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ σ : ℝ in 𝓝[>] 1, ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤
      K * (Real.log (|t| + Real.exp 1)) ^ 11 := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (1 : ℝ) < 5 / 4)] with σ hσ
    exact hb σ t hσ.1 hσ.2.le
  have hle := le_of_tendsto hlim hev
  have hval : ((1 : ℝ) : ℂ) + (t : ℂ) * I = 1 + (t : ℂ) * I := by simp
  rw [hval] at hle
  refine hle.trans ?_
  have hE : 1 ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hpos : 0 < |t| + Real.exp 1 := by positivity
  have hlogNN : 0 ≤ Real.log (|t| + Real.exp 1) :=
    Real.log_nonneg (by linarith [abs_nonneg t])
  have hlogLe : Real.log (|t| + Real.exp 1) ≤ Real.exp 1 * (1 + |t|) := by
    have h1 := Real.log_le_self hpos.le
    nlinarith [abs_nonneg t]
  calc K * Real.log (|t| + Real.exp 1) ^ 11 ≤ K * (Real.exp 1 * (1 + |t|)) ^ 11 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogNN hlogLe 11) hK.le
    _ = K * Real.exp 1 ^ 11 * (1 + |t|) ^ 11 := by
        rw [mul_pow]
        ring

/-! ### Location of the zeros -/

theorem re_lt_one_of_xi_eq_zero {s : ℂ} (h : xi s = 0) : s.re < 1 := by
  by_contra hcon
  exact xi_ne_zero_of_one_le_re (not_lt.mp hcon) h

theorem re_pos_of_xi_eq_zero {s : ℂ} (h : xi s = 0) : 0 < s.re := by
  have h1 : xi (1 - s) = 0 := by rw [xi_one_sub, h]
  have := re_lt_one_of_xi_eq_zero h1
  simp at this
  linarith

/-- The zeros of `ξ(1 + 2u)` in a horizontal band. -/
def ringdownPoleSet (T : ℝ) : Set ℂ := {u : ℂ | xi (1 + 2 * u) = 0 ∧ |u.im| ≤ T / 2}

theorem re_of_mem_ringdownPoleSet {T : ℝ} {u : ℂ} (hu : u ∈ ringdownPoleSet T) :
    -(1 / 2) < u.re ∧ u.re < 0 := by
  have h1 := re_pos_of_xi_eq_zero hu.1
  have h2 := re_lt_one_of_xi_eq_zero hu.1
  have hre : (1 + 2 * u).re = 1 + 2 * u.re := by simp
  rw [hre] at h1 h2
  constructor <;> linarith

theorem finite_ringdownPoleSet (T : ℝ) : (ringdownPoleSet T).Finite := by
  have hfin := xi_zeros_closedBall_finite 0 (1 + |T|)
  have hinj : InjOn (fun u : ℂ => 1 + 2 * u) (ringdownPoleSet T) := by
    intro a _ b _ h
    have h' : (1 : ℂ) + 2 * a = 1 + 2 * b := h
    have := add_left_cancel h'
    exact mul_left_cancel₀ (by norm_num) this
  refine Set.Finite.of_finite_image (hfin.subset ?_) hinj
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨?_, hu.1⟩
  have hs1 := re_pos_of_xi_eq_zero hu.1
  have hs2 := re_lt_one_of_xi_eq_zero hu.1
  have him : |(1 + 2 * u).im| ≤ |T| := by
    have h3 : (1 + 2 * u).im = 2 * u.im := by simp
    rw [h3, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have := hu.2
    linarith [le_abs_self T]
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre : |(1 + 2 * u).re| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  linarith

/-- The finite set of poles of `Q` in the band `|Im u| ≤ T/2`. -/
def ringdownPoles (T : ℝ) : Finset ℂ := (finite_ringdownPoleSet T).toFinset

@[simp] theorem mem_ringdownPoles {T : ℝ} {u : ℂ} :
    u ∈ ringdownPoles T ↔ xi (1 + 2 * u) = 0 ∧ |u.im| ≤ T / 2 := by
  simp [ringdownPoles, ringdownPoleSet]

/-! ### The good heights -/

/-- The good heights of `exists_seq_zeta_inv_horizontal`. -/
def goodHeight : ℕ → ℝ := Classical.choose exists_seq_zeta_inv_horizontal

theorem tendsto_goodHeight : Tendsto goodHeight atTop atTop :=
  (Classical.choose_spec exists_seq_zeta_inv_horizontal).2.1

theorem one_le_goodHeight (k : ℕ) : 1 ≤ goodHeight k :=
  (Classical.choose_spec exists_seq_zeta_inv_horizontal).2.2.1 k

theorem riemannZeta_conj_ne_zero {s : ℂ} (h : riemannZeta s ≠ 0) :
    riemannZeta ((starRingEnd ℂ) s) ≠ 0 := by
  rw [riemannZeta_conj]
  exact (map_ne_zero _).mpr h

/-- The zeta function has no zero at height `±T_k` across `-1 ≤ Re s ≤ 2`. -/
theorem riemannZeta_ne_zero_of_abs_im_goodHeight (k : ℕ) {s : ℂ} (h1 : -1 ≤ s.re) (h2 : s.re ≤ 2)
    (him : |s.im| = goodHeight k) : riemannZeta s ≠ 0 := by
  have hspec := (Classical.choose_spec exists_seq_zeta_inv_horizontal).2.2.2.2.1 k s.re h1 h2
  change riemannZeta ((s.re : ℂ) + ((goodHeight k : ℝ) : ℂ) * I) ≠ 0 at hspec
  rcases (abs_eq (by linarith [one_le_goodHeight k] : 0 ≤ goodHeight k)).mp him with h | h
  · have hs : s = (s.re : ℂ) + ((goodHeight k : ℝ) : ℂ) * I := by
      rw [← h]
      exact (Complex.re_add_im s).symm
    rwa [hs]
  · have hs : s = (starRingEnd ℂ) ((s.re : ℂ) + ((goodHeight k : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp [h]
    rw [hs]
    exact riemannZeta_conj_ne_zero hspec

/-- `1/ζ` is polynomially bounded at heights `±T_k`. -/
theorem exists_norm_inv_zeta_goodHeight (b : ℝ) (hb : 2 ≤ b) :
    ∃ (C : ℝ) (N : ℕ) (k₀ : ℕ), 0 ≤ C ∧ ∀ k : ℕ, k₀ ≤ k → ∀ s : ℂ, -b ≤ s.re → s.re ≤ b →
      |s.im| = goodHeight k → ‖(riemannZeta s)⁻¹‖ ≤ C * (1 + |s.im|) ^ N := by
  obtain ⟨C, A, k₀, hC, hA, hbound⟩ :=
    (Classical.choose_spec exists_seq_zeta_inv_horizontal).2.2.2.2.2 b hb
  refine ⟨C, ⌈A⌉₊, k₀, hC.le, fun k hk s h1 h2 him => ?_⟩
  have hT := one_le_goodHeight k
  have hmain : ‖(riemannZeta ((s.re : ℂ) + ((goodHeight k : ℝ) : ℂ) * I))⁻¹‖ ≤
      C * goodHeight k ^ A := hbound k hk s.re h1 h2
  have hpow : goodHeight k ^ A ≤ (1 + |s.im|) ^ ⌈A⌉₊ := by
    rw [him]
    calc goodHeight k ^ A ≤ goodHeight k ^ (⌈A⌉₊ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hT (Nat.le_ceil A)
      _ = goodHeight k ^ ⌈A⌉₊ := Real.rpow_natCast _ _
      _ ≤ (1 + goodHeight k) ^ ⌈A⌉₊ :=
          pow_le_pow_left₀ (by linarith) (by linarith) _
  have hnorm : ‖(riemannZeta s)⁻¹‖ =
      ‖(riemannZeta ((s.re : ℂ) + ((goodHeight k : ℝ) : ℂ) * I))⁻¹‖ := by
    rcases (abs_eq (by linarith : 0 ≤ goodHeight k)).mp him with h | h
    · congr 3
      rw [← h]
      exact (Complex.re_add_im s).symm
    · have hs : s = (starRingEnd ℂ) ((s.re : ℂ) + ((goodHeight k : ℝ) : ℂ) * I) := by
        apply Complex.ext <;> simp [h]
      conv_lhs => rw [hs]
      rw [riemannZeta_conj, ← map_inv₀, RCLike.norm_conj]
  rw [hnorm]
  exact hmain.trans (mul_le_mul_of_nonneg_left hpow hC.le)

/-- `ξ` has no zero at height `±T_k`. -/
theorem xi_ne_zero_of_abs_im_goodHeight (k : ℕ) {s : ℂ} (him : |s.im| = goodHeight k) : xi s ≠ 0 := by
  intro h0
  have h1 := re_pos_of_xi_eq_zero h0
  have h2 := re_lt_one_of_xi_eq_zero h0
  have hne : s.im ≠ 0 := by
    intro h
    rw [h, abs_zero] at him
    linarith [one_le_goodHeight k]
  have hzeta := riemannZeta_ne_zero_of_abs_im_goodHeight k (by linarith) (by linarith) him
  have hfac := xi_eq_factor hne
  rw [h0] at hfac
  have hs0 : s ≠ 0 := fun h => hne (by rw [h]; simp)
  have hs1 : s ≠ 1 := fun h => hne (by rw [h]; simp)
  have hG : Complex.Gammaℝ s ≠ 0 := by
    rw [Complex.Gammaℝ_def]
    refine mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast Real.pi_ne_zero))) ?_
    refine Complex.Gamma_ne_zero fun m hm => hne ?_
    have := congrArg Complex.im hm
    simp at this
    linarith
  have hk : s * (s - 1) / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) two_ne_zero
  exact (mul_ne_zero hk (mul_ne_zero hG hzeta)) hfac.symm

/-! ### The contour theorem -/

/-- The quotient `P(u)/ξ(1 + 2u)`. -/
def inverseXiQuotient (P : ℂ → ℂ) (u : ℂ) : ℂ := P u / xi (1 + 2 * u)

/-- Decay of a numerator on the strip `-A ≤ Re u ≤ 0`. -/
structure GaussianNumerator (A : ℝ) (P : ℂ → ℂ) : Prop where
  analytic : ∀ u : ℂ, -A ≤ u.re → u.re ≤ 0 → AnalyticAt ℂ P u
  decay : ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ u : ℂ, -A ≤ u.re → u.re ≤ 0 →
    ‖P u‖ ≤ C * Real.exp (-c * u.im ^ 2)

theorem differentiable_xi_shift : Differentiable ℂ fun u : ℂ => xi (1 + 2 * u) :=
  xi_differentiable.comp (by fun_prop)

theorem analyticAt_inverseXiQuotient {A : ℝ} {P : ℂ → ℂ} (hP : GaussianNumerator A P) {u : ℂ}
    (h1 : -A ≤ u.re) (h2 : u.re ≤ 0) (h0 : xi (1 + 2 * u) ≠ 0) :
    AnalyticAt ℂ (inverseXiQuotient P) u :=
  (hP.analytic u h1 h2).div (differentiable_xi_shift.analyticAt u) h0

theorem meromorphicAt_inverseXiQuotient {A : ℝ} {P : ℂ → ℂ} (hP : GaussianNumerator A P) {u : ℂ}
    (h1 : -A ≤ u.re) (h2 : u.re ≤ 0) : MeromorphicAt (inverseXiQuotient P) u :=
  (hP.analytic u h1 h2).meromorphicAt.div (differentiable_xi_shift.analyticAt u).meromorphicAt

/-- **Decay on the horizontal edges.** -/
theorem exists_norm_inverseXiQuotient_edge_le {A : ℝ} (hA : 1 ≤ A) {P : ℂ → ℂ}
    (hP : GaussianNumerator A P) :
    ∃ (C c : ℝ) (k₀ : ℕ), 0 ≤ C ∧ 0 < c ∧ ∀ k : ℕ, k₀ ≤ k → 2 ≤ goodHeight k → ∀ u : ℂ,
      -A ≤ u.re → u.re ≤ 0 → |u.im| = goodHeight k / 2 →
      ‖inverseXiQuotient P u‖ ≤ C * Real.exp (-c * goodHeight k ^ 2) := by
  obtain ⟨C₁, c, hC₁, hc, hdec⟩ := hP.decay
  obtain ⟨C₂, N₂, hC₂, hxi⟩ := exists_norm_inv_xi_le (1 - 2 * A) 1
  obtain ⟨C₃, N₃, k₀, hC₃, hzeta⟩ := exists_norm_inv_zeta_goodHeight (2 * A + 1) (by linarith)
  obtain ⟨C₄, hC₄, hcmp⟩ := exists_one_add_pow_mul_exp_le_gaussian (N₂ + N₃)
    (b := Real.pi / 4) (c := c / 8) (by positivity)
  refine ⟨C₁ * (C₂ * C₃ * C₄), c / 8, k₀, by positivity, by positivity, fun k hk hT u h1 h2 him => ?_⟩
  set T := goodHeight k with hTdef
  have hT0 : 0 ≤ T := by linarith
  have hsim : (1 + 2 * u).im = 2 * u.im := by simp
  have hsre : (1 + 2 * u).re = 1 + 2 * u.re := by simp
  have habs : |(1 + 2 * u).im| = T := by
    rw [hsim, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), him]
    ring
  have hP1 := hdec u h1 h2
  have hX := hxi (1 + 2 * u) (by rw [hsre]; linarith) (by rw [hsre]; linarith) (by rw [habs]; exact hT)
  have hZ := hzeta k hk (1 + 2 * u) (by rw [hsre]; linarith) (by rw [hsre]; linarith) habs
  rw [habs] at hX hZ
  have hu2 : u.im ^ 2 = T ^ 2 / 4 := by
    rw [← sq_abs, him]
    ring
  have hcm := hcmp T hT0
  have hexpEq : Real.pi * T / 4 = Real.pi / 4 * T := by ring
  rw [hexpEq] at hX
  have hinv : ‖inverseXiQuotient P u‖ = ‖P u‖ * ‖(xi (1 + 2 * u))⁻¹‖ := by
    rw [inverseXiQuotient, div_eq_mul_inv, norm_mul]
  rw [hinv]
  have hinvBound : ‖(xi (1 + 2 * u))⁻¹‖ ≤ C₂ * C₃ * ((1 + T) ^ (N₂ + N₃) * Real.exp (Real.pi / 4 * T)) := by
    refine hX.trans ?_
    calc C₂ * (1 + T) ^ N₂ * Real.exp (Real.pi / 4 * T) * ‖(riemannZeta (1 + 2 * u))⁻¹‖
        ≤ C₂ * (1 + T) ^ N₂ * Real.exp (Real.pi / 4 * T) * (C₃ * (1 + T) ^ N₃) :=
          mul_le_mul_of_nonneg_left hZ (by positivity)
      _ = C₂ * C₃ * ((1 + T) ^ (N₂ + N₃) * Real.exp (Real.pi / 4 * T)) := by
          rw [pow_add]
          ring
  have hfinal : ‖(xi (1 + 2 * u))⁻¹‖ ≤ C₂ * C₃ * (C₄ * Real.exp (c / 8 * T ^ 2)) :=
    hinvBound.trans (mul_le_mul_of_nonneg_left hcm (by positivity))
  calc ‖P u‖ * ‖(xi (1 + 2 * u))⁻¹‖
      ≤ (C₁ * Real.exp (-c * u.im ^ 2)) * (C₂ * C₃ * (C₄ * Real.exp (c / 8 * T ^ 2))) :=
        mul_le_mul hP1 hfinal (norm_nonneg _) (by positivity)
    _ = C₁ * (C₂ * C₃ * C₄) * (Real.exp (-c * (T ^ 2 / 4)) * Real.exp (c / 8 * T ^ 2)) := by
        rw [hu2]
        ring
    _ = C₁ * (C₂ * C₃ * C₄) * Real.exp (-(c / 8) * T ^ 2) := by
        rw [← Real.exp_add]
        congr 2
        ring

/-- **Integrability on the right line `Re u = 0`.** -/
theorem integrable_inverseXiQuotient_right {A : ℝ} (hA : 1 ≤ A) {P : ℂ → ℂ}
    (hP : GaussianNumerator A P) :
    Integrable fun y : ℝ => inverseXiQuotient P ((y : ℂ) * I) := by
  obtain ⟨C₁, c, hC₁, hc, hdec⟩ := hP.decay
  obtain ⟨C₂, N₂, hC₂, hxi⟩ := exists_norm_inv_xi_le 1 1
  obtain ⟨K, hK, hzeta⟩ := exists_norm_inv_zeta_one_line
  obtain ⟨C₄, hC₄, hcmp⟩ := exists_one_add_pow_mul_exp_le_gaussian (N₂ + 11)
    (b := Real.pi / 4) (c := c / 8) (by positivity)
  have hline : ∀ y : ℝ, (1 + 2 * ((y : ℂ) * I)) = 1 + ((2 * y : ℝ) : ℂ) * I := by
    intro y
    push_cast
    ring
  have hre : ∀ y : ℝ, (1 + 2 * ((y : ℂ) * I)).re = 1 := fun y => by simp
  have him : ∀ y : ℝ, (1 + 2 * ((y : ℂ) * I)).im = 2 * y := fun y => by simp
  have hcont : Continuous fun y : ℝ => inverseXiQuotient P ((y : ℂ) * I) := by
    refine continuous_iff_continuousAt.mpr fun y => ?_
    have hne : xi (1 + 2 * ((y : ℂ) * I)) ≠ 0 :=
      xi_ne_zero_of_one_le_re (by rw [hre])
    have hu : ((y : ℂ) * I).re = 0 := by simp
    have han := analyticAt_inverseXiQuotient hP (u := (y : ℂ) * I)
      (by rw [hu]; linarith) (by rw [hu]) hne
    exact ContinuousAt.comp (f := fun y : ℝ => (y : ℂ) * I) han.continuousAt (by fun_prop)
  refine integrable_of_continuous_of_gaussian_tail hcont (R := 1)
    (C := C₁ * (C₂ * (K * C₄))) (c := c / 2) (by positivity) fun y hy => ?_
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, abs_zero] at hy
    linarith
  have hu : ((y : ℂ) * I).re = 0 := by simp
  have huim : ((y : ℂ) * I).im = y := by simp
  have hP1 := hdec ((y : ℂ) * I) (by rw [hu]; linarith) (by rw [hu])
  rw [huim] at hP1
  have habs : |(1 + 2 * ((y : ℂ) * I)).im| = 2 * |y| := by
    rw [him, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hX := hxi (1 + 2 * ((y : ℂ) * I)) (by rw [hre]) (by rw [hre]) (by rw [habs]; linarith)
  rw [habs] at hX
  have hZ := hzeta (2 * y) (by simpa using hy0)
  rw [← hline y] at hZ
  have habs2 : |2 * y| = 2 * |y| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [habs2] at hZ
  set x := 2 * |y| with hx
  have hx0 : 0 ≤ x := by positivity
  have hcm := hcmp x hx0
  have hexpEq : Real.pi * x / 4 = Real.pi / 4 * x := by ring
  rw [hexpEq] at hX
  have hinv : ‖inverseXiQuotient P ((y : ℂ) * I)‖ =
      ‖P ((y : ℂ) * I)‖ * ‖(xi (1 + 2 * ((y : ℂ) * I)))⁻¹‖ := by
    rw [inverseXiQuotient, div_eq_mul_inv, norm_mul]
  rw [hinv]
  have hinvBound : ‖(xi (1 + 2 * ((y : ℂ) * I)))⁻¹‖ ≤
      C₂ * K * ((1 + x) ^ (N₂ + 11) * Real.exp (Real.pi / 4 * x)) := by
    refine hX.trans ?_
    calc C₂ * (1 + x) ^ N₂ * Real.exp (Real.pi / 4 * x) * ‖(riemannZeta (1 + 2 * ((y : ℂ) * I)))⁻¹‖
        ≤ C₂ * (1 + x) ^ N₂ * Real.exp (Real.pi / 4 * x) * (K * (1 + x) ^ 11) :=
          mul_le_mul_of_nonneg_left hZ (by positivity)
      _ = C₂ * K * ((1 + x) ^ (N₂ + 11) * Real.exp (Real.pi / 4 * x)) := by
          rw [pow_add]
          ring
  have hfinal : ‖(xi (1 + 2 * ((y : ℂ) * I)))⁻¹‖ ≤ C₂ * K * (C₄ * Real.exp (c / 8 * x ^ 2)) :=
    hinvBound.trans (mul_le_mul_of_nonneg_left hcm (by positivity))
  have hxsq : x ^ 2 = 4 * y ^ 2 := by
    rw [hx, mul_pow, sq_abs]
    ring
  calc ‖P ((y : ℂ) * I)‖ * ‖(xi (1 + 2 * ((y : ℂ) * I)))⁻¹‖
      ≤ (C₁ * Real.exp (-c * y ^ 2)) * (C₂ * K * (C₄ * Real.exp (c / 8 * x ^ 2))) :=
        mul_le_mul hP1 hfinal (norm_nonneg _) (by positivity)
    _ = C₁ * (C₂ * (K * C₄)) * (Real.exp (-c * y ^ 2) * Real.exp (c / 8 * x ^ 2)) := by ring
    _ = C₁ * (C₂ * (K * C₄)) * Real.exp (-(c / 2) * y ^ 2) := by
        rw [← Real.exp_add, hxsq]
        congr 2
        ring

/-- **Integrability on the left line `Re u = -A`.** -/
theorem integrable_inverseXiQuotient_left {A : ℝ} (hA : 1 ≤ A) {P : ℂ → ℂ}
    (hP : GaussianNumerator A P) :
    Integrable fun y : ℝ => inverseXiQuotient P (((-A : ℝ) : ℂ) + (y : ℂ) * I) := by
  obtain ⟨C₁, c, hC₁, hc, hdec⟩ := hP.decay
  obtain ⟨C₂, N₂, hC₂, hxi⟩ := exists_norm_inv_xi_le (1 - 2 * A) (1 - 2 * A)
  obtain ⟨C₃, T₀, N₃, hC₃, hzeta⟩ := exists_norm_zeta_inv_left_bound (2 * A)
  obtain ⟨C₄, hC₄, hcmp⟩ := exists_one_add_pow_mul_exp_le_gaussian (N₂ + N₃)
    (b := Real.pi / 4) (c := c / 8) (by positivity)
  have hu : ∀ y : ℝ, (((-A : ℝ) : ℂ) + (y : ℂ) * I).re = -A := fun y => by simp
  have huim : ∀ y : ℝ, (((-A : ℝ) : ℂ) + (y : ℂ) * I).im = y := fun y => by simp
  have hre : ∀ y : ℝ, (1 + 2 * (((-A : ℝ) : ℂ) + (y : ℂ) * I)).re = 1 - 2 * A := fun y => by
    simp
    ring
  have him : ∀ y : ℝ, (1 + 2 * (((-A : ℝ) : ℂ) + (y : ℂ) * I)).im = 2 * y := fun y => by simp
  have hcont : Continuous fun y : ℝ => inverseXiQuotient P (((-A : ℝ) : ℂ) + (y : ℂ) * I) := by
    refine continuous_iff_continuousAt.mpr fun y => ?_
    have hne : xi (1 + 2 * (((-A : ℝ) : ℂ) + (y : ℂ) * I)) ≠ 0 := fun h0 => by
      have := re_pos_of_xi_eq_zero h0
      rw [hre] at this
      linarith
    have han := analyticAt_inverseXiQuotient hP (u := ((-A : ℝ) : ℂ) + (y : ℂ) * I)
      (by rw [hu]) (by rw [hu]; linarith) hne
    exact ContinuousAt.comp (f := fun y : ℝ => ((-A : ℝ) : ℂ) + (y : ℂ) * I)
      han.continuousAt (by fun_prop)
  refine integrable_of_continuous_of_gaussian_tail hcont (R := max 1 (T₀ / 2))
    (C := C₁ * (C₂ * C₃ * C₄)) (c := c / 2) (by positivity) fun y hy => ?_
  have hy1 : 1 ≤ |y| := (le_max_left _ _).trans hy
  have hyT : T₀ ≤ 2 * |y| := by
    have := (le_max_right 1 (T₀ / 2)).trans hy
    linarith
  have hP1 := hdec (((-A : ℝ) : ℂ) + (y : ℂ) * I) (by rw [hu]) (by rw [hu]; linarith)
  rw [huim] at hP1
  have habs : |(1 + 2 * (((-A : ℝ) : ℂ) + (y : ℂ) * I)).im| = 2 * |y| := by
    rw [him, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hX := hxi (1 + 2 * (((-A : ℝ) : ℂ) + (y : ℂ) * I)) (by rw [hre]) (by rw [hre])
    (by rw [habs]; linarith)
  rw [habs] at hX
  have hline : (1 + 2 * (((-A : ℝ) : ℂ) + (y : ℂ) * I)) =
      ((1 - 2 * A : ℝ) : ℂ) + ((2 * y : ℝ) : ℂ) * I := by
    push_cast
    ring
  have habs2 : |2 * y| = 2 * |y| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hZ := hzeta (1 - 2 * A) (2 * y) (by linarith) (by linarith) (by rw [habs2]; exact hyT)
  rw [← hline, habs2] at hZ
  set x := 2 * |y| with hx
  have hx0 : 0 ≤ x := by positivity
  have hcm := hcmp x hx0
  have hexpEq : Real.pi * x / 4 = Real.pi / 4 * x := by ring
  rw [hexpEq] at hX
  have hinv : ‖inverseXiQuotient P (((-A : ℝ) : ℂ) + (y : ℂ) * I)‖ =
      ‖P (((-A : ℝ) : ℂ) + (y : ℂ) * I)‖ * ‖(xi (1 + 2 * (((-A : ℝ) : ℂ) + (y : ℂ) * I)))⁻¹‖ := by
    rw [inverseXiQuotient, div_eq_mul_inv, norm_mul]
  rw [hinv]
  have hinvBound : ‖(xi (1 + 2 * (((-A : ℝ) : ℂ) + (y : ℂ) * I)))⁻¹‖ ≤
      C₂ * C₃ * ((1 + x) ^ (N₂ + N₃) * Real.exp (Real.pi / 4 * x)) := by
    refine hX.trans ?_
    calc C₂ * (1 + x) ^ N₂ * Real.exp (Real.pi / 4 * x) *
          ‖(riemannZeta (1 + 2 * (((-A : ℝ) : ℂ) + (y : ℂ) * I)))⁻¹‖
        ≤ C₂ * (1 + x) ^ N₂ * Real.exp (Real.pi / 4 * x) * (C₃ * (1 + x) ^ N₃) :=
          mul_le_mul_of_nonneg_left hZ (by positivity)
      _ = C₂ * C₃ * ((1 + x) ^ (N₂ + N₃) * Real.exp (Real.pi / 4 * x)) := by
          rw [pow_add]
          ring
  have hfinal : ‖(xi (1 + 2 * (((-A : ℝ) : ℂ) + (y : ℂ) * I)))⁻¹‖ ≤
      C₂ * C₃ * (C₄ * Real.exp (c / 8 * x ^ 2)) :=
    hinvBound.trans (mul_le_mul_of_nonneg_left hcm (by positivity))
  have hxsq : x ^ 2 = 4 * y ^ 2 := by
    rw [hx, mul_pow, sq_abs]
    ring
  calc ‖P (((-A : ℝ) : ℂ) + (y : ℂ) * I)‖ * ‖(xi (1 + 2 * (((-A : ℝ) : ℂ) + (y : ℂ) * I)))⁻¹‖
      ≤ (C₁ * Real.exp (-c * y ^ 2)) * (C₂ * C₃ * (C₄ * Real.exp (c / 8 * x ^ 2))) :=
        mul_le_mul hP1 hfinal (norm_nonneg _) (by positivity)
    _ = C₁ * (C₂ * C₃ * C₄) * (Real.exp (-c * y ^ 2) * Real.exp (c / 8 * x ^ 2)) := by ring
    _ = C₁ * (C₂ * C₃ * C₄) * Real.exp (-(c / 2) * y ^ 2) := by
        rw [← Real.exp_add, hxsq]
        congr 2
        ring

/-- At a good height, the boundary integral over the rectangle `[-A,0] × [-T/2,T/2]` is the sum of the
residues at the zeros inside. -/
theorem rectangleIntegral'_inverseXiQuotient {A : ℝ} (hA : 1 ≤ A) {P : ℂ → ℂ}
    (hP : GaussianNumerator A P) (k : ℕ) :
    RectangleIntegral' (inverseXiQuotient P) ⟨-A, -(goodHeight k / 2)⟩ ⟨0, goodHeight k / 2⟩ =
      ∑ p ∈ ringdownPoles (goodHeight k), laurentCoeff (inverseXiQuotient P) p (-1) := by
  have hT := one_le_goodHeight k
  have hre1 : (-A : ℝ) ≤ 0 := by linarith
  have him1 : -(goodHeight k / 2) ≤ goodHeight k / 2 := by linarith
  have hmemRect : ∀ s ∈ Rectangle (⟨-A, -(goodHeight k / 2)⟩ : ℂ) ⟨0, goodHeight k / 2⟩,
      -A ≤ s.re ∧ s.re ≤ 0 ∧ |s.im| ≤ goodHeight k / 2 := by
    intro s hs
    rw [Rectangle, Complex.mem_reProdIm] at hs
    simp only at hs
    rw [uIcc_of_le hre1, uIcc_of_le him1] at hs
    exact ⟨hs.1.1, hs.1.2, abs_le.mpr hs.2⟩
  refine rectangleIntegral'_eq_sum_laurentCoeff hre1 him1 ?_ ?_ ?_
  · intro p hp
    obtain ⟨h0, hle⟩ := mem_ringdownPoles.mp hp
    have hloc := re_of_mem_ringdownPoleSet (T := goodHeight k) ⟨h0, hle⟩
    have hne : |p.im| ≠ goodHeight k / 2 := by
      intro he
      refine xi_ne_zero_of_abs_im_goodHeight k (s := 1 + 2 * p) ?_ h0
      have h3 : (1 + 2 * p).im = 2 * p.im := by simp
      rw [h3, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), he]
      ring
    have hlt : |p.im| < goodHeight k / 2 := lt_of_le_of_ne hle hne
    rw [rectangle_mem_nhds_iff, Complex.mem_reProdIm]
    simp only
    rw [uIoo_of_le hre1, uIoo_of_le him1]
    exact ⟨⟨by linarith [hloc.1], hloc.2⟩, abs_lt.mp hlt⟩
  · intro p hp
    obtain ⟨h0, hle⟩ := mem_ringdownPoles.mp hp
    have hloc := re_of_mem_ringdownPoleSet (T := goodHeight k) ⟨h0, hle⟩
    exact meromorphicAt_inverseXiQuotient hP (by linarith [hloc.1]) hloc.2.le
  · intro s hs hsP
    obtain ⟨h1, h2, h3⟩ := hmemRect s hs
    refine analyticAt_inverseXiQuotient hP h1 h2 fun h0 => hsP ?_
    exact mem_ringdownPoles.mpr ⟨h0, h3⟩

/-- **The contour theorem.**  The residues at the zeros up to the good heights converge to the
difference of the two line integrals. -/
theorem tendsto_sum_laurentCoeff_inverseXiQuotient {A : ℝ} (hA : 1 ≤ A) {P : ℂ → ℂ}
    (hP : GaussianNumerator A P) :
    Tendsto (fun k => ∑ p ∈ ringdownPoles (goodHeight k), laurentCoeff (inverseXiQuotient P) p (-1))
      atTop (𝓝 ((2 * Real.pi : ℂ)⁻¹ * ((∫ y : ℝ, inverseXiQuotient P ((y : ℂ) * I)) -
        ∫ y : ℝ, inverseXiQuotient P (((-A : ℝ) : ℂ) + (y : ℂ) * I)))) := by
  simp_rw [← rectangleIntegral'_inverseXiQuotient hA hP]
  obtain ⟨C, c, k₀, hC, hc, hedge⟩ := exists_norm_inverseXiQuotient_edge_le hA hP
  have hAnn : 0 ≤ A := by linarith
  have hTat := tendsto_goodHeight
  have hbound : Tendsto (fun k => C * Real.exp (-c * goodHeight k ^ 2) * A) atTop (𝓝 0) := by
    have hsq : Tendsto (fun k => c * goodHeight k ^ 2) atTop atTop :=
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hTat).const_mul_atTop hc
    have hexp : Tendsto (fun k => Real.exp (-c * goodHeight k ^ 2)) atTop (𝓝 0) := by
      refine (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hsq)).congr fun k => ?_
      simp only [Function.comp_def]
      congr 1
      ring
    simpa using (hexp.const_mul C).mul_const A
  have hEdge : ∀ s : ℝ, s = 1 ∨ s = -1 → Tendsto
      (fun k => HIntegral (inverseXiQuotient P) (-A) 0 (s * (goodHeight k / 2))) atTop (𝓝 0) := by
    intro s hs
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_ge_atTop k₀, hTat.eventually_ge_atTop 2] with k hk hT2
    rw [HIntegral]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := -A) (b := 0)
      (f := fun x : ℝ => inverseXiQuotient P ((x : ℂ) + ((s * (goodHeight k / 2) : ℝ) : ℂ) * I))
      (C := C * Real.exp (-c * goodHeight k ^ 2)) (fun x hx => by
        rw [uIoc_of_le (by linarith)] at hx
        have hre : ((x : ℂ) + ((s * (goodHeight k / 2) : ℝ) : ℂ) * I).re = x := by simp
        have him : ((x : ℂ) + ((s * (goodHeight k / 2) : ℝ) : ℂ) * I).im = s * (goodHeight k / 2) := by
          simp
        refine hedge k hk hT2 _ (by rw [hre]; exact hx.1.le) (by rw [hre]; exact hx.2) ?_
        rw [him]
        have hT0 : 0 ≤ goodHeight k / 2 := by linarith
        rcases hs with rfl | rfl
        · rw [one_mul, abs_of_nonneg hT0]
        · rw [neg_one_mul, abs_neg, abs_of_nonneg hT0])
    refine hb.trans (le_of_eq ?_)
    rw [sub_neg_eq_add, zero_add, abs_of_nonneg hAnn]
  have hBot := hEdge (-1) (Or.inr rfl)
  have hTop := hEdge 1 (Or.inl rfl)
  simp only [neg_one_mul, one_mul] at hBot hTop
  have hlow : Tendsto (fun k => -(goodHeight k / 2)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp (hTat.atTop_div_const (by norm_num))
  have hup : Tendsto (fun k => goodHeight k / 2) atTop atTop := hTat.atTop_div_const (by norm_num)
  have hR := intervalIntegral_tendsto_integral (integrable_inverseXiQuotient_right hA hP) hlow hup
  have hL := intervalIntegral_tendsto_integral (integrable_inverseXiQuotient_left hA hP) hlow hup
  have hmain := ((hBot.sub hTop).add (hR.const_smul I)).sub (hL.const_smul I)
  have hscaled := hmain.const_smul ((1 : ℂ) / (2 * Real.pi * I))
  have hlimit : ((1 : ℂ) / (2 * Real.pi * I)) •
      ((0 - 0 + I • ∫ y : ℝ, inverseXiQuotient P ((y : ℂ) * I)) -
        I • ∫ y : ℝ, inverseXiQuotient P (((-A : ℝ) : ℂ) + (y : ℂ) * I)) =
      (2 * Real.pi : ℂ)⁻¹ * ((∫ y : ℝ, inverseXiQuotient P ((y : ℂ) * I)) -
        ∫ y : ℝ, inverseXiQuotient P (((-A : ℝ) : ℂ) + (y : ℂ) * I)) := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [hlimit] at hscaled
  refine hscaled.congr fun k => ?_
  simp only [RectangleIntegral', RectangleIntegral, VIntegral]
  simp

/-! ### The residue at a simple zero -/

/-- **The residue at a simple zero** of an entire denominator. -/
theorem laurentCoeff_div_of_simple_zero {P D : ℂ → ℂ} {a : ℂ} (hP : AnalyticAt ℂ P a)
    (hD : Differentiable ℂ D) (h0 : D a = 0) (hd : deriv D a ≠ 0) :
    laurentCoeff (fun u => P u / D u) a (-1) = P a / deriv D a := by
  set g := dslope D a with hg
  have hgDiff : Differentiable ℂ g := by
    have h := (Complex.differentiableOn_dslope (c := a) (s := Set.univ) (f := D) Filter.univ_mem).mpr
      hD.differentiableOn
    exact differentiableOn_univ.mp h
  have hga : g a = deriv D a := dslope_same D a
  have hfac : ∀ t : ℂ, D (a + t) = t * g (a + t) := by
    intro t
    by_cases ht : t = 0
    · simp [ht, h0]
    · have h := sub_smul_dslope D a (a + t)
      simp only [add_sub_cancel_left, h0, sub_zero, smul_eq_mul] at h
      exact h.symm
  set H : ℂ → ℂ := fun t => P (a + t) / g (a + t) with hH
  have hshift : AnalyticAt ℂ (fun t : ℂ => a + t) 0 := by fun_prop
  have hPt : AnalyticAt ℂ (fun t : ℂ => P (a + t)) 0 := by
    have : AnalyticAt ℂ P (a + 0) := by simpa using hP
    exact AnalyticAt.fun_comp this hshift
  have hgt : AnalyticAt ℂ (fun t : ℂ => g (a + t)) 0 := by
    have : AnalyticAt ℂ g (a + 0) := hgDiff.analyticAt _
    exact AnalyticAt.fun_comp this hshift
  have hH0 : AnalyticAt ℂ H 0 := hPt.div hgt (by simpa [hga] using hd)
  have hL : laurentShift (fun u => P u / D u) a 2 = fun t => t * H t := by
    funext t
    simp only [laurentShift, hfac, hH]
    by_cases ht : t = 0
    · simp [ht]
    · by_cases hgz : g (a + t) = 0
      · simp [hgz]
      · field_simp
  have hanalytic : AnalyticAt ℂ (laurentShift (fun u => P u / D u) a 2) 0 := by
    rw [hL]
    exact (analyticAt_id).mul hH0
  have hval := laurentCoeff_eq_taylorCoeffZero (ℓ := -1) hanalytic (by norm_num)
  rw [hval]
  have hidx : ((-1 : ℤ) + ((2 : ℕ) : ℤ)).toNat = 1 := by norm_num
  rw [hidx, taylorCoeffZero, hL]
  simp only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, div_one]
  have hder : HasDerivAt (fun t => t * H t) (1 * H 0 + 0 * deriv H 0) 0 :=
    (hasDerivAt_id' (0 : ℂ)).mul hH0.differentiableAt.hasDerivAt
  rw [hder.deriv]
  simp [hH, hga]

/-- The residue of `P(u)/ξ(1 + 2u)` at a simple zero. -/
theorem laurentCoeff_inverseXiQuotient_of_simple {P : ℂ → ℂ} {p : ℂ} (hP : AnalyticAt ℂ P p)
    (h0 : xi (1 + 2 * p) = 0) (hd : deriv (fun u : ℂ => xi (1 + 2 * u)) p ≠ 0) :
    laurentCoeff (inverseXiQuotient P) p (-1) = P p / deriv (fun u : ℂ => xi (1 + 2 * u)) p :=
  laurentCoeff_div_of_simple_zero hP differentiable_xi_shift h0 hd

end GaloisForLFunctions.BlackHoleRingdown

end
