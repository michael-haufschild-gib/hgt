import GaloisForLFunctions.RHTower.ThetaHalfLinePortCrossings
import GaloisForLFunctions.RHTower.FiniteZeroHadamardProduct
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaEigenODE

/-!
# Exact symmetrization of the theta half-line port

With the right-half-plane reflection `F#(w) = conj F(-w̄)`, the half-line transform satisfies
`K# = K(-·)` and the symmetrized port `X = K + K#` is `ΞC(i·)`.

* A zero-free entire function of finite exponential type is `exp(aw + b)`: the finite-zero
  Hadamard form gives `g = p·e^q`, `p` has no root, and a polynomial with linearly bounded real
  part has degree at most one.
* **Gauge rigidity.** If `g` is such a gauge and `(gK) + (gK)# = K + K#`, then at every positive
  real Xi zero `gK(iγ)` is purely imaginary while `K(iγ) = i b(γ)` with `b(γ) > 0`, so
  `sin((Re a)γ + Im b) = 0`.  The zeros of `sin(αγ + β)` in `[0, T]` number `O(1 + T)`, whereas the
  simple critical ordinates number at least `T log T/(72π)`; hence `Re a = 0`, `Im b ∈ πℤ`,
  `g# = g`, and `(g - 1)X = 0` with `X(0) ≠ 0` forces `g ≡ 1`.
* Additive ports: `E + E# = K + K#` exactly when `E - K` is anti-reflected.  The circular receiver
  `E₀ = (1/2 + w)X` obeys `|E₀|² - |E₀#|² = 2 Re(w) |X|²` and vanishes at every critical zero.
  The first moment port `E₁ = X/2 + λX'` has `E₁(iγ) = -iλΞ'(γ)` and normal modulus derivative
  `2λΞ'(γ)²` at critical zeros, while `E₁# = -E₁` at every zero of `X`.
* The causal source flow has midpoint amplitude `u_z(0) = -i K(-iz)`, nonzero at every zero of
  `ΞC`.
-/

open Complex MeasureTheory Set Filter Topology Polynomial
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## Zero-free entire functions of finite exponential type -/

/-- A polynomial whose real part grows at most linearly has degree at most one. -/
theorem natDegree_le_one_of_re_eval_le {q : ℂ[X]} {A K : ℝ}
    (h : ∀ w : ℂ, (q.eval w).re ≤ A * ‖w‖ + K) : q.natDegree ≤ 1 := by
  by_contra hn
  rw [not_le] at hn
  set n := q.natDegree with hndef
  have hq0 : q ≠ 0 := by intro h0; rw [hndef, h0, natDegree_zero] at hn; omega
  set c := q.leadingCoeff
  have hc : c ≠ 0 := leadingCoeff_ne_zero.mpr hq0
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq ((‖c‖ : ℂ) / c) (by omega : 0 < n)
  have hun : ‖u‖ = 1 := by
    have h1 : ‖u‖ ^ n = 1 := by
      rw [← norm_pow, hu, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcn, div_self hcn.ne']
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).mp h1
  set M := ∑ i ∈ Finset.range n, ‖q.coeff i‖
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hre : ∀ r : ℝ, 1 ≤ r → ‖c‖ * r ^ n - M * r ^ (n - 1) ≤ (q.eval (r * u)).re := by
    intro r hr
    rw [eval_eq_sum_range, Finset.sum_range_succ]
    have hcoef : q.coeff n = c := by rw [hndef]; rfl
    have hlead : q.coeff n * ((r : ℂ) * u) ^ n = ((‖c‖ * r ^ n : ℝ) : ℂ) := by
      rw [hcoef, mul_pow, hu]; push_cast; field_simp
    rw [← hndef, hlead, Complex.add_re, Complex.ofReal_re]
    have hbound : ‖∑ i ∈ Finset.range n, q.coeff i * ((r : ℂ) * u) ^ i‖ ≤ M * r ^ (n - 1) := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith),
        hun, mul_one]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr ?_) (norm_nonneg _)
      have := Finset.mem_range.mp hi; omega
    have h3 := Complex.abs_re_le_norm (∑ i ∈ Finset.range n, q.coeff i * ((r : ℂ) * u) ^ i)
    have h4 := neg_abs_le (∑ i ∈ Finset.range n, q.coeff i * ((r : ℂ) * u) ^ i).re
    linarith
  -- choose a large radius
  set r := max 1 ((M + |A| + |K| + 1) / ‖c‖)
  have hr1 : 1 ≤ r := le_max_left _ _
  have hrc : M + |A| + |K| + 1 ≤ ‖c‖ * r := by
    have := le_max_right 1 ((M + |A| + |K| + 1) / ‖c‖)
    rw [div_le_iff₀ hcn] at this
    linarith
  have h1 := hre r hr1
  have h2 := h (r * u)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), hun, mul_one] at h2
  have hpow : r ≤ r ^ (n - 1) := by
    calc r = r ^ 1 := (pow_one r).symm
      _ ≤ r ^ (n - 1) := pow_le_pow_right₀ hr1 (by omega)
  have hsplit : r ^ n = r * r ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have key : ‖c‖ * r ^ n - M * r ^ (n - 1) ≥ (|A| + |K| + 1) * r ^ (n - 1) := by
    rw [hsplit]; nlinarith [pow_pos (lt_of_lt_of_le one_pos hr1) (n - 1)]
  have h5 : (|A| + |K| + 1) * r ^ (n - 1) ≥ (|A| + |K| + 1) * r := by
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have h6 : A * r ≤ |A| * r := mul_le_mul_of_nonneg_right (le_abs_self A) (by linarith)
  have h7 : K ≤ |K| * r := by nlinarith [le_abs_self K, abs_nonneg K]
  linarith

/-- A zero-free entire function of finite exponential type is `exp(aw + b)`. -/
theorem exists_eq_exp_affine_of_ne_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g) (hg0 : ∀ w, g w ≠ 0)
    {C A : ℝ} (hgrow : ∀ w, ‖g w‖ ≤ C * Real.exp (A * ‖w‖)) :
    ∃ a b : ℂ, ∀ w, g w = Complex.exp (a * w + b) := by
  have hC : 0 < C := by
    have := hgrow 0
    rw [norm_zero, mul_zero, Real.exp_zero, mul_one] at this
    exact lt_of_lt_of_le (norm_pos_iff.mpr (hg0 0)) this
  set C' := |Real.log C| + |A|
  have hgrow' : ∀ w, ‖g w‖ ≤ Real.exp (C' * (1 + ‖w‖) ^ 1) := by
    intro w
    refine (hgrow w).trans ?_
    rw [← Real.exp_log hC, ← Real.exp_add, pow_one]
    refine Real.exp_le_exp.mpr ?_
    have h1 : Real.log C ≤ |Real.log C| := le_abs_self _
    have h2 : A * ‖w‖ ≤ |A| * ‖w‖ := mul_le_mul_of_nonneg_right (le_abs_self A) (norm_nonneg _)
    nlinarith [norm_nonneg w, abs_nonneg (Real.log C), abs_nonneg A]
  have hfin : {z : ℂ | g z = 0}.Finite := by
    convert Set.finite_empty
    ext z; simp [hg0 z]
  obtain ⟨p, q, hp, hform⟩ := exists_polynomial_mul_expPolynomial_of_finite_zeroSet hg
    (by positivity) hgrow' hfin
  -- the polynomial factor has no root, hence is a nonzero constant
  have hdeg : p.natDegree = 0 := by
    by_contra hd
    obtain ⟨z, hz⟩ := Complex.exists_root (f := p) (by
      rw [Polynomial.degree_eq_natDegree hp]; exact_mod_cast Nat.pos_of_ne_zero hd)
    apply hg0 z
    rw [hform z, hz.eq_zero, zero_mul]
  set c := p.coeff 0
  have hpc : p = Polynomial.C c := eq_C_of_natDegree_eq_zero hdeg
  have hc : c ≠ 0 := by
    intro h0; apply hp; rw [hpc, h0, map_zero]
  -- the exponent has degree at most one
  have hq : q.natDegree ≤ 1 := by
    refine natDegree_le_one_of_re_eval_le (A := A) (K := Real.log C - Real.log ‖c‖) fun w => ?_
    have h1 := hgrow w
    rw [hform w, hpc, eval_C, norm_mul, Complex.norm_exp] at h1
    have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have h2 : Real.exp (q.eval w).re ≤ Real.exp (Real.log C - Real.log ‖c‖ + A * ‖w‖) := by
      rw [Real.exp_add, Real.exp_sub, Real.exp_log hC, Real.exp_log hcn]
      rw [div_mul_eq_mul_div, le_div_iff₀ hcn]
      linarith
    have := Real.exp_le_exp.mp h2
    linarith
  refine ⟨q.coeff 1, q.coeff 0 + Complex.log c, fun w => ?_⟩
  have hqe : q.eval w = q.coeff 1 * w + q.coeff 0 := by
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hq]
    simp
  rw [hform w, hpc, eval_C, hqe, show q.coeff 1 * w + (q.coeff 0 + Complex.log c) =
    (q.coeff 1 * w + q.coeff 0) + Complex.log c by ring,
    Complex.exp_add (q.coeff 1 * w + q.coeff 0) (Complex.log c), Complex.exp_log hc]
  ring

/-- The zeros of `sin(αγ + β)` in `[0, T]` number at most `2|α|T/π + 3` when `α ≠ 0`. -/
theorem card_le_of_sin_eq_zero {α β T : ℝ} (hα : α ≠ 0) (hT : 0 ≤ T) {Z : Finset ℝ}
    (hZ : ∀ γ ∈ Z, 0 ≤ γ ∧ γ ≤ T ∧ Real.sin (α * γ + β) = 0) :
    (Z.card : ℝ) ≤ 2 * |α| * T / Real.pi + 3 := by
  classical
  have hpi := Real.pi_pos
  set k : ℝ → ℤ := fun γ => ⌊(α * γ + β) / Real.pi⌋
  have hk : ∀ γ ∈ Z, ((k γ : ℤ) : ℝ) * Real.pi = α * γ + β := by
    intro γ hγ
    obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp (hZ γ hγ).2.2
    have : (α * γ + β) / Real.pi = m := by rw [← hm]; field_simp
    simp only [k, this, Int.floor_intCast]
    exact hm
  have hinj : Set.InjOn k Z := by
    intro γ hγ γ' hγ' h
    have h1 := hk γ hγ
    have h2 := hk γ' hγ'
    rw [h] at h1
    have : α * γ = α * γ' := by linarith
    exact mul_left_cancel₀ hα this
  set lo := ⌊(β - |α| * T) / Real.pi⌋
  set hi := ⌈(β + |α| * T) / Real.pi⌉
  have hsub : Z.image k ⊆ Finset.Icc lo hi := by
    intro m hm
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨h0, hT', _⟩ := hZ γ hγ
    have hb : |α * γ| ≤ |α| * T := by
      rw [abs_mul, abs_of_nonneg h0]; exact mul_le_mul_of_nonneg_left hT' (abs_nonneg _)
    have hkv := hk γ hγ
    have hlo : (β - |α| * T) / Real.pi ≤ k γ := by
      rw [div_le_iff₀ hpi, hkv]; linarith [neg_abs_le (α * γ)]
    have hhi : (k γ : ℝ) ≤ (β + |α| * T) / Real.pi := by
      rw [le_div_iff₀ hpi, hkv]; linarith [le_abs_self (α * γ)]
    exact Finset.mem_Icc.mpr ⟨Int.floor_le_iff.mpr (by linarith), Int.le_ceil_iff.mpr (by linarith)⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Int.card_Icc] at hcard
  have hlo' : (lo : ℝ) ≥ (β - |α| * T) / Real.pi - 1 := by
    have := Int.lt_floor_add_one ((β - |α| * T) / Real.pi); linarith
  have hhi' : (hi : ℝ) ≤ (β + |α| * T) / Real.pi + 1 := by
    have := Int.ceil_lt_add_one ((β + |α| * T) / Real.pi); linarith
  have hc : (Z.card : ℝ) ≤ ((hi + 1 - lo).toNat : ℝ) := by exact_mod_cast hcard
  have hbound0 : 0 ≤ 2 * |α| * T / Real.pi + 3 := by positivity
  rcases le_or_gt (hi + 1 - lo) 0 with h | h
  · rw [Int.toNat_eq_zero.mpr h] at hc; push_cast at hc; linarith
  have h1 : ((hi + 1 - lo).toNat : ℝ) = (hi : ℝ) + 1 - lo := by
    rw [show ((hi + 1 - lo).toNat : ℝ) = ((hi + 1 - lo : ℤ) : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg h.le]; push_cast; rfl
  have hdiv : (β + |α| * T) / Real.pi - (β - |α| * T) / Real.pi = 2 * |α| * T / Real.pi := by
    field_simp; ring
  linarith

/-! ## Exact symmetrization fixes every finite-type scalar gauge -/

/-- Right-half-plane reflection `F#(w) = conj F(-w̄)`. -/
def halfPortReflect (F : ℂ → ℂ) (w : ℂ) : ℂ := (starRingEnd ℂ) (F (-(starRingEnd ℂ) w))

theorem halfPortReflect_thetaHalfLaplace (w : ℂ) :
    halfPortReflect thetaHalfLaplace w = thetaHalfLaplace (-w) := by
  rw [halfPortReflect, ← thetaHalfLaplace_conj, map_neg, Complex.conj_conj]

/-- The symmetrized port `X(w) = K(w) + K(-w) = ΞC(iw)`. -/
def thetaSymmetrizedPort (w : ℂ) : ℂ := thetaHalfLaplace w + thetaHalfLaplace (-w)

theorem halfPortReflect_thetaSymmetrizedPort (w : ℂ) :
    halfPortReflect thetaSymmetrizedPort w = thetaSymmetrizedPort w := by
  rw [halfPortReflect, thetaSymmetrizedPort, thetaSymmetrizedPort, map_add, neg_neg,
    ← thetaHalfLaplace_conj, ← thetaHalfLaplace_conj, map_neg, Complex.conj_conj, add_comm]

theorem thetaSymmetrizedPort_mul_I (t : ℝ) : thetaSymmetrizedPort (t * I) = (Xi t : ℂ) :=
  (ofReal_Xi_eq_thetaHalfLaplace t).symm

theorem thetaSymmetrizedPort_zero_ne : thetaSymmetrizedPort 0 ≠ 0 := by
  rw [thetaSymmetrizedPort, neg_zero, thetaHalfLaplace_zero]
  have := integral_Ioi_thetaCuspFullSource_pos
  intro h
  have h2 := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at h2
  linarith

theorem differentiable_thetaSymmetrizedPort : Differentiable ℂ thetaSymmetrizedPort :=
  differentiable_thetaHalfLaplace.add (differentiable_thetaHalfLaplace.comp differentiable_neg)

/-- **Gauge rigidity (7b)–(7d).** A zero-free entire gauge `g` of finite exponential type with
`(gK) + (gK)# = K + K#` is identically `1`. -/
theorem thetaHalfLaplace_gauge_eq_one {g : ℂ → ℂ} (hg : Differentiable ℂ g) (hg0 : ∀ w, g w ≠ 0)
    {C A : ℝ} (hgrow : ∀ w, ‖g w‖ ≤ C * Real.exp (A * ‖w‖))
    (hsym : ∀ w, g w * thetaHalfLaplace w + halfPortReflect (fun z => g z * thetaHalfLaplace z) w =
      thetaHalfLaplace w + halfPortReflect thetaHalfLaplace w) :
    ∀ w, g w = 1 := by
  obtain ⟨a, b, hab⟩ := exists_eq_exp_affine_of_ne_zero hg hg0 hgrow
  -- the gauge is real at every positive real Xi zero
  have hphase : ∀ γ : ℝ, 0 < γ → Xi γ = 0 → Real.sin (a.re * γ + b.im) = 0 := by
    intro γ hγ hX
    have h := hsym (γ * I)
    have hc : -(starRingEnd ℂ) ((γ : ℂ) * I) = (γ : ℂ) * I := by simp
    simp only [halfPortReflect, hc] at h
    rw [thetaHalfLaplace_I_mul_of_Xi_eq_zero hX] at h
    set E := g (γ * I) * ((thetaHalfSineResponse γ : ℂ) * I)
    have hre : E.re = 0 := by
      have := congrArg Complex.re h
      simp only [Complex.add_re, Complex.conj_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im] at this
      linarith
    have hb := thetaHalfSineResponse_pos hγ
    have him : (g (γ * I)).im = 0 := by
      have : E.re = -(thetaHalfSineResponse γ * (g (γ * I)).im) := by
        simp only [E, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]; ring
      rw [this] at hre
      rcases mul_eq_zero.mp (neg_eq_zero.mp hre) with h | h
      · linarith
      · exact h
    rw [hab, Complex.exp_im] at him
    have hs := (mul_eq_zero.mp him).resolve_left (Real.exp_pos _).ne'
    simpa [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, mul_comm] using hs
  -- `Re a = 0`, by counting simple critical zeros against zeros of a sine
  have hare : a.re = 0 := by
    by_contra hα
    have hlog : ∀ᶠ T : ℝ in atTop, 144 * |a.re| + 72 * Real.pi ≤ Real.log T :=
      Real.tendsto_log_atTop.eventually_ge_atTop _
    obtain ⟨T, hT, hS, hT3⟩ := (hlog.and (eventually_superlinear_xiSimpleCriticalZeroCount.and
      (eventually_gt_atTop 3))).exists
    classical
    set Sf := (stripFinsetPos T).filter fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1
    have hcard : (Sf.image Complex.im).card = xiSimpleCriticalZeroCount T :=
      card_image_im_of_critical fun z hz => (Finset.mem_filter.mp hz).2.1
    have hbound := card_le_of_sin_eq_zero (Z := Sf.image Complex.im) hα (by linarith) (by
      intro γ hγ
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hγ
      obtain ⟨hzs, hre, _⟩ := Finset.mem_filter.mp hz
      have hmem := mem_stripFinsetPos.mp hzs
      exact ⟨hmem.2.2.1.le, hmem.2.2.2.1, hphase z.im hmem.2.2.1 (Xi_im_eq_zero_of_mem hzs hre)⟩)
    rw [hcard] at hbound
    have hpi := Real.pi_pos
    have h1 : 1 / (72 * Real.pi) * T * Real.log T ≥ T * (2 * |a.re| / Real.pi + 1) := by
      rw [ge_iff_le, show 1 / (72 * Real.pi) * T * Real.log T = T * (Real.log T / (72 * Real.pi)) by
        ring]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      rw [le_div_iff₀ (by positivity)]
      have e : (2 * |a.re| / Real.pi + 1) * (72 * Real.pi) = 144 * |a.re| + 72 * Real.pi := by
        field_simp; ring
      linarith
    have h2 : T * (2 * |a.re| / Real.pi + 1) = 2 * |a.re| * T / Real.pi + T := by
      field_simp
    linarith
  -- `Im b ∈ πℤ`
  obtain ⟨γ₀, hγ₀, hX₀, -⟩ := exists_simpleCrossing_above 1 (Or.inl rfl) 0
  have hsinb : Real.sin b.im = 0 := by simpa [hare] using hphase γ₀ hγ₀ hX₀
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hsinb
  -- the gauge is self-reflected
  have hself : ∀ w, (starRingEnd ℂ) (g (-(starRingEnd ℂ) w)) = g w := by
    intro w
    rw [hab, hab, ← Complex.exp_conj]
    have hb : (starRingEnd ℂ) b = b - (2 * m : ℤ) * (Real.pi * I) := by
      apply Complex.ext
      · simp
      · simp; linarith
    have ha : (starRingEnd ℂ) a = -a := by
      apply Complex.ext <;> simp [hare]
    rw [map_add, map_mul, map_neg, Complex.conj_conj, ha, hb,
      show -a * -w + (b - ((2 * m : ℤ) : ℂ) * (Real.pi * I)) =
        a * w + b - ((m : ℤ) : ℂ) * (2 * Real.pi * I) by push_cast; ring,
      Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]
  -- hence `(g - 1) X = 0`
  have hkey : ∀ w, (g w - 1) * thetaSymmetrizedPort w = 0 := by
    intro w
    have h := hsym w
    simp only [halfPortReflect, map_mul] at h
    rw [hself, ← thetaHalfLaplace_conj, map_neg, Complex.conj_conj] at h
    rw [thetaSymmetrizedPort]
    linear_combination h
  have hXev : ∀ᶠ w in 𝓝 (0 : ℂ), thetaSymmetrizedPort w ≠ 0 :=
    differentiable_thetaSymmetrizedPort.continuous.continuousAt.eventually_ne
      thetaSymmetrizedPort_zero_ne
  have hgev : g =ᶠ[𝓝 (0 : ℂ)] fun _ => (1 : ℂ) := by
    filter_upwards [hXev] with w hw
    have := hkey w
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hw)
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (f := g)
    (fun z _ => hg.analyticAt z) (analyticOnNhd_const (v := (1 : ℂ))) isPreconnected_univ
    (mem_univ 0) hgev
  exact fun w => heq (mem_univ w)

/-! ## Additive ports and the nondegeneracy gate (7e) -/

/-- Exact symmetrization of an additive port: `E + E# = K + K#` iff `(E - K)# = -(E - K)`. -/
theorem halfPortReflect_add_eq_iff (E : ℂ → ℂ) :
    (∀ w, E w + halfPortReflect E w = thetaHalfLaplace w + halfPortReflect thetaHalfLaplace w) ↔
      ∀ w, halfPortReflect (fun z => E z - thetaHalfLaplace z) w = -(E w - thetaHalfLaplace w) := by
  simp only [halfPortReflect, map_sub]
  constructor
  · intro h w; linear_combination h w
  · intro h w; linear_combination h w

/-- The circular receiver `E₀(w) = (1/2 + w) X(w)`. -/
def thetaCircularPort (w : ℂ) : ℂ := (1 / 2 + w) * thetaSymmetrizedPort w

theorem halfPortReflect_thetaCircularPort (w : ℂ) :
    halfPortReflect thetaCircularPort w = (1 / 2 - w) * thetaSymmetrizedPort w := by
  have h := halfPortReflect_thetaSymmetrizedPort w
  simp only [halfPortReflect, thetaCircularPort] at h ⊢
  rw [map_mul, h]
  congr 1
  apply Complex.ext
  · simp; ring
  · simp

/-- `E₀` symmetrizes exactly to `X`. -/
theorem thetaCircularPort_add_reflect (w : ℂ) :
    thetaCircularPort w + halfPortReflect thetaCircularPort w = thetaSymmetrizedPort w := by
  rw [halfPortReflect_thetaCircularPort, thetaCircularPort]; ring

/-- **The circular identity (7e).** `|E₀(w)|² - |E₀#(w)|² = 2 Re(w) |X(w)|²`. -/
theorem thetaCircularPort_imbalance (w : ℂ) :
    ‖thetaCircularPort w‖ ^ 2 - ‖halfPortReflect thetaCircularPort w‖ ^ 2 =
      2 * w.re * ‖thetaSymmetrizedPort w‖ ^ 2 := by
  have hs : ‖(1 / 2 : ℂ) + w‖ ^ 2 - ‖(1 / 2 : ℂ) - w‖ ^ 2 = 2 * w.re := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp
    ring
  rw [halfPortReflect_thetaCircularPort, thetaCircularPort, norm_mul, norm_mul, mul_pow, mul_pow]
  linear_combination ‖thetaSymmetrizedPort w‖ ^ 2 * hs

/-- `E₀` vanishes at every critical Xi zero. -/
theorem thetaCircularPort_eq_zero {γ : ℝ} (hγ : Xi γ = 0) : thetaCircularPort (γ * I) = 0 := by
  rw [thetaCircularPort, thetaSymmetrizedPort_mul_I, hγ, Complex.ofReal_zero, mul_zero]

/-! ## The first source-moment port -/

theorem hasDerivAt_thetaSymmetrizedPort (w : ℂ) :
    HasDerivAt thetaSymmetrizedPort (deriv thetaSymmetrizedPort w) w :=
  (differentiable_thetaSymmetrizedPort w).hasDerivAt

/-- `X'` is anti-reflected: `conj X'(-w̄) = -X'(w)`. -/
theorem halfPortReflect_deriv_thetaSymmetrizedPort (w : ℂ) :
    halfPortReflect (deriv thetaSymmetrizedPort) w = -deriv thetaSymmetrizedPort w := by
  have h := ((hasDerivAt_thetaSymmetrizedPort (-(starRingEnd ℂ) w)).comp
    ((starRingEnd ℂ) w) (hasDerivAt_neg _)).conj_conj
  have e : (⇑(starRingEnd ℂ) ∘ (thetaSymmetrizedPort ∘ fun z => -z) ∘ ⇑(starRingEnd ℂ)) =
      thetaSymmetrizedPort := by
    funext z
    have := halfPortReflect_thetaSymmetrizedPort z
    simp only [halfPortReflect] at this
    simp only [Function.comp, this]
  rw [e, Complex.conj_conj] at h
  rw [halfPortReflect, ← neg_eq_iff_eq_neg, h.deriv]
  simp

theorem differentiable_deriv_thetaSymmetrizedPort : Differentiable ℂ (deriv thetaSymmetrizedPort) :=
  fun w => ((differentiable_thetaSymmetrizedPort.analyticAt w).deriv).differentiableAt

/-- `X'(iγ) = -i Ξ'(γ)`. -/
theorem deriv_thetaSymmetrizedPort_mul_I (γ : ℝ) :
    deriv thetaSymmetrizedPort (γ * I) = -I * deriv Xi γ := by
  have h1 := ((hasDerivAt_thetaSymmetrizedPort ((γ : ℂ) * I)).comp (γ : ℂ)
    ((hasDerivAt_id (γ : ℂ)).mul_const I)).comp_ofReal
  have e : (fun y : ℝ => (thetaSymmetrizedPort ∘ fun x => id x * I) (y : ℂ)) =
      fun y : ℝ => ((Xi y : ℝ) : ℂ) := by
    funext y; simp [thetaSymmetrizedPort_mul_I]
  rw [e] at h1
  have h2 := (hasDerivAt_Xi_deriv γ).ofReal_comp
  have := h1.unique h2
  simp only [one_mul] at this
  rw [← this]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The first source-moment port `E₁ = X/2 + λ X'`. -/
def thetaMomentPort (lam : ℝ) (w : ℂ) : ℂ :=
  thetaSymmetrizedPort w / 2 + lam * deriv thetaSymmetrizedPort w

theorem halfPortReflect_thetaMomentPort (lam : ℝ) (w : ℂ) :
    halfPortReflect (thetaMomentPort lam) w =
      thetaSymmetrizedPort w / 2 - lam * deriv thetaSymmetrizedPort w := by
  have h1 := halfPortReflect_thetaSymmetrizedPort w
  have h2 := halfPortReflect_deriv_thetaSymmetrizedPort w
  simp only [halfPortReflect, thetaMomentPort] at h1 h2 ⊢
  rw [map_add, map_div₀, map_mul, h1, h2, Complex.conj_ofReal, map_ofNat]
  ring

/-- `E₁` symmetrizes exactly to `X`. -/
theorem thetaMomentPort_add_reflect (lam : ℝ) (w : ℂ) :
    thetaMomentPort lam w + halfPortReflect (thetaMomentPort lam) w = thetaSymmetrizedPort w := by
  rw [halfPortReflect_thetaMomentPort, thetaMomentPort]; ring

/-- At a critical zero `E₁(iγ) = -iλ Ξ'(γ)`. -/
theorem thetaMomentPort_mul_I {γ : ℝ} (hγ : Xi γ = 0) (lam : ℝ) :
    thetaMomentPort lam (γ * I) = -I * lam * deriv Xi γ := by
  rw [thetaMomentPort, thetaSymmetrizedPort_mul_I, hγ, deriv_thetaSymmetrizedPort_mul_I]
  push_cast; ring

/-- At every zero of `X`, `E₁# = -E₁`, so the two moduli agree. -/
theorem halfPortReflect_thetaMomentPort_of_eq_zero {w : ℂ} (hw : thetaSymmetrizedPort w = 0)
    (lam : ℝ) : halfPortReflect (thetaMomentPort lam) w = -thetaMomentPort lam w := by
  rw [halfPortReflect_thetaMomentPort, thetaMomentPort, hw]; ring

/-- **Local orientation of `E₁`.** At a critical zero the normal derivative of
`|E₁|² - |E₁#|²` equals `2λ Ξ'(γ)²`. -/
theorem hasDerivAt_thetaMomentPort_imbalance {γ : ℝ} (hγ : Xi γ = 0) (lam : ℝ) :
    HasDerivAt (fun α : ℝ => ‖thetaMomentPort lam (α + γ * I)‖ ^ 2 -
        ‖halfPortReflect (thetaMomentPort lam) (α + γ * I)‖ ^ 2)
      (2 * lam * deriv Xi γ ^ 2) 0 := by
  have hX : ∀ z, HasDerivAt thetaSymmetrizedPort ((deriv thetaSymmetrizedPort) z) z := hasDerivAt_thetaSymmetrizedPort
  have hX' : ∀ z, HasDerivAt (deriv thetaSymmetrizedPort) (deriv (deriv thetaSymmetrizedPort) z) z := fun z =>
    (differentiable_deriv_thetaSymmetrizedPort z).hasDerivAt
  have hline : HasDerivAt (fun α : ℝ => (α : ℂ) + γ * I) 1 0 := by
    simpa using ((hasDerivAt_id ((0 : ℝ) : ℂ)).add_const ((γ : ℂ) * I)).comp_ofReal
  have hE : HasDerivAt (fun α : ℝ => thetaMomentPort lam (α + γ * I))
      ((deriv thetaSymmetrizedPort) (γ * I) / 2 + lam * deriv (deriv thetaSymmetrizedPort) (γ * I)) 0 := by
    have h := ((hX ((((0 : ℝ) : ℂ)) + γ * I)).div_const 2).add
      ((hX' ((((0 : ℝ) : ℂ)) + γ * I)).const_mul (lam : ℂ))
    have h2 := (h.comp (((0 : ℝ) : ℂ)) ((hasDerivAt_id (((0 : ℝ) : ℂ))).add_const ((γ : ℂ) * I))).comp_ofReal
    simpa [thetaMomentPort, Function.comp] using h2
  have hEr : HasDerivAt (fun α : ℝ => halfPortReflect (thetaMomentPort lam) (α + γ * I))
      ((deriv thetaSymmetrizedPort) (γ * I) / 2 - lam * deriv (deriv thetaSymmetrizedPort) (γ * I)) 0 := by
    have h := ((hX ((((0 : ℝ) : ℂ)) + γ * I)).div_const 2).sub
      ((hX' ((((0 : ℝ) : ℂ)) + γ * I)).const_mul (lam : ℂ))
    have h2 := (h.comp (((0 : ℝ) : ℂ)) ((hasDerivAt_id (((0 : ℝ) : ℂ))).add_const ((γ : ℂ) * I))).comp_ofReal
    have e : (fun α : ℝ => halfPortReflect (thetaMomentPort lam) (α + γ * I)) =
        fun α : ℝ => thetaSymmetrizedPort (α + γ * I) / 2 - lam * (deriv thetaSymmetrizedPort) (α + γ * I) := by
      funext α; rw [halfPortReflect_thetaMomentPort]
    rw [e]
    simpa [Function.comp] using h2
  have h := hE.norm_sq.sub hEr.norm_sq
  refine h.congr_deriv ?_
  have hX0 : thetaSymmetrizedPort (γ * I) = 0 := by
    rw [thetaSymmetrizedPort_mul_I, hγ, Complex.ofReal_zero]
  have hE0 : thetaMomentPort lam (γ * I) = lam * (deriv thetaSymmetrizedPort) (γ * I) := by
    rw [thetaMomentPort, hX0]; ring
  have hEr0 : halfPortReflect (thetaMomentPort lam) (γ * I) = -(lam * (deriv thetaSymmetrizedPort) (γ * I)) := by
    rw [halfPortReflect_thetaMomentPort, hX0]; ring
  simp only [Complex.ofReal_zero, zero_add]
  rw [hE0, hEr0, Complex.inner, Complex.inner, deriv_thetaSymmetrizedPort_mul_I]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-! ## The midpoint amplitude (8) -/

/-- `u_z(0) = -i K(-iz)`. -/
theorem hedenmalmCausalVolterra_zero (α : ℂ) :
    hedenmalmCausalVolterra α 0 = -I * thetaHalfLaplace (-I * α) := by
  rw [hedenmalmCausalVolterra, thetaHalfLaplace, thetaHalfLaplaceTail]
  congr 1
  have h := integral_comp_neg_Ioi (0 : ℝ) (fun t : ℝ => hedenmalmVolterraIntegrand α 0 t)
  rw [neg_zero] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  simp only [hedenmalmVolterraIntegrand, thetaCuspFullSource_neg]
  push_cast
  ring_nf

/-- At every zero of `ΞC` the midpoint amplitude of the causal source flow is nonzero. -/
theorem hedenmalmCausalVolterra_zero_ne_zero {α : ℂ} (hα : XiC α = 0) :
    hedenmalmCausalVolterra α 0 ≠ 0 := by
  rw [hedenmalmCausalVolterra_zero]
  have h := thetaHalfLaplace_add_neg (-I * α)
  have e : I * (-I * α) = α := by ring_nf; rw [Complex.I_sq]; ring
  rw [e, hα] at h
  have := (thetaHalfLaplace_ne_zero_of_add_neg_eq_zero h).1
  exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) this

/-! ## The sine response as a jump integral (3) -/

/-- `γ b(γ) = ∫₀^∞ ν(u)(1 - cos γu) du` with `ν = -k'`. -/
theorem mul_thetaHalfSineResponse_eq (γ : ℝ) (hγ : γ ≠ 0) :
    γ * thetaHalfSineResponse γ =
      ∫ u in Ioi (0 : ℝ), -deriv thetaCuspFullSource u * (1 - Real.cos (γ * u)) := by
  have hw0 : (γ : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hγ) Complex.I_ne_zero
  have h := mul_thetaHalfLaplace_neg_of_nonneg (w := (γ : ℂ) * I) (by simp) hw0
  rw [show -((γ : ℂ) * I) = (starRingEnd ℂ) ((γ : ℂ) * I) by simp, thetaHalfLaplace_conj,
    thetaHalfLaplace_I_mul] at h
  have hν : IntegrableOn (fun u => -deriv thetaCuspFullSource u) (Ioi 0) :=
    integrableOn_Ioi_deriv_thetaCuspFullSource.neg
  have hint : IntegrableOn (fun u : ℝ => (((-deriv thetaCuspFullSource u : ℝ)) : ℂ) *
      (1 - Complex.exp (-((γ : ℂ) * I * u)))) (Ioi 0) := by
    have hcd := continuous_deriv_thetaCuspFullSource
    refine Integrable.mono' (hν.norm.mul_const 2) (by fun_prop : Continuous fun u : ℝ =>
      (((-deriv thetaCuspFullSource u : ℝ)) : ℂ) * (1 - Complex.exp (-((γ : ℂ) * I * u)))).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x _ => ?_))
    rw [norm_mul, Complex.norm_real]
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (norm_nonneg _)
    rw [norm_one, Complex.norm_exp]
    simp
    norm_num
  have hre := congrArg Complex.re h
  have hre2 := integral_re hint
  simp only [RCLike.re_to_complex] at hre2
  rw [← hre2] at hre
  rw [show (fun u : ℝ => ((((-deriv thetaCuspFullSource u : ℝ)) : ℂ) *
      (1 - Complex.exp (-((γ : ℂ) * I * u)))).re) =
      fun u => -deriv thetaCuspFullSource u * (1 - Real.cos (γ * u)) by
    funext u
    rw [Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re,
      show -((γ : ℂ) * I * u) = ((-(γ * u) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re, Real.cos_neg]] at hre
  rw [← hre]
  simp [Complex.mul_re, Complex.mul_im]

end RHTower
