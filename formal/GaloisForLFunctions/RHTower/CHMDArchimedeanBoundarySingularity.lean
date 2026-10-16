import GaloisForLFunctions.RHTower.CHMDKleinGordonBoundarySingularity
import GaloisForLFunctions.RHTower.HardyDyadicWindowTheorem

/-!
# CHMD: the archimedean boundary singularity and the exact boundary singular set

On the imaginary axis the zero-side waves are sums of `cosh(yγ_ρ) sech²(γ_ρ/2)`.  For
`|Im γ| ≤ 1/2`, `|Re γ| ≥ 3` and `1/2 ≤ y ≤ 1` every such term has real part at least
`e^{−(1−y)|Re γ|}` (`exp_le_re_cosh_div_cosh_sq_abs`), since
`cosh(yγ)/cosh²(γ/2) = 2e^{−(1−y)γ}(1 + e^{−2yγ})/(1 + e^{−γ})²`.  The finitely many low zeros cost a
bounded amount, and `Σ_ρ m_ρ e^{−δ|Re γ_ρ|} → ∞` as `δ → 0⁺` because there are infinitely many
nontrivial zeros (Hardy).  Hence `Re Φ₀((1 − δ)i) → +∞` (`tendsto_masslessZeroWave_imag_re`).  The
Bessel kernel is positive on the negative axis (`lightConeBesselReal_nonneg`), so the light-cone
transmutation only lowers `Re Φ` by a bounded amount and `Re Φ((1 − δ)i) → +∞` as well
(`tendsto_kgZeroWave_imag_re`).

Together with the continuation across the rest of the boundary and the prime-point laws this gives
the exact singular set on the boundary lines `|Im v| = 1` for both waves
(`masslessZeroWave_boundary_singular_set`, `kgZeroWave_boundary_singular_set`): a boundary point is
singular — no function continuous at it agrees with the wave inside the strip — exactly when
`|Re v| = log n` with `n = 1` or `Λ(n) ≠ 0`; at every other boundary point the wave continues
analytically.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped Real ComplexConjugate Nat
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.CHMDLightCone

open RHTower.CHMDGrowthCollapse RHTower.EvenSector

/-! ## Positivity of the Bessel kernel on the negative axis -/

/-- `B(x) ≥ 0` for `x ≤ 0`: every term `(−x/4)^k/(k!(k+1)!)` of the series is nonnegative. -/
theorem lightConeBesselReal_nonneg {x : ℝ} (hx : x ≤ 0) : 0 ≤ lightConeBesselReal x := by
  have hterm : ∀ k : ℕ, lightConeBesselTerm (x : ℂ) k =
      (((-x / 4) ^ k / ((k ! : ℝ) * ((k + 1)! : ℝ)) : ℝ) : ℂ) := fun k => by
    unfold lightConeBesselTerm; push_cast; ring
  have hs := hasSum_lightConeBessel (x : ℂ)
  unfold lightConeBesselReal
  rw [← hs.tsum_eq, Complex.re_tsum hs.summable]
  refine tsum_nonneg fun k => ?_
  rw [hterm, Complex.ofReal_re]
  have : 0 ≤ -x / 4 := by linarith
  positivity

/-! ## Sector positivity of the imaginary-time terms -/

theorem exp_neg_three_le_one_twentieth : Real.exp (-3) ≤ 1 / 20 := by
  have he := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 3
  have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have h20 : 20 ≤ Real.exp 3 := by rw [h3]; norm_num at he ⊢; linarith
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by norm_num) h20

/-- The factorisation `cosh(yγ)/cosh²(γ/2) = 2e^{−(1−y)γ}(1 + e^{−2yγ})/(1 + e^{−γ})²`, cleared of
denominators. -/
theorem cosh_factorisation (γ : ℂ) (y : ℝ) :
    2 * Complex.exp (-((1 - y) * γ)) * (1 + Complex.exp (-(2 * (y * γ)))) *
        Complex.cosh (γ / 2) ^ 2 =
      (1 + Complex.exp (-γ)) ^ 2 * Complex.cosh (y * γ) := by
  rw [show -((1 - (y : ℂ)) * γ) = y * γ + -(γ / 2) + -(γ / 2) by ring,
    show -(2 * ((y : ℂ) * γ)) = -(y * γ) + -(y * γ) by ring,
    show -γ = -(γ / 2) + -(γ / 2) by ring, Complex.cosh.eq_1, Complex.cosh.eq_1]
  simp only [Complex.exp_add, Complex.exp_neg]
  have hA := Complex.exp_ne_zero (y * γ)
  have hC := Complex.exp_ne_zero (γ / 2)
  field_simp

/-- **Sector positivity.**  For `|Im γ| ≤ 1/2`, `Re γ ≥ 3` and `1/2 ≤ y ≤ 1`,
`Re (cosh(yγ)/cosh²(γ/2)) ≥ e^{−(1−y) Re γ}`: the leading factor `2e^{−(1−y)γ}` has argument at most
`1/4`, and the correction `(1 + e^{−2yγ})/(1 + e^{−γ})²` lies within `1/4` of `1`. -/
theorem exp_le_re_cosh_div_cosh_sq {γ : ℂ} (hb : |γ.im| ≤ 1 / 2) (ha : 3 ≤ γ.re) {y : ℝ}
    (hy1 : 1 / 2 ≤ y) (hy2 : y ≤ 1) :
    Real.exp (-((1 - y) * γ.re)) ≤ (Complex.cosh (y * γ) / Complex.cosh (γ / 2) ^ 2).re := by
  have hch : Complex.cosh (γ / 2) ≠ 0 := cosh_half_ne_zero (by linarith)
  have h3 := exp_neg_three_le_one_twentieth
  set u := Complex.exp (-(2 * (y * γ))) with hu
  set w := Complex.exp (-γ) with hw
  set X : ℂ := -((1 - y) * γ) with hX
  set Z := 2 * Complex.exp X with hZ
  have hXre : X.re = -((1 - y) * γ.re) := by
    rw [hX]
    simp only [Complex.neg_re, Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Complex.sub_im, Complex.one_im, Complex.ofReal_im]
    ring
  have hXim : X.im = -((1 - y) * γ.im) := by
    rw [hX]
    simp only [Complex.neg_im, Complex.mul_im, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Complex.sub_im, Complex.one_im, Complex.ofReal_im]
    ring
  have hwn : ‖w‖ ≤ 1 / 20 := by
    rw [hw, Complex.norm_exp, Complex.neg_re]
    exact (Real.exp_le_exp.mpr (by linarith)).trans h3
  have hun : ‖u‖ ≤ 1 / 20 := by
    rw [hu, Complex.norm_exp]
    have : (-(2 * ((y : ℂ) * γ))).re = -(2 * y * γ.re) := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.re_ofNat, Complex.im_ofNat]
      ring
    rw [this]
    exact (Real.exp_le_exp.mpr (by nlinarith)).trans h3
  have hw1n : 19 / 20 ≤ ‖1 + w‖ := by
    have := norm_sub_le (1 + w) w
    rw [add_sub_cancel_right, norm_one] at this
    linarith
  have hw1 : 1 + w ≠ 0 := fun h => by rw [h, norm_zero] at hw1n; linarith
  have hid : Complex.cosh (y * γ) / Complex.cosh (γ / 2) ^ 2 = Z * ((1 + u) / (1 + w) ^ 2) := by
    rw [div_eq_iff (pow_ne_zero 2 hch),
      show Z * ((1 + u) / (1 + w) ^ 2) * Complex.cosh (γ / 2) ^ 2 =
        2 * Complex.exp X * (1 + u) * Complex.cosh (γ / 2) ^ 2 / (1 + w) ^ 2 by rw [hZ]; ring,
      hX, hu, hw, cosh_factorisation, mul_div_cancel_left₀ _ (pow_ne_zero 2 hw1)]
  set Q := (1 + u) / (1 + w) ^ 2 with hQ
  have hQ1 : ‖1 - Q‖ ≤ 1 / 4 := by
    have h1 : 1 - Q = (2 * w + w ^ 2 - u) / (1 + w) ^ 2 := by
      rw [hQ]; field_simp; ring
    have hnum : ‖2 * w + w ^ 2 - u‖ ≤ 61 / 400 := by
      have e1 := norm_sub_le (2 * w + w ^ 2) u
      have e2 := norm_add_le (2 * w) (w ^ 2)
      have e3 : ‖2 * w‖ = 2 * ‖w‖ := by rw [norm_mul]; norm_num
      have e4 : ‖w ^ 2‖ = ‖w‖ ^ 2 := norm_pow _ _
      nlinarith [norm_nonneg w]
    rw [h1, norm_div, norm_pow, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg w]
  have hE := Real.exp_pos (-((1 - y) * γ.re))
  have hZn : ‖Z‖ = 2 * Real.exp (-((1 - y) * γ.re)) := by
    rw [hZ, norm_mul, Complex.norm_exp, hXre, show ‖(2 : ℂ)‖ = 2 by norm_num]
  have hZre : Z.re = 2 * (Real.exp (-((1 - y) * γ.re)) * Real.cos (-((1 - y) * γ.im))) := by
    rw [hZ, show (2 : ℂ) * Complex.exp X = ((2 : ℝ) : ℂ) * Complex.exp X by push_cast; rfl,
      Complex.re_ofReal_mul, Complex.exp_re, hXre, hXim]
  have hcos : 31 / 32 ≤ Real.cos (-((1 - y) * γ.im)) := by
    have hsq : (-((1 - y) * γ.im)) ^ 2 ≤ 1 / 16 := by
      have : |-((1 - y) * γ.im)| ≤ 1 / 4 := by
        rw [abs_neg, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - y)]
        nlinarith [abs_nonneg γ.im]
      nlinarith [sq_abs (-((1 - y) * γ.im)), abs_nonneg (-((1 - y) * γ.im))]
    linarith [Real.one_sub_sq_div_two_le_cos (x := -((1 - y) * γ.im))]
  have hsplit : (Z * Q).re = Z.re - (Z * (1 - Q)).re := by
    rw [mul_sub, mul_one, Complex.sub_re]; ring
  have hcorr : (Z * (1 - Q)).re ≤ ‖Z‖ * (1 / 4) :=
    (Complex.re_le_norm _).trans (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left hQ1 (norm_nonneg _))
  rw [hid, hsplit, hZre]
  rw [hZn] at hcorr
  nlinarith

/-- Sector positivity on both sides: `Re (cosh(yγ)/cosh²(γ/2)) ≥ e^{−(1−y)|Re γ|}` for
`|Im γ| ≤ 1/2`, `|Re γ| ≥ 3`, `1/2 ≤ y ≤ 1`. -/
theorem exp_le_re_cosh_div_cosh_sq_abs {γ : ℂ} (hb : |γ.im| ≤ 1 / 2) (ha : 3 ≤ |γ.re|) {y : ℝ}
    (hy1 : 1 / 2 ≤ y) (hy2 : y ≤ 1) :
    Real.exp (-((1 - y) * |γ.re|)) ≤ (Complex.cosh (y * γ) / Complex.cosh (γ / 2) ^ 2).re := by
  rcases le_or_gt 0 γ.re with h | h
  · rw [abs_of_nonneg h] at ha ⊢
    exact exp_le_re_cosh_div_cosh_sq hb ha hy1 hy2
  · rw [abs_of_neg h] at ha ⊢
    have h' := exp_le_re_cosh_div_cosh_sq (γ := -γ) (by rwa [Complex.neg_im, abs_neg])
      (by rw [Complex.neg_re]; exact ha) hy1 hy2
    have e1 : Complex.cosh (y * -γ) / Complex.cosh (-γ / 2) ^ 2 =
        Complex.cosh (y * γ) / Complex.cosh (γ / 2) ^ 2 := by
      rw [mul_neg, Complex.cosh_neg, neg_div, Complex.cosh_neg]
    rwa [e1, Complex.neg_re] at h'

/-! ## The imaginary-time terms of the massless wave -/

/-- The weight of a zero is `sech²(γ/2)`. -/
theorem kgWeight_eq_inv (ρ : zetaZeroConfig.carrier) :
    kgWeight ρ = (Complex.cosh (Zeta23.gammaOf (ρ : ℂ) / 2) ^ 2)⁻¹ := by
  have hIm := abs_im_gammaOf_lt ρ
  exact eq_inv_of_mul_eq_one_left (specSq_sechHalf_mul_cosh_sq (by linarith))

/-- The bounded cost of the low zeros. -/
def archSlack : ℝ := (sechConst + 1) * Real.exp 3

/-- `Σ_ρ m_ρ e^{−δ|Re γ_ρ|}`. -/
def zeroMass (δ : ℝ) : ℝ :=
  ∑' ρ : zetaZeroConfig.carrier,
    (zetaZeroConfig.mult ρ : ℝ) * Real.exp (-(δ * |(Zeta23.gammaOf (ρ : ℂ)).re|))

theorem zeroMass_nonneg (δ : ℝ) : 0 ≤ zeroMass δ :=
  tsum_nonneg fun _ => by positivity

/-- Termwise lower bound on the imaginary axis: high zeros contribute at least `m_ρ e^{−(1−y)|Re γ|}`,
low zeros cost at most `archSlack · m_ρ e^{−|Re γ|}`. -/
theorem re_masslessTerm_imag_ge (ρ : zetaZeroConfig.carrier) {y : ℝ} (hy1 : 1 / 2 ≤ y)
    (hy2 : y ≤ 1) :
    (zetaZeroConfig.mult ρ : ℝ) * Real.exp (-((1 - y) * |(Zeta23.gammaOf (ρ : ℂ)).re|)) -
        archSlack * ((zetaZeroConfig.mult ρ : ℝ) *
          Real.exp (-(1 * |(Zeta23.gammaOf (ρ : ℂ)).re|))) ≤
      ((zetaZeroConfig.mult ρ : ℂ) *
        (Complex.cos ((y : ℂ) * I * Zeta23.gammaOf (ρ : ℂ)) * kgWeight ρ)).re := by
  have hIm := abs_im_gammaOf_lt ρ
  set γ := Zeta23.gammaOf (ρ : ℂ) with hγ
  set m := (zetaZeroConfig.mult ρ : ℝ) with hm
  have hm0 : 0 ≤ m := by positivity
  have hsl : 0 ≤ archSlack := by unfold archSlack; have := sechConst_pos; positivity
  rcases le_or_gt 3 |γ.re| with hhi | hlo
  · have hterm : ((zetaZeroConfig.mult ρ : ℂ) *
        (Complex.cos ((y : ℂ) * I * γ) * kgWeight ρ)).re =
        m * (Complex.cosh (y * γ) / Complex.cosh (γ / 2) ^ 2).re := by
      rw [show (y : ℂ) * I * γ = (y * γ) * I by ring, Complex.cos_mul_I, kgWeight_eq_inv, ← hγ,
        ← div_eq_mul_inv, show ((zetaZeroConfig.mult ρ : ℕ) : ℂ) = (m : ℂ) by rw [hm]; push_cast; rfl,
        Complex.re_ofReal_mul]
    rw [hterm]
    have h1 := mul_le_mul_of_nonneg_left
      (exp_le_re_cosh_div_cosh_sq_abs (by linarith) hhi hy1 hy2) hm0
    have h2 : 0 ≤ archSlack * (m * Real.exp (-(1 * |γ.re|))) :=
      mul_nonneg hsl (mul_nonneg hm0 (Real.exp_pos _).le)
    linarith
  · have hnorm := norm_masslessTerm_le (z := (y : ℂ) * I) (η := 1) (R := 0)
      (by rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
          rw [abs_le]; constructor <;> nlinarith)
      (by rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
          norm_num) ρ
    rw [sub_self, zero_mul, neg_zero, Real.exp_zero, mul_one, zero_div, Real.exp_zero, mul_one]
      at hnorm
    have hlow : -(sechConst * m) ≤ ((zetaZeroConfig.mult ρ : ℂ) *
        (Complex.cos ((y : ℂ) * I * γ) * kgWeight ρ)).re := by
      have h1 := Complex.abs_re_le_norm ((zetaZeroConfig.mult ρ : ℂ) *
        (Complex.cos ((y : ℂ) * I * γ) * kgWeight ρ))
      have h2 := neg_abs_le (((zetaZeroConfig.mult ρ : ℂ) *
        (Complex.cos ((y : ℂ) * I * γ) * kgWeight ρ)).re)
      linarith
    have he3 : 1 ≤ Real.exp 3 * Real.exp (-(1 * |γ.re|)) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    have hey : Real.exp (-((1 - y) * |γ.re|)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg γ.re])
    unfold archSlack
    nlinarith [mul_le_mul_of_nonneg_left hey hm0, mul_le_mul_of_nonneg_left he3 hm0,
      sechConst_pos]

/-! ## The zero mass diverges -/

/-- There are infinitely many nontrivial zeros: every dyadic window carries a critical-line zero. -/
theorem zetaZeroConfig_carrier_infinite : zetaZeroConfig.carrier.Infinite := by
  obtain ⟨T₀, -, hz⟩ := exists_riemannZeta_line_zero_dyadic
  intro hfin
  obtain ⟨B, hB⟩ := (hfin.image Complex.im).bddAbove
  obtain ⟨τ, hτ, hzero⟩ := hz (max T₀ (B + 1)) (le_max_left _ _)
  have hre : (linePt τ).re = 1 / 2 := by norm_num [linePt]
  have hmem : linePt τ ∈ zetaZeroConfig.carrier := by
    rw [zetaZeroConfig_carrier]
    exact (show riemannZeta (linePt τ) = 0 ∧ 0 < (linePt τ).re ∧ (linePt τ).re < 1 from
      ⟨hzero, by rw [hre]; norm_num, by rw [hre]; norm_num⟩)
  have h := hB ⟨linePt τ, hmem, rfl⟩
  have him : (linePt τ).im = τ := by simp [linePt]
  rw [him] at h
  linarith [hτ.1, le_max_right T₀ (B + 1)]

/-- `Σ_ρ m_ρ e^{−δ|Re γ_ρ|} → ∞` as `δ → 0⁺`. -/
theorem tendsto_zeroMass_atTop : Tendsto zeroMass (𝓝[>] 0) atTop := by
  haveI : Infinite zetaZeroConfig.carrier :=
    Set.infinite_coe_iff.mpr zetaZeroConfig_carrier_infinite
  rw [tendsto_atTop]
  intro N
  obtain ⟨F, hF⟩ := Infinite.exists_subset_card_eq zetaZeroConfig.carrier (⌈N⌉₊ + 1)
  have hlim : Tendsto (fun δ : ℝ => ∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) *
      Real.exp (-(δ * |(Zeta23.gammaOf (ρ : ℂ)).re|))) (𝓝[>] 0)
      (𝓝 (∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ))) := by
    have hc : Continuous (fun δ : ℝ => ∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) *
        Real.exp (-(δ * |(Zeta23.gammaOf (ρ : ℂ)).re|))) := by fun_prop
    have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using h
  have hgt : N < ∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) := by
    have h1 : ∀ ρ ∈ F, (1 : ℝ) ≤ zetaZeroConfig.mult ρ := fun ρ _ => by
      exact_mod_cast zetaZeroConfig.one_le_mult ρ ρ.2
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, hF] at h2
    push_cast at h2
    linarith [Nat.le_ceil N]
  filter_upwards [hlim.eventually (eventually_gt_nhds hgt), self_mem_nhdsWithin] with δ h1 h2
  exact h1.le.trans (Summable.sum_le_tsum F (fun _ _ => by positivity)
    (summable_mult_mul_exp_neg_abs_re h2))

/-! ## Divergence of the massless wave at `i` -/

theorem masslessZeroWave_imag_re_ge {y : ℝ} (hy1 : 1 / 2 ≤ y) (hy2 : y < 1) :
    zeroMass (1 - y) - archSlack * zeroMass 1 ≤ (masslessZeroWave (y * I)).re := by
  have hs : (y : ℂ) * I ∈ causalTimeStrip := by
    show |((y : ℂ) * I).im| < 1
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one,
      zero_mul, add_zero, abs_lt]
    constructor <;> linarith
  have h1 := summable_mult_mul_exp_neg_abs_re (ε := 1 - y) (by linarith)
  have h2 := summable_mult_mul_exp_neg_abs_re (ε := 1) one_pos
  have h3 := summable_masslessTerm _ hs
  unfold masslessZeroWave zeroMass
  rw [Complex.re_tsum h3, ← tsum_mul_left, ← h1.tsum_sub (h2.mul_left archSlack)]
  exact Summable.tsum_le_tsum (fun ρ => re_masslessTerm_imag_ge ρ hy1 hy2.le)
    (h1.sub (h2.mul_left archSlack)) (by simpa using Complex.reCLM.summable h3)

/-- **The archimedean singularity of the massless wave.**  `Re Φ₀((1 − δ) i) → +∞` as
`δ → 0⁺`. -/
theorem tendsto_masslessZeroWave_imag_re :
    Tendsto (fun δ : ℝ => (masslessZeroWave ((1 - δ : ℝ) * I)).re) (𝓝[>] 0) atTop := by
  refine tendsto_atTop_mono' _ ?_
    (tendsto_atTop_add_const_right _ (-(archSlack * zeroMass 1)) tendsto_zeroMass_atTop)
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with δ hδ
  have h := masslessZeroWave_imag_re_ge (y := 1 - δ) (by linarith [hδ.2]) (by linarith [hδ.1])
  rw [sub_sub_cancel] at h
  linarith

/-- A uniform lower bound for `Re Φ₀` on the imaginary segment `[0, i)`. -/
def archFloor : ℝ := archSlack * zeroMass 1 + sechConst * zeroMass (1 / 2)

theorem archFloor_nonneg : 0 ≤ archFloor := by
  have := sechConst_pos
  have hsl : 0 ≤ archSlack := by unfold archSlack; positivity
  unfold archFloor
  exact add_nonneg (mul_nonneg hsl (zeroMass_nonneg 1))
    (mul_nonneg this.le (zeroMass_nonneg _))

theorem neg_archFloor_le_masslessZeroWave_imag_re {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    -archFloor ≤ (masslessZeroWave (y * I)).re := by
  have hm1 := zeroMass_nonneg 1
  have hm2 := zeroMass_nonneg (1 / 2)
  have hc := sechConst_pos
  have hsl : 0 ≤ archSlack := by unfold archSlack; positivity
  rcases le_or_gt (1 / 2) y with hy | hy
  · have h1 := masslessZeroWave_imag_re_ge hy hy1
    have h2 := zeroMass_nonneg (1 - y)
    unfold archFloor
    nlinarith
  · have hnorm : ‖masslessZeroWave (y * I)‖ ≤ sechConst * zeroMass (1 / 2) := by
      have hs := summable_mult_mul_exp_neg_abs_re (ε := 1 / 2) (by norm_num)
      unfold masslessZeroWave zeroMass
      have h := tsum_of_norm_bounded (hs.mul_left sechConst).hasSum fun ρ => by
        have hb := norm_masslessTerm_le (z := (y : ℂ) * I) (η := 1 / 2) (R := 0)
          (by rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
                Complex.I_im, mul_one, zero_mul, add_zero, abs_of_nonneg hy0]; exact hy.le)
          (by rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
                Complex.I_im]; norm_num) ρ
        calc _ ≤ _ := hb
          _ = _ := by norm_num
      rwa [tsum_mul_left] at h
    have h1 := Complex.abs_re_le_norm (masslessZeroWave (y * I))
    have h2 := neg_abs_le (masslessZeroWave (y * I)).re
    unfold archFloor
    nlinarith

/-! ## Divergence of the causal wave at `i` -/

/-- On the imaginary axis the light-cone tail only lowers `Re Φ` by a bounded amount, because the
Bessel kernel is positive there: `Re Φ(iy) ≥ Re Φ₀(iy) − e^{1/2} · archFloor`. -/
theorem kgZeroWave_imag_re_ge {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    (masslessZeroWave (y * I)).re - Real.exp (1 / 2) * archFloor ≤ (kgZeroWave (y * I)).re := by
  set z : ℂ := (y : ℂ) * I with hz
  have hzim : z.im = y := by
    rw [hz, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
  have hzs : |z.im| < 1 := by rw [hzim, abs_lt]; constructor <;> linarith
  have hz2 : z ^ 2 = ((-(y ^ 2) : ℝ) : ℂ) := by
    rw [hz]; push_cast; linear_combination (y : ℂ) ^ 2 * I_sq
  have hB : ∀ t : ℝ, lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) =
      (lightConeBesselReal (-(2 * y ^ 2 * (1 - t ^ 2))) : ℂ) := fun t => by
    rw [ofReal_lightConeBesselReal, hz2]; congr 1; push_cast; ring
  have hzt : ∀ t : ℝ, z * t = ((y * t : ℝ) : ℂ) * I := fun t => by rw [hz]; push_cast; ring
  have hstrip : ∀ t ∈ Icc (0 : ℝ) 1, z * t ∈ causalTimeStrip := by
    intro t ht
    show |(z * t).im| < 1
    rw [hzt, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, zero_mul, add_zero, abs_lt]
    constructor <;> nlinarith [ht.1, ht.2]
  have hcB : Continuous fun t : ℝ => lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) :=
    differentiable_lightConeBessel.continuous.comp (by fun_prop)
  have hcΦ : ContinuousOn (fun t : ℝ => masslessZeroWave (z * t)) (Icc 0 1) := fun t ht =>
    (ContinuousAt.comp (f := fun t : ℝ => z * t) (g := masslessZeroWave)
      ((differentiableOn_masslessZeroWave.differentiableAt
        (isOpen_causalTimeStrip.mem_nhds (hstrip t ht))).continuousAt)
      (continuous_const.mul continuous_ofReal).continuousAt).continuousWithinAt
  have hII : IntervalIntegrable (fun t : ℝ => lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) *
      masslessZeroWave (z * t)) volume 0 1 :=
    ContinuousOn.intervalIntegrable (by rw [uIcc_of_le zero_le_one]; exact hcB.continuousOn.mul hcΦ)
  have hre_int : (∫ t in (0 : ℝ)..1, lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) *
      masslessZeroWave (z * t)).re = ∫ t in (0 : ℝ)..1,
        lightConeBesselReal (-(2 * y ^ 2 * (1 - t ^ 2))) * (masslessZeroWave (z * t)).re := by
    rw [← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hII]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [Complex.reCLM_apply]
    rw [hB t, Complex.re_ofReal_mul]
  have hA := archFloor_nonneg
  have hlow : -(Real.exp (1 / 2) * archFloor) ≤ ∫ t in (0 : ℝ)..1,
      lightConeBesselReal (-(2 * y ^ 2 * (1 - t ^ 2))) * (masslessZeroWave (z * t)).re := by
    have hcr : ContinuousOn (fun t : ℝ => lightConeBesselReal (-(2 * y ^ 2 * (1 - t ^ 2))) *
        (masslessZeroWave (z * t)).re) (Icc 0 1) :=
      (continuous_lightConeBesselReal.comp (by fun_prop)).continuousOn.mul
        (Complex.continuous_re.comp_continuousOn hcΦ)
    have hmono := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
      (intervalIntegrable_const (c := -(Real.exp (1 / 2) * archFloor)))
      (ContinuousOn.intervalIntegrable (by rw [uIcc_of_le zero_le_one]; exact hcr))
      fun t ht => by
        have h1t : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
        have hx : -(2 * y ^ 2 * (1 - t ^ 2)) ≤ 0 := by
          have := mul_nonneg (sq_nonneg y) h1t; linarith
        have hB0 := lightConeBesselReal_nonneg hx
        have hB1 : lightConeBesselReal (-(2 * y ^ 2 * (1 - t ^ 2))) ≤ Real.exp (1 / 2) := by
          refine (le_abs_self _).trans ((abs_lightConeBesselReal_le _).trans
            (Real.exp_le_exp.mpr ?_))
          rw [abs_of_nonpos hx]
          nlinarith [ht.1, ht.2, sq_nonneg y, sq_nonneg t]
        have hΦ := neg_archFloor_le_masslessZeroWave_imag_re (y := y * t)
          (mul_nonneg hy0 ht.1) (by nlinarith [ht.1, ht.2])
        rw [← hzt] at hΦ
        nlinarith [mul_le_mul_of_nonneg_left hΦ hB0, mul_le_mul_of_nonneg_right hB1 hA]
    simpa using hmono
  have hmain : kgZeroWave z = masslessZeroWave z - z ^ 2 * (∫ t in (0 : ℝ)..1,
      lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) * masslessZeroWave (z * t)) := by
    rw [kgZeroWave_eq_lightConeTransmuteC hzs, lightConeTransmuteC]
  have hout : ∀ J : ℂ, (z ^ 2 * J).re = -(y ^ 2) * J.re := fun J => by
    rw [hz2, Complex.re_ofReal_mul]
  rw [hmain, Complex.sub_re, hout, hre_int]
  have hy2 : y ^ 2 ≤ 1 := by nlinarith
  have k1 := mul_le_mul_of_nonneg_left hlow (sq_nonneg y)
  have k2 := mul_nonneg (sub_nonneg.mpr hy2) (mul_nonneg (Real.exp_pos (1 / 2)).le hA)
  nlinarith [k1, k2]

/-- **The archimedean singularity of the causal wave.**  `Re Φ((1 − δ) i) → +∞` as `δ → 0⁺`. -/
theorem tendsto_kgZeroWave_imag_re :
    Tendsto (fun δ : ℝ => (kgZeroWave ((1 - δ : ℝ) * I)).re) (𝓝[>] 0) atTop := by
  refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _
    (-(Real.exp (1 / 2) * archFloor)) tendsto_masslessZeroWave_imag_re)
  filter_upwards [Ioo_mem_nhdsGT one_pos] with δ hδ
  have := kgZeroWave_imag_re_ge (y := 1 - δ) (by linarith [hδ.2]) (by linarith [hδ.1])
  linarith

/-! ## Boundary singularities obstruct every continuous extension -/

/-- The vertical approach `q − ε Im(q) i` to a boundary point from inside the strip. -/
theorem tendsto_boundary_approach {q : ℂ} :
    Tendsto (fun ε : ℝ => q - ε * (q.im * I)) (𝓝[>] 0) (𝓝 q) := by
  have hc : Continuous (fun ε : ℝ => q - ε * (q.im * I)) :=
    continuous_const.sub (continuous_ofReal.mul continuous_const)
  have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simpa only [Complex.ofReal_zero, zero_mul, sub_zero] using h

theorem eventually_boundary_approach {Φ G : ℂ → ℂ} {q : ℂ} (hq : |q.im| = 1)
    (hG : ∀ᶠ z in 𝓝 q, |z.im| < 1 → G z = Φ z) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, G (q - ε * (q.im * I)) = Φ (q - ε * (q.im * I)) := by
  filter_upwards [tendsto_boundary_approach.eventually hG, Ioo_mem_nhdsGT zero_lt_one]
    with ε h1 h2
  refine h1 ?_
  have him : (q - (ε : ℂ) * ((q.im : ℂ) * I)).im = q.im * (1 - ε) := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  rw [him, abs_mul, hq, one_mul, abs_of_pos (by linarith [h2.2])]
  linarith [h2.1]

/-- A wave with a nonzero scaled limit `c(ε) Φ → L`, `c(ε) → 0`, along the vertical approach has no
continuous extension to the boundary point. -/
theorem not_continuousAt_of_scaled_limit {Φ G : ℂ → ℂ} {q : ℂ} (hq : |q.im| = 1)
    (hG : ∀ᶠ z in 𝓝 q, |z.im| < 1 → G z = Φ z) {c : ℝ → ℂ} (hc : Tendsto c (𝓝[>] 0) (𝓝 0))
    {L : ℂ} (hL : L ≠ 0)
    (h : Tendsto (fun ε : ℝ => c ε * Φ (q - ε * (q.im * I))) (𝓝[>] 0) (𝓝 L)) :
    ¬ ContinuousAt G q := by
  intro hcont
  have h1 := hc.mul (hcont.tendsto.comp tendsto_boundary_approach)
  rw [zero_mul] at h1
  refine hL (tendsto_nhds_unique (h.congr' ?_) h1)
  filter_upwards [eventually_boundary_approach hq hG] with ε hε
  simp only [Function.comp_apply, hε]

/-- A wave whose real part tends to `+∞` along the vertical approach has no continuous extension
to the boundary point. -/
theorem not_continuousAt_of_re_atTop {Φ G : ℂ → ℂ} {q : ℂ} (hq : |q.im| = 1)
    (hG : ∀ᶠ z in 𝓝 q, |z.im| < 1 → G z = Φ z)
    (h : Tendsto (fun ε : ℝ => (Φ (q - ε * (q.im * I))).re) (𝓝[>] 0) atTop) :
    ¬ ContinuousAt G q := by
  intro hcont
  have h1 := (Complex.continuous_re.tendsto _).comp (hcont.tendsto.comp tendsto_boundary_approach)
  refine (h1.congr' ?_).not_tendsto (disjoint_nhds_atTop _) h
  filter_upwards [eventually_boundary_approach hq hG] with ε hε
  simp only [Function.comp_apply, hε]

/-- On the imaginary axis the vertical approach to `±i` is `±(1 − ε) i`. -/
theorem boundary_approach_imag {q : ℂ} (h0 : q.re = 0) (hq : |q.im| = 1) {Φ : ℂ → ℂ}
    (hΦ : ∀ z, Φ (-z) = Φ z) (ε : ℝ) :
    Φ (q - ε * (q.im * I)) = Φ ((1 - ε : ℝ) * I) := by
  rcases (abs_eq zero_le_one).mp hq with h | h
  · congr 1
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, h0, h]
      ring
    · simp only [Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, h]
      ring
  · rw [← hΦ]
    congr 1
    apply Complex.ext
    · simp only [Complex.neg_re, Complex.sub_re, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, h0, h]
      ring
    · simp only [Complex.neg_im, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, h]
      ring

theorem ne_of_boundary_approach {q : ℂ} (hq : |q.im| = 1) {ε : ℝ} (hε : 0 < ε) :
    q - ε * (q.im * I) ≠ q := by
  have hqi : (q.im : ℂ) ≠ 0 := ofReal_ne_zero.mpr fun h0 => by rw [h0, abs_zero] at hq; norm_num at hq
  exact fun h => mul_ne_zero (ofReal_ne_zero.mpr hε.ne') (mul_ne_zero hqi I_ne_zero)
    (sub_eq_self.mp h)

/-- A boundary point with `|Re v| = x` is one of `±x ± i`. -/
theorem prime_point_cases {x : ℝ} (hx : 0 ≤ x) {v : ℂ} (hre : |v.re| = x) (him : |v.im| = 1) :
    (v = (x : ℂ) + I ∧ v.im = 1) ∨ (v = (x : ℂ) - I ∧ v.im = -1) ∨
      (v = -(x : ℂ) + I ∧ v.im = 1) ∨ (v = -(x : ℂ) - I ∧ v.im = -1) := by
  rcases (abs_eq hx).mp hre with hr | hr <;> rcases (abs_eq zero_le_one).mp him with hi | hi
  · exact Or.inl ⟨Complex.ext
      (by rw [Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero, hr])
      (by rw [Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add, hi]), hi⟩
  · exact Or.inr (Or.inl ⟨Complex.ext
      (by rw [Complex.sub_re, Complex.ofReal_re, Complex.I_re, sub_zero, hr])
      (by rw [Complex.sub_im, Complex.ofReal_im, Complex.I_im, zero_sub, hi]), hi⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨Complex.ext
      (by rw [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.I_re, add_zero, hr])
      (by rw [Complex.add_im, Complex.neg_im, Complex.ofReal_im, neg_zero, Complex.I_im, zero_add,
        hi]), hi⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨Complex.ext
      (by rw [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.I_re, sub_zero, hr])
      (by rw [Complex.sub_im, Complex.neg_im, Complex.ofReal_im, neg_zero, Complex.I_im, zero_sub,
        hi]), hi⟩))

/-- The four boundary points `±log n ± i` (`Λ(n) ≠ 0`) of the massless wave carry nonzero residues. -/
theorem exists_residue_masslessBoundaryWave {n : ℕ} (hw : chmdPrimeWeight n ≠ 0) {v : ℂ}
    (hre : |v.re| = Real.log n) (him : |v.im| = 1) :
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (fun z => (z - v) * masslessBoundaryWave z) (𝓝[≠] v) (𝓝 L) := by
  have hR0 : (2 * I / π * chmdPrimeWeight n : ℂ) ≠ 0 :=
    mul_ne_zero (div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero)
      (ofReal_ne_zero.mpr Real.pi_ne_zero)) (ofReal_ne_zero.mpr hw)
  have hlog : 0 ≤ Real.log n :=
    (half_lt_log_of_two_le (two_le_of_chmdPrimeWeight_ne_zero hw)).le.trans' (by norm_num)
  obtain ⟨h1, h2, h3, h4⟩ := tendsto_masslessBoundaryWave_residue hw
  rcases prime_point_cases hlog hre him with ⟨hv, -⟩ | ⟨hv, -⟩ | ⟨hv, -⟩ | ⟨hv, -⟩ <;> rw [hv]
  · exact ⟨_, hR0, h1⟩
  · exact ⟨_, neg_ne_zero.mpr hR0, h2⟩
  · exact ⟨_, hR0, h3⟩
  · exact ⟨_, neg_ne_zero.mpr hR0, h4⟩

/-- At a prime point the massless wave has no continuous extension (it has a pole). -/
theorem not_continuousAt_masslessZeroWave_prime {n : ℕ} (hw : chmdPrimeWeight n ≠ 0) {v : ℂ}
    (hre : |v.re| = Real.log n) (him : |v.im| = 1) {G : ℂ → ℂ}
    (hG : ∀ᶠ z in 𝓝 v, |z.im| < 1 → G z = masslessZeroWave z) : ¬ ContinuousAt G v := by
  obtain ⟨L, hL, hlim⟩ := exists_residue_masslessBoundaryWave hw hre him
  have hf : Tendsto (fun ε : ℝ => v - ε * (v.im * I)) (𝓝[>] 0) (𝓝[≠] v) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_boundary_approach, by
      filter_upwards [self_mem_nhdsWithin] with ε hε using ne_of_boundary_approach him hε⟩
  have hc : Tendsto (fun ε : ℝ => v - ε * (v.im * I) - v) (𝓝[>] 0) (𝓝 0) := by
    simpa only [sub_self] using (tendsto_boundary_approach (q := v)).sub_const v
  refine not_continuousAt_of_scaled_limit him hG hc hL ((hlim.comp hf).congr' ?_)
  filter_upwards [eventually_boundary_approach him
    (Eventually.of_forall fun z hz => masslessBoundaryWave_of_strip hz)] with ε hε
  simp only [Function.comp_apply, hε]

/-- At a prime point the causal wave has no continuous extension: `ε Φ → −(2/π)Λ(n)/√n ≠ 0`. -/
theorem not_continuousAt_kgZeroWave_prime {n : ℕ} (hw : chmdPrimeWeight n ≠ 0) {v : ℂ}
    (hre : |v.re| = Real.log n) (him : |v.im| = 1) {G : ℂ → ℂ}
    (hG : ∀ᶠ z in 𝓝 v, |z.im| < 1 → G z = kgZeroWave z) : ¬ ContinuousAt G v := by
  have hL : (-2 / π * chmdPrimeWeight n : ℂ) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero))
      (ofReal_ne_zero.mpr hw)
  have hc : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have h := (continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa only [Complex.ofReal_zero] using h
  have hlog : 0 ≤ Real.log n :=
    (half_lt_log_of_two_le (two_le_of_chmdPrimeWeight_ne_zero hw)).le.trans' (by norm_num)
  obtain ⟨h1, h2, h3, h4⟩ := tendsto_kgZeroWave_boundary_four hw
  refine not_continuousAt_of_scaled_limit him hG hc hL ?_
  rcases prime_point_cases hlog hre him with ⟨hv, hi⟩ | ⟨hv, hi⟩ | ⟨hv, hi⟩ | ⟨hv, hi⟩
  · refine h1.congr fun ε => ?_
    rw [hi, hv]; congr 2; push_cast; ring
  · refine h2.congr fun ε => ?_
    rw [hi, hv]; congr 2; push_cast; ring
  · refine h3.congr fun ε => ?_
    rw [hi, hv]; congr 2; push_cast; ring
  · refine h4.congr fun ε => ?_
    rw [hi, hv]; congr 2; push_cast; ring

/-! ## The exact boundary singular set -/

/-- A point `v` of the boundary lines `|Im v| = 1` is a regular point of the massless wave — some
function analytic (equivalently: continuous) at `v` agrees with `Φ₀` inside the strip — exactly when
`Re v ≠ 0` and `v` is not a prime point `±log n ± i`. -/
theorem masslessZeroWave_boundary_regular_iff {v : ℂ} (hv : |v.im| = 1) :
    ((∃ G : ℂ → ℂ, AnalyticAt ℂ G v ∧ ∀ᶠ z in 𝓝 v, |z.im| < 1 → G z = masslessZeroWave z) ↔
      v.re ≠ 0 ∧ AvoidsPrimePoints v) ∧
    ((∃ G : ℂ → ℂ, ContinuousAt G v ∧ ∀ᶠ z in 𝓝 v, |z.im| < 1 → G z = masslessZeroWave z) ↔
      v.re ≠ 0 ∧ AvoidsPrimePoints v) := by
  have hreg : v.re ≠ 0 ∧ AvoidsPrimePoints v → ∃ G : ℂ → ℂ, AnalyticAt ℂ G v ∧
      ∀ᶠ z in 𝓝 v, |z.im| < 1 → G z = masslessZeroWave z := fun h =>
    ⟨masslessBoundaryWave, analyticAt_masslessBoundaryWave (Or.inr ⟨by rw [hv]; norm_num, h.1, h.2⟩),
      Eventually.of_forall fun z hz => masslessBoundaryWave_of_strip hz⟩
  have hsing : (∃ G : ℂ → ℂ, ContinuousAt G v ∧
      ∀ᶠ z in 𝓝 v, |z.im| < 1 → G z = masslessZeroWave z) → v.re ≠ 0 ∧ AvoidsPrimePoints v := by
    rintro ⟨G, hG, hagree⟩
    refine ⟨fun h0 => not_continuousAt_of_re_atTop hv hagree ?_ hG, fun n hw => ?_⟩
    · exact tendsto_masslessZeroWave_imag_re.congr fun ε => by
        rw [boundary_approach_imag h0 hv masslessZeroWave_neg]
    · by_contra hcon
      push Not at hcon
      exact not_continuousAt_masslessZeroWave_prime hw hcon.1 hv hagree hG
  exact ⟨⟨fun ⟨G, hG, h⟩ => hsing ⟨G, hG.continuousAt, h⟩, hreg⟩,
    ⟨hsing, fun h => let ⟨G, hG, h'⟩ := hreg h; ⟨G, hG.continuousAt, h'⟩⟩⟩

/-- The same characterisation for the Klein–Gordon causal wave. -/
theorem kgZeroWave_boundary_regular_iff {v : ℂ} (hv : |v.im| = 1) :
    ((∃ G : ℂ → ℂ, AnalyticAt ℂ G v ∧ ∀ᶠ z in 𝓝 v, |z.im| < 1 → G z = kgZeroWave z) ↔
      v.re ≠ 0 ∧ AvoidsPrimePoints v) ∧
    ((∃ G : ℂ → ℂ, ContinuousAt G v ∧ ∀ᶠ z in 𝓝 v, |z.im| < 1 → G z = kgZeroWave z) ↔
      v.re ≠ 0 ∧ AvoidsPrimePoints v) := by
  have hreg : v.re ≠ 0 ∧ AvoidsPrimePoints v → ∃ G : ℂ → ℂ, AnalyticAt ℂ G v ∧
      ∀ᶠ z in 𝓝 v, |z.im| < 1 → G z = kgZeroWave z := by
    intro h
    have ha := analyticAt_kgBoundaryWave_boundary h.1 hv (by rw [Complex.re_add_im]; exact h.2)
    rw [Complex.re_add_im] at ha
    exact ⟨kgBoundaryWave, ha, Eventually.of_forall fun z hz => (kgZeroWave_eq_kgBoundaryWave hz).symm⟩
  have hsing : (∃ G : ℂ → ℂ, ContinuousAt G v ∧
      ∀ᶠ z in 𝓝 v, |z.im| < 1 → G z = kgZeroWave z) → v.re ≠ 0 ∧ AvoidsPrimePoints v := by
    rintro ⟨G, hG, hagree⟩
    refine ⟨fun h0 => not_continuousAt_of_re_atTop hv hagree ?_ hG, fun n hw => ?_⟩
    · exact tendsto_kgZeroWave_imag_re.congr fun ε => by
        rw [boundary_approach_imag h0 hv kgZeroWave_neg]
    · by_contra hcon
      push Not at hcon
      exact not_continuousAt_kgZeroWave_prime hw hcon.1 hv hagree hG
  exact ⟨⟨fun ⟨G, hG, h⟩ => hsing ⟨G, hG.continuousAt, h⟩, hreg⟩,
    ⟨hsing, fun h => let ⟨G, hG, h'⟩ := hreg h; ⟨G, hG.continuousAt, h'⟩⟩⟩

theorem boundary_singular_set_of_iff {P : ℂ → Prop}
    (h : ∀ v : ℂ, |v.im| = 1 → (P v ↔ v.re ≠ 0 ∧ AvoidsPrimePoints v)) :
    {v : ℂ | |v.im| = 1 ∧ ¬ P v} =
      {v : ℂ | |v.im| = 1 ∧ ∃ n : ℕ, (n = 1 ∨ chmdPrimeWeight n ≠ 0) ∧ |v.re| = Real.log n} := by
  ext v
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hv, hP⟩
    refine ⟨hv, ?_⟩
    rw [h v hv, not_and_or, not_not] at hP
    rcases hP with h0 | hav
    · exact ⟨1, Or.inl rfl, by rw [h0, abs_zero, Nat.cast_one, Real.log_one]⟩
    · unfold AvoidsPrimePoints at hav
      push Not at hav
      obtain ⟨n, hw, hre, -⟩ := hav
      exact ⟨n, Or.inr hw, hre⟩
  · rintro ⟨hv, n, hn, hre⟩
    refine ⟨hv, fun hP => ?_⟩
    obtain ⟨h0, hav⟩ := (h v hv).mp hP
    rcases hn with rfl | hw
    · rw [Nat.cast_one, Real.log_one, abs_eq_zero] at hre
      exact h0 hre
    · rcases hav n hw with h1 | h1
      · exact h1 hre
      · exact h1 hv

/-- **Cramér's boundary theorem for the massless wave.**  On the boundary lines `|Im v| = 1` of the
time strip, the points where `Φ₀` has no continuous extension are exactly `±log n ± i` with `n = 1`
(the archimedean point) or `Λ(n) ≠ 0` (the prime powers); everywhere else on these lines `Φ₀`
continues analytically. -/
theorem masslessZeroWave_boundary_singular_set :
    {v : ℂ | |v.im| = 1 ∧ ¬ ∃ G : ℂ → ℂ, ContinuousAt G v ∧
        ∀ᶠ z in 𝓝 v, |z.im| < 1 → G z = masslessZeroWave z} =
      {v : ℂ | |v.im| = 1 ∧ ∃ n : ℕ, (n = 1 ∨ chmdPrimeWeight n ≠ 0) ∧ |v.re| = Real.log n} :=
  boundary_singular_set_of_iff fun _ hv => (masslessZeroWave_boundary_regular_iff hv).2

/-- **Cramér's boundary theorem for the Klein–Gordon causal wave.**  The boundary singular set of
the causal wave is the same: `±log n ± i` with `n = 1` or `Λ(n) ≠ 0`. -/
theorem kgZeroWave_boundary_singular_set :
    {v : ℂ | |v.im| = 1 ∧ ¬ ∃ G : ℂ → ℂ, ContinuousAt G v ∧
        ∀ᶠ z in 𝓝 v, |z.im| < 1 → G z = kgZeroWave z} =
      {v : ℂ | |v.im| = 1 ∧ ∃ n : ℕ, (n = 1 ∨ chmdPrimeWeight n ≠ 0) ∧ |v.re| = Real.log n} :=
  boundary_singular_set_of_iff fun _ hv => (kgZeroWave_boundary_regular_iff hv).2

end RHTower.CHMDLightCone
