import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.RealProbeNodesDecideTheRiemannHypothesis
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheZeroSumOfAProfileConvergesAfterOneSubtraction
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeDefectCountsTheRightZeros
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ZeroDensityFilteredWeilPositivityAndCoercivity
import GaloisForLFunctions.RHTower.XiLocalZeroDensity
import GaloisForLFunctions.RHTower.EvenLandauPairTest

/-!
# The real probe kernel is a Krein form on the zeros

On real nodes `p, q ≥ 1` Weil's bare form on the probes is
`K(p, q) = (D(p) + D(q))/(p + q)`, `D = (log ξ)'(½ + ·)` (`bareMixedEnergy_probe`). The symmetrised
partial fractions of `ξ'/ξ` turn it into a sum over the centred zeros `z = ρ − ½`:

* **Zero-side form** (`bareMixedEnergy_probe_eq_tsum_carrier`).
  `K(p, q) = Σ_ρ m_ρ /((p − z_ρ)(q + z_ρ))`, absolutely convergent.
* **Krein form** (`bareMixedEnergy_probe_eq_inner`). With the coordinates
  `v_p(ρ) = √m_ρ/(p − z_ρ)` in `ℓ²` of the distinct zeros and the reflection `ρ ↦ 1 − ρ̄`,
  `K(p, q) = ⟨R v_q, v_p⟩`: the probe kernel is the Krein form of the zero configuration whose
  negative squares on compactly supported tests count the zeros right of the line.
* **Upper bound** (`hermNegIndex_probeGram_le`). Every real Pick matrix `(K(p_i, p_j))` with nodes
  `p_i ≥ 1` has at most as many negative squares as `ζ` has zeros right of the line: on the joint
  kernel of the evaluations at those zeros the form is `Σ_{on-line} |Σ_i x̄_i v_{p_i}(ρ)|² ≥ 0`.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped ComplexConjugate lp

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry Zeta23
  _root_.RHTower

/-! ### The probe kernel as a sum over the zero copies -/

theorem logDeriv_xiCent_eq_logDeriv_xi (W : ℂ) :
    logDeriv xiCent W = logDeriv xi (1 / 2 + W) := by
  rw [logDeriv_apply, logDeriv_apply]
  show deriv (fun W => xi (1 / 2 + W)) W / xi (1 / 2 + W) = _
  rw [deriv_comp_const_add]

/-- At a centred zero `|p − z|, |q + z| ≥ |Im z|` and `(Im z)² ≥ ¾|z|²`. -/
theorem norm_sub_mul_add_centredZero_ge (p q : ℝ) (c : XiZeroCopy) :
    (3 / 4) * ‖centredZero c‖ ^ 2 ≤
      ‖(p : ℂ) - centredZero c‖ * ‖(q : ℂ) + centredZero c‖ := by
  set z := centredZero c
  have hre := abs_re_centredZero_lt c
  have hz1 := one_lt_norm_centredZero c
  have h1 : |z.im| ≤ ‖(p : ℂ) - z‖ := by
    have := Complex.abs_im_le_norm ((p : ℂ) - z)
    rwa [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at this
  have h2 : |z.im| ≤ ‖(q : ℂ) + z‖ := by
    have := Complex.abs_im_le_norm ((q : ℂ) + z)
    rwa [Complex.add_im, Complex.ofReal_im, zero_add] at this
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hre2 : z.re ^ 2 ≤ 1 / 4 := by nlinarith [abs_lt.mp hre, sq_abs z.re]
  have hprod : |z.im| * |z.im| ≤ ‖(p : ℂ) - z‖ * ‖(q : ℂ) + z‖ :=
    mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
  rw [← sq, sq_abs] at hprod
  nlinarith

theorem im_centredZero_ne_zero (c : XiZeroCopy) : (centredZero c).im ≠ 0 := by
  intro h
  have hre := abs_re_centredZero_lt c
  have hz1 := one_lt_norm_centredZero c
  have hn : ‖centredZero c‖ ^ 2 = (centredZero c).re ^ 2 + (centredZero c).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [h] at hn
  nlinarith [abs_lt.mp hre, sq_abs (centredZero c).re]

theorem ofReal_sub_centredZero_ne_zero (p : ℝ) (c : XiZeroCopy) : (p : ℂ) - centredZero c ≠ 0 :=
  fun h => im_centredZero_ne_zero c (by
    have := congrArg Complex.im h
    simpa using this)

theorem ofReal_add_centredZero_ne_zero (p : ℝ) (c : XiZeroCopy) : (p : ℂ) + centredZero c ≠ 0 :=
  fun h => im_centredZero_ne_zero c (by
    have := congrArg Complex.im h
    simpa using this)

/-- `‖((p − z)(q + z))⁻¹‖ ≤ (4/3)|z|⁻²` at the centred zeros. -/
theorem norm_inv_sub_mul_add_le (p q : ℝ) (c : XiZeroCopy) :
    ‖(((p : ℂ) - centredZero c) * ((q : ℂ) + centredZero c))⁻¹‖ ≤
      4 / 3 * ‖centredZero c‖⁻¹ ^ 2 := by
  have hb := norm_sub_mul_add_centredZero_ge p q c
  have hz : 0 < ‖centredZero c‖ := norm_pos_iff.mpr (centredZero_ne_zero c)
  have hpos : 0 < ‖(p : ℂ) - centredZero c‖ * ‖(q : ℂ) + centredZero c‖ :=
    lt_of_lt_of_le (by positivity) hb
  rw [norm_inv, norm_mul, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity),
    inv_mul_le_iff₀ hpos]
  linarith

theorem summable_inv_sub_mul_add (p q : ℝ) :
    Summable fun c : XiZeroCopy =>
      (((p : ℂ) - centredZero c) * ((q : ℂ) + centredZero c))⁻¹ :=
  Summable.of_norm_bounded (summable_inv_sq_centredZero.mul_left (4 / 3))
    (norm_inv_sub_mul_add_le p q)

/-- The paired partial fractions `(p − z)⁻¹ + (p + z)⁻¹ = 2p/((p − z)(p + z))` are summable. -/
theorem summable_pairInv (p : ℝ) :
    Summable fun c : XiZeroCopy => ((p : ℂ) - centredZero c)⁻¹ + ((p : ℂ) + centredZero c)⁻¹ := by
  refine ((summable_inv_sub_mul_add p p).mul_left (2 * (p : ℂ))).congr fun c => ?_
  have h1 := ofReal_sub_centredZero_ne_zero p c
  have h2 := ofReal_add_centredZero_ne_zero p c
  field_simp
  ring

/-- The centred logarithmic derivative of `ξ` at a real point as a paired sum over the copies. -/
theorem two_mul_logDeriv_xiCent_eq_tsum {p : ℝ} (hp : 1 / 2 < p) :
    2 * logDeriv xiCent (p : ℂ) =
      ∑' c : XiZeroCopy, (((p : ℂ) - centredZero c)⁻¹ + ((p : ℂ) + centredZero c)⁻¹) := by
  have hxi : xi (1 / 2 + (p : ℂ)) ≠ 0 := xiCent_ne_zero_of_half_lt_re (by simpa using hp)
  rw [logDeriv_xiCent_eq_logDeriv_xi, two_logDeriv_xi_eq_pair_tsum hxi]
  refine tsum_congr fun c => ?_
  unfold centredZero
  congr 1 <;> congr 1 <;> ring

/-- **The probe kernel over the copies**: `2K(p,q) = Σ_c [1/((p−z)(q+z)) + 1/((p+z)(q−z))]`. -/
theorem two_mul_bareMixedEnergy_probe_eq_tsum {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    2 * (bareMixedEnergy (probe p) (probe q) : ℂ) = ∑' c : XiZeroCopy,
      ((((p : ℂ) - centredZero c) * ((q : ℂ) + centredZero c))⁻¹ +
        (((p : ℂ) + centredZero c) * ((q : ℂ) - centredZero c))⁻¹) := by
  have hp' : (1 / 2 : ℝ) < p := by linarith
  have hq' : (1 / 2 : ℝ) < q := by linarith
  have hDq : conj (logDeriv xiCent (q : ℂ)) = logDeriv xiCent (q : ℂ) := by
    rw [logDeriv_xiCent_ofReal_eq_re hq', Complex.conj_ofReal]
  have hpq : (p : ℂ) + q ≠ 0 := by
    rw [← Complex.ofReal_add]; exact Complex.ofReal_ne_zero.mpr (by linarith)
  rw [bareMixedEnergy_probe_eq_criticalLogDerivKernel hp' hq', criticalLogDerivKernel,
    Complex.conj_ofReal, hDq, mul_div_assoc', mul_add, two_mul_logDeriv_xiCent_eq_tsum hp',
    two_mul_logDeriv_xiCent_eq_tsum hq', ← (summable_pairInv p).tsum_add (summable_pairInv q),
    ← tsum_div_const]
  refine tsum_congr fun c => ?_
  have h1 := ofReal_sub_centredZero_ne_zero p c
  have h2 := ofReal_add_centredZero_ne_zero p c
  have h3 := ofReal_sub_centredZero_ne_zero q c
  have h4 := ofReal_add_centredZero_ne_zero q c
  field_simp
  ring

/-! ### The carrier form -/

theorem normSq_gammaOf_eq (ρ : ℂ) : Complex.normSq (gammaOf ρ) = Complex.normSq (ρ - 1 / 2) := by
  rw [ArithmeticCastelnuovoSeveri.gammaOf_eq, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.one_re, Complex.one_im, zero_div, zero_mul, one_mul, mul_zero, sub_zero, zero_sub]
  ring

theorem abs_re_carrier_sub_half (τ : zetaZeroConfig.carrier) : |((τ : ℂ) - 1 / 2).re| ≤ 1 / 2 := by
  have h := zetaZeroConfig.strip _ τ.2
  have hh : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  rw [Complex.sub_re, hh, abs_le]
  constructor <;> linarith [h.1, h.2]

/-- For real `p ≥ 1` and `|Re z| ≤ ½`: `1 + |z|² ≤ 5|p − z|²` and `1 + |z|² ≤ 5|p + z|²`. -/
theorem one_add_normSq_le_five_mul {p : ℝ} (hp : 1 ≤ p) {z : ℂ} (hz : |z.re| ≤ 1 / 2) :
    1 + Complex.normSq z ≤ 5 * Complex.normSq ((p : ℂ) - z) ∧
      1 + Complex.normSq z ≤ 5 * Complex.normSq ((p : ℂ) + z) := by
  have hz' := abs_le.mp hz
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im]
  constructor
  · nlinarith [mul_self_nonneg (p - z.re - 1 / 2), mul_self_nonneg z.im, hz'.1, hz'.2,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 2 - z.re) (by linarith : (0 : ℝ) ≤ 1 / 2 + z.re)]
  · nlinarith [mul_self_nonneg (p + z.re - 1 / 2), mul_self_nonneg z.im, hz'.1, hz'.2,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 2 - z.re) (by linarith : (0 : ℝ) ≤ 1 / 2 + z.re)]

theorem summable_mult_div_normSq :
    Summable fun τ : zetaZeroConfig.carrier => (zetaZeroConfig.mult τ : ℝ) / (1 + Complex.normSq ((τ : ℂ) - 1 / 2)) :=
  summable_zetaZeroConfig.congr fun τ => by rw [normSq_gammaOf_eq]

/-- `(1 + |z|²)/5 ≤ |p − z| |q + z|` on the carrier, for `p, q ≥ 1`. -/
theorem one_add_normSq_div_five_le {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (τ : zetaZeroConfig.carrier) :
    (1 + Complex.normSq ((τ : ℂ) - 1 / 2)) / 5 ≤
      ‖(p : ℂ) - ((τ : ℂ) - 1 / 2)‖ * ‖(q : ℂ) + ((τ : ℂ) - 1 / 2)‖ := by
  set z := (τ : ℂ) - 1 / 2
  have hp' := (one_add_normSq_le_five_mul hp (abs_re_carrier_sub_half τ)).1
  have hq' := (one_add_normSq_le_five_mul hq (abs_re_carrier_sub_half τ)).2
  have hN : 0 ≤ (1 + Complex.normSq z) / 5 :=
    div_nonneg (by linarith [Complex.normSq_nonneg z]) (by norm_num)
  by_contra h
  push Not at h
  have h0 : 0 ≤ ‖(p : ℂ) - z‖ * ‖(q : ℂ) + z‖ := by positivity
  have hsq := pow_lt_pow_left₀ h h0 two_ne_zero
  rw [mul_pow, Complex.sq_norm, Complex.sq_norm] at hsq
  have ha : (1 + Complex.normSq z) / 5 ≤ Complex.normSq ((p : ℂ) - z) := by linarith
  have hb : (1 + Complex.normSq z) / 5 ≤ Complex.normSq ((q : ℂ) + z) := by linarith
  nlinarith [mul_le_mul ha hb hN (Complex.normSq_nonneg _)]

/-- The carrier term `m/((p − z)(q + z))` is at most `5m/(1 + |z|²)`. -/
theorem norm_mult_div_le {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (τ : zetaZeroConfig.carrier) :
    ‖(zetaZeroConfig.mult τ : ℂ) * ((((p : ℂ) - ((τ : ℂ) - 1 / 2)) * ((q : ℂ) + ((τ : ℂ) - 1 / 2)))⁻¹)‖ ≤
      5 * ((zetaZeroConfig.mult τ : ℝ) / (1 + Complex.normSq ((τ : ℂ) - 1 / 2))) := by
  have h1 := one_add_normSq_div_five_le hp hq τ
  have hN : 0 < (1 + Complex.normSq ((τ : ℂ) - 1 / 2)) / 5 := by
    have := Complex.normSq_nonneg ((τ : ℂ) - 1 / 2)
    positivity
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult τ := Nat.cast_nonneg _
  rw [norm_mul, norm_inv, norm_mul, Complex.norm_natCast]
  calc (zetaZeroConfig.mult τ : ℝ) * (‖(p : ℂ) - ((τ : ℂ) - 1 / 2)‖ * ‖(q : ℂ) + ((τ : ℂ) - 1 / 2)‖)⁻¹
      = (zetaZeroConfig.mult τ : ℝ) / (‖(p : ℂ) - ((τ : ℂ) - 1 / 2)‖ * ‖(q : ℂ) + ((τ : ℂ) - 1 / 2)‖) :=
        (div_eq_mul_inv _ _).symm
    _ ≤ (zetaZeroConfig.mult τ : ℝ) / ((1 + Complex.normSq ((τ : ℂ) - 1 / 2)) / 5) :=
        div_le_div_of_nonneg_left hm hN h1
    _ = 5 * ((zetaZeroConfig.mult τ : ℝ) / (1 + Complex.normSq ((τ : ℂ) - 1 / 2))) := by
        have hN' : 1 + Complex.normSq ((τ : ℂ) - 1 / 2) ≠ 0 := by
          have := Complex.normSq_nonneg ((τ : ℂ) - 1 / 2)
          positivity
        field_simp

theorem summable_mult_div {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Summable fun τ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult τ : ℂ) * ((((p : ℂ) - ((τ : ℂ) - 1 / 2)) * ((q : ℂ) + ((τ : ℂ) - 1 / 2)))⁻¹) :=
  Summable.of_norm_bounded (summable_mult_div_normSq.mul_left 5) (norm_mult_div_le hp hq)

/-- Copy sums of complex functions of the zeros are multiplicity-weighted carrier sums. -/
theorem tsum_copies_eq_carrier {g : ℂ → ℂ} (hg : Summable fun c : XiZeroCopy => g (c.1 : ℂ))
    (hg' : Summable fun τ : zetaZeroConfig.carrier => (zetaZeroConfig.mult τ : ℂ) * g τ) :
    ∑' c : XiZeroCopy, g (c.1 : ℂ) = ∑' τ : zetaZeroConfig.carrier, (zetaZeroConfig.mult τ : ℂ) * g τ := by
  have h1 := tsum_xiZeroCopy_eq_zetaCarrier (g := fun z => (g z).re) (by
    simpa using Complex.reCLM.summable hg)
  have h2 := tsum_xiZeroCopy_eq_zetaCarrier (g := fun z => (g z).im) (by
    simpa using Complex.imCLM.summable hg)
  apply Complex.ext
  · rw [Complex.re_tsum hg, Complex.re_tsum hg', h1]
    refine tsum_congr fun τ => ?_
    simp
  · rw [Complex.im_tsum hg, Complex.im_tsum hg', h2]
    refine tsum_congr fun τ => ?_
    simp

/-- **The probe kernel over the distinct zeros**: `K(p, q) = Σ_ρ m_ρ/((p − z_ρ)(q + z_ρ))`. -/
theorem bareMixedEnergy_probe_eq_tsum_carrier {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    (bareMixedEnergy (probe p) (probe q) : ℂ) = ∑' τ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult τ : ℂ) * ((((p : ℂ) - ((τ : ℂ) - 1 / 2)) * ((q : ℂ) + ((τ : ℂ) - 1 / 2)))⁻¹) := by
  set a : ℂ → ℂ := fun ρ => (((p : ℂ) - (ρ - 1 / 2)) * ((q : ℂ) + (ρ - 1 / 2)))⁻¹ with ha
  set b : ℂ → ℂ := fun ρ => (((p : ℂ) + (ρ - 1 / 2)) * ((q : ℂ) - (ρ - 1 / 2)))⁻¹ with hb
  have hsa : Summable fun τ : zetaZeroConfig.carrier => (zetaZeroConfig.mult τ : ℂ) * a τ := summable_mult_div hp hq
  -- `ρ ↦ 1 − ρ` exchanges the two halves
  have hab : ∀ τ : zetaZeroConfig.carrier, (zetaZeroConfig.mult (zetaCarrierOneSub τ) : ℂ) * b (zetaCarrierOneSub τ) =
      (zetaZeroConfig.mult τ : ℂ) * a τ := by
    intro τ
    have hm : zetaZeroConfig.mult (1 - (τ : ℂ)) = zetaZeroConfig.mult τ := mult_one_sub_zetaZeroConfig τ.2
    show (zetaZeroConfig.mult (1 - (τ : ℂ)) : ℂ) * b (1 - (τ : ℂ)) = _
    simp only [ha, hb]
    rw [hm, show (p : ℂ) + (1 - (τ : ℂ) - 1 / 2) = (p : ℂ) - ((τ : ℂ) - 1 / 2) by ring,
      show (q : ℂ) - (1 - (τ : ℂ) - 1 / 2) = (q : ℂ) + ((τ : ℂ) - 1 / 2) by ring]
  have hsb : Summable fun τ : zetaZeroConfig.carrier => (zetaZeroConfig.mult τ : ℂ) * b τ := by
    rw [← zetaCarrierOneSub.summable_iff]
    exact hsa.congr fun τ => (hab τ).symm
  have hEb : ∑' τ : zetaZeroConfig.carrier, (zetaZeroConfig.mult τ : ℂ) * b τ = ∑' τ : zetaZeroConfig.carrier, (zetaZeroConfig.mult τ : ℂ) * a τ := by
    rw [← zetaCarrierOneSub.tsum_eq]
    exact tsum_congr hab
  have hsa' : Summable fun c : XiZeroCopy => a (c.1 : ℂ) :=
    (summable_inv_sub_mul_add p q).congr fun c => by simp only [ha, centredZero]
  have hsb' : Summable fun c : XiZeroCopy => b (c.1 : ℂ) :=
    (summable_inv_sub_mul_add (-p) (-q)).congr fun c => by
      simp only [hb, centredZero]
      push_cast
      congr 1
      ring
  have hcop : Summable fun c : XiZeroCopy => (a + b) (c.1 : ℂ) :=
    (hsa'.add hsb').congr fun c => (Pi.add_apply a b _).symm
  have h2 := two_mul_bareMixedEnergy_probe_eq_tsum hp hq
  have hcarrier : ∑' c : XiZeroCopy, (a + b) (c.1 : ℂ) =
      ∑' τ : zetaZeroConfig.carrier, (zetaZeroConfig.mult τ : ℂ) * (a + b) τ :=
    tsum_copies_eq_carrier hcop ((hsa.add hsb).congr fun τ => by simp only [Pi.add_apply]; ring)
  have hsplit : ∑' τ : zetaZeroConfig.carrier, (zetaZeroConfig.mult τ : ℂ) * (a + b) τ =
      2 * ∑' τ : zetaZeroConfig.carrier, (zetaZeroConfig.mult τ : ℂ) * a τ := by
    rw [show (fun τ : zetaZeroConfig.carrier => (zetaZeroConfig.mult τ : ℂ) * (a + b) τ) =
      fun τ : zetaZeroConfig.carrier =>
        (zetaZeroConfig.mult τ : ℂ) * a τ + (zetaZeroConfig.mult τ : ℂ) * b τ by
        funext τ; simp only [Pi.add_apply]; ring, hsa.tsum_add hsb, hEb]
    ring
  have hleft : ∑' c : XiZeroCopy,
      ((((p : ℂ) - centredZero c) * ((q : ℂ) + centredZero c))⁻¹ +
        (((p : ℂ) + centredZero c) * ((q : ℂ) - centredZero c))⁻¹) =
      ∑' c : XiZeroCopy, (a + b) (c.1 : ℂ) := by
    refine tsum_congr fun c => ?_
    simp only [Pi.add_apply, ha, hb, centredZero]
  rw [hleft, hcarrier, hsplit] at h2
  exact mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0) h2

/-! ### The Krein form -/

/-- The probe coordinates `v_p(ρ) = √m_ρ/(p − z_ρ)` on the distinct zeros. -/
def probeCoord (p : ℝ) (τ : zetaZeroConfig.carrier) : ℂ :=
  ((Real.sqrt (zetaZeroConfig.mult τ) : ℝ) : ℂ) / ((p : ℂ) - ((τ : ℂ) - 1 / 2))

theorem norm_probeCoord_sq_le {p : ℝ} (hp : 1 ≤ p) (τ : zetaZeroConfig.carrier) :
    ‖probeCoord p τ‖ ^ 2 ≤ 5 * ((zetaZeroConfig.mult τ : ℝ) / (1 + Complex.normSq ((τ : ℂ) - 1 / 2))) := by
  have h := (one_add_normSq_le_five_mul hp (abs_re_carrier_sub_half τ)).1
  have hN : 0 < 1 + Complex.normSq ((τ : ℂ) - 1 / 2) := by
    have := Complex.normSq_nonneg ((τ : ℂ) - 1 / 2)
    linarith
  have hD : 0 < Complex.normSq ((p : ℂ) - ((τ : ℂ) - 1 / 2)) := by linarith
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult τ := Nat.cast_nonneg _
  rw [probeCoord, norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt hm, Complex.sq_norm, div_le_iff₀ hD]
  rw [mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hN]
  nlinarith

theorem memℓp_probeCoord {p : ℝ} (hp : 1 ≤ p) : Memℓp (probeCoord p) 2 := by
  refine (memℓp_gen_iff (by norm_num)).mpr ?_
  refine Summable.of_nonneg_of_le (fun τ => by positivity) (fun τ => ?_)
    (summable_mult_div_normSq.mul_left 5)
  rw [ENNReal.toReal_ofNat, Real.rpow_two]
  exact norm_probeCoord_sq_le hp τ

/-- The probe vector `v_p ∈ ℓ²` of the distinct zeros, `p ≥ 1`. -/
def probeVec {p : ℝ} (hp : 1 ≤ p) : ℓ²(zetaZeroConfig.carrier, ℂ) := ⟨probeCoord p, memℓp_probeCoord hp⟩

theorem probeVec_apply {p : ℝ} (hp : 1 ≤ p) (τ : zetaZeroConfig.carrier) : probeVec hp τ = probeCoord p τ := rfl

/-- Pointwise: `m_ρ/((p − z)(q + z)) = conj v_q(1 − ρ̄) · v_p(ρ)`. -/
theorem mult_div_eq_conj_mul {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (τ : zetaZeroConfig.carrier) :
    (zetaZeroConfig.mult τ : ℂ) * ((((p : ℂ) - ((τ : ℂ) - 1 / 2)) * ((q : ℂ) + ((τ : ℂ) - 1 / 2)))⁻¹) =
      conj (probeCoord q (reflectCarrier zetaZeroConfig τ)) * probeCoord p τ := by
  have hm : zetaZeroConfig.mult (reflect (τ : ℂ)) = zetaZeroConfig.mult τ := zetaZeroConfig.mult_reflect _ τ.2
  have hsq : ((Real.sqrt (zetaZeroConfig.mult τ) : ℝ) : ℂ) * (Real.sqrt (zetaZeroConfig.mult τ) : ℝ) = (zetaZeroConfig.mult τ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  have hconj : conj ((q : ℂ) - (reflect (τ : ℂ) - 1 / 2)) = (q : ℂ) + ((τ : ℂ) - 1 / 2) := by
    simp only [reflect, map_sub, map_one, Complex.conj_ofReal, Complex.conj_conj, map_div₀,
      map_ofNat]
    ring
  have hp0 : (p : ℂ) - ((τ : ℂ) - 1 / 2) ≠ 0 := fun h => by
    have := (one_add_normSq_le_five_mul hp (abs_re_carrier_sub_half τ)).1
    rw [h, Complex.normSq_zero] at this
    linarith [Complex.normSq_nonneg ((τ : ℂ) - 1 / 2)]
  have hq0 : (q : ℂ) + ((τ : ℂ) - 1 / 2) ≠ 0 := fun h => by
    have := (one_add_normSq_le_five_mul hq (abs_re_carrier_sub_half τ)).2
    rw [h, Complex.normSq_zero] at this
    linarith [Complex.normSq_nonneg ((τ : ℂ) - 1 / 2)]
  simp only [probeCoord, reflectCarrier, hm, map_div₀, Complex.conj_ofReal, hconj]
  rw [mul_inv, ← hsq]
  ring

/-- **The probe kernel is the Krein form of the zeros**: `K(p, q) = ⟨R v_q, v_p⟩`. -/
theorem bareMixedEnergy_probe_eq_inner {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    (bareMixedEnergy (probe p) (probe q) : ℂ) =
      inner ℂ (reflectVec zetaZeroConfig (probeVec hq)) (probeVec hp) := by
  rw [bareMixedEnergy_probe_eq_tsum_carrier hp hq, lp.inner_eq_tsum]
  refine tsum_congr fun τ => ?_
  rw [mult_div_eq_conj_mul hp hq, RCLike.inner_apply', reflectVec_apply, probeVec_apply,
    probeVec_apply]

/-! ### The upper bound -/

/-- The real Pick matrix of the probe kernel on a finite family of nodes. -/
def probeGram {ι : Type*} (p : ι → ℝ) : Matrix ι ι ℂ :=
  fun i j => (bareMixedEnergy (probe (p i)) (probe (p j)) : ℂ)

/-- The combination `w = Σ_i x̄_i v_{p_i}` evaluated on the zeros. -/
def probeComb {ι : Type*} [Fintype ι] (p : ι → ℝ) (x : ι → ℂ) (τ : zetaZeroConfig.carrier) : ℂ :=
  ∑ i, conj (x i) * probeCoord (p i) τ

theorem summable_conj_mul_probeCoord {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Summable fun τ : zetaZeroConfig.carrier => conj (probeCoord q (reflectCarrier zetaZeroConfig τ)) * probeCoord p τ :=
  (summable_mult_div hp hq).congr (mult_div_eq_conj_mul hp hq)

theorem conj_probeComb_mul_eq {ι : Type*} [Fintype ι] (p : ι → ℝ) (x : ι → ℂ) (τ : zetaZeroConfig.carrier) :
    conj (probeComb p x (reflectCarrier zetaZeroConfig τ)) * probeComb p x τ = ∑ i, ∑ j,
      conj (x i) * ((conj (probeCoord (p j) (reflectCarrier zetaZeroConfig τ)) * probeCoord (p i) τ) * x j) := by
  rw [probeComb, probeComb, map_sum, Finset.sum_mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, Complex.conj_conj]
  ring

theorem summable_conj_probeComb_mul {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp : ∀ i, 1 ≤ p i)
    (x : ι → ℂ) :
    Summable fun τ : zetaZeroConfig.carrier => conj (probeComb p x (reflectCarrier zetaZeroConfig τ)) * probeComb p x τ :=
  (summable_sum fun i _ => summable_sum fun j _ =>
    ((summable_conj_mul_probeCoord (hp i) (hp j)).mul_right (x j)).mul_left (conj (x i))).congr
      fun τ => (conj_probeComb_mul_eq p x τ).symm

/-- The Pick form is the Krein form of the combination: `x* K x = Re Σ_ρ conj w(1 − ρ̄) w(ρ)`. -/
theorem hermQuad_probeGram_eq_tsum {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp : ∀ i, 1 ≤ p i)
    (x : ι → ℂ) :
    hermQuad (probeGram p) x =
      (∑' τ : zetaZeroConfig.carrier, conj (probeComb p x (reflectCarrier zetaZeroConfig τ)) * probeComb p x τ).re := by
  set T : zetaZeroConfig.carrier → ι → ι → ℂ := fun τ i j =>
    conj (x i) * ((conj (probeCoord (p j) (reflectCarrier zetaZeroConfig τ)) * probeCoord (p i) τ) * x j)
    with hT
  have hs : ∀ i j, Summable fun τ => T τ i j := fun i j =>
    ((summable_conj_mul_probeCoord (hp i) (hp j)).mul_right (x j)).mul_left (conj (x i))
  have hL : dotProduct (star x) (Matrix.mulVec (probeGram p) x) = ∑ i, ∑ j, ∑' τ, T τ i j := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Complex.star_def, probeGram,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [bareMixedEnergy_probe_eq_tsum_carrier (hp i) (hp j), ← tsum_mul_right, ← tsum_mul_left]
    exact tsum_congr fun τ => by rw [mult_div_eq_conj_mul (hp i) (hp j)]
  have hR : ∑' τ : zetaZeroConfig.carrier, conj (probeComb p x (reflectCarrier zetaZeroConfig τ)) * probeComb p x τ =
      ∑' τ, ∑ i, ∑ j, T τ i j :=
    tsum_congr fun τ => conj_probeComb_mul_eq p x τ
  rw [hermQuad, hL, hR, Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => hs i j]
  congr 1
  exact Finset.sum_congr rfl fun i _ => (Summable.tsum_finsetSum fun j _ => hs i j).symm

/-- Evaluation of the combination at a zero, as a linear functional of the coefficients. -/
def probeEval {ι : Type*} [Fintype ι] (p : ι → ℝ) (τ : zetaZeroConfig.carrier) : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun x := ∑ i, x i * conj (probeCoord (p i) τ)
  map_add' x y := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

theorem probeComb_eq_conj_probeEval {ι : Type*} [Fintype ι] (p : ι → ℝ) (x : ι → ℂ)
    (τ : zetaZeroConfig.carrier) : probeComb p x τ = conj (probeEval p τ x) := by
  simp only [probeComb, probeEval, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_mul,
    Complex.conj_conj]

/-- **Upper bound.** A real Pick matrix of the probe kernel with nodes `≥ 1` has at most as many
negative squares as `ζ` has zeros right of the critical line. -/
theorem hermNegIndex_probeGram_le {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp : ∀ i, 1 ≤ p i) :
    (hermNegIndex (probeGram p) : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard := by
  rcases (rightZeros zetaZeroConfig).finite_or_infinite with hR | hR
  · haveI := hR.fintype
    rw [hR.encard_eq_coe_toFinset_card, Set.Finite.card_toFinset]
    refine ENat.coe_le_coe.mpr (negIndex_le_card_of_nonneg_on_ker _
      (fun ρ : rightZeros zetaZeroConfig => probeEval p ⟨ρ.1, ρ.2.1⟩) fun x hx => ?_)
    have hw : ∀ τ : zetaZeroConfig.carrier, 1 / 2 < (τ : ℂ).re → probeComb p x τ = 0 := by
      intro τ hτ
      rw [probeComb_eq_conj_probeEval, hx ⟨τ.1, τ.2, hτ⟩, map_zero]
    rw [hermQuad_probeGram_eq_tsum hp x, Complex.re_tsum (summable_conj_probeComb_mul hp x)]
    refine tsum_nonneg fun τ => ?_
    rcases lt_trichotomy (τ : ℂ).re (1 / 2) with h | h | h
    · -- the reflected zero lies right of the line
      have hr : 1 / 2 < ((reflectCarrier zetaZeroConfig τ : zetaZeroConfig.carrier) : ℂ).re := by
        show 1 / 2 < (reflect (τ : ℂ)).re
        simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]
        linarith
      rw [hw _ hr, map_zero, zero_mul, Complex.zero_re]
    · -- on the line the reflection fixes the zero
      have hfix : reflectCarrier zetaZeroConfig τ = τ := by
        apply Subtype.ext
        show reflect (τ : ℂ) = τ
        apply Complex.ext
        · simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]
          linarith
        · simp only [reflect, Complex.sub_im, Complex.one_im, Complex.conj_im]
          ring
      rw [hfix, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
      exact Complex.normSq_nonneg _
    · rw [hw _ h, mul_zero, Complex.zero_re]
  · rw [hR.encard_eq]
    exact le_top

#print axioms bareMixedEnergy_probe_eq_inner
#print axioms hermNegIndex_probeGram_le

end GaloisForLFunctions.ExclusionOfTheCriticalState
