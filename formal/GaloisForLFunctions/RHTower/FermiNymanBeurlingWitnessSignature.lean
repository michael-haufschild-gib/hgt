import GaloisForLFunctions.RHTower.FermiNymanBeurlingHaarTarget

/-!
# The signature of the dyadic Hermitian form on alternating Nyman–Beurling witnesses

On witnesses `w` of the alternating Nyman–Beurling system (continuous, square-integrable on
`(0,1]`, orthogonal to every generator `φ_a = {1/(ax)} − 2{1/(2ax)}`, `a ≥ 1`) consider the Hermitian
form

`q(w) = ∫_0^{1/2} |w|² − ½ ∫_0^1 |w|²`.

The witness class is a complex vector space.  Spurious (dyadically self-similar) witnesses have
`q = 0`; a zero witness `w_ρ = t^{ρ̄−1}` has `q(w_ρ) = (2^{1−2Re ρ} − ½) ∫_0^1 |w_ρ|² > 0`.  Their
Hermitian cross term is

`B(g_k, w_ρ) = (2^{−ρ} − ½)/(ρ − 2πik/log 2) ≠ 0`,

so `g_k + ε w_ρ` with `ε = −B/q(w_ρ)` has `q = −|B|²/q(w_ρ) < 0`: an off-line zero makes the form
indefinite on the witness class, by interference with the prime-2 modes.

**Positivity criterion.**  If every witness carries at least half of its `L²` mass on `(0, 1/2]`
(`q ≥ 0` on witnesses), the Riemann hypothesis holds.  The identity `q ≡ 0` of
`FermiNymanBeurlingDyadicWitness` is thus needed only as a one-sided inequality.
-/

open Complex MeasureTheory Set Filter

noncomputable section

namespace RHTower

open GaloisForLFunctions.NymanMellin GaloisForLFunctions.HTGeometry

/-! ## The witness class is a vector space -/

theorem IsFermiNymanWitness.add_smul {u v : ℝ → ℂ} (hu : IsFermiNymanWitness u)
    (hv : IsFermiNymanWitness v) (ε : ℂ) : IsFermiNymanWitness (fun t => u t + ε * v t) := by
  refine ⟨hu.1.add (continuousOn_const.mul hv.1), ?_, fun a ha => ?_⟩
  · have hmeas : AEStronglyMeasurable (fun t => ‖u t + ε * v t‖ ^ 2)
        (volume.restrict (Ioc (0 : ℝ) 1)) :=
      (((hu.1.add (continuousOn_const.mul hv.1)).aestronglyMeasurable measurableSet_Ioc).norm).pow 2
    refine ((hu.2.1.const_mul 2).add (hv.2.1.const_mul (2 * ‖ε‖ ^ 2))).mono' hmeas
      (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : ‖u t + ε * v t‖ ≤ ‖u t‖ + ‖ε‖ * ‖v t‖ := by
      rw [← norm_mul]; exact norm_add_le _ _
    nlinarith [norm_nonneg (u t + ε * v t), norm_nonneg (u t), mul_nonneg (norm_nonneg ε)
      (norm_nonneg (v t)), sq_nonneg (‖u t‖ - ‖ε‖ * ‖v t‖)]
  · have iu := hu.integrableOn_mul_conj (measurable_fermiNymanGen a) (norm_fermiNymanGen_le a)
    have iv := hv.integrableOn_mul_conj (measurable_fermiNymanGen a) (norm_fermiNymanGen_le a)
    have hsplit : (fun t => fermiNymanGen a t * (starRingEnd ℂ) (u t + ε * v t)) =
        fun t => fermiNymanGen a t * (starRingEnd ℂ) (u t) +
          (starRingEnd ℂ) ε * (fermiNymanGen a t * (starRingEnd ℂ) (v t)) := by
      funext t; simp only [map_add, map_mul]; ring
    rw [hsplit, integral_add iu (iv.const_mul _), integral_const_mul, hu.2.2 a ha, hv.2.2 a ha]
    simp

/-! ## Expansion of the form -/

theorem IsFermiNymanWitness.integrableOn_mul_conj_witness {u v : ℝ → ℂ}
    (hu : IsFermiNymanWitness u) (hv : IsFermiNymanWitness v) :
    IntegrableOn (fun t => u t * (starRingEnd ℂ) (v t)) (Ioc 0 1) := by
  refine ((hu.2.1.add hv.2.1).div_const 2).mono'
    ((hu.1.aestronglyMeasurable measurableSet_Ioc).mul
      (hv.1.aestronglyMeasurable measurableSet_Ioc).star) (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply]
  rw [norm_mul, Complex.norm_conj]
  nlinarith [sq_nonneg (‖u t‖ - ‖v t‖)]

theorem norm_add_mul_sq (x y ε : ℂ) :
    ‖x + ε * y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ((starRingEnd ℂ) ε * (x * (starRingEnd ℂ) y)).re +
      ‖ε‖ ^ 2 * ‖y‖ ^ 2 := by
  have h1 : x * (starRingEnd ℂ) (ε * y) = (starRingEnd ℂ) ε * (x * (starRingEnd ℂ) y) := by
    rw [map_mul]; ring
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_add, h1, Complex.normSq_mul]
  ring

/-- Expansion of `∫_S |u + εv|²` on `S ⊆ (0,1]`. -/
theorem integral_normSq_add_mul {u v : ℝ → ℂ} (hu : IsFermiNymanWitness u)
    (hv : IsFermiNymanWitness v) (ε : ℂ) {c : ℝ} (hc : c ≤ 1) :
    (∫ t in Ioc (0 : ℝ) c, ‖u t + ε * v t‖ ^ 2) =
      (∫ t in Ioc (0 : ℝ) c, ‖u t‖ ^ 2) +
        2 * ((starRingEnd ℂ) ε * ∫ t in Ioc (0 : ℝ) c, u t * (starRingEnd ℂ) (v t)).re +
        ‖ε‖ ^ 2 * ∫ t in Ioc (0 : ℝ) c, ‖v t‖ ^ 2 := by
  have hsub : Ioc (0 : ℝ) c ⊆ Ioc 0 1 := Ioc_subset_Ioc_right hc
  have iu := hu.2.1.mono_set hsub
  have iv := hv.2.1.mono_set hsub
  have iuv := (hu.integrableOn_mul_conj_witness hv).mono_set hsub
  have hre : (∫ t in Ioc (0 : ℝ) c, ((starRingEnd ℂ) ε * (u t * (starRingEnd ℂ) (v t))).re) =
      ((starRingEnd ℂ) ε * ∫ t in Ioc (0 : ℝ) c, u t * (starRingEnd ℂ) (v t)).re := by
    rw [← integral_const_mul]
    exact integral_re (iuv.const_mul _)
  have iB : IntegrableOn (fun t => 2 * ((starRingEnd ℂ) ε * (u t * (starRingEnd ℂ) (v t))).re)
      (Ioc 0 c) := ((iuv.const_mul ((starRingEnd ℂ) ε)).re).const_mul 2
  have iA : IntegrableOn (fun t => ‖u t‖ ^ 2 + 2 * ((starRingEnd ℂ) ε *
      (u t * (starRingEnd ℂ) (v t))).re) (Ioc 0 c) := iu.add iB
  have iC : IntegrableOn (fun t => ‖ε‖ ^ 2 * ‖v t‖ ^ 2) (Ioc 0 c) := iv.const_mul _
  simp_rw [norm_add_mul_sq]
  rw [integral_add iA iC, integral_add iu iB, integral_const_mul, integral_const_mul, hre]

/-! ## The cross term of a spurious and a zero witness -/

theorem powerWitness_mul_conj_powerWitness {z w : ℂ} {t : ℝ} (ht : 0 < t) :
    powerWitness z t * (starRingEnd ℂ) (powerWitness w t) =
      (t : ℂ) ^ ((z + (starRingEnd ℂ) w - 1) - 1) := by
  unfold powerWitness
  rw [conj_ofReal_cpow ht, ← Complex.cpow_add _ _ (by exact_mod_cast ht.ne')]
  congr 1
  simp only [map_sub, map_one]
  ring

/-- `∫_0^c g_k conj(w_ρ) = c^σ/σ`, `σ = conj s_k + ρ − 1`. -/
theorem integral_spurious_mul_conj_zeroWitness (k : ℤ) {ρ : ℂ} (h1 : 0 < ρ.re) {c : ℝ}
    (hc : 0 ≤ c) :
    (∫ t in Ioc (0 : ℝ) c, powerWitness ((starRingEnd ℂ) (dyadicSpuriousMode k)) t *
        (starRingEnd ℂ) (powerWitness ((starRingEnd ℂ) ρ) t)) =
      (c : ℂ) ^ ((starRingEnd ℂ) (dyadicSpuriousMode k) + ρ - 1) /
        ((starRingEnd ℂ) (dyadicSpuriousMode k) + ρ - 1) := by
  have hσ : 0 < ((starRingEnd ℂ) (dyadicSpuriousMode k) + ρ - 1).re := by
    simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, dyadicSpuriousMode_re,
      Complex.one_re]
    linarith
  have hσ0 : (starRingEnd ℂ) (dyadicSpuriousMode k) + ρ - 1 ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hσ; exact lt_irrefl 0 hσ
  rw [setIntegral_congr_fun measurableSet_Ioc (fun t ht => by
      rw [powerWitness_mul_conj_powerWitness ht.1, Complex.conj_conj]),
    setIntegral_Ioc_cpow_sub_one hσ hc, Complex.ofReal_zero, Complex.zero_cpow hσ0, sub_zero]

theorem half_cpow_spurious_add (k : ℤ) (ρ : ℂ) :
    ((1 / 2 : ℝ) : ℂ) ^ ((starRingEnd ℂ) (dyadicSpuriousMode k) + ρ - 1) = (2 : ℂ) ^ (-ρ) := by
  have h := half_cpow_eq_two_cpow ((starRingEnd ℂ) (dyadicSpuriousMode k) + ρ)
  rw [h, conj_dyadicSpuriousMode]
  have hsplit : 1 - (dyadicSpuriousMode (-k) + ρ) = (1 - dyadicSpuriousMode (-k)) + (-ρ) := by ring
  rw [hsplit, Complex.cpow_add _ _ (by norm_num), two_cpow_one_sub_dyadicSpuriousMode, one_mul]

/-- The Hermitian cross term `B(g_k, w_ρ) = ∫_0^{1/2} g conj w − ½ ∫_0^1 g conj w`. -/
theorem crossTerm_spurious_zeroWitness (k : ℤ) {ρ : ℂ} (h1 : 0 < ρ.re) :
    (∫ t in Ioc (0 : ℝ) (1 / 2), powerWitness ((starRingEnd ℂ) (dyadicSpuriousMode k)) t *
        (starRingEnd ℂ) (powerWitness ((starRingEnd ℂ) ρ) t)) -
      (1 / 2 : ℂ) * (∫ t in Ioc (0 : ℝ) 1, powerWitness ((starRingEnd ℂ) (dyadicSpuriousMode k)) t *
        (starRingEnd ℂ) (powerWitness ((starRingEnd ℂ) ρ) t)) =
      ((2 : ℂ) ^ (-ρ) - 1 / 2) / ((starRingEnd ℂ) (dyadicSpuriousMode k) + ρ - 1) := by
  rw [integral_spurious_mul_conj_zeroWitness k h1 (by norm_num),
    integral_spurious_mul_conj_zeroWitness k h1 zero_le_one, half_cpow_spurious_add,
    Complex.ofReal_one, Complex.one_cpow]
  ring

theorem two_cpow_neg_ne_half {ρ : ℂ} (h2 : ρ.re < 1) : (2 : ℂ) ^ (-ρ) - 1 / 2 ≠ 0 := by
  intro h
  have hn := congrArg norm (sub_eq_zero.1 h)
  have hl : ‖(2 : ℂ) ^ (-ρ)‖ = (2 : ℝ) ^ (-ρ.re) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num),
      Complex.neg_re]
  have hr : ‖(1 / 2 : ℂ)‖ = (2 : ℝ) ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg_one]; norm_num
  rw [hl, hr] at hn
  have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
    (show -(1 : ℝ) < -ρ.re by linarith)
  linarith

/-! ## The positivity criterion -/

/-- **Hermitian positivity on witnesses implies the Riemann hypothesis.**  If every witness of the
alternating Nyman–Beurling system carries at least half of its `L²` mass on `(0, 1/2]`, the Riemann
hypothesis holds.  An off-line zero `ρ` violates this through the witness `g_1 + ε w_ρ`. -/
theorem riemannHypothesis_of_fermiNymanWitness_halfMass_le
    (h : ∀ w : ℝ → ℂ, IsFermiNymanWitness w →
      (1 / 2) * (∫ t in Ioc (0 : ℝ) 1, ‖w t‖ ^ 2) ≤ ∫ t in Ioc (0 : ℝ) (1 / 2), ‖w t‖ ^ 2) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨ρ, hζ, h1, h2⟩ := exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
  set g := powerWitness ((starRingEnd ℂ) (dyadicSpuriousMode 1)) with hg
  set w := powerWitness ((starRingEnd ℂ) ρ) with hw
  have hgW : IsFermiNymanWitness g := isFermiNymanWitness_spurious one_ne_zero
  have hwW : IsFermiNymanWitness w := isFermiNymanWitness_powerWitness_of_zeta_eq_zero hζ h1 h2
  have hz1 : 1 / 2 < ((starRingEnd ℂ) ρ).re := by rw [Complex.conj_re]; exact h1
  -- the form on the two witnesses
  set Iw := ∫ t in Ioc (0 : ℝ) 1, ‖w t‖ ^ 2 with hIw
  have hIw_pos : 0 < Iw := by
    rw [hIw, integral_Ioc_normSq_powerWitness hz1 one_pos, Real.one_rpow]
    have : 0 < 2 * ((starRingEnd ℂ) ρ).re - 1 := by linarith
    positivity
  set qw := (∫ t in Ioc (0 : ℝ) (1 / 2), ‖w t‖ ^ 2) - (1 / 2) * Iw with hqw
  have hqw_pos : 0 < qw := by
    rw [hqw, integral_half_normSq_powerWitness hz1, Complex.conj_re]
    have hlt : (1 / 2 : ℝ) < (2 : ℝ) ^ (1 - 2 * ρ.re) := by
      have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
        (show (-1 : ℝ) < 1 - 2 * ρ.re by linarith)
      rwa [Real.rpow_neg_one, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num] at this
    nlinarith
  have hqg : (∫ t in Ioc (0 : ℝ) (1 / 2), ‖g t‖ ^ 2) - (1 / 2) * ∫ t in Ioc (0 : ℝ) 1, ‖g t‖ ^ 2 = 0 := by
    rw [integral_half_normSq_of_selfSimilar (fun t ht => powerWitness_spurious_half 1 ht.1)]
    ring
  set B := (∫ t in Ioc (0 : ℝ) (1 / 2), g t * (starRingEnd ℂ) (w t)) -
    (1 / 2 : ℂ) * ∫ t in Ioc (0 : ℝ) 1, g t * (starRingEnd ℂ) (w t) with hB
  have hB_ne : B ≠ 0 := by
    rw [hB, hg, hw, crossTerm_spurious_zeroWitness 1 (by linarith)]
    refine div_ne_zero (two_cpow_neg_ne_half h2) ?_
    intro h0
    have := congrArg Complex.re h0
    simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, dyadicSpuriousMode_re,
      Complex.one_re, Complex.zero_re] at this
    linarith
  -- the destabilizing combination
  set ε : ℂ := -(B / (qw : ℂ)) with hε
  have hcomb := h _ (hgW.add_smul hwW ε)
  beta_reduce at hcomb
  rw [integral_normSq_add_mul hgW hwW ε (c := 1 / 2) (by norm_num),
    integral_normSq_add_mul hgW hwW ε (c := 1) le_rfl] at hcomb
  have hlin : ((starRingEnd ℂ) ε * ∫ t in Ioc (0 : ℝ) (1 / 2), g t * (starRingEnd ℂ) (w t)).re -
      (1 / 2) * ((starRingEnd ℂ) ε * ∫ t in Ioc (0 : ℝ) 1, g t * (starRingEnd ℂ) (w t)).re =
      ((starRingEnd ℂ) ε * B).re := by
    rw [hB, mul_sub, Complex.sub_re]
    congr 1
    rw [show (starRingEnd ℂ) ε * ((1 / 2 : ℂ) * ∫ t in Ioc (0 : ℝ) 1, g t * (starRingEnd ℂ) (w t)) =
      ((1 / 2 : ℝ) : ℂ) * ((starRingEnd ℂ) ε * ∫ t in Ioc (0 : ℝ) 1, g t * (starRingEnd ℂ) (w t))
      by push_cast; ring, Complex.re_ofReal_mul]
  have hcross : ((starRingEnd ℂ) ε * B).re = -(‖B‖ ^ 2 / qw) := by
    have hBB : (starRingEnd ℂ) B * B = ((‖B‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.conj_mul']; push_cast; ring
    have hval : (starRingEnd ℂ) ε * B = (((-(‖B‖ ^ 2 / qw)) : ℝ) : ℂ) := by
      rw [hε, map_neg, map_div₀, Complex.conj_ofReal, neg_mul, div_mul_eq_mul_div, hBB]
      push_cast; ring
    rw [hval, Complex.ofReal_re]
  have hnormε : ‖ε‖ ^ 2 = ‖B‖ ^ 2 / qw ^ 2 := by
    rw [hε, norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqw_pos, div_pow]
  have hBpos : 0 < ‖B‖ ^ 2 := by positivity
  have hεq : ‖ε‖ ^ 2 * qw = ‖B‖ ^ 2 / qw := by
    rw [hnormε]; field_simp
  have hq_expand : ‖ε‖ ^ 2 * qw = ‖ε‖ ^ 2 * (∫ t in Ioc (0 : ℝ) (1 / 2), ‖w t‖ ^ 2) -
      (1 / 2) * (‖ε‖ ^ 2 * Iw) := by
    rw [hqw]; ring
  have hneg : 0 < ‖B‖ ^ 2 / qw := div_pos hBpos hqw_pos
  linarith [hcomb, hqg, hlin, hcross, hεq, hq_expand, hneg]

/-! ## The generators are odd-floor indicators -/

/-- `{x} − 2{x/2} = 2⌊x/2⌋ − ⌊x⌋`. -/
theorem fract_sub_two_fract_half (x : ℝ) :
    Int.fract x - 2 * Int.fract (x / 2) = 2 * (⌊x / 2⌋ : ℝ) - (⌊x⌋ : ℝ) := by
  unfold Int.fract; ring

theorem floor_mem_double_floor_half (x : ℝ) :
    ⌊x⌋ = 2 * ⌊x / 2⌋ ∨ ⌊x⌋ = 2 * ⌊x / 2⌋ + 1 := by
  have h1 := Int.floor_le (x / 2)
  have h2 := Int.lt_floor_add_one (x / 2)
  have hlo : 2 * ⌊x / 2⌋ ≤ ⌊x⌋ := by
    rw [Int.le_floor]; push_cast; linarith
  have hhi : ⌊x⌋ < 2 * ⌊x / 2⌋ + 2 := by
    rw [Int.floor_lt]; push_cast; linarith
  omega

/-- **The alternating generator is minus the odd-floor indicator.**
`φ_a(t) = −1` if `⌊1/(at)⌋` is odd and `0` if it is even. -/
theorem fermiNymanGen_eq_oddFloor (a t : ℝ) :
    fermiNymanGen a t = if Odd ⌊1 / (a * t)⌋ then -1 else 0 := by
  unfold fermiNymanGen nymanGen
  have hx : 1 / (2 * a * t) = (1 / (a * t)) / 2 := by
    rcases eq_or_ne (a * t) 0 with h | h
    · rw [show 2 * a * t = 2 * (a * t) by ring, h]; simp
    · field_simp
  rw [hx]
  have hval : ((Int.fract (1 / (a * t)) : ℝ) : ℂ) - 2 * ((Int.fract (1 / (a * t) / 2) : ℝ) : ℂ) =
      (((2 * (⌊1 / (a * t) / 2⌋ : ℝ) - (⌊1 / (a * t)⌋ : ℝ)) : ℝ) : ℂ) := by
    rw [← fract_sub_two_fract_half]; push_cast; ring
  rw [hval]
  rcases floor_mem_double_floor_half (1 / (a * t)) with h | h
  · have hev : ¬ Odd ⌊1 / (a * t)⌋ := by
      rw [Int.not_odd_iff_even, h]; exact even_two_mul _
    rw [if_neg hev, h]; push_cast; ring
  · have hod : Odd ⌊1 / (a * t)⌋ := ⟨_, h⟩
    rw [if_pos hod, h]; push_cast; ring

/-! ## The `L^p` ladder -/

/-- An `L^p` witness: continuous, `p`-integrable on `(0,1]`, orthogonal to every generator `φ_a`, `a ≥ 1`. -/
def IsFermiNymanWitnessLp (p : ℝ) (w : ℝ → ℂ) : Prop :=
  ContinuousOn w (Ioc 0 1) ∧ IntegrableOn (fun t => ‖w t‖ ^ p) (Ioc 0 1) ∧
    ∀ a : ℝ, 1 ≤ a → ∫ t in Ioc (0 : ℝ) 1, fermiNymanGen a t * (starRingEnd ℂ) (w t) = 0

theorem integrableOn_rpow_normSq_powerWitness {z : ℂ} {p : ℝ} (hp : 0 < p)
    (hz : 1 - 1 / p < z.re) :
    IntegrableOn (fun t => ‖powerWitness z t‖ ^ p) (Ioc 0 1) := by
  have hr : (-1 : ℝ) < p * (z.re - 1) := by
    have h1 : 1 - 1 / p - 1 < z.re - 1 := by linarith
    have h2 := mul_lt_mul_of_pos_left h1 hp
    rw [show p * (1 - 1 / p - 1) = -1 by field_simp; ring] at h2
    exact h2
  have hint := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hr)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hint
  refine hint.congr_fun (fun t ht => ?_) measurableSet_Ioc
  unfold powerWitness
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht.1, ← Real.rpow_mul ht.1.le]
  simp only [Complex.sub_re, Complex.one_re]
  ring_nf

/-- **The `L^p` ladder.**  If every `L^p` witness of the alternating Nyman–Beurling system is dyadically
self-similar, then `ζ` has no zero with `1 − 1/p < Re ρ < 1`.  At `p = 2` this is the Riemann
hypothesis; as `p → ∞` it approaches the nonvanishing on `Re s = 1`. -/
theorem no_zeta_zero_of_fermiNymanWitnessLp_selfSimilar {p : ℝ} (hp : 0 < p)
    (h : ∀ w : ℝ → ℂ, IsFermiNymanWitnessLp p w → ∀ t ∈ Ioc (0 : ℝ) 1, w (t / 2) = w t)
    {ρ : ℂ} (hζ : riemannZeta ρ = 0) (h1 : 1 - 1 / p < ρ.re) (h2 : ρ.re < 1) (h0 : 0 < ρ.re) :
    False := by
  have hwit : IsFermiNymanWitnessLp p (powerWitness ((starRingEnd ℂ) ρ)) := by
    refine ⟨continuousOn_powerWitness _,
      integrableOn_rpow_normSq_powerWitness hp (by rw [Complex.conj_re]; exact h1), fun a ha => ?_⟩
    have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
    have hconj : ∀ t ∈ Ioc (0 : ℝ) 1, fermiNymanGen a t * (starRingEnd ℂ)
        (powerWitness ((starRingEnd ℂ) ρ) t) = fermiNymanGen a t * (t : ℂ) ^ (ρ - 1) := by
      intro t ht
      unfold powerWitness
      rw [conj_ofReal_cpow ht.1, map_sub, Complex.conj_conj, map_one]
    rw [setIntegral_congr_fun measurableSet_Ioc hconj, integral_Ioc_fermiNymanGen_mul_cpow ha,
      mellin_fermiNymanGen h0 h2 ha0, hζ]
    simp
  have hw := h _ hwit 1 ⟨one_pos, le_rfl⟩
  exact powerWitness_half_ne_of_re_lt_one (z := (starRingEnd ℂ) ρ) (by rwa [Complex.conj_re]) hw

end RHTower
