import GaloisForLFunctions.RHTower.FermiNymanBeurlingDyadicWitness
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# The dyadic Haar target of the alternating Nyman–Beurling system

The constant target `1_{(0,1]}` of the classical Nyman–Beurling problem pairs nontrivially with the
spurious witnesses `t^{−2πik/log 2}` of the alternating generators `φ_a(x) = {1/(ax)} − 2{1/(2ax)}`, so it
can never be approximated by them.  The natural target is the dyadic Haar function

`h(t) = −1` on `(0, 1/2]`,  `h(t) = +1` on `(1/2, 1]`,

whose Mellin pairing is `∫_0^1 h(t) t^{s−1} dt = (1 − 2^{1−s})/s`.  It vanishes exactly at the
spurious modes and at no zero of `ζ` in the strip: the Haar function annihilates the physical
(prime-2) witnesses and sees every off-line zero.

* Every finite combination of generators is orthogonal to every witness, so a zero `ρ` of `ζ`
  with `½ < Re ρ < 1` forces the explicit floor
  `∫_0^1 |h − Σ c_j φ_{a_j}|² ≥ (2 Re ρ − 1) |1 − 2^{1−ρ}|² / |ρ|²`.
* Consequently, if `h` is an `L²(0,1]`-limit of finite combinations of the `φ_a` (`a ≥ 1`), the
  Riemann hypothesis holds.

Since `|1 − 2^{1−s}|` is bounded above and below on `Re s = ½`, this is the classical Báez-Duarte
problem with a bounded equivalent weight: the physical source adds the explicit dyadic factor and
nothing else.
-/

open Complex MeasureTheory Set Filter

noncomputable section

namespace RHTower

open GaloisForLFunctions.NymanMellin GaloisForLFunctions.HTGeometry

/-- The dyadic Haar function on `(0,1]`. -/
def dyadicHaar (t : ℝ) : ℂ := if t ≤ 1 / 2 then -1 else 1

theorem measurable_dyadicHaar : Measurable dyadicHaar :=
  Measurable.ite measurableSet_Iic measurable_const measurable_const

theorem norm_dyadicHaar (t : ℝ) : ‖dyadicHaar t‖ = 1 := by
  unfold dyadicHaar; split_ifs <;> simp

/-- `∫_0^c t^{s−1} dt = c^s/s` for `Re s > 0`. -/
theorem integral_cpow_sub_one {s : ℂ} (hs : 0 < s.re) (c : ℝ) :
    (∫ t in (0 : ℝ)..c, (t : ℂ) ^ (s - 1)) = (c : ℂ) ^ s / s := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hs; exact lt_irrefl 0 hs
  rw [integral_cpow (Or.inl (by simp; linarith))]
  simp only [sub_add_cancel, Complex.ofReal_zero, Complex.zero_cpow hs0, sub_zero]

theorem integrableOn_Ioc_cpow_sub_one {s : ℂ} (hs : 0 < s.re) {a b : ℝ} (hab : a ≤ b) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1)) (Ioc a b) := by
  have h := intervalIntegral.intervalIntegrable_cpow' (a := a) (b := b) (r := s - 1)
    (by simp; linarith)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 h

theorem setIntegral_Ioc_cpow_sub_one {s : ℂ} (hs : 0 < s.re) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in Ioc a b, (t : ℂ) ^ (s - 1)) = ((b : ℂ) ^ s - (a : ℂ) ^ s) / s := by
  rw [← intervalIntegral.integral_of_le hab, integral_cpow (Or.inl (by simp; linarith))]
  simp only [sub_add_cancel]

/-- **Mellin pairing of the Haar target.**  `∫_0^1 h(t) t^{s−1} dt = (1 − 2^{1−s})/s`. -/
theorem integral_dyadicHaar_mul_cpow {s : ℂ} (hs : 0 < s.re) :
    (∫ t in Ioc (0 : ℝ) 1, dyadicHaar t * (t : ℂ) ^ (s - 1)) = (1 - (2 : ℂ) ^ (1 - s)) / s := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hs; exact lt_irrefl 0 hs
  have hL : ∀ t ∈ Ioc (0 : ℝ) (1 / 2), dyadicHaar t * (t : ℂ) ^ (s - 1) = -((t : ℂ) ^ (s - 1)) := by
    intro t ht; rw [dyadicHaar, if_pos ht.2]; ring
  have hR : ∀ t ∈ Ioc (1 / 2 : ℝ) 1, dyadicHaar t * (t : ℂ) ^ (s - 1) = (t : ℂ) ^ (s - 1) := by
    intro t ht; rw [dyadicHaar, if_neg (not_le.2 ht.1)]; ring
  have iL : IntegrableOn (fun t : ℝ => dyadicHaar t * (t : ℂ) ^ (s - 1)) (Ioc 0 (1 / 2)) :=
    ((integrableOn_Ioc_cpow_sub_one hs (by norm_num)).neg).congr_fun (fun t ht => (hL t ht).symm)
      measurableSet_Ioc
  have iR : IntegrableOn (fun t : ℝ => dyadicHaar t * (t : ℂ) ^ (s - 1)) (Ioc (1 / 2) 1) :=
    (integrableOn_Ioc_cpow_sub_one hs (by norm_num)).congr_fun (fun t ht => (hR t ht).symm)
      measurableSet_Ioc
  rw [← Ioc_union_Ioc_eq_Ioc (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1),
    setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc iL iR,
    setIntegral_congr_fun measurableSet_Ioc hL, setIntegral_congr_fun measurableSet_Ioc hR,
    integral_neg, setIntegral_Ioc_cpow_sub_one hs (by norm_num),
    setIntegral_Ioc_cpow_sub_one hs (by norm_num)]
  have hhalf : ((1 / 2 : ℝ) : ℂ) ^ s = (2 : ℂ) ^ (-s) := by
    have := half_cpow_eq_two_cpow (s + 1)
    rwa [add_sub_cancel_right, show (1 : ℂ) - (s + 1) = -s by ring] at this
  push_cast at hhalf ⊢
  rw [hhalf, Complex.zero_cpow hs0, Complex.one_cpow, ← two_mul_two_cpow_neg]
  field_simp
  ring

/-- Pairing of the Haar target with a power witness. -/
theorem integral_dyadicHaar_mul_conj_powerWitness {z : ℂ} (hz : 0 < z.re) :
    (∫ t in Ioc (0 : ℝ) 1, dyadicHaar t * (starRingEnd ℂ) (powerWitness z t)) =
      (1 - (2 : ℂ) ^ (1 - (starRingEnd ℂ) z)) / (starRingEnd ℂ) z := by
  have hcongr : ∀ t ∈ Ioc (0 : ℝ) 1, dyadicHaar t * (starRingEnd ℂ) (powerWitness z t) =
      dyadicHaar t * (t : ℂ) ^ ((starRingEnd ℂ) z - 1) := by
    intro t ht
    unfold powerWitness
    rw [conj_ofReal_cpow ht.1, map_sub, map_one]
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr,
    integral_dyadicHaar_mul_cpow (by rw [Complex.conj_re]; exact hz)]

/-- **The Haar target annihilates the spurious witnesses.** -/
theorem integral_dyadicHaar_mul_conj_spurious (k : ℤ) :
    (∫ t in Ioc (0 : ℝ) 1, dyadicHaar t *
      (starRingEnd ℂ) (powerWitness ((starRingEnd ℂ) (dyadicSpuriousMode k)) t)) = 0 := by
  have hre : 0 < ((starRingEnd ℂ) (dyadicSpuriousMode k)).re := by
    rw [Complex.conj_re, dyadicSpuriousMode_re]; norm_num
  rw [integral_dyadicHaar_mul_conj_powerWitness hre, Complex.conj_conj,
    two_cpow_one_sub_dyadicSpuriousMode, sub_self, zero_div]

theorem one_sub_two_cpow_ne_zero {ρ : ℂ} (h2 : ρ.re < 1) : 1 - (2 : ℂ) ^ (1 - ρ) ≠ 0 := by
  intro h
  have hn := congrArg norm (sub_eq_zero.1 h)
  rw [norm_one, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)] at hn
  have : 1 < (2 : ℝ) ^ ((1 - ρ).re) :=
    Real.one_lt_rpow (by norm_num) (by simp; linarith)
  linarith

/-- **The Haar target sees every off-line zero.** -/
theorem integral_dyadicHaar_mul_conj_zeroWitness_ne_zero {ρ : ℂ} (h1 : 0 < ρ.re) (h2 : ρ.re < 1) :
    (∫ t in Ioc (0 : ℝ) 1, dyadicHaar t * (starRingEnd ℂ) (powerWitness ((starRingEnd ℂ) ρ) t)) ≠ 0 := by
  rw [integral_dyadicHaar_mul_conj_powerWitness (by rw [Complex.conj_re]; exact h1),
    Complex.conj_conj]
  have hρ : ρ ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at h1; exact lt_irrefl 0 h1
  exact div_ne_zero (one_sub_two_cpow_ne_zero h2) hρ

/-! ## Finite combinations and the approximation floor -/

/-- A finite combination `Σ_j c_j φ_{a_j}` of alternating generators. -/
def fermiNymanCombination {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) : ℝ → ℂ :=
  fun t => ∑ j, c j * fermiNymanGen (a j) t

theorem measurable_fermiNymanCombination {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) :
    Measurable (fermiNymanCombination c a) := by
  unfold fermiNymanCombination
  exact Finset.measurable_sum _ (fun j _ => measurable_const.mul (measurable_fermiNymanGen _))

theorem norm_fermiNymanCombination_le {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) (t : ℝ) :
    ‖fermiNymanCombination c a t‖ ≤ ∑ j, ‖c j‖ * 3 := by
  unfold fermiNymanCombination
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_fermiNymanGen_le _ _) (norm_nonneg _)

theorem IsFermiNymanWitness.integrableOn_norm {w : ℝ → ℂ} (hw : IsFermiNymanWitness w) :
    IntegrableOn (fun t => ‖w t‖) (Ioc 0 1) := by
  refine (((integrableOn_const (C := (1 : ℝ)) measure_Ioc_lt_top.ne).add hw.2.1).div_const 2).mono'
    (hw.1.aestronglyMeasurable measurableSet_Ioc).norm (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  nlinarith [sq_nonneg (‖w t‖ - 1)]

/-- Bounded measurable functions pair integrably with witnesses. -/
theorem IsFermiNymanWitness.integrableOn_mul_conj {w : ℝ → ℂ} (hw : IsFermiNymanWitness w)
    {g : ℝ → ℂ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, ‖g t‖ ≤ M) :
    IntegrableOn (fun t => g t * (starRingEnd ℂ) (w t)) (Ioc 0 1) := by
  refine (hw.integrableOn_norm.const_mul M).mono'
    (hg.aestronglyMeasurable.mul (hw.1.aestronglyMeasurable measurableSet_Ioc).star)
    (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_right (hM t) (norm_nonneg _)

/-- **Finite combinations are orthogonal to every witness.** -/
theorem IsFermiNymanWitness.integral_combination_mul_conj {w : ℝ → ℂ} (hw : IsFermiNymanWitness w)
    {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) (ha : ∀ j, 1 ≤ a j) :
    (∫ t in Ioc (0 : ℝ) 1, fermiNymanCombination c a t * (starRingEnd ℂ) (w t)) = 0 := by
  unfold fermiNymanCombination
  have hfun : (fun t => (∑ j, c j * fermiNymanGen (a j) t) * (starRingEnd ℂ) (w t)) =
      fun t => ∑ j, c j * (fermiNymanGen (a j) t * (starRingEnd ℂ) (w t)) := by
    funext t; rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hfun, integral_finsetSum _ (fun j _ => (hw.integrableOn_mul_conj
    (measurable_fermiNymanGen _) (norm_fermiNymanGen_le _)).const_mul _)]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [integral_const_mul, hw.2.2 (a j) (ha j), mul_zero]

/-- **Cauchy–Schwarz for the witness pairing.** -/
theorem IsFermiNymanWitness.norm_sq_integral_mul_conj_le {w : ℝ → ℂ} (hw : IsFermiNymanWitness w)
    {g : ℝ → ℂ} (hg : Measurable g) (hg2 : IntegrableOn (fun t => ‖g t‖ ^ 2) (Ioc 0 1)) :
    ‖∫ t in Ioc (0 : ℝ) 1, g t * (starRingEnd ℂ) (w t)‖ ^ 2 ≤
      (∫ t in Ioc (0 : ℝ) 1, ‖g t‖ ^ 2) * ∫ t in Ioc (0 : ℝ) 1, ‖w t‖ ^ 2 := by
  have h1 : ‖∫ t in Ioc (0 : ℝ) 1, g t * (starRingEnd ℂ) (w t)‖ ≤
      ∫ t in Ioc (0 : ℝ) 1, ‖g t‖ * ‖w t‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [norm_mul, Complex.norm_conj]
  have h2 := sq_integral_mul_le (μ := volume.restrict (Ioc (0 : ℝ) 1)) (f := fun t => ‖g t‖)
    (g := fun t => ‖w t‖) hg.aestronglyMeasurable.norm
    (hw.1.aestronglyMeasurable measurableSet_Ioc).norm hg2 hw.2.1
  have h0 : 0 ≤ ‖∫ t in Ioc (0 : ℝ) 1, g t * (starRingEnd ℂ) (w t)‖ := norm_nonneg _
  calc ‖∫ t in Ioc (0 : ℝ) 1, g t * (starRingEnd ℂ) (w t)‖ ^ 2
      ≤ (∫ t in Ioc (0 : ℝ) 1, ‖g t‖ * ‖w t‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ _ := h2

theorem integrableOn_normSq_dyadicHaar_sub_combination {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) :
    IntegrableOn (fun t => ‖dyadicHaar t - fermiNymanCombination c a t‖ ^ 2) (Ioc 0 1) := by
  refine Measure.integrableOn_of_bounded (M := (1 + ∑ j, ‖c j‖ * 3) ^ 2) measure_Ioc_lt_top.ne
    ((measurable_dyadicHaar.sub (measurable_fermiNymanCombination c a)).norm.pow_const 2
      |>.aestronglyMeasurable) (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hb : ‖dyadicHaar t - fermiNymanCombination c a t‖ ≤ 1 + ∑ j, ‖c j‖ * 3 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_dyadicHaar]
    linarith [norm_fermiNymanCombination_le c a t]
  exact pow_le_pow_left₀ (norm_nonneg _) hb 2

/-- **Approximation floor.**  A zero `ρ` of `ζ` with `½ < Re ρ < 1` bounds every approximation of the
Haar target by alternating generators from below:
`∫_0^1 |h − Σ c_j φ_{a_j}|² ≥ (2 Re ρ − 1) |1 − 2^{1−ρ}|²/|ρ|²`. -/
theorem dyadicHaar_approximation_floor {ρ : ℂ} (hζ : riemannZeta ρ = 0) (h1 : 1 / 2 < ρ.re)
    (h2 : ρ.re < 1) {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) (ha : ∀ j, 1 ≤ a j) :
    (2 * ρ.re - 1) * ‖(1 - (2 : ℂ) ^ (1 - ρ)) / ρ‖ ^ 2 ≤
      ∫ t in Ioc (0 : ℝ) 1, ‖dyadicHaar t - fermiNymanCombination c a t‖ ^ 2 := by
  set w := powerWitness ((starRingEnd ℂ) ρ) with hwdef
  have hw := isFermiNymanWitness_powerWitness_of_zeta_eq_zero hζ h1 h2
  have hz1 : 1 / 2 < ((starRingEnd ℂ) ρ).re := by rw [Complex.conj_re]; exact h1
  have hpair : (∫ t in Ioc (0 : ℝ) 1, (dyadicHaar t - fermiNymanCombination c a t) *
      (starRingEnd ℂ) (w t)) = (1 - (2 : ℂ) ^ (1 - ρ)) / ρ := by
    have hsplit : (fun t => (dyadicHaar t - fermiNymanCombination c a t) * (starRingEnd ℂ) (w t)) =
        fun t => dyadicHaar t * (starRingEnd ℂ) (w t) -
          fermiNymanCombination c a t * (starRingEnd ℂ) (w t) := by
      funext t; ring
    rw [hsplit, integral_sub (hw.integrableOn_mul_conj measurable_dyadicHaar
      (fun t => (norm_dyadicHaar t).le))
      (hw.integrableOn_mul_conj (measurable_fermiNymanCombination c a)
        (norm_fermiNymanCombination_le c a)),
      hw.integral_combination_mul_conj c a ha, sub_zero,
      integral_dyadicHaar_mul_conj_powerWitness (by linarith), Complex.conj_conj]
  have hmeas : Measurable fun t => dyadicHaar t - fermiNymanCombination c a t :=
    measurable_dyadicHaar.sub (measurable_fermiNymanCombination c a)
  have hcs := hw.norm_sq_integral_mul_conj_le
    (g := fun t => dyadicHaar t - fermiNymanCombination c a t) hmeas
    (integrableOn_normSq_dyadicHaar_sub_combination c a)
  rw [hpair, integral_Ioc_normSq_powerWitness hz1 one_pos, Real.one_rpow, Complex.conj_re] at hcs
  have hpos : 0 < 2 * ρ.re - 1 := by linarith
  have := mul_le_mul_of_nonneg_left hcs hpos.le
  rw [show (2 * ρ.re - 1) * ((∫ t in Ioc (0 : ℝ) 1,
      ‖dyadicHaar t - fermiNymanCombination c a t‖ ^ 2) * (1 / (2 * ρ.re - 1))) =
      ∫ t in Ioc (0 : ℝ) 1, ‖dyadicHaar t - fermiNymanCombination c a t‖ ^ 2 by
    field_simp] at this
  exact this

/-- **The alternating Nyman–Beurling criterion with the dyadic Haar target.**  If the Haar function is an
`L²(0,1]`-limit of finite combinations of the alternating generators `φ_a` (`a ≥ 1`), the Riemann
hypothesis holds. -/
theorem riemannHypothesis_of_dyadicHaar_approximable
    (h : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (c : Fin n → ℂ) (a : Fin n → ℝ), (∀ j, 1 ≤ a j) ∧
      (∫ t in Ioc (0 : ℝ) 1, ‖dyadicHaar t - fermiNymanCombination c a t‖ ^ 2) < ε) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨ρ, hζ, h1, h2⟩ := exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
  have hρ : ρ ≠ 0 := by
    intro h0; rw [h0, Complex.zero_re] at h1; linarith
  have hfloor : 0 < (2 * ρ.re - 1) * ‖(1 - (2 : ℂ) ^ (1 - ρ)) / ρ‖ ^ 2 := by
    have : 0 < ‖(1 - (2 : ℂ) ^ (1 - ρ)) / ρ‖ :=
      norm_pos_iff.2 (div_ne_zero (one_sub_two_cpow_ne_zero h2) hρ)
    have h' : 0 < 2 * ρ.re - 1 := by linarith
    positivity
  obtain ⟨n, c, a, ha, hlt⟩ := h _ hfloor
  exact absurd (dyadicHaar_approximation_floor hζ h1 h2 c a ha) (not_le.2 hlt)

end RHTower
