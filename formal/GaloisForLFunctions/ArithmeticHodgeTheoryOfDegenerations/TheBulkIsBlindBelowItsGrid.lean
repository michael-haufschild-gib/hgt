import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePartialZetaSumIsQuietBelowItsGrid
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheBulkAtThePoleReadsTheArchimedeanGenus

/-!
# The bulk is blind below its grid

A fixed conductor packet `x = Σ_{e∈E} y_e r_e` (conductors `e ≤ L`) is read by a zero `ρ` through
its conductor polynomials `D_e(ρ;N)`. Below the grid of these polynomials, `|γ| ≤ π⌊N/L⌋`, the
partial zeta sums have no stationary point beyond `N/e`, so at a zero `D_e(ρ;N) = [e = 1]N^ρ/ρ +
O(N^{Re ρ − 1})` uniformly in the height (`ThePartialZetaSumIsQuietBelowItsGrid`). Hence:

* **A packet at a zero below its grid** (`norm_dirichletPoly_packet_sub_pole_le_grid`):
  `|√log N D_x(γ_ρ) − y_1 N^ρ/ρ| ≤ P N^{Re ρ − 1}` with `P = Σ_e |y_e/√φ(e)| 24e³`.
* **One zero below the grid** (`norm_log_div_mul_bulkLedger_sub_atom_le_grid`): the normalized
  ledger entry is `m_ρ a_N(ρ) y_1²/(ρ(1 − ρ))`, `a_N(ρ)` the atom factor, up to
  `m_ρ C (|y_1| P (1/|ρ| + 1/|1 − ρ|) + P²/N)/N`: the pole term reads the zero, the conductor
  remainders only through products of size `1/(N|ρ|)` and `1/N²`.
* **The bulk is blind below its grid** (`tendsto_sum_bulkLedger_belowGrid`): for `2λL ≤ π` and
  every overlap schedule with `c_N/N → 0`, all zeros of height `≤ λN` together contribute
  `(c_N/log N) κ y_1² Σ_ρ m_ρ/(ρ(1 − ρ)) + o(c_N/log N)`, `κ = (∫φ)²/∫φ²`: the archimedean genus at
  the pole and nothing else (`tendsto_sum_bulkLedger_belowGrid_poleFree`).

The atoms of width `c/N` resolve the zeros up to the height `N/c`; the packets see none of them,
nor any zero up to `λN`, a factor `λc` higher. Everything else in the normalized complete form of a
fixed packet, its first-order count and its second-order term, is carried by the zeros above the
grid of the conductor polynomials, where the atoms see them only through the spectral tail
`|φ̂(cγ/N)|²`, `cγ/N ≥ λc`, and where the conductor polynomials are shorter than the height
(the mean-value regime of Gonek and Montgomery–Vaughan).
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open BezoutValuationIncidence SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  ArithmeticCastelnuovoSeveri

/-! ### A packet at a zero below its grid -/

/-- The packet constant below the grid, `Σ_{e∈E} |y_e/√φ(e)| · 24e³`. -/
def packetConstGrid (E : Finset ℕ) (y : ℕ → ℝ) : ℝ :=
  ∑ e ∈ E, |y e / Real.sqrt e.totient| * (24 * (e : ℝ) ^ 3)

theorem packetConstGrid_nonneg (E : Finset ℕ) (y : ℕ → ℝ) : 0 ≤ packetConstGrid E y :=
  sum_nonneg fun e _ => by positivity

/-- **A packet at a zero below its grid**: for `N ≥ 2L` and `|Im s| ≤ π⌊N/L⌋`,
`‖√log N · D_x(γ_s) − y_1 N^s/s‖ ≤ P N^{Re s − 1}`. -/
theorem norm_dirichletPoly_packet_sub_pole_le_grid {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta (1 - s) = 0) {E : Finset ℕ} (hE : ∀ e ∈ E, 1 ≤ e) {L : ℕ}
    (hL : ∀ e ∈ E, e ≤ L) (y : ℕ → ℝ) {N : ℕ} (hLN : 2 * L ≤ N)
    (hτ : |s.im| ≤ Real.pi * (N / L : ℕ)) (hlog : 0 < Real.log N) :
    ‖((Real.sqrt (Real.log N) : ℝ) : ℂ) * dirichletPoly N (packetWeights E y N) (gammaOf s) -
        (poleCoefficient E y : ℂ) * (((N : ℝ) : ℂ) ^ s / s)‖ ≤
      packetConstGrid E y * (N : ℝ) ^ (s.re - 1) := by
  have hsq : ((Real.sqrt (Real.log N) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hlog).ne'
  rw [dirichletPoly_packetWeights, ← mul_assoc, mul_inv_cancel₀ hsq, one_mul]
  have hpole : (poleCoefficient E y : ℂ) =
      if 1 ∈ E then ((y 1 / Real.sqrt (Nat.totient 1) : ℝ) : ℂ) else 0 := by
    unfold poleCoefficient
    split_ifs <;> simp
  have hsum := sum_mul_horizonTerm E (fun e => ((y e / Real.sqrt e.totient : ℝ) : ℂ)) N s
  beta_reduce at hsum
  rw [hpole, ← hsum, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  unfold packetConstGrid
  rw [Finset.sum_mul]
  refine sum_le_sum fun e he => ?_
  have he1 := hE e he
  have heL := hL e he
  have heN : 2 * e ≤ N := le_trans (by omega) hLN
  have hτe : |s.im| ≤ Real.pi * (N / e : ℕ) := by
    refine hτ.trans (mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le)
    exact_mod_cast Nat.div_le_div_left heL he1
  have hb := norm_conductorDirichlet_sub_horizonTerm_le_grid hs0 hs1 hz he1 heN hτe
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |y e / Real.sqrt e.totient| * ‖conductorDirichlet e N s - horizonTerm e N s‖ ≤
        |y e / Real.sqrt e.totient| * (24 * (e : ℝ) ^ 3 * (N : ℝ) ^ (s.re - 1)) :=
        mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := by ring

/-! ### One zero below the grid -/

/-- The transform of a profile on `[0, 1]` at height `|Im z| ≤ ½` is at most `e^{1/2} ∫|φ|`. -/
theorem norm_paperFT_profile_le_of_im {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT (cx φ) z‖ ≤ (∫ u, |φ u|) * Real.exp (1 / 2) := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hint : Integrable (cx φ) :=
    (Complex.continuous_ofReal.comp hφ).integrable_of_hasCompactSupport
      (hφc.comp_left Complex.ofReal_zero)
  have hnorm : ∫ u, |φ u| = ∫ u, ‖cx φ u‖ := by
    congr 1; funext u; simp [cx, Complex.norm_real]
  rw [hnorm]
  unfold paperFT
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (hint.norm.mul_const _) (Eventually.of_forall fun u => ?_)
  rw [norm_mul, Complex.norm_exp]
  by_cases hu : u ∈ Set.Icc (0 : ℝ) 1
  · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have hre : (Complex.I * z * (u : ℂ)).re = -(z.im * u) := by simp
    rw [hre]
    have hu1 : |u| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
    calc -(z.im * u) ≤ |z.im * u| := neg_le_abs _
      _ = |z.im| * |u| := abs_mul _ _
      _ ≤ 1 / 2 * 1 := mul_le_mul hz hu1 (abs_nonneg _) (by norm_num)
      _ = 1 / 2 := by norm_num
  · simp [cx, hφsupp u hu]

/-- The atom factor `φ̂(wγ_ρ) conj φ̂(w conj γ_ρ)/∫φ²` at width `w = c/N`. -/
def atomFactor (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (ρ : ℂ) : ℂ :=
  paperFT (cx φ) (((c / N : ℝ) : ℂ) * gammaOf ρ) *
    conj (paperFT (cx φ) (((c / N : ℝ) : ℂ) * conj (gammaOf ρ))) / ((∫ u, φ u ^ 2 : ℝ) : ℂ)

/-- Below the resolution (`c ≤ N`) the atom factor at a point of the strip is at most
`e (∫|φ|)²/∫φ²`. -/
theorem norm_atomFactor_le {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hcN : c ≤ N) {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    ‖atomFactor φ c N ρ‖ ≤ Real.exp 1 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2) := by
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hc hcN
  have hw0 : 0 < c / N := div_pos hc hN0
  have hw1 : c / N ≤ 1 := (div_le_one hN0).mpr hcN
  have hgim : |(gammaOf ρ).im| ≤ 1 / 2 := by
    have : (gammaOf ρ).im = -(ρ.re - 1 / 2) := by simp [gammaOf, Complex.div_I]
    rw [this, abs_neg, abs_le]; constructor <;> linarith
  have hprod : c / N * |(gammaOf ρ).im| ≤ 1 / 2 :=
    (mul_le_mul hw1 hgim (abs_nonneg _) zero_le_one).trans (by norm_num)
  have him1 : |((((c / N : ℝ) : ℂ) * gammaOf ρ)).im| ≤ 1 / 2 := by
    rw [Complex.im_ofReal_mul, abs_mul, abs_of_pos hw0]; exact hprod
  have him2 : |((((c / N : ℝ) : ℂ) * conj (gammaOf ρ))).im| ≤ 1 / 2 := by
    rw [Complex.im_ofReal_mul, Complex.conj_im, abs_mul, abs_neg, abs_of_pos hw0]; exact hprod
  have h1 := norm_paperFT_profile_le_of_im hφ hφsupp him1
  have h2 := norm_paperFT_profile_le_of_im hφ hφsupp him2
  have hI0 : 0 ≤ ∫ u, |φ u| := integral_nonneg fun u => abs_nonneg _
  unfold atomFactor
  rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hφ2, div_le_div_iff_of_pos_right hφ2]
  calc ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * gammaOf ρ)‖ *
        ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * conj (gammaOf ρ))‖
      ≤ ((∫ u, |φ u|) * Real.exp (1 / 2)) * ((∫ u, |φ u|) * Real.exp (1 / 2)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = Real.exp 1 * (∫ u, |φ u|) ^ 2 := by
        rw [show Real.exp 1 = Real.exp (1 / 2) * Real.exp (1 / 2) by
          rw [← Real.exp_add]; norm_num]
        ring

/-- **One zero below the grid.** For a nontrivial zero `ρ` with `|Im ρ| ≤ π⌊N/L⌋`, `N ≥ 2L`,
`c ≤ N`: `‖(log N/c) W_ρ/∫g² − m_ρ a_N(ρ) y_1²/(ρ(1 − ρ))‖ ≤
m_ρ (e I₁²/∫φ²)(|y_1| P (1/|ρ| + 1/|1 − ρ|) + P²/N)/N`. -/
theorem norm_log_div_mul_bulkLedger_sub_atom_le_grid {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {E : Finset ℕ}
    (hE : ∀ e ∈ E, 1 ≤ e) {L : ℕ} (hL : ∀ e ∈ E, e ≤ L) (y : ℕ → ℝ) {ρ : ℂ}
    (hρ : ρ ∈ zetaZeroConfig.carrier) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN2 : 2 ≤ N)
    (hLN : 2 * L ≤ N) (hcN : c ≤ N) (hτ : |ρ.im| ≤ Real.pi * (N / L : ℕ)) :
    ‖((Real.log N / c : ℝ) : ℂ) * bulkLedger zetaZeroConfig φ E y c N ρ -
        (zetaZeroConfig.mult ρ : ℂ) * (atomFactor φ c N ρ *
          (((poleCoefficient E y ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))))‖ ≤
      zetaZeroConfig.mult ρ * (Real.exp 1 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)) *
        ((|poleCoefficient E y| * packetConstGrid E y * (1 / ‖ρ‖ + 1 / ‖1 - ρ‖) +
          packetConstGrid E y ^ 2 / N) / N) := by
  obtain ⟨hζ, hβ0, hβ1⟩ : riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 := ⟨hρ.1, hρ.2.1, hρ.2.2⟩
  have hz1 : riemannZeta (1 - ρ) = 0 :=
    RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hζ hβ0 hβ1
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hρ0 : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hβ0; exact lt_irrefl 0 hβ0
  have hρ1 : (1 : ℂ) - ρ ≠ 0 := fun h => by
    have : ρ = 1 := by linear_combination -h
    rw [this, Complex.one_re] at hβ1; exact lt_irrefl 1 hβ1
  rw [log_div_mul_bulkLedger zetaZeroConfig hφ hφc hφ2 E y hc (by omega) ρ]
  set A := atomFactor φ c N ρ with hA
  set D₁ := dirichletPoly N (packetWeights E y N) (gammaOf ρ) with hD₁
  set D₂ := dirichletPoly N (packetWeights E y N) (gammaOf (1 - ρ)) with hD₂
  set r : ℂ := ((Real.sqrt (Real.log N) : ℝ) : ℂ) with hr
  set y₁ := poleCoefficient E y with hy₁
  set P := packetConstGrid E y with hPdef
  have hP0 : 0 ≤ P := packetConstGrid_nonneg E y
  have hsplit : (zetaZeroConfig.mult ρ : ℂ) * (paperFT (cx φ) (((c / N : ℝ) : ℂ) * gammaOf ρ) *
        conj (paperFT (cx φ) (((c / N : ℝ) : ℂ) * conj (gammaOf ρ)))) /
        ((∫ u, φ u ^ 2 : ℝ) : ℂ) * (((Real.log N / N : ℝ) : ℂ) * (D₁ * D₂)) -
      (zetaZeroConfig.mult ρ : ℂ) * (A * (((y₁ ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ)))) =
      (zetaZeroConfig.mult ρ : ℂ) * A *
        ((r * D₁) * (r * D₂) / ((N : ℝ) : ℂ) - ((y₁ ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))) := by
    have hrr : r * r = ((Real.log N : ℝ) : ℂ) := by
      rw [hr, ← Complex.ofReal_mul, Real.mul_self_sqrt hlog.le]
    have hNC : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
    rw [hA]
    unfold atomFactor
    rw [show (r * D₁) * (r * D₂) = (r * r) * (D₁ * D₂) by ring, hrr]
    push_cast
    ring
  rw [hsplit, norm_mul, norm_mul, Complex.norm_natCast]
  -- the atom factor
  have hA_le := norm_atomFactor_le hφ hφsupp hφ2 hc hcN hβ0 hβ1
  -- the ledger factor via the product formula
  set H₁ : ℂ := (y₁ : ℂ) * (((N : ℝ) : ℂ) ^ ρ / ρ) with hH₁
  set H₂ : ℂ := (y₁ : ℂ) * (((N : ℝ) : ℂ) ^ (1 - ρ) / (1 - ρ)) with hH₂
  have hNC : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  have hHH : H₁ * H₂ = ((N : ℝ) : ℂ) * (((y₁ ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))) := by
    have hpow : ((N : ℝ) : ℂ) ^ ρ * ((N : ℝ) : ℂ) ^ (1 - ρ) = ((N : ℝ) : ℂ) := by
      rw [← Complex.cpow_add _ _ hNC, show ρ + (1 - ρ) = 1 by ring, Complex.cpow_one]
    rw [hH₁, hH₂]
    push_cast
    field_simp
    linear_combination (y₁ : ℂ) ^ 2 * hpow
  rw [mul_div_sub_eq hNC hHH]
  -- the remainders of the two Dirichlet factors
  have hX₁ : ‖r * D₁ - H₁‖ ≤ P * (N : ℝ) ^ (ρ.re - 1) :=
    norm_dirichletPoly_packet_sub_pole_le_grid hβ0 hβ1 hz1 hE hL y hLN hτ hlog
  have hs1 : 0 < (1 - ρ).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hs2 : (1 - ρ).re < 1 := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hz2 : riemannZeta (1 - (1 - ρ)) = 0 := by rw [sub_sub_cancel]; exact hζ
  have hτ2 : |(1 - ρ).im| ≤ Real.pi * (N / L : ℕ) := by
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using hτ
  have hX₂ : ‖r * D₂ - H₂‖ ≤ P * (N : ℝ) ^ ((1 - ρ).re - 1) :=
    norm_dirichletPoly_packet_sub_pole_le_grid hs1 hs2 hz2 hE hL y hLN hτ2 hlog
  have hre2 : (1 - ρ).re - 1 = -ρ.re := by simp only [Complex.sub_re, Complex.one_re]; ring
  rw [hre2] at hX₂
  have hNρ : ‖((N : ℝ) : ℂ) ^ ρ‖ = (N : ℝ) ^ ρ.re := Complex.norm_cpow_eq_rpow_re_of_pos hN0 ρ
  have hNρ' : ‖((N : ℝ) : ℂ) ^ (1 - ρ)‖ = (N : ℝ) ^ (1 - ρ.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN0]
    simp only [Complex.sub_re, Complex.one_re]
  have hH₁n : ‖H₁‖ = |y₁| * (N : ℝ) ^ ρ.re / ‖ρ‖ := by
    rw [hH₁, norm_mul, norm_div, hNρ, Complex.norm_real, Real.norm_eq_abs]; ring
  have hH₂n : ‖H₂‖ = |y₁| * (N : ℝ) ^ (1 - ρ.re) / ‖1 - ρ‖ := by
    rw [hH₂, norm_mul, norm_div, hNρ', Complex.norm_real, Real.norm_eq_abs]; ring
  have hρn : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ0
  have hρn' : 0 < ‖1 - ρ‖ := norm_pos_iff.mpr hρ1
  have e1 : (N : ℝ) ^ ρ.re * (N : ℝ) ^ (-ρ.re) = 1 := by
    rw [← Real.rpow_add hN0, add_neg_cancel, Real.rpow_zero]
  have e2 : (N : ℝ) ^ (ρ.re - 1) * (N : ℝ) ^ (1 - ρ.re) = 1 := by
    rw [← Real.rpow_add hN0, show ρ.re - 1 + (1 - ρ.re) = 0 by ring, Real.rpow_zero]
  have e3 : (N : ℝ) ^ (ρ.re - 1) * (N : ℝ) ^ (-ρ.re) = 1 / N := by
    rw [← Real.rpow_add hN0, show ρ.re - 1 + -ρ.re = -1 by ring, Real.rpow_neg_one, one_div]
  have hNa : 0 ≤ (N : ℝ) ^ ρ.re := by positivity
  have hNb : 0 ≤ (N : ℝ) ^ (1 - ρ.re) := by positivity
  have hNc : 0 ≤ (N : ℝ) ^ (ρ.re - 1) := by positivity
  have hNd : 0 ≤ (N : ℝ) ^ (-ρ.re) := by positivity
  have t1 : ‖H₁ * (r * D₂ - H₂)‖ ≤ |y₁| * P * (1 / ‖ρ‖) := by
    rw [norm_mul, hH₁n]
    calc |y₁| * (N : ℝ) ^ ρ.re / ‖ρ‖ * ‖r * D₂ - H₂‖
        ≤ |y₁| * (N : ℝ) ^ ρ.re / ‖ρ‖ * (P * (N : ℝ) ^ (-ρ.re)) :=
          mul_le_mul_of_nonneg_left hX₂ (by positivity)
      _ = |y₁| * P * ((N : ℝ) ^ ρ.re * (N : ℝ) ^ (-ρ.re)) * (1 / ‖ρ‖) := by ring
      _ = |y₁| * P * (1 / ‖ρ‖) := by rw [e1, mul_one]
  have t2 : ‖(r * D₁ - H₁) * H₂‖ ≤ |y₁| * P * (1 / ‖1 - ρ‖) := by
    rw [norm_mul, hH₂n]
    calc ‖r * D₁ - H₁‖ * (|y₁| * (N : ℝ) ^ (1 - ρ.re) / ‖1 - ρ‖)
        ≤ (P * (N : ℝ) ^ (ρ.re - 1)) * (|y₁| * (N : ℝ) ^ (1 - ρ.re) / ‖1 - ρ‖) :=
          mul_le_mul_of_nonneg_right hX₁ (by positivity)
      _ = |y₁| * P * ((N : ℝ) ^ (ρ.re - 1) * (N : ℝ) ^ (1 - ρ.re)) * (1 / ‖1 - ρ‖) := by ring
      _ = |y₁| * P * (1 / ‖1 - ρ‖) := by rw [e2, mul_one]
  have t3 : ‖(r * D₁ - H₁) * (r * D₂ - H₂)‖ ≤ P ^ 2 / N := by
    rw [norm_mul]
    calc ‖r * D₁ - H₁‖ * ‖r * D₂ - H₂‖ ≤ (P * (N : ℝ) ^ (ρ.re - 1)) * (P * (N : ℝ) ^ (-ρ.re)) :=
          mul_le_mul hX₁ hX₂ (norm_nonneg _) (by positivity)
      _ = P ^ 2 * ((N : ℝ) ^ (ρ.re - 1) * (N : ℝ) ^ (-ρ.re)) := by ring
      _ = P ^ 2 / N := by rw [e3]; ring
  have hfac : ‖(H₁ * (r * D₂ - H₂) + (r * D₁ - H₁) * H₂ + (r * D₁ - H₁) * (r * D₂ - H₂)) /
      ((N : ℝ) : ℂ)‖ ≤ (|y₁| * P * (1 / ‖ρ‖ + 1 / ‖1 - ρ‖) + P ^ 2 / N) / N := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN0]
    refine div_le_div_of_nonneg_right ?_ hN0.le
    calc ‖H₁ * (r * D₂ - H₂) + (r * D₁ - H₁) * H₂ + (r * D₁ - H₁) * (r * D₂ - H₂)‖
        ≤ ‖H₁ * (r * D₂ - H₂)‖ + ‖(r * D₁ - H₁) * H₂‖ + ‖(r * D₁ - H₁) * (r * D₂ - H₂)‖ :=
          (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ |y₁| * P * (1 / ‖ρ‖) + |y₁| * P * (1 / ‖1 - ρ‖) + P ^ 2 / N := by gcongr
      _ = _ := by ring
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  calc (zetaZeroConfig.mult ρ : ℝ) * ‖A‖ * ‖(H₁ * (r * D₂ - H₂) + (r * D₁ - H₁) * H₂ +
        (r * D₁ - H₁) * (r * D₂ - H₂)) / ((N : ℝ) : ℂ)‖
      ≤ (zetaZeroConfig.mult ρ : ℝ) * (Real.exp 1 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)) *
          ((|y₁| * P * (1 / ‖ρ‖ + 1 / ‖1 - ρ‖) + P ^ 2 / N) / N) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hA_le hm) hfac (norm_nonneg _)
          (mul_nonneg hm (by positivity))

/-! ### All zeros below the grid -/

/-- Dominated convergence for growing windows of zeros: if `g_N(ρ) → G(ρ)` with a summable
majorant, then `Σ_{|γ| ≤ T_N} g_N(ρ) → Σ_ρ G(ρ)` for `T_N → ∞`. -/
theorem tendsto_sum_lowZeros_of_dominated {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    {g : ℕ → ℂ → ℂ} {G : ℂ → ℂ} {b : ℂ → ℝ}
    (hb : Summable fun ρ : zetaZeroConfig.carrier => b ρ)
    (hbound : ∀ᶠ N in atTop, ∀ ρ ∈ zetaZeroConfig.carrier, ‖g N ρ‖ ≤ b ρ)
    (hlim : ∀ ρ ∈ zetaZeroConfig.carrier, Tendsto (fun N => g N ρ) atTop (𝓝 (G ρ))) :
    Tendsto (fun N => ∑ ρ ∈ (RHTower.lowZeros_finite (T N)).toFinset, g N ρ) atTop
      (𝓝 (∑' ρ : zetaZeroConfig.carrier, G ρ)) := by
  classical
  have hl := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun N (ρ : zetaZeroConfig.carrier) => if |(ρ : ℂ).im| ≤ T N then g N ρ else 0)
    (g := fun ρ : zetaZeroConfig.carrier => G ρ) (bound := fun ρ => b ρ) hb
    (fun ρ => (hlim ρ ρ.2).congr' (by
      filter_upwards [hT.eventually (eventually_ge_atTop |(ρ : ℂ).im|)] with N hN
      rw [if_pos hN]))
    (hbound.mono fun N hN ρ => by
      split_ifs
      · exact hN ρ ρ.2
      · rw [norm_zero]; exact (norm_nonneg _).trans (hN ρ ρ.2))
  refine hl.congr fun N => ?_
  set s := (RHTower.lowZeros_finite (T N)).toFinset with hs
  rw [tsum_eq_sum (s := s.subtype (· ∈ zetaZeroConfig.carrier))]
  · rw [show (∑ ρ ∈ s.subtype (· ∈ zetaZeroConfig.carrier),
        if |(ρ : ℂ).im| ≤ T N then g N ρ else 0) =
        ∑ ρ ∈ s.subtype (· ∈ zetaZeroConfig.carrier), g N ρ from
      sum_congr rfl fun ρ hρ => by
        rw [Finset.mem_subtype, hs, (RHTower.lowZeros_finite _).mem_toFinset] at hρ
        rw [if_pos hρ.2]]
    rw [Finset.sum_subtype_eq_sum_filter (f := fun z : ℂ => g N z)]
    rw [Finset.filter_true_of_mem fun z hz => by
      rw [hs, (RHTower.lowZeros_finite _).mem_toFinset] at hz; exact hz.1]
  · intro ρ hρ
    rw [Finset.mem_subtype, hs, (RHTower.lowZeros_finite _).mem_toFinset] at hρ
    rw [if_neg fun h => hρ ⟨ρ.2, h⟩]

/-- A window of zeros carries at most the full sum of a nonnegative summable weight. -/
theorem sum_lowZeros_le_tsum (T : ℝ) {b : ℂ → ℝ}
    (hb0 : ∀ ρ ∈ zetaZeroConfig.carrier, 0 ≤ b ρ)
    (hb : Summable fun ρ : zetaZeroConfig.carrier => b ρ) :
    ∑ ρ ∈ (RHTower.lowZeros_finite T).toFinset, b ρ ≤ ∑' ρ : zetaZeroConfig.carrier, b ρ := by
  classical
  set s := (RHTower.lowZeros_finite T).toFinset with hs
  have hsub : ∀ z ∈ s, z ∈ zetaZeroConfig.carrier := fun z hz => by
    rw [hs, (RHTower.lowZeros_finite _).mem_toFinset] at hz; exact hz.1
  rw [← Finset.filter_true_of_mem hsub, ← Finset.sum_subtype_eq_sum_filter]
  exact hb.sum_le_tsum _ (fun ρ _ => hb0 ρ ρ.2)

/-- The weight of a zero: `1/|ρ| + 1/|1 − ρ| ≤ 3/√N + 6√N/|ρ(1 − ρ)|`. -/
theorem inv_norm_add_inv_norm_le {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) {N : ℝ}
    (hN : 0 < N) :
    1 / ‖ρ‖ + 1 / ‖1 - ρ‖ ≤ 3 / Real.sqrt N + 6 * Real.sqrt N * (1 / ‖ρ * (1 - ρ)‖) := by
  obtain ⟨h3, -⟩ := three_lt_norm_of_mem hρ
  have hρ0 : 0 < ‖ρ‖ := by linarith
  have h1ρ : ‖ρ‖ / 2 ≤ ‖1 - ρ‖ := by
    have := norm_sub_norm_le ρ 1
    rw [norm_one, norm_sub_rev] at this
    linarith
  have h1ρu : ‖1 - ρ‖ ≤ 2 * ‖ρ‖ := by
    have := norm_sub_le (1 : ℂ) ρ
    rw [norm_one] at this
    linarith
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hprod : ‖ρ * (1 - ρ)‖ ≤ 2 * ‖ρ‖ ^ 2 := by
    rw [norm_mul]; nlinarith [norm_nonneg (1 - ρ)]
  have hP : 0 < ‖ρ * (1 - ρ)‖ := by
    rw [norm_mul]; exact mul_pos hρ0 (by linarith)
  -- `1/|1 − ρ| ≤ 2/|ρ|`
  have hb1 : 1 / ‖1 - ρ‖ ≤ 2 * (1 / ‖ρ‖) := by
    rw [mul_one_div, div_le_div_iff₀ (by linarith) hρ0]; linarith
  -- `1/|ρ| ≤ 1/√N + √N/|ρ|²`
  have hb2 : 1 / ‖ρ‖ ≤ 1 / Real.sqrt N + Real.sqrt N * (2 * (1 / ‖ρ * (1 - ρ)‖)) := by
    have hq : 1 / ‖ρ‖ ^ 2 ≤ 2 * (1 / ‖ρ * (1 - ρ)‖) := by
      rw [div_le_iff₀ (by positivity)]
      rw [show 2 * (1 / ‖ρ * (1 - ρ)‖) * ‖ρ‖ ^ 2 = 2 * ‖ρ‖ ^ 2 / ‖ρ * (1 - ρ)‖ by ring,
        le_div_iff₀ hP]
      linarith
    rcases le_or_gt (Real.sqrt N) ‖ρ‖ with h | h
    · have : 1 / ‖ρ‖ ≤ 1 / Real.sqrt N := one_div_le_one_div_of_le hs h
      have : 0 ≤ Real.sqrt N * (2 * (1 / ‖ρ * (1 - ρ)‖)) := by positivity
      linarith
    · have : 1 / ‖ρ‖ ≤ Real.sqrt N * (1 / ‖ρ‖ ^ 2) := by
        rw [mul_one_div, le_div_iff₀ (by positivity), one_div, pow_two, ← mul_assoc,
          inv_mul_cancel₀ hρ0.ne', one_mul]
        exact h.le
      have : 0 ≤ 1 / Real.sqrt N := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hq hs.le]
  have e1 : 3 / Real.sqrt N = 3 * (1 / Real.sqrt N) := by ring
  have e2 : 6 * Real.sqrt N * (1 / ‖ρ * (1 - ρ)‖) =
      3 * (Real.sqrt N * (2 * (1 / ‖ρ * (1 - ρ)‖))) := by ring
  rw [e1, e2]
  linarith

/-- `log²(λN)/√N → 0`. -/
theorem tendsto_log_sq_div_sqrt {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun N : ℕ => Real.log (lam * N) ^ 2 / Real.sqrt N) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x ^ (2 : ℝ) / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have h2 : Tendsto (fun N : ℕ => lam * (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hlam
  have h3 := (h1.comp h2).const_mul (Real.sqrt lam)
  rw [mul_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [Function.comp_apply]
  rw [Real.rpow_two, ← Real.sqrt_eq_rpow, Real.sqrt_mul hlam.le]
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  field_simp

/-- The atom factor of a fixed point tends to `(∫φ)²/∫φ²` when `c_N/N → 0`. -/
theorem tendsto_atomFactor {φ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    {c : ℕ → ℝ} (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) (ρ : ℂ) :
    Tendsto (fun N : ℕ => atomFactor φ (c N) N ρ) atTop
      (𝓝 (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ)) := by
  have hF : Continuous (paperFT (cx φ)) :=
    (RHTower.EvenSector.differentiable_paperFT_of_compact (Complex.continuous_ofReal.comp hφ)
      (hφc.comp_left Complex.ofReal_zero)).continuous
  have hw : Tendsto (fun N : ℕ => ((c N / N : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa using hcN.ofReal
  have h1 : Tendsto (fun N : ℕ => paperFT (cx φ) (((c N / N : ℝ) : ℂ) * gammaOf ρ)) atTop
      (𝓝 (paperFT (cx φ) 0)) := by
    have := hw.mul_const (gammaOf ρ)
    rw [zero_mul] at this
    exact (hF.tendsto 0).comp this
  have h2 : Tendsto (fun N : ℕ => conj (paperFT (cx φ) (((c N / N : ℝ) : ℂ) * conj (gammaOf ρ))))
      atTop (𝓝 (conj (paperFT (cx φ) 0))) := by
    have := hw.mul_const (conj (gammaOf ρ))
    rw [zero_mul] at this
    exact (Complex.continuous_conj.tendsto _).comp ((hF.tendsto 0).comp this)
  have hlim := (h1.mul h2).div_const ((∫ u, φ u ^ 2 : ℝ) : ℂ)
  rw [paperFT_cx_zero, Complex.conj_ofReal] at hlim
  have e : ((((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ)) : ℂ) =
      ((∫ u, φ u : ℝ) : ℂ) * ((∫ u, φ u : ℝ) : ℂ) / ((∫ u, φ u ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [e]
  exact hlim

/-- The pole term of one zero, `m_ρ a_N(ρ) y_1²/(ρ(1 − ρ))`. -/
def poleLedgerTerm (φ : ℝ → ℝ) (E : Finset ℕ) (y : ℕ → ℝ) (c : ℝ) (N : ℕ) (ρ : ℂ) : ℂ :=
  (zetaZeroConfig.mult ρ : ℂ) * (atomFactor φ c N ρ *
    (((poleCoefficient E y ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))))

/-- Below the resolution the pole term of a zero is dominated by `e I₁²/∫φ² · y_1² m_ρ/|ρ(1 − ρ)|`. -/
theorem norm_poleLedgerTerm_le {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) (E : Finset ℕ)
    (y : ℕ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hcN : c ≤ N) {ρ : ℂ} (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) :
    ‖poleLedgerTerm φ E y c N ρ‖ ≤ Real.exp 1 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2) *
      poleCoefficient E y ^ 2 * ‖(zetaZeroConfig.mult ρ : ℂ) / (ρ * (1 - ρ))‖ := by
  have hA := norm_atomFactor_le hφ hφsupp hφ2 hc hcN hρ0 hρ1
  unfold poleLedgerTerm
  rw [norm_mul, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_div, Complex.norm_natCast]
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  have hq : 0 ≤ poleCoefficient E y ^ 2 / ‖ρ * (1 - ρ)‖ := by positivity
  calc (zetaZeroConfig.mult ρ : ℝ) * (‖atomFactor φ c N ρ‖ *
        (poleCoefficient E y ^ 2 / ‖ρ * (1 - ρ)‖))
      ≤ (zetaZeroConfig.mult ρ : ℝ) * (Real.exp 1 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2) *
          (poleCoefficient E y ^ 2 / ‖ρ * (1 - ρ)‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA hq) hm
    _ = _ := by ring

/-- At a fixed zero the pole term tends to `κ y_1² m_ρ/(ρ(1 − ρ))` when `c_N/N → 0`. -/
theorem tendsto_poleLedgerTerm {φ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (E : Finset ℕ) (y : ℕ → ℝ) {c : ℕ → ℝ} (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0))
    (ρ : ℂ) :
    Tendsto (fun N : ℕ => poleLedgerTerm φ E y (c N) N ρ) atTop
      (𝓝 ((((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) * ((poleCoefficient E y ^ 2 : ℝ) : ℂ) *
        ((zetaZeroConfig.mult ρ : ℂ) / (ρ * (1 - ρ))))) := by
  have h := ((tendsto_atomFactor hφ hφc hcN ρ).mul_const
    (((poleCoefficient E y ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ)))).const_mul (zetaZeroConfig.mult ρ : ℂ)
  have e : (zetaZeroConfig.mult ρ : ℂ) * ((((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) *
      (((poleCoefficient E y ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ)))) =
      (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) * ((poleCoefficient E y ^ 2 : ℝ) : ℂ) *
        ((zetaZeroConfig.mult ρ : ℂ) / (ρ * (1 - ρ))) := by ring
  rw [e] at h
  exact h

/-- **The pole terms of all zeros below a growing height** tend to the archimedean genus
`κ y_1² Σ_ρ m_ρ/(ρ(1 − ρ))`: dominated convergence, since the atom factor is bounded below the
resolution and tends to `κ` at every fixed zero. -/
theorem tendsto_sum_poleLedgerTerm {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) (E : Finset ℕ)
    (y : ℕ → ℝ) {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) {c : ℕ → ℝ} (hc0 : ∀ N, 0 < c N)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑ ρ ∈ (RHTower.lowZeros_finite (T N)).toFinset,
      poleLedgerTerm φ E y (c N) N ρ) atTop
      (𝓝 ((((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) * ((poleCoefficient E y ^ 2 : ℝ) : ℂ) *
        ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) / ((ρ : ℂ) * (1 - ρ)))) := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hcle : ∀ᶠ N : ℕ in atTop, c N ≤ N := by
    filter_upwards [hcN.eventually (gt_mem_nhds one_pos), eventually_ge_atTop 1] with N h hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    exact ((div_lt_one hN0).mp h).le
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ ρ ∈ zetaZeroConfig.carrier,
      ‖poleLedgerTerm φ E y (c N) N ρ‖ ≤ Real.exp 1 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2) *
        poleCoefficient E y ^ 2 * ‖(zetaZeroConfig.mult ρ : ℂ) / (ρ * (1 - ρ))‖ := by
    filter_upwards [hcle] with N hN ρ hρ
    obtain ⟨-, hβ0, hβ1⟩ : riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 := ⟨hρ.1, hρ.2.1, hρ.2.2⟩
    exact norm_poleLedgerTerm_le hφ hφsupp hφ2 E y (hc0 N) hN hβ0 hβ1
  have h := tendsto_sum_lowZeros_of_dominated hT
    (g := fun N ρ => poleLedgerTerm φ E y (c N) N ρ)
    (G := fun ρ => (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) *
      ((poleCoefficient E y ^ 2 : ℝ) : ℂ) * ((zetaZeroConfig.mult ρ : ℂ) / (ρ * (1 - ρ))))
    (summable_norm_mult_div.mul_left _) hbound
    (fun ρ _ => tendsto_poleLedgerTerm hφ hφc E y hcN ρ)
  rw [tsum_mul_left] at h
  exact h

/-- The remainder bound: `‖Σ_{|γ| ≤ λN} (ledger − pole term)‖ ≤ U_N` with
`U_N = C₀(|y_1|P(3Kλ log²(λN)/√N + 6S/√N) + P²Kλ log²(λN)/N)`. -/
theorem eventually_norm_sum_ledger_sub_pole_le {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {E : Finset ℕ}
    (hE : ∀ e ∈ E, 1 ≤ e) {L : ℕ} (hL1 : 1 ≤ L) (hL : ∀ e ∈ E, e ≤ L) (y : ℕ → ℝ) {lam : ℝ}
    (hlam0 : 0 < lam) (hlamL : 2 * lam * L ≤ Real.pi) {c : ℕ → ℝ} (hc0 : ∀ N, 0 < c N)
    (hcle : ∀ᶠ N : ℕ in atTop, c N ≤ N) {K T₀ : ℝ}
    (hcount : ∀ T : ℝ, T₀ ≤ T → ∑ ρ ∈ (RHTower.lowZeros_finite T).toFinset,
      (zetaZeroConfig.mult ρ : ℝ) ≤ K * (T * Real.log T ^ 2)) :
    ∀ᶠ N : ℕ in atTop, ‖∑ ρ ∈ (RHTower.lowZeros_finite (lam * N)).toFinset,
      (((Real.log N / c N : ℝ) : ℂ) * bulkLedger zetaZeroConfig φ E y (c N) N ρ -
        poleLedgerTerm φ E y (c N) N ρ)‖ ≤
      Real.exp 1 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2) *
        (|poleCoefficient E y| * packetConstGrid E y *
          (3 * K * lam * (Real.log (lam * N) ^ 2 / Real.sqrt N) +
            6 * (∑' ρ : zetaZeroConfig.carrier,
              ‖(zetaZeroConfig.mult ρ : ℂ) / ((ρ : ℂ) * (1 - ρ))‖) * (1 / Real.sqrt N)) +
          packetConstGrid E y ^ 2 * K * lam *
            ((Real.log (lam * N) ^ 2 / Real.sqrt N) * (1 / Real.sqrt N))) := by
  obtain ⟨C₀, hC₀⟩ : ∃ C : ℝ, C = Real.exp 1 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2) := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑' ρ : zetaZeroConfig.carrier,
      ‖(zetaZeroConfig.mult ρ : ℂ) / ((ρ : ℂ) * (1 - ρ))‖ := ⟨_, rfl⟩
  obtain ⟨y₁, hy₁⟩ : ∃ y₁ : ℝ, y₁ = poleCoefficient E y := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = packetConstGrid E y := ⟨_, rfl⟩
  rw [← hC₀, ← hSdef, ← hy₁, ← hPdef]
  have hC₀0 : 0 ≤ C₀ := by rw [hC₀]; positivity
  have hP0 : 0 ≤ P := hPdef ▸ packetConstGrid_nonneg E y
  have hT : Tendsto (fun N : ℕ => lam * (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hlam0
  have hT₀' : ∀ᶠ N : ℕ in atTop, T₀ ≤ lam * N := hT.eventually (eventually_ge_atTop T₀)
  filter_upwards [hcle, hT₀', eventually_ge_atTop (2 * L)] with N hcN' hTN hLN
  have hN2 : 2 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  -- the zeros below `λN` lie below the grid `π⌊N/L⌋`
  have hgrid : lam * N ≤ Real.pi * (N / L : ℕ) := by
    have hL0 : (0 : ℝ) < L := by exact_mod_cast hL1
    have h1 : (N : ℝ) / (2 * L) ≤ ((N / L : ℕ) : ℝ) := by
      have h1 := Nat.lt_div_mul_add (a := N) (b := L) (by omega)
      have h1' : (N : ℝ) < (((N / L) * L + L : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h1'
      have h2 : (2 * L : ℝ) ≤ N := by exact_mod_cast hLN
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    calc lam * N = (2 * lam * L) * ((N : ℝ) / (2 * L)) := by field_simp
      _ ≤ Real.pi * ((N / L : ℕ) : ℝ) :=
        mul_le_mul hlamL h1 (by positivity) Real.pi_pos.le
  have hterm : ∀ ρ ∈ (RHTower.lowZeros_finite (lam * N)).toFinset,
      ‖((Real.log N / c N : ℝ) : ℂ) * bulkLedger zetaZeroConfig φ E y (c N) N ρ -
        poleLedgerTerm φ E y (c N) N ρ‖ ≤
      C₀ / N * (|y₁| * P * 3 / Real.sqrt N + P ^ 2 / N) * (zetaZeroConfig.mult ρ : ℝ) +
        C₀ / N * (|y₁| * P * (6 * Real.sqrt N)) *
          ‖(zetaZeroConfig.mult ρ : ℂ) / (ρ * (1 - ρ))‖ := by
    intro ρ hρ
    rw [(RHTower.lowZeros_finite _).mem_toFinset] at hρ
    have hb := norm_log_div_mul_bulkLedger_sub_atom_le_grid hφ hφsupp hφ2 hE hL y hρ.1 (hc0 N)
      hN2 hLN hcN' (hρ.2.trans hgrid)
    rw [← hC₀, ← hy₁, ← hPdef] at hb
    have hw := inv_norm_add_inv_norm_le hρ.1 hN0
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    have hnm : ‖(zetaZeroConfig.mult ρ : ℂ) / (ρ * (1 - ρ))‖ =
        (zetaZeroConfig.mult ρ : ℝ) * (1 / ‖ρ * (1 - ρ)‖) := by
      rw [norm_div, Complex.norm_natCast]; ring
    unfold poleLedgerTerm
    rw [← hy₁]
    refine hb.trans ?_
    rw [hnm]
    have hA : 0 ≤ |y₁| * P := mul_nonneg (abs_nonneg _) hP0
    have key : |y₁| * P * (1 / ‖ρ‖ + 1 / ‖1 - ρ‖) ≤
        |y₁| * P * (3 / Real.sqrt N + 6 * Real.sqrt N * (1 / ‖ρ * (1 - ρ)‖)) :=
      mul_le_mul_of_nonneg_left hw hA
    have hC : 0 ≤ (zetaZeroConfig.mult ρ : ℝ) * C₀ / N := by positivity
    calc (zetaZeroConfig.mult ρ : ℝ) * C₀ * ((|y₁| * P * (1 / ‖ρ‖ + 1 / ‖1 - ρ‖) +
          P ^ 2 / N) / N)
        = (zetaZeroConfig.mult ρ : ℝ) * C₀ / N * (|y₁| * P * (1 / ‖ρ‖ + 1 / ‖1 - ρ‖) +
          P ^ 2 / N) := by ring
      _ ≤ (zetaZeroConfig.mult ρ : ℝ) * C₀ / N * (|y₁| * P * (3 / Real.sqrt N +
          6 * Real.sqrt N * (1 / ‖ρ * (1 - ρ)‖)) + P ^ 2 / N) :=
          mul_le_mul_of_nonneg_left (by linarith) hC
      _ = _ := by ring
  have hM1 : ∑ ρ ∈ (RHTower.lowZeros_finite (lam * N)).toFinset,
      (zetaZeroConfig.mult ρ : ℝ) ≤ K * (lam * N * Real.log (lam * N) ^ 2) := hcount _ hTN
  have hM2 : ∑ ρ ∈ (RHTower.lowZeros_finite (lam * N)).toFinset,
      ‖(zetaZeroConfig.mult ρ : ℂ) / (ρ * (1 - ρ))‖ ≤ S :=
    hSdef ▸ sum_lowZeros_le_tsum _ (fun _ _ => norm_nonneg _) summable_norm_mult_div
  refine (norm_sum_le _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have hα : 0 ≤ C₀ / N * (|y₁| * P * 3 / Real.sqrt N + P ^ 2 / N) := by positivity
  have hβ : 0 ≤ C₀ / N * (|y₁| * P * (6 * Real.sqrt N)) := by positivity
  refine (add_le_add (mul_le_mul_of_nonneg_left hM1 hα)
    (mul_le_mul_of_nonneg_left hM2 hβ)).trans (le_of_eq ?_)
  generalize Real.log (lam * N) ^ 2 = ℓ
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt N := ⟨_, rfl⟩
  have hr0 : 0 < r := hr ▸ hsN
  have hNr : (N : ℝ) = r * r := by rw [hr]; exact (Real.mul_self_sqrt hN0.le).symm
  rw [← hr, hNr]
  field_simp
  ring

/-- **The bulk is blind below its grid.** Let the conductors of the packet be `≤ L` and
`2λL ≤ π`. Along every overlap schedule with `c_N/N → 0`, all zeros of height `≤ λN` together
contribute `(c_N/log N) κ y_1² Σ_ρ m_ρ/(ρ(1 − ρ)) + o(c_N/log N)`, `κ = (∫φ)²/∫φ²`, to the
normalized complete form of the packet: the archimedean genus at the pole and nothing else. -/
theorem tendsto_sum_bulkLedger_belowGrid {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {E : Finset ℕ}
    (hE : ∀ e ∈ E, 1 ≤ e) {L : ℕ} (hL1 : 1 ≤ L) (hL : ∀ e ∈ E, e ≤ L) (y : ℕ → ℝ) {lam : ℝ}
    (hlam0 : 0 < lam) (hlamL : 2 * lam * L ≤ Real.pi) {c : ℕ → ℝ} (hc0 : ∀ N, 0 < c N)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑ ρ ∈ (RHTower.lowZeros_finite (lam * N)).toFinset,
      ((Real.log N / c N : ℝ) : ℂ) * bulkLedger zetaZeroConfig φ E y (c N) N ρ) atTop
      (𝓝 ((((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) * ((poleCoefficient E y ^ 2 : ℝ) : ℂ) *
        ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) / ((ρ : ℂ) * (1 - ρ)))) := by
  have hT : Tendsto (fun N : ℕ => lam * (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hlam0
  have hcle : ∀ᶠ N : ℕ in atTop, c N ≤ N := by
    filter_upwards [hcN.eventually (gt_mem_nhds one_pos), eventually_ge_atTop 1] with N h hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    exact ((div_lt_one hN0).mp h).le
  obtain ⟨K, T₀, -, -, hcount⟩ := exists_sum_mult_lowZeros_le
  have hpole := tendsto_sum_poleLedgerTerm hφ hφsupp hφ2 E y hT hc0 hcN
  have herr := eventually_norm_sum_ledger_sub_pole_le hφ hφsupp hφ2 hE hL1 hL y hlam0 hlamL hc0
    hcle hcount
  have hinvsqrt : Tendsto (fun N : ℕ => 1 / Real.sqrt N) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    refine this.congr fun N => ?_
    simp [one_div]
  have hL2 := tendsto_log_sq_div_sqrt hlam0
  have hU := ((((hL2.const_mul (3 * K * lam)).add (hinvsqrt.const_mul
    (6 * ∑' ρ : zetaZeroConfig.carrier, ‖(zetaZeroConfig.mult ρ : ℂ) / ((ρ : ℂ) * (1 - ρ))‖))).const_mul
      (|poleCoefficient E y| * packetConstGrid E y)).add
        ((hL2.mul hinvsqrt).const_mul (packetConstGrid E y ^ 2 * K * lam))).const_mul
          (Real.exp 1 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2))
  simp only [mul_zero, add_zero] at hU
  have h0 := squeeze_zero_norm' herr hU
  have hsum := hpole.add h0
  rw [add_zero] at hsum
  refine hsum.congr fun N => ?_
  rw [← sum_add_distrib]
  exact sum_congr rfl fun ρ _ => by ring

/-- **Pole-free packets are blind below their grid**: for `y_1 = 0`, all zeros of height `≤ λN`
together contribute `o(c_N/log N)`. -/
theorem tendsto_sum_bulkLedger_belowGrid_poleFree {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {E : Finset ℕ}
    (hE : ∀ e ∈ E, 1 ≤ e) {L : ℕ} (hL1 : 1 ≤ L) (hL : ∀ e ∈ E, e ≤ L) {y : ℕ → ℝ}
    (hpole : poleCoefficient E y = 0) {lam : ℝ} (hlam0 : 0 < lam) (hlamL : 2 * lam * L ≤ Real.pi)
    {c : ℕ → ℝ} (hc0 : ∀ N, 0 < c N) (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑ ρ ∈ (RHTower.lowZeros_finite (lam * N)).toFinset,
      ((Real.log N / c N : ℝ) : ℂ) * bulkLedger zetaZeroConfig φ E y (c N) N ρ) atTop (𝓝 0) := by
  have h := tendsto_sum_bulkLedger_belowGrid hφ hφsupp hφ2 hE hL1 hL y hlam0 hlamL hc0 hcN
  rw [hpole] at h
  simpa using h

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
