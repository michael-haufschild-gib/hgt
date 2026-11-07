import GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.EveryHeckeOperatorIsDiagonalOnEisenstein
import GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.HeckeWordsHaveThePoissonSpectralMeasure

/-!
# The whole Hecke algebra has the Poisson spectral measure on a resonant state

Let `t_Y = Λ^Y E_u` be a truncated resonant state, `msA u = 0`, `Re u < 0`, and `T_n` the classical
Hecke operator of index `n` (`heckeN`). For every `n, m ≥ 1` and `Y ≥ n, m`,

`⟨T_n t_Y, T_m t_Y⟩_𝒟 = ‖t_Y‖² ∫ P_{−Re u}(t − Im u) W_{it}(n) W_{it}(m) dt`
(`integral_heckeN_mul_conj_heckeN`), so

* `⟨T_n t_Y, t_Y⟩ = μ_n(u) ‖t_Y‖²` for every `n`, not only squarefree ones
  (`integral_heckeN_mul_conj_eq_resonantHeckeMoment`), and
* `⟨T_n t_Y, T_m t_Y⟩ = ‖t_Y‖² Σ_{d ∣ (n, m)} μ_{nm/d²}(u)`, the Hecke multiplication law on the
  physical state (`integral_heckeN_mul_conj_heckeN_eq_sum_gcd`).

**Mechanism.** At a resonance the constant term is one Weyl power `B y^{½−u}`. A representative
`(a, d)` of determinant `n` moves the height to `ay/d`, so the truncation at `Y` becomes a
truncation at `Yd/a` with coefficient `(d/a)^u`; with `T_n E_u = W_u(n) E_u` this gives
`T_n t_Y = Σ_{ad = n} (d/a)^u t_{Yd/a}` (`heckeN_truncatedLeg`), a sum of translations of the
stationary cutoff family by `log(d/a)`. Its covariance is the Fourier transform of the Poisson
kernel, and `Σ_{ad=n} (d/a)^{it} = W_{it}(n)`.
-/

set_option autoImplicit false

open Complex Filter MeasureTheory Set ModularGroup Finset
open scoped ComplexConjugate UpperHalfPlane
open GaloisForLFunctions.HTGeometry RHTower
open GaloisForLFunctions.ArithmeticCorrespondencePositivity

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

noncomputable section

/-! ### Representatives as logarithmic shifts -/

/-- The logarithmic shift `log d − log a` of a representative `(a, d)`. -/
def representativeShift (ad : ℕ × ℕ) : ℝ := Real.log ad.2 - Real.log ad.1

theorem exp_representativeShift {n : ℕ} {ad : ℕ × ℕ} (had : ad ∈ n.divisorsAntidiagonal) :
    Real.exp (representativeShift ad) = (ad.2 : ℝ) / ad.1 := by
  obtain ⟨ha, hd⟩ := pos_of_mem_divisorsAntidiagonal had
  have hA : (0 : ℝ) < ad.1 := by exact_mod_cast ha
  have hD : (0 : ℝ) < ad.2 := by exact_mod_cast hd
  rw [representativeShift, Real.exp_sub, Real.exp_log hA, Real.exp_log hD]

theorem natCast_cpow_eq_cexp {k : ℕ} (hk : 0 < k) (s : ℂ) :
    (k : ℂ) ^ s = cexp (s * (Real.log k : ℂ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [Complex.cpow_def_of_ne_zero hkC, show (k : ℂ) = ((k : ℝ) : ℂ) by norm_cast,
    ← Complex.ofReal_log hkR.le, mul_comm]

theorem cexp_mul_representativeShift (s : ℂ) {n : ℕ} {ad : ℕ × ℕ}
    (had : ad ∈ n.divisorsAntidiagonal) :
    cexp (s * (representativeShift ad : ℂ)) = (ad.2 : ℂ) ^ s * (ad.1 : ℂ) ^ (-s) := by
  obtain ⟨ha, hd⟩ := pos_of_mem_divisorsAntidiagonal had
  rw [natCast_cpow_eq_cexp hd, natCast_cpow_eq_cexp ha, ← Complex.exp_add, representativeShift]
  congr 1
  push_cast
  ring

/-- `Σ_{ad = n} (d/a)^s = W_s(n)`. -/
theorem sum_cexp_representativeShift (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    ∑ ad ∈ n.divisorsAntidiagonal, cexp (s * (representativeShift ad : ℂ)) =
      whittakerCoeff s n := by
  rw [whittakerCoeff_eq_sum_antidiagonal s hn,
    sum_congr rfl fun ad had => cexp_mul_representativeShift s had]
  refine sum_nbij Prod.swap (fun x hx => ?_) (fun _ _ _ _ h => Prod.swap_injective h)
    (fun y hy => ⟨y.swap, ?_, Prod.swap_swap y⟩) (fun _ _ => rfl)
  · obtain ⟨hprod, hne⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    exact Nat.mem_divisorsAntidiagonal.mpr ⟨by simpa [mul_comm] using hprod, hne⟩
  · obtain ⟨hprod, hne⟩ := Nat.mem_divisorsAntidiagonal.mp hy
    exact Nat.mem_divisorsAntidiagonal.mpr ⟨by simpa [mul_comm] using hprod, hne⟩

/-- The Whittaker eigenvalue is even in the parameter. -/
theorem whittakerCoeff_neg (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    whittakerCoeff (-s) n = whittakerCoeff s n := by
  rw [← sum_cexp_representativeShift s hn, whittakerCoeff_eq_sum_antidiagonal _ hn, neg_neg]
  refine sum_congr rfl fun ad had => ?_
  rw [cexp_mul_representativeShift s had, mul_comm]

/-- The normalization of a representative: `(ad)^{-1/2} d = e^{ℓ/2}`, `ℓ = log d − log a`. -/
theorem sqrt_inv_mul_eq_exp {a d : ℕ} (ha : 0 < a) (hd : 0 < d) :
    (Real.sqrt ((a * d : ℕ) : ℝ))⁻¹ * d = Real.exp ((Real.log d - Real.log a) / 2) := by
  have hA : (0 : ℝ) < a := by exact_mod_cast ha
  have hD : (0 : ℝ) < d := by exact_mod_cast hd
  have hsA : 0 < Real.sqrt a := Real.sqrt_pos.mpr hA
  have hsD : 0 < Real.sqrt d := Real.sqrt_pos.mpr hD
  have h1 : Real.sqrt a = Real.exp (Real.log a / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hA]
    ring_nf
  have h2 : Real.sqrt d = Real.exp (Real.log d / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hD]
    ring_nf
  calc (Real.sqrt ((a * d : ℕ) : ℝ))⁻¹ * d
      = (Real.sqrt a * Real.sqrt d)⁻¹ * (Real.sqrt d * Real.sqrt d) := by
        rw [Nat.cast_mul, Real.sqrt_mul hA.le, Real.mul_self_sqrt hD.le]
    _ = Real.sqrt d / Real.sqrt a := by field_simp
    _ = Real.exp (Real.log d / 2) / Real.exp (Real.log a / 2) := by rw [h1, h2]
    _ = Real.exp ((Real.log d - Real.log a) / 2) := by rw [← Real.exp_sub]; ring_nf

/-- One representative on the Weyl power `y^{½−u}`: the coefficient `(d/a)^u`. -/
theorem representative_weyl_power (u : ℂ) {n : ℕ} {ad : ℕ × ℕ}
    (had : ad ∈ n.divisorsAntidiagonal) {y : ℝ} (hy : 0 < y) :
    (((Real.sqrt n)⁻¹ : ℝ) : ℂ) * ((ad.2 : ℂ) *
        ((((ad.1 : ℝ) * y / (ad.2 : ℝ) : ℝ) : ℂ) ^ (1 / 2 - u))) =
      cexp (u * (representativeShift ad : ℂ)) * (y : ℂ) ^ (1 / 2 - u) := by
  obtain ⟨ha, hd⟩ := pos_of_mem_divisorsAntidiagonal had
  have hprod := (Nat.mem_divisorsAntidiagonal.mp had).1
  have hA : (0 : ℝ) < ad.1 := by exact_mod_cast ha
  have hD : (0 : ℝ) < ad.2 := by exact_mod_cast hd
  have hy' : (ad.1 : ℝ) * y / ad.2 = y * Real.exp (-representativeShift ad) := by
    rw [Real.exp_neg, exp_representativeShift had]
    field_simp
  have hnorm := sqrt_inv_mul_eq_exp ha hd
  rw [hprod] at hnorm
  rw [hy', ofReal_mul_exp_cpow hy, ← mul_assoc, ← mul_assoc,
    show (((Real.sqrt n)⁻¹ : ℝ) : ℂ) * (ad.2 : ℂ) = (((Real.sqrt n)⁻¹ * ad.2 : ℝ) : ℂ) by
      push_cast; ring,
    hnorm, Complex.ofReal_exp]
  have hexp : cexp (((Real.log ad.2 - Real.log ad.1) / 2 : ℝ) : ℂ) *
      cexp (((-representativeShift ad : ℝ) : ℂ) * (1 / 2 - u)) =
        cexp (u * (representativeShift ad : ℂ)) := by
    rw [← Complex.exp_add, representativeShift]
    congr 1
    push_cast
    ring
  linear_combination ((y : ℂ) ^ (1 / 2 - u)) * hexp

/-! ### `T_n` on the truncated state -/

/-- `T_n` on the truncation: `T_n(1_{y > Y} c_u) = Σ_{ad=n} (d/a)^u 1_{y > Yd/a} c_u` at a resonance. -/
theorem heckeN_truncation {u : ℂ} (hAu : msA u = 0) {n : ℕ} (Y x : ℝ) {y : ℝ} (hy : 0 < y) :
    heckeN n (fun _ y => if Y < y then d4BMCompletedEisensteinCuspConstantPart .scalar u y else 0)
        x y =
      ∑ ad ∈ n.divisorsAntidiagonal, cexp (u * (representativeShift ad : ℂ)) *
        (if Y * Real.exp (representativeShift ad) < y then
          d4BMCompletedEisensteinCuspConstantPart .scalar u y else 0) := by
  unfold heckeN heckeOrbit
  simp only [sum_const, card_range, nsmul_eq_mul]
  rw [mul_sum]
  refine sum_congr rfl fun ad had => ?_
  obtain ⟨ha, hd⟩ := pos_of_mem_divisorsAntidiagonal had
  have hA : (0 : ℝ) < ad.1 := by exact_mod_cast ha
  have hD : (0 : ℝ) < ad.2 := by exact_mod_cast hd
  have hcond : Y < (ad.1 : ℝ) * y / ad.2 ↔ Y * Real.exp (representativeShift ad) < y := by
    rw [exp_representativeShift had, lt_div_iff₀ hD, ← mul_div_assoc, div_lt_iff₀ hA,
      mul_comm (ad.1 : ℝ) y]
  by_cases h : Y * Real.exp (representativeShift ad) < y
  · rw [if_pos (hcond.mpr h), if_pos h, cuspConstantPart_eq_msAB, cuspConstantPart_eq_msAB, hAu,
      zero_mul, add_zero, zero_mul, add_zero]
    have hrep := representative_weyl_power u had hy
    push_cast at hrep ⊢
    linear_combination msB u * hrep
  · rw [if_neg (mt hcond.mp h), if_neg h]
    ring

/-- **`T_n` is a sum of translations of the cutoff family.** At a resonance,
`T_n Λ^Y E_u = Σ_{ad = n} (d/a)^u Λ^{Yd/a} E_u`. -/
theorem heckeN_truncatedLeg {u : ℂ} (hAu : msA u = 0) {n : ℕ} (hn : n ≠ 0) (Y x : ℝ) {y : ℝ}
    (hy : 0 < y) :
    heckeN n (truncatedLeg u Y) x y =
      ∑ ad ∈ n.divisorsAntidiagonal, shiftedLeg u Y (representativeShift ad) x y := by
  have htrunc : truncatedLeg u Y = fun x y =>
      d4BMCompletedEisensteinCuspLeg .scalar u x y -
        (if Y < y then d4BMCompletedEisensteinCuspConstantPart .scalar u y else 0) := rfl
  rw [htrunc, heckeN_sub, heckeN_cuspLeg u hn x hy, heckeN_truncation hAu Y x hy,
    ← sum_cexp_representativeShift u hn, sum_mul, ← sum_sub_distrib]
  refine sum_congr rfl fun ad _ => ?_
  simp only [shiftedLeg, truncatedLeg]
  ring

/-! ### The Gram matrix of the translations -/

theorem integrableOn_truncated_mul_conj (u : ℂ) {Y Z : ℝ} (hY : 1 ≤ Y) (hZ : 1 ≤ Z) :
    IntegrableOn (fun z : ℍ => truncatedLineModel u Y z * conj (truncatedLineModel u Z z)) fd := by
  refine Measure.integrableOn_of_bounded volume_fd_ne_top
    ((measurable_truncatedLineModel u Y).mul
      ((Complex.continuous_conj.measurable).comp
        (measurable_truncatedLineModel u Z))).aestronglyMeasurable
    (M := truncBound' u Y * truncBound' u Z) ?_
  refine (ae_restrict_iff' isClosed_fd.measurableSet).mpr (Eventually.of_forall fun z hz => ?_)
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (norm_truncatedLineModel_le_truncBound' u hY hz)
    (norm_truncatedLineModel_le_truncBound' u hZ hz) (norm_nonneg _)
    ((norm_nonneg _).trans (norm_truncatedLineModel_le_truncBound' u hY hz))

/-- Every translation of a representative of `n` keeps the cutoff above `1` once `Y ≥ n`. -/
theorem one_le_mul_exp_representativeShift {n : ℕ} {Y : ℝ} (hY : (n : ℝ) ≤ Y) {ad : ℕ × ℕ}
    (had : ad ∈ n.divisorsAntidiagonal) : 1 ≤ Y * Real.exp (representativeShift ad) := by
  obtain ⟨ha, hd⟩ := pos_of_mem_divisorsAntidiagonal had
  have hprod := (Nat.mem_divisorsAntidiagonal.mp had).1
  have hA : (0 : ℝ) < ad.1 := by exact_mod_cast ha
  have hD : (1 : ℝ) ≤ ad.2 := by exact_mod_cast hd
  have hn : (ad.1 : ℝ) * ad.2 = n := by exact_mod_cast hprod
  have hY0 : 0 ≤ Y := le_trans (Nat.cast_nonneg n) hY
  rw [exp_representativeShift had, ← mul_div_assoc, le_div_iff₀ hA, one_mul]
  nlinarith

/-- The Poisson mixture of two sums of characters `Σ_{ad=n} e^{itℓ}`, `Σ_{ad=m} e^{-itℓ'}`. -/
theorem integral_poisson_mul_whittaker {u : ℂ} (hur : u.re < 0) {n m : ℕ} (hn : n ≠ 0)
    (hm : m ≠ 0) :
    ∫ t : ℝ, (halfPlanePoisson (-u.re) (t - u.im) : ℂ) *
        (whittakerCoeff (I * (t : ℂ)) n * whittakerCoeff (I * (t : ℂ)) m) =
      ∑ ad ∈ n.divisorsAntidiagonal, ∑ ad' ∈ m.divisorsAntidiagonal,
        poissonCovariance u (representativeShift ad - representativeShift ad') := by
  have hσ : 0 < -u.re := neg_pos.mpr hur
  have hexpand : ∀ t : ℝ, (halfPlanePoisson (-u.re) (t - u.im) : ℂ) *
      (whittakerCoeff (I * (t : ℂ)) n * whittakerCoeff (I * (t : ℂ)) m) =
        ∑ ad ∈ n.divisorsAntidiagonal, ∑ ad' ∈ m.divisorsAntidiagonal,
          (halfPlanePoisson (-u.re) (t - u.im) : ℂ) *
            cexp (I * ((representativeShift ad - representativeShift ad' : ℝ) : ℂ) * (t : ℂ)) := by
    intro t
    rw [← sum_cexp_representativeShift _ hn, ← whittakerCoeff_neg _ hm,
      ← sum_cexp_representativeShift _ hm, sum_mul_sum, mul_sum]
    refine sum_congr rfl fun ad _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun ad' _ => ?_
    rw [← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hint : ∀ y : ℝ, Integrable (fun t : ℝ =>
      (halfPlanePoisson (-u.re) (t - u.im) : ℂ) * cexp (I * (y : ℂ) * (t : ℂ))) :=
    fun y => integrable_halfPlanePoisson_shift_mul_cexp hσ u.im y
  rw [integral_congr_ae (Eventually.of_forall hexpand),
    integral_finsetSum _ fun ad _ => integrable_finsetSum _ fun ad' _ => hint _]
  refine sum_congr rfl fun ad _ => ?_
  rw [integral_finsetSum _ fun ad' _ => hint _]
  exact sum_congr rfl fun ad' _ => integral_halfPlanePoisson_shift_mul_cexp hσ u.im _

/-- **Physical Hecke moments for the whole Hecke algebra.** For `n, m ≥ 1` and `Y ≥ n, m`,
`⟨T_n t_Y, T_m t_Y⟩ = ‖t_Y‖² ∫ P_{−Re u}(t − Im u) W_{it}(n) W_{it}(m) dt`. -/
theorem integral_heckeN_mul_conj_heckeN {u : ℂ} (hu : u ∈ eisensteinLineDomain) (hur : u.re < 0)
    (hAu : msA u = 0) {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) {Y : ℝ} (hYn : (n : ℝ) ≤ Y)
    (hYm : (m : ℝ) ≤ Y) :
    ∫ z in fd, heckeN n (truncatedLeg u Y) z.re z.im *
        conj (heckeN m (truncatedLeg u Y) z.re z.im) =
      (∫ z in fd, truncatedLineModel u Y z * conj (truncatedLineModel u Y z)) *
        ∫ t : ℝ, (halfPlanePoisson (-u.re) (t - u.im) : ℂ) *
          (whittakerCoeff (I * (t : ℂ)) n * whittakerCoeff (I * (t : ℂ)) m) := by
  have hY1 : 1 ≤ Y := le_trans (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn) hYn
  set S : ℝ → ℍ → ℂ := fun x z => cexp (u * x) * truncatedLineModel u (Y * Real.exp x) z with hS
  have hpoint : ∀ k : ℕ, k ≠ 0 → ∀ z : ℍ, heckeN k (truncatedLeg u Y) z.re z.im =
      ∑ ad ∈ k.divisorsAntidiagonal, S (representativeShift ad) z := by
    intro k hk z
    rw [heckeN_truncatedLeg hAu hk Y z.re z.im_pos]
    rfl
  have hfun : ∀ z : ℍ, heckeN n (truncatedLeg u Y) z.re z.im *
      conj (heckeN m (truncatedLeg u Y) z.re z.im) =
        ∑ ad ∈ n.divisorsAntidiagonal, ∑ ad' ∈ m.divisorsAntidiagonal,
          S (representativeShift ad) z * conj (S (representativeShift ad') z) := by
    intro z
    rw [hpoint n hn z, hpoint m hm z, map_sum, sum_mul_sum]
  have hintS : ∀ ad ∈ n.divisorsAntidiagonal, ∀ ad' ∈ m.divisorsAntidiagonal,
      Integrable (fun z : ℍ => S (representativeShift ad) z * conj (S (representativeShift ad') z))
        (volume.restrict fd) := by
    intro ad had ad' had'
    have h := integrableOn_truncated_mul_conj u (one_le_mul_exp_representativeShift hYn had)
      (one_le_mul_exp_representativeShift hYm had')
    refine (h.const_mul (cexp (u * (representativeShift ad : ℂ)) *
      conj (cexp (u * (representativeShift ad' : ℂ))))).congr (Eventually.of_forall fun z => ?_)
    simp only [hS, map_mul]
    ring
  rw [integral_congr_ae (Eventually.of_forall hfun),
    integral_finsetSum _ fun ad had => integrable_finsetSum _ fun ad' had' => hintS ad had ad' had',
    integral_poisson_mul_whittaker hur hn hm, mul_sum]
  refine sum_congr rfl fun ad had => ?_
  rw [integral_finsetSum _ fun ad' had' => hintS ad had ad' had', mul_sum]
  exact sum_congr rfl fun ad' had' => integral_shifted_mul_conj hu hur hAu hY1
    (one_le_mul_exp_representativeShift hYn had) (one_le_mul_exp_representativeShift hYm had')

/-- **Every Hecke operator reads the formal moment.** For every `n ≥ 1` and `Y ≥ n`,
`⟨T_n t_Y, t_Y⟩ = μ_n(u) ‖t_Y‖²`. -/
theorem integral_heckeN_mul_conj_eq_resonantHeckeMoment {u : ℂ} (hu : u ∈ eisensteinLineDomain)
    (hur : u.re < 0) (hAu : msA u = 0) {n : ℕ} (hn : n ≠ 0) {Y : ℝ} (hY : (n : ℝ) ≤ Y) :
    ∫ z in fd, heckeN n (truncatedLeg u Y) z.re z.im * conj (truncatedLineModel u Y z) =
      (∫ z in fd, truncatedLineModel u Y z * conj (truncatedLineModel u Y z)) *
        resonantHeckeMoment u n := by
  have hY1 : (1 : ℝ) ≤ Y := le_trans (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn) hY
  have hmain := integral_heckeN_mul_conj_heckeN hu hur hAu hn one_ne_zero hY
    (by simpa using hY1)
  have hfun : (fun z : ℍ => heckeN n (truncatedLeg u Y) z.re z.im *
      conj (truncatedLineModel u Y z)) = fun z : ℍ => heckeN n (truncatedLeg u Y) z.re z.im *
        conj (heckeN 1 (truncatedLeg u Y) z.re z.im) := by
    funext z
    rw [heckeN_one, truncatedLineModel_eq_truncatedLeg]
  rw [hfun, hmain, resonantHeckeMoment_eq_poisson_integral hur hn]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [whittakerCoeff_one, mul_one]

/-- **The Hecke multiplication law on the physical state.** For `n, m ≥ 1` and `Y ≥ n, m`,
`⟨T_n t_Y, T_m t_Y⟩ = ‖t_Y‖² Σ_{d ∣ (n, m)} μ_{nm/d²}(u)`. -/
theorem integral_heckeN_mul_conj_heckeN_eq_sum_gcd {u : ℂ} (hu : u ∈ eisensteinLineDomain)
    (hur : u.re < 0) (hAu : msA u = 0) {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) {Y : ℝ}
    (hYn : (n : ℝ) ≤ Y) (hYm : (m : ℝ) ≤ Y) :
    ∫ z in fd, heckeN n (truncatedLeg u Y) z.re z.im *
        conj (heckeN m (truncatedLeg u Y) z.re z.im) =
      (∫ z in fd, truncatedLineModel u Y z * conj (truncatedLineModel u Y z)) *
        ∑ d ∈ (Nat.gcd n m).divisors, resonantHeckeMoment u (n * m / d ^ 2) := by
  have hσ : 0 < -u.re := neg_pos.mpr hur
  have hne : ∀ d ∈ (Nat.gcd n m).divisors, n * m / d ^ 2 ≠ 0 := by
    intro d hd
    have hdvd : d ∣ Nat.gcd n m := Nat.dvd_of_mem_divisors hd
    have hd2 : d ^ 2 ∣ n * m := by
      rw [sq]
      exact Nat.mul_dvd_mul (hdvd.trans (Nat.gcd_dvd_left n m)) (hdvd.trans (Nat.gcd_dvd_right n m))
    exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (mul_ne_zero hn hm)) hd2)
      (pow_pos (Nat.pos_of_mem_divisors hd) 2)).ne'
  have hintW : ∀ k : ℕ, k ≠ 0 → Integrable (fun t : ℝ =>
      (halfPlanePoisson (-u.re) (t - u.im) : ℂ) * whittakerCoeff (I * (t : ℂ)) k) := by
    intro k hk
    have hexp : (fun t : ℝ => (halfPlanePoisson (-u.re) (t - u.im) : ℂ) *
        whittakerCoeff (I * (t : ℂ)) k) = fun t : ℝ => ∑ ad ∈ k.divisorsAntidiagonal,
          (halfPlanePoisson (-u.re) (t - u.im) : ℂ) *
            cexp (I * ((representativeShift ad : ℝ) : ℂ) * (t : ℂ)) := by
      funext t
      rw [← sum_cexp_representativeShift _ hk, mul_sum]
      refine sum_congr rfl fun ad _ => ?_
      congr 2
      ring
    rw [hexp]
    exact integrable_finsetSum _ fun ad _ =>
      integrable_halfPlanePoisson_shift_mul_cexp hσ u.im _
  rw [integral_heckeN_mul_conj_heckeN hu hur hAu hn hm hYn hYm]
  congr 1
  have hprod : ∀ t : ℝ, (halfPlanePoisson (-u.re) (t - u.im) : ℂ) *
      (whittakerCoeff (I * (t : ℂ)) n * whittakerCoeff (I * (t : ℂ)) m) =
        ∑ d ∈ (Nat.gcd n m).divisors, (halfPlanePoisson (-u.re) (t - u.im) : ℂ) *
          whittakerCoeff (I * (t : ℂ)) (n * m / d ^ 2) := by
    intro t
    rw [whittakerCoeff_mul_eq_sum_gcd_divisors _ hn hm, mul_sum]
  rw [integral_congr_ae (Eventually.of_forall hprod),
    integral_finsetSum _ fun d hd => hintW _ (hne d hd)]
  exact sum_congr rfl fun d hd => (resonantHeckeMoment_eq_poisson_integral hur (hne d hd)).symm

end

end GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates
