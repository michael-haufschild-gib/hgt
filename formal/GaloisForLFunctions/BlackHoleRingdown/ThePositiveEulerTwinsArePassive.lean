import GaloisForLFunctions.BlackHoleRingdown.CausalIdentitiesCannotForceQuarterRingdown
import GaloisForLFunctions.SelbergClass.PositiveFiniteEulerCompletion
import GaloisForLFunctions.SelbergClass.PositiveFiniteEulerZeros
import GaloisForLFunctions.SelbergClass.PositiveFiniteEulerProduct

/-!
# Arithmetic coefficients and passive reciprocal Euler factors

The conductor-normalized prime-two deformation has negative coefficients precisely
at integers of valuation one at two. Positive reciprocal Euler modifications avoid
that obstruction; their scattering gates are nevertheless Schur contractions.
The ordinary Dirichlet coefficients and the logarithmic prime-power coefficients
therefore impose different arithmetic tests on a passive horizon.
-/

noncomputable section

open Complex Filter Topology
open GaloisForLFunctions.SelbergClass.PositiveFiniteEuler
open GaloisForLFunctions.ArithmeticScatteringHolography

namespace GaloisForLFunctions.BlackHoleRingdown

/-- The ordinary Dirichlet series obtained by removing the conductor factor. -/
def normalizedPrimeTwoZeta (α : ℝ) (s : ℂ) : ℂ :=
  localFactor 2 (-primeTwoTrace α) s * riemannZeta s

/-- The local polynomial is the same one that defines the passive prime-two gate. -/
theorem primeTwoFactor_eq_localFactor (α : ℝ) (s : ℂ) :
    primeTwoFactor α s =
      (2 : ℂ) ^ (s - 1 / 2) * localFactor 2 (-primeTwoTrace α) s := by
  have h := primeTwoFactor_two_mul_eq_schurNum α (s / 2)
  rw [show (2 : ℂ) * (s / 2) = s by ring,
    show (-2 : ℂ) * (s / 2) = -s by ring] at h
  simpa only [schurNum, localFactor, Nat.cast_ofNat, Complex.ofReal_ofNat, Complex.ofReal_neg,
    neg_mul, sub_eq_add_neg] using h

theorem normalizedPrimeTwoZeta_eq (α : ℝ) (s : ℂ) :
    normalizedPrimeTwoZeta α s =
      (2 : ℂ) ^ (1 / 2 - s) * primeTwoFactor α s * riemannZeta s := by
  rw [primeTwoFactor_eq_localFactor, ← mul_assoc,
    ← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0),
    show (1 / 2 - s) + (s - 1 / 2) = (0 : ℂ) by ring, cpow_zero, one_mul]
  rfl

/-- Absolute convergence identifies all coefficients of the normalized deformation. -/
theorem normalizedPrimeTwoZeta_hasSum (α : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (arithmeticCoeffs 2 (-primeTwoTrace α)) s
      (normalizedPrimeTwoZeta α s) :=
  lSeriesHasSum Nat.prime_two (-primeTwoTrace α) hs

private theorem one_lt_primeTwoTrace {α : ℝ} (hα : 0 < α) :
    1 < primeTwoTrace α := by
  have h1 := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hα
  have h2 := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (1 - α)
  change 1 < (2 : ℝ) ^ α + (2 : ℝ) ^ (1 - α)
  linarith only [h1, h2]

/-- Negative ordinary coefficients occur exactly on the valuation-one class. -/
theorem primeTwo_coeff_neg_iff {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {n : ℕ} (hn : n ≠ 0) :
    coeff 2 (-primeTwoTrace α) n < 0 ↔ 2 ∣ n ∧ ¬4 ∣ n := by
  have ht1 := one_lt_primeTwoTrace hα0
  have ht3 := (primeTwoTrace_pos_and_lt_three hα0 hα1).2
  have ht : primeTwoTrace α < 3 := (le_abs_self _).trans_lt ht3
  by_cases h2 : 2 ∣ n
  · by_cases h4 : 4 ∣ n
    · simp only [coeff, hn, h2, show (2 : ℕ) ^ 2 = 4 by norm_num,
        h4, if_false, if_true, Nat.cast_ofNat, not_true_eq_false, and_false, iff_false, not_lt]
      linarith only [ht]
    · simp only [coeff, hn, h2, show (2 : ℕ) ^ 2 = 4 by norm_num,
        h4, if_false, if_true, add_zero, not_false_eq_true, and_self, iff_true]
      linarith only [ht1]
  · have h4 : ¬4 ∣ n := fun h => h2 ((by norm_num : (2 : ℕ) ∣ 4).trans h)
    simp only [coeff, hn, h2, show (2 : ℕ) ^ 2 = 4 by norm_num,
      h4, if_false, add_zero, not_lt_of_ge zero_le_one, false_and]

/-- No choice of nonnegative Dirichlet coefficients can represent this deformation,
even if equality is required only on a real right ray. -/
theorem not_exists_nonnegative_primeTwo_representation (α : Set.Ioo (0 : ℝ) 1) :
    ¬ ∃ a : ℕ → ℂ, (∀ n : ℕ, 0 ≤ (a n).re) ∧
      LSeries.abscissaOfAbsConv a < ⊤ ∧
      (fun x : ℝ => LSeries a x) =ᶠ[atTop]
        (fun x => normalizedPrimeTwoZeta α x) := by
  rintro ⟨a, hpos, ha, he⟩
  have hc := (normalizedPrimeTwoZeta_hasSum (α : ℝ)
    (s := 2) (by norm_num)).LSeriesSummable
  have hsame : (fun x : ℝ => LSeries a x) =ᶠ[atTop]
      (fun x => LSeries (arithmeticCoeffs 2 (-primeTwoTrace α)) x) := by
    filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with x hx hx1
    exact hx.trans (normalizedPrimeTwoZeta_hasSum (α : ℝ) hx1).LSeries_eq.symm
  have heq := LSeries.eq_of_LSeries_eventually_eq ha
    (hc.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)) hsame (n := 2) (by norm_num)
  have hneg := (primeTwo_coeff_neg_iff α.property.1 α.property.2
    (n := 2) (by norm_num)).mpr (by norm_num)
  have hre : (a 2).re = coeff 2 (-primeTwoTrace α) 2 := by
    rw [heq, arithmeticCoeffs_apply, Complex.ofReal_re]
  rw [← hre] at hneg
  exact (not_lt_of_ge (hpos 2)) hneg

namespace PositiveEulerHorizon

open _root_.RHTower

/-- The reciprocal finite multiplier applied to the actual entire Xi function. -/
def completedXi (p : ℕ) (A : ℝ) (s : ℂ) : ℂ :=
  completedFactor p A s * xi s

def reducedScattering (p : ℕ) (A : ℝ) (w : ℂ) : ℂ :=
  completedXi p A (2 * w) / completedXi p A (1 + 2 * w)

def scatteringPhase (p : ℕ) (A : ℝ) (w : ℂ) : ℂ :=
  ((1 + 2 * w) / (2 * w - 1)) * reducedScattering p A w

/-- The finite multiplier contributes a reciprocal quadratic Schur gate. -/
def gate (p : ℕ) (A : ℝ) (w : ℂ) : ℂ :=
  schurNum p (-A) ((p : ℂ) ^ (-2 * w)) /
    schurDen p (-A) ((p : ℂ) ^ (-2 * w))

theorem completedXi_one_sub (p : ℕ) (A : ℝ) (s : ℂ) :
    completedXi p A (1 - s) = completedXi p A s := by
  rw [completedXi, completedXi, completedFactor_one_sub, xi_one_sub]

theorem differentiable_completedXi {p : ℕ} (hp : p ≠ 0) (A : ℝ) :
    Differentiable ℂ (completedXi p A) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hfactor : Differentiable ℂ (completedFactor p A) := by
    have heq : completedFactor p A = fun s : ℂ => (p : ℂ) ^ s * localFactor p A s :=
      funext fun s => (cpow_mul_localFactor hp A s).symm
    rw [heq]
    exact (differentiable_id.const_cpow (.inl hpC)).mul (differentiable_localFactor hp A)
  exact hfactor.mul xi_differentiable

theorem factor_ratio_eq_gate {p : ℕ} (hp : p ≠ 0) (A : ℝ) (w : ℂ) :
    completedFactor p A (2 * w) / completedFactor p A (1 + 2 * w) = gate p A w := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hz : (p : ℂ) ^ (2 * w) ≠ 0 := cpow_ne_zero_iff.mpr (.inl hpC)
  have hv : (p : ℂ) ^ (-2 * w) = ((p : ℂ) ^ (2 * w))⁻¹ := by
    rw [show (-2 : ℂ) * w = -(2 * w) by ring, cpow_neg]
  have hnum : completedFactor p A (2 * w) =
      (p : ℂ) ^ (2 * w) * schurNum p (-A) ((p : ℂ) ^ (-2 * w)) := by
    rw [completedFactor, cpow_sub _ _ hpC, cpow_one, hv, schurNum]
    push_cast
    field_simp [hz]
    ring
  have hden : completedFactor p A (1 + 2 * w) =
      (p : ℂ) ^ (2 * w) * schurDen p (-A) ((p : ℂ) ^ (-2 * w)) := by
    rw [completedFactor, cpow_add _ _ hpC, cpow_one,
      show (1 : ℂ) - (1 + 2 * w) = -(2 * w) by ring, cpow_neg, hv, schurDen]
    push_cast
    field_simp [hz]
    ring
  rw [hnum, hden, mul_div_mul_left _ _ hz, gate]

theorem reducedScattering_eq_gate_mul {p : ℕ} (hp : p ≠ 0) (A : ℝ) (w : ℂ) :
    reducedScattering p A w = gate p A w * modularReducedScattering w := by
  rw [reducedScattering, completedXi, completedXi, mul_div_mul_comm,
    factor_ratio_eq_gate hp, modularReducedScattering]

private theorem norm_frequency_le {p : ℕ} (hp : 1 < p) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖(p : ℂ) ^ (-2 * w)‖ ≤ 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega),
    show (-2 * w).re = -2 * w.re by simp]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp.le) (by linarith only [hw])

private theorem pair_trace_lt {p : ℕ} {r u : ℝ} (hr : 1 < r) (hu : 1 < u)
    (hru : r * u = p) : r + u < (p : ℝ) + 1 := by
  have h := mul_pos (sub_pos.mpr hr) (sub_pos.mpr hu)
  nlinarith only [h, hru]

private theorem schurDen_pair_ne_zero {p : ℕ} {r u : ℝ} (hr : 1 < r) (hu : 1 < u)
    (hru : r * u = p) {v : ℂ} (hv : ‖v‖ ≤ 1) :
    schurDen p (-(r + u)) v ≠ 0 := by
  have hfac : schurDen p (-(r + u)) v = ((r : ℂ) + v) * ((u : ℂ) + v) := by
    have hruC : (r : ℂ) * (u : ℂ) = p := by exact_mod_cast hru
    simp only [schurDen, Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_natCast]
    rw [← hruC]
    ring
  have hne (a : ℝ) (ha : 1 < a) : (a : ℂ) + v ≠ 0 := by
    intro h
    have he : v = -(a : ℂ) := by linear_combination h
    rw [he, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith only [ha])] at hv
    exact (not_le_of_gt ha) hv
  rw [hfac]
  exact mul_ne_zero (hne r hr) (hne u hu)

/-- Positive reciprocal roots place the gate strictly inside the passive trace range. -/
theorem norm_gate_le_one {p : ℕ} (hp : 1 < p) {r u : ℝ}
    (hr : 1 < r) (hu : 1 < u) (hru : r * u = p) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖gate p (r + u) w‖ ≤ 1 := by
  have hv := norm_frequency_le hp hw
  have ht : |-(r + u)| ≤ (p : ℝ) + 1 := by
    rw [abs_neg, abs_of_pos (by linarith only [hr, hu])]
    exact (pair_trace_lt hr hu hru).le
  have hb := (schur_bound_iff (q := p) (t := -(r + u)) (by exact_mod_cast hp)).mpr ht _ hv
  have hn := schurDen_pair_ne_zero hr hu hru hv
  rw [gate, norm_div, div_le_one (norm_pos_iff.mpr hn)]
  exact hb

/-- The complete reduced scattering symbol stays contractive despite its added zeros. -/
theorem norm_reducedScattering_le_one {p : ℕ} (hp : 1 < p) {r u : ℝ}
    (hr : 1 < r) (hu : 1 < u) (hru : r * u = p) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖reducedScattering p (r + u) w‖ ≤ 1 := by
  rw [reducedScattering_eq_gate_mul (by omega), norm_mul]
  calc ‖gate p (r + u) w‖ * ‖modularReducedScattering w‖ ≤ 1 * 1 :=
      mul_le_mul (norm_gate_le_one hp hr hu hru hw)
        (norm_modularReducedScattering_le_one hw) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

/-- The denominator never vanishes on the causal half-plane; contractivity is
therefore a property of a holomorphic scattering symbol. -/
theorem completedXi_den_ne_zero {p : ℕ} (hp : 1 < p) {r u : ℝ}
    (hr : 1 < r) (hu : 1 < u) (hru : r * u = p) {w : ℂ} (hw : 0 ≤ w.re) :
    completedXi p (r + u) (1 + 2 * w) ≠ 0 := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hz : (p : ℂ) ^ (2 * w) ≠ 0 := cpow_ne_zero_iff.mpr (.inl hpC)
  have hd : completedFactor p (r + u) (1 + 2 * w) =
      (p : ℂ) ^ (2 * w) * schurDen p (-(r + u)) ((p : ℂ) ^ (-2 * w)) := by
    rw [completedFactor, cpow_add _ _ hpC, cpow_one,
      show (1 : ℂ) - (1 + 2 * w) = -(2 * w) by ring,
      show (-2 : ℂ) * w = -(2 * w) by ring, cpow_neg, schurDen]
    push_cast
    field_simp [hz]
    ring
  rw [completedXi, hd]
  exact mul_ne_zero
    (mul_ne_zero hz (schurDen_pair_ne_zero hr hu hru (norm_frequency_le hp hw)))
    (xi_ne_zero_of_one_le_re (by simp only [Complex.add_re, Complex.one_re,
      Complex.mul_re, Complex.ofNat_re, Complex.ofNat_im, zero_mul, sub_zero]; linarith only [hw]))

theorem differentiableAt_reducedScattering {p : ℕ} (hp : 1 < p) {r u : ℝ}
    (hr : 1 < r) (hu : 1 < u) (hru : r * u = p) {w : ℂ} (hw : 0 ≤ w.re) :
    DifferentiableAt ℂ (reducedScattering p (r + u)) w := by
  have hd := differentiable_completedXi (p := p) (by omega) (r + u)
  exact ((hd _).comp w (by fun_prop)).div ((hd _).comp w (by fun_prop))
    (completedXi_den_ne_zero hp hr hu hru hw)

theorem herglotz_re_nonneg {p : ℕ} (hp : 1 < p) {r u : ℝ}
    (hr : 1 < r) (hu : 1 < u) (hru : r * u = p) {w : ℂ} (hw : 0 ≤ w.re) :
    0 ≤ ((1 - reducedScattering p (r + u) w) /
      (1 + reducedScattering p (r + u) w)).re := by
  let S := reducedScattering p (r + u) w
  have hn : Complex.normSq S ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    have h := norm_reducedScattering_le_one hp hr hu hru hw
    nlinarith only [h, norm_nonneg S]
  change 0 ≤ ((1 - S) / (1 + S)).re
  by_cases hd : 1 + S = 0
  · rw [hd, div_zero, Complex.zero_re]
  · rw [Complex.div_re, ← add_div]
    have he : (1 - S).re * (1 + S).re + (1 - S).im * (1 + S).im =
        1 - Complex.normSq S := by
      simp only [Complex.sub_re, Complex.add_re, Complex.one_re,
        Complex.sub_im, Complex.add_im, Complex.one_im, Complex.normSq_apply]
      ring
    rw [he]
    exact div_nonneg (sub_nonneg.mpr hn) (Complex.normSq_nonneg _)

/-- Every imaginary-axis frequency sees a unitary finite Euler gate. -/
theorem norm_gate_axis {p : ℕ} (hp : 1 < p) {r u : ℝ}
    (hr : 1 < r) (hu : 1 < u) (hru : r * u = p) (t : ℝ) :
    ‖gate p (r + u) ((t : ℂ) * I)‖ = 1 := by
  let v : ℂ := (p : ℂ) ^ (-2 * ((t : ℂ) * I))
  have hv : ‖v‖ = 1 := by
    dsimp only [v]
    rw [Complex.norm_natCast_cpow_of_pos (by omega),
      show (-2 * ((t : ℂ) * I)).re = 0 by simp, Real.rpow_zero]
  have hs : Complex.normSq v = 1 := by rw [Complex.normSq_eq_norm_sq, hv, one_pow]
  have hd := normSq_schurDen_sub_num (p : ℝ) (-(r + u)) v
  rw [hs, sub_self, mul_zero, zero_mul] at hd
  have he : ‖schurNum p (-(r + u)) v‖ = ‖schurDen p (-(r + u)) v‖ := by
    have he2 : ‖schurNum p (-(r + u)) v‖ ^ 2 = ‖schurDen p (-(r + u)) v‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      exact (sub_eq_zero.mp hd).symm
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he2
  have hn := schurDen_pair_ne_zero hr hu hru hv.le
  change ‖schurNum p (-(r + u)) v / schurDen p (-(r + u)) v‖ = 1
  rw [norm_div, he, div_self (norm_ne_zero_iff.mpr hn)]

theorem scatteringPhase_eq_gate_mul {p : ℕ} (hp : p ≠ 0) (A : ℝ) (w : ℂ) :
    scatteringPhase p A w = gate p A w * modularScatteringPhase w := by
  rw [scatteringPhase, reducedScattering_eq_gate_mul hp, modularReducedScattering,
    modularScatteringPhase]
  ring

/-- The full scattering phase is unitary on the continuous spectrum. -/
theorem norm_scatteringPhase_axis {p : ℕ} (hp : 1 < p) {r u : ℝ}
    (hr : 1 < r) (hu : 1 < u) (hru : r * u = p) (t : ℝ) :
    ‖scatteringPhase p (r + u) ((t : ℂ) * I)‖ = 1 := by
  rw [scatteringPhase_eq_gate_mul (by omega), norm_mul, norm_gate_axis hp hr hu hru,
    norm_modularScatteringPhase_axis, one_mul]

/-- Positive ordinary coefficients coexist with a negative repeated-prime logarithmic coefficient. -/
theorem eulerLogCoeff_prime_sq_neg {p : ℕ} (hp : p.Prime) {r u : ℝ}
    (hr : 1 < r) (hu : 1 < u) :
    (eulerLogCoeff p (-(r : ℂ)) (-(u : ℂ)) (p ^ 2)).re < 0 := by
  rw [eulerLogCoeff_prime_pow hp _ _ (by norm_num : (2 : ℕ) ≠ 0)]
  simp only [neg_sq, Complex.div_ofReal_re, Complex.sub_re, Complex.one_re,
    ← Complex.ofReal_pow, Complex.ofReal_re, Nat.cast_ofNat]
  nlinarith only [sq_pos_of_pos (by linarith only [hr] : 0 < r),
    sq_nonneg (u - 1), hu]

/-- Every finite zeta prefix extends to a positive arithmetic twin with passive
scattering and a prescribed off-line zero. Its prime-square logarithmic count is negative. -/
theorem exists_positive_passive_twin (N : ℕ) (σ : Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ (p : ℕ) (hp : p.Prime) (A : ℝ), N < p ∧
      (extendedClass hp A).presentationDegree = 1 ∧
      (arithmeticCoeffs p A).IsMultiplicative ∧
      (∃ C : ℝ, ∀ n : ℕ, n ≠ 0 →
        (arithmeticCoeffs p A n).im = 0 ∧
        1 ≤ (arithmeticCoeffs p A n).re ∧ ‖arithmeticCoeffs p A n‖ ≤ C) ∧
      (∀ n : ℕ, n ≠ 0 → n ≤ N → arithmeticCoeffs p A n = 1) ∧
      (∃ s : ℂ, s.re = σ ∧ completedXi p A s = 0 ∧ (extendedClass hp A) s = 0) ∧
      (∀ w : ℂ, 0 ≤ w.re → DifferentiableAt ℂ (reducedScattering p A) w ∧
        ‖reducedScattering p A w‖ ≤ 1 ∧
        0 ≤ ((1 - reducedScattering p A w) / (1 + reducedScattering p A w)).re) ∧
      (∀ t : ℝ, ‖scatteringPhase p A ((t : ℂ) * I)‖ = 1) ∧
      (∃ b : ArithmeticFunction ℂ,
        (∀ n : ℕ, b n ≠ 0 → IsPrimePow n) ∧
        (∀ s : ℂ, 1 < s.re → LSeriesSummable b s ∧
          Complex.exp (LSeries b s) = (extendedClass hp A) s) ∧
        (b (p ^ 2)).re < 0) := by
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N + 1)
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hpR
  let r : ℝ := (p : ℝ) ^ (σ : ℝ)
  let u : ℝ := (p : ℝ) ^ (1 - (σ : ℝ))
  have hr : 1 < r := Real.one_lt_rpow hpR (by linarith only [σ.property.1])
  have hu : 1 < u := Real.one_lt_rpow hpR (sub_pos.mpr σ.property.2)
  have hru : r * u = p := by
    dsimp only [r, u]
    rw [← Real.rpow_add hp0,
      show (σ : ℝ) + (1 - (σ : ℝ)) = 1 by ring, Real.rpow_one]
  have hrp : r ≤ p := by
    exact (Real.rpow_le_rpow_of_exponent_le hpR.le σ.property.2.le).trans_eq (Real.rpow_one _)
  have hup : u ≤ p := by
    exact (Real.rpow_le_rpow_of_exponent_le hpR.le
      (show 1 - (σ : ℝ) ≤ 1 by linarith only [σ.property.1])).trans_eq (Real.rpow_one _)
  have hA : 0 ≤ r + u := by linarith only [hr, hu]
  have hpr : (p : ℝ) / r = u := (div_eq_iff (by linarith only [hr] : r ≠ 0)).mpr
    (by rw [mul_comm, hru])
  have hparam : reciprocalParameter p r = r + u := by rw [reciprocalParameter, hpr]
  refine ⟨p, hp, r + u, by omega, extendedClass_degree hp _,
    arithmeticCoeffs_isMultiplicative hp _, ⟨1 + (r + u) + p, ?_⟩, ?_, ?_,
    fun w hw => ⟨differentiableAt_reducedScattering hp.one_lt hr hu hru hw,
      norm_reducedScattering_le_one hp.one_lt hr hu hru hw,
      herglotz_re_nonneg hp.one_lt hr hu hru hw⟩,
    fun t => norm_scatteringPhase_axis hp.one_lt hr hu hru t, ?_⟩
  · intro n hn
    have hb := coeff_bounds (p := p) hA hn
    rw [arithmeticCoeffs_apply, Complex.ofReal_im, Complex.ofReal_re,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hb.1)]
    exact ⟨rfl, hb⟩
  · intro n hn hnN
    rw [arithmeticCoeffs_apply, coeff_eq_one_of_lt hn (by omega), Complex.ofReal_one]
  · have hre : (factorZero p r).re = (σ : ℝ) := by
      rw [factorZero_re, show Real.log r = (σ : ℝ) * Real.log p by
        rw [r, Real.log_rpow hp0]]
      exact mul_div_cancel_right₀ _ (Real.log_pos hpR).ne'
    have hz : localFactor p (r + u) (factorZero p r) = 0 := by
      rw [← hparam]
      exact localFactor_factorZero hp.one_lt (by linarith only [hr])
    have he : completedFactor p (r + u) (factorZero p r) = 0 := by
      rw [← cpow_mul_localFactor hp.ne_zero, hz, mul_zero]
    have hs1 : factorZero p r ≠ 1 := by
      intro h
      have hreal := congrArg Complex.re h
      rw [hre, Complex.one_re] at hreal
      exact σ.property.2.ne hreal
    refine ⟨factorZero p r, hre, ?_, ?_⟩
    · rw [completedXi, he, zero_mul]
    · change (continuation hp.ne_zero (r + u)).value (factorZero p r) = 0
      rw [continuation_eq hp.ne_zero _ hs1, hz, zero_mul]
  · have hnR : ‖-(r : ℂ)‖ = r := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith only [hr])]
    have hnU : ‖-(u : ℂ)‖ = u := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith only [hu])]
    have hadd : -(r : ℂ) + -(u : ℂ) = -((r + u : ℝ) : ℂ) := by push_cast; ring
    have hmul : -(r : ℂ) * -(u : ℂ) = p := by
      rw [neg_mul_neg, ← Complex.ofReal_mul, hru, Complex.ofReal_natCast]
    refine ⟨logarithmicCoeffs hp (-(r : ℂ)) (-(u : ℂ)),
      fun n hn => eulerLogCoeff_primePower hp _ _ hn, ?_, eulerLogCoeff_prime_sq_neg hp hr hu⟩
    intro s hs
    refine ⟨logarithmicCoeffs_summable hp (hnR.trans_le hrp) (hnU.trans_le hup) hs, ?_⟩
    change Complex.exp (LSeries (logarithmicCoeffs hp (-(r : ℂ)) (-(u : ℂ))) s) =
      (continuation hp.ne_zero (r + u)).value s
    rw [logarithmicCoeffs_exp hp hadd hmul (hnR.trans_le hrp) (hnU.trans_le hup) hs,
      continuation_eq hp.ne_zero _ (by intro h; subst s; norm_num at hs)]

end PositiveEulerHorizon

end GaloisForLFunctions.BlackHoleRingdown
