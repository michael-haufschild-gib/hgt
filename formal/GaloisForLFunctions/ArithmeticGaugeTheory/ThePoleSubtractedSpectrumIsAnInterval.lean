import GaloisForLFunctions.ArithmeticGaugeTheory.ThePoleDoesNotDecideTheHalfPowerLaw
import GaloisForLFunctions.RHTower.QuasiRHQuotientHeadAndFiniteContactAbscissaLaw
import GaloisForLFunctions.RHTower.QuasiRHPowerMeshSquareSampleAndObserverJetAbscissaLaw
import GaloisForLFunctions.RHTower.ChebyshevSchmidtOmega

/-!
# The pole-subtracted spectrum of the gauge torus is `[Θ, 1]`

For a gauge point `y` let `E(y)` be the pole-subtracted exponent of the prime source,
`‖ψ_y(N) − N‖ ≪ (N+1)^{E(y)+ε}` (`poleSubtractedExponent`). The range of `E` over the whole gauge
torus is exactly the interval `[Θ, 1]`, `Θ = sup Re ρ` the zero abscissa, and the trivial point is a
minimizer. RH is the statement that the spectrum is `[1/2, 1]`.

* **Coherence** (`re_twistedPsi_le`). `Re ψ_y(N) ≤ ψ(N)`: the twist only rotates nonnegative
  weights. A law of exponent `a` at any `y` is therefore a one-sided bound `ψ(N) − N ≥ −C(N+1)^a`.
* **The floor `1/2`** (`half_le_poleSubtractedExponent`). Schmidt's oscillation
  `ψ(x) − x < −c√x` for arbitrarily large `x` gives `E(y) ≥ 1/2` at every point.
* **The floor `Θ`** (`zetaZeroAbscissa_le_poleSubtractedExponent`). The one-sided lower strip law of
  the square-sample sum turns `ψ(N) − N ≥ −C N^a` into `Θ ≤ a`; so `E(y) ≥ Θ` at every point.
* **The minimum** (`poleSubtractedExponent_zero`). `E(0) = Θ`, by the unconditional bound
  `|ψ(N) − N| ≪ N^{Θ+ε}`.
* **The maximum** (`poleSubtractedExponent_le_one`, `ae_poleSubtractedExponent_eq_one`). `E ≤ 1`
  by Chebyshev, and `E = 1` at Haar-almost every point, where the source has no pole.
* **The spectrum** (`range_poleSubtractedExponent`). With the flip points of
  `ThePoleDoesNotDecideTheHalfPowerLaw` (`E(x_θ) = θ` for `Θ < θ < 1`) the range is `[Θ, 1]`.
* **RH** (`riemannHypothesis_iff_range_poleSubtractedExponent`,
  `riemannHypothesis_iff_poleSubtractedExponent_zero`). RH iff the spectrum is `[1/2, 1]` iff the
  trivial point attains `1/2`.
-/

open Finset Filter Topology MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

/-! ### Coherence and the trivial bounds -/

theorem psi_natCast_eq_sum (N : ℕ) : Chebyshev.psi N = ∑ n ∈ Ioc 0 N, Λ n := by
  rw [Chebyshev.psi, Nat.floor_natCast]

/-- **Coherence**: `Re ψ_y(N) ≤ ψ(N)`. -/
theorem re_twistedPsi_le (N : ℕ) (y : GaugeTorus) : (twistedPsi N y).re ≤ Chebyshev.psi N := by
  rw [psi_natCast_eq_sum, twistedPsi, Complex.re_sum]
  refine sum_le_sum fun n _ => ?_
  rw [Complex.re_ofReal_mul]
  exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
    ((Complex.re_le_norm _).trans (norm_twist y n).le)

theorem norm_twistedPsi_le (N : ℕ) (y : GaugeTorus) : ‖twistedPsi N y‖ ≤ Chebyshev.psi N := by
  rw [psi_natCast_eq_sum, twistedPsi]
  refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
  rw [norm_mul, norm_twist, mul_one, Complex.norm_real,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- Chebyshev's bound: every point satisfies the law of exponent `1`. -/
theorem poleSubtractedPowerLaw_one (y : GaugeTorus) : PoleSubtractedPowerLaw y 1 := by
  refine ⟨Real.log 4 + 5, by positivity, fun N => ?_⟩
  have h1 := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (α := ℝ) N)
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [Real.rpow_one]
  calc ‖twistedPsi N y - N‖ ≤ ‖twistedPsi N y‖ + ‖(N : ℂ)‖ := norm_sub_le _ _
    _ ≤ Chebyshev.psi N + N := add_le_add (norm_twistedPsi_le N y) (by simp)
    _ ≤ _ := by nlinarith

theorem poleSubtractedExponent_le_one (y : GaugeTorus) : poleSubtractedExponent y ≤ 1 :=
  csInf_le ⟨0, fun _ ha => ha.1⟩ ⟨zero_le_one, poleSubtractedPowerLaw_one y⟩

/-- A law at any point is a one-sided bound for `ψ − N`. -/
theorem psi_sub_ge_of_bound {y : GaugeTorus} {a C : ℝ}
    (h : ∀ N : ℕ, ‖twistedPsi N y - N‖ ≤ C * ((N : ℝ) + 1) ^ a) (N : ℕ) :
    -(C * ((N : ℝ) + 1) ^ a) ≤ Chebyshev.psi N - N := by
  have h1 := re_twistedPsi_le N y
  have h2 : -(C * ((N : ℝ) + 1) ^ a) ≤ (twistedPsi N y - N).re := by
    have := (Complex.abs_re_le_norm (twistedPsi N y - N)).trans (h N)
    linarith [neg_abs_le (twistedPsi N y - N).re]
  rw [Complex.sub_re, Complex.natCast_re] at h2
  linarith

/-! ### The floors -/

/-- **The floor `1/2`** at every gauge point (Schmidt's oscillation and coherence). -/
theorem half_le_poleSubtractedExponent (y : GaugeTorus) : 1 / 2 ≤ poleSubtractedExponent y := by
  refine le_csInf ⟨1, zero_le_one, poleSubtractedPowerLaw_one y⟩ ?_
  rintro a ⟨ha0, C, hC, hb⟩
  by_contra hlt
  push Not at hlt
  have hlow := psi_sub_ge_of_bound hb
  obtain ⟨c, hc, hneg, -⟩ := RHTower.chebyshevPsi_sub_omega_pm
  set K := C * 2 ^ a + 1
  -- `K x^a < c √x` eventually, since `a < 1/2`.
  have hev : ∀ᶠ x : ℝ in atTop, K * x ^ a < c * Real.sqrt x := by
    filter_upwards [(tendsto_rpow_atTop (sub_pos.mpr hlt)).eventually_gt_atTop (K / c),
      eventually_gt_atTop 0] with x hx hx0
    have hxa : 0 < x ^ a := Real.rpow_pos_of_pos hx0 a
    rw [div_lt_iff₀ hc] at hx
    have hsq : Real.sqrt x = x ^ a * x ^ (1 / 2 - a) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]; ring_nf
    rw [hsq]
    nlinarith [mul_lt_mul_of_pos_left hx hxa]
  obtain ⟨x, hx1, hx2, hx3⟩ := (hneg.and_eventually (hev.and (eventually_ge_atTop 1))).exists
  set n := ⌊x⌋₊
  have hψ : Chebyshev.psi x = Chebyshev.psi n := by
    rw [Chebyshev.psi, Chebyshev.psi, Nat.floor_natCast]
  have hn : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hn1 : x < n + 1 := Nat.lt_floor_add_one x
  have hl := hlow n
  have hpow : ((n : ℝ) + 1) ^ a ≤ 2 ^ a * x ^ a := by
    rw [← Real.mul_rpow (by norm_num) (by linarith)]
    exact Real.rpow_le_rpow (by positivity) (by linarith) ha0
  have hxa : 1 ≤ x ^ a := Real.one_le_rpow hx3 ha0
  have : -(K * x ^ a) ≤ Chebyshev.psi x - x := by
    rw [hψ]
    have := mul_le_mul_of_nonneg_left hpow hC
    simp only [K]
    nlinarith
  linarith

/-- A pole-subtracted law of exponent `a ≥ 1/2` anywhere on the torus bounds the zero abscissa. -/
theorem zetaZeroAbscissa_le_of_poleSubtractedPowerLaw {y : GaugeTorus} {a : ℝ} (ha : 1 / 2 ≤ a)
    (h : PoleSubtractedPowerLaw y a) : RHTower.zetaZeroAbscissa ≤ a := by
  obtain ⟨C, hC, hb⟩ := h
  have hlow := psi_sub_ge_of_bound hb
  have hM : 0 ≤ C * 2 ^ a := by positivity
  have ha0 : 0 ≤ a := by linarith
  have hstrip := RHTower.zetaZeroAbscissa_le_half_add_max_of_neg_rpow_le_psiRemainder_squareSum
    (c := a - 1 / 2) (N₀ := 1) hM (fun N hN => ?_)
  · rw [max_eq_right (by linarith)] at hstrip
    linarith
  -- Each square sample is `≥ −C (s²+1)^a ≥ −C 2^a N^{2a}`.
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hterm : ∀ s ∈ Ico 1 N, -(C * 2 ^ a * (N : ℝ) ^ (2 * a)) ≤ RHTower.psiRemainder (s ^ 2) := by
    intro s hs
    obtain ⟨-, hsN⟩ := mem_Ico.mp hs
    have hl := hlow (s ^ 2)
    have hsq : ((s ^ 2 : ℕ) : ℝ) + 1 ≤ 2 * (N : ℝ) ^ 2 := by
      have : (s : ℝ) + 1 ≤ N := by exact_mod_cast hsN
      have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
      push_cast
      nlinarith
    have hpow : (((s ^ 2 : ℕ) : ℝ) + 1) ^ a ≤ 2 ^ a * (N : ℝ) ^ (2 * a) := by
      calc _ ≤ (2 * (N : ℝ) ^ 2) ^ a := Real.rpow_le_rpow (by positivity) hsq ha0
        _ = _ := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
            ← Real.rpow_mul (by positivity)]
          push_cast
          ring_nf
    unfold RHTower.psiRemainder
    rw [RHTower.chebyshevPsi_eq_psi]
    nlinarith [mul_le_mul_of_nonneg_left hpow hC]
  have hsum := sum_le_sum hterm
  rw [sum_const, Nat.card_Ico, nsmul_eq_mul] at hsum
  have hNa : (N : ℝ) ^ (2 + 2 * (a - 1 / 2)) = (N : ℝ) * (N : ℝ) ^ (2 * a) := by
    rw [show (2 : ℝ) + 2 * (a - 1 / 2) = 1 + 2 * a by ring, Real.rpow_add (by linarith),
      Real.rpow_one]
  have hcast : ((N - 1 : ℕ) : ℝ) ≤ N := by
    rw [Nat.cast_sub (by exact_mod_cast hN)]; linarith
  have hpos : 0 ≤ C * 2 ^ a * (N : ℝ) ^ (2 * a) := by positivity
  rw [hNa]
  nlinarith [mul_le_mul_of_nonneg_right hcast hpos, sq_nonneg (N : ℝ)]

/-- **The floor `Θ`** at every gauge point. -/
theorem zetaZeroAbscissa_le_poleSubtractedExponent (y : GaugeTorus) :
    RHTower.zetaZeroAbscissa ≤ poleSubtractedExponent y := by
  have hhalf := half_le_poleSubtractedExponent y
  refine le_of_forall_gt fun b hb => ?_
  obtain ⟨a, ⟨-, hla⟩, hab⟩ :=
    exists_lt_of_csInf_lt (s := {a | 0 ≤ a ∧ PoleSubtractedPowerLaw y a})
      ⟨1, zero_le_one, poleSubtractedPowerLaw_one y⟩ hb
  exact (zetaZeroAbscissa_le_of_poleSubtractedPowerLaw (le_max_right a (1 / 2))
    (hla.mono (le_max_left _ _))).trans_lt (max_lt hab (by linarith))

/-! ### The minimum and the maximum -/

/-- **The trivial point attains the floor**: `E(0) = Θ`. -/
theorem poleSubtractedExponent_zero : poleSubtractedExponent 0 = RHTower.zetaZeroAbscissa := by
  refine le_antisymm ?_ (zetaZeroAbscissa_le_poleSubtractedExponent 0)
  refine le_of_forall_gt fun b hb => ?_
  obtain ⟨c, hΘc, hcb⟩ := exists_between hb
  have hΘ := RHTower.half_le_zetaZeroAbscissa
  obtain ⟨C, hC, hR⟩ :=
    RHTower.exists_psiRemainder_le_rpow_zetaZeroAbscissa (c - RHTower.zetaZeroAbscissa)
      (sub_pos.mpr hΘc)
  have hlaw : PoleSubtractedPowerLaw 0 c := by
    refine ⟨C, hC, fun N => ?_⟩
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simpa [twistedPsi] using hC
    have h := hR N hN
    rw [show RHTower.zetaZeroAbscissa + (c - RHTower.zetaZeroAbscissa) = c by ring] at h
    unfold RHTower.psiRemainder at h
    rw [RHTower.chebyshevPsi_eq_psi] at h
    rw [twistedPsi_zero, ← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg N) (by linarith) (by linarith)) hC)
  exact (csInf_le (s := {a | 0 ≤ a ∧ PoleSubtractedPowerLaw 0 a}) ⟨0, fun _ ha => ha.1⟩
    ⟨by linarith, hlaw⟩).trans_lt hcb

/-- **The trivial point is a minimizer** of the pole-subtracted exponent. -/
theorem poleSubtractedExponent_zero_le (y : GaugeTorus) :
    poleSubtractedExponent 0 ≤ poleSubtractedExponent y :=
  poleSubtractedExponent_zero ▸ zetaZeroAbscissa_le_poleSubtractedExponent y

/-- **Haar-almost every point has exponent `1`**: its source has no pole. -/
theorem ae_poleSubtractedExponent_eq_one : ∀ᵐ y ∂gaugeHaar, poleSubtractedExponent y = 1 := by
  filter_upwards [ae_norm_twistedPsi_le] with y ⟨C, hC, hb⟩
  refine le_antisymm (poleSubtractedExponent_le_one y)
    (le_csInf ⟨1, zero_le_one, poleSubtractedPowerLaw_one y⟩ ?_)
  rintro a ⟨-, C', hC', hb'⟩
  by_contra hlt
  push Not at hlt
  set b := max a (3 / 4)
  have hb1 : b < 1 := max_lt hlt (by norm_num)
  set K := C' + C * 13 ^ 3
  -- `N ≤ K (N+1)^b` for every `N`.
  have hK : ∀ N : ℕ, (N : ℝ) ≤ K * ((N : ℝ) + 1) ^ b := by
    intro N
    have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
    have hlog : 1 + Real.log ((N : ℝ) + 1) ≤ 13 * ((N : ℝ) + 1) ^ ((1 : ℝ) / 12) := by
      have := Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)
        (by norm_num : (0 : ℝ) < 1 / 12)
      have h1 : 1 ≤ ((N : ℝ) + 1) ^ ((1 : ℝ) / 12) := Real.one_le_rpow hN1 (by norm_num)
      have h12 : ((N : ℝ) + 1) ^ ((1 : ℝ) / 12) / (1 / 12) = 12 * ((N : ℝ) + 1) ^ ((1 : ℝ) / 12) := by
        field_simp
      linarith
    have h0 : 0 ≤ 1 + Real.log ((N : ℝ) + 1) := by linarith [Real.log_nonneg hN1]
    have hcube : (1 + Real.log ((N : ℝ) + 1)) ^ 3 ≤ 13 ^ 3 * ((N : ℝ) + 1) ^ ((1 : ℝ) / 4) := by
      calc _ ≤ (13 * ((N : ℝ) + 1) ^ ((1 : ℝ) / 12)) ^ 3 := pow_le_pow_left₀ h0 hlog 3
        _ = _ := by
          rw [mul_pow, ← Real.rpow_natCast (((N : ℝ) + 1) ^ ((1 : ℝ) / 12)) 3,
            ← Real.rpow_mul (by positivity)]
          norm_num
    have h3 : Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 3 ≤
        13 ^ 3 * ((N : ℝ) + 1) ^ b := by
      rw [Real.sqrt_eq_rpow]
      calc _ ≤ ((N : ℝ) + 1) ^ ((1 : ℝ) / 2) * (13 ^ 3 * ((N : ℝ) + 1) ^ ((1 : ℝ) / 4)) :=
            mul_le_mul_of_nonneg_left hcube (by positivity)
        _ = 13 ^ 3 * ((N : ℝ) + 1) ^ ((3 : ℝ) / 4) := by
            rw [mul_left_comm, ← Real.rpow_add (by positivity)]; norm_num
        _ ≤ 13 ^ 3 * ((N : ℝ) + 1) ^ b :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hN1 (le_max_right _ _)) (by positivity)
    have h4 : C' * ((N : ℝ) + 1) ^ a ≤ C' * ((N : ℝ) + 1) ^ b :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 (le_max_left _ _)) hC'
    calc (N : ℝ) = ‖twistedPsi N y - (twistedPsi N y - N)‖ := by simp
      _ ≤ ‖twistedPsi N y‖ + ‖twistedPsi N y - N‖ := norm_sub_le _ _
      _ ≤ C * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 3 +
            C' * ((N : ℝ) + 1) ^ a := add_le_add (hb N) (hb' N)
      _ ≤ C * (13 ^ 3 * ((N : ℝ) + 1) ^ b) + C' * ((N : ℝ) + 1) ^ b := by
          rw [mul_assoc C]
          exact add_le_add (mul_le_mul_of_nonneg_left h3 hC) h4
      _ = _ := by simp only [K]; ring
  -- `(N+1)^{1−b} ≤ K + 1` for every `N` contradicts `(N+1)^{1−b} → ∞`.
  have hgrow : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (1 - b)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hb1)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  obtain ⟨N, hN⟩ := (hgrow.eventually_gt_atTop (K + 1)).exists
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hsplit : (N : ℝ) + 1 = ((N : ℝ) + 1) ^ (1 - b) * ((N : ℝ) + 1) ^ b := by
    rw [← Real.rpow_add hN1, sub_add_cancel, Real.rpow_one]
  have hb0 : 1 ≤ ((N : ℝ) + 1) ^ b :=
    Real.one_le_rpow (by linarith) (le_trans (by norm_num) (le_max_right a (3 / 4)))
  have hKN := hK N
  have hK0 : 0 ≤ K := by positivity
  have : ((N : ℝ) + 1) ^ (1 - b) * ((N : ℝ) + 1) ^ b ≤ (K + 1) * ((N : ℝ) + 1) ^ b := by
    rw [← hsplit]; nlinarith
  have hb0' : 0 < ((N : ℝ) + 1) ^ b := by positivity
  nlinarith [mul_lt_mul_of_pos_right hN hb0']

/-! ### The spectrum -/

/-- **The pole-subtracted spectrum of the gauge torus is `[Θ, 1]`.** -/
theorem range_poleSubtractedExponent :
    Set.range poleSubtractedExponent = Set.Icc RHTower.zetaZeroAbscissa 1 := by
  ext θ
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨zetaZeroAbscissa_le_poleSubtractedExponent y, poleSubtractedExponent_le_one y⟩
  · rintro ⟨h0, h1⟩
    rcases h0.eq_or_lt with h | h
    · exact ⟨0, poleSubtractedExponent_zero.trans h⟩
    rcases h1.eq_or_lt with h' | h'
    · obtain ⟨y, hy⟩ := ae_poleSubtractedExponent_eq_one.exists
      exact ⟨y, hy.trans h'.symm⟩
    · exact ⟨flipPoint θ, poleSubtractedExponent_flipPoint (poleSubtractedExponent_zero ▸ h) h'⟩

/-- **RH iff the trivial point attains `1/2`.** -/
theorem riemannHypothesis_iff_poleSubtractedExponent_zero :
    RiemannHypothesis ↔ poleSubtractedExponent 0 = 1 / 2 := by
  rw [poleSubtractedExponent_zero, RHTower.zetaZeroAbscissa_eq_half_iff_riemannHypothesis]

/-- **RH iff the pole-subtracted spectrum is `[1/2, 1]`.** -/
theorem riemannHypothesis_iff_range_poleSubtractedExponent :
    RiemannHypothesis ↔ Set.range poleSubtractedExponent = Set.Icc (1 / 2) 1 := by
  rw [range_poleSubtractedExponent, ← RHTower.zetaZeroAbscissa_eq_half_iff_riemannHypothesis]
  constructor
  · intro h; rw [h]
  · intro h
    have hmem : (1 / 2 : ℝ) ∈ Set.Icc RHTower.zetaZeroAbscissa 1 := by
      rw [h]; exact ⟨le_rfl, by norm_num⟩
    exact le_antisymm hmem.1 RHTower.half_le_zetaZeroAbscissa

end GaloisForLFunctions.ArithmeticGaugeTheory
