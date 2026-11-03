import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheZeroLedgerOfTheBulk
import GaloisForLFunctions.RHTower.ZetaEulerMaclaurinArbitraryOrder
import GaloisForLFunctions.RHTower.ZetaZeroCountUpperBound
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa
import GaloisForLFunctions.RHTower.CompactTestXiDivisibilityObstruction
import GaloisForLFunctions.SquareRootThreshold.ModulatedLagFamilySeesNearTopZerosOfZeta

/-!
# The bulk is blind to the low zeros

A zero `ρ` of `ζ` enters the normalized complete form of a fixed conductor packet
`x = Σ_{e∈E} y_e r_e` only through the pole coefficient `y_1` (`tendsto_bulkLedger`). This file
makes the statement uniform over all zeros below a height growing with `N`.

* **Second-order Euler–Maclaurin on the strip** (`norm_zetaStripError_le`):
  `‖Σ_{k≤M} k^{−w} − M^{1−w}/(1−w) − ζ(w)‖ ≤ (2 + ‖w‖) M^{−Re w}` for `‖w‖ ≤ M`, with no loss
  near `Re w = 0`.
* **The conductor polynomial at a zero** (`norm_conductorDirichlet_sub_horizonTerm_le`): if
  `ζ(1 − s) = 0`, `0 < Re s < 1`, then `‖D_e(s;N) − [e = 1]N^s/s‖ ≤ 4e³(5 + ‖s‖) N^{Re s − 1}`
  for `N ≥ 2e(‖s‖ + 2)`.
* **One zero, explicitly** (`norm_log_div_mul_bulkLedger_le`): for a pole-free packet
  (`y_1 = 0`), `(log N/c)|W_ρ|/∫g² ≤ C m_ρ (6 + |ρ|)²/N²` as soon as `N ≳ |ρ|` and `c|ρ| ≲ N`.
* **All low zeros together** (`tendsto_sum_bulkLedger_lowZeros`): with the zero count
  `#{|γ| ≤ T} ≪ T log T` and `m_ρ ≪ log|γ|`, the zeros of height `≤ T_N` contribute
  `O(T_N³ log² T_N/N²)` in total; so whenever `T_N³ log² T_N/N² → 0` and `c_N T_N/N → 0` their
  total ledger is `o(c_N/log N)`. In particular every height `T_N = N^θ`, `θ < 2/3`, is invisible
  (`tendsto_sum_bulkLedger_lowZeros_rpow`).

The bulk away from the pole does not see the zeros below the resolution height collectively: its
second-order term, if any, comes from zeros at heights comparable to `N/c`, where the atoms
resolve them.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open BezoutValuationIncidence SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  ArithmeticCastelnuovoSeveri

/-! ### Euler–Maclaurin at second order -/

/-- **Second-order Euler–Maclaurin on the strip**: for `0 < Re w`, `w ≠ 1`, `1 ≤ M`, `‖w‖ ≤ M`,
`‖Σ_{k≤M} k^{−w} − M^{1−w}/(1−w) − ζ(w)‖ ≤ (2 + ‖w‖) M^{−Re w}`. -/
theorem norm_zetaStripError_le {w : ℂ} (hw0 : 0 < w.re) (hw1 : w ≠ 1) {M : ℕ} (hM : 1 ≤ M)
    (hwM : ‖w‖ ≤ M) : ‖RHTower.zetaStripError w M‖ ≤ (2 + ‖w‖) * (M : ℝ) ^ (-w.re) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hEM := RHTower.norm_riemannZeta_sub_zetaEulerMaclaurinMain_le hw0 hw1 hM 0
  have hR : RHTower.complexRisingFactor w (2 * 0 + 2) = w * (w + 1) := by
    simp [RHTower.complexRisingFactor, Finset.prod_range_succ]
  have hB : |((bernoulli (2 * 0 + 2) : ℚ) : ℝ)| / ((2 * 0 + 2).factorial : ℝ) = 1 / 12 := by
    norm_num [bernoulli_two, Nat.factorial]
  set X := (M : ℝ) ^ (-w.re) with hX
  have hX0 : 0 < X := Real.rpow_pos_of_pos hM0 _
  have hexp : (M : ℝ) ^ (1 - w.re - ((2 * 0 + 2 : ℕ) : ℝ)) = X * (M : ℝ)⁻¹ := by
    rw [show 1 - w.re - ((2 * 0 + 2 : ℕ) : ℝ) = -w.re + (-1) by push_cast; ring,
      Real.rpow_add hM0, Real.rpow_neg_one]
  have hden : w.re + ((2 * 0 + 2 : ℕ) : ℝ) - 1 = w.re + 1 := by push_cast; ring
  rw [hB, hR, hexp, hden, norm_mul] at hEM
  have hbd : ‖RHTower.zetaEMBoundary 0 w M‖ ≤ X / 2 + 1 / 12 * (‖w‖ * (X * (M : ℝ)⁻¹)) := by
    rw [RHTower.zetaEMBoundary, Finset.sum_range_one]
    refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) (le_of_eq ?_))
    · rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hM0, Complex.neg_re]
      norm_num
      exact hX.symm
    · have hr1 : ‖RHTower.complexRisingFactor w (2 * 0 + 1)‖ = ‖w‖ := by
        simp [RHTower.complexRisingFactor]
      have hpw : (M : ℝ) ^ (-w.re - ((2 * 0 + 1 : ℕ) : ℝ)) = X * (M : ℝ)⁻¹ := by
        rw [show -w.re - ((2 * 0 + 1 : ℕ) : ℝ) = -w.re + (-1) by push_cast; ring,
          Real.rpow_add hM0, Real.rpow_neg_one]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, Nat.abs_cast, hB,
        RHTower.norm_complexPowerTower _ _ hM0, hr1, hpw]
  have hid : RHTower.zetaStripError w M =
      -(riemannZeta w - RHTower.zetaEulerMaclaurinMain 0 M w) + RHTower.zetaEMBoundary 0 w M := by
    unfold RHTower.zetaStripError RHTower.zetaEulerMaclaurinMain
    push_cast
    ring
  have h1 : ‖w‖ * (M : ℝ)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hM0, one_mul]; exact hwM
  have h2 : (w.re + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hw1' : ‖w + 1‖ ≤ ‖w‖ + 1 := (norm_add_le _ _).trans (by rw [norm_one])
  rw [hid]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg]
  have ht1 : 1 / 12 * (‖w‖ * ‖w + 1‖) * (X * (M : ℝ)⁻¹ / (w.re + 1)) ≤
      1 / 12 * (‖w‖ + 1) * X := by
    have : ‖w‖ * ‖w + 1‖ * (X * (M : ℝ)⁻¹ / (w.re + 1)) =
        ‖w + 1‖ * X * ((‖w‖ * (M : ℝ)⁻¹) * (w.re + 1)⁻¹) := by ring
    calc 1 / 12 * (‖w‖ * ‖w + 1‖) * (X * (M : ℝ)⁻¹ / (w.re + 1))
        = 1 / 12 * (‖w + 1‖ * X * ((‖w‖ * (M : ℝ)⁻¹) * (w.re + 1)⁻¹)) := by rw [mul_assoc, this]
      _ ≤ 1 / 12 * ((‖w‖ + 1) * X * (1 * 1)) := by gcongr
      _ = _ := by ring
  have ht3 : 1 / 12 * (‖w‖ * (X * (M : ℝ)⁻¹)) ≤ 1 / 12 * X := by
    have : ‖w‖ * (X * (M : ℝ)⁻¹) = X * (‖w‖ * (M : ℝ)⁻¹) := by ring
    rw [this]; gcongr; exact mul_le_of_le_one_right hX0.le h1
  have hn : 0 ≤ ‖w‖ := norm_nonneg w
  nlinarith [hEM, hbd, ht1, ht3]

/-! ### The conductor polynomial at a zero -/

theorem abs_moebiusReal_le (n : ℕ) : |moebiusReal n| ≤ 1 := by
  unfold moebiusReal; exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- One divisor of the Möbius splitting at a zero: with `M = ⌊N/d⌋`,
`‖ζ(1−s) + (M^s − (N/d)^s)/s + E(1−s, M)‖ ≤ (5 + ‖s‖) M^{Re s − 1}`. -/
theorem norm_divisorTerm_le {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta (1 - s) = 0) {d N : ℕ} (hd : 1 ≤ d) (hN : 2 * d * (‖s‖ + 2) ≤ N) :
    ‖riemannZeta (1 - s) + ((((N / d : ℕ) : ℝ) : ℂ) ^ s - (((N : ℝ) / d : ℝ) : ℂ) ^ s) / s +
        RHTower.zetaStripError (1 - s) (N / d)‖ ≤
      (5 + ‖s‖) * ((N / d : ℕ) : ℝ) ^ (s.re - 1) := by
  have hs0' : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs0; exact lt_irrefl 0 hs0
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0'
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨M, hM⟩ : ∃ M, M = N / d := ⟨_, rfl⟩
  rw [← hM]
  have hMd : (N : ℝ) < ((M : ℝ) + 1) * d := by
    have := Nat.lt_div_mul_add (a := N) (b := d) (by omega)
    rw [← hM] at this
    have h' : (N : ℝ) < ((M * d + d : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h'; linarith
  have hNd : 2 * (‖s‖ + 2) ≤ (N : ℝ) / d := by rw [le_div_iff₀ hd0]; linarith
  have hlt : (N : ℝ) / d < (M : ℝ) + 1 := by rw [div_lt_iff₀ hd0]; linarith
  have hM1 : ‖s‖ + 2 ≤ (M : ℝ) := by linarith [norm_nonneg s]
  have hM1' : 1 ≤ M := by
    have : (1 : ℝ) ≤ M := by linarith [norm_nonneg s]
    exact_mod_cast this
  have hfl : ⌊(N : ℝ) / d⌋₊ = M := by rw [hM]; exact Nat.floor_div_eq_div N d
  have hNd1 : (1 : ℝ) ≤ (N : ℝ) / d := by linarith [norm_nonneg s]
  have hflo := RHTower.norm_cpow_natFloor_sub_cpow_le (s := s) hNd1 (by rw [hfl]; linarith)
  rw [hfl] at hflo
  have hw0 : 0 < (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hw1 : (1 : ℂ) - s ≠ 1 := fun h => hs0' (by linear_combination -h)
  have hwn : ‖(1 : ℂ) - s‖ ≤ 1 + ‖s‖ := (norm_sub_le _ _).trans (by rw [norm_one])
  have hstr := norm_zetaStripError_le hw0 hw1 hM1' (by linarith)
  have hre : -(1 - s).re = s.re - 1 := by simp only [Complex.sub_re, Complex.one_re]; ring
  rw [hre] at hstr
  rw [hz, zero_add]
  refine (norm_add_le _ _).trans ?_
  rw [norm_div]
  have hX : 0 ≤ (M : ℝ) ^ (s.re - 1) := by positivity
  calc ‖(((M : ℝ) : ℂ)) ^ s - (((N : ℝ) / d : ℝ) : ℂ) ^ s‖ / ‖s‖ +
        ‖RHTower.zetaStripError (1 - s) M‖
      ≤ 2 * ‖s‖ * (M : ℝ) ^ (s.re - 1) / ‖s‖ + (2 + ‖1 - s‖) * (M : ℝ) ^ (s.re - 1) :=
        add_le_add (div_le_div_of_nonneg_right hflo hsn.le) hstr
    _ = 2 * (M : ℝ) ^ (s.re - 1) + (2 + ‖1 - s‖) * (M : ℝ) ^ (s.re - 1) := by
        field_simp
    _ ≤ (5 + ‖s‖) * (M : ℝ) ^ (s.re - 1) := by nlinarith

/-- **The conductor polynomial at a zero.** If `ζ(1 − s) = 0` and `0 < Re s < 1`, then for
`N ≥ 2e(‖s‖ + 2)`: `‖D_e(s;N) − [e = 1] N^s/s‖ ≤ 4e³(5 + ‖s‖) N^{Re s − 1}`. -/
theorem norm_conductorDirichlet_sub_horizonTerm_le {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta (1 - s) = 0) {e N : ℕ} (he : 1 ≤ e) (hN : 2 * e * (‖s‖ + 2) ≤ N) :
    ‖conductorDirichlet e N s - horizonTerm e N s‖ ≤
      4 * (e : ℝ) ^ 3 * (5 + ‖s‖) * (N : ℝ) ^ (s.re - 1) := by
  have hs0' : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs0; exact lt_irrefl 0 hs0
  have hrw : conductorDirichlet e N s - horizonTerm e N s =
      ∑ d ∈ e.divisors, (moebiusReal (e / d) : ℂ) * ((d : ℝ) : ℂ) ^ s *
        (riemannZeta (1 - s) + ((((N / d : ℕ) : ℝ) : ℂ) ^ s - (((N : ℝ) / d : ℝ) : ℂ) ^ s) / s +
          RHTower.zetaStripError (1 - s) (N / d)) := by
    rw [conductorDirichlet_eq, horizonTerm_eq_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun d _ => ?_
    rw [partialZeta_eq]
    field_simp
    ring
  rw [hrw]
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hN0 : (0 : ℝ) < N := by nlinarith [norm_nonneg s]
  have hσ : s.re - 1 ≤ 0 := by linarith
  have hterm : ∀ d ∈ e.divisors, ‖(moebiusReal (e / d) : ℂ) * ((d : ℝ) : ℂ) ^ s *
      (riemannZeta (1 - s) + ((((N / d : ℕ) : ℝ) : ℂ) ^ s - (((N : ℝ) / d : ℝ) : ℂ) ^ s) / s +
        RHTower.zetaStripError (1 - s) (N / d))‖ ≤
      4 * (e : ℝ) ^ 2 * (5 + ‖s‖) * (N : ℝ) ^ (s.re - 1) := by
    intro d hd
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    have hde : d ≤ e := Nat.divisor_le hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have hdeR : (d : ℝ) ≤ e := by exact_mod_cast hde
    have hNd : 2 * d * (‖s‖ + 2) ≤ (N : ℝ) := le_trans (by gcongr) hN
    have hdiv := norm_divisorTerm_le hs0 hs1 hz hd1 hNd
    have hμ : ‖(moebiusReal (e / d) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_moebiusReal_le _
    have hds : ‖((d : ℝ) : ℂ) ^ s‖ ≤ e := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hd0]
      calc (d : ℝ) ^ s.re ≤ (d : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hd1) hs1.le
        _ = d := Real.rpow_one _
        _ ≤ e := hdeR
    -- `⌊N/d⌋ ≥ N/(2e)`, so `⌊N/d⌋^{σ−1} ≤ 2e N^{σ−1}`
    have hMd : (N : ℝ) / (2 * e) ≤ ((N / d : ℕ) : ℝ) := by
      have h1 := Nat.lt_div_mul_add (a := N) (b := d) (by omega)
      have h1' : (N : ℝ) < (((N / d) * d + d : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h1'
      have hNd' : 2 * (‖s‖ + 2) ≤ (N : ℝ) / d := by rw [le_div_iff₀ hd0]; linarith
      have hlt : (N : ℝ) / d < ((N / d : ℕ) : ℝ) + 1 := by rw [div_lt_iff₀ hd0]; linarith
      have hge1 : (1 : ℝ) ≤ ((N / d : ℕ) : ℝ) := by linarith [norm_nonneg s]
      rw [div_le_iff₀ (by positivity)]
      have : (N : ℝ) < 2 * ((N / d : ℕ) : ℝ) * d := by nlinarith
      nlinarith
    have hNpos : (0 : ℝ) < (N : ℝ) / (2 * e) := by positivity
    have hM : ((N / d : ℕ) : ℝ) ^ (s.re - 1) ≤ 2 * e * (N : ℝ) ^ (s.re - 1) := by
      refine (Real.rpow_le_rpow_of_nonpos hNpos hMd hσ).trans ?_
      rw [div_eq_mul_inv, Real.mul_rpow hN0.le (by positivity), Real.inv_rpow (by positivity),
        ← Real.rpow_neg (by positivity), mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      calc (2 * (e : ℝ)) ^ (-(s.re - 1)) ≤ (2 * (e : ℝ)) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = 2 * e := Real.rpow_one _
    rw [norm_mul, norm_mul]
    calc ‖(moebiusReal (e / d) : ℂ)‖ * ‖((d : ℝ) : ℂ) ^ s‖ *
          ‖riemannZeta (1 - s) + ((((N / d : ℕ) : ℝ) : ℂ) ^ s - (((N : ℝ) / d : ℝ) : ℂ) ^ s) / s +
            RHTower.zetaStripError (1 - s) (N / d)‖
        ≤ 1 * e * ((5 + ‖s‖) * (2 * e * (N : ℝ) ^ (s.re - 1))) := by
          gcongr
          exact hdiv.trans (mul_le_mul_of_nonneg_left hM (by positivity))
      _ ≤ 4 * (e : ℝ) ^ 2 * (5 + ‖s‖) * (N : ℝ) ^ (s.re - 1) := by
          have : 0 ≤ (5 + ‖s‖) * (N : ℝ) ^ (s.re - 1) := by positivity
          nlinarith
  refine (norm_sum_le _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [sum_const, nsmul_eq_mul]
  have hcard : (e.divisors.card : ℝ) ≤ e := by exact_mod_cast Nat.card_divisors_le_self e
  calc (e.divisors.card : ℝ) * (4 * (e : ℝ) ^ 2 * (5 + ‖s‖) * (N : ℝ) ^ (s.re - 1)) ≤
        e * (4 * (e : ℝ) ^ 2 * (5 + ‖s‖) * (N : ℝ) ^ (s.re - 1)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

/-! ### A pole-free packet at a zero -/

/-- The packet constant `Σ_{e∈E} |y_e/√φ(e)| · 4e³`. -/
def packetConst (E : Finset ℕ) (y : ℕ → ℝ) : ℝ :=
  ∑ e ∈ E, |y e / Real.sqrt e.totient| * (4 * (e : ℝ) ^ 3)

theorem packetConst_nonneg (E : Finset ℕ) (y : ℕ → ℝ) : 0 ≤ packetConst E y :=
  sum_nonneg fun e _ => by positivity

/-- **A pole-free packet at a zero**: if `y_1 = 0` (or `1 ∉ E`), then
`‖D_x(γ_s)‖ ≤ (log N)^{−1/2} P (5 + ‖s‖) N^{Re s − 1}`. -/
theorem norm_dirichletPoly_packet_le {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta (1 - s) = 0) {E : Finset ℕ} (hE : ∀ e ∈ E, 1 ≤ e) {L : ℕ}
    (hL : ∀ e ∈ E, e ≤ L) {y : ℕ → ℝ} (hpole : poleCoefficient E y = 0) {N : ℕ}
    (hN : 2 * L * (‖s‖ + 2) ≤ N) :
    ‖dirichletPoly N (packetWeights E y N) (gammaOf s)‖ ≤
      (Real.sqrt (Real.log N))⁻¹ * (packetConst E y * (5 + ‖s‖) * (N : ℝ) ^ (s.re - 1)) := by
  rw [dirichletPoly_packetWeights]
  have h0 : ∑ e ∈ E, ((y e / Real.sqrt e.totient : ℝ) : ℂ) * horizonTerm e N s = 0 := by
    rw [sum_mul_horizonTerm]
    unfold poleCoefficient at hpole
    split_ifs at hpole ⊢ with h1
    · rw [hpole]; simp
    · simp
  have hsplit : ∑ e ∈ E, ((y e / Real.sqrt e.totient : ℝ) : ℂ) * conductorDirichlet e N s =
      ∑ e ∈ E, ((y e / Real.sqrt e.totient : ℝ) : ℂ) *
        (conductorDirichlet e N s - horizonTerm e N s) := by
    rw [← sub_zero (∑ e ∈ E, _ * conductorDirichlet e N s), ← h0, ← sum_sub_distrib]
    exact sum_congr rfl fun e _ => by ring
  rw [hsplit, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  refine (norm_sum_le _ _).trans ?_
  unfold packetConst
  rw [Finset.sum_mul, Finset.sum_mul]
  refine sum_le_sum fun e he => ?_
  have hNe : 2 * e * (‖s‖ + 2) ≤ (N : ℝ) := by
    refine le_trans ?_ hN
    have : (e : ℝ) ≤ L := by exact_mod_cast hL e he
    gcongr
  have hb := norm_conductorDirichlet_sub_horizonTerm_le hs0 hs1 hz (hE e he) hNe
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |y e / Real.sqrt e.totient| * ‖conductorDirichlet e N s - horizonTerm e N s‖ ≤
        |y e / Real.sqrt e.totient| * (4 * (e : ℝ) ^ 3 * (5 + ‖s‖) * (N : ℝ) ^ (s.re - 1)) :=
        mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := by ring

/-! ### One zero, explicitly -/

/-- The transform of a profile on `[0, 1]` is bounded by `e ∫|φ|` on the unit disc. -/
theorem norm_paperFT_profile_le {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖paperFT (cx φ) z‖ ≤ (∫ u, |φ u|) * Real.exp 1 := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hint : Integrable (cx φ) :=
    (Complex.continuous_ofReal.comp hφ).integrable_of_hasCompactSupport
      (hφc.comp_left Complex.ofReal_zero)
  have hsupp : ∀ u, cx φ u ≠ 0 → |u| ≤ 1 := by
    intro u hu
    by_contra hlt
    apply hu
    have : u ∉ Set.Icc (0 : ℝ) 1 := fun hm => hlt (abs_le.mpr ⟨by linarith [hm.1], hm.2⟩)
    simp [cx, hφsupp u this]
  have h := RHTower.CompactTestXiDivisibility.norm_paperFT_le_exp hint hsupp z
  have hnorm : ∫ u, ‖cx φ u‖ = ∫ u, |φ u| := by
    congr 1; funext u; simp [cx, Complex.norm_real]
  rw [hnorm] at h
  refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) ?_)
  exact integral_nonneg fun u => abs_nonneg _

theorem norm_gammaOf_le (ρ : ℂ) : ‖gammaOf ρ‖ ≤ ‖ρ‖ + 1 := by
  unfold gammaOf
  rw [norm_div, Complex.norm_I, div_one]
  refine (norm_sub_le _ _).trans ?_
  have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [this]; linarith

/-- **One zero, explicitly.** For a pole-free packet and a nontrivial zero `ρ`, as soon as
`N ≥ 2L(‖ρ‖ + 3)` and `c(‖ρ‖ + 1) ≤ N`:
`(log N/c) |W_ρ|/∫g² ≤ m_ρ (e∫|φ|)²/∫φ² · P² (6 + ‖ρ‖)²/N²`. -/
theorem norm_log_div_mul_bulkLedger_le {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {E : Finset ℕ}
    (hE : ∀ e ∈ E, 1 ≤ e) {L : ℕ} (hL : ∀ e ∈ E, e ≤ L) {y : ℕ → ℝ}
    (hpole : poleCoefficient E y = 0) {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) {c : ℝ}
    (hc : 0 < c) {N : ℕ} (hN2 : 2 ≤ N) (hNL : 2 * L * (‖ρ‖ + 3) ≤ N)
    (hcN : c * (‖ρ‖ + 1) ≤ N) :
    ‖((Real.log N / c : ℝ) : ℂ) * bulkLedger zetaZeroConfig φ E y c N ρ‖ ≤
      zetaZeroConfig.mult ρ * ((∫ u, |φ u|) * Real.exp 1) ^ 2 / (∫ u, φ u ^ 2) *
        packetConst E y ^ 2 * (6 + ‖ρ‖) ^ 2 / (N : ℝ) ^ 2 := by
  obtain ⟨hζ, hβ0, hβ1⟩ : riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 := hρ
  have hz1 : riemannZeta (1 - ρ) = 0 :=
    RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hζ hβ0 hβ1
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hN0 : (0 : ℝ) < N := by have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
                               linarith
  have hlog : 0 < Real.log N := Real.log_pos (by have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
                                                 linarith)
  rw [log_div_mul_bulkLedger zetaZeroConfig hφ hφc hφ2 E y hc (by omega) ρ]
  -- the two atom factors
  have hw : ‖((c / N : ℝ) : ℂ) * gammaOf ρ‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hc hN0)]
    calc c / N * ‖gammaOf ρ‖ ≤ c / N * (‖ρ‖ + 1) :=
          mul_le_mul_of_nonneg_left (norm_gammaOf_le ρ) (by positivity)
      _ ≤ 1 := by rw [div_mul_eq_mul_div, div_le_one hN0]; exact hcN
  have hw' : ‖((c / N : ℝ) : ℂ) * conj (gammaOf ρ)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_conj, ← norm_mul]; exact hw
  have hF1 := norm_paperFT_profile_le hφ hφsupp hw
  have hF2 := norm_paperFT_profile_le hφ hφsupp hw'
  -- the two Dirichlet factors
  have hD1 := norm_dirichletPoly_packet_le hβ0 hβ1 hz1 hE hL hpole (N := N)
    (by nlinarith [norm_nonneg ρ])
  have hre1 : 0 < (1 - ρ).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hre2 : (1 - ρ).re < 1 := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hn1 : ‖(1 : ℂ) - ρ‖ ≤ 1 + ‖ρ‖ := (norm_sub_le _ _).trans (by rw [norm_one])
  have hD2 := norm_dirichletPoly_packet_le hre1 hre2 (by rw [sub_sub_cancel]; exact hζ) hE hL hpole
    (N := N) (by nlinarith [norm_nonneg ρ])
  have hσ2 : (1 - ρ).re - 1 = -ρ.re := by simp only [Complex.sub_re, Complex.one_re]; ring
  rw [hσ2] at hD2
  set P := packetConst E y with hP
  have hP0 : 0 ≤ P := packetConst_nonneg E y
  set I₁ := ∫ u, |φ u| with hI₁
  have hI₁0 : 0 ≤ I₁ := integral_nonneg fun u => abs_nonneg _
  set I := ∫ u, φ u ^ 2 with hI
  have hsq : (Real.sqrt (Real.log N))⁻¹ * (Real.sqrt (Real.log N))⁻¹ = (Real.log N)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hlog.le]
  have hpow : (N : ℝ) ^ (ρ.re - 1) * (N : ℝ) ^ (-ρ.re) = (N : ℝ)⁻¹ := by
    rw [← Real.rpow_add hN0, show ρ.re - 1 + -ρ.re = -1 by ring, Real.rpow_neg_one]
  have hDD : ‖dirichletPoly N (packetWeights E y N) (gammaOf ρ)‖ *
      ‖dirichletPoly N (packetWeights E y N) (gammaOf (1 - ρ))‖ ≤
      (Real.log N)⁻¹ * (P ^ 2 * (6 + ‖ρ‖) ^ 2 * (N : ℝ)⁻¹) := by
    calc _ ≤ ((Real.sqrt (Real.log N))⁻¹ * (P * (5 + ‖ρ‖) * (N : ℝ) ^ (ρ.re - 1))) *
          ((Real.sqrt (Real.log N))⁻¹ * (P * (5 + ‖1 - ρ‖) * (N : ℝ) ^ (-ρ.re))) :=
          mul_le_mul hD1 hD2 (norm_nonneg _) (by positivity)
      _ = (Real.log N)⁻¹ * (P ^ 2 * ((5 + ‖ρ‖) * (5 + ‖1 - ρ‖)) *
          ((N : ℝ) ^ (ρ.re - 1) * (N : ℝ) ^ (-ρ.re))) := by rw [← hsq]; ring
      _ ≤ (Real.log N)⁻¹ * (P ^ 2 * (6 + ‖ρ‖) ^ 2 * (N : ℝ)⁻¹) := by
          rw [hpow]
          gcongr
          nlinarith [norm_nonneg ρ, norm_nonneg ((1 : ℂ) - ρ)]
  rw [norm_mul, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_natCast,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hφ2, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (div_pos hlog hN0)]
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  calc (zetaZeroConfig.mult ρ : ℝ) *
        (‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * gammaOf ρ)‖ *
          ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * conj (gammaOf ρ))‖) / I *
        (Real.log N / N * (‖dirichletPoly N (packetWeights E y N) (gammaOf ρ)‖ *
          ‖dirichletPoly N (packetWeights E y N) (gammaOf (1 - ρ))‖))
      ≤ (zetaZeroConfig.mult ρ : ℝ) * ((I₁ * Real.exp 1) * (I₁ * Real.exp 1)) / I *
        (Real.log N / N * ((Real.log N)⁻¹ * (P ^ 2 * (6 + ‖ρ‖) ^ 2 * (N : ℝ)⁻¹))) := by
        gcongr
    _ = _ := by field_simp

/-! ### All low zeros together -/

/-- The multiplicities of the zeros up to height `T` sum to at most `#Z_T · 40 log(180T)`. -/
theorem sum_mult_lowZeros_le (T : ℝ) :
    ∑ ρ ∈ (RHTower.lowZeros_finite T).toFinset, (zetaZeroConfig.mult ρ : ℝ) ≤
      (RHTower.lowZeros T).ncard * (40 * Real.log (180 * T)) := by
  rw [Set.ncard_eq_toFinset_card _ (RHTower.lowZeros_finite T)]
  have hb : ∀ ρ ∈ (RHTower.lowZeros_finite T).toFinset,
      (zetaZeroConfig.mult ρ : ℝ) ≤ 40 * Real.log (180 * T) := by
    intro ρ hρ
    obtain ⟨hρc, hρT⟩ := (RHTower.lowZeros_finite T).mem_toFinset.mp hρ
    have hm := SquareRootThreshold.mult_le_log_zeta hρc
    have h1 : (1 : ℝ) ≤ zetaZeroConfig.mult ρ := by exact_mod_cast zetaZeroConfig.one_le_mult ρ hρc
    have himpos : 0 < 180 * |ρ.im| := by
      by_contra hle
      have h0 : Real.log (180 * |ρ.im|) ≤ 0 := by
        have : 180 * |ρ.im| = 0 := by linarith [abs_nonneg ρ.im]
        rw [this, Real.log_zero]
      linarith
    exact hm.trans (by gcongr)
  calc ∑ ρ ∈ (RHTower.lowZeros_finite T).toFinset, (zetaZeroConfig.mult ρ : ℝ) ≤
        ∑ _ρ ∈ (RHTower.lowZeros_finite T).toFinset, 40 * Real.log (180 * T) := sum_le_sum hb
    _ = _ := by rw [sum_const, nsmul_eq_mul]

theorem norm_le_of_mem_lowZeros {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ RHTower.lowZeros T) : ‖ρ‖ ≤ 1 + T := by
  obtain ⟨hρc, hρT⟩ := hρ
  obtain ⟨-, hβ0, hβ1⟩ : riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 := hρc
  refine (Complex.norm_le_abs_re_add_abs_im ρ).trans ?_
  rw [abs_of_pos hβ0]; linarith

/-- **The zero count along a growing height**: for `T ≥ T₀`, `Σ_{|γ| ≤ T} m_ρ ≤ K T log² T`. -/
theorem exists_sum_mult_lowZeros_le :
    ∃ K T₀ : ℝ, 0 ≤ K ∧ 3 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∑ ρ ∈ (RHTower.lowZeros_finite T).toFinset, (zetaZeroConfig.mult ρ : ℝ) ≤
        K * (T * Real.log T ^ 2) := by
  obtain ⟨C, T₁, hC, hT₁, hcount⟩ := RHTower.zeroCount_upper
  obtain ⟨c₀, hc₀⟩ := RHTower.ncard_lowZeros_le
  have hlog3 : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
  refine ⟨240 * (2 + 2 * C + c₀), T₁, by positivity, hT₁, fun T hT => ?_⟩
  have hT3 : 3 ≤ T := hT₁.trans hT
  have hT0 : 0 < T := by linarith
  have hlogT : 1 ≤ Real.log T := hlog3.trans (Real.log_le_log (by norm_num) hT3)
  have hlogTT : Real.log T ≤ T := (Real.log_le_sub_one_of_pos hT0).trans (by linarith)
  have hs := sum_mult_lowZeros_le T
  have hn := hc₀ T hT0.le
  have hN := hcount T hT
  -- `F(T) ≤ T log T`
  have hF : RHTower.zeroCountMain T ≤ T * Real.log T := by
    unfold RHTower.zeroCountMain
    have hpi := Real.pi_gt_three
    have h1 : Real.log (T / (2 * Real.pi)) ≤ Real.log T :=
      Real.log_le_log (by positivity) (div_le_self hT0.le (by linarith))
    have h2 : T / (2 * Real.pi) ≤ T := div_le_self hT0.le (by linarith)
    have h3 : 0 ≤ T / (2 * Real.pi) := by positivity
    nlinarith
  have hcard : ((RHTower.lowZeros T).ncard : ℝ) ≤ (2 + 2 * C + c₀) * (T * Real.log T) := by
    have hn' : ((RHTower.lowZeros T).ncard : ℝ) ≤ 2 * (zetaZeroConfig.N 0 T : ℝ) + c₀ := by
      exact_mod_cast hn
    have hTl : 1 ≤ T * Real.log T := by nlinarith
    have hl2 : Real.log T ^ 2 ≤ T * Real.log T := by nlinarith
    have hc0 : (0 : ℝ) ≤ c₀ := Nat.cast_nonneg _
    nlinarith
  have h180 : Real.log (180 * T) ≤ 6 * Real.log T := by
    rw [Real.log_mul (by norm_num) hT0.ne']
    have : Real.log 180 ≤ 5 * Real.log 3 := by
      rw [← Real.log_rpow (by norm_num)]
      exact Real.log_le_log (by norm_num) (by norm_num)
    have h3T : Real.log 3 ≤ Real.log T := Real.log_le_log (by norm_num) hT3
    nlinarith
  calc ∑ ρ ∈ (RHTower.lowZeros_finite T).toFinset, (zetaZeroConfig.mult ρ : ℝ) ≤
        (RHTower.lowZeros T).ncard * (40 * Real.log (180 * T)) := hs
    _ ≤ ((2 + 2 * C + c₀) * (T * Real.log T)) * (40 * (6 * Real.log T)) := by
        gcongr
        · have : 0 < Real.log (180 * T) := Real.log_pos (by nlinarith)
          positivity
    _ = 240 * (2 + 2 * C + c₀) * (T * Real.log T ^ 2) := by ring

/-- **The bulk is blind to the low zeros.** For a pole-free conductor packet (`y_1 = 0`, all
conductors `≥ 1`), every overlap schedule `c_N ≥ 1` and every height `T_N → ∞` with
`c_N T_N/N → 0` and `T_N³ log² T_N/N² → 0`, the zeros of height `≤ T_N` together contribute
`o(c_N/log N)` to the normalized complete form:
`Σ_{|γ| ≤ T_N} (log N/c_N) |W_ρ|/∫g² → 0`. -/
theorem tendsto_sum_bulkLedger_lowZeros {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {E : Finset ℕ}
    (hE : ∀ e ∈ E, 1 ≤ e) {y : ℕ → ℝ} (hpole : poleCoefficient E y = 0) {c T : ℕ → ℝ}
    (hc1 : ∀ N, 1 ≤ c N) (hT : Tendsto T atTop atTop)
    (hcT : Tendsto (fun N : ℕ => c N * T N / N) atTop (𝓝 0))
    (hT3 : Tendsto (fun N : ℕ => T N ^ 3 * Real.log (T N) ^ 2 / (N : ℝ) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑ ρ ∈ (RHTower.lowZeros_finite (T N)).toFinset,
      ‖((Real.log N / c N : ℝ) : ℂ) * bulkLedger zetaZeroConfig φ E y (c N) N ρ‖) atTop (𝓝 0) := by
  obtain ⟨K, T₀, hK, hT₀, hcount⟩ := exists_sum_mult_lowZeros_le
  set L := ∑ e ∈ E, e with hLdef
  have hL : ∀ e ∈ E, e ≤ L := fun e he =>
    Finset.single_le_sum (f := fun e : ℕ => e) (fun _ _ => Nat.zero_le _) he
  set A₀ := ((∫ u, |φ u|) * Real.exp 1) ^ 2 / (∫ u, φ u ^ 2) * packetConst E y ^ 2 with hA₀
  have hA₀0 : 0 ≤ A₀ := by
    have := packetConst_nonneg E y
    have : 0 ≤ ∫ u, |φ u| := integral_nonneg fun u => abs_nonneg _
    positivity
  have hbound : Tendsto (fun N : ℕ => A₀ * 64 * K * (T N ^ 3 * Real.log (T N) ^ 2 / (N : ℝ) ^ 2))
      atTop (𝓝 0) := by
    have := hT3.const_mul (A₀ * 64 * K)
    rwa [mul_zero] at this
  have hL1 : (0 : ℝ) < 1 / (4 * ((L : ℝ) + 1)) := by positivity
  have hev := ((hT.eventually (eventually_ge_atTop T₀)).and
    (hcT.eventually (gt_mem_nhds hL1))).and (eventually_ge_atTop (16 * (L + 1)))
  refine squeeze_zero' (Eventually.of_forall fun N => sum_nonneg fun _ _ => norm_nonneg _) ?_ hbound
  filter_upwards [hev] with N ⟨⟨hTN, hcTN⟩, hNL⟩
  have hT3' : 3 ≤ T N := hT₀.trans hTN
  have hN16 : 16 * ((L : ℝ) + 1) ≤ N := by exact_mod_cast hNL
  have hN0 : (0 : ℝ) < N := by have : (0 : ℝ) ≤ L := Nat.cast_nonneg L
                               linarith
  have hN2 : 2 ≤ N := by omega
  have hc0 : 0 < c N := by linarith [hc1 N]
  have hcTle : c N * T N * (4 * ((L : ℝ) + 1)) ≤ N := by
    rw [div_lt_iff₀ hN0, one_div_mul_eq_div, lt_div_iff₀ (by positivity)] at hcTN
    linarith
  have hTle : T N ≤ c N * T N := le_mul_of_one_le_left (by linarith) (hc1 N)
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hper : ∀ ρ ∈ (RHTower.lowZeros_finite (T N)).toFinset,
      ‖((Real.log N / c N : ℝ) : ℂ) * bulkLedger zetaZeroConfig φ E y (c N) N ρ‖ ≤
        zetaZeroConfig.mult ρ * (A₀ * (7 + T N) ^ 2 / (N : ℝ) ^ 2) := by
    intro ρ hρ
    have hρ' := (RHTower.lowZeros_finite _).mem_toFinset.mp hρ
    have hnorm := norm_le_of_mem_lowZeros hρ'
    have hNL' : 2 * (L : ℝ) * (‖ρ‖ + 3) ≤ N := by
      have h1 : 2 * (L : ℝ) * (‖ρ‖ + 3) ≤ 2 * L * ((1 + T N) + 3) := by gcongr
      nlinarith
    have hcN' : c N * (‖ρ‖ + 1) ≤ N := by
      have h1 : c N * (‖ρ‖ + 1) ≤ c N * ((1 + T N) + 1) := by gcongr
      nlinarith
    have h := norm_log_div_mul_bulkLedger_le hφ hφsupp hφ2 hE hL hpole hρ'.1 hc0 hN2 hNL' hcN'
    refine h.trans ?_
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    have h67 : (6 + ‖ρ‖) ^ 2 ≤ (7 + T N) ^ 2 := by
      have : 0 ≤ 6 + ‖ρ‖ := by positivity
      exact pow_le_pow_left₀ this (by linarith) 2
    calc (zetaZeroConfig.mult ρ : ℝ) * ((∫ u, |φ u|) * Real.exp 1) ^ 2 / (∫ u, φ u ^ 2) *
          packetConst E y ^ 2 * (6 + ‖ρ‖) ^ 2 / (N : ℝ) ^ 2 =
        zetaZeroConfig.mult ρ * (A₀ * (6 + ‖ρ‖) ^ 2 / (N : ℝ) ^ 2) := by rw [hA₀]; ring
      _ ≤ zetaZeroConfig.mult ρ * (A₀ * (7 + T N) ^ 2 / (N : ℝ) ^ 2) := by gcongr
  have hl0 : 0 ≤ T N * Real.log (T N) ^ 2 := by positivity
  calc ∑ ρ ∈ (RHTower.lowZeros_finite (T N)).toFinset,
        ‖((Real.log N / c N : ℝ) : ℂ) * bulkLedger zetaZeroConfig φ E y (c N) N ρ‖ ≤
        ∑ ρ ∈ (RHTower.lowZeros_finite (T N)).toFinset,
          (zetaZeroConfig.mult ρ : ℝ) * (A₀ * (7 + T N) ^ 2 / (N : ℝ) ^ 2) := sum_le_sum hper
    _ = (∑ ρ ∈ (RHTower.lowZeros_finite (T N)).toFinset, (zetaZeroConfig.mult ρ : ℝ)) *
          (A₀ * (7 + T N) ^ 2 / (N : ℝ) ^ 2) := by rw [sum_mul]
    _ ≤ (K * (T N * Real.log (T N) ^ 2)) * (A₀ * (7 + T N) ^ 2 / (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right (hcount _ hTN) (by positivity)
    _ ≤ (K * (T N * Real.log (T N) ^ 2)) * (A₀ * (64 * T N ^ 2) / (N : ℝ) ^ 2) := by
        gcongr
        nlinarith
    _ = A₀ * 64 * K * (T N ^ 3 * Real.log (T N) ^ 2 / (N : ℝ) ^ 2) := by ring

/-- **Every power height below `N^{2/3}` is invisible.** For `0 < θ < 2/3` and every overlap
schedule with `c_N ≥ 1`, `c_N/N^{1−θ} → 0` (e.g. the critical curve), the zeros of height
`≤ N^θ` together contribute `o(c_N/log N)` to the normalized complete form of every pole-free
conductor packet. -/
theorem tendsto_sum_bulkLedger_lowZeros_rpow {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {E : Finset ℕ}
    (hE : ∀ e ∈ E, 1 ≤ e) {y : ℕ → ℝ} (hpole : poleCoefficient E y = 0) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ : θ < 2 / 3) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    (hcN : Tendsto (fun N : ℕ => c N / (N : ℝ) ^ (1 - θ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑ ρ ∈ (RHTower.lowZeros_finite ((N : ℝ) ^ θ)).toFinset,
      ‖((Real.log N / c N : ℝ) : ℂ) * bulkLedger zetaZeroConfig φ E y (c N) N ρ‖) atTop (𝓝 0) := by
  have hNat := tendsto_natCast_atTop_atTop (R := ℝ)
  have hT : Tendsto (fun N : ℕ => (N : ℝ) ^ θ) atTop atTop := (tendsto_rpow_atTop hθ0).comp hNat
  have hcT : Tendsto (fun N : ℕ => c N * (N : ℝ) ^ θ / N) atTop (𝓝 0) := by
    refine hcN.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Real.rpow_sub hN0, Real.rpow_one]
    field_simp
  set a := (2 - 3 * θ) / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have hlo : Tendsto (fun N : ℕ => Real.log N / (N : ℝ) ^ a) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_atTop ha0).tendsto_div_nhds_zero).comp hNat
  have hT3 : Tendsto (fun N : ℕ => ((N : ℝ) ^ θ) ^ 3 * Real.log ((N : ℝ) ^ θ) ^ 2 / (N : ℝ) ^ 2)
      atTop (𝓝 0) := by
    have h := (hlo.pow 2).const_mul (θ ^ 2)
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num, mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have h3 : ((N : ℝ) ^ θ) ^ 3 = (N : ℝ) ^ (3 * θ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
    have h2 : ((N : ℝ) ^ a) ^ 2 = (N : ℝ) ^ (2 * a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
    have hsum : (N : ℝ) ^ (3 * θ) * (N : ℝ) ^ (2 * a) = (N : ℝ) ^ 2 := by
      rw [← Real.rpow_add hN0, show 3 * θ + 2 * a = ((2 : ℕ) : ℝ) by rw [ha]; push_cast; ring,
        Real.rpow_natCast]
    have hpa : 0 < (N : ℝ) ^ (2 * a) := Real.rpow_pos_of_pos hN0 _
    rw [Real.log_rpow hN0, h3, div_pow, h2, ← hsum]
    field_simp
  exact tendsto_sum_bulkLedger_lowZeros hφ hφsupp hφ2 hE hpole hc1 hT hcT hT3

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
