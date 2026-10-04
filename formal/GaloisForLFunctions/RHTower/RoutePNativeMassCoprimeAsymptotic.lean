import GaloisForLFunctions.RHTower.RoutePNativeMassDilation
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Positive exponential source created by native mass compensation

The complete coprime form is a Möbius transform of the full dilation
square. An admitted inverse-square majorant passes every original label
through the limit. No endpoint, common divisor, or cross pair is removed.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

def routePNativeMassCoprimeSource (lam t : ℝ) : ℝ :=
  Real.exp (-t) * logarithmicCoprimeEnergy (routePNativeMassCoprimeProfile lam) t

def routePNativeMassCoprimePole (lam : ℝ) : ℝ :=
  (lam * (divisorHarmonicBoundary / 3)) ^ 2 * (6 / Real.pi ^ 2)

private theorem moebius_inverse_square :
    (∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2) =
      6 / Real.pi ^ 2 := by
  have hs : 1 < (2 : ℂ).re := by norm_num
  have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs, riemannZeta_two] at h
  have hm : LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) 2 =
      ∑' n : ℕ, (((ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
    unfold LSeries
    apply tsum_congr
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn, Complex.cpow_ofNat]
      push_cast
      rfl
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum, ← hm]
  have hc := eq_inv_of_mul_eq_one_right h
  rw [hc]
  simp only [inv_div, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat]

private def pairTerm (lam T : ℝ) (n : ℕ) : ℝ :=
  if n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊ then
    (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 *
      (Real.exp (-(T - Real.log n)) * routePNativeMassDilation lam (T - Real.log n)) ^ 2
  else 0

private theorem normalized_energy_eq_tsum (lam T : ℝ) :
    Real.exp (-2 * T) * logarithmicCoprimeEnergy (routePNativeMassCoprimeProfile lam) T =
      ∑' n : ℕ, pairTerm lam T n := by
  rw [logarithmicCoprimeEnergy_eq_mobius_square_dilation]
  change Real.exp (-2 * T) *
    (∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, (ArithmeticFunction.moebius n : ℝ) *
      routePNativeMassDilation lam (T - Real.log n) ^ 2) = _
  rw [Finset.mul_sum, tsum_eq_sum (s := Finset.Icc 1 ⌊Real.exp T⌋₊)
    (fun n hn => by simp [pairTerm, hn])]
  apply Finset.sum_congr rfl
  intro n hn
  rw [pairTerm, if_pos hn]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have he : Real.exp (-(T - Real.log n)) = (n : ℝ) * Real.exp (-T) := by
    rw [show -(T - Real.log n) = Real.log n + -T by ring, Real.exp_add,
      Real.exp_log hnpos]
  have he2 : Real.exp (-2 * T) = Real.exp (-T) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [he, he2]
  field_simp [hnpos.ne']

private theorem pair_bound (lam : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ T : ℝ, |Real.exp (-T) * routePNativeMassDilation lam T| ≤ C)
    (T : ℝ) (n : ℕ) : ‖pairTerm lam T n‖ ≤ C ^ 2 * ((n : ℝ) ^ 2)⁻¹ := by
  unfold pairTerm
  split_ifs with hn
  · have hm : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
    have hN := hb (T - Real.log n)
    have hs : (Real.exp (-(T - Real.log n)) *
        routePNativeMassDilation lam (T - Real.log n)) ^ 2 ≤ C ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (Real.exp (-(T - Real.log n)) *
          routePNativeMassDilation lam (T - Real.log n))) hC).mpr hN
    rw [Real.norm_eq_abs, abs_mul, abs_div]
    simp only [abs_pow, sq_abs]
    calc
      _ ≤ (1 / (n : ℝ) ^ 2) * C ^ 2 :=
        mul_le_mul (div_le_div_of_nonneg_right hm (sq_nonneg _)) hs
          (sq_nonneg _) (by positivity)
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

private theorem pair_limit (lam : ℝ) (n : ℕ) :
    Tendsto (fun T : ℝ => pairTerm lam T n) atTop
      (𝓝 ((ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 *
        (lam * (divisorHarmonicBoundary / 3)) ^ 2)) := by
  by_cases hn : n = 0
  · subst n
    simp [pairTerm]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hs : Tendsto (fun T : ℝ => T - Real.log n) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b + Real.log n)] with T hT
    linarith
  have h := ((routePNativeMassDilation_asymptotic lam).comp hs).pow 2
  apply (h.const_mul ((ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2)).congr'
  filter_upwards [eventually_ge_atTop (Real.log n)] with T hT
  have hmem : n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊ :=
    Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn,
      (Nat.le_floor_iff (Real.exp_pos T).le).mpr ((Real.log_le_iff_le_exp hnpos).mp hT)⟩
  simp only [pairTerm, hmem, if_true, Function.comp_def]

/-- Exact leading coefficient of the complete compensated native coprime
source. The inverse-square passage retains every finite-cutoff pair. -/
theorem routePNativeMassCoprimeSource_asymptotic (lam : ℝ) :
    Tendsto (fun T : ℝ => Real.exp (-T) * routePNativeMassCoprimeSource lam T)
      atTop (𝓝 (routePNativeMassCoprimePole lam)) := by
  obtain ⟨C, hC, hb⟩ := routePNativeMassDilation_normalized_bound lam
  have hi : Summable (fun n : ℕ => C ^ 2 * ((n : ℝ) ^ 2)⁻¹) :=
    (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ))).mul_left _
  have h := tendsto_tsum_of_dominated_convergence hi (pair_limit lam)
    (Eventually.of_forall (fun T => pair_bound lam hC hb T))
  have hlim : Tendsto
      (fun T : ℝ => Real.exp (-2 * T) *
        logarithmicCoprimeEnergy (routePNativeMassCoprimeProfile lam) T)
      atTop (𝓝 (routePNativeMassCoprimePole lam)) := by
    simp only [tsum_mul_right, moebius_inverse_square] at h
    apply (show Tendsto (fun T : ℝ => ∑' n : ℕ, pairTerm lam T n) atTop
      (𝓝 (routePNativeMassCoprimePole lam)) from by
        simpa only [routePNativeMassCoprimePole, mul_comm] using h).congr
    intro T
    exact (normalized_energy_eq_tsum lam T).symm
  apply hlim.congr
  intro T
  unfold routePNativeMassCoprimeSource
  rw [← mul_assoc, ← Real.exp_add]
  rw [show -T + -T = -2 * T by ring]

theorem routePNativeMassCoprimePole_pos {lam : ℝ} (hlam : lam ≠ 0) :
    0 < routePNativeMassCoprimePole lam := by
  have hd : 0 < divisorHarmonicBoundary / 3 := div_pos divisorHarmonicBoundary_pos (by norm_num)
  unfold routePNativeMassCoprimePole
  exact mul_pos (sq_pos_of_ne_zero (mul_ne_zero hlam hd.ne')) (by positivity)

end RHTower
