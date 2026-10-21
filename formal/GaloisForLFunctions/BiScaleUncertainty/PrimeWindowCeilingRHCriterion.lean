import GaloisForLFunctions.BiScaleUncertainty.PrimeWindowCeilingPolarAsymptotics
import GaloisForLFunctions.RHTower.ChebyshevDeficitPrimitiveOneSidedRH
import GaloisForLFunctions.RHTower.WeilParityPoleDeletionAdditionLaws

/-!
# A sharp window ceiling forces the Riemann hypothesis

On windows of length `L` the prime side `(A − W)/‖c‖²` reaches `e^{L/2}(1 + o(1))`
(`tendsto_windowCeiling_div_exp`): the ceiling is the polar ceiling. Its excess over `e^{L/2}` is
carried by the Chebyshev deficit near `X = e^L`.

**Theorem** (`riemannHypothesis_of_windowDeviations_le`). If for some `B` and all large `L` every
window deviation is at most `e^{L/2} + B(1 + L)`, then RH holds. Equivalently
(`riemannHypothesis_of_windowCeiling_le`): `c(L) ≤ e^{L/2} + O(L)` implies RH. The prime side must
match the pole to absolute precision `O(log X)` at the scale `√X`.

**Mechanism.** The polar test `(e^{−t/2} + e^{−(L−t)/2}) χ_δ` with cutoff width `δ = e^{−L/2}` has
mass `≤ 2 + 2L e^{−L/2}` and prime side
`≥ 2e^{−L/2} Σ_{n≤Y} Λ(n) log(Y/n) = 2e^{−L/2} (Y − 1 − D(log Y))`, `Y = e^{L−2δ}`, where
`D(T) = ∫_0^T (e^t − ψ(e^t)) dt` is the integrated Chebyshev deficit
(`RHTower.sum_vonMangoldt_mul_logGap_eq_integral`). The ceiling bound then gives
`D(L) ≥ −C(1 + L) e^{L/2}`, and a one-sided bound of this size forces RH by Landau's theorem
(`RHTower.riemannHypothesis_of_logChebyshevDeficitPrimitive_ge_mul`).
-/

open MeasureTheory Set Complex Finsupp Filter Topology
open Zeta23
open RHTower RHTower.WeilOneSided
open scoped ComplexConjugate Real

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-- The Riesz mean is the integrated Chebyshev function: `Σ_{n≤e^T} Λ(n) log(e^T/n) =
e^T − 1 − D(T)`. -/
theorem riesz_eq_deficit {T : ℝ} (hT : 0 ≤ T) :
    ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) *
        Real.log (Real.exp T / n) =
      Real.exp T - 1 - ccmLogChebyshevDeficitPrimitive T := by
  have h1 : ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) *
      Real.log (Real.exp T / n) =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp T⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) * (T - Real.log n) := by
    rw [← Finset.sum_subset (s₁ := Finset.Icc 2 ⌊Real.exp T⌋₊) (fun n hn => by
      rw [Finset.mem_Icc] at hn ⊢; omega) fun n hn hn2 => by
        have : n = 1 := by rw [Finset.mem_Icc] at hn hn2; omega
        subst this; simp]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by rw [Finset.mem_Icc] at hn; omega : 0 < n)
    rw [Real.log_div (Real.exp_pos _).ne' hn0.ne', Real.log_exp]
  have h2 : ∫ t in (0 : ℝ)..T, Chebyshev.psi (Real.exp t) =
      Real.exp T - 1 - ccmLogChebyshevDeficitPrimitive T := by
    have hpsi : IntervalIntegrable (fun t => Chebyshev.psi (Real.exp t)) volume 0 T :=
      (Chebyshev.psi_mono.comp Real.exp_monotone).intervalIntegrable
    rw [deficitPrimitive_eq, show (fun t => chebyshevLogDeficit t) =
        fun t => Real.exp t - Chebyshev.psi (Real.exp t) from rfl,
      intervalIntegral.integral_sub (Real.continuous_exp.intervalIntegrable 0 T) hpsi,
      integral_exp, Real.exp_zero]
    ring
  rw [h1, sum_vonMangoldt_mul_logGap_eq_integral hT, h2]

/-- The deficit changes by at most `(log 4 + 5) e^L (L − T)` between `T ≤ L`. -/
theorem deficit_sub_le {T L : ℝ} (hTL : T ≤ L) :
    |ccmLogChebyshevDeficitPrimitive L - ccmLogChebyshevDeficitPrimitive T| ≤
      chebyshevDeficitConst * Real.exp L * (L - T) := by
  rw [deficitPrimitive_eq, deficitPrimitive_eq,
    intervalIntegral.integral_interval_sub_left (intervalIntegrable_chebyshevLogDeficit 0 L)
      (intervalIntegrable_chebyshevLogDeficit 0 T)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := T) (b := L)
    (f := chebyshevLogDeficit) (C := chebyshevDeficitConst * Real.exp L) fun t ht => by
      rw [Set.uIoc_of_le hTL] at ht
      rw [Real.norm_eq_abs]
      exact (abs_chebyshevLogDeficit_le t).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr ht.2) chebyshevDeficitConst_pos.le)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hTL)] at h
  exact h

/-- The polar test has positive mass. -/
theorem massOf_polarTest_pos {L δ : ℝ} (hδ : 0 < δ) (hLδ : 2 * δ < L) :
    0 < massOf (Finsupp.single (polarTestFn hδ hLδ) 1) := by
  rw [WeilOneSided.massOf, Finsupp.sum_single_index (by simp), one_mul]
  change 0 < ∫ u, ‖(polarTestReal hδ hLδ u : ℂ)‖ ^ 2
  simp_rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hint : Integrable fun u => polarTestReal hδ hLδ u ^ 2 :=
    ((contDiff_polarTestReal hδ hLδ).continuous.pow 2).integrable_of_hasCompactSupport
      (hasCompactSupport_polarTestReal_sq hδ hLδ)
  rw [integral_pos_iff_support_of_nonneg (fun u => sq_nonneg _) hint]
  refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo δ (L - δ)) fun u hu => ?_)
  · rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (by linarith)
  · have h := polarTestReal_eq hδ hLδ (Ioo_subset_Icc_self hu)
    change polarTestReal hδ hLδ u ^ 2 ≠ 0
    rw [h]
    exact pow_ne_zero _ (polarProfile_pos L u).ne'

/-- **The window ceiling criterion.** If every window deviation is eventually at most
`e^{L/2} + B(1 + L)`, then the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_windowDeviations_le {B : ℝ}
    (h : ∀ᶠ L in atTop, ∀ x ∈ windowDeviations L, x ≤ Real.exp (L / 2) + B * (1 + L)) :
    RiemannHypothesis := by
  classical
  obtain ⟨L₁, hL₁⟩ := h.exists_forall_of_atTop
  set C := chebyshevDeficitConst
  have hC := chebyshevDeficitConst_pos
  set K₀ := 4 * |B| + 8 + 2 * C with hK₀
  set L₀ := max L₁ 4
  -- the deficit is bounded below by `−K₀ (1 + L) e^{L/2}` for large `L`
  have hlarge : ∀ L : ℝ, L₀ ≤ L →
      -(K₀ * (1 + L) * Real.exp (L / 2)) ≤ ccmLogChebyshevDeficitPrimitive L := by
    intro L hL
    have hL4 : 4 ≤ L := (le_max_right _ _).trans hL
    have hL1 : L₁ ≤ L := (le_max_left _ _).trans hL
    set E := Real.exp (L / 2) with hEdef
    have hEL : 0 < E := Real.exp_pos _
    set δ := Real.exp (-(L / 2)) with hδdef
    have hδ : 0 < δ := Real.exp_pos _
    have hδ1 : δ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hLδ : 2 * δ < L := by linarith
    have hEδ : δ * E = 1 := by
      rw [hδdef, hEdef, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hδneg : Real.exp (-L / 2) = δ := by rw [hδdef]; congr 1; ring
    -- `L e^{−L/2} ≤ 1` on `L ≥ 4`
    have hLδ1 : L * δ ≤ 1 := by
      have h1 : 1 + L / 2 + (L / 2) ^ 2 / 2 ≤ E := Real.quadratic_le_exp_of_nonneg (by linarith)
      have : L ≤ E := by nlinarith
      calc L * δ ≤ E * δ := mul_le_mul_of_nonneg_right this hδ.le
        _ = 1 := by rw [mul_comm]; exact hEδ
    set T := L - 2 * δ with hTdef
    have hT : 0 ≤ T := by linarith
    set f := polarTestFn hδ hLδ
    set c : WeilTestFn →₀ ℝ := Finsupp.single f 1
    have hc : ∀ g, 0 ≤ c g := fun g => by
      simp only [c]; rw [Finsupp.single_apply]; split_ifs <;> norm_num
    have hsupp : ∀ g ∈ c.support, ∃ a, ∀ u, g.1 u ≠ 0 → u ∈ Ioo a (a + L) := fun g hg => by
      have : g = f := by
        by_contra hne; exact (Finsupp.mem_support_iff.mp hg) (by simp [c, Ne.symm hne])
      exact ⟨0, this ▸ polarTestFn_supp hδ hLδ⟩
    have hm := massOf_polarTest_pos hδ hLδ
    have hM := massOf_polarTest_le hδ hLδ
    rw [hδneg] at hM
    have hdev : nodeArchEnergy c - weilEnergy c =
        linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
          (logVector f) := by
      rw [nodeArchEnergy_eq_weilEnergy_add, add_sub_cancel_left, nodeVector_single_test]
    have hP := primeSide_polarTest_ge hδ hLδ
    rw [riesz_eq_deficit hT, hδneg, ← hdev] at hP
    -- the hypothesis applied to the polar test
    have hx := hL₁ L hL1 _ ⟨c, hc, hsupp, hm, rfl⟩
    rw [div_le_iff₀ hm] at hx
    have hB1 : B * (1 + L) ≤ |B| * (1 + L) :=
      mul_le_mul_of_nonneg_right (le_abs_self B) (by linarith)
    have hpos : 0 ≤ E + |B| * (1 + L) := by positivity
    have hx' : nodeArchEnergy c - weilEnergy c ≤ (E + |B| * (1 + L)) * (2 + 2 * L * δ) :=
      hx.trans ((mul_le_mul_of_nonneg_right (by linarith) hm.le).trans
        (mul_le_mul_of_nonneg_left hM hpos))
    -- `2 e^{−L/2} e^T ≥ 2E − 4`
    have heT : 2 * E - 4 ≤ 2 * δ * Real.exp T := by
      have h1 : Real.exp T = E * E * Real.exp (-(2 * δ)) := by
        rw [hTdef, hEdef, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      have h2 : 1 - 2 * δ ≤ Real.exp (-(2 * δ)) := Real.one_sub_le_exp_neg _
      rw [h1]
      have : 2 * δ * (E * E * Real.exp (-(2 * δ))) = 2 * E * Real.exp (-(2 * δ)) := by
        rw [show 2 * δ * (E * E * Real.exp (-(2 * δ))) = 2 * (δ * E) * E * Real.exp (-(2 * δ)) by ring,
          hEδ]; ring
      rw [this]
      nlinarith
    -- combine: `−2δ D(T) ≤ (4|B| + 8)(1 + L)`
    have hD : -(2 * δ) * ccmLogChebyshevDeficitPrimitive T ≤ (4 * |B| + 8) * (1 + L) := by
      have hexp : (E + |B| * (1 + L)) * (2 + 2 * L * δ) =
          2 * E + 2 * L * (δ * E) + 2 * |B| * (1 + L) + 2 * |B| * (1 + L) * (L * δ) := by ring
      rw [hexp, hEδ] at hx'
      have hBLδ : 2 * |B| * (1 + L) * (L * δ) ≤ 2 * |B| * (1 + L) :=
        mul_le_of_le_one_right (by positivity) hLδ1
      nlinarith
    have hDT : -((2 * |B| + 4) * (1 + L) * E) ≤ ccmLogChebyshevDeficitPrimitive T := by
      have := mul_le_mul_of_nonneg_left hD (by positivity : (0 : ℝ) ≤ E / 2)
      have e1 : E / 2 * (-(2 * δ) * ccmLogChebyshevDeficitPrimitive T) =
          -(δ * E) * ccmLogChebyshevDeficitPrimitive T := by ring
      rw [e1, hEδ] at this
      nlinarith
    -- from `T` to `L`
    have hshift := deficit_sub_le (show T ≤ L by linarith)
    have hshift' : C * Real.exp L * (L - T) = 2 * C * E := by
      rw [hTdef, show L - (L - 2 * δ) = 2 * δ by ring]
      have : Real.exp L = E * E := by rw [hEdef, ← Real.exp_add]; congr 1; ring
      rw [this, show C * (E * E) * (2 * δ) = 2 * C * E * (δ * E) by ring, hEδ, mul_one]
    rw [hshift'] at hshift
    have habs := neg_abs_le (ccmLogChebyshevDeficitPrimitive L - ccmLogChebyshevDeficitPrimitive T)
    have hE1 : E ≤ (1 + L) * E := le_mul_of_one_le_left hEL.le (by linarith)
    have h1 : C * E ≤ C * ((1 + L) * E) := mul_le_mul_of_nonneg_left hE1 hC.le
    have h2 : 0 ≤ |B| * ((1 + L) * E) := by positivity
    have h3 : 0 ≤ (1 + L) * E := by positivity
    rw [hK₀]
    linarith
  -- the small range
  set B₁ := max K₀ (C * Real.exp L₀)
  refine riemannHypothesis_of_logChebyshevDeficitPrimitive_ge_mul (B := B₁) fun T hT => ?_
  by_cases hTL : L₀ ≤ T
  · have := hlarge T hTL
    have hK : K₀ ≤ B₁ := le_max_left _ _
    have : K₀ * (1 + T) * Real.exp (T / 2) ≤ B₁ * (1 + T) * Real.exp (T / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK (by linarith))
        (Real.exp_pos _).le
    linarith
  · push Not at hTL
    have hab := abs_deficitPrimitive_le hT
    have h1 : C * Real.exp T ≤ C * Real.exp L₀ :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hTL.le) hC.le
    have h2 : C * Real.exp L₀ ≤ B₁ := le_max_right _ _
    have h3 : 1 ≤ (1 + T) * Real.exp (T / 2) := by
      have := Real.one_le_exp (by linarith : 0 ≤ T / 2)
      nlinarith
    have hB₁ : 0 ≤ B₁ := (by positivity : (0 : ℝ) ≤ C * Real.exp L₀).trans h2
    have : B₁ ≤ B₁ * (1 + T) * Real.exp (T / 2) := by
      rw [mul_assoc]; exact le_mul_of_one_le_right hB₁ h3
    linarith [neg_abs_le (ccmLogChebyshevDeficitPrimitive T)]

/-- **The criterion in terms of the ceiling.** `c(L) ≤ e^{L/2} + O(L)` implies RH. -/
theorem riemannHypothesis_of_windowCeiling_le {B : ℝ}
    (h : ∀ᶠ L in atTop, windowCeiling L ≤ Real.exp (L / 2) + B * (1 + L)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_windowDeviations_le (B := B) ?_
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with L hL hL0 x hx
  have hbdd : BddAbove (windowDeviations L) :=
    ⟨(Real.log 4 + 4) * Real.exp (L / 2) + (1 + L) ^ 2, fun y ⟨c, hc, hs, hm, hy⟩ => by
      rw [hy, div_le_iff₀ hm]
      exact (le_abs_self _).trans (abs_nodeArchEnergy_sub_weilEnergy_le_chebyshev hc hL0 hs)⟩
  exact (le_csSup hbdd hx).trans hL

end

end GaloisForLFunctions.BiScaleUncertainty
