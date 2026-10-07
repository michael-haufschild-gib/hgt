import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorPoissonAnalytic
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorPoissonQuarter
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorAxisPolynomial
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorMaassDefect

/-!
# The original cubic datum's finite packet throughout the upper half-plane

Every regularity premise of axis uniqueness is paid for the actual Poisson
modes. Inverting the exact polynomial axis operator preserves nonzero residues.
-/

noncomputable section

open Complex Set Filter Polynomial
open scoped ContDiff
open GaloisForLFunctions.HTGeometry

namespace RHTower.WeilHigherDenominator

open MaassAxisContinuation MaassBesselSeries

private lemma quarter_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ)
    (hF : ∀ i ∈ s, ContDiffOn ℝ ∞ (F i) upper)
    (hQ : ∀ i ∈ s, ∀ z ∈ upper, quarterDefect (F i) z = 0)
    {z : ℂ} (hz : z ∈ upper) : quarterDefect (fun w => ∑ i ∈ s, F i w) z = 0 := by
  classical
  revert hF hQ
  induction s using Finset.induction_on with
  | empty =>
    intro _ _
    simpa only [Finset.sum_empty, zero_mul] using
      (quarterDefect_const_mul (F := fun _ => 0) contDiffOn_const (0 : ℂ) hz)
  | @insert i s hi ih =>
    intro hF hQ
    have hs : ∀ j ∈ s, ContDiffOn ℝ ∞ (F j) upper :=
      fun j hj => hF j (Finset.mem_insert_of_mem hj)
    simp only [Finset.sum_insert hi]
    rw [quarterDefect_add (hF i (Finset.mem_insert_self i s)) (ContDiffOn.sum hs) hz,
      hQ i (Finset.mem_insert_self i s) z hz, ih hs
        (fun j hj => hQ j (Finset.mem_insert_of_mem hj)), zero_add]

/-- Exact axis matching determines the actual finite Poisson defect everywhere. -/
theorem maass_defect_eq_poisson_packet {g : ℕ → ℂ} (hg : PolyGrowth g)
    (a b ε : ℂ) (Z : Finset ℂ) (R : ℂ → Polynomial ℂ)
    (hstrip : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1)
    (haxis : ∀ y : ℝ, 0 < y →
      maassFun g a b ((y : ℂ) * I) - ε * maassFun g a b (((y⁻¹ : ℝ) : ℂ) * I) =
        ∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) ((y : ℂ) * I))
    {z : ℂ} (hz : z ∈ upper) :
    maassFun g a b z - ε * maassFun g a b (invS z) =
      ∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) z := by
  let U : ℂ → ℂ := maassFun g a b
  let B : ℂ → ℂ := fun w => ∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) w
  let V : ℂ → ℂ := fun w => U w + (-ε) * U (invS w) + (-1 : ℂ) * B w
  have hU : ContDiffOn ℝ ∞ U upper := contDiffOn_maassFun hg a b
  have hUi : ContDiffOn ℝ ∞ (fun w => U (invS w)) upper := contDiffOn_comp_invS hU
  have hB : ContDiffOn ℝ ∞ B upper := ContDiffOn.sum fun ρ hρ =>
    contDiffOn_polynomialPolarMode (hstrip ρ hρ).1 (hstrip ρ hρ).2 (R ρ)
  have hUs : ContDiffOn ℝ ∞ (fun w => (-ε) * U (invS w)) upper := contDiffOn_const.mul hUi
  have hBs : ContDiffOn ℝ ∞ (fun w => (-1 : ℂ) * B w) upper := contDiffOn_const.mul hB
  have hV : ContDiffOn ℝ ∞ V upper := (hU.add hUs).add hBs
  have hQ : ∀ w ∈ upper, quarterDefect V w = 0 := by
    intro w hw
    have hQu : quarterDefect U w = 0 := quarterDefect_maassFun hg a b hw
    have hQi : quarterDefect (fun v => U (invS v)) w = 0 :=
      quarterDefect_comp_invS hU (fun v hv => quarterDefect_maassFun hg a b hv) hw
    have hQB : quarterDefect B w = 0 := quarter_sum Z (fun ρ => polynomialPolarMode ρ (R ρ))
      (fun ρ hρ => contDiffOn_polynomialPolarMode (hstrip ρ hρ).1 (hstrip ρ hρ).2 (R ρ))
      (fun ρ hρ v hv => quarterDefect_polynomialPolarMode (hstrip ρ hρ).1 (hstrip ρ hρ).2 (R ρ) hv) hw
    dsimp only [V]
    rw [quarterDefect_add (hU.add hUs) hBs hw, quarterDefect_add hU hUs hw,
      quarterDefect_const_mul hUi (-ε) hw, quarterDefect_const_mul hB (-1) hw,
      hQu, hQi, hQB]
    ring
  have heven : ∀ w ∈ upper, V (-(starRingEnd ℂ) w) = V w := by
    intro w _
    simp only [V, U, B, maassFun_neg_conj, invS_neg_conj, polynomialPolarMode_reflect]
  have hax : ∀ y : ℝ, 0 < y → V ((y : ℂ) * I) = 0 := by
    intro y hy
    have hh := haxis y hy
    dsimp only [V, U, B]
    rw [invS_I_mul, one_div]
    linear_combination hh
  have hana : ∀ y : ℝ, 0 < y →
      AnalyticOnNhd ℝ (fun x : ℝ => V ((x : ℂ) + (y : ℂ) * I)) univ := by
    intro y hy
    have hBa : AnalyticOnNhd ℝ (fun x : ℝ => B ((x : ℂ) + (y : ℂ) * I)) univ :=
      Finset.analyticOnNhd_fun_sum Z fun ρ hρ =>
        analyticOnNhd_polynomialPolarMode_line (hstrip ρ hρ).1 (hstrip ρ hρ).2 (R ρ) hy
    intro x hx
    exact ((analyticOnNhd_maassFun_line hg a b hy x hx).add
      (analyticAt_const.mul (analyticOnNhd_maassFun_inv_line hg a b hy x hx))).add
        (analyticAt_const.mul (hBa x hx))
  have hzero := eq_zero_of_axis hV hQ heven hax hana z hz
  dsimp only [V, U, B] at hzero
  linear_combination hzero

/-- All regularity, growth and mode-realization obligations are derived from the original datum. -/
theorem degreeThree_infiniteDeficits_or_spatialDefect {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (hE1 : E 1 ≠ 0) :
    (xiDeficitSupport E).Infinite ∨
      ∃ (P : Polynomial ℂ) (H : ℂ → ℂ) (ε : ℂ) (R : ℂ → Polynomial ℂ),
        P.Monic ∧ ‖ε‖ = 1 ∧ (∀ s, E (1 - s) = ε * E s) ∧
        (∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞)) ∧
        Differentiable ℂ H ∧ FiniteOrderEnvelope H ∧ H 1 ≠ 0 ∧
        (∀ z, P.eval z * E z = H z * xi z) ∧
        (∀ ρ ∈ P.roots.toFinset, 0 < ρ.re ∧ ρ.re < 1 ∧ R ρ ≠ 0) ∧
        ∀ z : ℂ, 0 < z.im →
          maassFun (degreeTwoQuotientCoeff g) (ε * degreeTwoEndpointNumerator E 1)
              (ε * deriv (degreeTwoEndpointNumerator E) 1) z -
            ε * maassFun (degreeTwoQuotientCoeff g) (ε * degreeTwoEndpointNumerator E 1)
              (ε * deriv (degreeTwoEndpointNumerator E) 1) (invS z) =
            ∑ ρ ∈ P.roots.toFinset, polynomialPolarMode ρ (R ρ) z := by
  classical
  rcases degreeThree_infiniteDeficits_or_maassDefect hD hE1 with hi |
    ⟨P, H, ε, Q, hm, hε, he, ho, hd, hg, h₁, hf, hs, haxis⟩
  · exact Or.inl hi
  · let R : ℂ → Polynomial ℂ := fun ρ => if hρ : ρ ∈ P.roots.toFinset then
      (polarAxisEquiv (hs ρ hρ).1 (hs ρ hρ).2.1).symm (Q ρ) else 0
    have hR (ρ : ℂ) (hρ : ρ ∈ P.roots.toFinset) :
        polarAxisEquiv (hs ρ hρ).1 (hs ρ hρ).2.1 (R ρ) = Q ρ := by
      simp only [R, dif_pos hρ, LinearEquiv.apply_symm_apply]
    refine Or.inr ⟨P, H, ε, R, hm, hε, he, ho, hd, hg, h₁, hf, ?_, ?_⟩
    · intro ρ hρ
      refine ⟨(hs ρ hρ).1, (hs ρ hρ).2.1, ?_⟩
      intro hzero
      have hh := hR ρ hρ
      rw [hzero, map_zero] at hh
      exact (hs ρ hρ).2.2 hh.symm
    · intro z hz
      apply maass_defect_eq_poisson_packet
        (MaassConverseLevelOne.polyGrowth_of_summable (fun _ hσ => degreeTwoQuotientCoeff_weighted_summable hD hσ))
        _ _ ε P.roots.toFinset R (fun ρ hρ => ⟨(hs ρ hρ).1, (hs ρ hρ).2.1⟩) ?_ hz
      intro y hy
      rw [haxis y hy]
      apply Finset.sum_congr rfl
      intro ρ hρ
      rw [polynomialPolarMode_axis (hs ρ hρ).1 (hs ρ hρ).2.1 _ hy, hR ρ hρ]

end RHTower.WeilHigherDenominator
