import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorSpectralSubtraction
import GaloisForLFunctions.RHTower.WeilConditionalConstantSignRigidity
import GaloisForLFunctions.RHTower.WeilZetaPowerForward
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence

/-!
# Multiplicity deficits of nontrivial degree-three data

The zeta measure has integer counting. Spectral domination by three times a third-counting
measure therefore falls under spectral subtraction. The atom formula translates this condition
to containment of the complete zeta divisor, retaining arbitrary zero multiplicities.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
open Zeta23
open GaloisForLFunctions.EntireZeroDivisor

noncomputable section

namespace RHTower.WeilHigherDenominator

open WeilSpectral WeilConditional WeilZetaPower

/-- Atomwise domination controls an entire measure carried by a countable set. -/
theorem measure_le_of_countable_atoms {μ ν : Measure ℝ} {Z : Set ℝ}
    (hZ : Z.Countable) (hnull : μ Zᶜ = 0) (h : ∀ x ∈ Z, μ {x} ≤ ν {x}) : μ ≤ ν := by
  apply Measure.le_iff.mpr
  intro A hA
  have hcount : (A ∩ Z).Countable := hZ.mono inter_subset_right
  have hsum (η : Measure ℝ) : (∑' x : ↑(A ∩ Z), η {(x : ℝ)}) = η (A ∩ Z) := by
    simpa using (tsum_measure_preimage_singleton (μ := η) (f := id) hcount
      (fun x _ => measurableSet_singleton x))
  calc
    μ A = μ (A ∩ Z) := (measure_inter_conull hnull).symm
    _ = ∑' x : ↑(A ∩ Z), μ {(x : ℝ)} := (hsum μ).symm
    _ ≤ ∑' x : ↑(A ∩ Z), ν {(x : ℝ)} := ENNReal.tsum_le_tsum (fun x => h x x.2.2)
    _ = ν (A ∩ Z) := hsum ν
    _ ≤ ν A := measure_mono inter_subset_left

/-- The canonical zeta atoms retain their natural multiplicities in extended nonnegative reals. -/
theorem boundaryMeasure_vonMangoldt_singleton_nat
    (hΛ : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (t : ℝ) :
    boundaryMeasure hΛ {t} = (analyticOrderNatAt xi ((1 / 2 : ℂ) + t * I) : ℝ≥0∞) := by
  rw [← ENNReal.ofReal_toReal (boundaryMeasure_singleton_ne_top hΛ t)]
  change ENNReal.ofReal ((boundaryMeasure hΛ).real {t}) = _
  rw [boundaryMeasure_vonMangoldt_real_singleton]
  simp

/-- Every bounded interval of the canonical zeta measure has integer mass. -/
theorem boundaryMeasure_vonMangoldt_integer_counting
    (hΛ : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (u v : ℝ) :
    ∃ n : ℕ, boundaryMeasure hΛ (Ioc u v) = n := by
  classical
  have hS : (Ioc u v ∩ criticalOrdinates).Finite := by
    refine ((zetaZeroConfig.finite_window u v).image Complex.im).subset ?_
    intro t ht
    refine ⟨(criticalZero ht.2 : ℂ), ?_, by simp [criticalZero]⟩
    exact ⟨(criticalZero ht.2).2, by simpa [criticalZero] using ht.1⟩
  let S := hS.toFinset
  refine ⟨∑ t ∈ S, analyticOrderNatAt xi ((1 / 2 : ℂ) + t * I), ?_⟩
  calc
    boundaryMeasure hΛ (Ioc u v) = boundaryMeasure hΛ (Ioc u v ∩ criticalOrdinates) :=
      (measure_inter_conull (boundaryMeasure_vonMangoldt_compl_criticalOrdinates hΛ)).symm
    _ = ∑ t ∈ S, boundaryMeasure hΛ {t} := by
      rw [sum_measure_singleton]
      simp [S]
    _ = _ := by simp only [boundaryMeasure_vonMangoldt_singleton_nat, Nat.cast_sum]

/-- Triple canonical atom mass is the exact analytic multiplicity of the completion. -/
theorem three_mul_boundaryMeasure_singleton {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : ZetaPowerDatum 3 g E) (hRH : ∀ s, E s = 0 → s.re = 1 / 2)
    {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΛ : ∀ s : ℂ, 1 < s.re →
      deriv (LSeries g) s = -(3 : ℂ) * LSeries (WeilHerglotz.lamC lam) s * LSeries g s)
    (t : ℝ) :
    (3 : ℝ≥0∞) * boundaryMeasure
      (weilPositiveFull_of_zetaPowerDatum (by norm_num) hD hRH hsl hΛ) {t} =
      (analyticOrderNatAt E ((1 / 2 : ℂ) + t * I) : ℝ≥0∞) := by
  classical
  let F : ℂ → ℂ := fun z => E (z + 2)
  let w : ℂ := (1 / 2 : ℂ) + t * I - 2
  have hF : AnalyticOnNhd ℂ F univ := fun z _ =>
    (hD.entire.comp (differentiable_id.add_const 2)).analyticAt z
  let S : Set (ZeroCopy F) := {q | zeroCopyPoint F q = w}
  have hS : S.Finite := (locallyFinite_zeroCopyPoint hF ‖w‖).subset (fun q hq => by
    change ‖zeroCopyPoint F q‖ ≤ ‖w‖
    rw [hq])
  have hτ (q : ZeroCopy F) : (zeroCopyPoint F q + 2).im = t ↔ q ∈ S := by
    constructor
    · intro ht
      have hz : F (zeroCopyPoint F q) = 0 := by
        by_contra hz
        apply q.1.2
        change (MeromorphicOn.divisor F univ) (zeroCopyPoint F q) = 0
        rw [divisor_univ_eq_analyticOrder hF,
          (hF _ (mem_univ _)).analyticOrderAt_eq_zero.mpr hz]
        rfl
      have hr := hRH _ hz
      change zeroCopyPoint F q = w
      apply Complex.ext
      · norm_num at hr
        norm_num [w]
        linarith
      · dsimp [w]
        simpa using ht
    · intro hq
      change zeroCopyPoint F q = w at hq
      rw [hq]
      simp [w]
  rw [boundaryMeasure_eq_zeroMeasure (by norm_num) hD hRH hsl hΛ,
    Measure.sum_apply _ (measurableSet_singleton t)]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton t), smul_eq_mul]
  rw [ENNReal.tsum_mul_left, ← mul_assoc]
  have hscalar : (3 : ℝ≥0∞) * ENNReal.ofReal (1 / (3 : ℝ)) = 1 := by
    rw [one_div, ENNReal.ofReal_inv_of_pos (show (0 : ℝ) < 3 by norm_num), ENNReal.ofReal_ofNat]
    exact ENNReal.mul_inv_cancel (by norm_num) (by simp)
  norm_num only [Nat.cast_ofNat] at *
  rw [hscalar, one_mul]
  have hsum : (∑' q : ZeroCopy F,
      ({t} : Set ℝ).indicator (1 : ℝ → ℝ≥0∞) (zeroCopyPoint F q + 2).im) = (S.ncard : ℝ≥0∞) := by
    rw [tsum_eq_sum (s := hS.toFinset) (fun q hq => by
      have hq' : q ∉ S := by simpa using hq
      simp only [Set.indicator_apply, mem_singleton_iff, hτ q, hq', ↓reduceIte])]
    rw [Set.ncard_eq_toFinset_card S hS]
    simp only [Set.indicator_apply, mem_singleton_iff, hτ]
    calc
      _ = ∑ _q ∈ hS.toFinset, (1 : ℝ≥0∞) :=
        Finset.sum_congr rfl (fun q hq => if_pos (hS.mem_toFinset.mp hq))
      _ = _ := by simp
  rw [hsum, ncard_zeroCopy_fiber w, divisor_univ_eq_analyticOrder hF w]
  have horder : analyticOrderAt F w = analyticOrderAt E ((1 / 2 : ℂ) + t * I) := by
    have h := analyticOrderAt_comp_of_deriv_ne_zero (f := E)
      (g := fun z : ℂ => z + 2) (z₀ := w) (by fun_prop) (by simp)
    simpa [F, Function.comp_def, w] using h
  rw [horder]
  rcases eq_or_ne (analyticOrderAt E ((1 / 2 : ℂ) + t * I)) ⊤ with ht | ht
  · unfold analyticOrderNatAt
    rw [ht]
    rfl
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp ht
    unfold analyticOrderNatAt
    rw [← hn]
    simp

/-- Containment of one complete zeta divisor reduces the third-counting datum to degree two. -/
theorem eq_vonMangoldt_of_xi_multiplicity_le {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : ZetaPowerDatum 3 g E) (hRH : ∀ s, E s = 0 → s.re = 1 / 2)
    {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΛ : ∀ s : ℂ, 1 < s.re →
      deriv (LSeries g) s = -(3 : ℂ) * LSeries (WeilHerglotz.lamC lam) s * LSeries g s)
    (horder : ∀ s, analyticOrderNatAt xi s ≤ analyticOrderNatAt E s) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hζRH : RiemannHypothesis := by
    apply riemannHypothesis_iff_xi_zero_re_eq_half.mpr
    intro s hs
    have hm : analyticOrderNatAt xi s ≠ 0 := by
      intro hm
      have ho := Nat.cast_analyticOrderNatAt (xi_orderAt_ne_top s)
      rw [hm, Nat.cast_zero] at ho
      exact ((xi_differentiable.analyticAt s).analyticOrderAt_eq_zero.mp ho.symm) hs
    exact hRH s (apply_eq_zero_of_analyticOrderNatAt_ne_zero
      (Nat.ne_of_gt ((Nat.pos_of_ne_zero hm).trans_le (horder s))))
  let hW := weilPositiveFull_of_zetaPowerDatum (by norm_num) hD hRH hsl hΛ
  have hWΛ := riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hζRH
  refine eq_vonMangoldt_of_third_counting_of_integer_domination hW hWΛ
    (fun u v _ => exists_natCast_eq_mul_boundaryMeasure (by norm_num) hD hRH hsl hΛ u v)
    (fun u v _ => boundaryMeasure_vonMangoldt_integer_counting hWΛ u v) ?_
  apply measure_le_of_countable_atoms countable_criticalOrdinates
    (boundaryMeasure_vonMangoldt_compl_criticalOrdinates hWΛ)
  intro t _
  rw [Measure.smul_apply, smul_eq_mul, boundaryMeasure_vonMangoldt_singleton_nat,
    three_mul_boundaryMeasure_singleton hD hRH hsl hΛ]
  exact_mod_cast horder ((1 / 2 : ℂ) + t * I)

/-- Every nontrivial complete degree-three datum loses some zeta multiplicity.
This unconditional dichotomy adds neither RH for zeta nor simplicity of its zeros. -/
theorem degreeThree_eq_vonMangoldt_or_multiplicity_deficit {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : ZetaPowerDatum 3 g E) (hRH : ∀ s, E s = 0 → s.re = 1 / 2)
    {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΛ : ∀ s : ℂ, 1 < s.re →
      deriv (LSeries g) s = -(3 : ℂ) * LSeries (WeilHerglotz.lamC lam) s * LSeries g s) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∨
      ∃ ρ : ℂ, xi ρ = 0 ∧ analyticOrderNatAt E ρ < analyticOrderNatAt xi ρ := by
  classical
  by_cases h : ∀ s, analyticOrderNatAt xi s ≤ analyticOrderNatAt E s
  · exact Or.inl (eq_vonMangoldt_of_xi_multiplicity_le hD hRH hsl hΛ h).1
  · push Not at h
    obtain ⟨ρ, hρ⟩ := h
    exact Or.inr ⟨ρ, apply_eq_zero_of_analyticOrderNatAt_ne_zero
      (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hρ)), hρ⟩

end RHTower.WeilHigherDenominator
