import GaloisForLFunctions.RHTower.WeilAtomicBoundaryMeasure
import GaloisForLFunctions.RHTower.WeilHalfIntegerMassRigidity

/-!
# Removing an integer spectral component from third-integral counting

The affine identity `3a = b + 2c` transports to the canonical measures. If the measure of
an integer-counting system `b` is dominated by three times that of a third-counting system
`a`, the remainder `c = (3a-b)/2` is Weil-positive and has half-integer counting. The proved
degree-two theorem then forces both the remainder and `a` to be von Mangoldt.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
open Zeta23

noncomputable section

namespace RHTower.WeilHigherDenominator

open WeilSpectral

/-- Affine balance of the coefficients preserves the complete explicit formula. -/
theorem weilFullFunctional_three_balance {a b c : ℕ → ℝ}
    (h : ∀ n, 3 * a n = b n + 2 * c n) {k : ℝ → ℂ} (hk : HasCompactSupport k) :
    3 * weilFullFunctional a k = weilFullFunctional b k + 2 * weilFullFunctional c k := by
  let P (v : ℕ → ℝ) (n : ℕ) : ℂ :=
    ((if 2 ≤ n then v n / Real.sqrt n else 0 : ℝ) : ℂ) *
      (k (Real.log n) + k (-Real.log n))
  have hs (v : ℕ → ℝ) : Summable (P v) := summable_primeAtoms _ hk
  have hP : 3 * ∑' n, P a n = (∑' n, P b n) + 2 * ∑' n, P c n := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (hs b).tsum_add ((hs c).mul_left 2)]
    apply tsum_congr
    intro n
    dsimp [P]
    split_ifs with hn
    · have hn' : (3 : ℂ) * a n = b n + 2 * c n := by exact_mod_cast h n
      push_cast
      linear_combination ((k (Real.log n) + k (-Real.log n)) / (Real.sqrt n : ℂ)) * hn'
    · simp
  unfold weilFullFunctional
  change 3 * (_ + _ - ∑' n, P a n + _) =
    (_ + _ - ∑' n, P b n + _) + 2 * (_ + _ - ∑' n, P c n + _)
  linear_combination -hP

private theorem integrable_character (μ : Measure ℝ) [IsFiniteMeasure μ] (y : ℝ) :
    Integrable (fun x : ℝ => Complex.exp ((y : ℂ) * x * I)) μ := by
  refine Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun x => ?_)
  rw [Complex.norm_exp]
  simp

private theorem charFun_add (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (y : ℝ) : charFun (μ + ν) y = charFun μ y + charFun ν y := by
  simp only [charFun_apply_real]
  exact integral_add_measure (integrable_character μ y) (integrable_character ν y)

private theorem charFun_smul (μ : Measure ℝ) (r : ℝ≥0∞) (y : ℝ) :
    charFun (r • μ) y = (r.toReal : ℂ) * charFun μ y := by
  simp [charFun_apply_real, integral_smul_measure, real_smul]

/-- The canonical measures retain every term of an affine coefficient balance. -/
theorem boundaryMeasure_three_balance {a b c : ℕ → ℝ}
    (ha : WeilPositiveFull a) (hb : WeilPositiveFull b) (hc : WeilPositiveFull c)
    (h : ∀ n, 3 * a n = b n + 2 * c n) :
    (3 : ℝ≥0∞) • boundaryMeasure ha = boundaryMeasure hb + (2 : ℝ≥0∞) • boundaryMeasure hc := by
  apply WeilAtomic.eq_of_forall_withDensity_mollC
  intro j
  haveI := isFiniteMeasure_mollifierMeasure ha j
  haveI := isFiniteMeasure_mollifierMeasure hb j
  haveI := isFiniteMeasure_mollifierMeasure hc j
  haveI := (mollifierMeasure ha j).smul_finite (c := (3 : ℝ≥0∞)) (by norm_num)
  haveI := (mollifierMeasure hc j).smul_finite (c := (2 : ℝ≥0∞)) (by norm_num)
  have hmeas : (3 : ℝ≥0∞) • mollifierMeasure ha j =
      mollifierMeasure hb j + (2 : ℝ≥0∞) • mollifierMeasure hc j := by
    apply Measure.ext_of_charFun
    funext y
    rw [charFun_add, charFun_smul, charFun_smul]
    simp only [ENNReal.toReal_ofNat, Complex.ofReal_ofNat, charFun_mollifierMeasure]
    exact weilFullFunctional_three_balance h
      (WeilAtomic.hasCompactSupport_transl
        (EF.weilTest_hasCompactSupport (WeilHerglotz.hasCompactSupport_mollC j)
          (WeilHerglotz.hasCompactSupport_mollC j)) y)
  have heq (v : ℕ → ℝ) (hv : WeilPositiveFull v) : mollifierMeasure hv j =
      (boundaryMeasure hv).withDensity (fun r => (specDensity (WeilHerglotz.mollC j) r : ℝ≥0∞)) := by
    haveI := isFiniteMeasure_mollifierMeasure hv j
    exact eq_withDensity_boundaryMeasure hv (contDiff_mollC j)
      (WeilHerglotz.hasCompactSupport_mollC j) (charFun_mollifierMeasure hv j)
  rw [withDensity_smul_measure, withDensity_add_measure, withDensity_smul_measure,
    ← heq a ha, ← heq b hb, ← heq c hc]
  exact hmeas

/-- Spectral domination pays the positivity of the degree-two remainder. -/
theorem weilPositiveFull_remainder_of_domination {a b : ℕ → ℝ}
    (ha : WeilPositiveFull a) (hb : WeilPositiveFull b)
    (hdom : boundaryMeasure hb ≤ (3 : ℝ≥0∞) • boundaryMeasure ha) :
    WeilPositiveFull (fun n => (3 * a n - b n) / 2) := by
  intro f hf hfc
  obtain ⟨hafin, haeq⟩ := weilFullFunctional_weilTest_eq_lintegral ha hf hfc
  obtain ⟨_, hbeq⟩ := weilFullFunctional_weilTest_eq_lintegral hb hf hfc
  have hle := lintegral_mono' hdom (fun r => le_refl (specDensity f r : ℝ≥0∞))
  rw [lintegral_smul_measure] at hle
  have hfin : (3 : ℝ≥0∞) * ∫⁻ r, (specDensity f r : ℝ≥0∞) ∂boundaryMeasure ha ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hafin.ne
  have hreal := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_mul] at hreal
  norm_num at hreal
  have hbalance := congrArg Complex.re (weilFullFunctional_three_balance
    (a := a) (b := b) (c := fun n => (3 * a n - b n) / 2) (fun n => by ring)
    (EF.weilTest_hasCompactSupport hfc hfc))
  rw [haeq, hbeq] at hbalance
  norm_num [Complex.add_re, Complex.mul_re] at hbalance
  linarith

/-- An integer component dominated by the third-counting measure forces complete rigidity.
The positivity of the remainder is proved from domination, not supplied as a premise. -/
theorem eq_vonMangoldt_of_third_counting_of_integer_domination {a b : ℕ → ℝ}
    (ha : WeilPositiveFull a) (hb : WeilPositiveFull b)
    (haCount : ∀ u v : ℝ, u < v → ∃ n : ℕ,
      (3 : ℝ≥0∞) * boundaryMeasure ha (Ioc u v) = n)
    (hbCount : ∀ u v : ℝ, u < v → ∃ n : ℕ, boundaryMeasure hb (Ioc u v) = n)
    (hdom : boundaryMeasure hb ≤ (3 : ℝ≥0∞) • boundaryMeasure ha) :
    (∀ n : ℕ, 2 ≤ n → a n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  let c : ℕ → ℝ := fun n => (3 * a n - b n) / 2
  have hc : WeilPositiveFull c := weilPositiveFull_remainder_of_domination ha hb hdom
  have hbalance := boundaryMeasure_three_balance ha hb hc (fun n => by dsimp [c]; ring)
  have hcCount : ∀ u v : ℝ, u < v → ∃ n : ℕ,
      (2 : ℝ≥0∞) * boundaryMeasure hc (Ioc u v) = n := by
    intro u v huv
    obtain ⟨m, hm⟩ := haCount u v huv
    obtain ⟨n, hn⟩ := hbCount u v huv
    have hset := congrArg (fun μ : Measure ℝ => μ (Ioc u v)) hbalance
    simp only [Measure.smul_apply, Measure.add_apply, smul_eq_mul] at hset
    rw [hm, hn] at hset
    refine ⟨m - n, ?_⟩
    rw [ENNReal.natCast_sub]
    exact ENNReal.eq_sub_of_add_eq (by norm_num)
      (by simpa only [add_comm] using hset.symm)
  have hcRigid := HalfIntegerMassRigidity.vonMangoldt_and_riemannHypothesis_of_half_integer_counting
    hc (Y := univ) (by simp) (fun u _ v _ huv => hcCount u v huv)
  have hbRigid := HalfIntegerMassRigidity.vonMangoldt_and_riemannHypothesis_of_half_integer_counting
    hb (Y := univ) (by simp) (fun u _ v _ huv => by
      obtain ⟨n, hn⟩ := hbCount u v huv
      exact ⟨2 * n, by rw [hn]; norm_cast⟩)
  refine ⟨fun n hn => ?_, hcRigid.2⟩
  have heq := hcRigid.1 n hn
  dsimp [c] at heq
  rw [hbRigid.1 n hn] at heq
  linarith

end RHTower.WeilHigherDenominator
