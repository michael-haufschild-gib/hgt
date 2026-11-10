import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.IsozericTangentFlow

/-!
# Local pole preservation classifies isozeric gauge fibres

A gauge fibre has a holomorphic regularization `(s-1)F_x(s)` with nonzero
value at one exactly when its prime perturbations are absolutely summable
at some exponent below one. Pairing with the opposite gauge continues the
positive prime-defect derivative through one; Landau forces a power saving,
and weighted Cauchy–Schwarz gives absolute summability.

The given regularization is the germ of `Z exp(H_x)`. Thus it extends to a
half-plane left of one with precisely the zero multiplicities of ζ away
from the pole. Only a local residue germ is required.
-/

open Complex Filter Topology Metric Set
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

private theorem conj_mem_ball_one {z : ℂ} {r : ℝ} (hz : z ∈ ball 1 r) :
    conj z ∈ ball 1 r := by
  have he : conj z - 1 = conj (z - 1) := by rw [map_sub, map_one]
  rw [mem_ball, dist_eq_norm, he, norm_conj]
  simpa only [mem_ball, dist_eq_norm] using hz

private theorem analyticAt_schwarz_one {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 1) :
    AnalyticAt ℂ (schwarzConjugate U) 1 := by
  obtain ⟨r, hr, hb⟩ := hU.exists_ball_analyticOnNhd
  have hd : DifferentiableOn ℂ (schwarzConjugate U) (ball 1 r) := by
    intro z hz
    have h := (hb (conj z) (conj_mem_ball_one hz)).differentiableAt.conj_conj
    rw [Complex.conj_conj] at h
    exact h.differentiableWithinAt
  exact hd.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hr))

/-- The paired logarithmic derivative identity only needs a germ of the Euler identity. -/
theorem cleared_pair_identity_local {x : GaugeTorus} {U V : ℂ → ℂ} {s : ℂ}
    (hs : 1 < s.re) (hU : AnalyticAt ℂ U s) (hV : AnalyticAt ℂ V s)
    (heq : (fun z => U z * V z) =ᶠ[𝓝 s]
      (fun z => zetaResidueFactor z ^ 2 * cexp (pairedExponent x z))) :
    pairedDenominator U V s * primeDefectDerivativeSeries x s =
      pairedNumerator x U V s := by
  have hZ := (differentiable_zetaResidueFactor s).hasDerivAt
  have hE := ((analyticOnNhd_primeDefectSeries x) s hs).differentiableAt.hasDerivAt
  rw [deriv_primeDefectSeries x hs] at hE
  have hR := ((analyticOnNhd_pairedRemainder x) s
    (show s ∈ PrimeTorusTheory.rightHalf by change 1 / 2 < s.re; linarith only [hs])).differentiableAt.hasDerivAt
  have hH : HasDerivAt (pairedExponent x)
      (2 * primeDefectDerivativeSeries x s + deriv (pairedRemainder x) s) s :=
    ((hE.const_mul (-2)).add hR).congr_deriv (by ring)
  have hright := (hZ.pow 2).mul hH.cexp
  have hleft := hU.differentiableAt.hasDerivAt.mul hV.differentiableAt.hasDerivAt
  have hd := hleft.unique (hright.congr_of_eventuallyEq heq)
  norm_num only [Pi.pow_apply] at hd
  have hv := heq.eq_of_nhds
  dsimp [pairedDenominator, pairedNumerator]
  linear_combination -zetaResidueFactor s * hd +
    (2 * deriv zetaResidueFactor s + zetaResidueFactor s *
      (2 * primeDefectDerivativeSeries x s + deriv (pairedRemainder x) s)) * hv

/-- A nonzero local residue forces convergence of the positive prime defect below one. -/
theorem prime_defect_below_one_of_local_residue {x : GaugeTorus} {U : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 1) (hUne : U 1 ≠ 0)
    (hagree : ∀ᶠ s in 𝓝 (1 : ℂ), 1 < s.re → U s = (s - 1) * gaugeFibre x s) :
    ∃ σ : ℝ, σ < 1 ∧ Summable (gdTwistTerm (primeDefect x) primeFrequency σ 0) := by
  let V := schwarzConjugate U
  have hV : AnalyticAt ℂ V 1 := analyticAt_schwarz_one hU
  have hVne : V 1 ≠ 0 := by simpa only [V, schwarzConjugate, map_one, map_ne_zero] using hUne
  have hZ : AnalyticAt ℂ zetaResidueFactor 1 := differentiable_zetaResidueFactor.analyticAt 1
  have hR : AnalyticAt ℂ (pairedRemainder x) 1 :=
    analyticOnNhd_pairedRemainder x 1 (by change (1 / 2 : ℝ) < 1; norm_num)
  have hP : AnalyticAt ℂ (pairedDenominator U V) 1 :=
    ((analyticAt_const.mul hZ).mul hU).mul hV
  have hN : AnalyticAt ℂ (pairedNumerator x U V) 1 :=
    ((hZ.mul ((hU.deriv.mul hV).add (hU.mul hV.deriv))).sub
      (((analyticAt_const.mul hZ.deriv).mul hU).mul hV)).sub
      (((hR.deriv.mul hZ).mul hU).mul hV)
  have hPne : pairedDenominator U V 1 ≠ 0 := by
    dsimp [pairedDenominator]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (by rw [zetaResidueFactor_one]; exact one_ne_zero)) hUne) hVne
  have hQ := hN.div hP hPne
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp
    (hU.eventually_analyticAt.and (hV.eventually_analyticAt.and hagree))
  have hpair (s : ℂ) (hs : s ∈ ball 1 r) (hse : 1 < s.re) :
      U s * V s = zetaResidueFactor s ^ 2 * cexp (pairedExponent x s) := by
    have hveq : V s = (s - 1) * gaugeFibre (-x) s := by
      dsimp [V, schwarzConjugate]
      rw [(hb (conj_mem_ball_one hs)).2.2 (by simpa using hse), map_mul,
        map_sub, map_one, Complex.conj_conj, gaugeFibre_neg_eq_conj]
    have hs1 : s ≠ 1 := by intro h; simp [h] at hse
    rw [(hb hs).2.2 hse, hveq, zetaResidueFactor_of_ne hs1]
    calc
      _ = (s - 1) ^ 2 * (gaugeFibre x s * gaugeFibre (-x) s) := by ring
      _ = _ := by rw [gaugeFibre_pair_eq x hse]; dsimp [pairedExponent]; ring
  have hid (s : ℂ) (hs : s ∈ ball 1 r) (hse : 1 < s.re) :
      pairedDenominator U V s * primeDefectDerivativeSeries x s = pairedNumerator x U V s := by
    apply cleared_pair_identity_local hse (hb hs).1 (hb hs).2.1
    filter_upwards [isOpen_ball.mem_nhds hs,
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hse] with z hz hze
    exact hpair z hz hze
  -- If convergence began at one, the holomorphic quotient would violate Landau.
  have hex : ∃ σ : ℝ, σ < 1 ∧ Summable (gdTwistTerm
      (fun p => primeDefect x p * primeFrequency p) primeFrequency σ 0) := by
    by_contra hn
    have hdiv : ∀ σ : ℝ, σ < 1 → ¬ Summable (gdTwistTerm
        (fun p => primeDefect x p * primeFrequency p) primeFrequency σ 0) := by
      intro σ hσ hs
      exact hn ⟨σ, hσ, hs⟩
    obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp
      (hQ.eventually_analyticAt.and
        ((hP.continuousAt.eventually_ne hPne).and (ball_mem_nhds 1 hr)))
    apply gdSeries_no_continuation_at_abscissa
      (fun p => mul_nonneg (primeDefect_nonneg x p) (primeFrequency_nonneg p))
      primeFrequency_nonneg (fun σ hσ => summable_primeDefectDerivative x hσ) hdiv hρ
      (G := fun s => pairedNumerator x U V s / pairedDenominator U V s)
    · intro s hs
      exact (hball hs).1.differentiableAt.differentiableWithinAt
    · intro s hs hse
      apply (div_eq_iff (hball hs).2.1).mpr
      simpa only [primeDefectDerivativeSeries, mul_comm] using (hid s (hball hs).2.2 hse).symm
  obtain ⟨σ, hσ, hs⟩ := hex
  exact ⟨σ, hσ, summable_primeDefect_of_derivative hs⟩

/-- Local pole preservation forces an absolutely summable prime perturbation below one. -/
theorem absolute_prime_below_one_of_local_residue {x : GaugeTorus} {U : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 1) (hUne : U 1 ≠ 0)
    (hagree : ∀ᶠ s in 𝓝 (1 : ℂ), 1 < s.re → U s = (s - 1) * gaugeFibre x s) :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧
      Summable (fun p : Nat.Primes => ‖twist x p - 1‖ * (p : ℝ) ^ (-σ)) := by
  obtain ⟨σ, hσ, hs⟩ := prime_defect_below_one_of_local_residue hU hUne hagree
  let τ := max σ (3 / 4)
  have hτ : τ < 1 := max_lt hσ (by norm_num)
  have hτ₀ : 3 / 4 ≤ τ := le_max_right _ _
  have ht := summable_gdTwistTerm_of_le (primeDefect_nonneg x) primeFrequency_nonneg hs
    (show σ ≤ τ from le_max_left _ _)
  have he (p : Nat.Primes) : ‖twist x p - 1‖ ^ 2 * (p : ℝ) ^ (-(1 - (1 - τ))) =
      2 * gdTwistTerm (primeDefect x) primeFrequency τ 0 p := by
    rw [norm_twist_sub_one_sq]
    simp only [gdTwistTerm, pow_zero, mul_one, sub_sub_cancel, prime_exp_decay]
    ring
  -- The squared distance of unit phases is twice their nonnegative real defect.
  have henergy : Summable (fun p : Nat.Primes =>
      ‖twist x p - 1‖ ^ 2 * (p : ℝ) ^ (-(1 - (1 - τ)))) := by
    simpa only [he] using ht.mul_left 2
  refine ⟨1 - (1 - τ) / 4, by linarith only [hτ₀], by linarith only [hτ], ?_⟩
  simpa only [abs_norm] using summable_absolute_prime_of_energy
    (show 0 < 1 - τ by linarith only [hτ]) henergy

#print axioms absolute_prime_below_one_of_local_residue

/-- Equality on the Euler side determines an analytic germ at one. -/
private theorem analytic_germ_eq_of_right_agreement {U W : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 1) (hW : AnalyticAt ℂ W 1)
    (hagree : ∀ᶠ s in 𝓝 (1 : ℂ), 1 < s.re → U s = W s) :
    U =ᶠ[𝓝 (1 : ℂ)] W := by
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp
    (hU.eventually_analyticAt.and (hW.eventually_analyticAt.and hagree))
  have hu : AnalyticOnNhd ℂ U (ball 1 r) := fun s hs => (hb hs).1
  have hw : AnalyticOnNhd ℂ W (ball 1 r) := fun s hs => (hb hs).2.1
  let c : ℂ := 1 + ((r / 2 : ℝ) : ℂ)
  have hc : c ∈ ball 1 r := by
    dsimp [c]
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith only [hr] : 0 < r / 2)]
    linarith only [hr]
  have hce : 1 < c.re := by
    dsimp [c]
    linarith only [hr]
  have he : U =ᶠ[𝓝 c] W := by
    filter_upwards [isOpen_ball.mem_nhds hc,
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hce] with s hs hse
    exact (hb hs).2.2 hse
  have hid := hu.eqOn_of_preconnected_of_eventuallyEq hw
    (convex_ball (1 : ℂ) r).isPreconnected hc he
  filter_upwards [ball_mem_nhds (1 : ℂ) hr] with s hs
  exact hid hs

/-- A local nonzero residue is equivalent to absolute prime summability below one. -/
theorem local_nonzero_residue_iff (x : GaugeTorus) :
    (∃ U : ℂ → ℂ, AnalyticAt ℂ U 1 ∧ U 1 ≠ 0 ∧
      ∀ᶠ s in 𝓝 (1 : ℂ), 1 < s.re → U s = (s - 1) * gaugeFibre x s) ↔
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧
      Summable (fun p : Nat.Primes => ‖twist x p - 1‖ * (p : ℝ) ^ (-σ)) := by
  constructor
  · rintro ⟨U, hU, hUne, he⟩
    exact absolute_prime_below_one_of_local_residue hU hUne he
  · rintro ⟨σ, hσ₀, hσ₁, hs⟩
    obtain ⟨hH, he⟩ := exists_isozeric hσ₀.le hs
    refine ⟨fun s => zetaResidueFactor s * cexp (deformationExponent x s),
      (differentiable_zetaResidueFactor.analyticAt 1).mul (hH 1 hσ₁).cexp, ?_, ?_⟩
    · change zetaResidueFactor 1 * cexp (deformationExponent x 1) ≠ 0
      rw [zetaResidueFactor_one, one_mul]
      exact Complex.exp_ne_zero _
    · apply Filter.Eventually.of_forall
      intro s hse
      have hs1 : s ≠ 1 := by intro h; simp [h] at hse
      change zetaResidueFactor s * cexp (deformationExponent x s) =
        (s - 1) * gaugeFibre x s
      rw [he s hse, zetaResidueFactor_of_ne hs1, mul_assoc]

/-- The given local regularization extends to an isozeric half-plane left of one. -/
theorem local_residue_isozeric_continuation {x : GaugeTorus} {U : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 1) (hUne : U 1 ≠ 0)
    (hagree : ∀ᶠ s in 𝓝 (1 : ℂ), 1 < s.re → U s = (s - 1) * gaugeFibre x s) :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧
      Summable (fun p : Nat.Primes => ‖twist x p - 1‖ * (p : ℝ) ^ (-σ)) ∧
      AnalyticOnNhd ℂ (deformationExponent x) {s : ℂ | σ < s.re} ∧
      (U =ᶠ[𝓝 (1 : ℂ)] (fun s => zetaResidueFactor s * cexp (deformationExponent x s))) ∧
      (∀ s : ℂ, 1 < s.re → gaugeFibre x s = riemannZeta s * cexp (deformationExponent x s)) ∧
      ∀ s : ℂ, σ < s.re → s ≠ 1 →
        analyticOrderAt (fun z => riemannZeta z * cexp (deformationExponent x z)) s =
          analyticOrderAt riemannZeta s := by
  obtain ⟨σ, hσ₀, hσ₁, hs⟩ := absolute_prime_below_one_of_local_residue hU hUne hagree
  obtain ⟨hH, he⟩ := exists_isozeric hσ₀.le hs
  refine ⟨σ, hσ₀, hσ₁, hs, hH, ?_, he, fun s hse hs1 =>
    analyticOrderAt_isozeric hσ₀.le hs hse hs1⟩
  apply analytic_germ_eq_of_right_agreement hU
    ((differentiable_zetaResidueFactor.analyticAt 1).mul (hH 1 hσ₁).cexp)
  filter_upwards [hagree] with s hse
  intro hsre
  have hs1 : s ≠ 1 := by intro h; simp [h] at hsre
  change U s = zetaResidueFactor s * cexp (deformationExponent x s)
  rw [hse hsre, he s hsre, zetaResidueFactor_of_ne hs1, mul_assoc]

#print axioms local_nonzero_residue_iff
#print axioms local_residue_isozeric_continuation

end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
