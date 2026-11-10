import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.LocalResidueClassification

/-!
# Common isozeric half-planes from joint pole germs

A positive Dirichlet series satisfying a local cleared analytic identity
on `B(1,r)` converges at every real exponent greater than `1-r`, provided
the denominator does not vanish on the real diameter. Analytic uniqueness
and Landau's theorem exclude any convergence boundary inside that disk.

For an actual gauge regularization this gives quadratic prime summability
up to the disk's left edge, and absolute summability at `1-r/8`.
A jointly holomorphic nonzero pole germ supplies a common disk for every
nearby real parameter. All these fibres therefore extend their given germs
to one common half-plane left of one, with exactly the zero multiplicities
of ζ. No separate holomorphic prime-coordinate model is assumed.
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

private theorem real_mem_pole_ball {t r : ℝ} :
    (t : ℂ) ∈ ball 1 r ↔ 1 - r < t ∧ t < 1 + r := by
  rw [mem_ball, dist_eq_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_lt]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith only [h₁, h₂]

/-- A local cleared identity transfers its real disk radius to the convergence abscissa. -/
theorem summable_of_pole_disk_identity {ι : Type*} {a lam : ι → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hlam : ∀ j, 0 ≤ lam j)
    (hsum : ∀ σ : ℝ, 1 < σ → Summable (gdTwistTerm a lam σ 0))
    {r : ℝ} (hr : 0 < r) {P N : ℂ → ℂ}
    (hP : AnalyticOnNhd ℂ P (ball 1 r)) (hN : AnalyticOnNhd ℂ N (ball 1 r))
    (hPne : ∀ t : ℝ, (t : ℂ) ∈ ball 1 r → P (t : ℂ) ≠ 0)
    (hagree : ∀ s ∈ ball (1 : ℂ) r, 1 < s.re → P s * gdSeries a lam s = N s)
    {σ : ℝ} (hσ : 1 - r < σ) : Summable (gdTwistTerm a lam σ 0) := by
  classical
  by_contra hnot
  let S : Set ℝ := {t | Summable (gdTwistTerm a lam t 0)}
  have hSne : S.Nonempty := ⟨2, hsum 2 (by norm_num)⟩
  have hbelow : ∀ t ∈ S, σ ≤ t := by
    intro t ht
    by_contra h
    exact hnot (summable_gdTwistTerm_of_le ha hlam ht (le_of_not_ge h))
  have hSbdd : BddBelow S := ⟨σ, hbelow⟩
  let σc : ℝ := sInf S
  have hσc : σ ≤ σc := le_csInf hSne hbelow
  have hc₁ : σc ≤ 1 := by
    by_contra hn
    have hh : 1 < σc := lt_of_not_ge hn
    have hm : σc ≤ (σc + 1) / 2 :=
      csInf_le hSbdd (hsum _ (by linarith only [hh]))
    linarith only [hh, hm]
  have hright : ∀ t : ℝ, σc < t → Summable (gdTwistTerm a lam t 0) := by
    intro t ht
    have hex : ∃ u ∈ S, u < t := by
      by_contra hn
      push Not at hn
      exact (not_le_of_gt ht) (le_csInf hSne hn)
    obtain ⟨u, hu, hut⟩ := hex
    exact summable_gdTwistTerm_of_le ha hlam hu hut.le
  have hleft : ∀ t : ℝ, t < σc → ¬ Summable (gdTwistTerm a lam t 0) := by
    intro t ht hts
    exact (not_le_of_gt ht) (csInf_le hSbdd hts)
  have hcb : (σc : ℂ) ∈ ball 1 r := real_mem_pole_ball.mpr
    ⟨hσ.trans_le hσc, by linarith only [hc₁, hr]⟩
  have hDdiff : DifferentiableOn ℂ (gdSeries a lam) {s : ℂ | σc < s.re} := by
    intro s hs
    change σc < s.re at hs
    have hm : σc < (σc + s.re) / 2 := by linarith only [hs]
    exact (differentiableAt_gdSeries ha hlam (hright _ hm)
      (by linarith only [hs])).differentiableWithinAt
  have hD := hDdiff.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)
  let T : Set ℂ := ball 1 r ∩ {s : ℂ | σc < s.re}
  -- Continue the cleared identity where the disk meets the convergence half-plane.
  have hid : EqOn (fun s => P s * gdSeries a lam s) N T := by
    have hanchor : (((1 + r / 2 : ℝ) : ℂ)) ∈ ball 1 r :=
      real_mem_pole_ball.mpr ⟨by linarith only [hr], by linarith only [hr]⟩
    apply ((hP.mono inter_subset_left).mul (hD.mono inter_subset_right)).eqOn_of_preconnected_of_eventuallyEq
      (hN.mono inter_subset_left)
      ((convex_ball (1 : ℂ) r).inter (convex_halfSpace_re_gt σc)).isPreconnected
      (z₀ := ((1 + r / 2 : ℝ) : ℂ))
    · exact ⟨hanchor, by simp only [mem_setOf_eq, Complex.ofReal_re]; linarith only [hc₁, hr]⟩
    · filter_upwards [isOpen_ball.mem_nhds hanchor,
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
          (show 1 < (((1 + r / 2 : ℝ) : ℂ)).re by simp only [Complex.ofReal_re]; linarith only [hr])]
        with s hs hse
      exact hagree s hs hse
  have hPc := hP (σc : ℂ) hcb
  have hQ := (hN (σc : ℂ) hcb).div hPc (hPne σc hcb)
  obtain ⟨ρ, hρ, hb⟩ := Metric.mem_nhds_iff.mp
    (hQ.eventually_analyticAt.and
      ((hPc.continuousAt.eventually_ne (hPne σc hcb)).and (isOpen_ball.mem_nhds hcb)))
  apply gdSeries_no_continuation_at_abscissa ha hlam hright hleft hρ
    (G := fun s => N s / P s)
  · intro s hs
    exact (hb hs).1.differentiableAt.differentiableWithinAt
  · intro s hs hse
    apply (div_eq_iff (hb hs).2.1).mpr
    simpa only [mul_comm] using (hid ⟨(hb hs).2.2, hse⟩).symm

private theorem conj_mem_pole_ball {s : ℂ} {r : ℝ} (hs : s ∈ ball 1 r) :
    conj s ∈ ball 1 r := by
  have he : conj s - 1 = conj (s - 1) := by rw [map_sub, map_one]
  rw [mem_ball, dist_eq_norm, he, norm_conj]
  simpa only [mem_ball, dist_eq_norm] using hs

private theorem pole_ball_subset_rightHalf {r : ℝ} (hr : r ≤ 1 / 2) :
    ball (1 : ℂ) r ⊆ PrimeTorusTheory.rightHalf := by
  intro s hs
  have hn : ‖s - 1‖ < r := by simpa only [mem_ball, dist_eq_norm] using hs
  have ha := Complex.abs_re_le_norm (s - 1)
  simp only [Complex.sub_re, Complex.one_re] at ha
  have hb := neg_le_abs (s.re - 1)
  change 1 / 2 < s.re
  linarith only [hn, ha, hb, hr]

/-- A residue disk gives a quadratic saving up to its left edge. -/
theorem quadratic_prime_summable_of_residue_disk {x : GaugeTorus} {r : ℝ}
    (hr : 0 < r) (hr₂ : r ≤ 1 / 2) {U : ℂ → ℂ}
    (hU : AnalyticOnNhd ℂ U (ball 1 r))
    (hUne : ∀ t : ℝ, (t : ℂ) ∈ ball 1 r → U (t : ℂ) ≠ 0)
    (hagree : ∀ s ∈ ball (1 : ℂ) r, 1 < s.re → U s = (s - 1) * gaugeFibre x s)
    {σ : ℝ} (hσ : 1 - r < σ) :
    Summable (fun p : Nat.Primes => ‖twist x p - 1‖ ^ 2 * (p : ℝ) ^ (-σ)) := by
  let V := schwarzConjugate U
  have hV : AnalyticOnNhd ℂ V (ball 1 r) := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_ball
    intro s hs
    have h := (hU (conj s) (conj_mem_pole_ball hs)).differentiableAt.conj_conj
    rw [Complex.conj_conj] at h
    exact h.differentiableWithinAt
  have hZ : AnalyticOnNhd ℂ zetaResidueFactor (ball 1 r) :=
    fun s _ => differentiable_zetaResidueFactor.analyticAt s
  have hR : AnalyticOnNhd ℂ (pairedRemainder x) (ball 1 r) :=
    (analyticOnNhd_pairedRemainder x).mono (pole_ball_subset_rightHalf hr₂)
  have hP : AnalyticOnNhd ℂ (pairedDenominator U V) (ball 1 r) :=
    ((analyticOnNhd_const.mul hZ).mul hU).mul hV
  have hN : AnalyticOnNhd ℂ (pairedNumerator x U V) (ball 1 r) :=
    ((hZ.mul ((hU.deriv.mul hV).add (hU.mul hV.deriv))).sub
      (((analyticOnNhd_const.mul hZ.deriv).mul hU).mul hV)).sub
      (((hR.deriv.mul hZ).mul hU).mul hV)
  have hPne (t : ℝ) (ht : (t : ℂ) ∈ ball 1 r) : pairedDenominator U V (t : ℂ) ≠ 0 := by
    have htl := (real_mem_pole_ball.mp ht).1
    have hVne : V (t : ℂ) ≠ 0 := by
      simpa only [V, schwarzConjugate, Complex.conj_ofReal, map_ne_zero] using hUne t ht
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (zetaResidueFactor_real_ne_zero (by linarith only [htl, hr₂]))) (hUne t ht)) hVne
  have hpair (s : ℂ) (hs : s ∈ ball 1 r) (hse : 1 < s.re) :
      U s * V s = zetaResidueFactor s ^ 2 * cexp (pairedExponent x s) := by
    have hveq : V s = (s - 1) * gaugeFibre (-x) s := by
      dsimp [V, schwarzConjugate]
      rw [hagree (conj s) (conj_mem_pole_ball hs) (by simpa using hse), map_mul,
        map_sub, map_one, Complex.conj_conj, gaugeFibre_neg_eq_conj]
    have hs1 : s ≠ 1 := by intro h; simp [h] at hse
    rw [hagree s hs hse, hveq, zetaResidueFactor_of_ne hs1]
    calc
      _ = (s - 1) ^ 2 * (gaugeFibre x s * gaugeFibre (-x) s) := by ring
      _ = _ := by rw [gaugeFibre_pair_eq x hse]; dsimp [pairedExponent]; ring
  have hid (s : ℂ) (hs : s ∈ ball 1 r) (hse : 1 < s.re) :
      pairedDenominator U V s * primeDefectDerivativeSeries x s = pairedNumerator x U V s := by
    apply cleared_pair_identity_local hse (hU s hs) (hV s hs)
    filter_upwards [isOpen_ball.mem_nhds hs,
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hse] with z hz hze
    exact hpair z hz hze
  have hd := summable_of_pole_disk_identity
    (fun p => mul_nonneg (primeDefect_nonneg x p) (primeFrequency_nonneg p))
    primeFrequency_nonneg (fun σ hσ => summable_primeDefectDerivative x hσ)
    hr hP hN hPne hid hσ
  have hf := summable_primeDefect_of_derivative hd
  have he (p : Nat.Primes) : ‖twist x p - 1‖ ^ 2 * (p : ℝ) ^ (-σ) =
      2 * gdTwistTerm (primeDefect x) primeFrequency σ 0 p := by
    rw [norm_twist_sub_one_sq]
    simp only [gdTwistTerm, pow_zero, mul_one, prime_exp_decay]
    ring
  simpa only [he] using hf.mul_left 2

/-- A nonzero residue disk of radius `r` forces absolute prime summability at `1-r/8`. -/
theorem absolute_prime_summable_of_residue_disk {x : GaugeTorus} {r : ℝ}
    (hr : 0 < r) (hr₂ : r ≤ 1 / 2) {U : ℂ → ℂ}
    (hU : AnalyticOnNhd ℂ U (ball 1 r))
    (hUne : ∀ t : ℝ, (t : ℂ) ∈ ball 1 r → U (t : ℂ) ≠ 0)
    (hagree : ∀ s ∈ ball (1 : ℂ) r, 1 < s.re → U s = (s - 1) * gaugeFibre x s) :
    Summable (fun p : Nat.Primes => ‖twist x p - 1‖ * (p : ℝ) ^ (-(1 - r / 8))) := by
  have he := quadratic_prime_summable_of_residue_disk hr hr₂ hU hUne hagree
    (σ := 1 - r / 2) (by linarith only [hr])
  have ha := summable_absolute_prime_of_energy (δ := r / 2) (by linarith only [hr]) he
  have hdiv : 1 - r / 2 / 4 = 1 - r / 8 := by ring
  simpa only [abs_norm, hdiv] using ha

#print axioms summable_of_pole_disk_identity
#print axioms absolute_prime_summable_of_residue_disk

/-- A jointly holomorphic nonzero pole germ supplies one residue disk for every nearby slice. -/
private theorem exists_common_residue_disk {x : ℝ → GaugeTorus} {U : ℂ × ℂ → ℂ}
    {R : ℝ} (hR : 0 < R) (hU : AnalyticAt ℂ U (0, 1)) (hUne : U (0, 1) ≠ 0)
    (hagree : ∀ t : ℝ, |t| < R → ∀ s ∈ ball (1 : ℂ) R, 1 < s.re →
      U ((t : ℂ), s) = (s - 1) * gaugeFibre (x t) s) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 2 ∧ ∀ t : ℝ, |t| < r →
      AnalyticOnNhd ℂ (fun s => U ((t : ℂ), s)) (ball 1 r) ∧
      (∀ τ : ℝ, (τ : ℂ) ∈ ball 1 r → U ((t : ℂ), (τ : ℂ)) ≠ 0) ∧
      ∀ s ∈ ball (1 : ℂ) r, 1 < s.re →
        U ((t : ℂ), s) = (s - 1) * gaugeFibre (x t) s := by
  obtain ⟨ρ, hρ, hb⟩ := Metric.mem_nhds_iff.mp
    (hU.eventually_analyticAt.and (hU.continuousAt.eventually_ne hUne))
  let r : ℝ := min (ρ / 2) (min (R / 2) (1 / 4))
  have hr : 0 < r := lt_min (by linarith only [hρ])
    (lt_min (by linarith only [hR]) (by norm_num))
  have hrρ : r ≤ ρ / 2 := min_le_left _ _
  have hrR : r ≤ R / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hrq : r ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hrrρ : r < ρ := by linarith only [hrρ, hρ]
  have hrrR : r < R := by linarith only [hrR, hR]
  have hprod (t : ℝ) (ht : |t| < r) (s : ℂ) (hs : s ∈ ball 1 r) :
      ((t : ℂ), s) ∈ ball ((0 : ℂ), (1 : ℂ)) ρ := by
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · simpa only [dist_zero_right, Complex.norm_real, Real.norm_eq_abs] using ht.trans hrrρ
    · exact (mem_ball.mp hs).trans hrrρ
  refine ⟨r, hr, by linarith only [hrq], ?_⟩
  intro t ht
  refine ⟨?_, fun τ hτ => (hb (hprod t ht (τ : ℂ) hτ)).2, ?_⟩
  · intro s hs
    exact (hb (hprod t ht s hs)).1.comp
      (f := fun z : ℂ => ((t : ℂ), z)) (analyticAt_const.prod analyticAt_id)
  · intro s hs hse
    exact hagree t (ht.trans hrrR) s (ball_subset_ball hrrR.le hs) hse

/-- Joint pole regularity forces a single absolute prime-summability exponent for all nearby fibres. -/
theorem joint_pole_common_absolute_summability {x : ℝ → GaugeTorus} {U : ℂ × ℂ → ℂ}
    {R : ℝ} (hR : 0 < R) (hU : AnalyticAt ℂ U (0, 1)) (hUne : U (0, 1) ≠ 0)
    (hagree : ∀ t : ℝ, |t| < R → ∀ s ∈ ball (1 : ℂ) R, 1 < s.re →
      U ((t : ℂ), s) = (s - 1) * gaugeFibre (x t) s) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 2 ∧ ∀ t : ℝ, |t| < r →
      Summable (fun p : Nat.Primes => ‖twist (x t) p - 1‖ * (p : ℝ) ^ (-(1 - r / 8))) := by
  obtain ⟨r, hr, hr₂, hd⟩ := exists_common_residue_disk hR hU hUne hagree
  refine ⟨r, hr, hr₂, ?_⟩
  intro t ht
  obtain ⟨hUt, hUnt, hEt⟩ := hd t ht
  exact absolute_prime_summable_of_residue_disk hr hr₂ hUt hUnt hEt

/-- Every nearby real fibre extends its given pole germ to one common isozeric half-plane. -/
theorem joint_pole_common_isozeric_halfPlane {x : ℝ → GaugeTorus} {U : ℂ × ℂ → ℂ}
    {R : ℝ} (hR : 0 < R) (hU : AnalyticAt ℂ U (0, 1)) (hUne : U (0, 1) ≠ 0)
    (hagree : ∀ t : ℝ, |t| < R → ∀ s ∈ ball (1 : ℂ) R, 1 < s.re →
      U ((t : ℂ), s) = (s - 1) * gaugeFibre (x t) s) :
    ∃ ε σ : ℝ, 0 < ε ∧ 1 / 2 < σ ∧ σ < 1 ∧ ∀ t : ℝ, |t| < ε →
      Summable (fun p : Nat.Primes => ‖twist (x t) p - 1‖ * (p : ℝ) ^ (-σ)) ∧
      AnalyticOnNhd ℂ (deformationExponent (x t)) {s : ℂ | σ < s.re} ∧
      ((fun s => U ((t : ℂ), s)) =ᶠ[𝓝 (1 : ℂ)]
        (fun s => zetaResidueFactor s * cexp (deformationExponent (x t) s))) ∧
      (∀ s : ℂ, 1 < s.re → gaugeFibre (x t) s = riemannZeta s * cexp (deformationExponent (x t) s)) ∧
      ∀ s : ℂ, σ < s.re → s ≠ 1 →
        analyticOrderAt (fun z => riemannZeta z * cexp (deformationExponent (x t) z)) s =
          analyticOrderAt riemannZeta s := by
  obtain ⟨r, hr, hr₂, hd⟩ := exists_common_residue_disk hR hU hUne hagree
  have hσ₀ : 1 / 2 < 1 - r / 8 := by linarith only [hr₂]
  have hσ₁ : 1 - r / 8 < 1 := by linarith only [hr]
  refine ⟨r, 1 - r / 8, hr, hσ₀, hσ₁, ?_⟩
  intro t ht
  obtain ⟨hUt, hUnt, hEt⟩ := hd t ht
  have hs := absolute_prime_summable_of_residue_disk hr hr₂ hUt hUnt hEt
  obtain ⟨hH, hE⟩ := exists_isozeric hσ₀.le hs
  have hev : ∀ᶠ s in 𝓝 (1 : ℂ), 1 < s.re →
      U ((t : ℂ), s) = (s - 1) * gaugeFibre (x t) s := by
    filter_upwards [ball_mem_nhds (1 : ℂ) hr] with s hs
    exact hEt s hs
  obtain ⟨_, _, _, _, _, hgerm, _, _⟩ := local_residue_isozeric_continuation
    (hUt 1 (mem_ball_self hr)) (hUnt 1 (mem_ball_self hr)) hev
  exact ⟨hs, hH, hgerm, hE, fun s hsre hs1 => analyticOrderAt_isozeric hσ₀.le hs hsre hs1⟩

#print axioms joint_pole_common_absolute_summability
#print axioms joint_pole_common_isozeric_halfPlane

end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
