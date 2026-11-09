import GaloisForLFunctions.SurfaceOfSpecZ.TheWidthIsTheStepanovExponentAtThePrimes
import GaloisForLFunctions.SurfaceOfSpecZ.TheOtherSideSeesEveryZero

/-!
# The other side at the primes

`TheWidthIsTheStepanovExponentAtThePrimes` reads the zero width off a lower bound on the traces at the
primes. An upper bound works the same way.

* `zetaZeroWidth_le_iff_bddAbove_primeDegrees`: for `0 ≤ a < ½`, the width is `≤ a` iff
  `2 Re S(log p) ≤ K p^a` at every prime; `riemannHypothesis_iff_bddAbove_primeDegrees` is `a = 0`.
* `riemannHypothesis_iff_weil_oddPrimeTwoBumps`: RH iff `Re W(B − τ_{log p}B, B − τ_{log p}B) ≥ 0` at
  every prime, since this value is `2 Re S(0) − 2 Re S(log p)` (`re_W_oddPrimeTwoBump_eq`);
  `zetaZeroWidth_le_iff_weil_oddPrimeTwoBumps` reads the width.

So either side of Hasse–Weil at the prime degrees decides RH, and Weil positivity on either family
of prime two-bumps `B ± τ_{log p}B` is RH. The proof is that of the lower side with the opposite sign:
the gap method from above uses the odd two-bump criterion (`re_le_of_bddAbove_exp_of_powGaps`), which
sees real zeros as well (`TheOtherSideSeesEveryZero`); the von Mangoldt series of
`K + 1 − 2 Re S(log q) q^{−a}` is `Σ_z e_z ζ'/ζ(s + a − z) − (K + 1)ζ'/ζ(s)`, with the same poles
(`forall_re_le_of_gdSeries_eq_signedWidthZeta`).
-/

open Complex Set Filter Topology Metric
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
open GaloisForLFunctions.HTGeometry ArithmeticFunction

/-- `ε Σ_z e_z ζ'/ζ(s + a − z) − (K + 1) ζ'/ζ(s)`; `ε = −1` is `widthZeta`. -/
def signedWidthZeta (ε : ℂ) (a K : ℝ) (s : ℂ) : ℂ :=
  ε * shiftLogDerivOf a (traceCoeff 3) s - ((K + 1 : ℝ) : ℂ) * logDeriv riemannZeta s

/-- The signed continuation is holomorphic on a ball around every non-pole `s₀`,
`1 < Re s₀ < 2 − a − b`. -/
theorem exists_ball_differentiableOn_signedWidthZeta {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hδ : 2 * b < 1 / 2 + a) (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + b) (ε : ℂ) (K : ℝ)
    {s₀ : ℂ} (hs1 : 1 < s₀.re) (hs2 : s₀.re < 2 - a - b)
    (hpole : ∀ z, traceCoeff 3 z ≠ 0 → s₀ ≠ 1 - a + z) :
    ∃ ρ : ℝ, 0 < ρ ∧ DifferentiableOn ℂ (signedWidthZeta ε a K) (ball s₀ ρ) := by
  classical
  set P : Set ℂ := {z | traceCoeff 3 z ≠ 0 ∧ |z.im - s₀.im| ≤ 1} with hPdef
  have hP : P.Finite := by
    refine (finite_traceCoeff_height 3 (|s₀.im| + 1)).subset fun z hz => ?_
    obtain ⟨hz0, hzim⟩ := hz
    refine ⟨hz0, ?_⟩
    have := abs_le.mp hzim
    rw [abs_le]; constructor <;> linarith [neg_abs_le s₀.im, le_abs_self s₀.im]
  obtain ⟨δ, hδ0, hδ1, hδP⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ z ∈ P, δ ≤ ‖s₀ - (1 - a + z)‖ := by
    rcases P.eq_empty_or_nonempty with hPe | hPne
    · exact ⟨1, one_pos, le_rfl, by simp [hPe]⟩
    · obtain ⟨z₁, hz₁, hmin⟩ := hP.toFinset.exists_min_image (fun z => ‖s₀ - (1 - a + z)‖)
        (by simpa using hPne)
      have hz₁' := hP.mem_toFinset.mp hz₁
      refine ⟨min 1 ‖s₀ - (1 - a + z₁)‖,
        lt_min one_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hpole z₁ hz₁'.1))),
        min_le_left _ _, fun z hz => (min_le_right _ _).trans (hmin z (hP.mem_toFinset.mpr hz))⟩
  set ρ := min δ (min (s₀.re - 1) (2 - a - b - s₀.re)) / 2 with hρdef
  have hρ0 : 0 < ρ := by
    rw [hρdef]; exact half_pos (lt_min hδ0 (lt_min (by linarith) (by linarith)))
  have hρδ : ρ < δ := by
    rw [hρdef]; have := min_le_left δ (min (s₀.re - 1) (2 - a - b - s₀.re)); linarith
  have hρ1 : ρ < s₀.re - 1 := by
    rw [hρdef]
    have := (min_le_right δ (min (s₀.re - 1) (2 - a - b - s₀.re))).trans (min_le_left _ _)
    linarith
  have hρ2 : ρ < 2 - a - b - s₀.re := by
    rw [hρdef]
    have := (min_le_right δ (min (s₀.re - 1) (2 - a - b - s₀.re))).trans (min_le_right _ _)
    linarith
  refine ⟨ρ, hρ0, fun s hs => ?_⟩
  rw [mem_ball, dist_eq_norm] at hs
  have hre : |s.re - s₀.re| < ρ :=
    lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (s - s₀)) hs
  have him : |s.im - s₀.im| < ρ :=
    lt_of_le_of_lt (by simpa using Complex.abs_im_le_norm (s - s₀)) hs
  have hs1' : 1 < s.re := by linarith [(abs_lt.mp hre).1]
  have hs2' : s.re < 2 - a - b := by linarith [(abs_lt.mp hre).2]
  have hnp : ∀ z, traceCoeff 3 z ≠ 0 → s ≠ 1 - a + z := by
    intro z hz h
    have hzim : s.im = z.im := by have := congrArg Complex.im h; simp at this; linarith
    have hzP : z ∈ P := ⟨hz, by rw [← hzim]; linarith [abs_lt.mp him, hδ1, hρδ]⟩
    have h1 := hδP z hzP
    rw [← h, norm_sub_rev] at h1
    linarith
  have h1 := differentiableAt_shiftLogDerivOf ha0 hab hδ hzf (c := traceCoeff 3) (fun _ => le_rfl)
    hs1' hs2' hnp
  have hs1ne : s ≠ 1 := fun h => by rw [h] at hs1'; simp at hs1'
  have h2 := differentiableAt_logDeriv_riemannZeta hs1ne
    (riemannZeta_ne_zero_of_one_le_re hs1'.le)
  exact ((h1.const_mul ε).sub (h2.const_mul _)).differentiableWithinAt


/-- **The signed Landau argument.** Let every zero have `Re ρ ≤ ½ + b`, `0 ≤ a ≤ b`, `2b < ½ + a`,
and `|ε| = 1`. Let `B ≥ 0`, `Σ B_j/(j + 1) = ∞`, convergent right of `1 + b − a`, have Dirichlet series
`ε Σ_z e_z ζ'/ζ(s + a − z) − (K + 1)ζ'/ζ(s) − N(s)` there, with `N` holomorphic on
`Re s > ¾ + (b − a)/2`. Then every zero has `Re ρ ≤ ½ + a`. -/
theorem forall_re_le_of_gdSeries_eq_signedWidthZeta {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hδ : 2 * b < 1 / 2 + a) (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + b)
    {B : ℕ → ℝ} (hB : ∀ j, 0 ≤ B j)
    (hdiv1 : ¬ Summable fun j : ℕ => B j * ((j : ℝ) + 1) ^ (-1 : ℝ))
    (hconv : ∀ σ : ℝ, 1 + (b - a) < σ → Summable fun j : ℕ => B j * ((j : ℝ) + 1) ^ (-σ))
    {N : ℂ → ℂ} (hN : DifferentiableOn ℂ N {s | 3 / 4 + (b - a) / 2 < s.re}) {ε : ℂ} (hε : ‖ε‖ = 1)
    (K : ℝ)
    (heq : ∀ s : ℂ, 1 + (b - a) < s.re → gdSeries B powerFreq s = signedWidthZeta ε a K s - N s) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + a := by
  classical
  intro ρ₁ hρ₁
  by_contra hρ₁re
  push Not at hρ₁re
  have hb1 : b < 1 / 2 := by linarith
  have hw : ∀ z, traceCoeff 3 z ≠ 0 → |z.re| ≤ b := fun z hz =>
    abs_re_le_of_traceCoeff_ne_zero_of_re_le hzf hz
  set U : ℝ := 2 - a - b with hU
  set A₀ : ℝ := 1 + (b - a) with hA₀
  have hA₀U : A₀ < U := by rw [hA₀, hU]; linarith
  have hr₀ : 3 / 4 + (b - a) / 2 < 1 := by linarith
  have hlam : ∀ j, 0 ≤ powerFreq j := powerFreq_nonneg
  have htw : ∀ σ j, gdTwistTerm B powerFreq σ 0 j = B j * ((j : ℝ) + 1) ^ (-σ) := by
    intro σ j; rw [gdTwistTerm, pow_zero, mul_one, real_exp_neg_mul_powerFreq]
  have hsumHigh : ∀ σ : ℝ, A₀ < σ → Summable (gdTwistTerm B powerFreq σ 0) := fun σ hσ =>
    (hconv σ hσ).congr fun j => (htw σ j).symm
  have hdivLow : ∀ σ : ℝ, σ ≤ 1 → ¬ Summable (gdTwistTerm B powerFreq σ 0) := by
    intro σ hσ hs
    apply hdiv1
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (hB j) (by positivity)) (fun j => ?_) hs
    rw [htw]
    have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hj1 (by linarith)) (hB j)
  -- the abscissa
  set S : Set ℝ := {σ | Summable (gdTwistTerm B powerFreq σ 0)} with hSdef
  set S2 : ℝ := (A₀ + U) / 2 with hS2def
  have hS2 : S2 ∈ S := hsumHigh _ (by rw [hS2def]; linarith)
  have hSne : S.Nonempty := ⟨_, hS2⟩
  have hSbdd : BddBelow S := ⟨1, fun σ hσ => by
    by_contra h; exact hdivLow σ (le_of_lt (not_le.mp h)) hσ⟩
  set σc := sInf S with hσcdef
  have hsum : ∀ σ, σc < σ → Summable (gdTwistTerm B powerFreq σ 0) := by
    intro σ hσ
    obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hSne hσ
    exact summable_gdTwistTerm_of_le hB hlam hσ'S hlt.le
  have hdiv : ∀ σ, σ < σc → ¬ Summable (gdTwistTerm B powerFreq σ 0) := fun σ hσ hs =>
    absurd (csInf_le hSbdd hs) (not_le.mpr hσ)
  have hσc2 : σc ≤ S2 := csInf_le hSbdd hS2
  -- analyticity
  have hgdAn : ∀ s : ℂ, σc < s.re → AnalyticAt ℂ (gdSeries B powerFreq) s := by
    intro s hs
    have hopen : IsOpen {w : ℂ | σc < w.re} := isOpen_lt continuous_const Complex.continuous_re
    refine DifferentiableOn.analyticAt (s := {w : ℂ | σc < w.re}) (fun w hw => ?_)
      (hopen.mem_nhds hs)
    have hw' : σc < w.re := hw
    exact (RHTower.differentiableAt_gdSeries hB hlam (hsum ((σc + w.re) / 2) (by linarith))
      (by linarith)).differentiableWithinAt
  have hNAn : ∀ s : ℂ, 3 / 4 + (b - a) / 2 < s.re → AnalyticAt ℂ N s := fun s hs =>
    hN.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  set G : ℂ → ℂ := fun s => signedWidthZeta ε a K s - N s with hGdef
  have hGball : ∀ s₀ : ℂ, 1 < s₀.re → s₀.re < U →
      (∀ z, traceCoeff 3 z ≠ 0 → s₀ ≠ 1 - a + z) →
        ∃ ρ : ℝ, 0 < ρ ∧ DifferentiableOn ℂ G (ball s₀ ρ) := by
    intro s₀ h1 h2 hp
    obtain ⟨ρ, hρ, hd⟩ := exists_ball_differentiableOn_signedWidthZeta ha0 hab hδ hzf ε K h1 h2 hp
    refine ⟨min ρ (s₀.re - 1), lt_min hρ (by linarith), ?_⟩
    refine (hd.mono (ball_subset_ball (min_le_left _ _))).sub (hN.mono fun s hs => ?_)
    rw [mem_ball, dist_eq_norm] at hs
    have hre : |s.re - s₀.re| < s₀.re - 1 :=
      lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (s - s₀))
        (hs.trans_le (min_le_right _ _))
    show 3 / 4 + (b - a) / 2 < s.re
    linarith [(abs_lt.mp hre).1]
  have hGAn : ∀ s : ℂ, 1 < s.re → s.re < U →
      (∀ z, traceCoeff 3 z ≠ 0 → s ≠ 1 - a + z) → AnalyticAt ℂ G s := by
    intro s h1 h2 hp
    obtain ⟨ρ, hρ, hd⟩ := hGball s h1 h2 hp
    exact hd.analyticAt (ball_mem_nhds s hρ)
  have hrealNoPole : ∀ t : ℝ, ∀ z, traceCoeff 3 z ≠ 0 → (t : ℂ) ≠ 1 - a + z := by
    intro t z hz h
    have him := congrArg Complex.im h
    simp only [Complex.ofReal_im, Complex.add_im, Complex.sub_im, Complex.one_im, zero_sub,
      neg_zero, zero_add] at him
    exact traceCoeff_im_ne_zero hz him.symm
  have hagreeHigh : ∀ s : ℂ, A₀ < s.re → gdSeries B powerFreq s = G s := heq
  -- Landau: the abscissa is at most `1`
  have hσc : σc ≤ 1 := by
    by_contra hgt
    push Not at hgt
    have h2 : σc < U := by linarith
    obtain ⟨ρ, hρ, hG⟩ := hGball (σc : ℂ) (by simpa using hgt) (by simpa using h2)
      (fun z hz => hrealNoPole σc z hz)
    have hreal : ∀ t ∈ Ioo σc U,
        gdSeries B powerFreq ((0 : ℂ) + t) = G ((0 : ℂ) + t) := by
      refine eqOn_ray_of_eventually (a := σc) (c := (S2 + U) / 2) (b := U)
        (by linarith) (by linarith) (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
      · rw [zero_add]; exact hgdAn _ (by simpa using ht.1)
      · rw [zero_add]
        exact hGAn _ (by simpa using hgt.trans ht.1) (by simpa using ht.2)
          (fun z hz => hrealNoPole t z hz)
      · rw [zero_add]; exact hagreeHigh _ (by simp; linarith [ht.1])
    have hhalf := eqOn_halfBall (f := G) (g := gdSeries B powerFreq) hρ
      (fun s hs _ => hG.analyticAt (isOpen_ball.mem_nhds hs))
      (fun s _ hs => hgdAn s hs)
      (fun t ht1 _ => by
        rcases lt_or_ge t U with htb | htb
        · have := hreal t ⟨ht1, htb⟩; rw [zero_add] at this; exact this.symm
        · exact (hagreeHigh _ (by simp; linarith)).symm)
    exact RHTower.gdSeries_no_continuation_at_abscissa hB hlam hsum hdiv hρ hG
      (fun s hs hre => hhalf s hs hre)
  -- the zero right of `½ + a`, rightmost on its line
  set z₁ := ρ₁ - 1 / 2 with hz₁def
  have hz₁ : traceCoeff 3 z₁ ≠ 0 := traceCoeff_sees (le_refl 3) hρ₁ (by linarith)
  set Lset := (finite_evenCoeff_line zetaZeroConfig (boxSpline 1 3) z₁.im).toFinset with hLset
  obtain ⟨z₀, hz₀L, hmax⟩ := Lset.exists_max_image Complex.re
    ⟨z₁, (Set.Finite.mem_toFinset _).mpr ⟨hz₁, rfl⟩⟩
  obtain ⟨hz₀, him₀⟩ := (Set.Finite.mem_toFinset _).mp hz₀L
  have hre₀ : z₁.re ≤ z₀.re := hmax z₁ ((Set.Finite.mem_toFinset _).mpr ⟨hz₁, rfl⟩)
  have hz₁re : a < z₁.re := by simp [hz₁def]; linarith
  have hz₀re : z₀.re ≤ b := (abs_le.mp (hw z₀ hz₀)).2
  set s₀ : ℂ := 1 - a + z₀ with hs₀def
  have hs₀re : s₀.re = 1 - a + z₀.re := by simp [hs₀def]
  have hs₀1 : 1 < s₀.re := by rw [hs₀re]; linarith
  have hs₀2 : s₀.re ≤ A₀ := by rw [hs₀re, hA₀]; linarith
  set T : ℝ := U - s₀.re with hTdef
  have hT : 0 < T := by rw [hTdef]; linarith
  have hqre : ∀ t : ℝ, (s₀ + t).re = s₀.re + t := fun t => by simp
  have hray : ∀ t : ℝ, 0 < t → ∀ z, traceCoeff 3 z ≠ 0 → s₀ + t ≠ 1 - a + z := by
    intro t ht z hz h
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp [hs₀def] at him hre
    have hle := hmax z ((Set.Finite.mem_toFinset _).mpr ⟨hz, him.symm.trans him₀⟩)
    linarith
  have hGray : ∀ t ∈ Ioo 0 T, AnalyticAt ℂ G (s₀ + t) := fun t ht =>
    hGAn _ (by rw [hqre]; linarith [ht.1]) (by rw [hqre]; linarith [ht.2]) (hray t ht.1)
  have hgdray : ∀ t ∈ Ioo 0 T, AnalyticAt ℂ (gdSeries B powerFreq) (s₀ + t) := fun t ht =>
    hgdAn _ (by rw [hqre]; linarith [ht.1])
  have hagreeRay : ∀ t ∈ Ioo 0 T, gdSeries B powerFreq (s₀ + t) = G (s₀ + t) :=
    eqOn_ray_of_eventually (c := (A₀ - s₀.re + T) / 2) (by linarith) (by linarith)
      hgdray hGray (fun t ht => hagreeHigh _ (by rw [hqre]; linarith [ht.1]))
  -- split off the pole
  set c' : ℂ → ℂ := fun z => if z = z₀ then 0 else traceCoeff 3 z with hc'def
  have hc' : ∀ z, ‖c' z‖ ≤ ‖traceCoeff 3 z‖ := fun z => by
    simp only [hc'def]; split_ifs <;> simp
  set R : ℂ → ℂ := fun s => ε * shiftLogDerivOf a c' s -
    ((K + 1 : ℝ) : ℂ) * logDeriv riemannZeta s - N s with hRdef
  have hsplit : ∀ t ∈ Ioo 0 T,
      G (s₀ + t) = ε * (traceCoeff 3 z₀ * logDeriv riemannZeta (1 + t)) + R (s₀ + t) := by
    intro t ht
    have hsm := summable_shiftLogDerivOf_terms ha0 hab hδ hzf (c := traceCoeff 3)
      (fun _ => le_rfl) (s := s₀ + t) (by rw [hqre]; linarith [ht.1])
      (by rw [hqre]; linarith [ht.2])
    simp only [hGdef, hRdef]
    unfold signedWidthZeta shiftLogDerivOf
    rw [hsm.tsum_eq_add_tsum_ite z₀]
    have h1 : (s₀ + t) + a - z₀ = 1 + t := by rw [hs₀def]; ring
    have h2 : ∑' z, (if z = z₀ then 0 else
          traceCoeff 3 z * logDeriv riemannZeta (s₀ + t + a - z)) =
        ∑' z, c' z * logDeriv riemannZeta (s₀ + t + a - z) :=
      tsum_congr fun z => by simp only [hc'def]; split_ifs <;> simp
    rw [h1, h2]
    ring
  have hs₀ne : s₀ ≠ 1 := fun h => by rw [h] at hs₀1; simp at hs₀1
  have hRcont : ContinuousAt R s₀ := by
    have hp : ∀ z, c' z ≠ 0 → s₀ ≠ 1 - a + z := by
      intro z hz h
      have hzz : z ≠ z₀ := fun e => hz (by simp [hc'def, e])
      exact hzz (by rw [hs₀def] at h; linear_combination -h)
    have h1 := differentiableAt_shiftLogDerivOf ha0 hab hδ hzf hc' hs₀1 (by linarith) hp
    have h2 := differentiableAt_logDeriv_riemannZeta hs₀ne
      (riemannZeta_ne_zero_of_one_le_re hs₀1.le)
    exact (((h1.const_mul ε).sub (h2.const_mul _)).continuousAt).sub
      (hNAn s₀ (by linarith)).continuousAt
  have hgdcont : ContinuousAt (gdSeries B powerFreq) s₀ := (hgdAn s₀ (by linarith)).continuousAt
  set H : ℂ → ℂ := fun s => gdSeries B powerFreq s - R s with hHdef
  have hHcont : ContinuousAt H s₀ := hgdcont.sub hRcont
  have hHray : ∀ t ∈ Ioo 0 T, H (s₀ + t) = ε * (traceCoeff 3 z₀ * logDeriv riemannZeta (1 + t)) := by
    intro t ht
    simp only [hHdef]
    rw [hagreeRay t ht, hsplit t ht]
    ring
  -- the pole of `ζ'/ζ` at `1` against continuity
  obtain ⟨δ₁, hδ₁, hδ₁H⟩ := Metric.continuousAt_iff.mp hHcont 1 one_pos
  set A := ‖traceCoeff 3 z₀‖ with hAdef
  have hA : 0 < A := norm_pos_iff.mpr hz₀
  obtain ⟨t, ht0, htδ, htB⟩ := exists_norm_logDeriv_zeta_one_add_gt ((‖H s₀‖ + 1) / A)
    (lt_min hδ₁ hT)
  have htδ₁ : t < δ₁ := htδ.trans_le (min_le_left _ _)
  have htT : t < T := htδ.trans_le (min_le_right _ _)
  have h1 := hHray t ⟨ht0, htT⟩
  have h2 : dist (H (s₀ + t)) (H s₀) < 1 := hδ₁H (by
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    exact htδ₁)
  have h4 : ‖H s₀‖ + 1 < ‖H (s₀ + t)‖ := by
    rw [h1, norm_mul, hε, one_mul, norm_mul]
    rw [div_lt_iff₀ hA] at htB
    linarith
  have h5 : ‖H (s₀ + t)‖ < ‖H s₀‖ + 1 := by
    have := norm_sub_norm_le (H (s₀ + t)) (H s₀)
    rw [dist_eq_norm] at h2
    linarith
  linarith


/-! ### The gap method from above -/

/-- **The gap method from above.** An upper bound `K d^a` at degrees with gaps `x^θ` puts every
zero in `Re ρ ≤ ½ + max(a, θ − ½)`, through the odd two-bump criterion. -/
theorem re_le_of_bddAbove_exp_of_powGaps {θ a : ℝ} (hθ1 : θ < 1) (ha0 : 0 ≤ a) {D : Set ℕ}
    (hD : PowGaps θ D) {K : ℝ}
    (hK : ∀ d ∈ D, zetaScalingDatum.orbitCorr splineCycle (Real.log d) ≤ K * (d : ℝ) ^ a) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + max a (θ - 1 / 2) := by
  obtain ⟨C, T, hC0, hT0, hCT⟩ := exists_orbitCorr_sub_powGap_le' hθ1 hD
  set b := max a (θ - 1 / 2) with hb
  have hb0 : 0 ≤ b := le_max_of_le_left ha0
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (continuous_zetaOrbitCorr' splineCycle).continuousOn
  set c0 := zetaScalingDatum.orbitCorr splineCycle 0 with hc0
  have hrate : ∃ C' V : ℝ, ∀ v : ℝ, V ≤ v → -(C' * Real.exp (b * v)) ≤
      (zetaZeroConfig.W (twoBump (boxSpline 1 3) v (-1)) (twoBump (boxSpline 1 3) v (-1))).re := by
    refine ⟨2 * (|K| + C + |B| + |c0|), 0, fun v hv => ?_⟩
    rw [re_W_lag_eq zetaZeroConfig SquareRootThreshold.temperedConfig_zetaZeroConfig
      (contDiff_boxSpline one_pos 2) (boxSpline_support one_pos 3) v,
      ← orbitCorr_eq_re_lagStructure_spline, ← orbitCorr_eq_re_lagStructure_spline, ← hc0]
    have he1 : 1 ≤ Real.exp (b * v) := Real.one_le_exp (mul_nonneg hb0 hv)
    have hE0 : 0 ≤ Real.exp (b * v) := (Real.exp_pos _).le
    have hea : Real.exp (a * v) ≤ Real.exp (b * v) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) hv)
    have heθ : Real.exp ((θ - 1 / 2) * v) ≤ Real.exp (b * v) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hv)
    have hup : zetaScalingDatum.orbitCorr splineCycle v ≤ (|K| + C + |B|) * Real.exp (b * v) := by
      rcases le_total v T with hvT | hTv
      · have h := hB v ⟨hv, hvT⟩
        rw [Real.norm_eq_abs] at h
        have h1 := (abs_le.mp (h.trans (le_abs_self B))).2
        have h2 := mul_le_mul_of_nonneg_left he1 (by positivity : (0 : ℝ) ≤ |K| + C + |B|)
        linarith [abs_nonneg K]
      · obtain ⟨d, hdD, hdle, hd⟩ := hCT v hTv
        have h1 := hK d hdD
        have h2 := (abs_le.mp hd).2
        have hd0 : (0 : ℝ) < d := by exact_mod_cast hD.1 d hdD
        have hda : (d : ℝ) ^ a ≤ Real.exp (a * v) := by
          calc (d : ℝ) ^ a ≤ (Real.exp v) ^ a := Real.rpow_le_rpow hd0.le hdle ha0
            _ = Real.exp (a * v) := by rw [← Real.exp_mul, mul_comm]
        have hdpos : 0 ≤ (d : ℝ) ^ a := Real.rpow_nonneg hd0.le a
        have h3 : K * (d : ℝ) ^ a ≤ |K| * Real.exp (b * v) :=
          (mul_le_mul_of_nonneg_right (le_abs_self K) hdpos).trans
            (mul_le_mul_of_nonneg_left (hda.trans hea) (abs_nonneg K))
        have h5 : C * Real.exp ((θ - 1 / 2) * v) ≤ C * Real.exp (b * v) :=
          mul_le_mul_of_nonneg_left heθ hC0
        have h6 := mul_nonneg (abs_nonneg B) hE0
        linarith
    have h7 := mul_le_mul_of_nonneg_left he1 (abs_nonneg c0)
    linarith [neg_abs_le c0]
  exact (re_le_iff_lag_twoBump_ge_neg_exp_of_pos zetaZeroConfig
    SquareRootThreshold.temperedConfig_zetaZeroConfig (fun ρ hρ => hρ.2.2)
    (contDiff_boxSpline one_pos 2) (boxSpline_support one_pos 3)
    (fun x hx hxre him => evenCoeff_spline_pos_of_real zetaZeroConfig hx hxre him)
    (fun ρ hρ h => evenCoeff_spline_sees hρ h) hb0).mpr hrate

/-! ### The theorems -/

/-- **The width is the exponent of the other side at the primes.** For `0 ≤ a < ½`, every zero lies
within `a` of the critical line iff `2 Re S(log p) ≤ K p^a` at every prime `p`. -/
theorem zetaZeroWidth_le_iff_bddAbove_primeDegrees {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    zetaZeroWidth ≤ a ↔ ∃ K : ℝ, ∀ p : ℕ, p.Prime →
      2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re ≤ K * (p : ℝ) ^ a := by
  rw [zetaZeroWidth_le_iff_re_le ha0]
  constructor
  · intro hzf
    have hw : ∀ z, traceCoeff 3 z ≠ 0 → |z.re| ≤ a := fun z hz =>
      abs_re_le_of_traceCoeff_ne_zero_of_re_le hzf hz
    refine ⟨∑' z : ℂ, ‖traceCoeff 3 z‖, fun p hp => ?_⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have habs := abs_two_re_lagStructure_le_of_width hw
      (Real.log_nonneg (by exact_mod_cast hp.one_lt.le : (1 : ℝ) ≤ p))
    have hexp : Real.exp (a * Real.log p) = (p : ℝ) ^ a := by
      rw [Real.rpow_def_of_pos hp0]; ring_nf
    rw [hexp] at habs
    linarith [(abs_le.mp habs).2]
  · rintro ⟨K, hK⟩
    set b := max a (1 / 8) with hbdef
    have hab : a ≤ b := le_max_left _ _
    have hδ : 2 * b < 1 / 2 + a := by
      rcases le_total a (1 / 8) with h | h
      · rw [hbdef, max_eq_right h]; linarith
      · rw [hbdef, max_eq_left h]; linarith
    have hb1 : b < 1 / 2 := by linarith
    -- step 1: the zeros lie in `Re ρ ≤ ½ + b`
    have hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + b := by
      have h := re_le_of_bddAbove_exp_of_powGaps (θ := 5 / 8) (by norm_num) ha0
        (powGaps_primes (by norm_num) (by norm_num)) (K := K / 2) fun p hp => by
          have := hK p hp
          rw [orbitCorr_eq_re_lagStructure_spline]; linarith
      intro ρ hρ
      have := h ρ hρ
      rw [show (5 / 8 : ℝ) - 1 / 2 = 1 / 8 by norm_num] at this
      exact this
    have hw : ∀ z, traceCoeff 3 z ≠ 0 → |z.re| ≤ b := fun z hz =>
      abs_re_le_of_traceCoeff_ne_zero_of_re_le hzf hz
    set E := ∑' z : ℂ, ‖traceCoeff 3 z‖ with hE
    -- step 2: the series of `K + 1 − 2 Re S(log p) p^{−a}` at the primes
    have hinner : ∀ j : ℕ, (j + 1).Prime → 1 ≤
        -(2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log ((j : ℝ) + 1))).re *
          ((j : ℝ) + 1) ^ (-a) + (-K - 2) + 1) := by
      intro j hj
      have h1 := hK (j + 1) hj
      push_cast at h1
      have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have hpa : 0 < ((j : ℝ) + 1) ^ (-a) := by positivity
      have hprod : ((j : ℝ) + 1) ^ a * ((j : ℝ) + 1) ^ (-a) = 1 := by
        rw [← Real.rpow_add hj0]; simp
      have h2 : 2 * (lagStructure zetaZeroConfig (boxSpline 1 3)
          (Real.log ((j : ℝ) + 1))).re * ((j : ℝ) + 1) ^ (-a) ≤ K := by
        calc 2 * (lagStructure zetaZeroConfig (boxSpline 1 3)
              (Real.log ((j : ℝ) + 1))).re * ((j : ℝ) + 1) ^ (-a)
            ≤ K * ((j : ℝ) + 1) ^ a * ((j : ℝ) + 1) ^ (-a) := mul_le_mul_of_nonneg_right h1 hpa.le
          _ = K := by rw [mul_assoc, hprod, mul_one]
      linarith
    set Bc : ℕ → ℝ := fun j => -primeWidthCoeff a (-K - 2) j with hBc
    have hge : ∀ j, primeWeight j ≤ Bc j := by
      intro j
      simp only [hBc, primeWidthCoeff]
      by_cases hj : (j + 1).Prime
      · have h0 : 0 ≤ primeWeight j := primeWeight_nonneg j
        have := mul_le_mul_of_nonneg_left (hinner j hj) h0
        linarith
      · simp [primeWeight, hj]
    have hBn : ∀ j, 0 ≤ Bc j := fun j => (primeWeight_nonneg j).trans (hge j)
    have hbound : ∀ (w : ℕ → ℝ), (∀ j, 0 ≤ w j) → (∀ j, w j ≤ Λ (j + 1)) → ∀ j,
        |w j * (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log (j + 1))).re *
          ((j : ℝ) + 1) ^ (-a) + (-K - 2) + 1)| ≤
            (E + |-K - 2| + 1) * (Λ (j + 1) * ((j : ℝ) + 1) ^ (b - a)) := by
      intro w hw0 hwΛ j
      rw [abs_mul, abs_of_nonneg (hw0 j)]
      have h1 := abs_widthTrace_add_le hab hw (-K - 2) j
      calc w j * |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log ((j : ℝ) + 1))).re *
            ((j : ℝ) + 1) ^ (-a) + (-K - 2) + 1| ≤
            Λ (j + 1) * ((E + |-K - 2| + 1) * ((j : ℝ) + 1) ^ (b - a)) :=
            mul_le_mul (hwΛ j) h1 (abs_nonneg _) vonMangoldt_nonneg
        _ = _ := by ring
    have hbP : ∀ j, |Bc j| ≤ (E + |-K - 2| + 1) * (Λ (j + 1) * ((j : ℝ) + 1) ^ (b - a)) := by
      intro j; simp only [hBc, abs_neg]; exact hbound primeWeight primeWeight_nonneg primeWeight_le j
    have hbH : ∀ j, |higherWidthCoeff a (-K - 2) j| ≤
        (E + |-K - 2| + 1) * (Λ (j + 1) * ((j : ℝ) + 1) ^ (b - a)) :=
      hbound higherWeight higherWeight_nonneg higherWeight_le
    have hbA : ∀ j, |widthCoeff a (-K - 2) j| ≤
        (E + |-K - 2| + 1) * (Λ (j + 1) * ((j : ℝ) + 1) ^ (b - a)) :=
      hbound (fun j => Λ (j + 1)) (fun _ => vonMangoldt_nonneg) (fun _ => le_rfl)
    refine forall_re_le_of_gdSeries_eq_signedWidthZeta ha0 hab hδ hzf hBn ?_ ?_
      (N := fun s => -gdSeries (higherWidthCoeff a (-K - 2)) powerFreq s)
      (differentiableOn_gdSeries_higherWidthCoeff ha0 hab hb1 hzf (-K - 2)).neg
      (ε := 1) (by simp) K ?_
    · intro hs
      apply not_summable_primeWeight_div
      refine Summable.of_nonneg_of_le (fun j => mul_nonneg (primeWeight_nonneg j) (by positivity))
        (fun j => mul_le_mul_of_nonneg_right (hge j) (by positivity)) hs
    · intro σ hσ
      have h := summable_gdTerm_of_abs_le' hbP (s := (σ : ℂ)) (by simpa using hσ)
      refine h.norm.congr fun j => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hBn j),
        cexp_neg_mul_powerFreq, norm_natCast_add_one_cpow]
      simp
    · intro s hs
      have hA := summable_gdTerm_of_abs_le' hbA hs
      have hH := summable_gdTerm_of_abs_le' hbH hs
      have hfull := gdSeries_widthCoeff_eq hab hzf (-K - 2) hs
      unfold gdSeries at hfull ⊢
      have hterm : ∀ j : ℕ, ((Bc j : ℝ) : ℂ) * cexp (-(s * (powerFreq j : ℂ))) =
          -(((widthCoeff a (-K - 2) j : ℝ) : ℂ) * cexp (-(s * (powerFreq j : ℂ)))) +
            ((higherWidthCoeff a (-K - 2) j : ℝ) : ℂ) * cexp (-(s * (powerFreq j : ℂ))) := by
        intro j
        simp only [hBc]
        rw [← primeWidthCoeff_add_higherWidthCoeff a (-K - 2) j]
        push_cast
        ring
      rw [tsum_congr hterm, hA.neg.tsum_add hH, tsum_neg, hfull]
      unfold signedWidthZeta widthZeta
      push_cast
      ring

theorem riemannHypothesis_iff_zetaZeroWidth_le_zero : RiemannHypothesis ↔ zetaZeroWidth ≤ 0 := by
  rw [zetaZeroWidth_le_iff_re_le le_rfl]
  constructor
  · intro hRH ρ hρ
    have := riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH ρ hρ
    linarith
  · intro h
    exact riemannHypothesis_of_forall_re_le fun ρ hρ => by linarith [h ρ hρ]

/-- **The other side at the primes is RH.** -/
theorem riemannHypothesis_iff_bddAbove_primeDegrees :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ p : ℕ, p.Prime →
      2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re ≤ K := by
  rw [riemannHypothesis_iff_zetaZeroWidth_le_zero,
    zetaZeroWidth_le_iff_bddAbove_primeDegrees le_rfl (by norm_num)]
  simp only [Real.rpow_zero, mul_one]

/-- **The odd prime two-bump identity.** `Re W(B − τ_v B, B − τ_v B) = 2 Re S(0) − 2 Re S(v)`. -/
theorem re_W_oddPrimeTwoBump_eq (v : ℝ) :
    (zetaZeroConfig.W (twoBump (boxSpline 1 3) v (-1)) (twoBump (boxSpline 1 3) v (-1))).re =
      2 * (lagStructure zetaZeroConfig (boxSpline 1 3) 0).re -
        2 * (lagStructure zetaZeroConfig (boxSpline 1 3) v).re :=
  re_W_lag_eq zetaZeroConfig SquareRootThreshold.temperedConfig_zetaZeroConfig
    (contDiff_boxSpline one_pos 2) (boxSpline_support one_pos 3) v

/-- **Weil positivity at the odd prime two-bumps is RH.** -/
theorem riemannHypothesis_iff_weil_oddPrimeTwoBumps :
    RiemannHypothesis ↔ ∀ p : ℕ, p.Prime →
      0 ≤ (zetaZeroConfig.W (twoBump (boxSpline 1 3) (Real.log p) (-1))
        (twoBump (boxSpline 1 3) (Real.log p) (-1))).re := by
  constructor
  · intro hRH p hp
    have h := (riemannHypothesis_iff_hasseWeil_integerDegrees.mp hRH) p hp.pos
    rw [ScalingDatum.HasseWeilAt, orbitCorr_eq_re_lagStructure_spline,
      orbitCorr_eq_re_lagStructure_spline] at h
    rw [re_W_oddPrimeTwoBump_eq]; linarith [(abs_le.mp h).2]
  · intro h
    rw [riemannHypothesis_iff_bddAbove_primeDegrees]
    refine ⟨2 * (lagStructure zetaZeroConfig (boxSpline 1 3) 0).re, fun p hp => ?_⟩
    have := h p hp
    rw [re_W_oddPrimeTwoBump_eq] at this
    linarith

/-- **The width from the odd prime two-bumps.** -/
theorem zetaZeroWidth_le_iff_weil_oddPrimeTwoBumps {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    zetaZeroWidth ≤ a ↔ ∃ K : ℝ, ∀ p : ℕ, p.Prime →
      -(K * (p : ℝ) ^ a) ≤ (zetaZeroConfig.W (twoBump (boxSpline 1 3) (Real.log p) (-1))
        (twoBump (boxSpline 1 3) (Real.log p) (-1))).re := by
  rw [zetaZeroWidth_le_iff_bddAbove_primeDegrees ha0 ha]
  set c0 := 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) 0).re with hc0
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K + |c0|, fun p hp => ?_⟩
    have h1 := hK p hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) ^ a :=
      Real.one_le_rpow (by exact_mod_cast hp.one_lt.le) ha0
    have h2 := mul_le_mul_of_nonneg_left hp1 (abs_nonneg c0)
    rw [re_W_oddPrimeTwoBump_eq, ← hc0]
    nlinarith [neg_abs_le c0]
  · rintro ⟨K, hK⟩
    refine ⟨K + |c0|, fun p hp => ?_⟩
    have h1 := hK p hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) ^ a :=
      Real.one_le_rpow (by exact_mod_cast hp.one_lt.le) ha0
    have h2 := mul_le_mul_of_nonneg_left hp1 (abs_nonneg c0)
    rw [re_W_oddPrimeTwoBump_eq, ← hc0] at h1
    nlinarith [le_abs_self c0]

end GaloisForLFunctions.SurfaceOfSpecZ
