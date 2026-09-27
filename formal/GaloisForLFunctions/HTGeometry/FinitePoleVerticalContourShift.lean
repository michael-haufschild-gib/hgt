import GaloisForLFunctions.HTGeometry.RectangleResidueTheorem

/-!
# Vertical contour transport across finitely many poles

The arbitrary-order rectangle residue theorem, passed to two infinite vertical lines along any
escaping sequence of heights on which both horizontal sides vanish:

```text
∫ f(c + it) dt − ∫ f(a + it) dt = 2π Σ_{p ∈ P} Res_p f
```

(`verticalIntegral_sub_eq_sum_laurentCoeff_of_horizontal_tendsto_seq`), with `Res_p f` the
order-one Laurent coefficient, for poles of any order.

`laurentCoeff_neg_one_of_eq_div` computes that coefficient at a simple pole written as
`G(z)/(z − p)` with `G` analytic: it is `G(p)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory Set Filter Topology intervalIntegral
open scoped BigOperators Interval

noncomputable section

theorem verticalIntegral_sub_eq_sum_laurentCoeff_of_horizontal_tendsto_seq
    {f : ℂ → ℂ} {a c : ℝ} (hac : a < c) {P : Finset ℂ}
    (hPre : ∀ p ∈ P, a < p.re ∧ p.re < c)
    (hmero : ∀ p ∈ P, MeromorphicAt f p)
    (hoff : ∀ s : ℂ, a ≤ s.re → s.re ≤ c → s ∉ P → AnalyticAt ℂ f s)
    (ha : Integrable fun t : ℝ => f ((a : ℂ) + (t : ℂ) * Complex.I))
    (hc : Integrable fun t : ℝ => f ((c : ℂ) + (t : ℂ) * Complex.I))
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    (htop : Tendsto (fun n => HIntegral f a c (T n)) atTop (𝓝 0))
    (hbot : Tendsto (fun n => HIntegral f a c (-(T n))) atTop (𝓝 0)) :
    (∫ t : ℝ, f ((c : ℂ) + (t : ℂ) * Complex.I)) -
        (∫ t : ℝ, f ((a : ℂ) + (t : ℂ) * Complex.I)) =
      2 * (Real.pi : ℂ) * ∑ p ∈ P, laurentCoeff f p (-1) := by
  let B : ℝ := (∑ p ∈ P, |p.im|) + 1
  have hBpos : 0 < B := by
    dsimp only [B]
    have hsum : 0 ≤ ∑ p ∈ P, |p.im| := Finset.sum_nonneg fun p _ => abs_nonneg p.im
    linarith
  have hlarge : ∀ᶠ n : ℕ in atTop, B ≤ T n := (tendsto_atTop.1 hT) B
  have hres : ∀ᶠ n : ℕ in atTop,
      (1 / (2 * (Real.pi : ℂ) * Complex.I)) •
        (HIntegral f a c (-(T n)) - HIntegral f a c (T n) +
          VIntegral f c (-(T n)) (T n) - VIntegral f a (-(T n)) (T n)) =
        ∑ p ∈ P, laurentCoeff f p (-1) := by
    filter_upwards [hlarge] with n hn
    have hTpos : 0 < T n := lt_of_lt_of_le hBpos hn
    have hpIm : ∀ p ∈ P, -(T n) < p.im ∧ p.im < T n := by
      intro p hp
      have hpabs : |p.im| ≤ ∑ q ∈ P, |q.im| :=
        Finset.single_le_sum (fun q _ => abs_nonneg q.im) hp
      have habsT : |p.im| < T n := by
        dsimp only [B] at hn
        linarith
      exact ⟨by linarith [neg_abs_le p.im], by linarith [le_abs_self p.im]⟩
    let z : ℂ := (a : ℂ) + (-(T n) : ℂ) * Complex.I
    let w : ℂ := (c : ℂ) + (T n : ℂ) * Complex.I
    have hzre : z.re ≤ w.re := by dsimp [z, w]; simp; exact hac.le
    have hzim : z.im ≤ w.im := by dsimp [z, w]; simp; linarith
    have hpNhd : ∀ p ∈ P, Rectangle z w ∈ 𝓝 p := by
      intro p hp
      rw [rectangle_mem_nhds_iff]
      have hre := hPre p hp
      have him := hpIm p hp
      constructor
      · simpa [z, w, Set.uIoo_of_le hac.le] using hre
      · simpa [z, w, Set.uIoo_of_le (by linarith : -(T n) ≤ T n)] using him
    have hoffRect : ∀ s ∈ Rectangle z w, s ∉ P → AnalyticAt ℂ f s := by
      intro s hs hsP
      have hsre : s.re ∈ Set.Icc a c := by
        have := hs.1
        simpa [z, w, Set.uIcc_of_le hac.le] using this
      exact hoff s hsre.1 hsre.2 hsP
    have hr := rectangleIntegral'_eq_sum_laurentCoeff hzre hzim hpNhd hmero hoffRect
    simpa [z, w, RectangleIntegral, HIntegral, VIntegral] using hr
  have hright : Tendsto (fun n => VIntegral f c (-(T n)) (T n)) atTop
      (𝓝 (Complex.I * ∫ t : ℝ, f ((c : ℂ) + (t : ℂ) * Complex.I))) := by
    simpa [VIntegral] using (intervalIntegral_tendsto_integral hc
      (tendsto_neg_atTop_atBot.comp hT) hT).const_mul Complex.I
  have hleft : Tendsto (fun n => VIntegral f a (-(T n)) (T n)) atTop
      (𝓝 (Complex.I * ∫ t : ℝ, f ((a : ℂ) + (t : ℂ) * Complex.I))) := by
    simpa [VIntegral] using (intervalIntegral_tendsto_integral ha
      (tendsto_neg_atTop_atBot.comp hT) hT).const_mul Complex.I
  have hlim := (((hbot.sub htop).add hright).sub hleft).const_smul
    (1 / (2 * (Real.pi : ℂ) * Complex.I))
  have hlim' : Tendsto (fun n =>
      (1 / (2 * (Real.pi : ℂ) * Complex.I)) •
        (HIntegral f a c (-(T n)) - HIntegral f a c (T n) +
          VIntegral f c (-(T n)) (T n) - VIntegral f a (-(T n)) (T n))) atTop
      (𝓝 ((1 / (2 * (Real.pi : ℂ) * Complex.I)) •
        (Complex.I * ((∫ t : ℝ, f ((c : ℂ) + (t : ℂ) * Complex.I)) -
          ∫ t : ℝ, f ((a : ℂ) + (t : ℂ) * Complex.I))))) := by
    convert hlim using 2
    ring
  have heq := tendsto_nhds_unique (hlim'.congr' hres) tendsto_const_nhds
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hscale : (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
      (Complex.I * ((∫ t : ℝ, f ((c : ℂ) + (t : ℂ) * Complex.I)) -
        ∫ t : ℝ, f ((a : ℂ) + (t : ℂ) * Complex.I))) =
      ∑ p ∈ P, laurentCoeff f p (-1) := by
    simpa [smul_eq_mul] using heq
  rw [← hscale]
  generalize (∫ t : ℝ, f ((c : ℂ) + (t : ℂ) * Complex.I)) -
    (∫ t : ℝ, f ((a : ℂ) + (t : ℂ) * Complex.I)) = X
  field_simp

/-- The order-one Laurent coefficient at a simple pole `G(z)/(z − p)` is `G(p)`. -/
theorem laurentCoeff_neg_one_of_eq_div {f G : ℂ → ℂ} {p : ℂ} (hG : AnalyticAt ℂ G p)
    (hf : ∀ᶠ z in 𝓝[≠] p, f z = G z / (z - p)) :
    laurentCoeff f p (-1) = G p := by
  have hshift : laurentShift f p 2 =ᶠ[𝓝 0] fun t : ℂ => t * G (p + t) := by
    have h1 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), f (p + t) = G (p + t) / (p + t - p) :=
      (tendsto_const_add_nhdsNE p).eventually hf
    have h2 : ∀ᶠ t in 𝓝 (0 : ℂ), t ≠ 0 → f (p + t) = G (p + t) / (p + t - p) :=
      eventually_nhdsWithin_iff.1 h1
    filter_upwards [h2] with t ht
    simp only [laurentShift]
    rcases eq_or_ne t 0 with rfl | ht0
    · simp
    · rw [ht ht0, show p + t - p = t by ring]
      field_simp
  have hGt : AnalyticAt ℂ (fun t : ℂ => G (p + t)) 0 := by
    have : AnalyticAt ℂ (fun t : ℂ => p + t) 0 := by fun_prop
    exact (by simpa using hG : AnalyticAt ℂ G (p + 0)).comp this
  have hana : AnalyticAt ℂ (laurentShift f p 2) 0 :=
    (analyticAt_id.mul hGt).congr hshift.symm
  rw [laurentCoeff_eq_taylorCoeffZero hana (by norm_num)]
  have hidx : ((-1 : ℤ) + ((2 : ℕ) : ℤ)).toNat = 1 := by norm_num
  rw [hidx, taylorCoeffZero, iteratedDeriv_one, hshift.deriv_eq]
  have hd : HasDerivAt (fun t : ℂ => t * G (p + t)) (1 * G (p + 0) + 0 * deriv (fun t => G (p + t)) 0) 0 :=
    (hasDerivAt_id 0).mul hGt.differentiableAt.hasDerivAt
  rw [hd.deriv]
  simp

end

end GaloisForLFunctions.HTGeometry
