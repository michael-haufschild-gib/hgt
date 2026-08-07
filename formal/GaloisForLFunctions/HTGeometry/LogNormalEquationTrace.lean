import GaloisForLFunctions.HTGeometry.HalfLogCesaroAverage
import GaloisForLFunctions.HTGeometry.GammaTransportKernel
import GaloisForLFunctions.HTGeometry.MollifierUniformApproximation

/-!
# The equation bounds the half-log trace

The logarithmic normal equation says the Dirichlet operator plus the transport operator equals the
source.  A bound on the source together with a bound on the transport term therefore bounds the
Dirichlet operator, and dividing by `2√L` converts that into a bound on the half-log trace offset
by the averaged trace.

This is where the equation is actually used: everything else in the chain is an estimate about one
of the two operators separately.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The equation bounds the trace from above.**  A source bounded by `T` and a transport term
bounded below by `−B` give `√X f(X) ≤ (T+B)/(2√X) + A(X)`. -/
theorem halfLog_le_of_equation {f : ℝ → ℝ} {X S T B : ℝ} (hX : 0 < X)
    (heq : logDirichlet f X + gammaTransport f X = S) (hS : S ≤ T)
    (hB : -B ≤ gammaTransport f X) :
    Real.sqrt X * f X ≤ (T + B) / (2 * Real.sqrt X) + halfLogAverage f X := by
  refine halfLog_le_of_logDirichlet_le hX ?_
  linarith [heq, hS, hB]

/-- **The equation bounds the trace from below.**  The mirror, with the transport term bounded
above. -/
theorem le_halfLog_of_equation {f : ℝ → ℝ} {X S T B : ℝ} (hX : 0 < X)
    (heq : logDirichlet f X + gammaTransport f X = S) (hS : T ≤ S)
    (hB : gammaTransport f X ≤ B) :
    (T - B) / (2 * Real.sqrt X) + halfLogAverage f X ≤ Real.sqrt X * f X := by
  refine le_halfLog_of_le_logDirichlet hX ?_
  linarith [heq, hS, hB]

/-! ## The trace bounds with every derived input chained

The two lemmas above take a bound on the transport term.  That bound is not an assumption — it is
the transport estimate at the critical point.  Chaining it leaves only the equation, the
maximizing (resp. minimizing) property of the point, and object regularity.
-/

open MeasureTheory Set in
/-- **The trace bound at a penalized maximizer, with nothing derived assumed.** -/
theorem halfLog_le_of_equation_isMaxOn {f : ℝ → ℝ} {X δ M L₀ a S T : ℝ}
    (hX : 0 < X) (hδ : 0 ≤ δ) (hf : 0 ≤ f X) (hFb : ∀ x, |f x| ≤ M) (hmeas : Measurable f)
    (hnear : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioc 0 (X / 2)))
    (hmax : IsMaxOn (penalized (fun L => Real.sqrt L * f L) δ L₀) (Ici a) X)
    (ha : a ≤ X / 2)
    (heq : logDirichlet f X + gammaTransport f X = S) (hS : S ≤ T) :
    Real.sqrt X * f X
      ≤ (T + ((2 * δ / Real.sqrt X + 2 * (f X + δ * Real.sqrt X / 2) / X)
              * (∫ s in Ioc (0:ℝ) (X / 2), s * gammaTransportKernel s)
            + 4 * M * (-Real.log (1 - Real.exp (-(X / 2))))))
          / (2 * Real.sqrt X) + halfLogAverage f X :=
  halfLog_le_of_equation hX heq hS
    (neg_le_gammaTransport_of_isMaxOn hX hδ hf hFb hmeas hnear hmax ha)

open MeasureTheory Set in
/-- **The mirrored trace bound at a penalized minimizer.** -/
theorem le_halfLog_of_equation_isMaxOn_neg {f : ℝ → ℝ} {X δ M L₀ a S T : ℝ}
    (hX : 0 < X) (hδ : 0 ≤ δ) (hFb : ∀ x, |f x| ≤ M) (hmeas : Measurable f)
    (hnear : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioc 0 (X / 2)))
    (hnum : ∀ s, 0 ≤ s → s ≤ X / 2 → 0 ≤ f X - δ * s / Real.sqrt X)
    (hmax : IsMaxOn (penalized (fun L => -(Real.sqrt L * f L)) δ L₀) (Ici a) X)
    (ha : a ≤ X / 2)
    (heq : logDirichlet f X + gammaTransport f X = S) (hS : T ≤ S) :
    (T - ((2 * δ / Real.sqrt X + f X / (2 * X))
            * (∫ s in Ioc (0:ℝ) (X / 2), s * gammaTransportKernel s)
          + 4 * M * (-Real.log (1 - Real.exp (-(X / 2))))))
        / (2 * Real.sqrt X) + halfLogAverage f X
      ≤ Real.sqrt X * f X :=
  le_halfLog_of_equation hX heq hS
    (gammaTransport_le_of_isMaxOn_neg hX hδ hFb hmeas hnear hnum hmax ha)

/-! ## The bound transfers to the base point

The maximizer dominates the base point by construction, so the trace bound at the maximizer is
also a bound at the base point.  This removes any need to extract a subsequence realising the upper
limit: the estimate holds at *every* base point, so it bounds the upper limit directly.
-/

open MeasureTheory Set in
/-- **The trace at the base point is bounded.**  Chaining `le_value_of_isMaxOn_penalized` with the
trace bound at the maximizer. -/
theorem halfLog_base_le_of_equation_isMaxOn {f : ℝ → ℝ} {X δ M L₀ a S T : ℝ}
    (hX : 0 < X) (hδ : 0 ≤ δ) (hf : 0 ≤ f X) (hFb : ∀ x, |f x| ≤ M) (hmeas : Measurable f)
    (hnear : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioc 0 (X / 2)))
    (hmax : IsMaxOn (penalized (fun L => Real.sqrt L * f L) δ L₀) (Ici a) X)
    (ha : a ≤ X / 2) (hL₀ : L₀ ∈ Ici a)
    (heq : logDirichlet f X + gammaTransport f X = S) (hS : S ≤ T) :
    Real.sqrt L₀ * f L₀
      ≤ (T + ((2 * δ / Real.sqrt X + 2 * (f X + δ * Real.sqrt X / 2) / X)
              * (∫ s in Ioc (0:ℝ) (X / 2), s * gammaTransportKernel s)
            + 4 * M * (-Real.log (1 - Real.exp (-(X / 2))))))
          / (2 * Real.sqrt X) + halfLogAverage f X := by
  have hbase : Real.sqrt L₀ * f L₀ ≤ Real.sqrt X * f X :=
    le_value_of_isMaxOn_penalized hmax hδ hL₀
  exact hbase.trans
    (halfLog_le_of_equation_isMaxOn hX hδ hf hFb hmeas hnear hmax ha heq hS)

/-! ## The limit passage

Given a family of critical points running to infinity and the pointwise trace bound at each base
point, the upper limit of the trace is bounded by the limit of the averaged trace.  The prefactor
vanishes because the critical points diverge, and the average converges along them.
-/

open Filter MeasureTheory Set in
/-- The limsup half of the trace theorem, from a family of penalized maximizers. -/
theorem limsup_halfLog_le_of_family
    {F : ℝ → ℝ} {X : ℝ → ℝ} {α T : ℝ} {C : ℝ → ℝ}
    (hXdiv : Tendsto X atTop atTop)
    (hCb : ∀ᶠ L in atTop, |C L| ≤ T)
    (hbound : ∀ᶠ L in atTop, Real.sqrt L * F L ≤ C L / (2 * Real.sqrt (X L))
      + halfLogAverage F (X L))
    (hA : Tendsto (halfLogAverage F) atTop (nhds α))
    (hcb : IsCoboundedUnder (· ≤ ·) atTop fun L => Real.sqrt L * F L) :
    limsup (fun L => Real.sqrt L * F L) atTop ≤ α := by
  have hpre : Tendsto (fun L => C L / (2 * Real.sqrt (X L))) atTop (nhds 0) := by
    have h := tendsto_bounded_div_sqrt_comp (b := fun L => C L / 2) (X := X) (K := T / 2) hXdiv
      (by
        filter_upwards [hCb] with L hL
        rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        linarith [hL])
    refine h.congr fun L => ?_
    rw [div_div]
  have hAX : Tendsto (fun L => halfLogAverage F (X L)) atTop (nhds α) := hA.comp hXdiv
  have hg : Tendsto (fun L => C L / (2 * Real.sqrt (X L)) + halfLogAverage F (X L))
      atTop (nhds α) := by
    have := hpre.add hAX
    rwa [zero_add] at this
  exact limsup_le_of_eventually_le_of_tendsto hbound hg hcb hg.isBoundedUnder_le

open Filter MeasureTheory Set in
/-- The liminf half, by the same composition with the inequalities reversed. -/
theorem le_liminf_halfLog_of_family
    {F : ℝ → ℝ} {X : ℝ → ℝ} {α T : ℝ} {C : ℝ → ℝ}
    (hXdiv : Tendsto X atTop atTop)
    (hCb : ∀ᶠ L in atTop, |C L| ≤ T)
    (hbound : ∀ᶠ L in atTop, C L / (2 * Real.sqrt (X L)) + halfLogAverage F (X L)
      ≤ Real.sqrt L * F L)
    (hA : Tendsto (halfLogAverage F) atTop (nhds α))
    (hcb : IsCoboundedUnder (· ≥ ·) atTop fun L => Real.sqrt L * F L) :
    α ≤ liminf (fun L => Real.sqrt L * F L) atTop := by
  have hpre : Tendsto (fun L => C L / (2 * Real.sqrt (X L))) atTop (nhds 0) := by
    have h := tendsto_bounded_div_sqrt_comp (b := fun L => C L / 2) (X := X) (K := T / 2) hXdiv
      (by
        filter_upwards [hCb] with L hL
        rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        linarith [hL])
    refine h.congr fun L => ?_
    rw [div_div]
  have hAX : Tendsto (fun L => halfLogAverage F (X L)) atTop (nhds α) := hA.comp hXdiv
  have hg : Tendsto (fun L => C L / (2 * Real.sqrt (X L)) + halfLogAverage F (X L))
      atTop (nhds α) := by
    have := hpre.add hAX
    rwa [zero_add] at this
  exact le_liminf_of_eventually_le_of_tendsto hbound hg hcb hg.isBoundedUnder_ge

/-! ## The signed half-log trace exists

Two families of critical points — one from the penalized maximum, one from the penalized minimum —
pin the upper and lower limits of the half-log profile to the limit of its average.  The trace
therefore exists and equals that limit.
-/

open Filter in
/-- **The signed half-log trace exists.**  Given upper and lower critical-point families along
which the trace is squeezed by the averaged trace, the half-log profile converges to the limit of
the average. -/
theorem tendsto_halfLogTrace_of_families
    {F : ℝ → ℝ} {Xu Xl : ℝ → ℝ} {α Tu Tl : ℝ} {Cu Cl : ℝ → ℝ}
    (hXu : Tendsto Xu atTop atTop) (hXl : Tendsto Xl atTop atTop)
    (hCu : ∀ᶠ L in atTop, |Cu L| ≤ Tu) (hCl : ∀ᶠ L in atTop, |Cl L| ≤ Tl)
    (hup : ∀ᶠ L in atTop, Real.sqrt L * F L
      ≤ Cu L / (2 * Real.sqrt (Xu L)) + halfLogAverage F (Xu L))
    (hlow : ∀ᶠ L in atTop, Cl L / (2 * Real.sqrt (Xl L)) + halfLogAverage F (Xl L)
      ≤ Real.sqrt L * F L)
    (hA : Tendsto (halfLogAverage F) atTop (nhds α))
    (hb : IsBoundedUnder (· ≤ ·) atTop fun L => Real.sqrt L * F L)
    (hb' : IsBoundedUnder (· ≥ ·) atTop fun L => Real.sqrt L * F L)
    (hcb : IsCoboundedUnder (· ≤ ·) atTop fun L => Real.sqrt L * F L)
    (hcb' : IsCoboundedUnder (· ≥ ·) atTop fun L => Real.sqrt L * F L) :
    Tendsto (fun L => Real.sqrt L * F L) atTop (nhds α) :=
  tendsto_of_le_liminf_of_limsup_le
    (le_liminf_halfLog_of_family hXl hCl hlow hA hcb')
    (limsup_halfLog_le_of_family hXu hCu hup hA hcb) hb hb'

/-! ## The equation supplies the squeeze

Applying the base-point trace bound along a maximizer family turns the equation into the eventual
inequality that the limit passage consumes.  The numerator is explicit: the source bound plus the
transport estimate at the critical point.
-/

open MeasureTheory Set in
/-- The explicit numerator of the trace bound along a critical-point family. -/
noncomputable def traceBoundNumerator (F X : ℝ → ℝ) (M T : ℝ) (L₀ : ℝ) : ℝ :=
  T + ((2 * (Real.sqrt L₀)⁻¹ / Real.sqrt (X L₀)
        + 2 * (F (X L₀) + (Real.sqrt L₀)⁻¹ * Real.sqrt (X L₀) / 2) / X L₀)
      * (∫ s in Ioc (0:ℝ) (X L₀ / 2), s * gammaTransportKernel s)
    + 4 * M * (-Real.log (1 - Real.exp (-(X L₀ / 2)))))

open Filter MeasureTheory Set in
/-- **The equation gives the upper squeeze.**  Along a maximizer family whose points eventually sit
more than `a` inside the ray, the trace is eventually bounded by the explicit numerator over
`2√X` plus the averaged trace. -/
theorem eventually_halfLog_le_of_equation
    {F X S : ℝ → ℝ} {a M T : ℝ}
    (hFb : ∀ x, |F x| ≤ M) (hmeas : Measurable F) (hFpos : ∀ x, 0 ≤ F x)
    (hnear : ∀ Y, IntegrableOn (fun s => secondDifference F Y s * gammaTransportKernel s)
      (Ioc 0 (Y / 2)))
    (heq : ∀ Y, logDirichlet F Y + gammaTransport F Y = S Y) (hS : ∀ Y, S Y ≤ T)
    (hXmax : ∀ L₀ : ℝ, 0 < L₀ →
      IsMaxOn (penalized (fun L => Real.sqrt L * F L) (Real.sqrt L₀)⁻¹ L₀) (Ici a) (X L₀))
    (hXint : ∀ᶠ L₀ in atTop, a ≤ X L₀ / 2)
    (hXpos : ∀ᶠ L₀ in atTop, 0 < X L₀) :
    ∀ᶠ L₀ in atTop, Real.sqrt L₀ * F L₀
      ≤ traceBoundNumerator F X M T L₀ / (2 * Real.sqrt (X L₀))
        + halfLogAverage F (X L₀) := by
  filter_upwards [hXint, hXpos, eventually_gt_atTop (0:ℝ), eventually_ge_atTop a]
    with L₀ hint hpos hL₀ hmem
  have hδ : (0:ℝ) ≤ (Real.sqrt L₀)⁻¹ := by positivity
  exact halfLog_base_le_of_equation_isMaxOn hpos hδ (hFpos _) hFb hmeas (hnear _)
    (hXmax L₀ hL₀) hint hmem (heq _) (hS _)

open Filter MeasureTheory Set in
/-- **The mirrored base-point bound.**  At a penalized minimizer the value at the base point
dominates the value at the minimizer, so the lower bound there transfers up to the base point. -/
theorem le_halfLog_base_of_equation_isMaxOn_neg {f : ℝ → ℝ} {X δ M L₀ a S T : ℝ}
    (hX : 0 < X) (hδ : 0 ≤ δ) (hFb : ∀ x, |f x| ≤ M) (hmeas : Measurable f)
    (hnear : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioc 0 (X / 2)))
    (hnum : ∀ s, 0 ≤ s → s ≤ X / 2 → 0 ≤ f X - δ * s / Real.sqrt X)
    (hmax : IsMaxOn (penalized (fun L => -(Real.sqrt L * f L)) δ L₀) (Ici a) X)
    (ha : a ≤ X / 2) (hL₀ : L₀ ∈ Ici a)
    (heq : logDirichlet f X + gammaTransport f X = S) (hS : T ≤ S) :
    (T - ((2 * δ / Real.sqrt X + f X / (2 * X))
            * (∫ s in Ioc (0:ℝ) (X / 2), s * gammaTransportKernel s)
          + 4 * M * (-Real.log (1 - Real.exp (-(X / 2))))))
        / (2 * Real.sqrt X) + halfLogAverage f X
      ≤ Real.sqrt L₀ * f L₀ := by
  have hb := le_value_of_isMaxOn_penalized hmax hδ hL₀
  have hbase : Real.sqrt X * f X ≤ Real.sqrt L₀ * f L₀ := by linarith [hb]
  exact (le_halfLog_of_equation_isMaxOn_neg hX hδ hFb hmeas hnear hnum hmax ha heq hS).trans hbase

open MeasureTheory Set in
/-- The explicit numerator of the mirrored trace bound. -/
noncomputable def traceBoundNumeratorLower (F X : ℝ → ℝ) (M T : ℝ) (L₀ : ℝ) : ℝ :=
  T - ((2 * (Real.sqrt L₀)⁻¹ / Real.sqrt (X L₀) + F (X L₀) / (2 * X L₀))
      * (∫ s in Ioc (0:ℝ) (X L₀ / 2), s * gammaTransportKernel s)
    + 4 * M * (-Real.log (1 - Real.exp (-(X L₀ / 2)))))

open Filter MeasureTheory Set in
/-- **The equation gives the lower squeeze.**  The mirror of `eventually_halfLog_le_of_equation`,
along a minimizer family. -/
theorem eventually_le_halfLog_of_equation
    {F X S : ℝ → ℝ} {a M T : ℝ}
    (hFb : ∀ x, |F x| ≤ M) (hmeas : Measurable F)
    (hnear : ∀ Y, IntegrableOn (fun s => secondDifference F Y s * gammaTransportKernel s)
      (Ioc 0 (Y / 2)))
    (hnum : ∀ L₀ Y, ∀ s, 0 ≤ s → s ≤ Y / 2 →
      0 ≤ F Y - (Real.sqrt L₀)⁻¹ * s / Real.sqrt Y)
    (heq : ∀ Y, logDirichlet F Y + gammaTransport F Y = S Y) (hS : ∀ Y, T ≤ S Y)
    (hXmax : ∀ L₀ : ℝ, 0 < L₀ →
      IsMaxOn (penalized (fun L => -(Real.sqrt L * F L)) (Real.sqrt L₀)⁻¹ L₀) (Ici a) (X L₀))
    (hXint : ∀ᶠ L₀ in atTop, a ≤ X L₀ / 2)
    (hXpos : ∀ᶠ L₀ in atTop, 0 < X L₀) :
    ∀ᶠ L₀ in atTop, traceBoundNumeratorLower F X M T L₀ / (2 * Real.sqrt (X L₀))
        + halfLogAverage F (X L₀) ≤ Real.sqrt L₀ * F L₀ := by
  filter_upwards [hXint, hXpos, eventually_gt_atTop (0:ℝ), eventually_ge_atTop a]
    with L₀ hint hpos hL₀ hmem
  have hδ : (0:ℝ) ≤ (Real.sqrt L₀)⁻¹ := by positivity
  exact le_halfLog_base_of_equation_isMaxOn_neg hpos hδ hFb hmeas (hnear _) (hnum L₀ _)
    (hXmax L₀ hL₀) hint hmem (heq _) (hS _)

open Filter in
/-- **The trace theorem in the form the argument supplies.**  The numerators converge rather than
being bounded by a named constant, and convergence is what the trace bound actually produces. -/
theorem tendsto_halfLogTrace_of_convergent_families
    {F Xu Xl : ℝ → ℝ} {α Tu Tl : ℝ} {Cu Cl : ℝ → ℝ}
    (hXu : Tendsto Xu atTop atTop) (hXl : Tendsto Xl atTop atTop)
    (hCu : Tendsto Cu atTop (nhds Tu)) (hCl : Tendsto Cl atTop (nhds Tl))
    (hup : ∀ᶠ L in atTop, Real.sqrt L * F L
      ≤ Cu L / (2 * Real.sqrt (Xu L)) + halfLogAverage F (Xu L))
    (hlow : ∀ᶠ L in atTop, Cl L / (2 * Real.sqrt (Xl L)) + halfLogAverage F (Xl L)
      ≤ Real.sqrt L * F L)
    (hA : Tendsto (halfLogAverage F) atTop (nhds α))
    (hb : IsBoundedUnder (· ≤ ·) atTop fun L => Real.sqrt L * F L)
    (hb' : IsBoundedUnder (· ≥ ·) atTop fun L => Real.sqrt L * F L)
    (hcb : IsCoboundedUnder (· ≤ ·) atTop fun L => Real.sqrt L * F L)
    (hcb' : IsCoboundedUnder (· ≥ ·) atTop fun L => Real.sqrt L * F L) :
    Tendsto (fun L => Real.sqrt L * F L) atTop (nhds α) :=
  tendsto_halfLogTrace_of_families hXu hXl
    (eventually_abs_le_of_tendsto hCu) (eventually_abs_le_of_tendsto hCl)
    hup hlow hA hb hb' hcb hcb'

/-! ## The numerator converges

The trace bound's numerator is `T` plus a bracket that vanishes: a coefficient tending to zero
times the bounded partial first moment, plus the vanishing tail mass.  Its convergence is what
supplies the boundedness hypothesis of the trace theorem.
-/

open Filter in
/-- The first coefficient term vanishes: `(√L₀)⁻¹ ≤ 1` eventually, over `√(X L₀) → ∞`. -/
theorem tendsto_traceBound_term1 {X : ℝ → ℝ} (hXdiv : Tendsto X atTop atTop) :
    Tendsto (fun L₀ => 2 * (Real.sqrt L₀)⁻¹ / Real.sqrt (X L₀)) atTop (nhds 0) := by
  refine tendsto_bounded_div_sqrt_comp (K := 2) hXdiv ?_
  filter_upwards [eventually_ge_atTop (1:ℝ)] with L₀ hL
  have hs : (1:ℝ) ≤ Real.sqrt L₀ := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hL
  have hspos : (0:ℝ) < Real.sqrt L₀ := lt_of_lt_of_le zero_lt_one hs
  have hinv : (Real.sqrt L₀)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    exact Or.inr hs
  rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  linarith [hinv]

open Filter in
/-- **The cross factor is bounded.**  `(√L₀)⁻¹ √(X L₀) = √(X L₀ / L₀) → 1`, so it is eventually
bounded — this is what keeps the second coefficient term's numerator under control. -/
theorem eventually_abs_inv_sqrt_mul_sqrt_le {X : ℝ → ℝ}
    (hratio : Tendsto (fun L₀ => X L₀ / L₀) atTop (nhds 1))
    (hXnn : ∀ᶠ L₀ in atTop, 0 ≤ X L₀) :
    ∀ᶠ L₀ in atTop, |(Real.sqrt L₀)⁻¹ * Real.sqrt (X L₀)| ≤ |(1:ℝ)| + 1 := by
  have hsqrt : Tendsto (fun L₀ => Real.sqrt (X L₀ / L₀)) atTop (nhds 1) := by
    have h := (Real.continuous_sqrt.tendsto 1).comp hratio
    rwa [Real.sqrt_one] at h
  have hev := eventually_abs_le_of_tendsto hsqrt
  filter_upwards [hev, hXnn, eventually_gt_atTop (0:ℝ)] with L₀ h1 h2 h3
  have hrw : Real.sqrt (X L₀ / L₀) = (Real.sqrt L₀)⁻¹ * Real.sqrt (X L₀) := by
    rw [Real.sqrt_div h2, div_eq_inv_mul]
  rwa [hrw] at h1

open Filter in
/-- The second coefficient term vanishes: a bounded numerator over `X L₀ → ∞`.  The numerator is
bounded because the profile is and the cross factor converges. -/
theorem tendsto_traceBound_term2 {F X : ℝ → ℝ} {M : ℝ}
    (hFb : ∀ x, |F x| ≤ M)
    (hXdiv : Tendsto X atTop atTop)
    (hratio : Tendsto (fun L₀ => X L₀ / L₀) atTop (nhds 1))
    (hXnn : ∀ᶠ L₀ in atTop, 0 ≤ X L₀) :
    Tendsto (fun L₀ => 2 * (F (X L₀) + (Real.sqrt L₀)⁻¹ * Real.sqrt (X L₀) / 2) / X L₀)
      atTop (nhds 0) := by
  refine tendsto_bounded_div_atTop (K := 2 * (M + (|(1:ℝ)| + 1) / 2)) hXdiv ?_
  filter_upwards [eventually_abs_inv_sqrt_mul_sqrt_le hratio hXnn] with L₀ hcross
  rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have h1 := hFb (X L₀)
  have h2 : |(Real.sqrt L₀)⁻¹ * Real.sqrt (X L₀) / 2| ≤ (|(1:ℝ)| + 1) / 2 := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith [hcross]
  have h3 := abs_add_le (F (X L₀)) ((Real.sqrt L₀)⁻¹ * Real.sqrt (X L₀) / 2)
  linarith [h1, h2, h3]

open Filter MeasureTheory Set in
/-- **The trace-bound numerator converges to the source bound.**  Both coefficient terms vanish,
the partial first moment is bounded, and the tail mass vanishes, so the whole bracket does. -/
theorem tendsto_traceBoundNumerator {F X : ℝ → ℝ} {M T : ℝ}
    (hFb : ∀ x, |F x| ≤ M)
    (hXdiv : Tendsto X atTop atTop)
    (hratio : Tendsto (fun L₀ => X L₀ / L₀) atTop (nhds 1))
    (hXnn : ∀ᶠ L₀ in atTop, 0 ≤ X L₀) :
    Tendsto (traceBoundNumerator F X M T) atTop (nhds T) := by
  have h1 := tendsto_traceBound_term1 (X := X) hXdiv
  have h2 := tendsto_traceBound_term2 hFb hXdiv hratio hXnn
  have hcoef : Tendsto (fun L₀ => 2 * (Real.sqrt L₀)⁻¹ / Real.sqrt (X L₀)
      + 2 * (F (X L₀) + (Real.sqrt L₀)⁻¹ * Real.sqrt (X L₀) / 2) / X L₀)
      atTop (nhds 0) := by
    have := h1.add h2
    rwa [add_zero] at this
  have hmom : ∀ᶠ L₀ in atTop,
      |∫ s in Ioc (0:ℝ) (X L₀ / 2), s * gammaTransportKernel s|
        ≤ |∫ s in Ioi (0:ℝ), s * gammaTransportKernel s| := by
    filter_upwards with L₀
    have hle := integral_Ioc_id_mul_kernel_le (X L₀ / 2)
    have hnn : 0 ≤ ∫ s in Ioc (0:ℝ) (X L₀ / 2), s * gammaTransportKernel s := by
      refine setIntegral_nonneg measurableSet_Ioc fun s hs => ?_
      exact le_of_lt (mul_pos hs.1 (gammaTransportKernel_pos hs.1))
    rw [abs_of_nonneg hnn]
    exact hle.trans (le_abs_self _)
  have hprod : Tendsto (fun L₀ => (2 * (Real.sqrt L₀)⁻¹ / Real.sqrt (X L₀)
      + 2 * (F (X L₀) + (Real.sqrt L₀)⁻¹ * Real.sqrt (X L₀) / 2) / X L₀)
      * ∫ s in Ioc (0:ℝ) (X L₀ / 2), s * gammaTransportKernel s) atTop (nhds 0) :=
    tendsto_zero_mul_of_eventually_bounded hcoef hmom
  have htail : Tendsto (fun L₀ => 4 * M * (-Real.log (1 - Real.exp (-(X L₀ / 2)))))
      atTop (nhds 0) := by
    have h := tendsto_kernelTailMass_atTop.comp
      ((tendsto_id.atTop_div_const (by norm_num : (0:ℝ) < 2)).comp hXdiv)
    have := h.const_mul (4 * M)
    rwa [mul_zero] at this
  have hbr := hprod.add htail
  rw [add_zero] at hbr
  have := hbr.const_add T
  rw [add_zero] at this
  exact this

open Filter MeasureTheory Set in
/-- **The mirrored numerator also converges to the source bound.**  Simpler than the maximizer
version: the second coefficient term is `F(X)/(2X)`, with no cross factor. -/
theorem tendsto_traceBoundNumeratorLower {F X : ℝ → ℝ} {M T : ℝ}
    (hFb : ∀ x, |F x| ≤ M)
    (hXdiv : Tendsto X atTop atTop) :
    Tendsto (traceBoundNumeratorLower F X M T) atTop (nhds T) := by
  have h1 := tendsto_traceBound_term1 (X := X) hXdiv
  have h2X : Tendsto (fun L₀ => 2 * X L₀) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2) hXdiv
  have h2 : Tendsto (fun L₀ => F (X L₀) / (2 * X L₀)) atTop (nhds 0) :=
    tendsto_bounded_div_atTop (K := M) h2X (Filter.Eventually.of_forall fun L₀ => hFb _)
  have hcoef : Tendsto (fun L₀ => 2 * (Real.sqrt L₀)⁻¹ / Real.sqrt (X L₀)
      + F (X L₀) / (2 * X L₀)) atTop (nhds 0) := by
    have := h1.add h2
    rwa [add_zero] at this
  have hmom : ∀ᶠ L₀ in atTop,
      |∫ s in Ioc (0:ℝ) (X L₀ / 2), s * gammaTransportKernel s|
        ≤ |∫ s in Ioi (0:ℝ), s * gammaTransportKernel s| := by
    filter_upwards with L₀
    have hle := integral_Ioc_id_mul_kernel_le (X L₀ / 2)
    have hnn : 0 ≤ ∫ s in Ioc (0:ℝ) (X L₀ / 2), s * gammaTransportKernel s := by
      refine setIntegral_nonneg measurableSet_Ioc fun s hs => ?_
      exact le_of_lt (mul_pos hs.1 (gammaTransportKernel_pos hs.1))
    rw [abs_of_nonneg hnn]
    exact hle.trans (le_abs_self _)
  have hprod := tendsto_zero_mul_of_eventually_bounded hcoef hmom
  have htail : Tendsto (fun L₀ => 4 * M * (-Real.log (1 - Real.exp (-(X L₀ / 2)))))
      atTop (nhds 0) := by
    have h := tendsto_kernelTailMass_atTop.comp
      ((tendsto_id.atTop_div_const (by norm_num : (0:ℝ) < 2)).comp hXdiv)
    have := h.const_mul (4 * M)
    rwa [mul_zero] at this
  have hbr := hprod.add htail
  rw [add_zero] at hbr
  have := hbr.const_sub T
  rw [sub_zero] at this
  exact this

open Filter in
/-- **The signed half-log trace exists**, with the numerator bounds discharged from convergence. -/
theorem tendsto_halfLogTrace_of_equation_families
    {F Xu Xl : ℝ → ℝ} {α M T Tl : ℝ}
    (hFb : ∀ x, |F x| ≤ M)
    (hXu : Tendsto Xu atTop atTop) (hXl : Tendsto Xl atTop atTop)
    (hratio : Tendsto (fun L₀ => Xu L₀ / L₀) atTop (nhds 1))
    (hXunn : ∀ᶠ L₀ in atTop, 0 ≤ Xu L₀)
    (hup : ∀ᶠ L in atTop, Real.sqrt L * F L
      ≤ traceBoundNumerator F Xu M T L / (2 * Real.sqrt (Xu L)) + halfLogAverage F (Xu L))
    (hlow : ∀ᶠ L in atTop,
      traceBoundNumeratorLower F Xl M Tl L / (2 * Real.sqrt (Xl L)) + halfLogAverage F (Xl L)
        ≤ Real.sqrt L * F L)
    (hA : Tendsto (halfLogAverage F) atTop (nhds α))
    (hb : IsBoundedUnder (· ≤ ·) atTop fun L => Real.sqrt L * F L)
    (hb' : IsBoundedUnder (· ≥ ·) atTop fun L => Real.sqrt L * F L)
    (hcb : IsCoboundedUnder (· ≤ ·) atTop fun L => Real.sqrt L * F L)
    (hcb' : IsCoboundedUnder (· ≥ ·) atTop fun L => Real.sqrt L * F L) :
    Tendsto (fun L => Real.sqrt L * F L) atTop (nhds α) :=
  tendsto_halfLogTrace_of_convergent_families hXu hXl
    (tendsto_traceBoundNumerator hFb hXu hratio hXunn)
    (tendsto_traceBoundNumeratorLower hFb hXl)
    hup hlow hA hb hb' hcb hcb'

open Filter MeasureTheory Set in
/-- **The family is uniformly localised.**  With the profile bounded in `[−B, B]` on the ray, the
maximizer sits within `2B√L₀` of its base point — a bound with no `L₀`-dependent constant, which is
what the divergence and ratio lemmas require. -/
theorem eventually_localised_of_isMaxOn_family {H X : ℝ → ℝ} {a B : ℝ}
    (hHup : ∀ L ∈ Ici a, H L ≤ B) (hHlow : ∀ L ∈ Ici a, -B ≤ H L)
    (hXmax : ∀ L₀ : ℝ, 0 < L₀ →
      IsMaxOn (penalized H (Real.sqrt L₀)⁻¹ L₀) (Ici a) (X L₀))
    (hXmem : ∀ L₀ : ℝ, 0 < L₀ → X L₀ ∈ Ici a) :
    ∀ᶠ L₀ in atTop, |X L₀ - L₀| ≤ Real.sqrt L₀ * (2 * B) := by
  filter_upwards [eventually_gt_atTop (0:ℝ), eventually_ge_atTop a] with L₀ hL₀ hmem
  have hloc := abs_sub_le_sqrt_mul_of_isMaxOn hL₀ (hXmax L₀ hL₀) hmem (hHup _ (hXmem L₀ hL₀))
  have hlow := hHlow L₀ hmem
  have hs : 0 ≤ Real.sqrt L₀ := Real.sqrt_nonneg _
  nlinarith [hloc, hlow, hs]

/-! ## The boundedness side conditions are not hypotheses

The four filter-boundedness conditions of the trace theorem follow from the card's `(1)` — the
profile being bounded on the terminal ray — and so must be derived rather than assumed.
-/

open Filter Set in
/-- Bounded above on a terminal ray gives boundedness under `atTop`. -/
theorem isBoundedUnder_le_of_eventually_le {f : ℝ → ℝ} {a B : ℝ}
    (h : ∀ L ∈ Ici a, f L ≤ B) : IsBoundedUnder (· ≤ ·) atTop f :=
  ⟨B, by
    rw [Filter.eventually_map]
    filter_upwards [eventually_ge_atTop a] with L hL using h L hL⟩

open Filter Set in
/-- Bounded below on a terminal ray gives the dual. -/
theorem isBoundedUnder_ge_of_eventually_le {f : ℝ → ℝ} {a B : ℝ}
    (h : ∀ L ∈ Ici a, -B ≤ f L) : IsBoundedUnder (· ≥ ·) atTop f :=
  ⟨-B, by
    rw [Filter.eventually_map]
    filter_upwards [eventually_ge_atTop a] with L hL using h L hL⟩

open Filter Set in
/-- Coboundedness above, from the lower bound. -/
theorem isCoboundedUnder_le_of_eventually_le {f : ℝ → ℝ} {a B : ℝ}
    (h : ∀ L ∈ Ici a, -B ≤ f L) : IsCoboundedUnder (· ≤ ·) atTop f :=
  (isBoundedUnder_ge_of_eventually_le h).isCoboundedUnder_le

open Filter Set in
/-- Coboundedness below, from the upper bound. -/
theorem isCoboundedUnder_ge_of_eventually_le {f : ℝ → ℝ} {a B : ℝ}
    (h : ∀ L ∈ Ici a, f L ≤ B) : IsCoboundedUnder (· ≥ ·) atTop f :=
  (isBoundedUnder_le_of_eventually_le h).isCoboundedUnder_ge

/-! ## The signed half-log trace theorem

Assembling everything: from the logarithmic normal equation with a bounded source, a bounded
half-log profile, and convergence of the averaged trace, the signed half-log trace exists and
equals the limit of the average.

The two penalized families — a maximum family and a minimum family — are constructed here, their
localisation, divergence, ratio and positivity are read off, the equation supplies the two squeeze
inequalities, and the limit passage concludes.
-/

open Filter MeasureTheory Set in
/-- **The signed half-log trace exists.**  For a bounded profile satisfying the logarithmic normal
equation with a bounded source, whose averaged trace converges to `α`, the half-log trace
`√L F(L)` converges to `α`. -/
theorem tendsto_halfLogTrace_of_equation
    {F S : ℝ → ℝ} {a α M T Tl B : ℝ}
    (hFb : ∀ x, |F x| ≤ M) (hmeas : Measurable F) (hFpos : ∀ x, 0 ≤ F x)
    (hHcont : ContinuousOn (fun L => Real.sqrt L * F L) (Ici a))
    (hHup : ∀ L ∈ Ici a, Real.sqrt L * F L ≤ B)
    (hHlow : ∀ L ∈ Ici a, -B ≤ Real.sqrt L * F L)
    (hnear : ∀ Y, IntegrableOn (fun s => secondDifference F Y s * gammaTransportKernel s)
      (Ioc 0 (Y / 2)))
    (hnumlow : ∀ L₀ Y, ∀ s, 0 ≤ s → s ≤ Y / 2 →
      0 ≤ F Y - (Real.sqrt L₀)⁻¹ * s / Real.sqrt Y)
    (heq : ∀ Y, logDirichlet F Y + gammaTransport F Y = S Y)
    (hSu : ∀ Y, S Y ≤ T) (hSl : ∀ Y, Tl ≤ S Y)
    (hA : Tendsto (halfLogAverage F) atTop (nhds α)) :
    Tendsto (fun L => Real.sqrt L * F L) atTop (nhds α) := by
  have hb := isBoundedUnder_le_of_eventually_le hHup
  have hb' := isBoundedUnder_ge_of_eventually_le hHlow
  have hcb := isCoboundedUnder_le_of_eventually_le hHlow
  have hcb' := isCoboundedUnder_ge_of_eventually_le hHup
  obtain ⟨Xu, hXu⟩ := exists_maximizer_family (B := B) hHcont hHup
  obtain ⟨Xl, hXl⟩ := exists_minimizer_family (B := B) hHcont hHlow
  have hlocu := eventually_localised_of_isMaxOn_family hHup hHlow
    (fun L₀ h => (hXu L₀ h).2) (fun L₀ h => (hXu L₀ h).1)
  have hlocl := eventually_localised_of_isMaxOn_family
    (H := fun L => -(Real.sqrt L * F L))
    (fun L hL => by simpa using neg_le_neg (hHlow L hL))
    (fun L hL => by simpa using neg_le_neg (hHup L hL))
    (fun L₀ h => (hXl L₀ h).2) (fun L₀ h => (hXl L₀ h).1)
  have hXudiv := tendsto_atTop_of_localised hlocu
  have hXldiv := tendsto_atTop_of_localised hlocl
  have hratio := tendsto_div_one_of_localised hlocu
  have hXunn : ∀ᶠ L₀ in atTop, 0 ≤ Xu L₀ := eventually_le_of_localised hlocu 0
  have hXupos : ∀ᶠ L₀ in atTop, 0 < Xu L₀ := by
    filter_upwards [eventually_le_of_localised hlocu 1] with L₀ h; linarith
  have hXlpos : ∀ᶠ L₀ in atTop, 0 < Xl L₀ := by
    filter_upwards [eventually_le_of_localised hlocl 1] with L₀ h; linarith
  have hXuint : ∀ᶠ L₀ in atTop, a ≤ Xu L₀ / 2 := by
    filter_upwards [eventually_le_of_localised hlocu (2 * a)] with L₀ h; linarith
  have hXlint : ∀ᶠ L₀ in atTop, a ≤ Xl L₀ / 2 := by
    filter_upwards [eventually_le_of_localised hlocl (2 * a)] with L₀ h; linarith
  have hup := eventually_halfLog_le_of_equation (X := Xu) hFb hmeas hFpos hnear heq hSu
    (fun L₀ h => (hXu L₀ h).2) hXuint hXupos
  have hlow := eventually_le_halfLog_of_equation (X := Xl) hFb hmeas hnear hnumlow heq hSl
    (fun L₀ h => (hXl L₀ h).2) hXlint hXlpos
  exact tendsto_halfLogTrace_of_equation_families hFb hXudiv hXldiv hratio hXunn
    hup hlow hA hb hb' hcb hcb'


/-! ## The trace theorem with the averaged limit chained

`(12)` — existence of the averaged trace — is itself a theorem, not an assumption.  Chaining it
determines the limit explicitly and leaves only the equation, the source bounds and object
regularity.
-/

open Filter MeasureTheory Set in
/-- **The signed half-log trace, with `(12)` chained.**  The limit is the explicit value
`A(L₀) + ∫_{L₀}^∞ P F/(4L^{3/2})` rather than a free parameter. -/
theorem tendsto_halfLogTrace_of_equation_of_integrable
    {F S : ℝ → ℝ} {a M T Tl B L₀ : ℝ}
    (hFb : ∀ x, |F x| ≤ M) (hmeas : Measurable F) (hFpos : ∀ x, 0 ≤ F x)
    (hFcont : Continuous F)
    (hHcont : ContinuousOn (fun L => Real.sqrt L * F L) (Ici a))
    (hHup : ∀ L ∈ Ici a, Real.sqrt L * F L ≤ B)
    (hHlow : ∀ L ∈ Ici a, -B ≤ Real.sqrt L * F L)
    (hnear : ∀ Y, IntegrableOn (fun s => secondDifference F Y s * gammaTransportKernel s)
      (Ioc 0 (Y / 2)))
    (hnumlow : ∀ L₀' Y, ∀ s, 0 ≤ s → s ≤ Y / 2 →
      0 ≤ F Y - (Real.sqrt L₀')⁻¹ * s / Real.sqrt Y)
    (heq : ∀ Y, logDirichlet F Y + gammaTransport F Y = S Y)
    (hSu : ∀ Y, S Y ≤ T) (hSl : ∀ Y, Tl ≤ S Y)
    (hL₀ : 0 < L₀)
    (hAint : IntegrableOn (fun L => logDirichlet F L / (4 * L * Real.sqrt L)) (Ioi L₀)) :
    Tendsto (fun L => Real.sqrt L * F L) atTop
      (nhds (halfLogAverage F L₀
        + ∫ x in Ioi L₀, logDirichlet F x / (4 * x * Real.sqrt x))) :=
  tendsto_halfLogTrace_of_equation hFb hmeas hFpos hHcont hHup hHlow hnear hnumlow heq hSu hSl
    (tendsto_halfLogAverage hFcont hL₀ hAint)

/-! ## The averaged-trace integrability, reduced to the card's `(10)`

The equation splits `P F/(4L^{3/2})` into a bounded source over `L^{3/2}` — always integrable on a
terminal ray — and the transport term over the same weight, which is exactly the card's `(10)`.
-/

open MeasureTheory Set in
/-- `L^{-3/2}` is integrable on any terminal ray. -/
theorem integrableOn_inv_weight {L₀ : ℝ} (hL₀ : 0 < L₀) :
    IntegrableOn (fun L : ℝ => L ^ (-(3:ℝ)/2)) (Ioi L₀) := by
  rw [integrableOn_Ioi_rpow_iff hL₀]
  norm_num

open MeasureTheory Set in
/-- A bounded numerator over `4L^{3/2}` is integrable on a terminal ray. -/
theorem integrableOn_bounded_div_weight {S : ℝ → ℝ} {L₀ C : ℝ} (hL₀ : 0 < L₀)
    (hmeas : Measurable S) (hbd : ∀ L, |S L| ≤ C) :
    IntegrableOn (fun L => S L / (4 * L * Real.sqrt L)) (Ioi L₀) := by
  have hdom : IntegrableOn (fun L : ℝ => C * L ^ (-(3:ℝ)/2)) (Ioi L₀) :=
    (integrableOn_inv_weight hL₀).const_mul C
  have hm : Measurable fun L : ℝ => S L / (4 * L * Real.sqrt L) := by fun_prop
  refine Integrable.mono' hdom hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
  have hpos : 0 < L := lt_trans hL₀ hL
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hpos
  have hden : 0 < 4 * L * Real.sqrt L := by positivity
  have hprod : L * Real.sqrt L = L ^ ((3:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, show ((3:ℝ)/2) = 1 + 1/2 by norm_num, Real.rpow_add hpos,
      Real.rpow_one]
  have hrw : L ^ (-(3:ℝ)/2) = 1 / (L * Real.sqrt L) := by
    rw [hprod, one_div, ← Real.rpow_neg hpos.le]
    norm_num
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hden, div_le_iff₀ hden, hrw]
  have h1 := hbd L
  have h2 : C * (1 / (L * Real.sqrt L)) * (4 * L * Real.sqrt L) = 4 * C := by
    field_simp
  rw [h2]
  linarith [h1, abs_nonneg (S L)]

open MeasureTheory Set in
/-- **The averaged-trace integrability follows from the equation and `(10)`.**  The source half is
automatic; only the transport half is the card's `(10)`. -/
theorem integrableOn_logDirichlet_weight_of_equation {F S : ℝ → ℝ} {L₀ C : ℝ}
    (hL₀ : 0 < L₀) (hSmeas : Measurable S) (hSbd : ∀ L, |S L| ≤ C)
    (heq : ∀ Y, logDirichlet F Y + gammaTransport F Y = S Y)
    (hR : IntegrableOn (fun L => gammaTransport F L / (4 * L * Real.sqrt L)) (Ioi L₀)) :
    IntegrableOn (fun L => logDirichlet F L / (4 * L * Real.sqrt L)) (Ioi L₀) := by
  have hS := integrableOn_bounded_div_weight (S := S) hL₀ hSmeas hSbd
  have hdiff := hS.sub hR
  refine hdiff.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with L _
  have h := heq L
  have hsub : S L - gammaTransport F L = logDirichlet F L := by linarith
  show S L / (4 * L * Real.sqrt L) - gammaTransport F L / (4 * L * Real.sqrt L)
    = logDirichlet F L / (4 * L * Real.sqrt L)
  rw [div_sub_div_same, hsub]

/-! ## The mollified equation

Mollification commutes with the transport operator and with the primitive; only multiplication by
the coordinate does not, and its defect is the first-moment kernel.  So the logarithmic Dirichlet
operator of the mollified profile is the mollified operator plus twice that defect — the card's
`(17)`, and the step that converts the equation into its pointwise smoothed form `(18)`.
-/

open MeasureTheory in
/-- **The card's `(17)`.**  `P f_ε = ρ_ε * (P f) + 2 (s ρ_ε) * f`, from `mollify_position_eq` plus
linearity.

**Caution on `hY`.**  The hypothesis `ρ * Y_F = Y_{ρ*F}` is stated here for the *half-line*
primitive, and in that form it is **false** for a mollifier supported on both sides of the origin:
unfolding the right-hand side gives `∫ρ(t)(∫_{−t}^{L−t}F)dt`, which differs from
`∫ρ(t)(∫_0^{L−t}F)dt`.  The correct statement uses the *full* primitive of the zero extension,
where the commutation is associativity of convolution.  Use this lemma only with a `ρ` supported in
`[0,∞)`, or restate it via `zeroExtend`. -/
theorem logDirichlet_mollify {ρ F : ℝ → ℝ} (hρ : Continuous ρ) (hF : Continuous F)
    (hcρ : HasCompactSupport ρ) (L : ℝ)
    (hY : mollify ρ (halfLinePrimitive F) L = halfLinePrimitive (mollify ρ F) L) :
    logDirichlet (mollify ρ F) L
      = mollify ρ (logDirichlet F) L + 2 * mollify (firstMomentKernel ρ) F L := by
  have hpos := mollify_position_eq ρ F hρ hF hcρ L
  have hlin : mollify ρ (fun Y => 2 * Y * F Y - halfLinePrimitive F Y) L
      = 2 * mollify ρ (fun y => y * F y) L - mollify ρ (halfLinePrimitive F) L := by
    unfold mollify
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_sub]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      show ρ t * (2 * (L - t) * F (L - t) - halfLinePrimitive F (L - t))
        = 2 * (ρ t * ((L - t) * F (L - t))) - ρ t * halfLinePrimitive F (L - t)
      ring
    · exact (integrable_mollifyKernel hρ (continuous_id.mul hF) hcρ L).const_mul 2
    · exact integrable_mollifyKernel hρ (continuous_halfLinePrimitive hF) hcρ L
  unfold logDirichlet
  rw [← hY, hlin, hpos]
  ring

/-! ## The zero extension and the primitive

Section DD of the promotion ledger records that the mollified-primitive identity must be stated for
the *full* primitive of the zero extension, not the half-line primitive of the profile: the
half-line version is false for a two-sided mollifier because the lower limit of integration is
pinned at the origin.

The bridge below is what makes the reformulation usable: on the nonnegative ray the full primitive
of the zero extension *is* the half-line primitive.
-/

open MeasureTheory Set in
/-- The full primitive of the zero extension collapses to an integral over the positive part.  The
negative part contributes nothing, and the origin is a null set. -/
theorem integral_Iic_zeroExtend (F : ℝ → ℝ) (L : ℝ) :
    (∫ x in Iic L, zeroExtend F x) = ∫ x in Ioc (0:ℝ) L, F x := by
  have hsub : Ioc (0:ℝ) L ⊆ Iic L := fun x hx => mem_Iic.mpr hx.2
  have hdiff : ∀ᵐ x : ℝ, x ∈ Iic L \ Ioc (0:ℝ) L → zeroExtend F x = 0 := by
    have hne : ∀ᵐ x : ℝ, x ≠ 0 := by
      rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hne] with x hx hmem
    simp only [Set.mem_sdiff, mem_Iic, mem_Ioc, not_and] at hmem
    have hx0 : x ≤ 0 := by
      by_contra hc
      exact absurd hmem.1 (hmem.2 (not_le.mp hc))
    unfold zeroExtend
    rw [if_neg (by cases lt_or_eq_of_le hx0 with | inl h => linarith | inr h => exact absurd h hx)]
  rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Iic.nullMeasurableSet hsub hdiff]
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  unfold zeroExtend
  rw [if_pos hx.1.le]


open MeasureTheory Set in
/-- **The bridge.**  On the nonnegative ray the full primitive of the zero extension is the
half-line primitive of the profile. -/
theorem integral_Iic_zeroExtend_eq_halfLinePrimitive {F : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in Iic L, zeroExtend F x) = halfLinePrimitive F L := by
  rw [integral_Iic_zeroExtend F L]
  unfold halfLinePrimitive
  rw [intervalIntegral.integral_of_le hL]

open MeasureTheory Set in
/-- **Translating a lower-unbounded window.**  `∫_{Iic L} f(x−t) dx = ∫_{Iic (L−t)} f`.  This is the
step that fails for `Ioc 0 L` — the lower limit `−∞` is fixed by translation, the lower limit `0` is
not — and it is why `(16)` must be stated for the full primitive of the zero extension. -/
theorem setIntegral_Iic_sub_right (f : ℝ → ℝ) (L t : ℝ) :
    (∫ x in Iic L, f (x - t)) = ∫ u in Iic (L - t), f u := by
  have h := MeasureTheory.integral_indicator (μ := volume)
    (f := fun x => f (x - t)) (s := Iic L) measurableSet_Iic
  have h2 := MeasureTheory.integral_indicator (μ := volume)
    (f := f) (s := Iic (L - t)) measurableSet_Iic
  rw [← h, ← h2, ← MeasureTheory.integral_sub_right_eq_self
    (fun x => Set.indicator (Iic (L - t)) f x) t]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (Iic L).indicator (fun y => f (y - t)) x = (Iic (L - t)).indicator f (x - t)
  by_cases hx : x ∈ Iic L
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (by simpa using (mem_Iic.mp hx))]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (by simpa using hx)]

open MeasureTheory Set in
/-- **Truncating a lower-unbounded window at the support.**  A function vanishing below `c`
integrates over `Iic L` exactly as over `Icc c L` — a *bounded* window, where Fubini applies.  This
is the step that makes `(16)` provable despite the profile not being integrable. -/
theorem setIntegral_Iic_eq_Icc_of_vanishing {g : ℝ → ℝ} (c L : ℝ)
    (hzero : ∀ x, x < c → g x = 0) :
    (∫ x in Iic L, g x) = ∫ x in Icc c L, g x := by
  have hsub : Icc c L ⊆ Iic L := fun x hx => mem_Iic.mpr hx.2
  refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Iic.nullMeasurableSet hsub ?_
  filter_upwards with x hx
  simp only [Set.mem_sdiff, mem_Iic, mem_Icc, not_and] at hx
  exact hzero x (by by_contra hcon; exact absurd hx.1 (hx.2 (not_lt.mp hcon)))

open MeasureTheory Set Function in
/-- **The Fubini interchange on a bounded window.**  With the outer window bounded and `ρ`
compactly supported, the product integrand is dominated by `M ‖ρ(t)‖`, which is integrable on the
product because the restricted measure is finite.  This is step 2 of `(16)`. -/
theorem integral_mollify_swap {ρ f : ℝ → ℝ} {c L M : ℝ}
    (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ)
    (hf : Measurable f) (hfb : ∀ x, |f x| ≤ M) :
    (∫ t, ρ t * ∫ x in Icc c L, f (x - t))
      = ∫ x in Icc c L, ∫ t, ρ t * f (x - t) := by
  have hMnn : 0 ≤ M := le_trans (abs_nonneg (f 0)) (hfb 0)
  have hρint : Integrable ρ := hρ.integrable_of_hasCompactSupport hcρ
  have hfin : IsFiniteMeasure (volume.restrict (Icc c L)) := by
    constructor
    simp
  have hmeas : AEStronglyMeasurable (uncurry fun t x => ρ t * f (x - t))
      ((volume : Measure ℝ).prod (volume.restrict (Icc c L))) := by
    refine Measurable.aestronglyMeasurable ?_
    exact (hρ.measurable.comp measurable_fst).mul
      (hf.comp (measurable_snd.sub measurable_fst))
  have hdom : Integrable (fun p : ℝ × ℝ => M * ‖ρ p.1‖)
      ((volume : Measure ℝ).prod (volume.restrict (Icc c L))) :=
    Integrable.comp_fst (hρint.norm.const_mul M) (volume.restrict (Icc c L))
  have hint : Integrable (uncurry fun t x => ρ t * f (x - t))
      ((volume : Measure ℝ).prod (volume.restrict (Icc c L))) := by
    refine hdom.mono' hmeas ?_
    filter_upwards with p
    show ‖ρ p.1 * f (p.2 - p.1)‖ ≤ M * ‖ρ p.1‖
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hfb _) (abs_nonneg _)
  rw [← MeasureTheory.integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  exact (MeasureTheory.integral_const_mul (ρ t) _).symm

open MeasureTheory in
/-- **The mollification inherits a shifted support.**  If the profile vanishes below `0` and the
mollifier is supported in `[−ε, ε]`, the mollification vanishes below `−ε`.  This is what makes the
truncation constant of `(16)` uniform in `t`. -/
theorem mollify_eq_zero_of_lt {ρ f : ℝ → ℝ} {ε x : ℝ}
    (hsupp : ∀ t, ε < |t| → ρ t = 0) (hfz : ∀ y, y < 0 → f y = 0) (hx : x < -ε) :
    mollify ρ f x = 0 := by
  unfold mollify
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun t => ?_)
  show ρ t * f (x - t) = 0
  by_cases ht : ε < |t|
  · rw [hsupp t ht, zero_mul]
  · have ht' : |t| ≤ ε := not_lt.mp ht
    have hlt : x - t < 0 := by
      have h := abs_le.mp ht'
      linarith [h.1]
    rw [hfz _ hlt, mul_zero]

/-! ## `(16)`: the primitive commutes with mollification

Stated for the *full* primitive of a profile vanishing on the negatives — the form in which it is
true.  The proof truncates both sides to a bounded window (uniform in the shift because the
mollifier has bounded support), applies Fubini there, and translates the window back.
-/

open MeasureTheory Set in
/-- **The card's `(16)`.**  `ρ * Y_f = Y_{ρ*f}` for the full primitive of a profile supported in
`[0,∞)`. -/
theorem mollify_fullPrimitive {ρ f : ℝ → ℝ} {ε M : ℝ}
    (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ)
    (hsupp : ∀ t, ε < |t| → ρ t = 0)
    (hf : Measurable f) (hfb : ∀ x, |f x| ≤ M) (hfz : ∀ y, y < 0 → f y = 0) (L₀ : ℝ) :
    mollify ρ (fun L => ∫ x in Iic L, f x) L₀ = ∫ x in Iic L₀, mollify ρ f x := by
  have hRHS : (∫ x in Iic L₀, mollify ρ f x) = ∫ x in Icc (-ε) L₀, mollify ρ f x :=
    setIntegral_Iic_eq_Icc_of_vanishing (-ε) L₀
      (fun x hx => mollify_eq_zero_of_lt hsupp hfz hx)
  have hswap : (∫ x in Icc (-ε) L₀, mollify ρ f x)
      = ∫ t, ρ t * ∫ x in Icc (-ε) L₀, f (x - t) :=
    (integral_mollify_swap hρ hcρ hf hfb).symm
  have hun : (∫ t, ρ t * ∫ x in Icc (-ε) L₀, f (x - t))
      = ∫ t, ρ t * ∫ x in Iic L₀, f (x - t) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show ρ t * (∫ x in Icc (-ε) L₀, f (x - t)) = ρ t * ∫ x in Iic L₀, f (x - t)
    by_cases ht : ε < |t|
    · rw [hsupp t ht, zero_mul, zero_mul]
    · have ht' : |t| ≤ ε := not_lt.mp ht
      have hlow : ∀ x, x < -ε → f (x - t) = 0 := by
        intro x hx
        refine hfz _ ?_
        have h := abs_le.mp ht'
        linarith [h.1]
      rw [setIntegral_Iic_eq_Icc_of_vanishing (-ε) L₀ hlow]
  have halign : (∫ t, ρ t * ∫ x in Iic L₀, f (x - t))
      = ∫ t, ρ t * ∫ x in Iic (L₀ - t), f x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show ρ t * (∫ x in Iic L₀, f (x - t)) = ρ t * ∫ x in Iic (L₀ - t), f x
    rw [setIntegral_Iic_sub_right f L₀ t]
  rw [hRHS, hswap, hun, halign]
  rfl

/-! ## The full-primitive form of the operator

Everything that gets mollified must be phrased with the primitive from `−∞`: the half-line
primitive does not commute with translation, and the mollification of a profile supported in
`[0,∞)` is supported only in `[−ε,∞)`, so no range restriction repairs it.  The conversion to the
half-line primitive happens once, at the end, on the *unmollified* profile where `L ≥ 0` makes the
two agree.
-/

open MeasureTheory Set in
/-- The primitive from `−∞`, the form used throughout the mollification passage. -/
noncomputable def fullPrimitive (f : ℝ → ℝ) (L : ℝ) : ℝ := ∫ x in Iic L, f x

/-- The logarithmic Dirichlet operator built on the full primitive. -/
noncomputable def fullLogDirichlet (f : ℝ → ℝ) (L : ℝ) : ℝ :=
  2 * L * f L - fullPrimitive f L

theorem fullPrimitive_eq_halfLinePrimitive {F : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L) :
    fullPrimitive (zeroExtend F) L = halfLinePrimitive F L :=
  integral_Iic_zeroExtend_eq_halfLinePrimitive hL

theorem mollify_fullPrimitive_eq {ρ f : ℝ → ℝ} {ε M : ℝ}
    (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ)
    (hsupp : ∀ t, ε < |t| → ρ t = 0)
    (hf : Measurable f) (hfb : ∀ x, |f x| ≤ M) (hfz : ∀ y, y < 0 → f y = 0) (L : ℝ) :
    mollify ρ (fullPrimitive f) L = fullPrimitive (mollify ρ f) L :=
  mollify_fullPrimitive hρ hcρ hsupp hf hfb hfz L

open MeasureTheory Set in
/-- **The card's `(17)` in its correct form.**  Stated for the full primitive throughout, so no
range restriction is needed and `hY` is *derived* rather than assumed: the primitive half is
`mollify_fullPrimitive_eq` and the position half is `mollify_position_eq`. -/
theorem fullLogDirichlet_mollify {ρ f : ℝ → ℝ} {ε M : ℝ}
    (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (hsupp : ∀ t, ε < |t| → ρ t = 0)
    (hfc : Continuous f) (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ M)
    (hfz : ∀ y, y < 0 → f y = 0) (hPc : Continuous (fullPrimitive f)) (L : ℝ) :
    fullLogDirichlet (mollify ρ f) L
      = mollify ρ (fullLogDirichlet f) L + 2 * mollify (firstMomentKernel ρ) f L := by
  have hpos := mollify_position_eq ρ f hρ hfc hcρ L
  have hY := mollify_fullPrimitive_eq hρ hcρ hsupp hfm hfb hfz L
  have hlin : mollify ρ (fun Y => 2 * Y * f Y - fullPrimitive f Y) L
      = 2 * mollify ρ (fun y => y * f y) L - mollify ρ (fullPrimitive f) L := by
    unfold mollify
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_sub]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      show ρ t * (2 * (L - t) * f (L - t) - fullPrimitive f (L - t))
        = 2 * (ρ t * ((L - t) * f (L - t))) - ρ t * fullPrimitive f (L - t)
      ring
    · exact (integrable_mollifyKernel hρ (continuous_id.mul hfc) hcρ L).const_mul 2
    · exact integrable_mollifyKernel hρ hPc hcρ L
  unfold fullLogDirichlet
  rw [← hY, hlin, hpos]
  ring

/-! ## Continuity of the full primitive

`fullPrimitive f` is an integral over a varying unbounded window, so no continuity tactic applies.
It is in fact Lipschitz: the difference over `[L', L]` is bounded by `M (L − L')`.
-/

open MeasureTheory Set in
/-- A bounded measurable profile vanishing below the origin is integrable on every `Iic L`, because
the window reduces to `Icc 0 L`. -/
theorem integrableOn_Iic_of_vanishing {f : ℝ → ℝ} {M : ℝ}
    (hf : Measurable f) (hfb : ∀ x, |f x| ≤ M) (hfz : ∀ y, y < 0 → f y = 0) (L : ℝ) :
    IntegrableOn f (Iic L) := by
  have heq : (Iic L).indicator f = (Icc 0 L).indicator f := by
    funext x
    by_cases h1 : x ≤ L
    · by_cases h2 : (0:ℝ) ≤ x
      · rw [Set.indicator_of_mem (mem_Iic.mpr h1), Set.indicator_of_mem (Set.mem_Icc.mpr ⟨h2, h1⟩)]
      · rw [Set.indicator_of_mem (mem_Iic.mpr h1),
          Set.indicator_of_notMem (by simp only [mem_Icc, not_and]; intro hc; exact absurd hc h2)]
        exact hfz x (not_le.mp h2)
    · rw [Set.indicator_of_notMem (by simpa using h1),
        Set.indicator_of_notMem (by simp only [mem_Icc, not_and]; intro _; exact h1)]
  have hIcc : IntegrableOn f (Icc (0:ℝ) L) := by
    have hfin : IsFiniteMeasure (volume.restrict (Icc (0:ℝ) L)) := by
      constructor; simp
    exact Integrable.mono' (integrable_const M) hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hfb x)
  rw [← MeasureTheory.integrable_indicator_iff measurableSet_Iic, heq,
    MeasureTheory.integrable_indicator_iff measurableSet_Icc]
  exact hIcc

open MeasureTheory Set in
/-- The increment of the full primitive is the integral over the intervening window. -/
theorem fullPrimitive_sub {f : ℝ → ℝ} {M : ℝ}
    (hf : Measurable f) (hfb : ∀ x, |f x| ≤ M) (hfz : ∀ y, y < 0 → f y = 0)
    {L' L : ℝ} (h : L' ≤ L) :
    fullPrimitive f L - fullPrimitive f L' = ∫ x in Ioc L' L, f x := by
  have hsplit : Iic L = Iic L' ∪ Ioc L' L := by
    ext x
    simp only [mem_Iic, mem_union, mem_Ioc]
    constructor
    · intro hx
      rcases le_or_gt x L' with hc | hc
      · exact Or.inl hc
      · exact Or.inr ⟨hc, hx⟩
    · rintro (hc | ⟨_, hc⟩)
      · linarith
      · exact hc
  have hdisj : Disjoint (Iic L') (Ioc L' L) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx' (by simp only [mem_Ioc, not_and]; intro hc; linarith [mem_Iic.mp hx])
  have h1 : IntegrableOn f (Iic L') := integrableOn_Iic_of_vanishing hf hfb hfz L'
  have h2 : IntegrableOn f (Ioc L' L) :=
    (integrableOn_Iic_of_vanishing hf hfb hfz L).mono_set fun x hx => mem_Iic.mpr hx.2
  unfold fullPrimitive
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioc h1 h2]
  ring

open MeasureTheory Set in
/-- The full primitive's increment is bounded by the profile's bound times the window length. -/
theorem abs_fullPrimitive_sub_le {f : ℝ → ℝ} {M : ℝ}
    (hf : Measurable f) (hfb : ∀ x, |f x| ≤ M) (hfz : ∀ y, y < 0 → f y = 0) {L' L : ℝ}
    (h : L' ≤ L) : |fullPrimitive f L - fullPrimitive f L'| ≤ M * (L - L') := by
  rw [fullPrimitive_sub hf hfb hfz h]
  have hfin : volume (Ioc L' L) < ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  have hb := norm_setIntegral_le_of_norm_le_const (C := M) hfin
    (fun x _ => by rw [Real.norm_eq_abs]; exact hfb x)
  rw [MeasureTheory.measureReal_def, Real.volume_Ioc,
    ENNReal.toReal_ofReal (by linarith), Real.norm_eq_abs] at hb
  exact hb

open MeasureTheory Set in
/-- **`hPc` discharged.**  The full primitive of a bounded measurable profile vanishing below the
origin is Lipschitz, hence continuous. -/
theorem continuous_fullPrimitive {f : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hf : Measurable f) (hfb : ∀ x, |f x| ≤ M) (hfz : ∀ y, y < 0 → f y = 0) :
    Continuous (fullPrimitive f) := by
  refine LipschitzWith.continuous (K := ⟨M, hM⟩) (LipschitzWith.of_dist_le_mul fun L' L => ?_)
  rw [Real.dist_eq, Real.dist_eq]
  show |fullPrimitive f L' - fullPrimitive f L| ≤ M * |L' - L|
  rcases le_total L' L with h | h
  · rw [abs_sub_comm (fullPrimitive f L'), abs_sub_comm L' L,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ L - L')]
    exact abs_fullPrimitive_sub_le hf hfb hfz h
  · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ L' - L)]
    exact abs_fullPrimitive_sub_le hf hfb hfz h

open MeasureTheory Set in
/-- **The card's `(17)`, hypothesis-free.**  Every input is object regularity of the profile: the
continuity of the full primitive is derived, not assumed. -/
theorem fullLogDirichlet_mollify' {ρ f : ℝ → ℝ} {ε M : ℝ}
    (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (hsupp : ∀ t, ε < |t| → ρ t = 0)
    (hfc : Continuous f) (hfb : ∀ x, |f x| ≤ M) (hfz : ∀ y, y < 0 → f y = 0) (L : ℝ) :
    fullLogDirichlet (mollify ρ f) L
      = mollify ρ (fullLogDirichlet f) L + 2 * mollify (firstMomentKernel ρ) f L := by
  have hM : 0 ≤ M := le_trans (abs_nonneg (f 0)) (hfb 0)
  exact fullLogDirichlet_mollify hρ hcρ hsupp hfc hfc.measurable hfb hfz
    (continuous_fullPrimitive hM hfc.measurable hfb hfz) L

/-! ## `(15)`: the transport operator commutes with mollification

The transport operator is built from translations, so its second difference passes through a
convolution unchanged: the second difference of a mollification is the mollification of the second
difference.  This is the pointwise heart of `(15)`; integrating it against the kernel is a Fubini
step of the same shape as `(16)`.
-/

open MeasureTheory in
/-- **The second difference commutes with mollification.** -/
theorem secondDifference_mollify {ρ f : ℝ → ℝ} (hρ : Continuous ρ) (hf : Continuous f)
    (hcρ : HasCompactSupport ρ) (L s : ℝ) :
    secondDifference (mollify ρ f) L s = mollify ρ (fun y => secondDifference f y s) L := by
  have i0 := integrable_mollifyKernel hρ hf hcρ L
  have i1 := integrable_mollifyKernel hρ hf hcρ (L + s)
  have i2 := integrable_mollifyKernel hρ hf hcρ (L - s)
  unfold secondDifference mollify
  have e1 : Integrable (fun t => 2 * (ρ t * f (L - t)) - ρ t * f (L + s - t)) :=
    (i0.const_mul 2).sub i1
  rw [← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_sub ((i0.const_mul 2)) i1,
    ← MeasureTheory.integral_sub e1 i2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show 2 * (ρ t * f (L - t)) - ρ t * f (L + s - t) - ρ t * f (L - s - t)
    = ρ t * (2 * f (L - t) - f (L - t + s) - f (L - t - s))
  rw [show L - t + s = L + s - t by ring, show L - t - s = L - s - t by ring]
  ring

/-! ## The uniform majorant for `(15)`

The transport integrand is bounded, **uniformly in the base point**, by a constant near the origin
and by an exponential beyond.  Uniformity is what makes the Fubini majorant for `(15)` exist: the
base point is the convolution variable, so a `y`-dependent bound would be useless.
-/

/-- Near the origin the Lipschitz bound cancels the pole, leaving the constant `2K`. -/
theorem abs_secondDifference_mul_kernel_le_near {f : ℝ → ℝ} {K : ℝ}
    (hK : ∀ x y, |f x - f y| ≤ K * |x - y|) {y s : ℝ} (hs : 0 < s) :
    |secondDifference f y s * gammaTransportKernel s| ≤ 2 * K := by
  have hk : 0 < gammaTransportKernel s := gammaTransportKernel_pos hs
  have hsd := abs_secondDifference_le_of_lipschitz hK y s
  have hinv := gammaTransportKernel_le_inv hs
  rw [abs_mul, abs_of_pos hk]
  have hK0 : 0 ≤ K := by
    have h := hK 1 0
    rw [show |(1:ℝ) - 0| = 1 by norm_num, mul_one] at h
    linarith [abs_nonneg (f 1 - f 0)]
  rw [abs_of_pos hs] at hsd
  calc |secondDifference f y s| * gammaTransportKernel s
      ≤ (2 * K * s) * (1 / s) := by
        refine mul_le_mul hsd hinv hk.le (by positivity)
    _ = 2 * K := by field_simp

/-- Beyond `s = 1` boundedness and the exponential tail give `8M e^{−s}`. -/
theorem abs_secondDifference_mul_kernel_le_far {f : ℝ → ℝ} {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) {y s : ℝ} (hs : 1 ≤ s) :
    |secondDifference f y s * gammaTransportKernel s| ≤ 8 * M * Real.exp (-s) := by
  have hs0 : 0 < s := by linarith
  have hk : 0 < gammaTransportKernel s := gammaTransportKernel_pos hs0
  have hsd := abs_secondDifference_le_of_bounded hM y s
  have htail := gammaTransportKernel_le_two_mul_exp_neg hs
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (f 0)) (hM 0)
  rw [abs_mul, abs_of_pos hk]
  calc |secondDifference f y s| * gammaTransportKernel s
      ≤ (4 * M) * (2 * Real.exp (-s)) := by
        refine mul_le_mul hsd htail hk.le (by linarith)
    _ = 8 * M * Real.exp (-s) := by ring

end GaloisForLFunctions.HTGeometry
