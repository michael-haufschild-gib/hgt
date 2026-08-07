import GaloisForLFunctions.HTGeometry.HalfLogCesaroAverage
import GaloisForLFunctions.HTGeometry.GammaTransportKernel

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
    (hA : Tendsto (halfLogAverage F) atTop (nhds α))
    (hb : IsBoundedUnder (· ≤ ·) atTop fun L => Real.sqrt L * F L)
    (hb' : IsBoundedUnder (· ≥ ·) atTop fun L => Real.sqrt L * F L)
    (hcb : IsCoboundedUnder (· ≤ ·) atTop fun L => Real.sqrt L * F L)
    (hcb' : IsCoboundedUnder (· ≥ ·) atTop fun L => Real.sqrt L * F L) :
    Tendsto (fun L => Real.sqrt L * F L) atTop (nhds α) := by
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

end GaloisForLFunctions.HTGeometry
