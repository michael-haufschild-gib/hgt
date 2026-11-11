import GaloisForLFunctions.FloorFreeArithmetic.FiniteTopLayersAreSeenOnEveryWindow
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.LengthDependentFloorsGiveTheAbscissaLaw

/-!
# The top trace determines the top layer

The **tangent datum** of a configuration at a depth `b` is what its trace keeps after
normalization by `e^{bu}`: the top trace `Σ_{Re z = b} e_z e^{i Im z · u}`, an absolutely
convergent trigonometric series. Its Bohr coefficient at a frequency `λ` is the spline
coefficient `e_{b + iλ}` of the layer, so the datum is the family of these coefficients and
nothing else of the configuration survives the normalization.

* `bohrCoefficient_topTraceC`: the Bohr coefficients of the top trace.
* `tendsto_normTrace_zero_iff`: the normalized trace tends to zero exactly when the top line is
  empty. Non-attainment in the strong sense is the absence of a top layer, finite or not.
* `topCoeff_eq_of_tendsto_normTrace_sub`: two configurations whose normalized traces differ by
  `o(1)` have the same top coefficients: the tangent trace determines the top layer.
* `tendsto_normTrace_zero_or_attained`, `windowNonAttainment_forall_iff_tendsto`: the attainment
  dichotomy. Either the normalized trace tends to zero or it is attained on every late window of
  some fixed length; non-attainment on windows of every length is the first alternative.
* `tendsto_normTrace_zeta_zero_iff`, `windowNonAttainment_zeta_forall_iff`: for `ζ` and a depth
  `b > 0` bounding all zeros, the trace is `o(e^{bu})` if and only if no zero has real part
  `½ + b`, if and only if it is non-attained on windows of every length.
* `zeta_top_line_empty_or_infinite_of_windowNonAttainment`: non-attainment on windows of one
  length leaves the top line empty or infinite, even when other zeros accumulate at it: more
  than the abscissa law.
* `asymptoticAbscissaLaw_of_tendsto_normTrace_zero`: strong non-attainment at every such depth
  gives the asymptotic abscissa law.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

open SquareRootThreshold Zeta23 SurfaceOfSpecZ SurfaceOfSpecZ.ScaleLocality
open ArithmeticCastelnuovoSeveri

variable {Z Z' : ZeroConfig} {b : ℝ}

/-! ### The Bohr coefficients of the top trace -/

/-- The complex top trace is the real top trace. -/
theorem ofReal_topTrace (Z : ZeroConfig) (b u : ℝ) :
    ((topTrace Z b u : ℝ) : ℂ) = topTraceC Z b u := by
  apply Complex.ext
  · rw [Complex.ofReal_re, topTrace_eq_re]
  · rw [Complex.ofReal_im, topTraceC_im]

/-- **The tangent datum.** The Bohr coefficient of the top trace at the frequency `λ` is the
spline coefficient of the point `b + iλ`. -/
theorem bohrCoefficient_topTraceC (hZ : TemperedConfig Z) (lam : ℝ) :
    bohrCoefficient (topTraceC Z b) lam = evenCoeff Z (boxSpline 1 3) ⟨b, lam⟩ := by
  classical
  refine eq_of_sub_eq_zero (norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε => ?_))
  obtain ⟨S₀, hS₀⟩ := exists_finset_topTraceC_approx (b := b) hZ hε
  set S : Finset ℂ := insert (⟨b, lam⟩ : ℂ) S₀ with hS
  have happrox := hS₀ S (Finset.subset_insert _ _)
  have hsum : bohrCoefficient (fun u => ∑ z ∈ S, topTerm Z b z u) lam =
      evenCoeff Z (boxSpline 1 3) ⟨b, lam⟩ := by
    rw [bohrCoefficient_finset_sum S (fun z => continuous_topTerm z)
      (fun z => isBohrAlmostPeriodic_topTerm z) lam,
      Finset.sum_eq_single (⟨b, lam⟩ : ℂ)]
    · rw [bohrCoefficient_topTerm, if_pos ⟨rfl, rfl⟩]
    · intro z _ hz
      rw [bohrCoefficient_topTerm, if_neg]
      rintro ⟨hre, him⟩
      exact hz (Complex.ext hre him.symm)
    · intro hnot
      exact absurd (Finset.mem_insert_self _ _) hnot
  have hlip := norm_bohrCoefficient_sub_le (continuous_topTraceC hZ)
    (isBohrAlmostPeriodic_topTraceC hZ) (continuous_topTerm_sum (Z := Z) (b := b) S)
    (isBohrAlmostPeriodic_topTerm_sum S) happrox lam
  rw [hsum] at hlip
  linarith only [hlip]

/-- The top coefficients vanish when the top trace does. -/
theorem topCoeff_eq_zero_of_topTraceC_eq_zero (hZ : TemperedConfig Z)
    (h : ∀ u, topTraceC Z b u = 0) {z : ℂ} (hz : z.re = b) :
    evenCoeff Z (boxSpline 1 3) z = 0 := by
  have hzero : topTraceC Z b = fun _ => 0 := funext h
  have hcoef := bohrCoefficient_topTraceC (b := b) hZ z.im
  rw [hzero] at hcoef
  have h0 : bohrCoefficient (fun _ : ℝ => (0 : ℂ)) z.im = 0 := by
    unfold bohrCoefficient
    simp only [zero_mul]
    exact bohrMean_zero
  have hpt : (⟨b, z.im⟩ : ℂ) = z := Complex.ext hz.symm rfl
  rw [← hpt, ← hcoef, h0]

/-- The top trace of an empty top line vanishes. -/
theorem topTrace_eq_zero_of_topCoeff_eq_zero
    (h : ∀ z : ℂ, z.re = b → evenCoeff Z (boxSpline 1 3) z = 0) (u : ℝ) :
    topTrace Z b u = 0 := by
  unfold topTrace
  have hterm : (fun z : ℂ => if z.re = b then
      evenCoeff Z (boxSpline 1 3) z * cexp ((z - b) * u) else 0) = fun _ => 0 := by
    funext z
    split_ifs with hz
    · rw [h z hz, zero_mul]
    · rfl
  rw [hterm, tsum_zero, Complex.zero_re]

/-! ### Strong non-attainment is an empty top line -/

/-- **The normalized trace tends to zero exactly when the top line is empty.** -/
theorem tendsto_normTrace_zero_iff (hZ : TemperedConfig Z) (htop : TopDepth Z b) :
    Tendsto (normTrace Z b) atTop (𝓝 0) ↔
      ∀ z : ℂ, z.re = b → evenCoeff Z (boxSpline 1 3) z = 0 := by
  have hrem := tendsto_normTrace_sub_topTrace hZ htop
  constructor
  · intro hnorm z hz
    -- the top trace tends to zero, and it is almost periodic
    have htt : Tendsto (topTrace Z b) atTop (𝓝 0) := by
      have := hnorm.sub hrem
      simpa using this
    have htc : Tendsto (topTraceC Z b) atTop (𝓝 0) := by
      have h1 := (Complex.continuous_ofReal.tendsto 0).comp htt
      simpa only [Function.comp_def, ofReal_topTrace, Complex.ofReal_zero] using h1
    exact topCoeff_eq_zero_of_topTraceC_eq_zero hZ
      (_root_.HTGeometry.eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero
        (isBohrAlmostPeriodic_topTraceC hZ) htc) hz
  · intro hzero
    have h0 : ∀ u, topTrace Z b u = 0 := topTrace_eq_zero_of_topCoeff_eq_zero hzero
    simpa only [h0, sub_zero] using hrem

/-- **The tangent trace determines the top layer.** Two tempered configurations of depth at
most `b` whose normalized traces differ by `o(1)` have the same spline coefficients on the top
line. -/
theorem topCoeff_eq_of_tendsto_normTrace_sub (hZ : TemperedConfig Z) (hZ' : TemperedConfig Z')
    (htop : TopDepth Z b) (htop' : TopDepth Z' b)
    (h : Tendsto (fun u => normTrace Z b u - normTrace Z' b u) atTop (𝓝 0)) {z : ℂ}
    (hz : z.re = b) :
    evenCoeff Z (boxSpline 1 3) z = evenCoeff Z' (boxSpline 1 3) z := by
  have hrem := tendsto_normTrace_sub_topTrace hZ htop
  have hrem' := tendsto_normTrace_sub_topTrace hZ' htop'
  have htt : Tendsto (fun u => topTrace Z b u - topTrace Z' b u) atTop (𝓝 0) := by
    have h1 := (h.sub hrem).add hrem'
    simp only [sub_zero, add_zero] at h1
    refine h1.congr fun u => ?_
    ring
  have htc : Tendsto (fun u => topTraceC Z b u - topTraceC Z' b u) atTop (𝓝 0) := by
    have h1 := (Complex.continuous_ofReal.tendsto 0).comp htt
    simpa only [Function.comp_def, Complex.ofReal_sub, ofReal_topTrace, Complex.ofReal_zero]
      using h1
  have hvan := _root_.HTGeometry.eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero
    (isBohrAlmostPeriodic_sub (continuous_topTraceC hZ) (isBohrAlmostPeriodic_topTraceC hZ)
      (continuous_topTraceC hZ') (isBohrAlmostPeriodic_topTraceC hZ')) htc
  have heq : topTraceC Z b = topTraceC Z' b := funext fun u => sub_eq_zero.mp (hvan u)
  have hpt : (⟨b, z.im⟩ : ℂ) = z := Complex.ext hz.symm rfl
  rw [← hpt, ← bohrCoefficient_topTraceC (b := b) hZ z.im,
    ← bohrCoefficient_topTraceC (b := b) hZ' z.im, heq]

/-! ### The attainment dichotomy -/

/-- An almost periodic function that is not identically zero is at least `c > 0` in norm
somewhere on every window of some fixed length. -/
theorem exists_window_le_norm_of_isBohrAlmostPeriodic {f : ℝ → ℂ}
    (hap : _root_.HTGeometry.IsBohrAlmostPeriodic f) {x₀ : ℝ} (hx₀ : f x₀ ≠ 0) :
    ∃ L c : ℝ, 0 < L ∧ 0 < c ∧ ∀ T : ℝ, ∃ u ∈ Icc T (T + L), c ≤ ‖f u‖ := by
  have hc0 : 0 < ‖f x₀‖ / 2 := half_pos (norm_pos_iff.mpr hx₀)
  obtain ⟨L, hL, hdense⟩ := hap (‖f x₀‖ / 2) hc0
  refine ⟨L, ‖f x₀‖ / 2, hL, hc0, fun T => ?_⟩
  obtain ⟨τ, hτ, hclose⟩ := hdense (T - x₀)
  refine ⟨x₀ + τ, ⟨by linarith only [hτ.1], by linarith only [hτ.2]⟩, ?_⟩
  have h1 := hclose x₀
  have h2 := norm_sub_norm_le (f x₀) (f (x₀ + τ))
  rw [norm_sub_rev] at h2
  linarith only [h1, h2]

/-- **The attainment dichotomy.** At a depth bounding the configuration, either the normalized
trace tends to zero, or it is attained: at least `c > 0` in absolute value somewhere on every
late window of some fixed length. -/
theorem tendsto_normTrace_zero_or_attained (hZ : TemperedConfig Z) (htop : TopDepth Z b) :
    Tendsto (normTrace Z b) atTop (𝓝 0) ∨
      ∃ L c U : ℝ, 0 < L ∧ 0 < c ∧ ∀ T : ℝ, U ≤ T →
        ∃ u ∈ Icc T (T + L), c ≤ |normTrace Z b u| := by
  by_cases h : ∀ u, topTraceC Z b u = 0
  · exact Or.inl ((tendsto_normTrace_zero_iff hZ htop).mpr fun z hz =>
      topCoeff_eq_zero_of_topTraceC_eq_zero hZ h hz)
  · right
    push Not at h
    obtain ⟨x₀, hx₀⟩ := h
    obtain ⟨L, c, hL, hc, hatt⟩ :=
      exists_window_le_norm_of_isBohrAlmostPeriodic (isBohrAlmostPeriodic_topTraceC hZ) hx₀
    have hrem := tendsto_normTrace_sub_topTrace hZ htop
    obtain ⟨V, hV⟩ := eventually_atTop.mp
      ((tendsto_order.mp hrem).1 (-(c / 2)) (by linarith only [hc]) |>.and
        ((tendsto_order.mp hrem).2 (c / 2) (by linarith only [hc])))
    refine ⟨L, c / 2, V, hL, half_pos hc, fun T hT => ?_⟩
    obtain ⟨u, hu, hbig⟩ := hatt T
    refine ⟨u, hu, ?_⟩
    obtain ⟨hlo, hhi⟩ := hV u (hT.trans hu.1)
    have hn : ‖topTraceC Z b u‖ = |topTrace Z b u| := by
      rw [← ofReal_topTrace, Complex.norm_real, Real.norm_eq_abs]
    rw [hn] at hbig
    have htri := abs_sub_abs_le_abs_sub (topTrace Z b u) (normTrace Z b u)
    have hsmall : |topTrace Z b u - normTrace Z b u| ≤ c / 2 := by
      rw [abs_sub_comm]
      exact abs_le.mpr ⟨hlo.le, hhi.le⟩
    linarith only [hbig, htri, hsmall]

/-- **Non-attainment on windows of every length is the vanishing of the normalized trace.** -/
theorem windowNonAttainment_forall_iff_tendsto (hZ : TemperedConfig Z) (htop : TopDepth Z b) :
    (∀ L : ℝ, 0 < L → WindowNonAttainment Z b L) ↔ Tendsto (normTrace Z b) atTop (𝓝 0) := by
  constructor
  · intro hN
    rcases tendsto_normTrace_zero_or_attained hZ htop with h | ⟨L, c, U, hL, hc, hatt⟩
    · exact h
    · exfalso
      obtain ⟨T, hT, hsmall⟩ := hN L hL (c / 2) (half_pos hc) U
      obtain ⟨u, hu, hbig⟩ := hatt T hT
      linarith only [hsmall u hu, hbig, hc]
  · intro hlim L _ ε hε U
    obtain ⟨V, hV⟩ := eventually_atTop.mp
      ((tendsto_order.mp hlim).1 (-ε) (by linarith only [hε]) |>.and
        ((tendsto_order.mp hlim).2 ε hε))
    refine ⟨max U V, le_max_left _ _, fun u hu => ?_⟩
    obtain ⟨hlo, hhi⟩ := hV u ((le_max_right U V).trans hu.1)
    exact abs_le.mpr ⟨hlo.le, hhi.le⟩

/-! ### The zeta function -/

/-- **Strong non-attainment for `ζ`.** For a depth `b > 0` bounding all zeros, the spline
trace is `o(e^{bu})` if and only if no zero of `ζ` has real part `½ + b`. -/
theorem tendsto_normTrace_zeta_zero_iff (hb : 0 < b) (htop : TopDepth zetaZeroConfig b) :
    Tendsto (normTrace zetaZeroConfig b) atTop (𝓝 0) ↔
      ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2 + b := by
  rw [tendsto_normTrace_zero_iff temperedConfig_zetaZeroConfig htop]
  constructor
  · intro hzero ρ hρ hre
    have hgt : 1 / 2 < ρ.re := by linarith only [hre, hb]
    have hsee := evenCoeff_spline_sees hρ hgt
    have hreb : (ρ - 1 / 2).re = b := by
      have he : (ρ - 1 / 2).re = ρ.re - 1 / 2 := by simp
      rw [he, hre]
      ring
    exact hsee (hzero _ hreb)
  · intro hnone z hz
    by_contra hne
    have hmem := add_half_mem_zetaZeroConfig_of_evenCoeff_ne_zero hne
    have he : ((1 / 2 : ℂ) + z).re = 1 / 2 + z.re := by norm_num
    exact hnone _ hmem (by rw [he, hz])

/-- For `ζ` at a depth `b > 0` bounding all zeros: the trace is non-attained on windows of every
length if and only if no zero has real part `½ + b`. -/
theorem windowNonAttainment_zeta_forall_iff (hb : 0 < b) (htop : TopDepth zetaZeroConfig b) :
    (∀ L : ℝ, 0 < L → WindowNonAttainment zetaZeroConfig b L) ↔
      ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2 + b := by
  rw [windowNonAttainment_forall_iff_tendsto temperedConfig_zetaZeroConfig htop,
    tendsto_normTrace_zeta_zero_iff hb htop]

/-- **One window length empties every finite top line.** If the trace of `ζ` is non-attained on
windows of one length `L` at a depth `b > 0` bounding all zeros, the zeros on the line
`Re s = ½ + b` are none or infinitely many, whether or not other zeros accumulate at that
line. -/
theorem zeta_top_line_empty_or_infinite_of_windowNonAttainment (hb : 0 < b)
    (htop : TopDepth zetaZeroConfig b) {L : ℝ} (hL : 0 < L)
    (hN : WindowNonAttainment zetaZeroConfig b L) :
    (∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2 + b) ∨
      {ρ : ℂ | ρ ∈ zetaZeroConfig.carrier ∧ ρ.re = 1 / 2 + b}.Infinite := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨ρ₀, hρ₀, hre₀⟩, hfin⟩ := hcon
  have he : ∀ z : ℂ, ((1 / 2 : ℂ) + z).re = 1 / 2 + z.re := fun z => by norm_num
  -- the positive top support is finite: it embeds into the zeros of the line
  have hfinite : (positiveTopSupport zetaZeroConfig b).Finite := by
    apply (hfin.preimage (f := fun z : ℂ => (1 / 2 : ℂ) + z)
      (add_right_injective (1 / 2 : ℂ)).injOn).subset
    intro z hz
    exact ⟨add_half_mem_zetaZeroConfig_of_evenCoeff_ne_zero hz.2.2, by rw [he, hz.1]⟩
  -- and nonempty: the zero of the line, or its conjugate, has a positive ordinate
  have hnonempty : (positiveTopSupport zetaZeroConfig b).Nonempty := by
    have hsee := evenCoeff_spline_sees hρ₀ (by linarith only [hre₀, hb])
    have hzre : (ρ₀ - 1 / 2).re = b := by
      have h1 : (ρ₀ - 1 / 2).re = ρ₀.re - 1 / 2 := by simp
      rw [h1, hre₀]
      ring
    rcases lt_or_gt_of_ne (evenCoeff_spline_real hsee) with hn | hp
    · refine ⟨conj (ρ₀ - 1 / 2), ?_⟩
      refine ⟨by simpa only [Complex.conj_re] using hzre,
        by simpa only [Complex.conj_im] using neg_pos.mpr hn, ?_⟩
      rw [SurfaceOfSpecZ.evenCoeff_conj]
      intro hzero
      exact hsee (by simpa only [Complex.conj_conj, map_zero] using congrArg conj hzero)
    · exact ⟨ρ₀ - 1 / 2, hzre, hp, hsee⟩
  exact not_windowNonAttainment_of_finite_top temperedConfig_zetaZeroConfig htop hL
    hfinite.toFinset (fun z => Set.Finite.mem_toFinset hfinite)
    (hfinite.toFinset_nonempty.mpr hnonempty) (fun z hz _ => evenCoeff_spline_real hz) hN

/-- **Strong non-attainment gives the abscissa law.** If for every depth `b > 0` bounding all
zeros the spline trace is `o(e^{bu})`, the asymptotic abscissa law holds. -/
theorem asymptoticAbscissaLaw_of_tendsto_normTrace_zero
    (h : ∀ b : ℝ, 0 < b → TopDepth zetaZeroConfig b →
      Tendsto (normTrace zetaZeroConfig b) atTop (𝓝 0)) :
    _root_.RHTower.AsymptoticAbscissaLaw := by
  by_contra hnot
  obtain ⟨b, hb, htop, S, hS, hne⟩ := exists_finite_top_of_not_abscissaLaw hnot
  obtain ⟨z, hz⟩ := hne
  obtain ⟨hre, -, hcoef⟩ := (hS z).mp hz
  exact hcoef
    ((tendsto_normTrace_zero_iff temperedConfig_zetaZeroConfig htop).mp (h b hb htop) z hre)

end GaloisForLFunctions.FloorFreeArithmetic
