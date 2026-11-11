import GaloisForLFunctions.FloorFreeArithmetic.TheTopTraceDeterminesTheTopLayer
import GaloisForLFunctions.FloorFreeArithmetic.NonAttainmentIsALawOfConfigurations
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa

/-!
# The spline trace classification at the zero abscissa

At the zero abscissa `Θ = zetaZeroAbscissa` of `ζ`, let `b_* = Θ − ½ ≥ 0` and consider the
normalized cubic-spline trace `G(u) = normTrace zetaZeroConfig b_* u = 2 Re S(u) e^{−b_* u}`.
At any bounding depth `b` of a tempered configuration `Z`, `normTrace Z b − topTrace Z b → 0`,
and the Bohr spectrum of `topTraceC Z b` identifies the asymptotic behaviour of `normTrace Z b`
with the cardinality of the active top layer `{z : Re z = b, e_z ≠ 0}`:

* `tendsto_normTrace_sub_trigPoly_iff_finite_activeTop`: `normTrace Z b` approaches a real
  finite trigonometric polynomial at `+∞` if and only if the active top layer is finite, in
  which case the limiting trigonometric polynomial is `topTrace Z b` itself.
* `tendsto_normTrace_sub_nonzero_trigPoly_iff`: `normTrace Z b` approaches a nonzero real
  finite trigonometric polynomial at `+∞` if and only if the active top layer is finite and
  nonempty.
* `zetaNormTrace_quadrichotomy`: unconditionally, `G` falls into four mutually exclusive
  sectors:
  1. `RiemannHypothesis` (`Θ = ½`), where `G = topTrace zetaZeroConfig 0` is identically Bohr
     almost periodic;
  2. `Θ > ½` with empty top line `Re ρ = Θ`, where `G(u) → 0`;
  3. `Θ > ½` with finite nonempty top line `Re ρ = Θ`, where `G` approaches a nonzero real
     finite trigonometric polynomial;
  4. `Θ > ½` with infinite top line `Re ρ = Θ`, where `G − T ↛ 0` for every real finite
     trigonometric polynomial `T` (in particular `G(u) ↛ 0`).
* `zeta_abscissaLaw_of_no_nonzero_trigPoly_limit`: for `ζ`, excluding nonzero finite
  trigonometric-polynomial limits when `Θ > ½` is equivalent to the top line being empty or
  infinite, and unconditionally implies `AsymptoticAbscissaLaw`.
* `exists_tempered_abscissaLaw_infinite_top`, `exists_tempered_abscissaLaw_nonzero_trigPoly_limit`:
  on tempered conjugation-symmetric configurations without real zeros, the three off-line laws
  (`normTrace → 0`, no nonzero trigonometric-polynomial limit, and `AbscissaLaw`) are strictly
  separated at every depth `0 < b ≤ ½`. In particular, `AbscissaLaw` (`Θ_∞ = Θ`) does not by
  itself exclude convergence of `normTrace` to a nonzero finite trigonometric polynomial when
  sub-top zeros accumulate at `Θ` from the left beneath a finite nonempty top layer.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

open SquareRootThreshold Zeta23 SurfaceOfSpecZ SurfaceOfSpecZ.ScaleLocality
open ArithmeticCastelnuovoSeveri
open ZeroConfigurationGeometry ZeroConfigurationGeometry.ConfigAbscissa

/-! ### Real finite trigonometric polynomials and their Bohr spectrum -/

/-- A real finite trigonometric polynomial `T(u) = Re (∑_{ω ∈ S} c(ω) e^{iωu})`. -/
def IsRealTrigPoly (T : ℝ → ℝ) : Prop :=
  ∃ (S : Finset ℝ) (c : ℝ → ℂ), ∀ u : ℝ,
    T u = (∑ ω ∈ S, c ω * bohrExp ω u).re

/-- The zero function is a real finite trigonometric polynomial. -/
theorem isRealTrigPoly_zero : IsRealTrigPoly (fun _ => 0) :=
  ⟨∅, fun _ => 0, fun _ => by simp⟩

/-- A conjugate pair of pure imaginary exponentials `(c/2) e^{iωu} + (c̄/2) e^{−iωu}`. -/
private def trigTerm (c : ℂ) (ω u : ℝ) : ℂ :=
  (c / 2) * bohrExp ω u + (conj c / 2) * bohrExp (-ω) u

private theorem trigTerm_eq_ofReal_re (c : ℂ) (ω u : ℝ) :
    (((c * bohrExp ω u).re : ℝ) : ℂ) = trigTerm c ω u := by
  have hre : ∀ w : ℂ, ((w.re : ℝ) : ℂ) = (w + conj w) / 2 := fun w => by
    apply Complex.ext <;> simp
  have hconj_exp : conj (bohrExp ω u) = bohrExp (-ω) u := by
    rw [bohrExp_apply, bohrExp_apply, ← Complex.exp_conj]
    congr 1
    simp
  rw [hre, map_mul, hconj_exp, trigTerm]
  ring

/-- Complexification of `Re (∑_{ω ∈ S} c(ω) e^{iωu})` as a sum of `trigTerm`s. -/
theorem ofReal_re_sum_bohrExp (S : Finset ℝ) (c : ℝ → ℂ) (u : ℝ) :
    (((∑ ω ∈ S, c ω * bohrExp ω u).re : ℝ) : ℂ) = ∑ ω ∈ S, trigTerm (c ω) ω u := by
  classical
  refine Finset.induction_on S (by simp) fun ω₀ S' hnot ih => ?_
  rw [Finset.sum_insert hnot, Finset.sum_insert hnot, Complex.add_re, Complex.ofReal_add,
    trigTerm_eq_ofReal_re, ih]

private theorem continuous_trigTerm (c : ℂ) (ω : ℝ) : Continuous (trigTerm c ω) :=
  (continuous_const.mul (continuous_bohrExp ω)).add
    (continuous_const.mul (continuous_bohrExp (-ω)))

private theorem isBohrAlmostPeriodic_trigTerm (c : ℂ) (ω : ℝ) :
    _root_.HTGeometry.IsBohrAlmostPeriodic (trigTerm c ω) :=
  isBohrAlmostPeriodic_add
    (continuous_const.mul (continuous_bohrExp ω))
    (isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_bohrExp ω))
    (continuous_const.mul (continuous_bohrExp (-ω)))
    (isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_bohrExp (-ω)))

theorem continuous_ofReal_of_isRealTrigPoly {T : ℝ → ℝ} (hT : IsRealTrigPoly T) :
    Continuous fun u : ℝ => ((T u : ℝ) : ℂ) := by
  obtain ⟨S, c, hTc⟩ := hT
  have heq : (fun u : ℝ => ((T u : ℝ) : ℂ)) = fun u : ℝ => ∑ ω ∈ S, trigTerm (c ω) ω u := by
    funext u; rw [hTc u, ofReal_re_sum_bohrExp]
  rw [heq]
  exact continuous_finsetSum S fun ω _ => continuous_trigTerm (c ω) ω

theorem isBohrAlmostPeriodic_ofReal_of_isRealTrigPoly {T : ℝ → ℝ} (hT : IsRealTrigPoly T) :
    _root_.HTGeometry.IsBohrAlmostPeriodic fun u : ℝ => ((T u : ℝ) : ℂ) := by
  obtain ⟨S, c, hTc⟩ := hT
  have heq : (fun u : ℝ => ((T u : ℝ) : ℂ)) = fun u : ℝ => ∑ ω ∈ S, trigTerm (c ω) ω u := by
    funext u; rw [hTc u, ofReal_re_sum_bohrExp]
  rw [heq]
  exact isBohrAlmostPeriodic_sum S (fun ω _ => continuous_trigTerm (c ω) ω)
    (fun ω _ => isBohrAlmostPeriodic_trigTerm (c ω) ω)

private theorem bohrCoefficient_const_mul_bohrExp (a : ℂ) (ω lam : ℝ) :
    bohrCoefficient (fun u => a * bohrExp ω u) lam = if lam = ω then a else 0 := by
  unfold bohrCoefficient
  have e : (fun t => a * bohrExp ω t * bohrChar lam t) =
      fun t => a * (bohrExp ω t * bohrChar lam t) := by
    funext t; ring
  rw [e, bohrMean_const_mul (f := fun t => bohrExp ω t * bohrChar lam t) a
    ((continuous_bohrExp ω).mul (continuous_bohrChar lam))
    (isBohrAlmostPeriodic_mul_bohrChar (continuous_bohrExp ω)
      (isBohrAlmostPeriodic_bohrExp ω) lam)]
  have hc := bohrCoefficient_bohrExp ω lam
  unfold bohrCoefficient at hc
  rw [hc]
  by_cases h : lam = ω <;> simp [h]

private theorem bohrCoefficient_trigTerm_eq_zero (c : ℂ) {ω lam : ℝ}
    (h1 : lam ≠ ω) (h2 : lam ≠ -ω) :
    bohrCoefficient (trigTerm c ω) lam = 0 := by
  unfold bohrCoefficient trigTerm
  have hmul : (fun t => ((c / 2) * bohrExp ω t + (conj c / 2) * bohrExp (-ω) t) * bohrChar lam t) =
      fun t => ((c / 2) * bohrExp ω t) * bohrChar lam t +
        ((conj c / 2) * bohrExp (-ω) t) * bohrChar lam t := by
    funext t; ring
  have hc1 : Continuous fun t => (c / 2) * bohrExp ω t :=
    continuous_const.mul (continuous_bohrExp ω)
  have hc2 : Continuous fun t => (conj c / 2) * bohrExp (-ω) t :=
    continuous_const.mul (continuous_bohrExp (-ω))
  have ha1 := isBohrAlmostPeriodic_const_mul (c / 2) (isBohrAlmostPeriodic_bohrExp ω)
  have ha2 := isBohrAlmostPeriodic_const_mul (conj c / 2) (isBohrAlmostPeriodic_bohrExp (-ω))
  have hm1 : Continuous fun t => ((c / 2) * bohrExp ω t) * bohrChar lam t :=
    hc1.mul (continuous_bohrChar lam)
  have hm2 : Continuous fun t => ((conj c / 2) * bohrExp (-ω) t) * bohrChar lam t :=
    hc2.mul (continuous_bohrChar lam)
  rw [hmul, bohrMean_add hm1 (isBohrAlmostPeriodic_mul_bohrChar hc1 ha1 lam)
    hm2 (isBohrAlmostPeriodic_mul_bohrChar hc2 ha2 lam)]
  have hb1 := bohrCoefficient_const_mul_bohrExp (c / 2) ω lam
  have hb2 := bohrCoefficient_const_mul_bohrExp (conj c / 2) (-ω) lam
  unfold bohrCoefficient at hb1 hb2
  rw [hb1, if_neg h1, hb2, if_neg h2, add_zero]

/-- A real finite trigonometric polynomial has only finitely many nonzero Bohr frequencies. -/
theorem finite_bohrSupport_of_isRealTrigPoly {T : ℝ → ℝ} (hT : IsRealTrigPoly T) :
    {lam : ℝ | bohrCoefficient (fun u : ℝ => ((T u : ℝ) : ℂ)) lam ≠ 0}.Finite := by
  classical
  obtain ⟨S, c, hTc⟩ := hT
  refine ((S ∪ S.image Neg.neg).finite_toSet).subset fun lam hlam => ?_
  by_contra hnot
  rw [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_coe, not_or] at hnot
  obtain ⟨hnotS, hnotNeg⟩ := hnot
  apply hlam
  have heq : (fun u : ℝ => ((T u : ℝ) : ℂ)) = fun u : ℝ => ∑ ω ∈ S, trigTerm (c ω) ω u := by
    funext u; rw [hTc u, ofReal_re_sum_bohrExp]
  rw [heq, bohrCoefficient_finset_sum S (fun ω => continuous_trigTerm (c ω) ω)
    (fun ω => isBohrAlmostPeriodic_trigTerm (c ω) ω) lam]
  refine Finset.sum_eq_zero fun ω hω => bohrCoefficient_trigTerm_eq_zero (c ω) ?_ ?_
  · rintro rfl; exact hnotS hω
  · intro he
    exact hnotNeg (Finset.mem_image.mpr ⟨ω, hω, by linarith only [he]⟩)

/-! ### Active top layer vs trigonometric-polynomial asymptotics -/

/-- The active top exponents of `Z` at depth `b`: `{z : Re z = b ∧ e_z ≠ 0}`. -/
def activeTopLayer (Z : ZeroConfig) (b : ℝ) : Set ℂ :=
  {z : ℂ | z.re = b ∧ evenCoeff Z (boxSpline 1 3) z ≠ 0}

/-- When `activeTopLayer Z b` is finite, `topTrace Z b` is a real finite trigonometric
polynomial. -/
theorem isRealTrigPoly_topTrace_of_finite {Z : ZeroConfig} (_ : TemperedConfig Z) {b : ℝ}
    (hfin : (activeTopLayer Z b).Finite) :
    IsRealTrigPoly (topTrace Z b) := by
  classical
  set F := hfin.toFinset
  refine ⟨F.image Complex.im, fun ω => evenCoeff Z (boxSpline 1 3) ⟨b, ω⟩, fun u => ?_⟩
  rw [topTrace_eq_re]
  congr 1
  have htsum : topTraceC Z b u = ∑ z ∈ F, topTerm Z b z u := by
    unfold topTraceC
    refine tsum_eq_sum fun z hz => ?_
    rw [Set.Finite.mem_toFinset] at hz
    unfold topTerm
    split_ifs with hre
    · have h0 : evenCoeff Z (boxSpline 1 3) z = 0 := by
        by_contra hne
        exact hz ⟨hre, hne⟩
      rw [h0, zero_mul]
    · rfl
  rw [htsum]
  have hinj : Set.InjOn Complex.im (F : Set ℂ) := fun z₁ hz₁ z₂ hz₂ him => by
    have h1 : z₁ ∈ activeTopLayer Z b := (Set.Finite.mem_toFinset hfin).mp hz₁
    have h2 : z₂ ∈ activeTopLayer Z b := (Set.Finite.mem_toFinset hfin).mp hz₂
    exact Complex.ext (h1.1.trans h2.1.symm) him
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hmem : z ∈ activeTopLayer Z b := (Set.Finite.mem_toFinset hfin).mp hz
  have hpt : (⟨b, z.im⟩ : ℂ) = z := Complex.ext hmem.1.symm rfl
  dsimp only
  rw [hpt, topTerm, if_pos hmem.1]

/-- If `normTrace Z b − T → 0` for a real finite trigonometric polynomial `T`, then `T` equals
`topTrace Z b` identically and `activeTopLayer Z b` is finite. -/
theorem eq_topTrace_and_finite_of_tendsto_sub_trigPoly {Z : ZeroConfig} (hZ : TemperedConfig Z)
    {b : ℝ} (htop : TopDepth Z b) {T : ℝ → ℝ} (hT : IsRealTrigPoly T)
    (hlim : Tendsto (fun u => normTrace Z b u - T u) atTop (𝓝 0)) :
    (∀ u, T u = topTrace Z b u) ∧ (activeTopLayer Z b).Finite := by
  have hrem := tendsto_normTrace_sub_topTrace hZ htop
  have htt : Tendsto (fun u => topTrace Z b u - T u) atTop (𝓝 0) := by
    have h1 := hlim.sub hrem
    simp only [sub_zero] at h1
    exact h1.congr fun u => by ring
  have htc : Tendsto (fun u => topTraceC Z b u - ((T u : ℝ) : ℂ)) atTop (𝓝 0) := by
    have h1 := (Complex.continuous_ofReal.tendsto 0).comp htt
    simpa only [Function.comp_def, Complex.ofReal_sub, ofReal_topTrace, Complex.ofReal_zero]
      using h1
  have hvan := _root_.HTGeometry.eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero
    (isBohrAlmostPeriodic_sub (continuous_topTraceC hZ) (isBohrAlmostPeriodic_topTraceC hZ)
      (continuous_ofReal_of_isRealTrigPoly hT)
      (isBohrAlmostPeriodic_ofReal_of_isRealTrigPoly hT)) htc
  have heqC : topTraceC Z b = fun u : ℝ => ((T u : ℝ) : ℂ) :=
    funext fun u => sub_eq_zero.mp (hvan u)
  refine ⟨fun u => ?_, ?_⟩
  · have hre := congrArg Complex.re (congrFun heqC u)
    simpa only [← topTrace_eq_re, Complex.ofReal_re] using hre.symm
  · have hfinIm := finite_bohrSupport_of_isRealTrigPoly hT
    refine ((hfinIm.image fun ω : ℝ => (⟨b, ω⟩ : ℂ))).subset fun z ⟨hzre, hzne⟩ => ?_
    refine ⟨z.im, ?_, Complex.ext hzre.symm rfl⟩
    rw [mem_setOf_eq, ← heqC, bohrCoefficient_topTraceC hZ z.im]
    have hpt : (⟨b, z.im⟩ : ℂ) = z := Complex.ext hzre.symm rfl
    rwa [hpt]

/-- **Characterization of trigonometric-polynomial limits.** At a bounding depth `b`, the
normalized spline trace approaches a real finite trigonometric polynomial at `+∞` if and only if
`activeTopLayer Z b` is finite. -/
theorem tendsto_normTrace_sub_trigPoly_iff_finite_activeTop {Z : ZeroConfig}
    (hZ : TemperedConfig Z) {b : ℝ} (htop : TopDepth Z b) :
    (∃ T : ℝ → ℝ, IsRealTrigPoly T ∧ Tendsto (fun u => normTrace Z b u - T u) atTop (𝓝 0)) ↔
      (activeTopLayer Z b).Finite := by
  constructor
  · rintro ⟨T, hT, hlim⟩
    exact (eq_topTrace_and_finite_of_tendsto_sub_trigPoly hZ htop hT hlim).2
  · intro hfin
    exact ⟨topTrace Z b, isRealTrigPoly_topTrace_of_finite hZ hfin,
      tendsto_normTrace_sub_topTrace hZ htop⟩

/-- **Characterization of nonzero trigonometric-polynomial limits.** At a bounding depth `b`,
`normTrace Z b` approaches a nonzero real finite trigonometric polynomial at `+∞` if and only if
`activeTopLayer Z b` is finite and nonempty. -/
theorem tendsto_normTrace_sub_nonzero_trigPoly_iff {Z : ZeroConfig} (hZ : TemperedConfig Z)
    {b : ℝ} (htop : TopDepth Z b) :
    (∃ T : ℝ → ℝ, IsRealTrigPoly T ∧ (∃ u, T u ≠ 0) ∧
      Tendsto (fun u => normTrace Z b u - T u) atTop (𝓝 0)) ↔
      (activeTopLayer Z b).Finite ∧ (activeTopLayer Z b).Nonempty := by
  constructor
  · rintro ⟨T, hT, ⟨u₀, hu₀⟩, hlim⟩
    obtain ⟨heq, hfin⟩ := eq_topTrace_and_finite_of_tendsto_sub_trigPoly hZ htop hT hlim
    refine ⟨hfin, ?_⟩
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hall : ∀ z : ℂ, z.re = b → evenCoeff Z (boxSpline 1 3) z = 0 := fun z hz => by
      by_contra hne
      have : z ∈ (∅ : Set ℂ) := hemp ▸ ⟨hz, hne⟩
      exact this
    exact hu₀ ((heq u₀).trans (topTrace_eq_zero_of_topCoeff_eq_zero hall u₀))
  · rintro ⟨hfin, z₀, hz₀re, hz₀ne⟩
    refine ⟨topTrace Z b, isRealTrigPoly_topTrace_of_finite hZ hfin, ?_,
      tendsto_normTrace_sub_topTrace hZ htop⟩
    by_contra hall
    push Not at hall
    have hallC : ∀ u, topTraceC Z b u = 0 := fun u => by
      rw [← ofReal_topTrace, hall u, Complex.ofReal_zero]
    exact hz₀ne (topCoeff_eq_zero_of_topTraceC_eq_zero hZ hallC hz₀re)

/-- For a conjugation-symmetric configuration and `b > 0`, `z ↦ ½ + z` identifies
`activeTopLayer Z b` with `{ρ ∈ Z.carrier | Re ρ = ½ + b}`. -/
theorem activeTopLayer_bij_of_conj_symm {Z : ZeroConfig}
    (hconj : ∀ ρ ∈ Z.carrier, conj ρ ∈ Z.carrier) {b : ℝ} (hb : 0 < b) :
    (fun z : ℂ => (1 / 2 : ℂ) + z) '' activeTopLayer Z b =
      {ρ ∈ Z.carrier | ρ.re = 1 / 2 + b} := by
  have he : ∀ z : ℂ, ((1 / 2 : ℂ) + z).re = 1 / 2 + z.re := fun _ => by norm_num
  ext ρ
  constructor
  · rintro ⟨z, ⟨hzre, hzne⟩, rfl⟩
    exact ⟨add_half_mem_of_evenCoeff_ne_zero hconj hzne, by rw [he, hzre]⟩
  · rintro ⟨hρ, hρre⟩
    refine ⟨ρ - 1 / 2, ⟨?_, ?_⟩, by ring⟩
    · have hs : (ρ - 1 / 2).re = ρ.re - 1 / 2 := by simp
      rw [hs, hρre]
      ring
    · exact evenCoeff_spline_sees_config hρ (by linarith only [hρre, hb])

theorem activeTopLayer_empty_iff_of_conj_symm {Z : ZeroConfig}
    (hconj : ∀ ρ ∈ Z.carrier, conj ρ ∈ Z.carrier) {b : ℝ} (hb : 0 < b) :
    activeTopLayer Z b = ∅ ↔ {ρ ∈ Z.carrier | ρ.re = 1 / 2 + b} = ∅ := by
  rw [← activeTopLayer_bij_of_conj_symm hconj hb, Set.image_eq_empty]

theorem activeTopLayer_finite_iff_of_conj_symm {Z : ZeroConfig}
    (hconj : ∀ ρ ∈ Z.carrier, conj ρ ∈ Z.carrier) {b : ℝ} (hb : 0 < b) :
    (activeTopLayer Z b).Finite ↔ {ρ ∈ Z.carrier | ρ.re = 1 / 2 + b}.Finite := by
  rw [← activeTopLayer_bij_of_conj_symm hconj hb,
    Set.finite_image_iff (add_right_injective (1 / 2 : ℂ)).injOn]

theorem activeTopLayer_nonempty_iff_of_conj_symm {Z : ZeroConfig}
    (hconj : ∀ ρ ∈ Z.carrier, conj ρ ∈ Z.carrier) {b : ℝ} (hb : 0 < b) :
    (activeTopLayer Z b).Nonempty ↔ {ρ ∈ Z.carrier | ρ.re = 1 / 2 + b}.Nonempty := by
  rw [← activeTopLayer_bij_of_conj_symm hconj hb, Set.image_nonempty]

/-! ### Four-sector classification for `ζ` at `b_* = Θ − ½` -/

/-- The canonical top depth `b_* = Θ − ½` of the Riemann zeta function. -/
def zetaTopDepth : ℝ := _root_.RHTower.zetaZeroAbscissa - 1 / 2

/-- The spline trace of `ζ` normalized by its exact zero abscissa `Θ`:
`G(u) = 2 Re S(u) e^{−(Θ − ½)u}`. -/
def zetaNormTrace (u : ℝ) : ℝ := normTrace zetaZeroConfig zetaTopDepth u

/-- The nontrivial zeros of `ζ` lying on the frontier line `Re ρ = Θ`. -/
def zetaTopZeroLine : Set ℂ :=
  {ρ ∈ zetaZeroConfig.carrier | ρ.re = _root_.RHTower.zetaZeroAbscissa}

theorem zero_le_zetaTopDepth : 0 ≤ zetaTopDepth := by
  unfold zetaTopDepth
  linarith [_root_.RHTower.half_le_zetaZeroAbscissa]

private theorem zetaZeroAbscissa_eq_half_iff_rh :
    _root_.RHTower.zetaZeroAbscissa = 1 / 2 ↔ RiemannHypothesis := by
  rw [_root_.RHTower.CrossRouteReceiverBridges.riemannHypothesis_iff_zetaZeroConfig_onLine]
  constructor
  · intro hΘ ρ hρ
    have hle1 := _root_.RHTower.re_le_zetaZeroAbscissa hρ.1
    have hrefl := _root_.RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hρ.1 hρ.2.1 hρ.2.2
    have hle2 := _root_.RHTower.re_le_zetaZeroAbscissa hrefl
    have hsub : ((1 : ℂ) - ρ).re = 1 - ρ.re := by simp
    rw [hsub, hΘ] at hle2
    rw [hΘ] at hle1
    linarith only [hle1, hle2]
  · intro hon
    refine le_antisymm (csSup_le _root_.RHTower.zetaZeroReSet_nonempty ?_)
      _root_.RHTower.half_le_zetaZeroAbscissa
    rintro x ⟨ρ, hρ, rfl⟩
    rcases le_or_gt ρ.re 0 with hle0 | hpos
    · linarith only [hle0]
    · have hlt1 : ρ.re < 1 := by
        by_contra hc
        exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hc) hρ
      exact (hon ρ ⟨hρ, hpos, hlt1⟩).le

theorem zetaTopDepth_eq_zero_iff_riemannHypothesis :
    zetaTopDepth = 0 ↔ RiemannHypothesis := by
  unfold zetaTopDepth
  rw [sub_eq_zero, zetaZeroAbscissa_eq_half_iff_rh]

theorem zetaTopDepth_pos_iff :
    0 < zetaTopDepth ↔ 1 / 2 < _root_.RHTower.zetaZeroAbscissa := by
  unfold zetaTopDepth
  constructor <;> intro h <;> linarith

/-- Every spline exponent of `ζ` has real part at most `Θ − ½`. -/
theorem topDepth_zetaZeroConfig_zetaTopDepth : TopDepth zetaZeroConfig zetaTopDepth := by
  intro z hz
  have hmem := add_half_mem_zetaZeroConfig_of_evenCoeff_ne_zero hz
  have hle := _root_.RHTower.re_le_zetaZeroAbscissa hmem.1
  have he : ((1 / 2 : ℂ) + z).re = 1 / 2 + z.re := by norm_num
  rw [he] at hle
  unfold zetaTopDepth
  linarith only [hle]

private theorem conj_mem_zetaZeroConfig :
    ∀ ρ ∈ zetaZeroConfig.carrier, conj ρ ∈ zetaZeroConfig.carrier := by
  intro ρ hρ
  have hzc : riemannZeta (conj ρ) = 0 := by rw [_root_.riemannZeta_conj, hρ.1, map_zero]
  exact ⟨hzc, by simpa using hρ.2.1, by simpa using hρ.2.2⟩

theorem activeTopLayer_zeta_bij (hΘ : 1 / 2 < _root_.RHTower.zetaZeroAbscissa) :
    (fun z : ℂ => (1 / 2 : ℂ) + z) '' activeTopLayer zetaZeroConfig zetaTopDepth =
      zetaTopZeroLine := by
  have hb : 0 < zetaTopDepth := zetaTopDepth_pos_iff.mpr hΘ
  have hbij := activeTopLayer_bij_of_conj_symm conj_mem_zetaZeroConfig hb
  have hsum : 1 / 2 + zetaTopDepth = _root_.RHTower.zetaZeroAbscissa := by
    unfold zetaTopDepth; ring
  unfold zetaTopZeroLine
  simpa only [hsum] using hbij

/-- Under `RiemannHypothesis`, `zetaNormTrace` equals `topTrace zetaZeroConfig 0` identically
and its complexification is Bohr almost periodic. -/
theorem zetaNormTrace_eq_topTrace_of_riemannHypothesis (hRH : RiemannHypothesis) :
    (∀ u, zetaNormTrace u = topTrace zetaZeroConfig 0 u) ∧
      _root_.HTGeometry.IsBohrAlmostPeriodic (fun u : ℝ => ((zetaNormTrace u : ℝ) : ℂ)) := by
  have hb0 : zetaTopDepth = 0 := zetaTopDepth_eq_zero_iff_riemannHypothesis.mpr hRH
  have htop : TopDepth zetaZeroConfig 0 := hb0 ▸ topDepth_zetaZeroConfig_zetaTopDepth
  have heq : ∀ u, zetaNormTrace u = topTrace zetaZeroConfig 0 u := by
    intro u
    unfold zetaNormTrace
    rw [hb0]
    have hnorm := ofReal_normTrace (b := 0) temperedConfig_zetaZeroConfig u
    have hre := congrArg Complex.re hnorm
    rw [Complex.ofReal_re] at hre
    rw [hre, topTrace]
    congr 1
    refine tsum_congr fun z => ?_
    split_ifs with hz
    · rfl
    · have h0 : evenCoeff zetaZeroConfig (boxSpline 1 3) z = 0 := by
        by_contra hne
        have hle := htop z hne
        have hmem := add_half_mem_zetaZeroConfig_of_evenCoeff_ne_zero hne
        have hrefl := zetaZeroConfig.reflect_mem _ hmem
        have hler := _root_.RHTower.re_le_zetaZeroAbscissa hrefl.1
        rw [ArithmeticCastelnuovoSeveri.re_reflect] at hler
        have he : ((1 / 2 : ℂ) + z).re = 1 / 2 + z.re := by norm_num
        rw [he, zetaZeroAbscissa_eq_half_iff_rh.mpr hRH] at hler
        exact hz (by linarith only [hle, hler])
      rw [h0, zero_mul]
  refine ⟨heq, ?_⟩
  have heqC : (fun u : ℝ => ((zetaNormTrace u : ℝ) : ℂ)) = topTraceC zetaZeroConfig 0 := by
    funext u
    rw [heq u, ofReal_topTrace]
  rw [heqC]
  exact isBohrAlmostPeriodic_topTraceC temperedConfig_zetaZeroConfig

/-- **Unconditional four-sector classification of `zetaNormTrace`.** At `b_* = Θ − ½`,
`zetaNormTrace − topTrace → 0` and `zetaNormTrace` lies in one of four mutually exclusive
regimes: `RiemannHypothesis` (`Θ = ½`), off-line unattained top (`G → 0`), off-line finite
attained top (`G − T → 0` for a nonzero trigonometric polynomial `T`), or off-line infinite
attained top (`G − T ↛ 0` for every finite trigonometric polynomial `T`). -/
theorem zetaNormTrace_quadrichotomy :
    Tendsto (fun u => zetaNormTrace u - topTrace zetaZeroConfig zetaTopDepth u) atTop (𝓝 0) ∧
      ((RiemannHypothesis ∧
          (∀ u, zetaNormTrace u = topTrace zetaZeroConfig 0 u) ∧
          _root_.HTGeometry.IsBohrAlmostPeriodic (fun u : ℝ => ((zetaNormTrace u : ℝ) : ℂ))) ∨
        (1 / 2 < _root_.RHTower.zetaZeroAbscissa ∧ zetaTopZeroLine = ∅ ∧
          Tendsto zetaNormTrace atTop (𝓝 0)) ∨
        (1 / 2 < _root_.RHTower.zetaZeroAbscissa ∧
          zetaTopZeroLine.Finite ∧ zetaTopZeroLine.Nonempty ∧
          ∃ T : ℝ → ℝ, IsRealTrigPoly T ∧ (∃ u, T u ≠ 0) ∧
            Tendsto (fun u => zetaNormTrace u - T u) atTop (𝓝 0)) ∨
        (1 / 2 < _root_.RHTower.zetaZeroAbscissa ∧ zetaTopZeroLine.Infinite ∧
          ∀ T : ℝ → ℝ, IsRealTrigPoly T →
            ¬ Tendsto (fun u => zetaNormTrace u - T u) atTop (𝓝 0))) := by
  have htop := topDepth_zetaZeroConfig_zetaTopDepth
  refine ⟨tendsto_normTrace_sub_topTrace temperedConfig_zetaZeroConfig htop, ?_⟩
  rcases eq_or_lt_of_le _root_.RHTower.half_le_zetaZeroAbscissa with hhalf | hΘ
  · left
    have hRH := zetaZeroAbscissa_eq_half_iff_rh.mp hhalf.symm
    obtain ⟨heq, hap⟩ := zetaNormTrace_eq_topTrace_of_riemannHypothesis hRH
    exact ⟨hRH, heq, hap⟩
  · right
    have hb : 0 < zetaTopDepth := zetaTopDepth_pos_iff.mpr hΘ
    have hsum : 1 / 2 + zetaTopDepth = _root_.RHTower.zetaZeroAbscissa := by
      unfold zetaTopDepth; ring
    by_cases hemp : zetaTopZeroLine = ∅
    · left
      refine ⟨hΘ, hemp, ?_⟩
      unfold zetaNormTrace
      rw [tendsto_normTrace_zeta_zero_iff hb htop]
      intro ρ hρ hre
      have : ρ ∈ (∅ : Set ℂ) := hemp ▸ ⟨hρ, hsum ▸ hre⟩
      exact this
    · right
      have hne : zetaTopZeroLine.Nonempty := Set.nonempty_iff_ne_empty.mpr hemp
      by_cases hfin : zetaTopZeroLine.Finite
      · left
        refine ⟨hΘ, hfin, hne, ?_⟩
        unfold zetaNormTrace
        rw [tendsto_normTrace_sub_nonzero_trigPoly_iff temperedConfig_zetaZeroConfig htop]
        refine ⟨?_, ?_⟩
        · rw [activeTopLayer_finite_iff_of_conj_symm conj_mem_zetaZeroConfig hb, hsum]
          exact hfin
        · rw [activeTopLayer_nonempty_iff_of_conj_symm conj_mem_zetaZeroConfig hb, hsum]
          exact hne
      · right
        have hinf : zetaTopZeroLine.Infinite := hfin
        refine ⟨hΘ, hinf, fun T hT hlim => hfin ?_⟩
        have hfinA : (activeTopLayer zetaZeroConfig zetaTopDepth).Finite :=
          (tendsto_normTrace_sub_trigPoly_iff_finite_activeTop
            temperedConfig_zetaZeroConfig htop).mp ⟨T, hT, hlim⟩
        rwa [activeTopLayer_finite_iff_of_conj_symm conj_mem_zetaZeroConfig hb, hsum] at hfinA

/-- **Strong off-line non-attainment for `ζ`** at `b_* = Θ − ½`: `G(u) → 0` when `Θ > ½` holds
if and only if no zero of `ζ` attains `Re ρ = Θ`. -/
theorem zeta_offLine_tendsto_zero_iff :
    (1 / 2 < _root_.RHTower.zetaZeroAbscissa → Tendsto zetaNormTrace atTop (𝓝 0)) ↔
      (1 / 2 < _root_.RHTower.zetaZeroAbscissa → zetaTopZeroLine = ∅) := by
  refine forall_congr' fun hΘ => ?_
  have hb : 0 < zetaTopDepth := zetaTopDepth_pos_iff.mpr hΘ
  have hsum : 1 / 2 + zetaTopDepth = _root_.RHTower.zetaZeroAbscissa := by
    unfold zetaTopDepth; ring
  unfold zetaNormTrace
  rw [tendsto_normTrace_zero_iff temperedConfig_zetaZeroConfig topDepth_zetaZeroConfig_zetaTopDepth]
  have hbij := activeTopLayer_empty_iff_of_conj_symm conj_mem_zetaZeroConfig hb
  rw [hsum] at hbij
  change (∀ z : ℂ, z.re = zetaTopDepth → evenCoeff zetaZeroConfig (boxSpline 1 3) z = 0) ↔
    zetaTopZeroLine = ∅
  unfold zetaTopZeroLine
  rw [← hbij]
  constructor
  · intro hall
    ext z
    simp only [activeTopLayer, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
    exact fun hre hne => hne (hall z hre)
  · intro hemp z hre
    by_contra hne
    have : z ∈ (∅ : Set ℂ) := hemp ▸ ⟨hre, hne⟩
    exact this

/-- **Exclusion of nonzero trigonometric-polynomial limits for `ζ`** at `b_* = Θ − ½`: when
`Θ > ½`, `G` approaches no nonzero finite trigonometric polynomial if and only if the frontier
line `Re ρ = Θ` is either empty or infinite. -/
theorem zeta_offLine_no_nonzero_trigPoly_iff :
    (1 / 2 < _root_.RHTower.zetaZeroAbscissa →
      ∀ T : ℝ → ℝ, IsRealTrigPoly T → (∃ u, T u ≠ 0) →
        ¬ Tendsto (fun u => zetaNormTrace u - T u) atTop (𝓝 0)) ↔
      (1 / 2 < _root_.RHTower.zetaZeroAbscissa →
        zetaTopZeroLine = ∅ ∨ zetaTopZeroLine.Infinite) := by
  refine forall_congr' fun hΘ => ?_
  have hb : 0 < zetaTopDepth := zetaTopDepth_pos_iff.mpr hΘ
  have hsum : 1 / 2 + zetaTopDepth = _root_.RHTower.zetaZeroAbscissa := by
    unfold zetaTopDepth; ring
  have hiff := tendsto_normTrace_sub_nonzero_trigPoly_iff (Z := zetaZeroConfig)
    temperedConfig_zetaZeroConfig (b := zetaTopDepth) topDepth_zetaZeroConfig_zetaTopDepth
  rw [activeTopLayer_finite_iff_of_conj_symm conj_mem_zetaZeroConfig hb,
    activeTopLayer_nonempty_iff_of_conj_symm conj_mem_zetaZeroConfig hb, hsum] at hiff
  constructor
  · intro hno
    by_cases hemp : zetaTopZeroLine = ∅
    · exact Or.inl hemp
    · right
      intro hfin
      obtain ⟨T, hT, hnz, hlim⟩ := hiff.mpr ⟨hfin, Set.nonempty_iff_ne_empty.mpr hemp⟩
      exact hno T hT hnz hlim
  · rintro (hemp | hinf) T hT hnz hlim
    · obtain ⟨_, hne⟩ := hiff.mp ⟨T, hT, hnz, hlim⟩
      unfold zetaTopZeroLine at hemp
      rw [hemp] at hne
      exact Set.not_nonempty_empty hne
    · obtain ⟨hfin, _⟩ := hiff.mp ⟨T, hT, hnz, hlim⟩
      exact hinf hfin

/-- **Unconditional implication chain for `ζ`:**
`(Θ > ½ → G → 0) → (Θ > ½ → no nonzero finite trig poly limit) → AsymptoticAbscissaLaw`. -/
theorem zeta_abscissaLaw_of_no_nonzero_trigPoly_limit
    (hno : 1 / 2 < _root_.RHTower.zetaZeroAbscissa →
      ∀ T : ℝ → ℝ, IsRealTrigPoly T → (∃ u, T u ≠ 0) →
        ¬ Tendsto (fun u => zetaNormTrace u - T u) atTop (𝓝 0)) :
    _root_.RHTower.AsymptoticAbscissaLaw := by
  by_contra hnot
  obtain ⟨b, hb, htop, S, hS, ⟨z₀, hz₀⟩⟩ := exists_finite_top_of_not_abscissaLaw hnot
  obtain ⟨hz₀re, -, hz₀ne⟩ := (hS z₀).mp hz₀
  have hmem₀ := add_half_mem_zetaZeroConfig_of_evenCoeff_ne_zero hz₀ne
  have hble : 1 / 2 + b ≤ _root_.RHTower.zetaZeroAbscissa := by
    have hle := _root_.RHTower.re_le_zetaZeroAbscissa hmem₀.1
    have he : ((1 / 2 : ℂ) + z₀).re = 1 / 2 + z₀.re := by norm_num
    rwa [he, hz₀re] at hle
  have hΘgt : 1 / 2 < _root_.RHTower.zetaZeroAbscissa := by linarith only [hb, hble]
  have hΘle : _root_.RHTower.zetaZeroAbscissa ≤ 1 / 2 + b := by
    refine csSup_le _root_.RHTower.zetaZeroReSet_nonempty ?_
    rintro x ⟨ρ, hρ, rfl⟩
    rcases le_or_gt ρ.re (1 / 2) with hle | hgt
    · linarith only [hle, hb]
    · have hρ1 : ρ.re < 1 := by
        by_contra hc
        exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hc) hρ
      have hρ0 : 0 < ρ.re := by linarith only [hgt]
      have hsee := evenCoeff_spline_sees ⟨hρ, hρ0, hρ1⟩ hgt
      have hle := htop (ρ - 1 / 2) hsee
      have hs : (ρ - 1 / 2).re = ρ.re - 1 / 2 := by simp
      linarith only [hle, hs]
  have hbeq : b = zetaTopDepth := by
    unfold zetaTopDepth
    linarith only [hble, hΘle]
  have hfinA : (activeTopLayer zetaZeroConfig b).Finite := by
    classical
    refine ((S.finite_toSet.union (S.finite_toSet.image conj))).subset fun z ⟨hzre, hzne⟩ => ?_
    rcases lt_or_gt_of_ne (evenCoeff_spline_real hzne) with hneg | hpos
    · right
      refine ⟨conj z, (hS (conj z)).mpr ⟨by simpa using hzre, by simpa using neg_pos.mpr hneg, ?_⟩,
        Complex.conj_conj z⟩
      rw [SurfaceOfSpecZ.evenCoeff_conj]
      intro h0
      exact hzne (by simpa using congrArg conj h0)
    · left
      exact (hS z).mpr ⟨hzre, hpos, hzne⟩
  have hneA : (activeTopLayer zetaZeroConfig b).Nonempty := ⟨z₀, hz₀re, hz₀ne⟩
  rw [hbeq] at hfinA hneA htop
  obtain ⟨T, hT, hnz, hlim⟩ :=
    (tendsto_normTrace_sub_nonzero_trigPoly_iff temperedConfig_zetaZeroConfig htop).mpr
      ⟨hfinA, hneA⟩
  exact hno hΘgt T hT hnz hlim

theorem zeta_no_nonzero_trigPoly_of_offLine_tendsto_zero
    (hz : 1 / 2 < _root_.RHTower.zetaZeroAbscissa → Tendsto zetaNormTrace atTop (𝓝 0)) :
    1 / 2 < _root_.RHTower.zetaZeroAbscissa →
      ∀ T : ℝ → ℝ, IsRealTrigPoly T → (∃ u, T u ≠ 0) →
        ¬ Tendsto (fun u => zetaNormTrace u - T u) atTop (𝓝 0) :=
  zeta_offLine_no_nonzero_trigPoly_iff.mpr fun hΘ =>
    Or.inl (zeta_offLine_tendsto_zero_iff.mp hz hΘ)

/-! ### Strict separation of the three top-line laws on tempered configurations -/

section OrbitModel

/-- Parametric 4-fold symmetric sequence configuration with depths `d k ∈ [0, ½]` at ordinates
`±(k + 1)` (`k ∈ ℕ`). -/
def orbitPt (d : ℕ → ℝ) (p : ℕ × Bool × Bool) : ℂ :=
  ⟨1 / 2 + (if p.2.1 then d p.1 else -d p.1),
    if p.2.2 then (p.1 : ℝ) + 1 else -((p.1 : ℝ) + 1)⟩

def orbitCarrier (d : ℕ → ℝ) : Set ℂ :=
  {ρ : ℂ | ∃ k : ℕ, |ρ.re - 1 / 2| = d k ∧ |ρ.im| = (k : ℝ) + 1}

private theorem orbitPt_abs_im (d : ℕ → ℝ) (p : ℕ × Bool × Bool) :
    |(orbitPt d p).im| = (p.1 : ℝ) + 1 := by
  rcases p with ⟨k, b₁, (_ | _)⟩
  · have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    change |-((k : ℝ) + 1)| = (k : ℝ) + 1
    rw [abs_neg, abs_of_pos hk]
  · have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    change |(k : ℝ) + 1| = (k : ℝ) + 1
    exact abs_of_pos hk

private theorem range_orbitPt_eq (d : ℕ → ℝ) (hd0 : ∀ k, 0 ≤ d k) :
    Set.range (orbitPt d) = orbitCarrier d := by
  ext ρ
  constructor
  · rintro ⟨⟨k, b₁, b₂⟩, rfl⟩
    refine ⟨k, ?_, orbitPt_abs_im d (k, b₁, b₂)⟩
    cases b₁ <;> simp [orbitPt, abs_of_nonneg (hd0 k)]
  · rintro ⟨k, hre, him⟩
    have hb₁ : ρ.re = 1 / 2 + d k ∨ ρ.re = 1 / 2 + -d k := by
      rcases eq_or_eq_neg_of_abs_eq hre with h | h
      · exact Or.inl (by linarith only [h])
      · exact Or.inr (by linarith only [h])
    have hb₂ : ρ.im = (k : ℝ) + 1 ∨ ρ.im = -((k : ℝ) + 1) := eq_or_eq_neg_of_abs_eq him
    rcases hb₁ with hr | hr <;> rcases hb₂ with hi | hi
    · exact ⟨(k, true, true), Complex.ext (by simp [orbitPt, hr]) (by simp [orbitPt, hi])⟩
    · exact ⟨(k, true, false), Complex.ext (by simp [orbitPt, hr]) (by simp [orbitPt, hi])⟩
    · exact ⟨(k, false, true), Complex.ext (by simp [orbitPt, hr]) (by simp [orbitPt, hi])⟩
    · exact ⟨(k, false, false), Complex.ext (by simp [orbitPt, hr]) (by simp [orbitPt, hi])⟩

/-- The configuration of 4-fold orbits `½ ± d_k ± i(k + 1)` with multiplicity `1`. -/
def orbitConfig (d : ℕ → ℝ) (hd0 : ∀ k, 0 ≤ d k) (hd1 : ∀ k, d k ≤ 1 / 2) : ZeroConfig where
  carrier := orbitCarrier d
  mult := fun _ => 1
  one_le_mult := fun _ _ => le_rfl
  strip := by
    rintro ρ ⟨k, hre, -⟩
    have h := abs_le.mp (hre.le.trans (hd1 k))
    constructor <;> linarith only [h.1, h.2]
  reflect_mem := by
    rintro ρ ⟨k, hre, him⟩
    have h1 : (reflect ρ).re = 1 - ρ.re := by simp [reflect]
    have h2 : (reflect ρ).im = ρ.im := by simp [reflect]
    refine ⟨k, ?_, by rw [h2]; exact him⟩
    rw [h1, ← hre, ← abs_neg (ρ.re - 1 / 2)]
    congr 1
    ring
  mult_reflect := fun _ _ => rfl
  finite_window := fun T₁ T₂ => by
    classical
    set M := ⌊max |T₁| |T₂|⌋₊ + 1
    refine (((Finset.range M ×ˢ (Finset.univ : Finset (Bool × Bool))).finite_toSet.image
      (orbitPt d)).subset ?_)
    rintro ρ ⟨hmem, hT₁, hT₂⟩
    obtain ⟨k, hre, him⟩ := hmem
    obtain ⟨p, hp⟩ := (range_orbitPt_eq d hd0).symm.subset ⟨k, hre, him⟩
    have hpim : |ρ.im| = (p.1 : ℝ) + 1 := by
      rw [← hp]
      exact orbitPt_abs_im d p
    have habs : |ρ.im| ≤ max |T₁| |T₂| := by
      rw [abs_le]
      exact ⟨by linarith [neg_abs_le T₁, le_max_left |T₁| |T₂|],
        by linarith [le_abs_self T₂, le_max_right |T₁| |T₂|]⟩
    have hklt : p.1 < M := by
      have hle : (p.1 : ℝ) ≤ max |T₁| |T₂| := by linarith only [hpim, habs]
      exact Nat.lt_succ_of_le (Nat.le_floor hle)
    exact ⟨p, Finset.mem_coe.mpr (Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hklt, Finset.mem_univ _⟩), hp⟩

theorem conj_mem_orbitConfig (d : ℕ → ℝ) (hd0 : ∀ k, 0 ≤ d k) (hd1 : ∀ k, d k ≤ 1 / 2) :
    ∀ ρ ∈ (orbitConfig d hd0 hd1).carrier, conj ρ ∈ (orbitConfig d hd0 hd1).carrier := by
  rintro ρ ⟨k, hre, him⟩
  exact ⟨k, by simpa using hre, by simpa [abs_neg] using him⟩

theorem im_ne_zero_orbitConfig (d : ℕ → ℝ) (hd0 : ∀ k, 0 ≤ d k) (hd1 : ∀ k, d k ≤ 1 / 2) :
    ∀ ρ ∈ (orbitConfig d hd0 hd1).carrier, ρ.im ≠ 0 := by
  rintro ρ ⟨k, -, him⟩ h0
  rw [h0, abs_zero] at him
  have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  linarith only [him, this]

theorem topDepth_orbitConfig (d : ℕ → ℝ) (hd0 : ∀ k, 0 ≤ d k) (hd1 : ∀ k, d k ≤ 1 / 2)
    {b : ℝ} (hdb : ∀ k, d k ≤ b) :
    TopDepth (orbitConfig d hd0 hd1) b := by
  intro z hz
  obtain ⟨k, hre, -⟩ := add_half_mem_of_evenCoeff_ne_zero (conj_mem_orbitConfig d hd0 hd1) hz
  have he : ((1 / 2 : ℂ) + z).re = 1 / 2 + z.re := by norm_num
  rw [he] at hre
  have h1 := le_abs_self (1 / 2 + z.re - 1 / 2)
  have h2 := hdb k
  linarith only [h1, hre, h2]

theorem temperedConfig_orbitConfig (d : ℕ → ℝ) (hd0 : ∀ k, 0 ≤ d k) (hd1 : ∀ k, d k ≤ 1 / 2) :
    TemperedConfig (orbitConfig d hd0 hd1) := by
  classical
  unfold TemperedConfig
  have hsurj : ∀ y : (orbitConfig d hd0 hd1).carrier, ∃ p : ℕ × Bool × Bool, orbitPt d p = y.1 := by
    intro y
    have hy : y.1 ∈ Set.range (orbitPt d) := (range_orbitPt_eq d hd0).symm ▸ y.2
    exact hy
  choose g hg using hsurj
  have hinj : Function.Injective g := fun y₁ y₂ h => by
    apply Subtype.ext
    rw [← hg y₁, ← hg y₂, h]
  have hdom : Summable fun p : ℕ × Bool × Bool => 1 / ((p.1 : ℝ) + 1) ^ 2 := by
    refine (summable_prod_of_nonneg (fun _ => by positivity)).mpr ⟨fun _ => ?_, ?_⟩
    · exact (hasSum_fintype _).summable
    · have hbase : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
        have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
        simpa [Nat.cast_add, Nat.cast_one] using this
      refine Summable.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => by positivity)
        (fun k => ?_) (hbase.mul_left 4)
      rw [tsum_fintype]
      have hcard : (Finset.univ : Finset (Bool × Bool)).card = 4 := rfl
      simp only [Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_ofNat, le_rfl]
  have hdom_g : Summable fun y : (orbitConfig d hd0 hd1).carrier => 1 / (((g y).1 : ℝ) + 1) ^ 2 :=
    Summable.comp_injective (f := fun p : ℕ × Bool × Bool => 1 / ((p.1 : ℝ) + 1) ^ 2) hdom hinj
  refine Summable.of_nonneg_of_le (fun y => div_nonneg (Nat.cast_nonneg _)
    (by linarith [Complex.normSq_nonneg (gammaOf y.1)])) (fun y => ?_) hdom_g
  simp only [orbitConfig, Nat.cast_one]
  refine one_div_le_one_div_of_le (by positivity) ?_
  have hre : (gammaOf y.1).re = y.1.im := by simp [gammaOf, Complex.div_I]
  have hyim : |y.1.im| = ((g y).1 : ℝ) + 1 := by
    rw [← hg y]
    exact orbitPt_abs_im d (g y)
  have hsq : (((g y).1 : ℝ) + 1) ^ 2 = (gammaOf y.1).re ^ 2 := by
    rw [hre, ← hyim, sq_abs]
  rw [Complex.normSq_apply]
  have him_nn : 0 ≤ (gammaOf y.1).im * (gammaOf y.1).im := mul_self_nonneg _
  have hre_sq : (gammaOf y.1).re * (gammaOf y.1).re = (gammaOf y.1).re ^ 2 := (sq _).symm
  linarith only [him_nn, hre_sq, hsq]

end OrbitModel

/-- **Separation 1 (Infinite top line):** For every depth `0 < b ≤ ½`, there is a tempered,
conjugation-symmetric configuration without real zeros of top depth `b` that satisfies
`AbscissaLaw` and admits no finite trigonometric-polynomial approximation to `normTrace Z b`,
yet `normTrace Z b ↛ 0`. -/
theorem exists_tempered_abscissaLaw_infinite_top {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2) :
    ∃ Z : ZeroConfig, TemperedConfig Z ∧
      (∀ ρ ∈ Z.carrier, conj ρ ∈ Z.carrier) ∧
      (∀ ρ ∈ Z.carrier, ρ.im ≠ 0) ∧
      TopDepth Z b ∧
      AbscissaLaw Z ∧
      (∀ T : ℝ → ℝ, IsRealTrigPoly T → ¬ Tendsto (fun u => normTrace Z b u - T u) atTop (𝓝 0)) ∧
      ¬ Tendsto (normTrace Z b) atTop (𝓝 0) := by
  have hd0 : ∀ _ : ℕ, 0 ≤ b := fun _ => hb.le
  have hd1 : ∀ _ : ℕ, b ≤ 1 / 2 := fun _ => hb'
  set Z := orbitConfig (fun _ => b) hd0 hd1
  have hZ := temperedConfig_orbitConfig (fun _ => b) hd0 hd1
  have hconj := conj_mem_orbitConfig (fun _ => b) hd0 hd1
  have hnonreal := im_ne_zero_orbitConfig (fun _ => b) hd0 hd1
  have htop := topDepth_orbitConfig (fun _ => b) hd0 hd1 (fun _ => le_rfl)
  have hmem_k : ∀ k : ℕ, (⟨1 / 2 + b, (k : ℝ) + 1⟩ : ℂ) ∈ Z.carrier := fun k => by
    refine ⟨k, ?_, ?_⟩
    · show |1 / 2 + b - 1 / 2| = b
      rw [add_sub_cancel_left, abs_of_pos hb]
    · show |(k : ℝ) + 1| = (k : ℝ) + 1
      exact abs_of_pos (by positivity)
  have hinj_k : Function.Injective (fun k : ℕ => (⟨1 / 2 + b, (k : ℝ) + 1⟩ : ℂ)) := fun k₁ k₂ h => by
    have him := congrArg Complex.im h
    simp only at him
    exact_mod_cast add_right_cancel him
  have hinf_top : {ρ ∈ Z.carrier | ρ.re = 1 / 2 + b}.Infinite :=
    (Set.infinite_range_of_injective hinj_k).mono (by
      rintro _ ⟨k, rfl⟩
      exact ⟨hmem_k k, rfl⟩)
  have habs : AbscissaLaw Z := by
    intro h _ hfin ρ hρ
    by_cases hlt : h < b
    · exfalso
      exact hinf_top (hfin.subset fun τ ⟨hτ, hτre⟩ => ⟨hτ, by linarith only [hτre, hlt]⟩)
    · obtain ⟨k, hre, -⟩ := hρ
      have h1 := le_abs_self (ρ.re - 1 / 2)
      linarith only [h1, hre, le_of_not_gt hlt]
  have hno_trig : ∀ T : ℝ → ℝ, IsRealTrigPoly T →
      ¬ Tendsto (fun u => normTrace Z b u - T u) atTop (𝓝 0) := by
    intro T hT hlim
    have hfinA := (tendsto_normTrace_sub_trigPoly_iff_finite_activeTop hZ htop).mp ⟨T, hT, hlim⟩
    rw [activeTopLayer_finite_iff_of_conj_symm hconj hb] at hfinA
    exact hinf_top hfinA
  refine ⟨Z, hZ, hconj, hnonreal, htop, habs, hno_trig, fun h0 => ?_⟩
  exact hno_trig (fun _ => 0) isRealTrigPoly_zero (by simpa only [sub_zero] using h0)

private def subTopDepth (b : ℝ) : ℕ → ℝ
  | 0 => b
  | m + 1 => b * (1 - 1 / ((m : ℝ) + 2))

private def subTopPt (b : ℝ) (N₀ n : ℕ) : ℂ :=
  ⟨1 / 2 + subTopDepth b (N₀ + n + 1), ((N₀ + n + 1 : ℕ) : ℝ) + 1⟩

/-- **Separation 2 (Sub-top accumulation refutes the converse in `[D]`):** For every depth
`0 < b ≤ ½`, there is a tempered, conjugation-symmetric configuration without real zeros of top
depth `b` that satisfies `AbscissaLaw` (`Θ_∞ = Θ = ½ + b`), yet `normTrace Z b` converges at `+∞`
to a nonzero real finite trigonometric polynomial. -/
theorem exists_tempered_abscissaLaw_nonzero_trigPoly_limit {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2) :
    ∃ Z : ZeroConfig, TemperedConfig Z ∧
      (∀ ρ ∈ Z.carrier, conj ρ ∈ Z.carrier) ∧
      (∀ ρ ∈ Z.carrier, ρ.im ≠ 0) ∧
      TopDepth Z b ∧
      AbscissaLaw Z ∧
      ∃ T : ℝ → ℝ, IsRealTrigPoly T ∧ (∃ u, T u ≠ 0) ∧
        Tendsto (fun u => normTrace Z b u - T u) atTop (𝓝 0) := by
  have hd0 : ∀ k, 0 ≤ subTopDepth b k := by
    intro k
    cases k with
    | zero => exact hb.le
    | succ m =>
      have h1 : (1 : ℝ) / ((m : ℝ) + 2) ≤ 1 :=
        div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) m]) (by positivity)
      exact mul_nonneg hb.le (by linarith only [h1])
  have hdb : ∀ k, subTopDepth b k ≤ b := by
    intro k
    cases k with
    | zero => exact le_rfl
    | succ m =>
      simp only [subTopDepth]
      have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 2) := by positivity
      nlinarith only [hb, hpos]
  have hd1 : ∀ k, subTopDepth b k ≤ 1 / 2 := fun k => (hdb k).trans hb'
  have hZ := temperedConfig_orbitConfig (subTopDepth b) hd0 hd1
  have hconj := conj_mem_orbitConfig (subTopDepth b) hd0 hd1
  have hnonreal := im_ne_zero_orbitConfig (subTopDepth b) hd0 hd1
  have htop := topDepth_orbitConfig (subTopDepth b) hd0 hd1 hdb
  have hd_lt : ∀ m : ℕ, subTopDepth b (m + 1) < b := fun m => by
    simp only [subTopDepth]
    have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 2) := by positivity
    nlinarith only [hb, hpos]
  have habs : AbscissaLaw (orbitConfig (subTopDepth b) hd0 hd1) := by
    intro h _ hfin ρ hρ
    by_cases hlt : h < b
    · exfalso
      have hinj : Function.Injective (subTopPt b ⌈b / (b - h)⌉₊) := fun n₁ n₂ heq => by
        have him := congrArg Complex.im heq
        simp only [subTopPt] at him
        have hnat : ⌈b / (b - h)⌉₊ + n₁ + 1 = ⌈b / (b - h)⌉₊ + n₂ + 1 := by
          exact_mod_cast add_right_cancel him
        omega
      have hmem_f : ∀ n : ℕ,
          subTopPt b ⌈b / (b - h)⌉₊ n ∈ rightOf (orbitConfig (subTopDepth b) hd0 hd1) h := fun n => by
        refine ⟨⟨⌈b / (b - h)⌉₊ + n + 1, ?_, ?_⟩, ?_⟩
        · simp only [subTopPt, add_sub_cancel_left, abs_of_nonneg (hd0 _)]
        · simp only [subTopPt]
          exact abs_of_pos (by positivity)
        · simp only [subTopPt, subTopDepth]
          have hbh : 0 < b - h := sub_pos.mpr hlt
          have hN : b / (b - h) ≤ (⌈b / (b - h)⌉₊ : ℝ) := Nat.le_ceil _
          have hden : (⌈b / (b - h)⌉₊ : ℝ) + 2 ≤ ((⌈b / (b - h)⌉₊ + n : ℕ) : ℝ) + 2 := by
            push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
          have hgt : b / (b - h) < ((⌈b / (b - h)⌉₊ + n : ℕ) : ℝ) + 2 := by
            linarith only [hN, hden]
          have hposD : (0 : ℝ) < ((⌈b / (b - h)⌉₊ + n : ℕ) : ℝ) + 2 := by positivity
          have hmul : b < (((⌈b / (b - h)⌉₊ + n : ℕ) : ℝ) + 2) * (b - h) :=
            (div_lt_iff₀ hbh).mp hgt
          have hdiv : b / (((⌈b / (b - h)⌉₊ + n : ℕ) : ℝ) + 2) < b - h :=
            (div_lt_iff₀ hposD).mpr (by linarith)
          have hexp : b * (1 - 1 / (((⌈b / (b - h)⌉₊ + n : ℕ) : ℝ) + 2)) =
              b - b / (((⌈b / (b - h)⌉₊ + n : ℕ) : ℝ) + 2) := by ring
          linarith only [hdiv, hexp]
      exact (Set.infinite_range_of_injective hinj).not_finite
        (hfin.subset (by rintro _ ⟨n, rfl⟩; exact hmem_f n))
    · obtain ⟨k, hre, -⟩ := hρ
      have h1 := le_abs_self (ρ.re - 1 / 2)
      have h2 := hdb k
      linarith only [h1, hre, h2, le_of_not_gt hlt]
  have htop_fin : {ρ ∈ (orbitConfig (subTopDepth b) hd0 hd1).carrier | ρ.re = 1 / 2 + b}.Finite := by
    refine (({(⟨1 / 2 + b, 1⟩ : ℂ), (⟨1 / 2 + b, -1⟩ : ℂ)} : Set ℂ).toFinite).subset ?_
    rintro ρ ⟨⟨k, hre, him⟩, hρre⟩
    have hdk : subTopDepth b k = b := by
      rw [hρre, add_sub_cancel_left, abs_of_pos hb] at hre
      exact hre.symm
    have hk0 : k = 0 := by
      cases k with
      | zero => rfl
      | succ m => exact absurd hdk (hd_lt m).ne
    rw [hk0, Nat.cast_zero, zero_add] at him
    rcases eq_or_eq_neg_of_abs_eq him with hi | hi
    · exact Or.inl (Complex.ext hρre hi)
    · exact Or.inr (Complex.ext hρre hi)
  have htop_ne : {ρ ∈ (orbitConfig (subTopDepth b) hd0 hd1).carrier | ρ.re = 1 / 2 + b}.Nonempty := by
    refine ⟨⟨1 / 2 + b, 1⟩, ⟨0, ?_, ?_⟩, rfl⟩
    · show |1 / 2 + b - 1 / 2| = b
      rw [add_sub_cancel_left, abs_of_pos hb]
    · simp
  have htrig : ∃ T : ℝ → ℝ, IsRealTrigPoly T ∧ (∃ u, T u ≠ 0) ∧
      Tendsto (fun u => normTrace (orbitConfig (subTopDepth b) hd0 hd1) b u - T u) atTop (𝓝 0) := by
    rw [tendsto_normTrace_sub_nonzero_trigPoly_iff hZ htop,
      activeTopLayer_finite_iff_of_conj_symm hconj hb,
      activeTopLayer_nonempty_iff_of_conj_symm hconj hb]
    exact ⟨htop_fin, htop_ne⟩
  exact ⟨orbitConfig (subTopDepth b) hd0 hd1, hZ, hconj, hnonreal, htop, habs, htrig⟩

end GaloisForLFunctions.FloorFreeArithmetic
