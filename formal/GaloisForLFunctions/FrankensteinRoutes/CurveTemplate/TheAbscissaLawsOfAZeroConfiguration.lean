import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheScalingSurfaceOfACurve
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheZerosOfAnExponentialPolynomialRecur
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheHyperellipticCalibration
import GaloisForLFunctions.RHTower.CrossRouteReceiverBridges
import GaloisForLFunctions.RHTower.ZetaWeakRecurrenceLadderCollapse

/-!
# The abscissa laws of a zero configuration: the curve proof and ζ in one language

For a zero configuration `Z` (a reflection-symmetric, ordinate-locally-finite multiset of points of
the strip) put

* **ZAL** (`ZeroConfig.ApproachesLine`): for every `h > 0` only finitely many zeros have
  `Re ρ > ½ + h`;
* **AAL** (`ZeroConfig.AbscissaLaw`): for every `h ≥ 0`, finitely many zeros right of `½ + h`
  means none;
* **purity**: every zero is on `Re ρ = ½`.

**Theorems.**
* `pure_iff_approachesLine_and_abscissaLaw`: purity ⇔ ZAL ∧ AAL, for every configuration (the
  reflection `ρ ↦ 1 − ρ̄` gives the left half).
* `abscissaLaw_iff_transport`: AAL ⇔ every zero right of the line has, for every `ε > 0` and every
  height `T`, a zero with real part `> Re ρ − ε` and `|Im| > T`. This is exactly the zero-level
  conclusion of weak recurrence: AAL is the trace of recurrence on the zero set.
* `abscissaLaw_of_verticallyRecurrent`: recurrence gives AAL. Curves (periodic in height) and
  zero sets of exponential polynomials satisfy AAL unconditionally (`curveConfig_abscissaLaw`,
  `abscissaLaw_of_expPoly`).
* Curves (`curveConfig_approachesLine_iff_unitary`): for a curve datum in the strip, ZAL ⇔ purity
  ⇔ unitarity. For odd hyperelliptic curves all hold (`hyperellipticConfig_pure`).
* ζ (`zetaZeroConfig_abscissaLaw_iff`, `zetaZeroConfig_approachesLine_iff`): the configuration
  laws of `zetaZeroConfig` are `AsymptoticAbscissaLaw` and `ZerosApproachLine`.
* `pairConfig_not_abscissaLaw`: the reflection symmetry of a configuration does not give the
  finite case of AAL: `{ρ, 1 − ρ̄}` approaches the line and violates AAL at `h = 0`.

So, in the coordinate where both laws are stated, the curve proof splits as: AAL is supplied by the
Frobenius (periodicity of the zeros in height), and ZAL is the whole content (Stepanov's count,
power sums and the functional equation).
-/

open Complex Set
open Zeta23

noncomputable section

namespace GaloisForLFunctions.FrankensteinRoutes

open ArithmeticCastelnuovoSeveri

namespace ZeroConfig'

variable (Z : ZeroConfig)

/-- The zeros with `Re ρ > ½ + h`. -/
def rightOf (h : ℝ) : Set ℂ := {ρ ∈ Z.carrier | 1 / 2 + h < ρ.re}

/-- **ZAL**: finitely many zeros beyond every positive depth. -/
def ApproachesLine : Prop := ∀ h : ℝ, 0 < h → (rightOf Z h).Finite

/-- **AAL at depth `h`**: finitely many zeros right of `½ + h` means none. -/
def AbscissaLawAt (h : ℝ) : Prop := (rightOf Z h).Finite → ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + h

/-- **AAL**: the abscissa law at every depth `h ≥ 0`. -/
def AbscissaLaw : Prop := ∀ h : ℝ, 0 ≤ h → AbscissaLawAt Z h

/-- **Purity**: every zero lies on the critical line. -/
def Pure : Prop := ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2

theorem re_reflect (ρ : ℂ) : (reflect ρ).re = 1 - ρ.re := by simp [reflect]

theorem pure_iff_forall_re_le : Pure Z ↔ ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 := by
  refine ⟨fun h ρ hρ => (h ρ hρ).le, fun h ρ hρ => le_antisymm (h ρ hρ) ?_⟩
  have := h _ (Z.reflect_mem ρ hρ)
  rw [re_reflect] at this
  linarith

/-- **Purity is ZAL plus AAL**, for every zero configuration. -/
theorem pure_iff_approachesLine_and_abscissaLaw :
    Pure Z ↔ ApproachesLine Z ∧ AbscissaLaw Z := by
  constructor
  · intro hP
    have hempty : ∀ h, 0 ≤ h → rightOf Z h = ∅ := fun h hh => by
      ext ρ
      simp only [rightOf, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
      intro hρ
      rw [hP ρ hρ]
      linarith
    refine ⟨fun h hh => by rw [hempty h hh.le]; exact finite_empty, fun h hh _ ρ hρ => ?_⟩
    rw [hP ρ hρ]
    linarith
  · rintro ⟨hZ, hA⟩
    rw [pure_iff_forall_re_le]
    intro ρ hρ
    by_contra hlt
    push Not at hlt
    have hh : 0 < (ρ.re - 1 / 2) / 2 := by linarith
    have := hA _ hh.le (hZ _ hh) ρ hρ
    linarith

/-! ### AAL is zero transport -/

/-- A set of zeros of bounded height is finite (local finiteness in the ordinate). -/
theorem finite_of_abs_im_le (T : ℝ) : {ρ ∈ Z.carrier | |ρ.im| ≤ T}.Finite :=
  (Z.finite_window (-T - 1) T).subset fun ρ ⟨hρ, hT⟩ =>
    ⟨hρ, by linarith [neg_abs_le ρ.im], (abs_le.mp hT).2⟩

/-- **AAL is zero transport.** The abscissa law holds iff every zero right of the line has, for
every `ε > 0` and every height `T`, a zero of real part `> Re ρ − ε` and height `|Im| > T`. -/
theorem abscissaLaw_iff_transport :
    AbscissaLaw Z ↔ ∀ ρ ∈ Z.carrier, 1 / 2 < ρ.re → ∀ ε > 0, ∀ T : ℝ,
      ∃ ρ' ∈ Z.carrier, ρ.re - ε < ρ'.re ∧ T < |ρ'.im| := by
  constructor
  · intro hA ρ hρ hre ε hε T
    by_contra hno
    push Not at hno
    -- the depth `h` with `½ + h = max (Re ρ − ε) ½`
    set h := max (ρ.re - ε) (1 / 2) - 1 / 2 with hhdef
    have hh : 0 ≤ h := by rw [hhdef]; linarith [le_max_right (ρ.re - ε) (1 / 2)]
    have hfin : (rightOf Z h).Finite := (finite_of_abs_im_le Z T).subset fun ρ' ⟨hρ', hlt⟩ =>
      ⟨hρ', hno ρ' hρ' (by
        have : ρ.re - ε ≤ 1 / 2 + h := by rw [hhdef]; linarith [le_max_left (ρ.re - ε) (1 / 2)]
        linarith)⟩
    have := hA h hh hfin ρ hρ
    have hlt : 1 / 2 + h < ρ.re := by
      rw [hhdef]
      have : max (ρ.re - ε) (1 / 2) < ρ.re := max_lt (by linarith) hre
      linarith
    linarith
  · intro hT h hh hfin ρ hρ
    by_contra hlt
    push Not at hlt
    obtain ⟨M, hM⟩ := (hfin.image fun z => |z.im|).bddAbove
    obtain ⟨ρ', hρ', hre', him'⟩ := hT ρ hρ (by linarith) (ρ.re - (1 / 2 + h)) (by linarith) M
    have := hM ⟨ρ', ⟨hρ', by linarith⟩, rfl⟩
    linarith

/-- **Recurrence gives AAL.** -/
theorem abscissaLaw_of_verticallyRecurrent (hrec : VerticallyRecurrent Z) : AbscissaLaw Z := by
  rw [abscissaLaw_iff_transport]
  intro ρ hρ _ ε hε T
  obtain ⟨ρ', hρ', hT, hclose⟩ := hrec ρ hρ ε hε T
  exact ⟨ρ', hρ', by linarith [(abs_lt.mp hclose).1], hT.trans_le (le_abs_self _)⟩

/-- Under recurrence, ZAL is purity. -/
theorem pure_iff_approachesLine_of_verticallyRecurrent (hrec : VerticallyRecurrent Z) :
    Pure Z ↔ ApproachesLine Z := by
  rw [pure_iff_approachesLine_and_abscissaLaw]
  exact ⟨And.left, fun h => ⟨h, abscissaLaw_of_verticallyRecurrent Z hrec⟩⟩

/-- **Zeros of exponential polynomials satisfy AAL.** A configuration cut out by a nonzero
`Σ_j c_j e^{λ_j s}` (finite Dirichlet polynomials included) recurs, hence obeys the law. -/
theorem abscissaLaw_of_expPoly {r : ℕ} (c : Fin r → ℂ) (w : Fin r → ℝ)
    (hne : ∃ s, expPoly c w s ≠ 0) (hZ : ∀ s, s ∈ Z.carrier ↔ expPoly c w s = 0) :
    AbscissaLaw Z :=
  abscissaLaw_of_verticallyRecurrent Z (verticallyRecurrent_of_expPoly Z c w hne hZ)

/-! ### The finite case is not given by the reflection symmetry -/

/-- The configuration `{ρ, 1 − ρ̄}` of one reflection pair. -/
def pairConfig (ρ : ℂ) (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1) : ZeroConfig where
  carrier := {ρ, reflect ρ}
  mult _ := 1
  one_le_mult _ _ := le_rfl
  strip := by
    rintro z (rfl | rfl)
    · exact ⟨h0, h1⟩
    · rw [re_reflect]; exact ⟨by linarith, by linarith⟩
  reflect_mem := by
    rintro z (rfl | rfl)
    · exact Or.inr rfl
    · left; simp [reflect]
  mult_reflect _ _ := rfl
  finite_window _ _ := ((finite_singleton _).insert _).subset inter_subset_left

/-- **The reflection symmetry does not exclude a finite exceptional set.** For `½ < Re ρ ≤ 1` the
configuration `{ρ, 1 − ρ̄}` satisfies ZAL and violates AAL at `h = 0`. -/
theorem pairConfig_not_abscissaLaw {ρ : ℂ} (h12 : 1 / 2 < ρ.re) (h1 : ρ.re ≤ 1) :
    ApproachesLine (pairConfig ρ (by linarith) h1) ∧
      ¬ AbscissaLawAt (pairConfig ρ (by linarith) h1) 0 := by
  have hfin : ∀ h, (rightOf (pairConfig ρ (by linarith) h1) h).Finite := fun h =>
    ((finite_singleton _).insert _).subset fun z hz => hz.1
  refine ⟨fun h _ => hfin h, fun hA => ?_⟩
  have := hA (hfin 0) ρ (Or.inl rfl)
  linarith

end ZeroConfig'

/-! ### Curves: the Frobenius supplies AAL -/

namespace CurveTemplate

open ZeroConfig'

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι) (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq)

/-- **AAL holds on every curve**: the zeros are periodic in height. -/
theorem curveConfig_abscissaLaw : AbscissaLaw (D.curveConfig hD) :=
  abscissaLaw_of_verticallyRecurrent _
    (verticallyRecurrent_of_periodic _ D.period_pos (D.curveConfig_periodic hD))

/-- Purity of a curve configuration is unitarity of the normalized eigenvalues. -/
theorem curveConfig_pure_iff_unitary : Pure (D.curveConfig hD) ↔ ∀ i, ‖D.β i‖ = 1 := by
  rw [pure_iff_forall_re_le]
  constructor
  · intro h
    by_contra hU
    obtain ⟨z, hz⟩ := D.nonempty_outerSpectrum_iff.mpr hU
    obtain ⟨_, ⟨⟨i, k⟩, rfl⟩, hre⟩ := (D.rightZeros_curveConfig_nonempty_iff hD).mpr ⟨z, hz⟩
    exact absurd (h _ ⟨⟨i, k⟩, rfl⟩) (not_le.mpr hre)
  · rintro hU _ ⟨⟨i, k⟩, rfl⟩
    exact not_lt.mp fun h => lt_irrefl _ ((hU i) ▸ (D.re_zetaZero_gt_iff i k).mp h)

/-- **On a curve ZAL is RH**: AAL is free, so the crude half carries the whole content. -/
theorem curveConfig_approachesLine_iff_unitary :
    ApproachesLine (D.curveConfig hD) ↔ ∀ i, ‖D.β i‖ = 1 := by
  rw [← curveConfig_pure_iff_unitary,
    pure_iff_approachesLine_of_verticallyRecurrent _
      (verticallyRecurrent_of_periodic _ D.period_pos (D.curveConfig_periodic hD))]

section Hyperelliptic

open ArithmeticEffectivityTheory Polynomial

variable {F : Type*} [Field F] [Fintype F] (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f)
  (hodd : Odd f.natDegree)

/-- The hyperelliptic datum lies in the strip. -/
theorem hyperellipticDatum_strip :
    ∀ i, ‖(hyperellipticDatum hF hsq hodd).β i‖ ≤ (hyperellipticDatum hF hsq hodd).sqrtq := by
  intro i
  rw [hyperellipticDatum_unitary hF hsq hodd i]
  have hq := (hyperellipticDatum hF hsq hodd).one_lt_q
  exact Real.one_le_sqrt.mpr hq.le

/-- **The curve template closes on odd hyperelliptic curves**: ZAL, AAL and purity of the zero
configuration of `y² = f(x)` all hold. -/
theorem hyperellipticConfig_pure :
    Pure ((hyperellipticDatum hF hsq hodd).curveConfig (hyperellipticDatum_strip hF hsq hodd)) ∧
      ApproachesLine
        ((hyperellipticDatum hF hsq hodd).curveConfig (hyperellipticDatum_strip hF hsq hodd)) ∧
      AbscissaLaw
        ((hyperellipticDatum hF hsq hodd).curveConfig (hyperellipticDatum_strip hF hsq hodd)) :=
  ⟨(curveConfig_pure_iff_unitary _ _).mpr (hyperellipticDatum_unitary hF hsq hodd),
    (curveConfig_approachesLine_iff_unitary _ _).mpr (hyperellipticDatum_unitary hF hsq hodd),
    curveConfig_abscissaLaw _ _⟩

end Hyperelliptic

end CurveTemplate

/-! ### ζ: the configuration laws are the corpus laws -/

namespace ZetaTemplate

open ZeroConfig' RHTower RHTower.CrossRouteReceiverBridges

/-- The copies of the zeros right of `½ + h` are finite iff the zeros are. -/
theorem finite_copies_iff (h : ℝ) :
    {q : XiZeroCopy | 1 / 2 + h < (q.1 : ℂ).re}.Finite ↔ (rightOf zetaZeroConfig h).Finite := by
  constructor
  · intro hc
    refine ((hc.image fun q : XiZeroCopy => (q.1 : ℂ))).subset fun ρ ⟨hρ, hre⟩ => ?_
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero
      (mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp hρ).1
    exact ⟨q, by show 1 / 2 + h < (q.1 : ℂ).re; rw [hq]; exact hre, hq⟩
  · intro hp
    -- the support points right of `½ + h` are finite, and each carries finitely many copies
    have hs : {ρ : XiDivisorSupport | 1 / 2 + h < (ρ : ℂ).re}.Finite :=
      (hp.preimage Subtype.val_injective.injOn).subset fun ρ hre =>
        ⟨mem_zetaZeroConfig_carrier_of_xi_eq_zero (xi_eq_zero_of_mem_divisor_support ρ), hre⟩
    refine (hs.preimage' fun ρ _ => ?_).subset fun q hq => hq
    exact (Set.finite_range (fun k => (⟨ρ, k⟩ : XiZeroCopy))).subset fun q hq => by
      obtain ⟨ρ', k⟩ := q
      simp only [mem_preimage, mem_singleton_iff] at hq
      subst hq
      exact ⟨k, rfl⟩

/-- **The configuration AAL of ζ is `AsymptoticAbscissaLaw`.** -/
theorem zetaZeroConfig_abscissaLaw_iff : AbscissaLaw zetaZeroConfig ↔ AsymptoticAbscissaLaw := by
  refine forall₂_congr fun h _ => ?_
  rw [AbscissaLawAt, finite_copies_iff]
  refine imp_congr_right fun _ => ⟨fun H q => H _ (xiZeroCopy_mem_zetaZeroConfig_carrier q),
    fun H ρ hρ => ?_⟩
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero
    (mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp hρ).1
  rw [← hq]
  exact H q

/-- The left copies of depth `> h` are the reflections of the right copies. -/
theorem deepCopies_finite_iff (h : ℝ) :
    (CosineDefectBudget.deepCopies h).Finite ↔ (rightOf zetaZeroConfig h).Finite := by
  have hdeep : ∀ q : XiZeroCopy, q ∈ CosineDefectBudget.deepCopies h ↔ (q.1 : ℂ).re < 1 / 2 - h :=
    fun q => by
      show h < (xiSpectralPoint q).im ↔ _
      simp only [xiSpectralPoint, mul_im, sub_re, sub_im, neg_re, neg_im, I_re, I_im]
      norm_num
      constructor <;> intro <;> linarith
  -- left zeros of depth `> h` are finite iff right ones are, by reflection
  have hleft : {q : XiZeroCopy | (q.1 : ℂ).re < 1 / 2 - h}.Finite ↔
      {ρ ∈ zetaZeroConfig.carrier | ρ.re < 1 / 2 - h}.Finite := by
    constructor
    · intro hc
      refine ((hc.image fun q : XiZeroCopy => (q.1 : ℂ))).subset fun ρ ⟨hρ, hre⟩ => ?_
      obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero
        (mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp hρ).1
      exact ⟨q, by show (q.1 : ℂ).re < 1 / 2 - h; rw [hq]; exact hre, hq⟩
    · intro hp
      have hs : {ρ : XiDivisorSupport | (ρ : ℂ).re < 1 / 2 - h}.Finite :=
        (hp.preimage Subtype.val_injective.injOn).subset fun ρ hre =>
          ⟨mem_zetaZeroConfig_carrier_of_xi_eq_zero (xi_eq_zero_of_mem_divisor_support ρ), hre⟩
      refine (hs.preimage' fun ρ _ => ?_).subset fun q hq => hq
      exact (Set.finite_range (fun k => (⟨ρ, k⟩ : XiZeroCopy))).subset fun q hq => by
        obtain ⟨ρ', k⟩ := q
        simp only [mem_preimage, mem_singleton_iff] at hq
        subst hq
        exact ⟨k, rfl⟩
  have hrefl : {ρ ∈ zetaZeroConfig.carrier | ρ.re < 1 / 2 - h} =
      reflect '' rightOf zetaZeroConfig h := by
    ext ρ
    constructor
    · rintro ⟨hρ, hre⟩
      refine ⟨reflect ρ, ⟨zetaZeroConfig.reflect_mem ρ hρ, ?_⟩, by simp [reflect]⟩
      rw [re_reflect]; linarith
    · rintro ⟨z, ⟨hz, hre⟩, rfl⟩
      exact ⟨zetaZeroConfig.reflect_mem z hz, by rw [re_reflect]; linarith⟩
  have hinj : InjOn reflect (rightOf zetaZeroConfig h) := fun a _ b _ hab => by
    have := congrArg reflect hab
    simpa [reflect] using this
  rw [show CosineDefectBudget.deepCopies h = {q : XiZeroCopy | (q.1 : ℂ).re < 1 / 2 - h} from
    Set.ext hdeep, hleft, hrefl, finite_image_iff hinj]

/-- **The configuration ZAL of ζ is `ZerosApproachLine`.** -/
theorem zetaZeroConfig_approachesLine_iff :
    ApproachesLine zetaZeroConfig ↔ BacklundConverse.ZerosApproachLine :=
  forall₂_congr fun h _ => (deepCopies_finite_iff h).symm

/-- **The template over ℤ**: RH ⇔ ZAL ∧ AAL on the zero configuration of ζ, and AAL is zero
transport. -/
theorem riemannHypothesis_iff_template :
    RiemannHypothesis ↔ ApproachesLine zetaZeroConfig ∧ AbscissaLaw zetaZeroConfig := by
  rw [← pure_iff_approachesLine_and_abscissaLaw, riemannHypothesis_iff_zetaZeroConfig_onLine]
  rfl

end ZetaTemplate

end GaloisForLFunctions.FrankensteinRoutes
