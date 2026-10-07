import GaloisForLFunctions.RHTower.WeilConeDilationRealnessRigidity
import GaloisForLFunctions.RHTower.WeilFiniteTypeUniqueness
import GaloisForLFunctions.HTGeometry.ImStripAlmostPeriodicZeroDensity

/-!
# Dilation rigidity of the Weil cone for absolutely convergent dilation series

Let `a : ℕ → ℝ` with `Σ |a(n)| n^{−1/2+δ} < ∞` for some `δ > 0`, i.e. the Dirichlet series
`A(s) = Σ a(n) n^{−s}` converges absolutely on `Re s ≥ ½ − δ`, and let `v` be a regular sequence
(`RegularPart`).  Suppose `lam = Λ ⋆ a + v` is full-cone Weil-positive.

**Theorem** (`eq_delta_of_weilPositiveFull`).  Then `a(1) = 1` and `a(n) = 0` for every `n ≥ 2`, so
`lam = Λ + v`, and then `v = 0` (`eq_delta_and_eq_zero_of_weilPositiveFull`).  Hence within this
class a Weil-positive completion exists iff RH (`exists_dilation_weilPositive_iff`).

**Proof.**
* *Master identity.*  On `Re s > 1`, `Σ lam(n) n^{−s} = −A ζ'/ζ + E`.  Both sides of
  `Z₁ ((s − 1)(Φ − G + E) − 1) = A ((s − 1) Z₁' − Z₁)` are holomorphic on `Re s > ½`, so they agree
  there (`master_identity`).  At `s = 1` this gives `A(1) = 1`.
* *Realness.*  At a simple critical zero `ρ` the continuation `Φ` has a boundary pole with residue
  `A(ρ)`; nonnegativity of `Re Φ` on `Re s > ½` makes it real (`LSeries_im_eq_zero_of_critical_simple`).
  So `D(z) = A(½ + iz) − A(½ − iz)` vanishes at every simple critical ordinate.
* *Counting.*  `D` is an absolutely convergent exponential series on `|Im z| ≤ δ/2`, hence has
  relatively compact real translates there.  A nonzero such function has only `O(T)` real zeros in
  `[0, T]` (uniform large values on windows plus Jensen), while Zeta23 supplies `≫ T log T` simple
  critical ordinates.  So `D ≡ 0` on `|Im z| < δ/2`, i.e. `A(s) = A(1 − s)` for `|Re s − ½| < δ/2`.
* *Coefficients.*  Gluing `A` on `Re s ≥ ½` with `A(1 − s)` on `Re s ≤ ½` gives a bounded entire
  function, constant by Liouville.  The limit `A(σ) → a(1)` as `σ → ∞` and `A(1) = 1` give
  `a(1) = 1`, and uniqueness of Dirichlet coefficients gives `a(n) = 0` for `n ≥ 2`.

Compared with the finitely supported case, exponential type is replaced by almost periodicity on a
strip, and the finite reflection argument by Liouville's theorem.
-/

noncomputable section

open Complex Filter Topology Set
open scoped ComplexConjugate
open RHTower.WeilSpectral RHTower.WeilHerglotz RHTower.WeilFiniteType
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- **Strip almost periodic functions cannot vanish at all simple critical ordinates.**  A function
holomorphic on `|Im z| < η` with relatively compact real translates on `|Im z| ≤ r` (`0 < r < η`)
that vanishes at every positive simple critical ordinate vanishes on `|Im z| < r`. -/
theorem eqOn_zero_of_compactImStripTranslates_of_simpleCritical {f : ℂ → ℂ} {r η : ℝ}
    (h : HasCompactImStripTranslates f r) (hr0 : 0 < r) (hrη : r < η)
    (hf : DifferentiableOn ℂ f (imStrip η))
    (hvanish : ∀ t : ℝ, 0 < t → xi (linePt t) = 0 →
      (analyticOrderAt xi (linePt t)).toNat = 1 → f t = 0) :
    EqOn f 0 (imStrip r) := by
  intro z₀ hz₀
  by_contra hne
  obtain ⟨K, -, hK⟩ := h.exists_linear_realZero_count hr0 hrη hf hz₀ hne
  refine not_linear_bound_of_superlinear (c := 1 / (72 * Real.pi)) (by positivity)
    eventually_superlinear_xiSimpleCriticalZeroCount (K := K) (m := 0) fun T hT => ?_
  have hcount := hK T (by linarith) (xiSimpleCriticalOrdinateFinset T) fun t ht => by
    obtain ⟨ht0, htT, hxi, hs⟩ := mem_xiSimpleCriticalOrdinateFinset.mp ht
    exact ⟨ht0.le, htT, hvanish t ht0 hxi hs⟩
  rw [card_xiSimpleCriticalOrdinateFinset] at hcount
  linarith

namespace WeilInfiniteDilation

/-! ## The dilation series -/

/-- `A(s) = Σ a(n) n^{−s}`. -/
abbrev dilSeries (a : ℕ → ℝ) : ℂ → ℂ := LSeries (fun n => (a n : ℂ))

variable {a v : ℕ → ℝ} {E : ℂ → ℂ} {δ : ℝ}

theorem summable_of_le_re (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ))
    {s : ℂ} (hs : 1 / 2 - δ ≤ s.re) : LSeriesSummable (fun n => (a n : ℂ)) s :=
  ha.of_re_le_re (by simpa using hs)

theorem differentiableOn_dilSeries
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) :
    DifferentiableOn ℂ (dilSeries a) {s : ℂ | 1 / 2 - δ < s.re} := by
  refine (LSeries_differentiableOn _).mono fun s hs => ?_
  have h1 := ha.abscissaOfAbsConv_le
  simp only [mem_setOf_eq, ofReal_re] at hs h1 ⊢
  exact lt_of_le_of_lt h1 (EReal.coe_lt_coe_iff.mpr hs)

theorem finiteTypeSeq_zero_cast (a v : ℕ → ℝ) :
    (fun n => (finiteTypeSeq a 0 v n : ℂ)) =
      LSeries.convolution (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (fun n => (a n : ℂ)) + fun n => (v n : ℂ) := by
  rw [finiteTypeSeq_cast]
  have h0 : LSeries.convolution (fun n => (ArithmeticFunction.moebius n : ℂ))
      (fun n => (((0 : ℕ → ℝ) n : ℝ) : ℂ)) = 0 := by
    funext n
    simp [LSeries.convolution_def]
  rw [h0, add_zero]

/-- On `Re s > 1`: `Σ lam(n) n^{−s} = −A ζ'/ζ + E`. -/
theorem LSeries_finiteTypeSeq_zero (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hv : RegularPart v E)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (finiteTypeSeq a 0 v n : ℂ)) s =
      -(dilSeries a s * deriv riemannZeta s / riemannZeta s) + E s := by
  have hΛ := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hA : LSeriesSummable (fun n => (a n : ℂ)) s := summable_of_le_re ha (by linarith)
  rw [finiteTypeSeq_zero_cast, LSeries_add (hΛ.convolution hA) (hv.summable s hs),
    LSeries_convolution' hΛ hA, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
    ← hv.series s hs]
  ring

/-! ## The master identity -/

/-- The right side of the master identity. -/
def masterRightSeries (a : ℕ → ℝ) (s : ℂ) : ℂ :=
  dilSeries a s * ((s - 1) * deriv zetaResidueUnit s - zetaResidueUnit s)

theorem analyticOnNhd_masterRightSeries
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) :
    AnalyticOnNhd ℂ (masterRightSeries a) {s : ℂ | 1 / 2 - δ < s.re} := by
  have hU : IsOpen {s : ℂ | 1 / 2 - δ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hA := (differentiableOn_dilSeries ha).analyticOnNhd hU
  have hZ : AnalyticOnNhd ℂ zetaResidueUnit univ := fun s _ => analyticAt_zetaResidueUnit s
  have hZ' := hZ.deriv
  intro s hs
  have h1 : AnalyticAt ℂ (fun z : ℂ => z - 1) s := analyticAt_id.sub analyticAt_const
  exact (hA s hs).mul ((h1.mul (hZ' s trivial)).sub (hZ s trivial))

/-- **The master identity** on `Re s > ½`. -/
theorem master_identity (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a 0 v)) {s : ℂ} (hs : 1 / 2 < s.re) :
    masterLeft hW E s = masterRightSeries a s := by
  obtain ⟨η₀, hη₀, hEd⟩ := hv.holo
  have hE : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re} :=
    hEd.mono fun z hz => by simp only [mem_setOf_eq] at hz ⊢; linarith
  have hpre : IsPreconnected {s : ℂ | 1 / 2 < s.re} :=
    (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have h2U : (2 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by show (1 / 2 : ℝ) < (2 : ℂ).re; norm_num
  refine (analyticOnNhd_masterLeft hW hE).eqOn_of_preconnected_of_eventuallyEq
    (fun z hz => analyticOnNhd_masterRightSeries ha z
      (by simp only [mem_setOf_eq] at hz ⊢; linarith)) hpre h2U ?_ hs
  have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [hV] with z hz
  have hz : 1 < z.re := hz
  have hz1 : z ≠ 1 := by intro h; rw [h] at hz; simp at hz
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hζ : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hz
  unfold masterLeft masterRightSeries
  rw [weilContinuation_eq hW hz, weilFunction, lamC_finiteTypeSeq a rfl hv.zero hv.one,
    LSeries_finiteTypeSeq_zero hδ ha hv hz, ← sq_mul_deriv_riemannZeta hz1,
    (zetaResidueUnit_eventuallyEq hz1).eq_of_nhds]
  unfold zetaArchimedeanDatum
  field_simp
  ring

/-- **Normalization at `s = 1`**: `A(1) = Σ a(n)/n = 1`. -/
theorem dilSeries_one_eq_one (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a 0 v)) : dilSeries a 1 = 1 := by
  have h := master_identity hδ ha hv hW (s := 1) (by norm_num)
  unfold masterLeft masterRightSeries at h
  simp only [sub_self, zero_mul, zetaResidueUnit_one, zero_sub, mul_neg, mul_one] at h
  linear_combination h

/-! ## Residues at simple critical zeros -/

/-- On the half-disc at a critical zero `ρ` of order `m`, `Φ(s) = g(s)/(s − ρ)^m` with `g`
continuous at `ρ` and `g(ρ) = (ρ − 1) A(ρ) ζ'(ρ)/u(ρ)`, where `Z₁ = (s − ρ)^m u`. -/
theorem exists_boundary_quotient (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a 0 v)) {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    (hz : riemannZeta ρ = 0) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ u : ℂ → ℂ, AnalyticAt ℂ u ρ ∧ u ρ ≠ 0 ∧
      (∀ᶠ s in 𝓝 ρ, zetaResidueUnit s = (s - ρ) ^ m * u s) ∧
      ∃ g : ℂ → ℂ, ContinuousAt g ρ ∧
        g ρ = (ρ - 1) * (dilSeries a ρ * deriv riemannZeta ρ) / u ρ ∧
        ∃ r : ℝ, 0 < r ∧ ∀ s : ℂ, ρ.re < s.re → ‖s - ρ‖ < r →
          0 ≤ (g s / (s - ρ) ^ m).re := by
  have hρ1 : ρ ≠ 1 := by rintro rfl; norm_num at hρ
  have hZρ : zetaResidueUnit ρ = 0 := (zetaResidueUnit_eq_zero_iff hρ1).mpr hz
  obtain ⟨u, hu, hu0, hfac⟩ :=
    ((analyticAt_zetaResidueUnit ρ).analyticOrderAt_ne_top).mp
      (analyticOrderAt_zetaResidueUnit_ne_top ρ)
  set m := analyticOrderNatAt zetaResidueUnit ρ with hm
  have hm1 : 1 ≤ m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    have := hfac.eq_of_nhds
    rw [hm0, pow_zero, one_smul] at this
    exact hu0 (this ▸ hZρ)
  obtain ⟨η₀, hη₀, hEd⟩ := hv.holo
  set P := masterRightSeries a with hP
  set g : ℂ → ℂ := fun s => (s - ρ) ^ m * (zetaArchimedeanDatum s - E s + 1 / (s - 1)) +
    P s / (u s * (s - 1)) with hg
  have hρm1 : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have hGc : ContinuousAt zetaArchimedeanDatum ρ :=
    (differentiableAt_zetaArchimedeanDatum (by rw [hρ]; norm_num)).continuousAt
  have hEc : ContinuousAt E ρ :=
    (hEd.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by show 1 / 2 - η₀ < ρ.re; rw [hρ]; linarith))).continuousAt
  have hPc : ContinuousAt P ρ :=
    (analyticOnNhd_masterRightSeries ha ρ (by show 1 / 2 - δ < ρ.re; rw [hρ]; linarith)).continuousAt
  have hgc : ContinuousAt g ρ := by
    refine ((continuousAt_id.sub continuousAt_const).pow m |>.mul
      ((hGc.sub hEc).add (continuousAt_const.div (continuousAt_id.sub continuousAt_const)
        hρm1))).add (hPc.div (hu.continuousAt.mul (continuousAt_id.sub continuousAt_const))
        (mul_ne_zero hu0 hρm1))
  refine ⟨m, hm1, u, hu, hu0, ?_, g, hgc, ?_, ?_⟩
  · filter_upwards [hfac] with s hs
    simp only [hs, smul_eq_mul]
  · have hPρ : P ρ = (ρ - 1) ^ 2 * (dilSeries a ρ * deriv riemannZeta ρ) := by
      rw [hP]
      unfold masterRightSeries
      rw [deriv_zetaResidueUnit_of_zero hρ1 hz, hZρ]
      ring
    simp only [hg, sub_self, zero_pow (by omega : m ≠ 0), zero_mul, zero_add, hPρ]
    field_simp
  · have hev : ∀ᶠ s in 𝓝 ρ, u s ≠ 0 ∧ s ≠ 1 ∧
        zetaResidueUnit s = (s - ρ) ^ m * u s ∧ 1 / 2 - η₀ < s.re :=
      (hu.continuousAt.eventually_ne hu0).and ((eventually_ne_nhds hρ1).and
        ((hfac.mono fun s hs => by simp only [hs, smul_eq_mul]).and
          ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
            (by show 1 / 2 - η₀ < ρ.re; rw [hρ]; linarith))))
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨r, hr, fun s hs hsr => ?_⟩
    obtain ⟨hus, hs1, hZs, -⟩ := hball (by rwa [dist_eq_norm])
    have hsρ : s ≠ ρ := by rintro rfl; exact lt_irrefl _ hs
    have hs' : 1 / 2 < s.re := by rw [hρ] at hs; exact hs
    have hsρ' : s - ρ ≠ 0 := sub_ne_zero.mpr hsρ
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hmaster := master_identity hδ ha hv hW hs'
    unfold masterLeft at hmaster
    rw [hZs] at hmaster
    have hmaster' : (s - ρ) ^ m * u s *
        ((s - 1) * (weilContinuation hW s - zetaArchimedeanDatum s + E s) - 1) = P s := hmaster
    have hΦ : weilContinuation hW s = g s / (s - ρ) ^ m := by
      rw [eq_div_iff (pow_ne_zero m hsρ')]
      simp only [hg]
      rw [← hmaster']
      field_simp
      ring
    rw [← hΦ]
    exact re_weilContinuation_nonneg hW hs'

/-- **Realness at simple critical zeros**: `A(ρ)` is real. -/
theorem dilSeries_im_eq_zero_of_critical_simple (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a 0 v)) {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    (hz : riemannZeta ρ = 0) (hd : deriv riemannZeta ρ ≠ 0) :
    (dilSeries a ρ).im = 0 := by
  have hρ1 : ρ ≠ 1 := by rintro rfl; norm_num at hρ
  have hρm1 : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  obtain ⟨m, hm1, u, hu, hu0, hfac, g, hgc, hgρ, r, hr, hpos⟩ :=
    exists_boundary_quotient hδ ha hv hW hρ hz
  have hm : m = 1 := by
    by_contra hne
    have hm2 : 2 ≤ m := by omega
    have hderiv : HasDerivAt zetaResidueUnit 0 ρ := by
      have h1 : HasDerivAt (fun s => (s - ρ) ^ m * u s)
          (((m : ℂ) * (ρ - ρ) ^ (m - 1) * 1) * u ρ + (ρ - ρ) ^ m * deriv u ρ) ρ :=
        (((hasDerivAt_id ρ).sub_const ρ).pow m).mul hu.differentiableAt.hasDerivAt
      have hz1 : (ρ - ρ) ^ (m - 1) = 0 := by rw [sub_self]; exact zero_pow (by omega)
      have hz2 : (ρ - ρ) ^ m = 0 := by rw [sub_self]; exact zero_pow (by omega)
      rw [hz1, hz2] at h1
      simp only [mul_zero, zero_mul, add_zero] at h1
      exact h1.congr_of_eventuallyEq hfac
    have := hderiv.deriv
    rw [deriv_zetaResidueUnit_of_zero hρ1 hz] at this
    exact hd ((mul_eq_zero.mp this).resolve_left hρm1)
  subst hm
  have huρ : u ρ = (ρ - 1) * deriv riemannZeta ρ := by
    have hderiv : HasDerivAt zetaResidueUnit (u ρ) ρ := by
      have h1 : HasDerivAt (fun s => (s - ρ) * u s) (1 * u ρ + (ρ - ρ) * deriv u ρ) ρ :=
        ((hasDerivAt_id' ρ).sub_const ρ).mul hu.differentiableAt.hasDerivAt
      rw [sub_self, zero_mul, add_zero, one_mul] at h1
      exact h1.congr_of_eventuallyEq (hfac.mono fun s hs => by rw [hs, pow_one])
    rw [← hderiv.deriv, deriv_zetaResidueUnit_of_zero hρ1 hz]
  have hres := (boundary_pole_of_re_nonneg hr hgc le_rfl hpos).2 rfl
  have hval : g ρ = dilSeries a ρ := by
    rw [hgρ, huρ]
    field_simp
  rw [hval] at hres
  exact hres.1

/-! ## The reflection defect -/

/-- `A(conj s) = conj A(s)` for real coefficients. -/
theorem dilSeries_conj (a : ℕ → ℝ) (s : ℂ) : dilSeries a (conj s) = conj (dilSeries a s) := by
  unfold dilSeries LSeries
  rw [Complex.conj_tsum]
  congr 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have harg : (n : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀, Complex.conj_ofReal,
    Complex.cpow_conj _ _ harg, Complex.conj_natCast]

/-- The reflection defect `A(½ + iz) − A(½ − iz)`. -/
def seriesReflectionDefect (a : ℕ → ℝ) (z : ℂ) : ℂ :=
  dilSeries a (1 / 2 + z * I) - dilSeries a (1 / 2 - z * I)

theorem seriesReflectionDefect_ofReal_eq_zero {t : ℝ} (him : (dilSeries a (linePt t)).im = 0) :
    seriesReflectionDefect a t = 0 := by
  have hconj : (1 / 2 : ℂ) - (t : ℂ) * I = conj (linePt t) := by
    apply Complex.ext <;> simp [linePt]
  have hline : (1 / 2 : ℂ) + (t : ℂ) * I = linePt t := by simp [linePt]
  unfold seriesReflectionDefect
  rw [hconj, dilSeries_conj, hline, Complex.sub_conj, him]
  simp

/-- The defect vanishes at every simple critical ordinate. -/
theorem seriesReflectionDefect_eq_zero_of_simpleCritical (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a 0 v)) {t : ℝ} (hxi : xi (linePt t) = 0)
    (hsimple : (analyticOrderAt xi (linePt t)).toNat = 1) :
    seriesReflectionDefect a t = 0 := by
  have hre : (linePt t).re = 1 / 2 := by simp [linePt]
  have hstrip : 0 < (linePt t).re ∧ (linePt t).re < 1 := by rw [hre]; norm_num
  have hz : riemannZeta (linePt t) = 0 :=
    (xi_zero_iff_zeta_zero_of_mem_strip hstrip.1 hstrip.2).1 hxi
  have horder : analyticOrderAt riemannZeta (linePt t) = 1 := by
    rw [← xi_analyticOrderAt_eq_riemannZeta_of_mem_strip hstrip]
    cases h : analyticOrderAt xi (linePt t) with
    | top => rw [h] at hsimple; simp at hsimple
    | coe m =>
      rw [h] at hsimple
      simp only [ENat.toNat_coe] at hsimple
      rw [hsimple]; rfl
  have hρ1 : linePt t ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hre] at this; norm_num at this
  have hd := WeilDilationRealness.deriv_riemannZeta_ne_zero_of_order_one hρ1 horder
  exact seriesReflectionDefect_ofReal_eq_zero
    (dilSeries_im_eq_zero_of_critical_simple hδ ha hv hW hre hz hd)

/-! ## Almost periodicity of the defect -/

/-- `term a (s + w) n = term a s n · e^{−w log n}`. -/
theorem term_add (a : ℕ → ℝ) (s w : ℂ) (n : ℕ) :
    LSeries.term (fun n => (a n : ℂ)) (s + w) n =
      LSeries.term (fun n => (a n : ℂ)) s n * cexp (-(w * Real.log n)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, Complex.cpow_add _ _ hn0,
    Complex.cpow_def_of_ne_zero hn0 w, ← Complex.natCast_log, div_mul_eq_div_div, div_eq_mul_inv,
    ← Complex.exp_neg]
  ring_nf

theorem norm_term_mul_exp (a : ℕ → ℝ) {r : ℝ} (n : ℕ) :
    ‖LSeries.term (fun n => (a n : ℂ)) (1 / 2) n‖ * Real.exp (|Real.log n| * r) =
      ‖LSeries.term (fun n => (a n : ℂ)) ((1 / 2 - r : ℝ) : ℂ) n‖ := by
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  have h12 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
  rw [if_neg hn, if_neg hn, h12, Complex.ofReal_re, abs_of_nonneg hlog,
    ← Real.rpow_def_of_pos hnpos, Real.rpow_sub hnpos]
  have hp1 : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hnpos _
  have hp2 : 0 < (n : ℝ) ^ r := Real.rpow_pos_of_pos hnpos _
  field_simp

/-- **The defect is an absolutely convergent exponential series on `|Im z| ≤ r`, `r < δ`.** -/
theorem hasCompactImStripTranslates_seriesReflectionDefect
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) {r : ℝ} (hrδ : r ≤ δ) :
    HasCompactImStripTranslates (seriesReflectionDefect a) r := by
  set c : ℕ → ℂ := LSeries.term (fun n => (a n : ℂ)) (1 / 2) with hc
  have hw : Summable fun n : ℕ => ‖c n‖ * Real.exp (|-Real.log n| * r) +
      ‖-c n‖ * Real.exp (|Real.log n| * r) := by
    have hsum : Summable fun n => ‖LSeries.term (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ) n‖ :=
      summable_norm_iff.mpr ha
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hsum.mul_left 2)
    rw [abs_neg, norm_neg, hc, norm_term_mul_exp]
    have := LSeries.norm_term_le_of_re_le_re (fun n => (a n : ℂ))
      (s := ((1 / 2 - δ : ℝ) : ℂ)) (s' := ((1 / 2 - r : ℝ) : ℂ)) (by simp; linarith) n
    linarith
  have hstrip := hasCompactImStripTranslates_tsum c (fun n => -c n) (fun n => -Real.log n)
    (fun n => Real.log n) hw
  intro ε hε
  obtain ⟨S, hS⟩ := hstrip ε hε
  refine ⟨S, fun t => ?_⟩
  obtain ⟨s, hs, hts⟩ := hS t
  refine ⟨s, hs, fun z hz => ?_⟩
  -- the defect equals the exponential series on the closed strip
  have hid : ∀ u : ℂ, |u.im| ≤ r → seriesReflectionDefect a u =
      ∑' n, (c n * cexp (I * ((-Real.log n : ℝ) : ℂ) * u) +
        -c n * cexp (I * ((Real.log n : ℝ) : ℂ) * u)) := by
    intro u hu
    have hu' := abs_le.mp hu
    have h1 : LSeriesSummable (fun n => (a n : ℂ)) (1 / 2 + u * I) :=
      summable_of_le_re ha (by simp; linarith)
    have h2 : LSeriesSummable (fun n => (a n : ℂ)) (1 / 2 - u * I) :=
      summable_of_le_re ha (by simp; linarith)
    unfold seriesReflectionDefect dilSeries LSeries
    rw [← h1.tsum_sub h2]
    congr 1
    funext n
    rw [sub_eq_add_neg (1 / 2 : ℂ), term_add, term_add, ← hc]
    push_cast
    ring_nf
  have hzt : |(z + t).im| ≤ r := by simpa using hz
  have hzs : |(z + s).im| ≤ r := by simpa using hz
  rw [hid _ hzt, hid _ hzs]
  exact hts z hz

theorem differentiableOn_seriesReflectionDefect
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) :
    DifferentiableOn ℂ (seriesReflectionDefect a) (imStrip δ) := by
  have hA := differentiableOn_dilSeries ha
  intro z hz
  have hz' := abs_lt.mp (mem_imStrip.mp hz)
  have h1 : DifferentiableAt ℂ (dilSeries a) (1 / 2 + z * I) :=
    hA.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by simp; linarith))
  have h2 : DifferentiableAt ℂ (dilSeries a) (1 / 2 - z * I) :=
    hA.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by simp; linarith))
  unfold seriesReflectionDefect
  exact ((h1.comp z ((differentiableAt_const _).add (differentiableAt_id.mul_const I))).sub
    (h2.comp z ((differentiableAt_const _).sub (differentiableAt_id.mul_const I)))).differentiableWithinAt

/-! ## Coefficients -/

/-- **The defect vanishes on a strip**, hence `A(s) = A(1 − s)` for `|Re s − ½| < δ/2`. -/
theorem dilSeries_reflect (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a 0 v)) {s : ℂ} (hs : |s.re - 1 / 2| < δ / 2) :
    dilSeries a s = dilSeries a (1 - s) := by
  have hzero := eqOn_zero_of_compactImStripTranslates_of_simpleCritical (r := δ / 2) (η := δ)
    (hasCompactImStripTranslates_seriesReflectionDefect ha (by linarith))
    (by positivity) (by linarith) (differentiableOn_seriesReflectionDefect ha)
    (fun t _ hxi hsimple => seriesReflectionDefect_eq_zero_of_simpleCritical hδ ha hv hW hxi hsimple)
  set z : ℂ := (s - 1 / 2) * -I with hz
  have hzim : z.im = -(s.re - 1 / 2) := by simp [hz]
  have hzs : z ∈ imStrip (δ / 2) := by
    rw [mem_imStrip, hzim, abs_neg]
    exact hs
  have h := hzero hzs
  simp only [seriesReflectionDefect, Pi.zero_apply, sub_eq_zero] at h
  have e1 : (1 / 2 : ℂ) + z * I = s := by
    rw [hz]; ring_nf; rw [I_sq]; ring
  have e2 : (1 / 2 : ℂ) - z * I = 1 - s := by
    rw [hz]; ring_nf; rw [I_sq]; ring
  rwa [e1, e2] at h

theorem norm_dilSeries_le (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ))
    (hδ : 0 < δ) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖dilSeries a s‖ ≤ ∑' n, ‖LSeries.term (fun n => (a n : ℂ)) (1 / 2) n‖ := by
  have hsum : Summable fun n => ‖LSeries.term (fun n => (a n : ℂ)) (1 / 2) n‖ :=
    summable_norm_iff.mpr (summable_of_le_re ha (by norm_num; linarith))
  have hle : ∀ n, ‖LSeries.term (fun n => (a n : ℂ)) s n‖ ≤
      ‖LSeries.term (fun n => (a n : ℂ)) (1 / 2) n‖ :=
    LSeries.norm_term_le_of_re_le_re _ (by norm_num; linarith)
  exact (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hle hsum)).trans
    (Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hle hsum) hsum)

/-- **Liouville**: `A` is constant on `Re s ≥ ½`. -/
theorem dilSeries_eq_const (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a 0 v)) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    dilSeries a s = dilSeries a 2 := by
  classical
  set H : ℂ → ℂ := fun w => if 1 / 2 ≤ w.re then dilSeries a w else dilSeries a (1 - w) with hH
  have hA := differentiableOn_dilSeries ha
  have hright : ∀ w : ℂ, 1 / 2 - δ / 2 < w.re → H w = dilSeries a w := by
    intro w hw
    simp only [hH]
    split_ifs with h
    · rfl
    · push Not at h
      exact (dilSeries_reflect hδ ha hv hW (by rw [abs_lt]; constructor <;> linarith)).symm
  have hleft : ∀ w : ℂ, w.re < 1 / 2 + δ / 2 → H w = dilSeries a (1 - w) := by
    intro w hw
    simp only [hH]
    split_ifs with h
    · exact dilSeries_reflect hδ ha hv hW (by rw [abs_lt]; constructor <;> linarith)
    · rfl
  have hHd : Differentiable ℂ H := by
    intro w
    by_cases hw : 1 / 2 - δ / 2 < w.re
    · have hev : H =ᶠ[𝓝 w] dilSeries a :=
        Filter.eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw)
          fun u hu => hright u hu
      exact (hA.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show 1 / 2 - δ < w.re by linarith))).congr_of_eventuallyEq hev
    · push Not at hw
      have hw' : w.re < 1 / 2 + δ / 2 := by linarith
      have hev : H =ᶠ[𝓝 w] fun u => dilSeries a (1 - u) :=
        Filter.eventually_of_mem ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds hw')
          fun u hu => hleft u hu
      have hd : DifferentiableAt ℂ (dilSeries a) (1 - w) :=
        hA.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
          (by simp; linarith))
      exact (hd.comp w ((differentiableAt_const _).sub differentiableAt_id)).congr_of_eventuallyEq
        hev
  have hHb : Bornology.IsBounded (range H) := by
    refine isBounded_iff_forall_norm_le.mpr
      ⟨∑' n, ‖LSeries.term (fun n => (a n : ℂ)) (1 / 2) n‖, ?_⟩
    rintro _ ⟨w, rfl⟩
    simp only [hH]
    split_ifs with h
    · exact norm_dilSeries_le ha hδ h
    · push Not at h
      exact norm_dilSeries_le ha hδ (by simp; linarith)
  have hconst := hHd.apply_eq_apply_of_bounded hHb s 2
  have hs2 : H 2 = dilSeries a 2 := hright 2 (by norm_num; linarith)
  rw [← hs2, ← hconst, hright s (by linarith)]

/-- **Dilation rigidity of the Weil cone, infinite type.**  If `Λ ⋆ a + v` is full-cone
Weil-positive, with `Σ |a(n)| n^{−1/2+δ} < ∞` for some `δ > 0` and `v` regular, then `a = δ₁`. -/
theorem eq_delta_of_weilPositiveFull (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a 0 v)) :
    a 1 = 1 ∧ ∀ n, 2 ≤ n → a n = 0 := by
  classical
  have habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) < ⊤ :=
    lt_of_le_of_lt ha.abscissaOfAbsConv_le (EReal.coe_lt_top _)
  -- `A(σ) = A(2)` for real `σ ≥ ½`, and `A(σ) → a(1)`
  have hconst : ∀ σ : ℝ, 1 / 2 ≤ σ → dilSeries a σ = dilSeries a 2 := fun σ hσ =>
    dilSeries_eq_const hδ ha hv hW (by simpa using hσ)
  have hlim := LSeries.tendsto_atTop habs
  have ha1 : ((a 1 : ℝ) : ℂ) = dilSeries a 2 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop (1 / 2 : ℝ)] with σ hσ
      exact (hconst σ hσ).symm))
  have hone : dilSeries a 1 = 1 := dilSeries_one_eq_one hδ ha hv hW
  have ha1' : a 1 = 1 := by
    have h := hconst 1 (by norm_num)
    push_cast at h
    rw [hone, ← ha1] at h
    exact_mod_cast h.symm
  refine ⟨ha1', ?_⟩
  -- the coefficients beyond the first
  set b : ℕ → ℂ := fun n => if n = 1 then 0 else (a n : ℂ) with hb
  set e : ℕ → ℂ := fun n => if n = 1 then (a 1 : ℂ) else 0 with he
  have hab : (fun n => (a n : ℂ)) = b + e := by
    funext n
    simp only [hb, he, Pi.add_apply]
    split_ifs with h <;> simp [h]
  have heS : ∀ s : ℂ, LSeriesSummable e s := fun s =>
    summable_of_ne_finset_zero (s := {1}) fun n hn => by
      have : n ≠ 1 := by simpa using hn
      simp [LSeries.term, he, this]
  have hLe : ∀ s : ℂ, LSeries e s = a 1 := by
    intro s
    rw [LSeries, tsum_eq_single 1 fun n hn => by simp [LSeries.term, he, hn]]
    simp [LSeries.term, he]
  have hbS : ∀ s : ℂ, 1 / 2 - δ ≤ s.re → LSeriesSummable b s := by
    intro s hs
    have h := summable_of_le_re ha hs
    have hbe : b = (fun n => (a n : ℂ)) - e := by rw [hab]; abel
    rw [hbe]
    exact (LSeriesSummable.sub h (heS s))
  have hLb : (fun x : ℝ => LSeries b x) =ᶠ[atTop] 0 := by
    filter_upwards [eventually_ge_atTop (1 / 2 : ℝ)] with σ hσ
    have h := LSeries_add (hbS σ (by simp; linarith)) (heS σ)
    rw [← hab, hLe] at h
    simp only [Pi.zero_apply]
    have hσ' := hconst σ hσ
    have h2 : LSeries (fun n => (a n : ℂ)) 2 = (a 1 : ℂ) := ha1.symm
    unfold dilSeries at hσ'
    rw [hσ', h2] at h
    linear_combination -h
  rcases LSeries_eventually_eq_zero_iff'.mp hLb with hzero | htop
  · intro n hn
    have h := hzero n (by omega)
    simp only [hb, if_neg (show n ≠ 1 by omega)] at h
    exact_mod_cast h
  · exfalso
    have := (hbS _ (le_refl (((1 / 2 - δ : ℝ) : ℂ).re)) |>.abscissaOfAbsConv_le)
    rw [htop] at this
    exact absurd this (not_le.mpr (EReal.coe_lt_top _))

/-- **A Weil-positive infinite dilation system of `Λ` forces RH.**  If `Λ ⋆ a` is full-cone
Weil-positive for some `a` with `Σ |a(n)| n^{−1/2+δ} < ∞`, `δ > 0`, then `a = δ₁`, so `Λ` itself is
Weil-positive and RH holds. -/
theorem riemannHypothesis_of_weilPositiveFull_dilation (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ))
    (hW : WeilPositiveFull (finiteTypeSeq a 0 0)) : RiemannHypothesis := by
  obtain ⟨h1, h2⟩ := eq_delta_of_weilPositiveFull hδ ha WeilDilationRealness.regularPart_zero hW
  have hlam : finiteTypeSeq a 0 0 = fun n => (ArithmeticFunction.vonMangoldt n : ℝ) := by
    funext n
    rw [WeilDilationRealness.finiteTypeSeq_eq_vonMangoldt_add h1 h2]
    simp
  rw [hlam] at hW
  refine RHTower.WeilSpectral.riemannHypothesis_of_weilPositiveFull_of_summable_deviationPos hW
    fun σ _ => ?_
  simp [RHTower.WeilSpectral.deviationPos]

theorem finiteTypeSeq_eq_delta {a : ℕ → ℝ} (h1 : a 1 = 1) (h2 : ∀ n, 2 ≤ n → a n = 0)
    (v : ℕ → ℝ) :
    finiteTypeSeq a 0 v = finiteTypeSeq (fun n => if n = 1 then 1 else 0) 0 v := by
  funext n
  unfold finiteTypeSeq
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp0 : p.2 ≠ 0 := by
    obtain ⟨hmul, hn⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    intro h
    rw [h, mul_zero] at hmul
    exact hn hmul.symm
  have hq : a p.2 = if p.2 = 1 then 1 else 0 := by
    split_ifs with h
    · rw [h, h1]
    · exact h2 _ (by omega)
  rw [hq]

/-- **Full uniqueness in the dilation class**: `a = δ₁` and `v = 0`. -/
theorem eq_delta_and_eq_zero_of_weilPositiveFull (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a 0 v)) :
    a 1 = 1 ∧ (∀ n, 2 ≤ n → a n = 0) ∧ ∀ n, v n = 0 := by
  obtain ⟨h1, h2⟩ := eq_delta_of_weilPositiveFull hδ ha hv hW
  refine ⟨h1, h2, ?_⟩
  rw [finiteTypeSeq_eq_delta h1 h2] at hW
  exact WeilFiniteType.regularPart_eq_zero (N := 1) ⟨by simp, fun n hn => if_neg (by omega)⟩
    ⟨rfl, fun _ _ => rfl⟩ rfl hv hW

/-- **Within the dilation class, a Weil-positive completion exists iff RH.**  The class consists of
`Λ ⋆ a + v` with `Σ |a(n)| n^{−1/2+δ} < ∞` for some `δ > 0` and `v` regular. -/
theorem exists_dilation_weilPositive_iff :
    (∃ (a v : ℕ → ℝ) (E : ℂ → ℂ) (δ : ℝ), 0 < δ ∧
      LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ) ∧ RegularPart v E ∧
      WeilPositiveFull (finiteTypeSeq a 0 v)) ↔ RiemannHypothesis := by
  rw [riemannHypothesis_iff_weilPositiveFull_vonMangoldt]
  constructor
  · rintro ⟨a, v, E, δ, hδ, ha, hv, hW⟩
    obtain ⟨h1, h2, h3⟩ := eq_delta_and_eq_zero_of_weilPositiveFull hδ ha hv hW
    have hv' : v = fun _ => 0 := funext h3
    rw [finiteTypeSeq_eq_delta h1 h2, hv'] at hW
    have e : finiteTypeSeq (fun n => if n = 1 then 1 else 0) 0 (fun _ => 0) =
        finiteTypeSeq (fun n => if n = 1 then 1 else 0) (fun _ => 0) (fun _ => 0) := rfl
    rw [e, WeilFiniteType.finiteTypeSeq_delta_zero_zero] at hW
    exact hW
  · intro hW
    refine ⟨fun n => if n = 1 then 1 else 0, fun _ => 0, fun _ => 0, 1, one_pos, ?_,
      WeilFiniteType.regularPart_zero, ?_⟩
    · refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
      have : n ≠ 1 := by simpa using hn
      simp [LSeries.term, this]
    · have e : finiteTypeSeq (fun n => if n = 1 then 1 else 0) 0 (fun _ => 0) =
          finiteTypeSeq (fun n => if n = 1 then 1 else 0) (fun _ => 0) (fun _ => 0) := rfl
      rw [e, WeilFiniteType.finiteTypeSeq_delta_zero_zero]
      exact hW

end WeilInfiniteDilation

end RHTower
