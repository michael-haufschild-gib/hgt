import GaloisForLFunctions.RHTower.WeilConeInfiniteDilationRigidity
import GaloisForLFunctions.RHTower.HardyZPhaseAsymptotic

/-!
# The `|ζ|²`-weighted boundary inequality for Weil-positive dilation systems

Let `a, f : ℕ → ℝ` with `Σ |a(n)| n^{−1/2+δ} < ∞`, `Σ |f(n)| n^{−1/2+δ} < ∞` for some `δ > 0`,
`f(1) = 0`, and let `v` be regular with continuation `E`. Put `A(s) = Σ a(n) n^{−s}`,
`F(s) = Σ f(n) n^{−s}` and suppose `lam = Λ ⋆ a + μ ⋆ f + v` is full-cone Weil-positive, with Herglotz
continuation `Φ`.

* **Master identity** (`zeta_mul_eq`).  On `Re s > ½`, `s ≠ 1`:
  `ζ (Φ − G − 1/(s − 1) + E) = A ζ′ − F`, and `A(1) = 1` (`dilSeries_one_eq_one`).
* **Boundary inequality** (`re_boundary_ge`).  For every real `t`, at `s = ½ + it`,
  `Re E(s) |ζ(s)|² + Re(F(s) ζ̄(s)) ≤ Re((A(s) − 1) ζ′(s) ζ̄(s))`.

  On `Re s > ½` the function `H = Φζ = (G + 1/(s−1) − E)ζ + Aζ′ − F` satisfies
  `Re(H ζ̄) = |ζ|² Re Φ ≥ 0`. Both factors are continuous up to the critical line, so the inequality
  holds there too. On the line the functional equation gives
  `Re[(G + 1/(s−1)) |ζ|² + ζ′ ζ̄] = 0` (`re_datum_normSq_add_deriv_mul_conj`), which removes the
  archimedean part. No residue at a zero of `ζ` enters: the weight `|ζ|²` vanishes there.
* **Decomposition** (`re_deriv_mul_conj_line`, `hasDerivAt_normSq_zeta_line`).  On the line
  `Re(ζ′ζ̄) = −θ′(t)|ζ|²` with `θ′ = gammaHardyPhaseRate`, and `d/dt |ζ(½+it)|² = −2 Im(ζ′ζ̄)`.
-/

noncomputable section

open Complex Filter Topology Set
open scoped ComplexConjugate
open RHTower.WeilSpectral RHTower.WeilHerglotz RHTower.WeilFiniteType
open RHTower.WeilInfiniteDilation

namespace RHTower.WeilZetaSquare

variable {a f v : ℕ → ℝ} {E : ℂ → ℂ} {δ : ℝ}

/-! ## The Dirichlet series of the system -/

/-- On `Re s > 1`: `Σ lam(n) n^{−s} = −A ζ′/ζ + F/ζ + E`. -/
theorem LSeries_finiteTypeSeq (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ))
    (hf : LSeriesSummable (fun n => (f n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hv : RegularPart v E)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (finiteTypeSeq a f v n : ℂ)) s =
      -(dilSeries a s * deriv riemannZeta s / riemannZeta s) + dilSeries f s / riemannZeta s +
        E s := by
  have hΛ := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hμ := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have hA : LSeriesSummable (fun n => (a n : ℂ)) s := summable_of_le_re ha (by linarith)
  have hF : LSeriesSummable (fun n => (f n : ℂ)) s := summable_of_le_re hf (by linarith)
  rw [finiteTypeSeq_cast, LSeries_add ((hΛ.convolution hA).add (hμ.convolution hF))
    (hv.summable s hs), LSeries_add (hΛ.convolution hA) (hμ.convolution hF),
    LSeries_convolution' hΛ hA, LSeries_convolution' hμ hF,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, ← hv.series s hs]
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hμζ : LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s = 1 / riemannZeta s := by
    have h := LSeries_one_mul_Lseries_moebius hs
    rw [LSeries_one_eq_riemannZeta hs] at h
    field_simp
    linear_combination h
  rw [hμζ]
  field_simp

/-! ## The master identity -/

/-- The right side of the master identity. -/
def masterRight (a f : ℕ → ℝ) (s : ℂ) : ℂ :=
  dilSeries a s * ((s - 1) * deriv zetaResidueUnit s - zetaResidueUnit s) -
    (s - 1) ^ 2 * dilSeries f s

theorem analyticOnNhd_masterRight
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ))
    (hf : LSeriesSummable (fun n => (f n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) :
    AnalyticOnNhd ℂ (masterRight a f) {s : ℂ | 1 / 2 - δ < s.re} := by
  have hU : IsOpen {s : ℂ | 1 / 2 - δ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hA := (differentiableOn_dilSeries ha).analyticOnNhd hU
  have hF := (differentiableOn_dilSeries hf).analyticOnNhd hU
  have hZ : AnalyticOnNhd ℂ zetaResidueUnit univ := fun s _ => analyticAt_zetaResidueUnit s
  have hZ' := hZ.deriv
  intro s hs
  have h1 : AnalyticAt ℂ (fun z : ℂ => z - 1) s := analyticAt_id.sub analyticAt_const
  exact ((hA s hs).mul ((h1.mul (hZ' s trivial)).sub (hZ s trivial))).sub
    ((h1.pow 2).mul (hF s hs))

/-- **The master identity** on `Re s > ½`. -/
theorem master_identity (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ))
    (hf : LSeriesSummable (fun n => (f n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hf1 : f 1 = 0)
    (hv : RegularPart v E) (hW : WeilPositiveFull (finiteTypeSeq a f v)) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    masterLeft hW E s = masterRight a f s := by
  obtain ⟨η₀, hη₀, hEd⟩ := hv.holo
  have hE : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re} :=
    hEd.mono fun z hz => by simp only [mem_setOf_eq] at hz ⊢; linarith
  have hpre : IsPreconnected {s : ℂ | 1 / 2 < s.re} :=
    (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have h2U : (2 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by show (1 / 2 : ℝ) < (2 : ℂ).re; norm_num
  refine (analyticOnNhd_masterLeft hW hE).eqOn_of_preconnected_of_eventuallyEq
    (fun z hz => analyticOnNhd_masterRight ha hf z
      (by simp only [mem_setOf_eq] at hz ⊢; linarith)) hpre h2U ?_ hs
  have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [hV] with z hz
  have hz : 1 < z.re := hz
  have hz1 : z ≠ 1 := by intro h; rw [h] at hz; simp at hz
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hζ : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hz
  unfold masterLeft masterRight
  rw [weilContinuation_eq hW hz, weilFunction, lamC_finiteTypeSeq a hf1 hv.zero hv.one,
    LSeries_finiteTypeSeq hδ ha hf hv hz, ← sq_mul_deriv_riemannZeta hz1,
    (zetaResidueUnit_eventuallyEq hz1).eq_of_nhds]
  unfold zetaArchimedeanDatum
  field_simp
  ring

/-- **Off `s = 1`**: `ζ (Φ − G − 1/(s − 1) + E) = A ζ′ − F`. -/
theorem zeta_mul_eq (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ))
    (hf : LSeriesSummable (fun n => (f n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hf1 : f 1 = 0)
    (hv : RegularPart v E) (hW : WeilPositiveFull (finiteTypeSeq a f v)) {s : ℂ}
    (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s * (weilContinuation hW s - zetaArchimedeanDatum s - 1 / (s - 1) + E s) =
      dilSeries a s * deriv riemannZeta s - dilSeries f s := by
  have h := master_identity hδ ha hf hf1 hv hW hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  unfold masterLeft masterRight at h
  rw [← sq_mul_deriv_riemannZeta hs1, (zetaResidueUnit_eventuallyEq hs1).eq_of_nhds] at h
  have h2 : (s - 1) ^ 2 * (riemannZeta s *
      (weilContinuation hW s - zetaArchimedeanDatum s - 1 / (s - 1) + E s)) =
      (s - 1) ^ 2 * (dilSeries a s * deriv riemannZeta s - dilSeries f s) := by
    have e : (s - 1) ^ 2 * (riemannZeta s *
        (weilContinuation hW s - zetaArchimedeanDatum s - 1 / (s - 1) + E s)) =
        (s - 1) * riemannZeta s *
          ((s - 1) * (weilContinuation hW s - zetaArchimedeanDatum s + E s) - 1) := by
      field_simp; ring
    rw [e, h]; ring
  exact mul_left_cancel₀ (pow_ne_zero 2 hs1') h2

/-- **Normalization at `s = 1`**: `A(1) = Σ a(n)/n = 1`. -/
theorem dilSeries_one_eq_one (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ))
    (hf : LSeriesSummable (fun n => (f n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hf1 : f 1 = 0)
    (hv : RegularPart v E) (hW : WeilPositiveFull (finiteTypeSeq a f v)) :
    dilSeries a 1 = 1 := by
  have h := master_identity hδ ha hf hf1 hv hW (s := 1) (by norm_num)
  unfold masterLeft masterRight at h
  simp only [sub_self, zero_mul, zetaResidueUnit_one, zero_sub, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_neg, mul_one] at h
  linear_combination h

/-! ## The boundary numerator -/

/-- `H(s) = (G(s) + 1/(s − 1) − E(s)) ζ(s) + A(s) ζ′(s) − F(s)`, equal to `Φ ζ` on `Re s > ½`. -/
def boundaryNumerator (a f : ℕ → ℝ) (E : ℂ → ℂ) (s : ℂ) : ℂ :=
  (zetaArchimedeanDatum s + 1 / (s - 1) - E s) * riemannZeta s +
    dilSeries a s * deriv riemannZeta s - dilSeries f s

theorem weilContinuation_mul_zeta (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ))
    (hf : LSeriesSummable (fun n => (f n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hf1 : f 1 = 0)
    (hv : RegularPart v E) (hW : WeilPositiveFull (finiteTypeSeq a f v)) {s : ℂ}
    (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    weilContinuation hW s * riemannZeta s = boundaryNumerator a f E s := by
  have h := zeta_mul_eq hδ ha hf hf1 hv hW hs hs1
  unfold boundaryNumerator
  linear_combination h

/-- `Re(H ζ̄) = |ζ|² Re Φ ≥ 0` on `Re s > ½`. -/
theorem re_boundaryNumerator_mul_conj_nonneg (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ))
    (hf : LSeriesSummable (fun n => (f n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hf1 : f 1 = 0)
    (hv : RegularPart v E) (hW : WeilPositiveFull (finiteTypeSeq a f v)) {s : ℂ}
    (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    0 ≤ (boundaryNumerator a f E s * conj (riemannZeta s)).re := by
  rw [← weilContinuation_mul_zeta hδ ha hf hf1 hv hW hs hs1, mul_assoc, Complex.mul_conj,
    Complex.re_mul_ofReal]
  exact mul_nonneg (re_weilContinuation_nonneg hW hs) (Complex.normSq_nonneg _)

theorem continuousAt_boundaryNumerator
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ))
    (hf : LSeriesSummable (fun n => (f n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hδ : 0 < δ)
    (hv : RegularPart v E) (t : ℝ) :
    ContinuousAt (boundaryNumerator a f E) (linePt t) := by
  obtain ⟨η₀, hη₀, hEd⟩ := hv.holo
  have hre : (linePt t).re = 1 / 2 := by simp [linePt]
  have hs1 : linePt t ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hre] at this; norm_num at this
  have hU : ∀ c : ℝ, c < 1 / 2 → {s : ℂ | c < s.re} ∈ 𝓝 (linePt t) := fun c hc =>
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by show c < (linePt t).re; rw [hre]; exact hc)
  have hG : ContinuousAt zetaArchimedeanDatum (linePt t) :=
    (differentiableAt_zetaArchimedeanDatum (by rw [hre]; norm_num)).continuousAt
  have hinv : ContinuousAt (fun s : ℂ => 1 / (s - 1)) (linePt t) :=
    continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hs1)
  have hEc : ContinuousAt E (linePt t) :=
    (hEd.differentiableAt (hU _ (by linarith))).continuousAt
  have hζ : ContinuousAt riemannZeta (linePt t) := (differentiableAt_riemannZeta hs1).continuousAt
  have hζ' : ContinuousAt (deriv riemannZeta) (linePt t) := by
    have han : AnalyticAt ℂ riemannZeta (linePt t) := by
      have hopen : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
      exact (DifferentiableOn.analyticOnNhd (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
        hopen) _ hs1
    exact han.deriv.continuousAt
  have hA : ContinuousAt (dilSeries a) (linePt t) :=
    ((differentiableOn_dilSeries ha).differentiableAt (hU _ (by linarith))).continuousAt
  have hF : ContinuousAt (dilSeries f) (linePt t) :=
    ((differentiableOn_dilSeries hf).differentiableAt (hU _ (by linarith))).continuousAt
  unfold boundaryNumerator
  exact ((((hG.add hinv).sub hEc).mul hζ).add (hA.mul hζ')).sub hF

/-- **The boundary inequality before simplification**: `Re(H ζ̄) ≥ 0` on the critical line. -/
theorem re_boundaryNumerator_mul_conj_line_nonneg (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ))
    (hf : LSeriesSummable (fun n => (f n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hf1 : f 1 = 0)
    (hv : RegularPart v E) (hW : WeilPositiveFull (finiteTypeSeq a f v)) (t : ℝ) :
    0 ≤ (boundaryNumerator a f E (linePt t) * conj (riemannZeta (linePt t))).re := by
  have hre : (linePt t).re = 1 / 2 := by simp [linePt]
  have hs1 : linePt t ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hre] at this; norm_num at this
  set path : ℝ → ℂ := fun σ => (σ : ℂ) + (t : ℂ) * I with hpath
  have hpath0 : path (1 / 2) = linePt t := by simp [hpath, linePt]
  have hpc : Continuous path := by fun_prop
  have hlim : Tendsto path (𝓝[>] (1 / 2)) (𝓝 (linePt t)) := by
    rw [← hpath0]; exact hpc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hfun : ContinuousAt (fun s => (boundaryNumerator a f E s * conj (riemannZeta s)).re)
      (linePt t) :=
    Complex.continuous_re.continuousAt.comp
      ((continuousAt_boundaryNumerator ha hf hδ hv t).mul
        (Complex.continuous_conj.continuousAt.comp
          (differentiableAt_riemannZeta hs1).continuousAt))
  refine ge_of_tendsto (hfun.tendsto.comp hlim) ?_
  have hev : ∀ᶠ σ in 𝓝[>] (1 / 2 : ℝ), σ < 1 := by
    exact nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num))
  filter_upwards [self_mem_nhdsWithin, hev] with σ hσ hσ1
  have hσ' : (1 / 2 : ℝ) < σ := hσ
  have hre' : (path σ).re = σ := by simp [hpath]
  have hne : path σ ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hre'] at this; simp at this; linarith
  exact re_boundaryNumerator_mul_conj_nonneg hδ ha hf hf1 hv hW (by rw [hre']; exact hσ') hne

/-! ## The functional equation on the critical line -/

theorem linePt_eq_half_add_I_mul (t : ℝ) : linePt t = (1 / 2 : ℂ) + I * (t : ℂ) := by
  simp [linePt]; ring

/-- `Re(G(s) + 1/(s − 1)) = θ′(t)` at `s = ½ + it`. -/
theorem re_datum_add_inv_line (t : ℝ) :
    (zetaArchimedeanDatum (linePt t) + 1 / (linePt t - 1)).re = gammaHardyPhaseRate t := by
  unfold zetaArchimedeanDatum gammaHardyPhaseRate
  have h1 : (1 / linePt t + 1 / (linePt t - 1)).re = 0 := by
    have hs : linePt t = (1 / 2 : ℂ) + (t : ℂ) * I := by simp [linePt]
    have hden1 : ((1 / 2 : ℂ) + (t : ℂ) * I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    have hden2 : ((1 / 2 : ℂ) + (t : ℂ) * I - 1) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; norm_num at this
    rw [hs, div_add_div _ _ hden1 hden2]
    have hnum : (1 * ((1 / 2 : ℂ) + (t : ℂ) * I - 1) + (1 / 2 + (t : ℂ) * I) * 1) =
        ((2 * t : ℝ) : ℂ) * I := by push_cast; ring
    have hden : ((1 / 2 : ℂ) + (t : ℂ) * I) * ((1 / 2 : ℂ) + (t : ℂ) * I - 1) =
        ((-(1 / 4) - t ^ 2 : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [I_sq]; ring
    rw [hnum, hden, show ((2 * t : ℝ) : ℂ) * I / ((-(1 / 4) - t ^ 2 : ℝ) : ℂ) =
      (((2 * t) / (-(1 / 4) - t ^ 2) : ℝ) : ℂ) * I by push_cast; ring]
    rw [Complex.mul_I_re, Complex.ofReal_im, neg_zero]
  have h2 : ((Complex.digamma (linePt t / 2) / 2 - (Real.log Real.pi : ℂ) / 2 + 1 / linePt t) +
      1 / (linePt t - 1)).re =
      (Complex.digamma (linePt t / 2)).re / 2 - Real.log Real.pi / 2 +
        (1 / linePt t + 1 / (linePt t - 1)).re := by
    simp only [Complex.add_re, Complex.sub_re, Complex.div_re]
    norm_num
    ring
  rw [h2, h1, add_zero]

/-- **The functional equation on the line**: `Re[(G + 1/(s−1))|ζ|² + ζ′ζ̄] = 0`. -/
theorem re_datum_normSq_add_deriv_mul_conj (t : ℝ) :
    ((zetaArchimedeanDatum (linePt t) + 1 / (linePt t - 1)) *
        (riemannZeta (linePt t) * conj (riemannZeta (linePt t))) +
      deriv riemannZeta (linePt t) * conj (riemannZeta (linePt t))).re = 0 := by
  set s := linePt t with hsdef
  by_cases hζ : riemannZeta s = 0
  · simp [hζ]
  have hre : s.re = 1 / 2 := by simp [hsdef, linePt]
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hre] at this; norm_num at this
  have hlog := logDeriv_xi_eq_datum_add (s := s) (by rw [hre]; norm_num) hs1 hζ
  have hre0 : (logDeriv xi s).re = 0 := by
    rw [logDeriv_apply, hsdef, linePt_eq_half_add_I_mul]
    exact re_logDeriv_xi_criticalLine t
  have hkey : (zetaArchimedeanDatum s + 1 / (s - 1)) * (riemannZeta s * conj (riemannZeta s)) +
      deriv riemannZeta s * conj (riemannZeta s) =
      logDeriv xi s * ((Complex.normSq (riemannZeta s) : ℝ) : ℂ) := by
    rw [hlog, ← Complex.mul_conj]
    field_simp
  rw [hkey, Complex.re_mul_ofReal, hre0, zero_mul]

/-- `Re(ζ′ζ̄) = −θ′(t) |ζ|²` on the critical line. -/
theorem re_deriv_mul_conj_line (t : ℝ) :
    (deriv riemannZeta (linePt t) * conj (riemannZeta (linePt t))).re =
      -(gammaHardyPhaseRate t * Complex.normSq (riemannZeta (linePt t))) := by
  have h := re_datum_normSq_add_deriv_mul_conj t
  rw [Complex.add_re, Complex.mul_conj, Complex.re_mul_ofReal, re_datum_add_inv_line] at h
  linarith

/-- **The boundary inequality**: at `s = ½ + it`,
`Re E(s) |ζ(s)|² + Re(F(s) ζ̄(s)) ≤ Re((A(s) − 1) ζ′(s) ζ̄(s))`. -/
theorem re_boundary_ge (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ))
    (hf : LSeriesSummable (fun n => (f n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hf1 : f 1 = 0)
    (hv : RegularPart v E) (hW : WeilPositiveFull (finiteTypeSeq a f v)) (t : ℝ) :
    (E (linePt t)).re * Complex.normSq (riemannZeta (linePt t)) +
        (dilSeries f (linePt t) * conj (riemannZeta (linePt t))).re ≤
      ((dilSeries a (linePt t) - 1) * deriv riemannZeta (linePt t) *
        conj (riemannZeta (linePt t))).re := by
  have h := re_boundaryNumerator_mul_conj_line_nonneg hδ ha hf hf1 hv hW t
  have hfe := re_datum_normSq_add_deriv_mul_conj t
  set s := linePt t
  have hsplit : boundaryNumerator a f E s * conj (riemannZeta s) =
      ((zetaArchimedeanDatum s + 1 / (s - 1)) * (riemannZeta s * conj (riemannZeta s)) +
        deriv riemannZeta s * conj (riemannZeta s)) +
      (dilSeries a s - 1) * deriv riemannZeta s * conj (riemannZeta s) -
      E s * ((Complex.normSq (riemannZeta s) : ℝ) : ℂ) -
      dilSeries f s * conj (riemannZeta s) := by
    unfold boundaryNumerator
    rw [← Complex.mul_conj]
    ring
  rw [hsplit, Complex.sub_re, Complex.sub_re, Complex.add_re, hfe, Complex.re_mul_ofReal] at h
  linarith

/-! ## The height derivative of `|ζ(½+it)|²` -/

theorem hasDerivAt_zeta_line (t : ℝ) :
    HasDerivAt (fun τ : ℝ => riemannZeta (linePt τ)) (deriv riemannZeta (linePt t) * I) t := by
  have hre : (linePt t).re = 1 / 2 := by simp [linePt]
  have hs1 : linePt t ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hre] at this; norm_num at this
  have hl : HasDerivAt (fun τ : ℝ => linePt τ) I t := by
    have h0 : HasDerivAt (fun τ : ℝ => (τ : ℂ) * I) (1 * I) t :=
      (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I
    have h1 := h0.const_add (1 / 2 : ℂ)
    simpa [linePt] using h1
  exact (differentiableAt_riemannZeta hs1).hasDerivAt.comp t hl

/-- `d/dt |ζ(½+it)|² = −2 Im(ζ′ζ̄)`. -/
theorem hasDerivAt_normSq_zeta_line (t : ℝ) :
    HasDerivAt (fun τ : ℝ => Complex.normSq (riemannZeta (linePt τ)))
      (-(2 * (deriv riemannZeta (linePt t) * conj (riemannZeta (linePt t))).im)) t := by
  have h := (hasDerivAt_zeta_line t).norm_sq
  have hfun : (fun τ : ℝ => ‖riemannZeta (linePt τ)‖ ^ 2) =
      fun τ : ℝ => Complex.normSq (riemannZeta (linePt τ)) := by
    funext τ; rw [Complex.normSq_eq_norm_sq]
  rw [hfun] at h
  convert h using 1
  rw [Complex.inner]
  have e : deriv riemannZeta (linePt t) * I * conj (riemannZeta (linePt t)) =
      I * (deriv riemannZeta (linePt t) * conj (riemannZeta (linePt t))) := by ring
  rw [e, Complex.mul_re, Complex.I_re, Complex.I_im]
  ring

end RHTower.WeilZetaSquare
