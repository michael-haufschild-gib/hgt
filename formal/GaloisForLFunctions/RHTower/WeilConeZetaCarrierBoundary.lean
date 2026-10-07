import GaloisForLFunctions.RHTower.WeilConeVonMangoldtZetaPencil
import GaloisForLFunctions.RHTower.WeilPositivityResidueRigidity
import GaloisForLFunctions.RHTower.WeilFullConeCCMBridge

/-!
# ζ-multiplicative pole carriers: the boundary cases

Let `m, v : ℕ → ℝ` with `Σ |m(n)| n^{−½} < ∞`, `Σ |v(n)| n^{−½} < ∞` and `v(0) = v(1) = 0`, and
let `β ∈ ℝ`. The system

`λ(n) = β Λ(n) + (1 ⋆ m)(n) + v(n)`  (`n ≥ 2`, `λ(0) = λ(1) = 0`)

has Dirichlet series `−β ζ′/ζ + ζ M − m(1) + V`, with `M = Σ m(n) n^{−s}`. It carries the pole
of the Weil function at `s = 1` partly in the logarithmic derivative `ζ′/ζ` and partly in `ζ`
itself, with share `μ = M(1)`.

**Theorems.** If `λ` is full-cone Weil-positive, then
* `β + M(1) = 1` (`beta_add_mu`);
* `M(1) ≥ 0` (`mu_nonneg`);
* if `M(1) = 0`, then `λ = Λ` on `n ≥ 2` (`eq_vonMangoldt_of_mu_eq_zero`).

**Proof.**
* The master identity `Z₁((s−1)(Φ − G + V − m(1)) − 1) = β((s−1)Z₁′ − Z₁) − Z₁² M` on `Re s > ½`,
  `Z₁ = (s − 1)ζ`, evaluated at `s = 1`, gives `β + M(1) = 1`.
* `Φ ζ = H := (G + 1/(s−1) − ζM + m(1) − V)ζ + βζ′` is continuous up to the line, and the
  functional equation turns `Re(H ζ̄) ≥ 0` into `|ζ|²(M(1)θ′ − Re(ζM) + m(1) − Re V) ≥ 0`.
* `M(1) < 0`: near a zero of `ζ` on the line at large height (Hardy) `ζM → 0`, while
  `M(1)θ′ → −∞`.
* `M(1) = 0`: then `β = 1`, `λ = Λ + w` with `w = (1 ⋆ m) + v`, and
  `Σ_{k ≤ n} (1 ⋆ m)(k) = −Σ_{j ≤ n} m(j){n/j} − n Σ_{j > n} m(j)/j`. Its weighted sizes
  `|·|/(n√n)` are summable, which by Fubini against `Σ_{n < j} n^{−½} ≤ 2√j` and
  `Σ_{n ≥ j} n^{−3/2} ≤ 3/√j` needs only `Σ |m(j)| j^{−½} < ∞`. The two-pole rigidity of
  regular perturbations of `Λ` (`vonMangoldt_add_twoPole_eq_zero`) gives `w = 0`.
-/

noncomputable section

open Complex Filter Topology Set
open scoped ComplexConjugate
open RHTower.WeilSpectral RHTower.WeilHerglotz RHTower.WeilFiniteType RHTower.WeilInfiniteDilation
open RHTower.WeilZetaSquare

namespace RHTower.WeilZetaCarrier

open RHTower.WeilBoundaryDilation (BoundaryRegular regSeries)

/-- `(1 ⋆ m)(n)` for `n ≥ 2`, and `0` at `n = 0, 1`. -/
def carrier (m : ℕ → ℝ) (n : ℕ) : ℝ := if 2 ≤ n then ∑ k ∈ n.divisors, m k else 0

/-- `λ(n) = β Λ(n) + (1 ⋆ m)(n) + v(n)`. -/
def carrierSystem (β : ℝ) (m v : ℕ → ℝ) (n : ℕ) : ℝ :=
  β * ArithmeticFunction.vonMangoldt n + carrier m n + v n

/-- `M(s) = Σ m(n) n^{−s}`. -/
abbrev mSeries (m : ℕ → ℝ) : ℂ → ℂ := LSeries (fun n => (m n : ℂ))

variable {β : ℝ} {m v : ℕ → ℝ}

/-! ## The Dirichlet series -/

theorem convolution_one_apply (m : ℕ → ℝ) (n : ℕ) :
    LSeries.convolution 1 (fun n => (m n : ℂ)) n = ∑ k ∈ n.divisors, (m k : ℂ) := by
  simp only [LSeries.convolution_def, Pi.one_apply, one_mul]
  rw [Nat.sum_divisorsAntidiagonal (fun _ y => (m y : ℂ))]
  exact Nat.sum_div_divisors n (fun k => (m k : ℂ))

theorem carrier_eq (m : ℕ → ℝ) (n : ℕ) :
    ((carrier m n : ℝ) : ℂ) = LSeries.convolution 1 (fun n => (m n : ℂ)) n -
      (if n = 1 then (m 1 : ℂ) else 0) := by
  rw [convolution_one_apply]
  unfold carrier
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · rw [if_pos h, if_neg (by omega)]
    push_cast
    ring

theorem summable_of_half {f : ℕ → ℂ} (hf : LSeriesSummable f (1 / 2)) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) : LSeriesSummable f s :=
  hf.of_re_le_re (by simpa using hs)

theorem LSeries_carrier (hm : LSeriesSummable (fun n => (m n : ℂ)) (1 / 2)) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (fun n => ((carrier m n : ℝ) : ℂ)) s = riemannZeta s * mSeries m s - m 1 := by
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have hM : LSeriesSummable (fun n => (m n : ℂ)) s := summable_of_half hm (by linarith)
  have hconv := LSeries_convolution' h1 hM
  have hcs : LSeriesSummable (LSeries.convolution 1 (fun n => (m n : ℂ))) s :=
    LSeriesSummable.convolution h1 hM
  have hδ : Summable fun n : ℕ => LSeries.term (fun n => if n = 1 then (m 1 : ℂ) else 0) s n :=
    summable_of_ne_finset_zero (s := {1}) fun n hn => by
      have : n ≠ 1 := by simpa using hn
      simp [LSeries.term, this]
  have hpt : (fun n => ((carrier m n : ℝ) : ℂ)) =
      fun n => LSeries.convolution 1 (fun n => (m n : ℂ)) n -
        (if n = 1 then (m 1 : ℂ) else 0) := funext (carrier_eq m)
  rw [hpt]
  have hsub : LSeries (fun n => LSeries.convolution 1 (fun n => (m n : ℂ)) n -
      (if n = 1 then (m 1 : ℂ) else 0)) s =
      LSeries (LSeries.convolution 1 (fun n => (m n : ℂ))) s -
        LSeries (fun n => if n = 1 then (m 1 : ℂ) else 0) s := LSeries_sub hcs hδ
  rw [hsub, hconv, LSeries_one_eq_riemannZeta hs]
  congr 1
  rw [LSeries, tsum_eq_single 1 fun n hn => by simp [LSeries.term, hn]]
  simp [LSeries.term]

theorem LSeries_carrierSystem (hm : LSeriesSummable (fun n => (m n : ℂ)) (1 / 2))
    (hv : BoundaryRegular v) {s : ℂ} (hs : 1 < s.re) :
    LSeries (lamC (carrierSystem β m v)) s =
      -(β * deriv riemannZeta s / riemannZeta s) + (riemannZeta s * mSeries m s - m 1) +
        regSeries v s := by
  have hΛ := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hV : LSeriesSummable (fun n => (v n : ℂ)) s := summable_of_half hv.summable (by linarith)
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have hM : LSeriesSummable (fun n => (m n : ℂ)) s := summable_of_half hm (by linarith)
  have hC : LSeriesSummable (fun n => ((carrier m n : ℝ) : ℂ)) s := by
    have hcs : LSeriesSummable (LSeries.convolution 1 (fun n => (m n : ℂ))) s :=
      LSeriesSummable.convolution h1 hM
    have hδ : LSeriesSummable (fun n => if n = 1 then (m 1 : ℂ) else 0) s :=
      summable_of_ne_finset_zero (s := {1}) fun n hn => by
        have : n ≠ 1 := by simpa using hn
        simp [LSeries.term, this]
    rw [funext (carrier_eq m)]
    exact hcs.sub hδ
  have hpt : lamC (carrierSystem β m v) =
      ((β : ℂ) • fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) +
      (fun n => ((carrier m n : ℝ) : ℂ)) + fun n => (v n : ℂ) := by
    funext n
    simp only [lamC, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp [carrier, hv.zero, hv.one]
    · rw [if_pos h]
      simp only [carrierSystem]
      push_cast
      ring
  rw [hpt, LSeries_add ((hΛ.smul _).add hC) hV, LSeries_add (hΛ.smul _) hC, LSeries_smul,
    LSeries_carrier hm hs, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  ring

/-! ## The residue identity -/

theorem differentiableOn_mSeries (hm : LSeriesSummable (fun n => (m n : ℂ)) (1 / 2)) :
    DifferentiableOn ℂ (mSeries m) {s : ℂ | 1 / 2 < s.re} := by
  refine (LSeries_differentiableOn _).mono fun s hs => ?_
  have h1 := hm.abscissaOfAbsConv_le
  have hs' : (1 / 2 : ℝ) < s.re := hs
  show LSeries.abscissaOfAbsConv _ < (s.re : EReal)
  calc LSeries.abscissaOfAbsConv _ ≤ ((1 / 2 : ℂ).re : EReal) := h1
    _ < (s.re : EReal) := by norm_num; exact_mod_cast hs'

/-- **The master identity** on `Re s > ½`. -/
theorem masterLeft_carrier (hm : LSeriesSummable (fun n => (m n : ℂ)) (1 / 2))
    (hv : BoundaryRegular v) (hW : WeilPositiveFull (carrierSystem β m v)) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    masterLeft hW (fun s => regSeries v s - m 1) s =
      β * ((s - 1) * deriv zetaResidueUnit s - zetaResidueUnit s) -
        zetaResidueUnit s ^ 2 * mSeries m s := by
  have hpre : IsPreconnected {s : ℂ | 1 / 2 < s.re} :=
    (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have h2U : (2 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by show (1 / 2 : ℝ) < (2 : ℂ).re; norm_num
  have hU : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hZ : AnalyticOnNhd ℂ zetaResidueUnit univ := fun s _ => analyticAt_zetaResidueUnit s
  have hMa : AnalyticOnNhd ℂ (mSeries m) {s : ℂ | 1 / 2 < s.re} :=
    (differentiableOn_mSeries hm).analyticOnNhd hU
  have hR : AnalyticOnNhd ℂ (fun s => β * ((s - 1) * deriv zetaResidueUnit s -
      zetaResidueUnit s) - zetaResidueUnit s ^ 2 * mSeries m s) {s : ℂ | 1 / 2 < s.re} := by
    intro s hs
    have h1 : AnalyticAt ℂ (fun z : ℂ => z - 1) s := analyticAt_id.sub analyticAt_const
    exact (analyticAt_const.mul ((h1.mul (hZ.deriv s trivial)).sub (hZ s trivial))).sub
      (((hZ s trivial).pow 2).mul (hMa s hs))
  have hE : DifferentiableOn ℂ (fun s => regSeries v s - m 1) {s : ℂ | 1 / 2 < s.re} :=
    (WeilBoundaryDilation.differentiableOn_regSeries hv).sub_const _
  refine (analyticOnNhd_masterLeft hW hE).eqOn_of_preconnected_of_eventuallyEq
    hR hpre h2U ?_ hs
  have hV1 : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [hV1] with z hz
  have hz : 1 < z.re := hz
  have hz1 : z ≠ 1 := by intro h; rw [h] at hz; simp at hz
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hζ : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hz
  unfold masterLeft
  rw [weilContinuation_eq hW hz, weilFunction, LSeries_carrierSystem hm hv hz,
    ← sq_mul_deriv_riemannZeta hz1, (zetaResidueUnit_eventuallyEq hz1).eq_of_nhds]
  unfold zetaArchimedeanDatum
  field_simp
  ring

/-- The share `μ = M(1)` of the pole carried by `ζ`. -/
abbrev mu (m : ℕ → ℝ) : ℝ := (mSeries m 1).re

theorem beta_add_mu (hm : LSeriesSummable (fun n => (m n : ℂ)) (1 / 2)) (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (carrierSystem β m v)) : β + mu m = 1 := by
  have h := masterLeft_carrier hm hv hW (s := 1) (by norm_num)
  unfold masterLeft at h
  simp only [sub_self, zero_mul, zetaResidueUnit_one, zero_sub, mul_neg, mul_one, one_pow,
    one_mul] at h
  have := congrArg Complex.re h
  simp at this
  linarith

/-! ## The boundary inequality -/

/-- The boundary numerator `H = (G + 1/(s−1) − ζM + m(1) − V) ζ + β ζ′`. -/
def carrierNumerator (β : ℝ) (m v : ℕ → ℝ) (s : ℂ) : ℂ :=
  (zetaArchimedeanDatum s + 1 / (s - 1) - riemannZeta s * mSeries m s + m 1 - regSeries v s) *
    riemannZeta s + β * deriv riemannZeta s

theorem weilContinuation_mul_zeta_carrier (hm : LSeriesSummable (fun n => (m n : ℂ)) (1 / 2))
    (hv : BoundaryRegular v) (hW : WeilPositiveFull (carrierSystem β m v)) {s : ℂ}
    (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    weilContinuation hW s * riemannZeta s = carrierNumerator β m v s := by
  have h := masterLeft_carrier hm hv hW hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  unfold masterLeft at h
  rw [← sq_mul_deriv_riemannZeta hs1, (zetaResidueUnit_eventuallyEq hs1).eq_of_nhds] at h
  unfold carrierNumerator
  apply mul_left_cancel₀ (pow_ne_zero 2 hs1')
  have e : (s - 1) ^ 2 * (weilContinuation hW s * riemannZeta s) =
      (s - 1) * riemannZeta s * ((s - 1) * (weilContinuation hW s - zetaArchimedeanDatum s +
        (regSeries v s - m 1)) - 1) + (s - 1) ^ 2 * riemannZeta s *
          (zetaArchimedeanDatum s - (regSeries v s - m 1)) + (s - 1) * riemannZeta s := by ring
  rw [e, h]
  field_simp
  ring

theorem re_carrierNumerator_mul_conj_nonneg (hm : LSeriesSummable (fun n => (m n : ℂ)) (1 / 2))
    (hv : BoundaryRegular v) (hW : WeilPositiveFull (carrierSystem β m v)) {s : ℂ}
    (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    0 ≤ (carrierNumerator β m v s * conj (riemannZeta s)).re := by
  rw [← weilContinuation_mul_zeta_carrier hm hv hW hs hs1, mul_assoc, Complex.mul_conj,
    Complex.re_mul_ofReal]
  exact mul_nonneg (re_weilContinuation_nonneg hW hs) (Complex.normSq_nonneg _)

theorem continuousWithinAt_carrierNumerator (hm : LSeriesSummable (fun n => (m n : ℂ)) (1 / 2))
    (hv : BoundaryRegular v) (t : ℝ) :
    ContinuousWithinAt (fun s => (carrierNumerator β m v s * conj (riemannZeta s)).re)
      {s : ℂ | 1 / 2 ≤ s.re} (linePt t) := by
  have hre := linePt_re t
  have hs1 : linePt t ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hre] at this; norm_num at this
  have hmem : linePt t ∈ {s : ℂ | 1 / 2 ≤ s.re} := by
    show (1 / 2 : ℝ) ≤ (linePt t).re; rw [hre]
  have hG : ContinuousAt zetaArchimedeanDatum (linePt t) :=
    (differentiableAt_zetaArchimedeanDatum (by rw [hre]; norm_num)).continuousAt
  have hinv : ContinuousAt (fun s : ℂ => 1 / (s - 1)) (linePt t) :=
    continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hs1)
  have hZan : AnalyticAt ℂ riemannZeta (linePt t) := analyticOn_riemannZeta (linePt t) hs1
  have hZ := hZan.continuousAt
  have hZ' := hZan.deriv.continuousAt
  have hV := WeilBoundaryDilation.continuousOn_regSeries hv (linePt t) hmem
  have hM := WeilBoundaryDilation.continuousOn_LSeries_half hm (linePt t) hmem
  have hH : ContinuousWithinAt (carrierNumerator β m v) {s : ℂ | 1 / 2 ≤ s.re} (linePt t) := by
    unfold carrierNumerator
    have hA : ContinuousWithinAt (fun s => zetaArchimedeanDatum s + 1 / (s - 1) -
        riemannZeta s * mSeries m s + m 1) {s : ℂ | 1 / 2 ≤ s.re} (linePt t) :=
      (((hG.add hinv).continuousWithinAt).sub (hZ.continuousWithinAt.mul hM)).add
        continuousWithinAt_const
    exact ((hA.sub hV).mul hZ.continuousWithinAt).add
      (continuousAt_const.mul hZ').continuousWithinAt
  exact Complex.continuous_re.continuousAt.comp_continuousWithinAt
    (hH.mul (Complex.continuous_conj.continuousAt.comp_continuousWithinAt hZ.continuousWithinAt))

theorem re_carrierNumerator_line_nonneg (hm : LSeriesSummable (fun n => (m n : ℂ)) (1 / 2))
    (hv : BoundaryRegular v) (hW : WeilPositiveFull (carrierSystem β m v)) (t : ℝ) :
    0 ≤ (carrierNumerator β m v (linePt t) * conj (riemannZeta (linePt t))).re := by
  obtain ⟨path, hpath⟩ : ∃ path : ℝ → ℂ, path = fun σ : ℝ => (σ : ℂ) + (t : ℂ) * I := ⟨_, rfl⟩
  have hpre : ∀ σ, (path σ).re = σ := fun σ => by simp [hpath]
  have hpath0 : path (1 / 2) = linePt t := by simp [hpath, linePt]
  have hpc : Continuous path := by rw [hpath]; fun_prop
  have hlim : Tendsto path (𝓝[>] (1 / 2)) (𝓝[{s : ℂ | 1 / 2 ≤ s.re}] (linePt t)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · rw [← hpath0]; exact hpc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      show (1 / 2 : ℝ) ≤ (path σ).re
      rw [hpre]; exact le_of_lt hσ
  refine ge_of_tendsto ((continuousWithinAt_carrierNumerator hm hv t).tendsto.comp hlim) ?_
  have hev : ∀ᶠ σ in 𝓝[>] (1 / 2 : ℝ), σ < 1 :=
    nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num))
  filter_upwards [self_mem_nhdsWithin, hev] with σ hσ hσ1
  have hσ' : (1 / 2 : ℝ) < σ := hσ
  have hne : path σ ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hpre] at this; simp at this; linarith
  exact re_carrierNumerator_mul_conj_nonneg hm hv hW (by rw [hpre]; exact hσ') hne

/-- **The line inequality**: `|ζ|² (M(1) θ′ − Re(ζM) + m(1) − Re V) ≥ 0` at every height. -/
theorem line_ineq_carrier (hm : LSeriesSummable (fun n => (m n : ℂ)) (1 / 2))
    (hv : BoundaryRegular v) (hW : WeilPositiveFull (carrierSystem β m v)) (t : ℝ) :
    0 ≤ Complex.normSq (riemannZeta (linePt t)) * (mu m * gammaHardyPhaseRate t -
      (riemannZeta (linePt t) * mSeries m (linePt t)).re + m 1 -
        (regSeries v (linePt t)).re) := by
  have h := re_carrierNumerator_line_nonneg hm hv hW t
  have hβ : β = 1 - mu m := by linarith [beta_add_mu hm hv hW]
  have hd := re_datum_add_inv_line t
  have hP := re_deriv_mul_conj_line t
  obtain ⟨z, hz⟩ : ∃ z, z = riemannZeta (linePt t) := ⟨_, rfl⟩
  rw [← hz] at h hP ⊢
  have e : carrierNumerator β m v (linePt t) * conj z =
      (zetaArchimedeanDatum (linePt t) + 1 / (linePt t - 1)) * ((Complex.normSq z : ℝ) : ℂ) -
        z * mSeries m (linePt t) * ((Complex.normSq z : ℝ) : ℂ) +
          (m 1 : ℂ) * ((Complex.normSq z : ℝ) : ℂ) -
            regSeries v (linePt t) * ((Complex.normSq z : ℝ) : ℂ) +
              β * (deriv riemannZeta (linePt t) * conj z) := by
    unfold carrierNumerator
    rw [← hz, ← Complex.mul_conj]
    ring
  rw [e, Complex.add_re, Complex.sub_re, Complex.add_re, Complex.sub_re, Complex.re_mul_ofReal,
    Complex.re_mul_ofReal, Complex.re_mul_ofReal, Complex.re_mul_ofReal, Complex.re_ofReal_mul,
    hd, hP, Complex.ofReal_re] at h
  have e3 : Complex.normSq z * (mu m * gammaHardyPhaseRate t -
      (z * mSeries m (linePt t)).re + m 1 - (regSeries v (linePt t)).re) =
      gammaHardyPhaseRate t * Complex.normSq z - (z * mSeries m (linePt t)).re * Complex.normSq z +
        m 1 * Complex.normSq z - (regSeries v (linePt t)).re * Complex.normSq z +
          β * -(gammaHardyPhaseRate t * Complex.normSq z) := by
    rw [hβ]; ring
  rw [e3]
  exact h

/-! ## `M(1) < 0` is impossible -/

theorem continuous_zeta_mul_mSeries_line (hm : LSeriesSummable (fun n => (m n : ℂ)) (1 / 2)) :
    Continuous fun t => riemannZeta (linePt t) * mSeries m (linePt t) := by
  refine continuous_zeta_line.mul ?_
  refine (WeilBoundaryDilation.continuousOn_LSeries_half hm).comp_continuous continuous_linePt
    fun t => ?_
  show (1 / 2 : ℝ) ≤ (linePt t).re
  rw [linePt_re]

/-- **`M(1) ≥ 0`.** If `M(1) < 0`, then `M(1) θ′ ≥ Re(ζM) − m(1) + Re V` off the zeros of `ζ`; at a
zero of `ζ` on the line at large height (Hardy) `ζM → 0` while `M(1) θ′ → −∞`. -/
theorem mu_nonneg (hm : LSeriesSummable (fun n => (m n : ℂ)) (1 / 2)) (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (carrierSystem β m v)) : 0 ≤ mu m := by
  by_contra hμ
  push Not at hμ
  obtain ⟨S, hS⟩ : ∃ S, S = ∑' n, ‖LSeries.term (fun n => (v n : ℂ)) (1 / 2) n‖ := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; exact tsum_nonneg fun _ => norm_nonneg _
  have hc : 0 < -mu m := by linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (1 + |m 1| + S) / (-mu m) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have key : ∀ t, riemannZeta (linePt t) ≠ 0 →
      (riemannZeta (linePt t) * mSeries m (linePt t)).re - |m 1| - S ≤
        mu m * gammaHardyPhaseRate t := by
    intro t hz
    have hN : 0 < Complex.normSq (riemannZeta (linePt t)) := Complex.normSq_pos.mpr hz
    have hb := (mul_nonneg_iff_of_pos_left hN).mp (line_ineq_carrier hm hv hW t)
    have hV := WeilPencil.abs_re_regSeries_line_le hv t
    rw [← hS] at hV
    linarith [(abs_le.mp hV).1, le_abs_self (m 1)]
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = 2 * Real.pi * Real.exp (2 * (4 + K)) := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE]; positivity
  obtain ⟨t₀, ht₀, hXi⟩ := exists_Xi_zero_gt (2 * E + 2)
  have hz0 : riemannZeta (linePt t₀) = 0 := by
    have hZ := (Xi_eq_zero_iff_hardyZ t₀).mp hXi
    have := WeilBoundaryDilation.norm_riemannZeta_linePt t₀
    rw [hZ, abs_zero] at this
    exact norm_eq_zero.mp this
  -- near `t₀`, `Re(ζM) ≤ −1`
  have hlarge : ∀ᶠ t in 𝓝[≠] t₀,
      (riemannZeta (linePt t) * mSeries m (linePt t)).re ≤ -1 := by
    have hnear : ∀ᶠ t in 𝓝[≠] t₀, t₀ - 1 < t :=
      nhdsWithin_le_nhds (eventually_gt_nhds (by linarith))
    filter_upwards [WeilPencil.eventually_zeta_linePt_ne_zero t₀, hnear] with t hz ht
    have ht1 : 1 ≤ t := by linarith
    have htE : E ≤ t / 1 := by rw [div_one]; linarith
    have hlog : 2 * (4 + K) ≤ Real.log (t / (2 * Real.pi)) := by
      rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
      rw [hE] at htE; linarith
    have h1 := key t hz
    have h2 := WeilPencil.log_div_sub_le_gammaHardyPhaseRate ht1
    have h3 : K ≤ gammaHardyPhaseRate t := by linarith
    have h4 : mu m * gammaHardyPhaseRate t ≤ mu m * K := mul_le_mul_of_nonpos_left h3 hμ.le
    have h5 : mu m * K = -(1 + |m 1| + S) := by
      rw [hK, mul_div_assoc', div_eq_iff (by linarith : -mu m ≠ 0)]; ring
    linarith
  -- but `ζM → 0`
  have hsmall : ∀ᶠ t in 𝓝[≠] t₀, -1 < (riemannZeta (linePt t) * mSeries m (linePt t)).re := by
    have hc : Tendsto (fun t => (riemannZeta (linePt t) * mSeries m (linePt t)).re) (𝓝 t₀)
        (𝓝 (riemannZeta (linePt t₀) * mSeries m (linePt t₀)).re) :=
      (Complex.continuous_re.comp (continuous_zeta_mul_mSeries_line hm)).tendsto t₀
    rw [hz0, zero_mul, Complex.zero_re] at hc
    exact nhdsWithin_le_nhds (hc.eventually (lt_mem_nhds (by norm_num)))
  obtain ⟨t, h1, h2⟩ := (hlarge.and hsmall).exists
  linarith

/-! ## Fubini bounds for partial sums -/

theorem inv_mul_sqrt_le_sub {n : ℕ} (hn : 1 ≤ n) :
    1 / ((n : ℝ) * Real.sqrt n) ≤
      2 / Real.sqrt ((n : ℝ) - 1 / 2) - 2 / Real.sqrt ((n : ℝ) + 1 / 2) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨a, ha⟩ : ∃ a, a = Real.sqrt ((n : ℝ) - 1 / 2) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = Real.sqrt ((n : ℝ) + 1 / 2) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = Real.sqrt n := ⟨_, rfl⟩
  have ha2 : a ^ 2 = n - 1 / 2 := by rw [ha, Real.sq_sqrt (by linarith)]
  have hb2 : b ^ 2 = n + 1 / 2 := by rw [hb, Real.sq_sqrt (by linarith)]
  have hc2 : c ^ 2 = n := by rw [hc, Real.sq_sqrt (by linarith)]
  have ha0 : 0 < a := by rw [ha]; exact Real.sqrt_pos.mpr (by linarith)
  have hb0 : 0 < b := by rw [hb]; exact Real.sqrt_pos.mpr (by linarith)
  have hc0 : 0 < c := by rw [hc]; exact Real.sqrt_pos.mpr (by linarith)
  have hab : a * b ≤ n := by nlinarith [sq_nonneg (a * b), sq_nonneg (a - b)]
  have hsum : a + b ≤ 2 * c := by nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2 * c)]
  have hprod : a * b * (a + b) ≤ 2 * (n * c) := by
    have := mul_le_mul hab hsum (by positivity) (by positivity); linarith
  have e : 2 / a - 2 / b = 2 / (a * b * (a + b)) := by
    field_simp
    nlinarith [ha2, hb2]
  rw [← ha, ← hb, ← hc, e, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

theorem sum_Ico_inv_mul_sqrt_le {j : ℕ} (hj : 1 ≤ j) (N : ℕ) :
    ∑ n ∈ Finset.Ico j N, 1 / ((n : ℝ) * Real.sqrt n) ≤ 3 / Real.sqrt j := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, c = fun n : ℕ => 2 / Real.sqrt ((n : ℝ) - 1 / 2) := ⟨_, rfl⟩
  have hstep : ∀ n, j ≤ n → 1 / ((n : ℝ) * Real.sqrt n) ≤ c n - c (n + 1) := by
    intro n hn
    rw [hc]
    have := inv_mul_sqrt_le_sub (le_trans hj hn)
    push_cast
    rw [show (n : ℝ) + 1 - 1 / 2 = n + 1 / 2 by ring]
    exact this
  have hc0 : ∀ n, 0 ≤ c n := fun n => by rw [hc]; positivity
  have htel : ∀ N, ∑ n ∈ Finset.Ico j N, 1 / ((n : ℝ) * Real.sqrt n) ≤ c j := by
    intro N
    induction N with
    | zero => simp [hc0 j]
    | succ N ih =>
      rcases Nat.lt_or_ge N j with h | h
      · rw [Finset.Ico_eq_empty (by omega)]; simp [hc0 j]
      · have key : ∀ M, j ≤ M → ∑ n ∈ Finset.Ico j M, 1 / ((n : ℝ) * Real.sqrt n) ≤
            c j - c M := by
          intro M hM
          induction M, hM using Nat.le_induction with
          | base => simp
          | succ M hM ihM =>
            rw [Finset.sum_Ico_succ_top hM]
            linarith [hstep M hM]
        linarith [key (N + 1) (by omega), hc0 (N + 1)]
  refine (htel N).trans ?_
  rw [hc]
  simp only
  have h1 : Real.sqrt ((j : ℝ) / 2) ≤ Real.sqrt ((j : ℝ) - 1 / 2) :=
    Real.sqrt_le_sqrt (by linarith)
  have h2 : Real.sqrt ((j : ℝ) / 2) = Real.sqrt j / Real.sqrt 2 := Real.sqrt_div' _ (by norm_num)
  have hs : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hs2 : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs2' : 0 < Real.sqrt 2 := by positivity
  calc 2 / Real.sqrt ((j : ℝ) - 1 / 2) ≤ 2 / Real.sqrt ((j : ℝ) / 2) :=
        div_le_div_of_nonneg_left (by norm_num) (by rw [h2]; positivity) h1
    _ = 2 * Real.sqrt 2 / Real.sqrt j := by rw [h2]; field_simp
    _ ≤ 3 / Real.sqrt j := by
        rw [div_le_div_iff_of_pos_right hs]; linarith

theorem sum_range_inv_sqrt_le (j : ℕ) :
    ∑ n ∈ Finset.range j, 1 / Real.sqrt n ≤ 2 * Real.sqrt j := by
  have key : ∀ j : ℕ, ∑ n ∈ Finset.range (j + 1), 1 / Real.sqrt n ≤ 2 * Real.sqrt j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ]
      have h0 : (0 : ℝ) ≤ Real.sqrt j := Real.sqrt_nonneg _
      have h1 : 0 < Real.sqrt ((j : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
      have hle : Real.sqrt (j : ℝ) ≤ Real.sqrt ((j : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
      have hsq : Real.sqrt ((j : ℝ) + 1) ^ 2 = j + 1 := Real.sq_sqrt (by positivity)
      have hsq' : Real.sqrt (j : ℝ) ^ 2 = j := Real.sq_sqrt (by positivity)
      have : 1 / Real.sqrt ((j : ℝ) + 1) ≤ 2 * Real.sqrt ((j : ℝ) + 1) - 2 * Real.sqrt j := by
        rw [div_le_iff₀ h1]
        nlinarith
      push_cast
      linarith
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; simp
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    refine (key k).trans ?_
    push_cast
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by norm_num)

theorem summable_sum_Ioc_div {a : ℕ → ℝ} (ha0 : ∀ j, 0 ≤ a j)
    (ha : Summable fun j => a j / Real.sqrt j) :
    Summable fun n : ℕ => (∑ j ∈ Finset.Ioc 0 n, a j) / ((n : ℝ) * Real.sqrt n) := by
  refine summable_of_sum_range_le (c := 3 * ∑' j, a j / Real.sqrt j)
    (fun n => div_nonneg (Finset.sum_nonneg fun j _ => ha0 j) (by positivity)) fun N => ?_
  have hsplit : ∀ n ∈ Finset.range N, (∑ j ∈ Finset.Ioc 0 n, a j) / ((n : ℝ) * Real.sqrt n) =
      ∑ j ∈ Finset.range N, (if 0 < j ∧ j ≤ n then a j / ((n : ℝ) * Real.sqrt n) else 0) := by
    intro n hn
    rw [Finset.sum_div, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext j
    simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_range]
    have := Finset.mem_range.mp hn
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h1, h2⟩
    · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
  rw [Finset.sum_congr rfl hsplit, Finset.sum_comm]
  have hinner : ∀ j ∈ Finset.range N, ∑ n ∈ Finset.range N,
      (if 0 < j ∧ j ≤ n then a j / ((n : ℝ) * Real.sqrt n) else 0) ≤ 3 * (a j / Real.sqrt j) := by
    intro j _
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; simp
    · have e : ∑ n ∈ Finset.range N, (if 0 < j ∧ j ≤ n then a j / ((n : ℝ) * Real.sqrt n) else 0)
          = a j * ∑ n ∈ Finset.Ico j N, 1 / ((n : ℝ) * Real.sqrt n) := by
        rw [Finset.mul_sum, ← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun n _ => by ring
        ext n
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        constructor
        · rintro ⟨h1, -, h2⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, h, h1⟩
      rw [e]
      have := mul_le_mul_of_nonneg_left (sum_Ico_inv_mul_sqrt_le h N) (ha0 j)
      calc a j * ∑ n ∈ Finset.Ico j N, 1 / ((n : ℝ) * Real.sqrt n) ≤ a j * (3 / Real.sqrt j) :=
            this
        _ = 3 * (a j / Real.sqrt j) := by ring
  refine (Finset.sum_le_sum hinner).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (ha.sum_le_tsum _ fun j _ => div_nonneg (ha0 j)
    (Real.sqrt_nonneg _)) (by norm_num)

theorem summable_inv_sqrt_mul_tail {a : ℕ → ℝ} (ha0 : ∀ j, 0 ≤ a j)
    (ha : Summable fun j => a j / Real.sqrt j) :
    Summable fun n : ℕ => 1 / Real.sqrt n * ∑' j, (if n < j then a j / j else 0) := by
  have hj : Summable fun j : ℕ => a j / j := by
    refine Summable.of_nonneg_of_le (fun j => div_nonneg (ha0 j) (Nat.cast_nonneg _))
      (fun j => ?_) ha
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; simp
    · have h1 : (1 : ℝ) ≤ j := by exact_mod_cast h
      have hs : Real.sqrt j ≤ j := by
        rw [Real.sqrt_le_left (by linarith)]; nlinarith
      exact div_le_div_of_nonneg_left (ha0 j) (Real.sqrt_pos.mpr (by linarith)) hs
  have hind : ∀ n : ℕ, Summable fun j : ℕ => (if n < j then a j / j else 0) := fun n =>
    Summable.of_nonneg_of_le (fun j => by
        split_ifs
        · exact div_nonneg (ha0 j) (Nat.cast_nonneg _)
        · exact le_rfl)
      (fun j => by split_ifs <;> simp [div_nonneg (ha0 j) (Nat.cast_nonneg j)]) hj
  refine summable_of_sum_range_le (c := 2 * ∑' j, a j / Real.sqrt j)
    (fun n => mul_nonneg (by positivity) (tsum_nonneg fun j => by
      split_ifs <;> simp [div_nonneg (ha0 j) (Nat.cast_nonneg j)])) fun N => ?_
  have e : ∑ n ∈ Finset.range N, 1 / Real.sqrt n * ∑' j, (if n < j then a j / j else 0) =
      ∑' j, ∑ n ∈ Finset.range N, 1 / Real.sqrt n * (if n < j then a j / j else 0) := by
    rw [Summable.tsum_finsetSum fun n _ => (hind n).mul_left _]
    exact Finset.sum_congr rfl fun n _ => (tsum_mul_left).symm
  rw [e, ← tsum_mul_left]
  have hpt : ∀ j, ∑ n ∈ Finset.range N, 1 / Real.sqrt n * (if n < j then a j / j else 0) ≤
      2 * (a j / Real.sqrt j) := by
    intro j
    have e2 : ∑ n ∈ Finset.range N, 1 / Real.sqrt n * (if n < j then a j / j else 0) =
        a j / j * ∑ n ∈ (Finset.range N).filter (· < j), 1 / Real.sqrt n := by
      rw [Finset.mul_sum, Finset.sum_filter]
      exact Finset.sum_congr rfl fun n _ => by split_ifs <;> ring
    rw [e2]
    have hsub : ∑ n ∈ (Finset.range N).filter (· < j), 1 / Real.sqrt n ≤ 2 * Real.sqrt j := by
      refine (Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun _ _ _ => by
        positivity).trans (sum_range_inv_sqrt_le j)
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hn).2
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; simp
    · have hs : 0 < Real.sqrt j := Real.sqrt_pos.mpr (by exact_mod_cast h)
      have hsq : Real.sqrt (j : ℝ) ^ 2 = j := Real.sq_sqrt (Nat.cast_nonneg _)
      have hjpos : (0 : ℝ) < j := by exact_mod_cast h
      calc a j / j * ∑ n ∈ (Finset.range N).filter (· < j), 1 / Real.sqrt n ≤
            a j / j * (2 * Real.sqrt j) :=
            mul_le_mul_of_nonneg_left hsub (div_nonneg (ha0 j) hjpos.le)
        _ = 2 * a j * (Real.sqrt j / j) := by ring
        _ = 2 * a j * (1 / Real.sqrt j) := by
            congr 1
            rw [div_eq_div_iff hjpos.ne' hs.ne', one_mul, Real.mul_self_sqrt hjpos.le]
        _ = 2 * (a j / Real.sqrt j) := by ring
  have hsum2 : Summable fun j : ℕ => 2 * (a j / Real.sqrt j) := ha.mul_left 2
  refine (Summable.tsum_le_tsum hpt ?_ hsum2).trans le_rfl
  refine Summable.of_nonneg_of_le (fun j => Finset.sum_nonneg fun n _ => mul_nonneg (by
    positivity) (by split_ifs <;> simp [div_nonneg (ha0 j) (Nat.cast_nonneg j)])) hpt hsum2

/-! ## `M(1) = 0` forces `λ = Λ` -/

theorem summable_abs_div_sqrt {f : ℕ → ℝ} (hf : LSeriesSummable (fun n => (f n : ℂ)) (1 / 2)) :
    Summable fun j : ℕ => |f j| / Real.sqrt j := by
  refine (summable_norm_iff.mpr hf).congr fun j => ?_
  rw [LSeries.norm_term_eq]
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; simp
  · rw [if_neg h.ne', Complex.norm_real, Real.norm_eq_abs, Real.sqrt_eq_rpow]
    norm_num

theorem mu_eq_tsum (hm : LSeriesSummable (fun n => (m n : ℂ)) (1 / 2)) :
    mu m = ∑' j : ℕ, m j / j := by
  have h1 : LSeriesSummable (fun n => (m n : ℂ)) 1 := summable_of_half hm (by norm_num)
  rw [mu, mSeries, LSeries, Complex.re_tsum h1]
  refine tsum_congr fun j => ?_
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; simp
  · rw [LSeries.term_of_ne_zero h.ne', Complex.cpow_one, ← Complex.ofReal_natCast,
      ← Complex.ofReal_div, Complex.ofReal_re]

/-- The arithmetic function `n ↦ m(n)` (zero at `0`). -/
def mArith (m : ℕ → ℝ) : ArithmeticFunction ℝ := ⟨fun n => if n = 0 then 0 else m n, by simp⟩

theorem sum_Ioc_divisors_eq (m : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.Ioc 0 n, ∑ j ∈ k.divisors, m j =
      ∑ j ∈ Finset.Ioc 0 n, m j * ((n / j : ℕ) : ℝ) := by
  have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (mArith m) n
  have hl : ∀ k ∈ Finset.Ioc 0 n, (mArith m * ↑ArithmeticFunction.zeta) k =
      ∑ j ∈ k.divisors, m j := by
    intro k _
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    refine Finset.sum_congr rfl fun j hj => ?_
    have : j ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hj)
    simp [mArith, this]
  have hr : ∀ j ∈ Finset.Ioc 0 n, mArith m j * ((n / j : ℕ) : ℝ) = m j * ((n / j : ℕ) : ℝ) := by
    intro j hj
    have : j ≠ 0 := by have := (Finset.mem_Ioc.mp hj).1; omega
    simp [mArith, this]
  rw [Finset.sum_congr rfl hl, Finset.sum_congr rfl hr] at h
  exact h

theorem sum_Icc_carrier_eq (m : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 2 n, carrier m k = ∑ j ∈ Finset.Ioc 0 n, m j * ((n / j : ℕ) : ℝ) - m 1 := by
  rw [← sum_Ioc_divisors_eq]
  have hI : Finset.Ioc 0 n = insert 1 (Finset.Icc 2 n) := by
    ext k; simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hI, Finset.sum_insert (by simp), Nat.divisors_one, Finset.sum_singleton]
  have : ∑ k ∈ Finset.Icc 2 n, carrier m k = ∑ k ∈ Finset.Icc 2 n, ∑ j ∈ k.divisors, m j :=
    Finset.sum_congr rfl fun k hk => by
      rw [carrier, if_pos (Finset.mem_Icc.mp hk).1]
  rw [this]; ring

theorem tsum_split_le (f : ℕ → ℝ) (hf : Summable f) (h0 : f 0 = 0) (n : ℕ) :
    ∑' j, f j = ∑ j ∈ Finset.Ioc 0 n, f j + ∑' j, (if n < j then f j else 0) := by
  have hlo : Summable fun j => if j ≤ n then f j else 0 :=
    summable_of_ne_finset_zero (s := Finset.range (n + 1)) fun j hj => by
      rw [if_neg]; simp at hj; omega
  have hhi : Summable fun j => if n < j then f j else 0 :=
    hf.indicator {j | n < j} |>.congr fun j => by
      simp [Set.indicator_apply]
  have hsplit : ∑' j, f j =
      ∑' j, (if j ≤ n then f j else 0) + ∑' j, (if n < j then f j else 0) := by
    rw [← hlo.tsum_add hhi]
    refine tsum_congr fun j => ?_
    by_cases h : j ≤ n
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]
  rw [hsplit, tsum_eq_sum (s := Finset.range (n + 1)) fun j hj => by
    rw [if_neg]; simp at hj; omega]
  congr 1
  have hR : Finset.range (n + 1) = insert 0 (Finset.Ioc 0 n) := by
    ext j; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]; omega
  rw [hR, Finset.sum_insert (by simp), if_pos (Nat.zero_le _), h0, zero_add]
  exact Finset.sum_congr rfl fun j hj => by rw [if_pos (Finset.mem_Ioc.mp hj).2]

theorem abs_sum_Icc_carrier_le (hm : LSeriesSummable (fun n => (m n : ℂ)) (1 / 2))
    (hμ : mu m = 0) {n : ℕ} (hn : 1 ≤ n) :
    |∑ k ∈ Finset.Icc 2 n, carrier m k| ≤ |m 1| + ∑ j ∈ Finset.Ioc 0 n, |m j| +
      n * ∑' j, (if n < j then |m j| / j else 0) := by
  have hs1 := summable_abs_div_sqrt hm
  have hsum : Summable fun j : ℕ => m j / j := by
    refine Summable.of_norm_bounded hs1 fun j => ?_
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; simp
    · have h1 : (1 : ℝ) ≤ j := by exact_mod_cast h
      exact div_le_div_of_nonneg_left (abs_nonneg _) (Real.sqrt_pos.mpr (by linarith))
        (by rw [Real.sqrt_le_left (by linarith)]; nlinarith)
  have hsplit := tsum_split_le (fun j => m j / j) hsum (by simp) n
  rw [← mu_eq_tsum hm, hμ] at hsplit
  rw [sum_Icc_carrier_eq m hn]
  -- `⌊n/j⌋ = n/j − δ_j`
  have hdiff : |∑ j ∈ Finset.Ioc 0 n, m j * ((n / j : ℕ) : ℝ) -
      n * ∑ j ∈ Finset.Ioc 0 n, m j / j| ≤ ∑ j ∈ Finset.Ioc 0 n, |m j| := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    have hj : 0 < j := (Finset.mem_Ioc.mp hj).1
    have hjr : (0 : ℝ) < j := by exact_mod_cast hj
    have hle : ((n / j : ℕ) : ℝ) ≤ n / j := Nat.cast_div_le
    have hlt : (n : ℝ) / j - 1 < ((n / j : ℕ) : ℝ) := by
      rw [sub_lt_iff_lt_add, div_lt_iff₀ hjr]
      have := Nat.lt_div_mul_add (a := n) hj
      have : (n : ℝ) < ((n / j : ℕ) : ℝ) * j + j := by exact_mod_cast this
      linarith
    have e : m j * ((n / j : ℕ) : ℝ) - n * (m j / j) = m j * (((n / j : ℕ) : ℝ) - n / j) := by ring
    rw [e, abs_mul]
    have : |((n / j : ℕ) : ℝ) - n / j| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    nlinarith [abs_nonneg (m j)]
  have htail : |∑' j, (if n < j then m j / j else 0)| ≤
      ∑' j, (if n < j then |m j| / j else 0) := by
    have hs : Summable fun j : ℕ => if n < j then m j / j else 0 :=
      hsum.indicator {j | n < j} |>.congr fun j => by simp [Set.indicator_apply]
    refine (norm_tsum_le_tsum_norm hs.norm).trans (le_of_eq (tsum_congr fun j => ?_))
    split_ifs <;> simp
  have hmain : ∑ j ∈ Finset.Ioc 0 n, m j / j = -∑' j, (if n < j then m j / j else 0) := by
    linarith
  rw [hmain] at hdiff
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  calc |∑ j ∈ Finset.Ioc 0 n, m j * ((n / j : ℕ) : ℝ) - m 1|
      ≤ |∑ j ∈ Finset.Ioc 0 n, m j * ((n / j : ℕ) : ℝ) -
          n * -∑' j, (if n < j then m j / j else 0)| +
        |(n : ℝ) * -∑' j, (if n < j then m j / j else 0)| + |m 1| := by
        have := abs_sub_le (∑ j ∈ Finset.Ioc 0 n, m j * ((n / j : ℕ) : ℝ))
          ((n : ℝ) * -∑' j, (if n < j then m j / j else 0)) 0
        have h2 := abs_sub (∑ j ∈ Finset.Ioc 0 n, m j * ((n / j : ℕ) : ℝ)) (m 1)
        simp only [sub_zero] at this
        linarith
    _ ≤ ∑ j ∈ Finset.Ioc 0 n, |m j| + n * ∑' j, (if n < j then |m j| / j else 0) + |m 1| := by
        rw [abs_mul, abs_neg, abs_of_nonneg hn0]
        nlinarith [mul_le_mul_of_nonneg_left htail hn0]
    _ = _ := by ring

theorem summable_partialSumWeight_carrier (hm : LSeriesSummable (fun n => (m n : ℂ)) (1 / 2))
    (hv : BoundaryRegular v) (hμ : mu m = 0) :
    Summable (partialSumWeight fun n => carrier m n + v n) := by
  have hm1 := summable_abs_div_sqrt hm
  have hv1 := summable_abs_div_sqrt hv.summable
  have hA := summable_sum_Ioc_div (fun j => abs_nonneg (m j)) hm1
  have hV := summable_sum_Ioc_div (fun j => abs_nonneg (v j)) hv1
  have hT := summable_inv_sqrt_mul_tail (fun j => abs_nonneg (m j)) hm1
  refine Summable.of_nonneg_of_le (partialSumWeight_nonneg _) (fun n => ?_)
    (((hA.mul_left 2).add hV).add hT)
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [partialSumWeight]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h
  have hden : 0 < (n : ℝ) * Real.sqrt n := by positivity
  unfold partialSumWeight partialFrom2
  rw [Finset.sum_add_distrib, div_le_iff₀ hden]
  have h1 := abs_sum_Icc_carrier_le hm hμ h
  have h2 : |∑ k ∈ Finset.Icc 2 n, v k| ≤ ∑ j ∈ Finset.Ioc 0 n, |v j| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (fun k hk => ?_) fun _ _ _ => abs_nonneg _)
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hk ⊢; omega
  have hm1le : |m 1| ≤ ∑ j ∈ Finset.Ioc 0 n, |m j| :=
    Finset.single_le_sum (f := fun j => |m j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_Ioc.mpr ⟨by norm_num, h⟩)
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (by linarith)
  have hs0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hT0 : 0 ≤ ∑' j, (if n < j then |m j| / j else 0) :=
    tsum_nonneg fun j => by
      split_ifs
      · exact div_nonneg (abs_nonneg _) (Nat.cast_nonneg (α := ℝ) j)
      · exact le_rfl
  have e : (2 * ((∑ j ∈ Finset.Ioc 0 n, |m j|) / ((n : ℝ) * Real.sqrt n)) +
      (∑ j ∈ Finset.Ioc 0 n, |v j|) / ((n : ℝ) * Real.sqrt n) +
        1 / Real.sqrt n * ∑' j, (if n < j then |m j| / j else 0)) * ((n : ℝ) * Real.sqrt n) =
      2 * ∑ j ∈ Finset.Ioc 0 n, |m j| + ∑ j ∈ Finset.Ioc 0 n, |v j| +
        n * ∑' j, (if n < j then |m j| / j else 0) := by
    field_simp
  rw [e]
  have := abs_add_le (∑ k ∈ Finset.Icc 2 n, carrier m k) (∑ k ∈ Finset.Icc 2 n, v k)
  linarith

/-- **`M(1) = 0` forces `λ = Λ`.** -/
theorem eq_vonMangoldt_of_mu_eq_zero (hm : LSeriesSummable (fun n => (m n : ℂ)) (1 / 2))
    (hv : BoundaryRegular v) (hW : WeilPositiveFull (carrierSystem β m v)) (hμ : mu m = 0)
    {n : ℕ} (hn : 2 ≤ n) : carrierSystem β m v n = ArithmeticFunction.vonMangoldt n := by
  have hβ : β = 1 := by linarith [beta_add_mu hm hv hW]
  have hfun : carrierSystem β m v =
      fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + (carrier m n + v n) := by
    funext n; simp only [carrierSystem, hβ]; ring
  have hpos := weilPositive_of_weilPositiveFull hW
  rw [hfun] at hpos
  have hE : Summable (partialSumWeight fun n => carrier m n + v n - 0 - 0 * sqrtStep n) := by
    simpa using summable_partialSumWeight_carrier hm hv hμ
  have hw := vonMangoldt_add_twoPole_eq_zero hE hpos hn
  rw [hfun]
  simp [hw]

end RHTower.WeilZetaCarrier
