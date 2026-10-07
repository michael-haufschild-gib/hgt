import GaloisForLFunctions.RHTower.WeilConeZetaPoleProducerObstruction
import GaloisForLFunctions.RHTower.WeilConeBoundaryDilationRigidity
import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.RHTower.HardyZThetaTrace

/-!
# The pencil `βΛ + γ·[n ≥ 2] + v` meets the Weil cone at most in `Λ`

Let `v : ℕ → ℝ` with `v(0) = v(1) = 0` and `Σ |v(n)| n^{−½} < ∞`, and let `β, γ ∈ ℝ`. The system
`λ = βΛ + γ·[n ≥ 2] + v` has Dirichlet series `−β ζ′/ζ + γ(ζ − 1) + V`. It interpolates between
the von Mangoldt producer (`γ = 0`) and the ζ-type pole carrier (`β = 0`, MUST-813).

**Theorem** (`eq_vonMangoldt_of_weilPositiveFull_pencil`). If `λ` is full-cone Weil-positive, then
`β = 1`, `γ = 0` and `v = 0`, so `λ = Λ`.

**Proof.**
* The master identity `Z₁((s−1)(Φ − G + V) − 1) = β((s−1)Z₁′ − Z₁) − γ Z₁(Z₁ − (s − 1))` on
  `Re s > ½`, with `Z₁ = (s − 1)ζ`, gives `β + γ = 1` at `s = 1`. It also gives `Φ ζ = H` with
  `H = (G + 1/(s−1) − γ(ζ − 1) − V) ζ + β ζ′`.
* `H` is continuous up to the line and `Re(H ζ̄) = |ζ|² Re Φ ≥ 0`. On the line the functional
  equation (`Re((G + 1/(s−1))|ζ|²) = θ′|ζ|² = −Re(ζ′ζ̄)`) turns this into
  `|ζ|² (γ (θ′ − Re ζ + 1) − Re V) ≥ 0`.
* `γ > 0`: `Re ζ(½+it) ≤ θ′ + 1 + S_V/γ` wherever `ζ ≠ 0`, against the resonance theorem
  (`ZetaResonator.exists_log_add_lt_re_zeta`).
* `γ < 0`: `Re ζ(½+it) ≥ θ′ + 1 − S_V/|γ|` wherever `ζ ≠ 0`. Near a zero of `ζ` on the line at
  large height (Hardy, `exists_Xi_zero_gt`) the zeros are isolated, so `Re ζ` would be `≥ 1` on a
  punctured neighbourhood while tending to `0`.
* `γ = 0`: `λ = Λ + v`, and the boundary-class rigidity (MUST-804) gives `v = 0`.
-/

noncomputable section

open Complex Filter Topology Set
open scoped ComplexConjugate
open RHTower.WeilSpectral RHTower.WeilHerglotz RHTower.WeilFiniteType RHTower.WeilInfiniteDilation
open RHTower.WeilZetaSquare

namespace RHTower.WeilPencil

open RHTower.WeilBoundaryDilation (BoundaryRegular regSeries)

/-- The pencil `λ(n) = β Λ(n) + γ · [n ≥ 2] + v(n)`. -/
def pencil (β γ : ℝ) (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  β * ArithmeticFunction.vonMangoldt n + γ * (if 2 ≤ n then 1 else 0) + v n

variable {β γ : ℝ} {v : ℕ → ℝ}

theorem LSeries_pencil (hv : BoundaryRegular v) {s : ℂ} (hs : 1 < s.re) :
    LSeries (lamC (pencil β γ v)) s =
      -(β * deriv riemannZeta s / riemannZeta s) + γ * (riemannZeta s - 1) + regSeries v s := by
  have hΛ := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have hV : LSeriesSummable (fun n => (v n : ℂ)) s :=
    hv.summable.of_re_le_re (by norm_num; linarith)
  have hδ : Summable fun n : ℕ => (γ : ℂ) * (if n = 1 then 1 else 0) :=
    summable_of_ne_finset_zero (s := {1}) fun n hn => by simp at hn; simp [hn]
  have hpt : ∀ n, LSeries.term (lamC (pencil β γ v)) s n =
      (β : ℂ) * LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n +
        (γ : ℂ) * LSeries.term 1 s n + LSeries.term (fun n => (v n : ℂ)) s n -
          (γ : ℂ) * (if n = 1 then 1 else 0) := by
    intro n
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · simp [LSeries.term]
      · simp [LSeries.term, lamC, hv.one]
    · have hn0 : n ≠ 0 := by omega
      have hn1 : n ≠ 1 := by omega
      simp only [LSeries.term, if_neg hn0, if_neg hn1, lamC, pencil, if_pos h, Pi.one_apply]
      push_cast
      ring
  rw [LSeries, tsum_congr hpt, Summable.tsum_sub (((hΛ.mul_left _).add (h1.mul_left _)).add hV) hδ,
    Summable.tsum_add ((hΛ.mul_left _).add (h1.mul_left _)) hV,
    Summable.tsum_add (hΛ.mul_left _) (h1.mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_mul_left, tsum_ite_eq, ← LSeries, ← LSeries, LSeries_one_eq_riemannZeta hs,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  simp only [regSeries, LSeries, mul_one]
  ring

/-- **The master identity** for the pencil on `Re s > ½`. -/
theorem masterLeft_pencil (hv : BoundaryRegular v) (hW : WeilPositiveFull (pencil β γ v))
    {s : ℂ} (hs : 1 / 2 < s.re) :
    masterLeft hW (regSeries v) s =
      β * ((s - 1) * deriv zetaResidueUnit s - zetaResidueUnit s) -
        γ * (zetaResidueUnit s * (zetaResidueUnit s - (s - 1))) := by
  have hpre : IsPreconnected {s : ℂ | 1 / 2 < s.re} :=
    (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have h2U : (2 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by show (1 / 2 : ℝ) < (2 : ℂ).re; norm_num
  have hZ : AnalyticOnNhd ℂ zetaResidueUnit univ := fun s _ => analyticAt_zetaResidueUnit s
  have hR : AnalyticOnNhd ℂ (fun s => β * ((s - 1) * deriv zetaResidueUnit s - zetaResidueUnit s) -
      γ * (zetaResidueUnit s * (zetaResidueUnit s - (s - 1)))) {s : ℂ | 1 / 2 < s.re} := by
    intro s _
    have h1 : AnalyticAt ℂ (fun z : ℂ => z - 1) s := analyticAt_id.sub analyticAt_const
    exact (analyticAt_const.mul ((h1.mul (hZ.deriv s trivial)).sub (hZ s trivial))).sub
      (analyticAt_const.mul ((hZ s trivial).mul ((hZ s trivial).sub h1)))
  refine (analyticOnNhd_masterLeft hW
    (WeilBoundaryDilation.differentiableOn_regSeries hv)).eqOn_of_preconnected_of_eventuallyEq
    hR hpre h2U ?_ hs
  have hV1 : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [hV1] with z hz
  have hz : 1 < z.re := hz
  have hz1 : z ≠ 1 := by intro h; rw [h] at hz; simp at hz
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hζ : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hz
  unfold masterLeft
  rw [weilContinuation_eq hW hz, weilFunction, LSeries_pencil hv hz,
    ← sq_mul_deriv_riemannZeta hz1, (zetaResidueUnit_eventuallyEq hz1).eq_of_nhds]
  unfold zetaArchimedeanDatum
  field_simp
  ring

theorem beta_add_gamma (hv : BoundaryRegular v) (hW : WeilPositiveFull (pencil β γ v)) :
    β + γ = 1 := by
  have h := masterLeft_pencil hv hW (s := 1) (by norm_num)
  unfold masterLeft at h
  simp only [sub_self, zero_mul, zetaResidueUnit_one, zero_sub, mul_neg, mul_one, sub_zero] at h
  have := congrArg Complex.re h
  simp at this
  linarith

/-- The boundary numerator `H = (G + 1/(s−1) − γ(ζ − 1) − V) ζ + β ζ′`. -/
def pencilNumerator (β γ : ℝ) (v : ℕ → ℝ) (s : ℂ) : ℂ :=
  (zetaArchimedeanDatum s + 1 / (s - 1) - γ * (riemannZeta s - 1) - regSeries v s) *
    riemannZeta s + β * deriv riemannZeta s

theorem weilContinuation_mul_zeta_pencil (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (pencil β γ v)) {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    weilContinuation hW s * riemannZeta s = pencilNumerator β γ v s := by
  have h := masterLeft_pencil hv hW hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  unfold masterLeft at h
  rw [← sq_mul_deriv_riemannZeta hs1, (zetaResidueUnit_eventuallyEq hs1).eq_of_nhds] at h
  unfold pencilNumerator
  apply mul_left_cancel₀ (pow_ne_zero 2 hs1')
  have e : (s - 1) ^ 2 * (weilContinuation hW s * riemannZeta s) =
      (s - 1) * riemannZeta s * ((s - 1) * (weilContinuation hW s - zetaArchimedeanDatum s +
        regSeries v s) - 1) + (s - 1) ^ 2 * riemannZeta s *
          (zetaArchimedeanDatum s - regSeries v s) + (s - 1) * riemannZeta s := by ring
  rw [e, h]
  field_simp
  ring

theorem re_pencilNumerator_mul_conj_nonneg (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (pencil β γ v)) {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    0 ≤ (pencilNumerator β γ v s * conj (riemannZeta s)).re := by
  rw [← weilContinuation_mul_zeta_pencil hv hW hs hs1, mul_assoc, Complex.mul_conj,
    Complex.re_mul_ofReal]
  exact mul_nonneg (re_weilContinuation_nonneg hW hs) (Complex.normSq_nonneg _)

theorem continuousWithinAt_pencilNumerator (hv : BoundaryRegular v) (t : ℝ) :
    ContinuousWithinAt (fun s => (pencilNumerator β γ v s * conj (riemannZeta s)).re)
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
  have hH : ContinuousWithinAt (pencilNumerator β γ v) {s : ℂ | 1 / 2 ≤ s.re} (linePt t) := by
    unfold pencilNumerator
    have hA : ContinuousAt (fun s => zetaArchimedeanDatum s + 1 / (s - 1) -
        γ * (riemannZeta s - 1)) (linePt t) :=
      (hG.add hinv).sub (continuousAt_const.mul (hZ.sub continuousAt_const))
    exact ((hA.continuousWithinAt.sub hV).mul hZ.continuousWithinAt).add
      (continuousAt_const.mul hZ').continuousWithinAt
  exact Complex.continuous_re.continuousAt.comp_continuousWithinAt
    (hH.mul (Complex.continuous_conj.continuousAt.comp_continuousWithinAt hZ.continuousWithinAt))

theorem re_pencilNumerator_line_nonneg (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (pencil β γ v)) (t : ℝ) :
    0 ≤ (pencilNumerator β γ v (linePt t) * conj (riemannZeta (linePt t))).re := by
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
  refine ge_of_tendsto ((continuousWithinAt_pencilNumerator hv t).tendsto.comp hlim) ?_
  have hev : ∀ᶠ σ in 𝓝[>] (1 / 2 : ℝ), σ < 1 :=
    nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num))
  filter_upwards [self_mem_nhdsWithin, hev] with σ hσ hσ1
  have hσ' : (1 / 2 : ℝ) < σ := hσ
  have hne : path σ ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hpre] at this; simp at this; linarith
  exact re_pencilNumerator_mul_conj_nonneg hv hW (by rw [hpre]; exact hσ') hne

/-- **The line inequality**: `|ζ|² (γ(θ′ − Re ζ + 1) − Re V) ≥ 0` at every height. -/
theorem line_ineq (hv : BoundaryRegular v) (hW : WeilPositiveFull (pencil β γ v)) (t : ℝ) :
    0 ≤ Complex.normSq (riemannZeta (linePt t)) * (γ * (gammaHardyPhaseRate t -
      (riemannZeta (linePt t)).re + 1) - (regSeries v (linePt t)).re) := by
  have h := re_pencilNumerator_line_nonneg hv hW t
  have hβ : β = 1 - γ := by linarith [beta_add_gamma hv hW]
  have hd := re_datum_add_inv_line t
  have hP := re_deriv_mul_conj_line t
  obtain ⟨z, hz⟩ : ∃ z, z = riemannZeta (linePt t) := ⟨_, rfl⟩
  rw [← hz] at h hP ⊢
  have e : pencilNumerator β γ v (linePt t) * conj z =
      (zetaArchimedeanDatum (linePt t) + 1 / (linePt t - 1)) * ((Complex.normSq z : ℝ) : ℂ) -
        γ * (z - 1) * ((Complex.normSq z : ℝ) : ℂ) -
          regSeries v (linePt t) * ((Complex.normSq z : ℝ) : ℂ) +
            β * (deriv riemannZeta (linePt t) * conj z) := by
    unfold pencilNumerator
    rw [← hz, ← Complex.mul_conj]
    ring
  rw [e, Complex.add_re, Complex.sub_re, Complex.sub_re, Complex.re_mul_ofReal,
    Complex.re_mul_ofReal, Complex.re_mul_ofReal, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
    hd, hP, Complex.sub_re, Complex.one_re] at h
  have e3 : Complex.normSq z * (γ * (gammaHardyPhaseRate t - z.re + 1) -
      (regSeries v (linePt t)).re) =
      gammaHardyPhaseRate t * Complex.normSq z - γ * (z.re - 1) * Complex.normSq z -
        (regSeries v (linePt t)).re * Complex.normSq z +
          β * -(gammaHardyPhaseRate t * Complex.normSq z) := by
    rw [hβ]; ring
  rw [e3]
  exact h

/-! ## The three cases -/

/-- `S_V = Σ |v(n)| n^{−½}` bounds `|Re V|` on the line. -/
theorem abs_re_regSeries_line_le (hv : BoundaryRegular v) (t : ℝ) :
    |(regSeries v (linePt t)).re| ≤ ∑' n, ‖LSeries.term (fun n => (v n : ℂ)) (1 / 2) n‖ :=
  (Complex.abs_re_le_norm _).trans (WeilBoundaryDilation.norm_LSeries_linePt_le hv.summable t)

theorem gammaHardyPhaseRate_le {t : ℝ} (ht : 1 ≤ t) : gammaHardyPhaseRate t ≤ Real.log t + 4 := by
  have ht0 : 0 < t := by linarith
  have hb := gammaHardyPhaseRate_sub_log_conductor_bound ht0
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have hlog2 : Real.log (t / (2 * Real.pi)) ≤ Real.log t :=
    Real.log_le_log (by positivity) (div_le_self ht0.le (by nlinarith [Real.pi_gt_three]))
  have h1 : 33 / (16 * t ^ 2) ≤ 33 / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have h2 : Real.pi / (2 * t) ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [Real.pi_pos]
  linarith [(abs_le.mp hb).2, Real.pi_lt_d2]

theorem log_div_sub_le_gammaHardyPhaseRate {t : ℝ} (ht : 1 ≤ t) :
    Real.log (t / (2 * Real.pi)) / 2 - 4 ≤ gammaHardyPhaseRate t := by
  have ht0 : 0 < t := by linarith
  have hb := gammaHardyPhaseRate_sub_log_conductor_bound ht0
  have h1 : 33 / (16 * t ^ 2) ≤ 33 / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have h2 : Real.pi / (2 * t) ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [Real.pi_pos]
  linarith [(abs_le.mp hb).1, Real.pi_lt_d2]

/-- **`γ > 0` is impossible**: resonance beats `Re ζ ≤ θ′ + 1 + S_V/γ`. -/
theorem gamma_nonpos (hv : BoundaryRegular v) (hW : WeilPositiveFull (pencil β γ v)) :
    γ ≤ 0 := by
  by_contra hγ
  push Not at hγ
  obtain ⟨S, hS⟩ : ∃ S, S = ∑' n, ‖LSeries.term (fun n => (v n : ℂ)) (1 / 2) n‖ := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; exact tsum_nonneg fun _ => norm_nonneg _
  obtain ⟨t, ht1, ht⟩ := ZetaResonator.exists_log_add_lt_re_zeta (5 + S / γ) 1
  have hl := line_ineq hv hW t
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hSγ : 0 ≤ S / γ := div_nonneg hS0 hγ.le
  have hpos : 0 < (riemannZeta (linePt t)).re := by linarith
  have hz : riemannZeta (linePt t) ≠ 0 := fun h => by rw [h] at hpos; simp at hpos
  have hN : 0 < Complex.normSq (riemannZeta (linePt t)) := Complex.normSq_pos.mpr hz
  have hb := (mul_nonneg_iff_of_pos_left hN).mp hl
  have hV := abs_re_regSeries_line_le hv t
  rw [← hS] at hV
  have h1 : -S ≤ γ * (gammaHardyPhaseRate t - (riemannZeta (linePt t)).re + 1) := by
    linarith [(abs_le.mp hV).1]
  have h2 : -(S / γ) ≤ gammaHardyPhaseRate t - (riemannZeta (linePt t)).re + 1 := by
    have : (-S) / γ ≤ gammaHardyPhaseRate t - (riemannZeta (linePt t)).re + 1 :=
      (div_le_iff₀ hγ).mpr (by linarith)
    rwa [neg_div] at this
  linarith [gammaHardyPhaseRate_le ht1]

theorem linePt_im (t : ℝ) : (linePt t).im = t := by simp [linePt]

/-- Zeros of `ζ` on the critical line are isolated. -/
theorem eventually_zeta_linePt_ne_zero (t₀ : ℝ) :
    ∀ᶠ t in 𝓝[≠] t₀, riemannZeta (linePt t) ≠ 0 := by
  have hρ1 : linePt t₀ ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [linePt_re] at this; norm_num at this
  have han : AnalyticAt ℂ riemannZeta (linePt t₀) := analyticOn_riemannZeta _ hρ1
  rcases han.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have hU : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := fun z hz => analyticOn_riemannZeta z hz
    have hpre : IsPreconnected ({1}ᶜ : Set ℂ) :=
      (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
        (1 : ℂ)).isPreconnected
    have h2 := hU.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre (z₀ := linePt t₀) hρ1 h
      (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num)
    exact riemannZeta_ne_zero_of_one_lt_re (by norm_num : 1 < (2 : ℂ).re) h2
  · have hlim : Tendsto (fun t : ℝ => linePt t) (𝓝[≠] t₀) (𝓝[≠] (linePt t₀)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (continuous_linePt.tendsto t₀).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        intro heq
        apply ht
        have := congrArg Complex.im heq
        rwa [linePt_im, linePt_im] at this
    exact hlim.eventually h

/-- **`γ < 0` is impossible**: `Re ζ ≥ θ′ + 1 − S_V/|γ|` off the zeros, against a zero of `ζ`
on the line at large height (Hardy). -/
theorem gamma_nonneg (hv : BoundaryRegular v) (hW : WeilPositiveFull (pencil β γ v)) :
    0 ≤ γ := by
  by_contra hγ
  push Not at hγ
  obtain ⟨S, hS⟩ : ∃ S, S = ∑' n, ‖LSeries.term (fun n => (v n : ℂ)) (1 / 2) n‖ := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; exact tsum_nonneg fun _ => norm_nonneg _
  have hc : 0 < -γ := by linarith
  have key : ∀ t, riemannZeta (linePt t) ≠ 0 →
      gammaHardyPhaseRate t + 1 - S / (-γ) ≤ (riemannZeta (linePt t)).re := by
    intro t hz
    have hN : 0 < Complex.normSq (riemannZeta (linePt t)) := Complex.normSq_pos.mpr hz
    have hb := (mul_nonneg_iff_of_pos_left hN).mp (line_ineq hv hW t)
    have hV := abs_re_regSeries_line_le hv t
    rw [← hS] at hV
    have h1 : (-γ) * (gammaHardyPhaseRate t - (riemannZeta (linePt t)).re + 1) ≤ S := by
      linarith [(abs_le.mp hV).1]
    have h2 : gammaHardyPhaseRate t - (riemannZeta (linePt t)).re + 1 ≤ S / (-γ) := by
      rw [le_div_iff₀ hc]; linarith
    linarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = 2 * Real.pi * Real.exp (2 * (4 + S / (-γ))) := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE]; positivity
  obtain ⟨t₀, ht₀, hXi⟩ := exists_Xi_zero_gt (2 * E + 2)
  have hz0 : riemannZeta (linePt t₀) = 0 := by
    have hZ := (Xi_eq_zero_iff_hardyZ t₀).mp hXi
    have := WeilBoundaryDilation.norm_riemannZeta_linePt t₀
    rw [hZ, abs_zero] at this
    exact norm_eq_zero.mp this
  -- near `t₀`, `Re ζ ≥ 1`
  have hlarge : ∀ᶠ t in 𝓝[≠] t₀, 1 ≤ (riemannZeta (linePt t)).re := by
    have hnear : ∀ᶠ t in 𝓝[≠] t₀, t₀ - 1 < t :=
      nhdsWithin_le_nhds (eventually_gt_nhds (by linarith))
    filter_upwards [eventually_zeta_linePt_ne_zero t₀, hnear] with t hz ht
    have ht1 : 1 ≤ t := by linarith
    have htE : E ≤ t / 1 := by rw [div_one]; linarith
    have hlog : 2 * (4 + S / (-γ)) ≤ Real.log (t / (2 * Real.pi)) := by
      rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
      rw [hE] at htE; linarith
    have := key t hz
    have := log_div_sub_le_gammaHardyPhaseRate ht1
    linarith
  -- but `Re ζ(½ + it) → 0`
  have hsmall : ∀ᶠ t in 𝓝[≠] t₀, (riemannZeta (linePt t)).re < 1 := by
    have hc : Tendsto (fun t => (riemannZeta (linePt t)).re) (𝓝 t₀)
        (𝓝 (riemannZeta (linePt t₀)).re) :=
      (Complex.continuous_re.comp continuous_zeta_line).tendsto t₀
    rw [hz0, Complex.zero_re] at hc
    exact nhdsWithin_le_nhds (hc.eventually (gt_mem_nhds (by norm_num)))
  obtain ⟨t, h1, h2⟩ := (hlarge.and hsmall).exists
  linarith

/-- **The pencil theorem.** If `βΛ + γ·[n ≥ 2] + v` is full-cone Weil-positive, with
`v(0) = v(1) = 0` and `Σ |v(n)| n^{−½} < ∞`, then `β = 1`, `γ = 0` and `v = 0`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_pencil (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (pencil β γ v)) : β = 1 ∧ γ = 0 ∧ ∀ n, v n = 0 := by
  have hγ : γ = 0 := le_antisymm (gamma_nonpos hv hW) (gamma_nonneg hv hW)
  have hβ : β = 1 := by linarith [beta_add_gamma hv hW]
  refine ⟨hβ, hγ, ?_⟩
  have he : pencil β γ v = finiteTypeSeq (fun n => if n = 1 then 1 else 0) 0 v := by
    funext n
    rw [WeilDilationRealness.finiteTypeSeq_eq_vonMangoldt_add (by simp)
      (fun n hn => by simp only [ite_eq_right_iff]; omega)]
    simp [pencil, hβ, hγ]
  rw [he] at hW
  have hδ : WeilBoundaryDilation.HalfSummable (fun n : ℕ => if n = 1 then (1 : ℝ) else 0) := by
    refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
    have : n ≠ 1 := by simpa using hn
    simp [LSeries.term, this]
  have hlog : LSeriesSummable (LSeries.logMul fun n =>
      (((fun n : ℕ => if n = 1 then (1 : ℝ) else 0) n : ℝ) : ℂ)) (1 / 2) := by
    refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
    have : n ≠ 1 := by simpa using hn
    simp [LSeries.term, LSeries.logMul, this]
  exact (WeilBoundaryDilation.eq_vonMangoldt_of_weilPositiveFull_boundary hδ hv hW hlog).2

end RHTower.WeilPencil
