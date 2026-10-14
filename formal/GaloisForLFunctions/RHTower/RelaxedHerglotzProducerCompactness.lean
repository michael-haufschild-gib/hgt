import GaloisForLFunctions.RHTower.HerglotzProducerUniquenessUnconditional
import GaloisForLFunctions.HTGeometry.VitaliConvergence
import GaloisForLFunctions.HTGeometry.ShortBumpMellinSmoothedSums

/-!
# Relaxed Herglotz producers and the Riemann hypothesis

For `σ₀ ∈ ℝ` and a real weight sequence `lam`, call `lam` a **Herglotz producer on `Re s > σ₀`**
(`IsHerglotzProducerOn σ₀ lam`) when its Weil function

`Φ_lam(s) = ½ψ(s/2) − ½ log π + 1/s + 1/(s − 1) − Σ_{n≥2} lam(n) n^{−s}`  (`Re s > 1`)

continues holomorphically to `Re s > σ₀` with nonnegative real part there.  For `σ₀ < 1` this asks
the Dirichlet series of `lam` to carry a simple pole of residue `1` at `s = 1` and nothing else, and
`Re Σ lam(n) n^{−s} ≤ Re(½ψ(s/2) − ½ log π + 1/s + 1/(s − 1))` on the half-plane.  The condition
involves only `lam` and the Gamma function.

**Closedness** (`exists_herglotzProducerOn_of_forall_gt`).  For `0 ≤ σ₀ < 1`, if every half-plane
`Re s > σ₀ + δ` carries a log-bounded producer, so does `Re s > σ₀`.  Its sequential form
(`isHerglotzProducerOn_of_tendsto`): a pointwise limit of log-bounded producers on
`Re s > σ₀ + 1/(k+2)` is a producer on `Re s > σ₀`.

**Theorem** (`riemannHypothesis_iff_forall_herglotzProducerOn`).  RH holds if and only if for every
`δ > 0` some weight sequence with `|lam(n)| ≤ log n` is a Herglotz producer on `Re s > ½ + δ`.

The weights may depend on `δ` and need not be `Λ`.  Under RH every small bounded perturbation of `Λ`
supported at finitely many `n` is a producer on `Re s > ½ + δ`, so the relaxed problems have many
solutions.

Proof of the converse.  The weights live in the compact box `∏ [−log n, log n]`.  Pick
`δ_k = 1/(k + 2)` and pass to a pointwise convergent subsequence `lam_k → lam₀`.  By dominated
convergence `Φ_k → Φ_{lam₀}` on `Re s > 1`.  On each half-plane `Re s > ½ + 1/(m + 2)` the tail of
`Φ_k` is locally bounded by Harnack's inequality for functions with nonnegative real part, centred
two units to the right where `|Φ_k|` is bounded uniformly in `k`.  Vitali's theorem then gives
pointwise convergence on the whole of `Re s > ½`, and the limit is a Herglotz continuation of
`Φ_{lam₀}`.  The uniqueness of Herglotz producers (`herglotzProducer_eq_vonMangoldt`) gives
`lam₀ = Λ` and RH.
-/

open Complex Filter Topology Metric Set

noncomputable section

namespace RHTower.RelaxedHerglotz

open RHTower.AtomDomination GaloisForLFunctions.HTGeometry

/-- `lam` is a **Herglotz producer on `Re s > σ₀`**: its Weil function has a holomorphic
continuation with nonnegative real part to that half-plane. -/
def IsHerglotzProducerOn (σ₀ : ℝ) (lam : ℕ → ℝ) : Prop :=
  ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ {s : ℂ | σ₀ < s.re} ∧
    (∀ s : ℂ, σ₀ < s.re → 0 ≤ (Φ s).re) ∧
    ∀ s : ℂ, 1 < s.re → Φ s = WeilHerglotz.weilFunction lam s

/-- The archimedean part of the Weil function. -/
def archPart (s : ℂ) : ℂ :=
  Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2 + 1 / s + 1 / (s - 1)

theorem weilFunction_eq_archPart_sub (lam : ℕ → ℝ) (s : ℂ) :
    WeilHerglotz.weilFunction lam s = archPart s - LSeries (WeilHerglotz.lamC lam) s := rfl

/-- Producers persist on smaller half-planes. -/
theorem IsHerglotzProducerOn.mono {σ₀ σ₁ : ℝ} {lam : ℕ → ℝ} (h : IsHerglotzProducerOn σ₀ lam)
    (hσ : σ₀ ≤ σ₁) : IsHerglotzProducerOn σ₁ lam := by
  obtain ⟨Φ, hΦd, hΦre, hΦ⟩ := h
  refine ⟨Φ, hΦd.mono fun s hs => ?_, fun s hs => hΦre s (by linarith), hΦ⟩
  simp only [mem_setOf_eq] at hs ⊢
  linarith

/-- `log n ≤ (2/(σ − 1)) n^{(σ−1)/2}`. -/
theorem log_le_rpow_half {σ : ℝ} (hσ : 1 < σ) (n : ℕ) :
    Real.log n ≤ 2 / (σ - 1) * (n : ℝ) ^ ((σ - 1) / 2) := by
  have h := Real.log_le_rpow_div (Nat.cast_nonneg n) (by linarith : 0 < (σ - 1) / 2)
  calc Real.log n ≤ (n : ℝ) ^ ((σ - 1) / 2) / ((σ - 1) / 2) := h
    _ = 2 / (σ - 1) * (n : ℝ) ^ ((σ - 1) / 2) := by field_simp

/-- The dominating sequence `(2/(σ − 1)) n^{−(σ+1)/2}`. -/
def logBound (σ : ℝ) (n : ℕ) : ℝ := 2 / (σ - 1) * (n : ℝ) ^ (-((σ + 1) / 2))

theorem summable_logBound {σ : ℝ} (hσ : 1 < σ) : Summable (logBound σ) :=
  (Real.summable_nat_rpow.mpr (by linarith)).mul_left _

/-- Each term of the `L`-series of a log-bounded weight is dominated by `logBound`. -/
theorem norm_term_lamC_le {lam : ℕ → ℝ} (hlam : ∀ n, |lam n| ≤ Real.log n) {s : ℂ}
    (hs : 1 < s.re) (n : ℕ) :
    ‖LSeries.term (WeilHerglotz.lamC lam) s n‖ ≤ logBound s.re n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [LSeries.term_zero, norm_zero, logBound]
    exact mul_nonneg (div_nonneg (by norm_num) (by linarith))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [LSeries.term_of_ne_zero hn.ne', norm_div, norm_natCast_cpow_of_pos hn]
  have hnum : ‖WeilHerglotz.lamC lam n‖ ≤ Real.log n := by
    unfold WeilHerglotz.lamC
    rw [Complex.norm_real, Real.norm_eq_abs]
    split_ifs
    · exact hlam n
    · rw [abs_zero]; exact Real.log_natCast_nonneg n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : 0 < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos hnpos _
  rw [div_le_iff₀ hpow]
  calc ‖WeilHerglotz.lamC lam n‖ ≤ Real.log n := hnum
    _ ≤ 2 / (s.re - 1) * (n : ℝ) ^ ((s.re - 1) / 2) := log_le_rpow_half hs n
    _ = logBound s.re n * (n : ℝ) ^ s.re := by
        unfold logBound
        rw [mul_assoc, ← Real.rpow_add hnpos]
        congr 2
        ring

theorem norm_LSeries_lamC_le {lam : ℕ → ℝ} (hlam : ∀ n, |lam n| ≤ Real.log n) {s : ℂ}
    (hs : 1 < s.re) :
    ‖LSeries (WeilHerglotz.lamC lam) s‖ ≤ ∑' n, logBound s.re n := by
  unfold LSeries
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact (summable_logBound hs).of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_term_lamC_le hlam hs)
  · exact Summable.tsum_le_tsum (norm_term_lamC_le hlam hs)
      ((summable_logBound hs).of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_lamC_le hlam hs))
      (summable_logBound hs)

/-- The Weil functions of log-bounded weights are bounded at each point of `Re s > 1`, uniformly in
the weights. -/
theorem norm_weilFunction_le_of_log {lam : ℕ → ℝ} (hlam : ∀ n, |lam n| ≤ Real.log n) {s : ℂ}
    (hs : 1 < s.re) :
    ‖WeilHerglotz.weilFunction lam s‖ ≤ ‖archPart s‖ + ∑' n, logBound s.re n := by
  rw [weilFunction_eq_archPart_sub]
  exact (norm_sub_le _ _).trans (by gcongr; exact norm_LSeries_lamC_le hlam hs)

/-- Pointwise convergence of log-bounded weights gives convergence of the Weil functions on
`Re s > 1`. -/
theorem tendsto_weilFunction {lam : ℕ → ℕ → ℝ} {lam₀ : ℕ → ℝ}
    (hlam : ∀ k n, |lam k n| ≤ Real.log n)
    (hlim : ∀ n, Tendsto (fun k => lam k n) atTop (𝓝 (lam₀ n)))
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun k => WeilHerglotz.weilFunction (lam k) s) atTop
      (𝓝 (WeilHerglotz.weilFunction lam₀ s)) := by
  simp_rw [weilFunction_eq_archPart_sub]
  refine tendsto_const_nhds.sub ?_
  unfold LSeries
  refine tendsto_tsum_of_dominated_convergence (summable_logBound hs) (fun n => ?_)
    (Eventually.of_forall fun k n => norm_term_lamC_le (hlam k) hs n)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [LSeries.term_zero]; exact tendsto_const_nhds
  simp only [LSeries.term_of_ne_zero hn.ne', WeilHerglotz.lamC]
  refine Tendsto.div_const ?_ _
  refine Complex.continuous_ofReal.continuousAt.tendsto.comp ?_
  split_ifs
  · exact hlim n
  · exact tendsto_const_nhds

/-- Log-bounded weights satisfy the summability hypothesis of the Herglotz bridge. -/
theorem summable_abs_div_rpow_of_log {lam : ℕ → ℝ} (hlam : ∀ n, |lam n| ≤ Real.log n) {σ : ℝ}
    (hσ : 1 < σ) : Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (summable_logBound hσ)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, Real.zero_rpow (by linarith), div_zero]
    exact mul_nonneg (div_nonneg (by norm_num) (by linarith))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hnpos _)]
  calc |lam n| ≤ Real.log n := hlam n
    _ ≤ 2 / (σ - 1) * (n : ℝ) ^ ((σ - 1) / 2) := log_le_rpow_half hσ n
    _ = logBound σ n * (n : ℝ) ^ σ := by
        unfold logBound
        rw [mul_assoc, ← Real.rpow_add hnpos]
        congr 2
        ring

/-- **Harnack's bound.**  A holomorphic function with nonnegative real part on a ball is bounded at
`w` by `(1 + 2|w − c|/(R − |w − c|))` times its modulus at the centre. -/
theorem norm_le_of_re_nonneg_on_ball {f : ℂ → ℂ} {c w : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (ball c R)) (hre : ∀ v ∈ ball c R, 0 ≤ (f v).re)
    (hw : w ∈ ball c R) :
    ‖f w‖ ≤ (1 + 2 * ‖w - c‖ / (R - ‖w - c‖)) * ‖f c‖ := by
  have h := norm_sub_le_of_re_nonneg_on_ball hf hre hw
  have hwr : ‖w - c‖ < R := mem_ball_iff_norm.mp hw
  have hfac : 0 ≤ 2 * ‖w - c‖ / (R - ‖w - c‖) :=
    div_nonneg (by positivity) (by linarith)
  have h1 : ‖f w‖ ≤ ‖f c‖ + 2 * ‖w - c‖ / (R - ‖w - c‖) * (f c).re := by
    have := norm_sub_norm_le (f w) (f c); linarith
  have h2 : 2 * ‖w - c‖ / (R - ‖w - c‖) * (f c).re ≤ 2 * ‖w - c‖ / (R - ‖w - c‖) * ‖f c‖ :=
    mul_le_mul_of_nonneg_left (Complex.re_le_norm _) hfac
  linarith

/-- A ball centred at `c` of radius `Re c − a` lies in `Re s > a`. -/
theorem ball_subset_halfPlane {c : ℂ} {a : ℝ} : ball c (c.re - a) ⊆ {s : ℂ | a < s.re} := by
  intro v hv
  rw [mem_ball, dist_eq_norm] at hv
  have := Complex.abs_re_le_norm (v - c)
  rw [Complex.sub_re] at this
  have := (abs_lt.mp (lt_of_le_of_lt this hv)).1
  simp only [mem_setOf_eq]
  linarith

theorem isPreconnected_halfPlane (a : ℝ) : IsPreconnected {s : ℂ | a < s.re} :=
  (convex_halfSpace_re_gt a).isPreconnected

theorem isOpen_halfPlane (a : ℝ) : IsOpen {s : ℂ | a < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

/-- **Sequential closedness of producer levels.** -/
theorem isHerglotzProducerOn_of_tendsto {σ₀ : ℝ} (h0 : 0 ≤ σ₀) (h1 : σ₀ < 1)
    {lamk : ℕ → ℕ → ℝ} {lam₀ : ℕ → ℝ} (hlamk : ∀ k n, |lamk k n| ≤ Real.log n)
    (hprod : ∀ k : ℕ, IsHerglotzProducerOn (σ₀ + 1 / ((k : ℝ) + 2)) (lamk k))
    (hlimn : ∀ n, Tendsto (fun k => lamk k n) atTop (𝓝 (lam₀ n))) :
    IsHerglotzProducerOn σ₀ lam₀ := by
  choose F hFd hFre hFeq using hprod
  have hlev : ∀ m k : ℕ, m ≤ k → σ₀ + 1 / ((k : ℝ) + 2) ≤ σ₀ + 1 / ((m : ℝ) + 2) := by
    intro m k hmk
    have h1 : (m : ℝ) ≤ k := by exact_mod_cast hmk
    have : 1 / ((k : ℝ) + 2) ≤ 1 / ((m : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have hconv1 : ∀ s : ℂ, 1 < s.re →
      Tendsto (fun k => F k s) atTop (𝓝 (WeilHerglotz.weilFunction lam₀ s)) := by
    intro s hs
    exact (tendsto_weilFunction hlamk hlimn hs).congr fun k => (hFeq k s hs).symm
  have hvit : ∀ m : ℕ, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | σ₀ + 1 / ((m : ℝ) + 2) < s.re}
      ∧ ∀ z : ℂ, σ₀ + 1 / ((m : ℝ) + 2) < z.re →
        Tendsto (fun k => F (k + m) z) atTop (𝓝 (G z)) := by
    intro m
    set a : ℝ := σ₀ + 1 / ((m : ℝ) + 2) with ha
    have ha1 : a < 2 := by
      have : 1 / ((m : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by
        have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith)
      linarith [h1]
    have hdiff : ∀ k, DifferentiableOn ℂ (F (k + m)) {s : ℂ | a < s.re} := fun k =>
      (hFd (k + m)).mono fun s hs => by
        simp only [mem_setOf_eq] at hs ⊢
        have := hlev m (k + m) (by omega)
        linarith
    have hre : ∀ k, ∀ s : ℂ, a < s.re → 0 ≤ (F (k + m) s).re := fun k s hs =>
      hFre (k + m) s (by have := hlev m (k + m) (by omega); linarith)
    have hloc : ∀ z ∈ {s : ℂ | a < s.re}, ∃ R : ℝ, 0 < R ∧ ball z R ⊆ {s : ℂ | a < s.re} ∧
        ∃ C : ℝ, ∀ k, ∀ w ∈ ball z R, ‖F (k + m) w‖ ≤ C := by
      intro z hz
      simp only [mem_setOf_eq] at hz
      set r : ℝ := (z.re - a) / 4 with hr
      have hr0 : 0 < r := by rw [hr]; linarith
      set c : ℂ := z + 2 with hc
      have hcre : c.re = z.re + 2 := by rw [hc]; simp
      have ha0 : 0 < a := by
        have : 0 < 1 / ((m : ℝ) + 2) := by positivity
        rw [ha]; linarith
      have hc1 : 1 < c.re := by rw [hcre]; linarith
      refine ⟨r, hr0, fun w hw => ?_, ?_⟩
      · rw [mem_ball, dist_eq_norm] at hw
        have := Complex.abs_re_le_norm (w - z)
        rw [Complex.sub_re] at this
        have := (abs_lt.mp (lt_of_le_of_lt this hw)).1
        simp only [mem_setOf_eq]
        linarith
      set B : ℝ := ‖archPart c‖ + ∑' n, logBound c.re n with hB
      refine ⟨(1 + 2 * (r + 2) / (3 * r)) * B, fun k w hw => ?_⟩
      have hball : ball c (c.re - a) ⊆ {s : ℂ | a < s.re} := ball_subset_halfPlane
      have hwc : ‖w - c‖ < r + 2 := by
        rw [mem_ball, dist_eq_norm] at hw
        have hzc : ‖z - c‖ = 2 := by rw [hc]; simp
        calc ‖w - c‖ ≤ ‖w - z‖ + ‖z - c‖ := norm_sub_le_norm_sub_add_norm_sub w z c
          _ < r + 2 := by rw [hzc]; linarith
      have hRw : 3 * r ≤ (c.re - a) - ‖w - c‖ := by
        rw [hcre]; rw [hr] at hwc ⊢; linarith
      have hwball : w ∈ ball c (c.re - a) := by
        rw [mem_ball, dist_eq_norm]; linarith
      have hH := norm_le_of_re_nonneg_on_ball ((hdiff k).mono hball)
        (fun v hv => hre k v (hball hv)) hwball
      have hFc : ‖F (k + m) c‖ ≤ B := by
        rw [hFeq (k + m) c hc1]
        exact norm_weilFunction_le_of_log (hlamk _) hc1
      have hfac : 2 * ‖w - c‖ / ((c.re - a) - ‖w - c‖) ≤ 2 * (r + 2) / (3 * r) :=
        div_le_div₀ (by positivity) (by linarith) (by positivity) hRw
      calc ‖F (k + m) w‖ ≤ (1 + 2 * ‖w - c‖ / ((c.re - a) - ‖w - c‖)) * ‖F (k + m) c‖ := hH
        _ ≤ (1 + 2 * (r + 2) / (3 * r)) * B := by gcongr
    have hY : ∀ z ∈ {s : ℂ | 2 < s.re}, ∃ Lz : ℂ, Tendsto (fun k => F (k + m) z) atTop (𝓝 Lz) :=
      fun z hz => ⟨_, (tendsto_add_atTop_iff_nat m).mpr (hconv1 z (by
        simp only [mem_setOf_eq] at hz; linarith))⟩
    have hacc : ∃ᶠ z in 𝓝[≠] (3 : ℂ), z ∈ {s : ℂ | 2 < s.re} := by
      have hopen : {s : ℂ | 2 < s.re} ∈ 𝓝 (3 : ℂ) :=
        (isOpen_halfPlane 2).mem_nhds (by simp; norm_num)
      exact Filter.Eventually.frequently (mem_nhdsWithin_of_mem_nhds hopen)
    obtain ⟨G, hGd, hGlim⟩ := vitali_tendstoLocallyUniformlyOn_of_isPreconnected
      (isPreconnected_halfPlane a) hdiff hloc (by simp; linarith) hacc hY
    exact ⟨G, hGd, fun z hz => hGlim.tendsto_at hz⟩
  choose G hGd hGlim using hvit
  have hlevel : ∀ z : ℂ, σ₀ < z.re → ∃ m : ℕ, σ₀ + 1 / ((m : ℝ) + 2) < z.re := by
    intro z hz
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (by linarith : (0 : ℝ) < z.re - σ₀)
    refine ⟨m, ?_⟩
    have : 1 / ((m : ℝ) + 2) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  set Ψ : ℂ → ℂ := fun z => limUnder atTop fun k => F k z with hΨ
  have hΨlim : ∀ (m : ℕ) (z : ℂ), σ₀ + 1 / ((m : ℝ) + 2) < z.re →
      Tendsto (fun k => F k z) atTop (𝓝 (G m z)) :=
    fun m z hz => (tendsto_add_atTop_iff_nat m).mp (hGlim m z hz)
  have hΨeqG : ∀ (m : ℕ) (z : ℂ), σ₀ + 1 / ((m : ℝ) + 2) < z.re → Ψ z = G m z :=
    fun m z hz => (hΨlim m z hz).limUnder_eq
  refine ⟨Ψ, ?_, ?_, ?_⟩
  · intro z hz
    simp only [mem_setOf_eq] at hz
    obtain ⟨m, hm⟩ := hlevel z hz
    have hopen : {s : ℂ | σ₀ + 1 / ((m : ℝ) + 2) < s.re} ∈ 𝓝 z :=
      (isOpen_halfPlane _).mem_nhds hm
    have heq : G m =ᶠ[𝓝 z] Ψ := Filter.eventually_of_mem hopen fun w hw => (hΨeqG m w hw).symm
    exact (((hGd m).differentiableAt hopen).congr_of_eventuallyEq heq.symm).differentiableWithinAt
  · intro z hz
    obtain ⟨m, hm⟩ := hlevel z hz
    have hlimre := (Complex.continuous_re.tendsto _).comp (hΨlim m z hm)
    rw [hΨeqG m z hm]
    refine ge_of_tendsto hlimre (eventually_atTop.mpr ⟨m, fun k hk => ?_⟩)
    simp only [Function.comp_apply]
    exact hFre k z (by have := hlev m k hk; linarith)
  · intro s hs
    exact (hconv1 s hs).limUnder_eq

/-- **The producer levels form a closed set.**  If every half-plane `Re s > σ₀ + δ` (`δ > 0`)
carries a Herglotz producer with `|lam(n)| ≤ log n`, so does `Re s > σ₀` (for `0 ≤ σ₀ < 1`). -/
theorem exists_herglotzProducerOn_of_forall_gt {σ₀ : ℝ} (h0 : 0 ≤ σ₀) (h1 : σ₀ < 1)
    (h : ∀ δ : ℝ, 0 < δ → ∃ lam : ℕ → ℝ, (∀ n, |lam n| ≤ Real.log n) ∧
      IsHerglotzProducerOn (σ₀ + δ) lam) :
    ∃ lam : ℕ → ℝ, (∀ n, |lam n| ≤ Real.log n) ∧ IsHerglotzProducerOn σ₀ lam := by
  choose lamk hlamk hprod using fun k : ℕ => h (1 / ((k : ℝ) + 2)) (by positivity)
  set K : Set (ℕ → ℝ) := univ.pi fun n => Icc (-Real.log n) (Real.log n) with hKdef
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ k, lamk k ∈ K := fun k => mem_univ_pi.mpr fun n => abs_le.mp (hlamk k n)
  obtain ⟨lam₀, hlam₀K, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hlam₀ : ∀ n, |lam₀ n| ≤ Real.log n := fun n => abs_le.mpr (mem_univ_pi.mp hlam₀K n)
  have hlimn : ∀ n, Tendsto (fun k => lamk (φ k) n) atTop (𝓝 (lam₀ n)) :=
    fun n => (continuous_apply n).continuousAt.tendsto.comp hlim
  have hprodφ : ∀ k : ℕ, IsHerglotzProducerOn (σ₀ + 1 / ((k : ℝ) + 2)) (lamk (φ k)) := by
    intro k
    refine (hprod (φ k)).mono ?_
    have h1' : (k : ℝ) ≤ φ k := by exact_mod_cast hφ.id_le k
    have : 1 / ((φ k : ℝ) + 2) ≤ 1 / ((k : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  exact ⟨lam₀, hlam₀, isHerglotzProducerOn_of_tendsto h0 h1 (fun k n => hlamk (φ k) n) hprodφ
    hlimn⟩

/-- **Relaxed producers at every level force RH.** -/
theorem riemannHypothesis_of_forall_herglotzProducerOn
    (h : ∀ δ : ℝ, 0 < δ → ∃ lam : ℕ → ℝ, (∀ n, |lam n| ≤ Real.log n) ∧
      IsHerglotzProducerOn (1 / 2 + δ) lam) :
    RiemannHypothesis := by
  obtain ⟨lam, hlam, Φ, hΦd, hΦre, hΦ⟩ :=
    exists_herglotzProducerOn_of_forall_gt (by norm_num) (by norm_num) h
  exact (herglotzProducer_eq_vonMangoldt (fun σ hσ => summable_abs_div_rpow_of_log hlam hσ)
    hΦd hΦre hΦ).1

/-- The von Mangoldt weights are a Herglotz producer on every half-plane `Re s > ½ + δ` under RH. -/
theorem herglotzProducerOn_vonMangoldt (hRH : RiemannHypothesis) {σ₀ : ℝ} (hσ₀ : 1 / 2 ≤ σ₀) :
    IsHerglotzProducerOn σ₀ fun n => (ArithmeticFunction.vonMangoldt n : ℝ) := by
  obtain ⟨lam, hsl, Φ, hΦd, hΦre, hΦ⟩ := riemannHypothesis_iff_exists_herglotzProducer.mp hRH
  have heq := (herglotzProducer_eq_vonMangoldt hsl hΦd hΦre hΦ).2
  have hfun : WeilHerglotz.lamC lam =
      WeilHerglotz.lamC fun n => ArithmeticFunction.vonMangoldt n := by
    funext n
    unfold WeilHerglotz.lamC
    split_ifs with hn
    · rw [heq n hn]
    · rfl
  refine ⟨Φ, hΦd.mono fun s hs => ?_, fun s hs => hΦre s (by linarith), fun s hs => ?_⟩
  · simp only [mem_setOf_eq] at hs ⊢; linarith
  · rw [hΦ s hs]
    unfold WeilHerglotz.weilFunction
    rw [hfun]

/-- **RH is the existence of relaxed producers at every level.**  The Riemann hypothesis holds if
and only if for every `δ > 0` some weight sequence with `|lam(n)| ≤ log n` is a Herglotz producer on
`Re s > ½ + δ`. -/
theorem riemannHypothesis_iff_forall_herglotzProducerOn :
    RiemannHypothesis ↔ ∀ δ : ℝ, 0 < δ → ∃ lam : ℕ → ℝ, (∀ n, |lam n| ≤ Real.log n) ∧
      IsHerglotzProducerOn (1 / 2 + δ) lam := by
  refine ⟨fun hRH δ hδ => ⟨fun n => ArithmeticFunction.vonMangoldt n, fun n => ?_,
    herglotzProducerOn_vonMangoldt hRH (by linarith)⟩,
    riemannHypothesis_of_forall_herglotzProducerOn⟩
  rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact ArithmeticFunction.vonMangoldt_le_log

end RHTower.RelaxedHerglotz
