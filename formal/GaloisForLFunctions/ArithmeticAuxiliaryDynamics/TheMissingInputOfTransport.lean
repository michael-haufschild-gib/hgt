import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheHurwitzLimitSetEmbedsInTheGaugeTorus
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheZerosOfAnExponentialPolynomialRecur
import GaloisForLFunctions.RHTower.HardyZ
import GaloisForLFunctions.RHTower.PrimeShiftResidueClosability
import GaloisForLFunctions.RHTower.ZetaRealStrip
import GaloisForLFunctions.RHTower.ZetaWeakRecurrenceLadderCollapse

/-!
# The missing input of transport

Sequences `τ_j → ∞` with `n^{-iτ_j} → 1` for every `n` always exist, by Kronecker. On `Re s > 1` their translates converge to `ζ`.
Everything that blocks transport is therefore one bound.

**Suppose the translates are bounded on a connected open set `U` in the upper half-plane that joins a zero `ρ` to `Re s > 1`.** By
Vitali and the identity theorem they converge to `ζ` locally uniformly on `U`, by Rouché each translate carries a zero near `ρ`, and so
infinitely many zeros lie right of `Re ρ − r`, for every `r > 0`.

So in a world with finitely many zeros right of `½ + h`, **every phase return sequence has unbounded translates on every connected
domain joining a zero right of `½ + h` to `Re s > 1`**. Conversely, one bounded phase return at each zero gives the asymptotic abscissa
law. This is the exact form of the input that transport lacks. It says nothing about the primes, whose phases return freely: it is a
statement about the size of `ζ` along a return.
-/

open Complex Filter Metric Set Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- A sequence along which every prime phase returns. -/
structure IsPhaseReturn (τ : ℕ → ℝ) : Prop where
  nonneg : ∀ j, 0 ≤ τ j
  tendsto : Tendsto τ atTop atTop
  phase : ∀ n, Tendsto (fun j => phaseDefect τ j n) atTop (𝓝 0)

/-- The translates along `τ` are locally bounded on `U`. -/
def TranslatesBoundedOn (τ : ℕ → ℝ) (U : Set ℂ) : Prop :=
  ∀ z ∈ U, ∃ R : ℝ, 0 < R ∧ ball z R ⊆ U ∧ ∃ C : ℝ,
    ∀ j, ∀ w ∈ ball z R, ‖riemannZeta (w + (τ j : ℂ) * I)‖ ≤ C

private lemma phaseDefect_eq (τ : ℕ → ℝ) (j n : ℕ) :
    phaseDefect τ j n = exp (((-Real.log ((n : ℝ) + 1) * τ j : ℝ) : ℂ) * I) - 1 := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hne : (((n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [phaseDefect, cpow_def_of_ne_zero hne, ← ofReal_log hpos.le]
  congr 2
  push_cast
  ring

/-- **Phase returns exist.** -/
theorem exists_isPhaseReturn : ∃ τ : ℕ → ℝ, IsPhaseReturn τ := by
  have hstep : ∀ j : ℕ, ∃ τ > (j : ℝ), ∀ i : Fin (j + 1),
      ‖exp ((((-Real.log (((i : ℕ) : ℝ) + 1)) * τ : ℝ) : ℂ) * I) - 1‖ < 1 / ((j : ℝ) + 1) := fun j =>
    ArithmeticCastelnuovoSeveri.exists_large_almost_period
      (fun i : Fin (j + 1) => -Real.log (((i : ℕ) : ℝ) + 1)) (by positivity) (j : ℝ)
  choose τ hτ hclose using hstep
  have hτ0 : ∀ j, 0 ≤ τ j := fun j => (Nat.cast_nonneg j).trans (hτ j).le
  refine ⟨τ, ⟨hτ0, ?_, fun n => ?_⟩⟩
  · exact tendsto_atTop_mono (fun j => (hτ j).le) tendsto_natCast_atTop_atTop
  · refine squeeze_zero_norm' ?_ (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    filter_upwards [eventually_ge_atTop n] with j hj
    rw [phaseDefect_eq]
    exact (hclose j ⟨n, by omega⟩).le

/-- A phase return converges to `ζ` on `Re s > 1`. -/
theorem IsPhaseReturn.tendsto_of_one_lt_re {τ : ℕ → ℝ} (h : IsPhaseReturn τ) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun j => riemannZeta (s + (τ j : ℂ) * I)) atTop (𝓝 (riemannZeta s)) := by
  have hdom := summable_norm_zetaTerm hs
  have hlim : Tendsto (fun j => ∑' n, zetaTerm s n * phaseDefect τ j n) atTop (𝓝 (∑' _n : ℕ, (0 : ℂ))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun n => ‖zetaTerm s n‖ * 2)
      (hdom.mul_right 2) (fun n => ?_) (Eventually.of_forall fun j n => ?_)
    · have := (h.phase n).const_mul (zetaTerm s n)
      simpa using this
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_phaseDefect_le τ j n) (norm_nonneg _)
  rw [tsum_zero] at hlim
  have hval : ∀ j, ∑' n, zetaTerm s n * phaseDefect τ j n = translateDiff τ j s := fun j =>
    (hasSum_translateDiff τ j hs).tsum_eq
  simp only [hval] at hlim
  have := hlim.add_const (riemannZeta s)
  simp only [translateDiff, sub_add_cancel, zero_add] at this
  exact this

/-- **Propagation from the right.** Bounded translates along a phase return converge to `ζ` locally uniformly on a connected open set in
the upper half-plane that meets `Re s > 1`. -/
theorem IsPhaseReturn.tendstoLocallyUniformlyOn {τ : ℕ → ℝ} (h : IsPhaseReturn τ) {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUim : ∀ z ∈ U, 0 < z.im) {s₀ : ℂ} (hs₀ : s₀ ∈ U) (hs₀1 : 1 < s₀.re)
    (hbd : TranslatesBoundedOn τ U) :
    TendstoLocallyUniformlyOn (fun j s => riemannZeta (s + (τ j : ℂ) * I)) riemannZeta atTop U := by
  have hne1 : ∀ z ∈ U, z ≠ 1 := fun z hz hz1 => by
    have := hUim z hz
    rw [hz1] at this
    simp at this
  have hne2 : ∀ j, ∀ z ∈ U, z + (τ j : ℂ) * I ≠ 1 := by
    intro j z hz hz1
    have him : (z + (τ j : ℂ) * I).im = 1 * 0 := by rw [hz1]; simp
    have : (z + (τ j : ℂ) * I).im = z.im + τ j := by simp
    have h1 := hUim z hz
    have h2 := h.nonneg j
    linarith
  have hdiff : ∀ j, DifferentiableOn ℂ (fun s => riemannZeta (s + (τ j : ℂ) * I)) U := by
    intro j z hz
    exact ((differentiableAt_riemannZeta (hne2 j z hz)).comp z
      (differentiableAt_id.add_const _)).differentiableWithinAt
  have hYo : IsOpen {z | z ∈ U ∧ 1 < z.re} := hUo.inter (isOpen_lt continuous_const continuous_re)
  have hYnhds : {z | z ∈ U ∧ 1 < z.re} ∈ 𝓝 s₀ := hYo.mem_nhds ⟨hs₀, hs₀1⟩
  have hacc : ∃ᶠ z in 𝓝[≠] s₀, z ∈ {z | z ∈ U ∧ 1 < z.re} := by
    have hev : ∀ᶠ z in 𝓝[≠] s₀, z ∈ {z | z ∈ U ∧ 1 < z.re} := nhdsWithin_le_nhds hYnhds
    exact hev.frequently
  obtain ⟨G, hGd, hG⟩ := HTGeometry.vitali_tendstoLocallyUniformlyOn_of_isPreconnected hUc hdiff hbd hs₀ hacc
    fun z hz => ⟨_, h.tendsto_of_one_lt_re hz.2⟩
  have hGeq : ∀ z ∈ {z | z ∈ U ∧ 1 < z.re}, G z = riemannZeta z := fun z hz =>
    tendsto_nhds_unique (hG.tendsto_at hz.1) (h.tendsto_of_one_lt_re hz.2)
  have hGana : AnalyticOnNhd ℂ G U := hGd.analyticOnNhd hUo
  have hζana : AnalyticOnNhd ℂ riemannZeta U := by
    have : DifferentiableOn ℂ riemannZeta U := fun z hz =>
      (differentiableAt_riemannZeta (hne1 z hz)).differentiableWithinAt
    exact this.analyticOnNhd hUo
  have hev : G =ᶠ[𝓝 s₀] riemannZeta := Filter.eventually_of_mem hYnhds hGeq
  exact hG.congr_right (hGana.eqOn_of_preconnected_of_eventuallyEq hζana hUc hs₀ hev)

/-- An isolating circle at a zero, inside a prescribed neighbourhood. -/
theorem exists_isolating_circle {ρ : ℂ} (hρ1 : ρ ≠ 1) (hρ : riemannZeta ρ = 0) {U : Set ℂ}
    (hU : U ∈ 𝓝 ρ) {r : ℝ} (hr : 0 < r) :
    ∃ r' m : ℝ, 0 < r' ∧ r' < r ∧ closedBall ρ r' ⊆ U ∧ 0 < m ∧ ∀ z ∈ sphere ρ r', m ≤ ‖riemannZeta z‖ := by
  have hana : AnalyticAt ℂ riemannZeta ρ :=
    DifferentiableOn.analyticAt (s := {1}ᶜ)
      (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
      (isOpen_compl_singleton.mem_nhds hρ1)
  have hne : ∀ᶠ z in 𝓝[≠] ρ, riemannZeta z ≠ 0 := by
    rcases hana.eventually_eq_zero_or_eventually_ne_zero with h0 | h0
    · exfalso
      exact RHTower.analyticOrderAt_riemannZeta_ne_top hρ1 (analyticOrderAt_eq_top.mpr h0)
    · exact h0
  rw [eventually_nhdsWithin_iff] at hne
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hne
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hU
  have hd1 : 0 < dist ρ 1 := dist_pos.mpr hρ1
  obtain ⟨r', hr'def⟩ : ∃ r', r' = min (min ε δ) (min r (dist ρ 1)) / 2 := ⟨_, rfl⟩
  have hmin : 0 < min (min ε δ) (min r (dist ρ 1)) := lt_min (lt_min hε hδ) (lt_min hr hd1)
  have hr'0 : 0 < r' := by rw [hr'def]; linarith
  have hr'lt : r' < min (min ε δ) (min r (dist ρ 1)) := by rw [hr'def]; linarith
  have h1 : r' < ε := hr'lt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : r' < δ := hr'lt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : r' < r := hr'lt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : r' < dist ρ 1 := hr'lt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hsph : ∀ z ∈ sphere ρ r', riemannZeta z ≠ 0 := by
    intro z hz
    have hd : dist z ρ = r' := mem_sphere.mp hz
    refine hball z (mem_ball.mpr (by rw [hd]; exact h1)) ?_
    intro hzρ
    rw [mem_singleton_iff] at hzρ
    rw [hzρ, dist_self] at hd
    linarith
  have hcont : ContinuousOn (fun z => ‖riemannZeta z‖) (sphere ρ r') := by
    intro z hz
    have hz1 : z ≠ 1 := by
      intro hz1
      have hd : dist z ρ = r' := mem_sphere.mp hz
      rw [hz1, dist_comm] at hd
      linarith
    exact (differentiableAt_riemannZeta hz1).continuousAt.norm.continuousWithinAt
  obtain ⟨z₀, hz₀, hmin₀⟩ := (isCompact_sphere ρ r').exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr'0.le) hcont
  refine ⟨r', ‖riemannZeta z₀‖, hr'0, h3, ?_, norm_pos_iff.mpr (hsph z₀ hz₀), fun z hz => hmin₀ hz⟩
  exact (closedBall_subset_ball h2).trans hδU

/-- **Transport.** Along a bounded phase return, each translate eventually carries a zero near a zero of `ζ`. -/
theorem IsPhaseReturn.eventually_exists_zero {τ : ℕ → ℝ} (h : IsPhaseReturn τ) {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUim : ∀ z ∈ U, 0 < z.im) {s₀ : ℂ} (hs₀ : s₀ ∈ U) (hs₀1 : 1 < s₀.re)
    (hbd : TranslatesBoundedOn τ U) {ρ : ℂ} (hρU : ρ ∈ U) (hρ : riemannZeta ρ = 0) (hρ1 : ρ.re < 1)
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ j in atTop, ∃ z ∈ ball ρ r, riemannZeta (z + (τ j : ℂ) * I) = 0 := by
  have hρne : ρ ≠ 1 := fun hρ' => by
    rw [hρ'] at hρ1
    simp at hρ1
  have hU' : U ∩ {z | z.re < 1} ∈ 𝓝 ρ :=
    (hUo.inter (isOpen_lt continuous_re continuous_const)).mem_nhds ⟨hρU, hρ1⟩
  obtain ⟨r', m, hr', hr'r, hsub, hm, hsph⟩ := exists_isolating_circle hρne hρ hU' hr
  have hloc := h.tendstoLocallyUniformlyOn hUo hUc hUim hs₀ hs₀1 hbd
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hUo).mp hloc (closedBall ρ r')
    (hsub.trans inter_subset_left) (isCompact_closedBall ρ r')
  have hev := Metric.tendstoUniformlyOn_iff.mp hunif (m / 2) (half_pos hm)
  filter_upwards [hev] with j hj
  have hτ : τ j ∈ RHTower.zetaReturnSet (closedBall ρ r') (m / 2) := by
    intro s hs
    have := hj s hs
    rwa [dist_comm, dist_eq_norm] at this
  obtain ⟨z, hz, hzero⟩ := RHTower.exists_zero_of_mem_zetaReturnSet hr'
    (fun s hs => (hsub hs).2) hρ hsph hτ
  exact ⟨z, ball_subset_ball hr'r.le hz, hzero⟩

/-- **A bounded phase return at a zero gives infinitely many zeros** right of `Re ρ − r`, for every `r > 0`. -/
theorem IsPhaseReturn.infinite_zeros {τ : ℕ → ℝ} (h : IsPhaseReturn τ) {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUim : ∀ z ∈ U, 0 < z.im) {s₀ : ℂ} (hs₀ : s₀ ∈ U) (hs₀1 : 1 < s₀.re)
    (hbd : TranslatesBoundedOn τ U) {ρ : ℂ} (hρU : ρ ∈ U) (hρ : riemannZeta ρ = 0) (hρ1 : ρ.re < 1)
    {r : ℝ} (hr : 0 < r) : {w : ℂ | riemannZeta w = 0 ∧ ρ.re - r < w.re}.Infinite := by
  intro hfin
  obtain ⟨H, hH⟩ := (hfin.image Complex.im).bddAbove
  have hlarge : ∀ᶠ j in atTop, H - (ρ.im - r) < τ j := h.tendsto.eventually_gt_atTop _
  obtain ⟨j, ⟨z, hz, hzero⟩, hj⟩ := ((h.eventually_exists_zero hUo hUc hUim hs₀ hs₀1 hbd hρU hρ hρ1 hr).and hlarge).exists
  have hzb : ‖z - ρ‖ < r := by
    rw [mem_ball, dist_eq_norm] at hz
    exact hz
  have hre : |z.re - ρ.re| < r := by
    have := Complex.abs_re_le_norm (z - ρ)
    rw [Complex.sub_re] at this
    linarith
  have him : |z.im - ρ.im| < r := by
    have := Complex.abs_im_le_norm (z - ρ)
    rw [Complex.sub_im] at this
    linarith
  have hwre : (z + (τ j : ℂ) * I).re = z.re := by simp
  have hwim : (z + (τ j : ℂ) * I).im = z.im + τ j := by simp
  have hmem : z + (τ j : ℂ) * I ∈ {w : ℂ | riemannZeta w = 0 ∧ ρ.re - r < w.re} :=
    ⟨hzero, by rw [hwre]; linarith [(abs_lt.mp hre).1]⟩
  have hle := hH ⟨_, hmem, rfl⟩
  rw [hwim] at hle
  linarith [(abs_lt.mp him).1]

/-- **The exact obstruction.** With finitely many zeros right of `σ`, every phase return has unbounded translates on every connected
domain joining a zero right of `σ` to `Re s > 1`. -/
theorem not_translatesBoundedOn_of_finite {σ : ℝ} (hfin : {w : ℂ | riemannZeta w = 0 ∧ σ < w.re}.Finite)
    {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hσ : σ < ρ.re) (hρ1 : ρ.re < 1) {τ : ℕ → ℝ} (h : IsPhaseReturn τ)
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUim : ∀ z ∈ U, 0 < z.im) {s₀ : ℂ} (hs₀ : s₀ ∈ U)
    (hs₀1 : 1 < s₀.re) (hρU : ρ ∈ U) : ¬ TranslatesBoundedOn τ U := by
  intro hbd
  have hr : 0 < ρ.re - σ := by linarith
  have hinf := h.infinite_zeros hUo hUc hUim hs₀ hs₀1 hbd hρU hρ hρ1 hr
  have hset : ρ.re - (ρ.re - σ) = σ := by ring
  rw [hset] at hinf
  exact hinf hfin

/-- **Bounded phase returns give the asymptotic abscissa law.** If each zero right of `½` in the upper half-plane has a phase return with
translates bounded on a connected domain joining it to `Re s > 1`, then finitely many zeros right of `½ + h` forces none. -/
theorem asymptoticAbscissaLaw_of_boundedReturns
    (hB : ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re → ρ.re < 1 → 0 < ρ.im →
      ∃ (τ : ℕ → ℝ) (U : Set ℂ) (s₀ : ℂ), IsPhaseReturn τ ∧ IsOpen U ∧ IsPreconnected U ∧
        (∀ z ∈ U, 0 < z.im) ∧ ρ ∈ U ∧ s₀ ∈ U ∧ 1 < s₀.re ∧ TranslatesBoundedOn τ U) :
    RHTower.AsymptoticAbscissaLaw := by
  intro h hh hF q₀
  by_contra hlt
  push Not at hlt
  have hρ1 := RHTower.xiZeroCopy_re_lt_one q₀
  have hne1 : (q₀.1 : ℂ) ≠ 1 := by
    intro h1
    rw [h1, one_re] at hρ1
    exact lt_irrefl 1 hρ1
  have hζ : riemannZeta (q₀.1 : ℂ) = 0 :=
    (RHTower.xi_eq_zero_iff (by linarith) hne1).mp (RHTower.xi_xiZeroCopy_eq_zero q₀)
  -- Reflect into the upper half-plane.
  obtain ⟨ρ, hρ, hρre, hρim⟩ : ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.re = (q₀.1 : ℂ).re ∧ 0 < ρ.im := by
    rcases lt_trichotomy (q₀.1 : ℂ).im 0 with him | him | him
    · refine ⟨(starRingEnd ℂ) (q₀.1 : ℂ), ?_, by simp, by simpa using him⟩
      exact (RHTower.riemannZeta_conj_eq_zero_iff_of_re_pos (by linarith) hne1).mpr hζ
    · exfalso
      have hreal : (q₀.1 : ℂ) = (((q₀.1 : ℂ).re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [him]
      rw [hreal] at hζ
      exact RHTower.riemannZeta_real_strip_ne_zero (by linarith) hρ1 hζ
    · exact ⟨_, hζ, rfl, him⟩
  obtain ⟨τ, U, s₀, hτ, hUo, hUc, hUim, hρU, hs₀, hs₀1, hbd⟩ :=
    hB ρ hρ (by rw [hρre]; linarith) (by rw [hρre]; exact hρ1) hρim
  have hr : 0 < ρ.re - (1 / 2 + h) := by rw [hρre]; linarith
  have hinf := hτ.infinite_zeros hUo hUc hUim hs₀ hs₀1 hbd hρU hρ (by rw [hρre]; exact hρ1) hr
  have hset : ρ.re - (ρ.re - (1 / 2 + h)) = 1 / 2 + h := by ring
  rw [hset] at hinf
  refine hinf ((hF.image fun q => (q.1 : ℂ)).subset ?_)
  rintro w ⟨hw0, hwre⟩
  have hwre1 : w.re < 1 := by
    by_contra hge
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hw0
  obtain ⟨q, hq⟩ := RHTower.exists_xiZeroCopy_of_zeta_eq_zero_strip hw0 (by linarith) hwre1
  exact ⟨q, by
    show 1 / 2 + h < (q.1 : ℂ).re
    rw [hq]
    exact hwre, hq⟩

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
