import Mathlib

/-!
# The residue of `-ζ'/ζ` at the pole `s = 1`

The logarithmic derivative of the Riemann zeta function has a simple pole at `s = 1` with residue
`-1`; equivalently `-ζ'/ζ` has residue `+1`, i.e. `(s-1)·(-ζ'/ζ)(s) → 1` as `s → 1`.

This is obtained from Riemann's removable-singularity theorem: `G(s) = (s-1)·ζ(s)` extends analytically
across `s = 1` with `G(1) = 1` (this is `riemannZeta_residue_one`), so near `1` one has
`ζ = G/(s-1)` and hence `ζ'/ζ = G'/G - 1/(s-1)`.  The `G'/G` part is bounded at `1` (as `G(1) ≠ 0`),
so `(s-1)·(-ζ'/ζ) = 1 - (s-1)·G'/G → 1`.  This residue is the `-ζ'/ζ` charge that the prime–polar
tomography cancels against the polar term at the pole `s = 3/2`.
-/

open Filter Topology Complex

namespace RHTower

/-- **Residue of a logarithmic derivative at a zero equals the multiplicity.**  If, near `ρ`, an
analytic function factors as `f = (z-ρ)ⁿ·g` with `g` analytic and `g(ρ) ≠ 0`, then
`(s-ρ)·(f'/f)(s) → n` as `s → ρ`.  For a genuine zero `n ≥ 1`; the residue of `-f'/f` is then `-n`.
This is the local structure that turns a zeta zero of order `m` into a pole of `-ζ'/ζ` with residue
`-m`. -/
theorem logDeriv_residue_of_factorization {f g : ℂ → ℂ} {ρ : ℂ} {n : ℕ}
    (hg : AnalyticAt ℂ g ρ) (hg0 : g ρ ≠ 0)
    (hfac : f =ᶠ[𝓝 ρ] fun z => (z - ρ) ^ n • g z) :
    Tendsto (fun s => (s - ρ) * logDeriv f s) (𝓝[≠] ρ) (𝓝 n) := by
  have hgne : ∀ᶠ z in 𝓝 ρ, g z ≠ 0 := hg.continuousAt.eventually_ne hg0
  have hlogGcont : ContinuousAt (logDeriv g) ρ :=
    (hg.deriv.continuousAt).div hg.continuousAt hg0
  have ha : Tendsto (fun s : ℂ => s - ρ) (𝓝[≠] ρ) (𝓝 0) :=
    ((continuous_id.sub continuous_const).tendsto' ρ 0 (by simp)).mono_left nhdsWithin_le_nhds
  have hb : Tendsto (logDeriv g) (𝓝[≠] ρ) (𝓝 (logDeriv g ρ)) :=
    hlogGcont.mono_left nhdsWithin_le_nhds
  have htend0 : Tendsto (fun s => (s - ρ) * logDeriv g s) (𝓝[≠] ρ) (𝓝 0) := by
    simpa using ha.mul hb
  have htend1 : Tendsto (fun s => (n : ℂ) + (s - ρ) * logDeriv g s) (𝓝[≠] ρ) (𝓝 n) := by
    simpa using tendsto_const_nhds.add htend0
  refine htend1.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hfac.eventuallyEq_nhds,
    nhdsWithin_le_nhds hgne, nhdsWithin_le_nhds hg.eventually_analyticAt]
    with s hs hfacs hgs hgana
  have hsρ : s ≠ ρ := by simpa using hs
  have hsρ0 : s - ρ ≠ 0 := sub_ne_zero.mpr hsρ
  have hFeq : f =ᶠ[𝓝 s] (fun z => (z - ρ) ^ n * g z) := by
    filter_upwards [hfacs] with z hz; rw [hz, smul_eq_mul]
  have hlogf : logDeriv f s = logDeriv (fun z => (z - ρ) ^ n * g z) s := by
    rw [logDeriv_apply, logDeriv_apply, hFeq.deriv_eq, hFeq.eq_of_nhds]
  have hdz : DifferentiableAt ℂ (fun z : ℂ => z - ρ) s := by fun_prop
  have hderiv : deriv (fun z : ℂ => z - ρ) s = 1 := by simp
  have hld : logDeriv (fun z => z - ρ) s = (s - ρ)⁻¹ := by
    rw [logDeriv_apply, hderiv, one_div]
  rw [hlogf, logDeriv_mul (f := fun z => (z - ρ) ^ n) (g := g) s (pow_ne_zero n hsρ0) hgs
    ((differentiableAt_id.sub_const ρ).pow n) hgana.differentiableAt,
    logDeriv_fun_pow hdz n, hld]
  field_simp

/-- The analytic continuation of `(s-1)·ζ(s)` across `s = 1`, with the removable value `1`. -/
noncomputable def zetaResidueUnit : ℂ → ℂ :=
  Function.update (fun s => (s - 1) * riemannZeta s) 1 1

@[simp] theorem zetaResidueUnit_one : zetaResidueUnit 1 = 1 := Function.update_self _ _ _

theorem zetaResidueUnit_eventuallyEq {t : ℂ} (ht : t ≠ 1) :
    zetaResidueUnit =ᶠ[𝓝 t] (fun s => (s - 1) * riemannZeta s) := by
  filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using ht)] with z hz
  simp [zetaResidueUnit, Function.update_of_ne (by simpa using hz)]

/-- `(s-1)·ζ(s)` is analytic at `1` — Riemann's removable-singularity theorem applied to the simple
pole of `ζ`, with the limit value supplied by `riemannZeta_residue_one`. -/
theorem zetaResidueUnit_analyticAt : AnalyticAt ℂ zetaResidueUnit 1 := by
  refine analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 1 := by simpa using ht
    exact ((differentiableAt_id.sub_const 1).mul
      (differentiableAt_riemannZeta ht')).congr_of_eventuallyEq (zetaResidueUnit_eventuallyEq ht')
  · exact continuousAt_update_same.mpr riemannZeta_residue_one

theorem zetaResidueUnit_diffAt {t : ℂ} (ht : t ≠ 1) : DifferentiableAt ℂ zetaResidueUnit t :=
  ((differentiableAt_id.sub_const 1).mul
    (differentiableAt_riemannZeta ht)).congr_of_eventuallyEq (zetaResidueUnit_eventuallyEq ht)

theorem zetaResidueUnit_ne_zero_eventually : ∀ᶠ s in 𝓝 (1 : ℂ), zetaResidueUnit s ≠ 0 :=
  zetaResidueUnit_analyticAt.continuousAt.eventually_ne (by rw [zetaResidueUnit_one]; norm_num)

/-- `logDeriv (z ↦ (z-1)⁻¹) s = -(s-1)⁻¹`. -/
theorem logDeriv_inv_sub_one {s : ℂ} (hs : s ≠ 1) :
    logDeriv (fun z => (z - 1)⁻¹) s = -(s - 1)⁻¹ := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hd : HasDerivAt (fun z => (z - 1)⁻¹) (-1 / (s - 1) ^ 2) s :=
    ((hasDerivAt_id s).sub_const 1).inv hs1
  rw [logDeriv_apply, hd.deriv]
  field_simp

/-- Near `1` (off the pole), `ζ'/ζ = G'/G - 1/(s-1)` with `G = zetaResidueUnit`. -/
theorem logDeriv_zeta_eq {s : ℂ} (hs : s ≠ 1) (hGz : zetaResidueUnit s ≠ 0) :
    logDeriv riemannZeta s = logDeriv zetaResidueUnit s - (s - 1)⁻¹ := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hinvne : (s - 1)⁻¹ ≠ 0 := inv_ne_zero hs1
  have hdiff_inv : DifferentiableAt ℂ (fun z => (z - 1)⁻¹) s :=
    (differentiableAt_id.sub_const 1).inv hs1
  have hzeta_eq : (fun z => zetaResidueUnit z * (z - 1)⁻¹) =ᶠ[𝓝 s] riemannZeta := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show s ∈ ({1}ᶜ : Set ℂ) by simpa using hs)]
      with z hz
    have hz1 : z ≠ 1 := by simpa using hz
    simp only [zetaResidueUnit, Function.update_of_ne hz1]
    rw [mul_right_comm, mul_inv_cancel₀ (sub_ne_zero.mpr hz1), one_mul]
  have hlogcong : logDeriv (fun z => zetaResidueUnit z * (z - 1)⁻¹) s = logDeriv riemannZeta s := by
    rw [logDeriv_apply, logDeriv_apply, hzeta_eq.deriv_eq, hzeta_eq.eq_of_nhds]
  rw [← hlogcong, logDeriv_mul s hGz hinvne (zetaResidueUnit_diffAt hs) hdiff_inv,
    logDeriv_inv_sub_one hs]
  ring

/-- **The residue of `-ζ'/ζ` at `s = 1` is `+1`.**  `(s-1)·(-ζ'(s)/ζ(s)) → 1` as `s → 1`. -/
theorem neg_logDeriv_zeta_residue :
    Tendsto (fun s => (s - 1) * (-deriv riemannZeta s / riemannZeta s)) (𝓝[≠] 1) (𝓝 1) := by
  have hGz1 : zetaResidueUnit 1 ≠ 0 := by rw [zetaResidueUnit_one]; norm_num
  have hlogGz_cont : ContinuousAt (logDeriv zetaResidueUnit) 1 :=
    (zetaResidueUnit_analyticAt.deriv.continuousAt).div zetaResidueUnit_analyticAt.continuousAt hGz1
  have ha : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] 1) (𝓝 0) :=
    ((continuous_id.sub continuous_const).tendsto' 1 0 (by norm_num)).mono_left nhdsWithin_le_nhds
  have hb : Tendsto (logDeriv zetaResidueUnit) (𝓝[≠] 1) (𝓝 (logDeriv zetaResidueUnit 1)) :=
    hlogGz_cont.mono_left nhdsWithin_le_nhds
  have htend0 : Tendsto (fun s => (s - 1) * logDeriv zetaResidueUnit s) (𝓝[≠] 1) (𝓝 0) := by
    simpa using ha.mul hb
  have htend1 : Tendsto (fun s => 1 - (s - 1) * logDeriv zetaResidueUnit s) (𝓝[≠] 1) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub htend0
  refine htend1.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds zetaResidueUnit_ne_zero_eventually]
    with s hs hGz
  have hs' : s ≠ 1 := by simpa using hs
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs'
  have hconv : -deriv riemannZeta s / riemannZeta s = -logDeriv riemannZeta s := by
    rw [logDeriv_apply]; ring
  rw [hconv, logDeriv_zeta_eq hs' hGz]
  field_simp
  ring

/-- **The residue of `-ζ'/ζ` at a zeta zero `ρ ≠ 1` is `-m(ρ)`**, where `m(ρ) ≥ 1` is the analytic
multiplicity of the zero: `(s-ρ)·(-ζ'/ζ)(s) → -m`.  Obtained by factoring `ζ = (z-ρ)^m·g` near `ρ`
(`g` analytic, `g(ρ) ≠ 0`, from the removable/order structure of the analytic `ζ` on the connected set
`{1}ᶜ`, using that `ζ` is not identically zero since `ζ(2) ≠ 0`) and applying
`logDeriv_residue_of_factorization`.  This turns each off-critical zeta zero into a pole of the
prime–polar continuation with residue proportional to its multiplicity. -/
theorem neg_logDeriv_zeta_zero_residue {ρ : ℂ} (hρ1 : ρ ≠ 1) (hζρ : riemannZeta ρ = 0) :
    ∃ m : ℕ, 1 ≤ m ∧ Tendsto (fun s => (s - ρ) * (-deriv riemannZeta s / riemannZeta s))
      (𝓝[≠] ρ) (𝓝 (-(m : ℂ))) := by
  have hpreconn : IsPreconnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num) 1).isPreconnected
  have hdiffon : DifferentiableOn ℂ riemannZeta {(1 : ℂ)}ᶜ :=
    fun z hz => (differentiableAt_riemannZeta (by simpa using hz)).differentiableWithinAt
  have hana_on : AnalyticOnNhd ℂ riemannZeta {(1 : ℂ)}ᶜ :=
    hdiffon.analyticOnNhd isOpen_compl_singleton
  have hρmem : ρ ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by simpa using hρ1
  have hana : AnalyticAt ℂ riemannZeta ρ := hana_on ρ hρmem
  have hne : ¬ ∀ᶠ z in 𝓝 ρ, riemannZeta z = 0 := by
    intro hev
    have heqon : Set.EqOn riemannZeta 0 {(1 : ℂ)}ᶜ :=
      hana_on.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpreconn hρmem hev
    have hζ2ne : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
    exact hζ2ne (by simpa using heqon (show (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) by norm_num))
  obtain ⟨n, g, hg, hg0, hfac⟩ := hana.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  have hfac' : riemannZeta =ᶠ[𝓝 ρ] (fun z => (z - ρ) ^ n • g z) := hfac
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exfalso; apply hg0
      have hval := hfac'.eq_of_nhds
      rw [hn] at hval
      simpa [hζρ] using hval.symm
    · exact hn
  refine ⟨n, hn1, ?_⟩
  refine (logDeriv_residue_of_factorization hg hg0 hfac').neg.congr'
    (Filter.Eventually.of_forall (fun s => ?_))
  rw [logDeriv_apply]; ring

end RHTower
