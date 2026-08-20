import GaloisForLFunctions.RHTower.ZetaRealSignature
import GaloisForLFunctions.RHTower.ZetaDerivResidue

/-!
# The Fisher metric of the arithmetic state family blows up at the critical line

The quantum-Fisher / Fubini–Study metric of the Bohr state family is the second logarithmic
derivative `g = (log ζ)''`.  Writing the Laurent factorisation `ζ(s) = U(s)/(s-1)` with `U` entire
and `U(1) = 1`, multiplicativity of the logarithmic derivative gives

`(log ζ)'' = (log U)'' + 1/(s-1)²`,

and `(log U)''` is continuous at the pole.  Hence

`(s-1)² · (log ζ)''(s) → 1`,

i.e. `g ∼ 1/(2σ-1)²` in the position coordinate `x = 2σ`: the critical line is an infinite-distance
horizon of the information metric.
-/

noncomputable section

open Filter Topology

namespace RHTower

/-! ### The Laurent unit -/

/-- The unit of the Laurent factorisation of `ζ` at its pole: `ζ(s) = U(s)/(s-1)`. -/
def zetaLaurentUnit (s : ℂ) : ℂ := (s - 1) * zetaPoleFree s + gammaRInv s

theorem differentiable_zetaLaurentUnit : Differentiable ℂ zetaLaurentUnit := by
  intro s
  exact (((differentiable_id.sub_const 1).mul differentiable_zetaPoleFree).add
    differentiable_gammaRInv) s

theorem zetaLaurentUnit_one : zetaLaurentUnit 1 = 1 := by
  rw [zetaLaurentUnit, gammaRInv_one]
  ring

theorem riemannZeta_eq_laurentUnit_div {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s = zetaLaurentUnit s / (s - 1) := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [riemannZeta_eq_poleFree_add hs, zetaLaurentUnit]
  field_simp

/-! ### The Fisher metric -/

/-- The quantum-Fisher / Fubini–Study metric of the arithmetic state family: the second
logarithmic derivative of `ζ`. -/
def zetaFisherMetric (s : ℂ) : ℂ := deriv (logDeriv riemannZeta) s

/-- The open set on which the Laurent factorisation has an invertible unit. -/
def zetaLaurentDomain : Set ℂ := {s : ℂ | s ≠ 1 ∧ zetaLaurentUnit s ≠ 0}

theorem isOpen_zetaLaurentDomain : IsOpen zetaLaurentDomain := by
  have h1 : IsOpen ({(1 : ℂ)}ᶜ : Set ℂ) := isOpen_compl_singleton
  have h2 : IsOpen {s : ℂ | zetaLaurentUnit s ≠ 0} :=
    isOpen_ne_fun differentiable_zetaLaurentUnit.continuous continuous_const
  exact h1.inter h2

/-- The derivative of the Cauchy factor of the Laurent factorisation. -/
theorem hasDerivAt_sub_one_inv {s : ℂ} (hs : s ≠ 1) :
    HasDerivAt (fun z : ℂ => (z - 1)⁻¹) (-1 / (s - 1) ^ 2) s := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hd : HasDerivAt (fun z : ℂ => z - 1) 1 s := by
    simpa using (hasDerivAt_id s).sub_const 1
  have h := hd.inv hsub
  rw [Pi.inv_def] at h
  simpa using h

theorem logDeriv_sub_one_inv {s : ℂ} (hs : s ≠ 1) :
    logDeriv (fun z : ℂ => (z - 1)⁻¹) s = -(s - 1)⁻¹ := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [logDeriv_apply, (hasDerivAt_sub_one_inv hs).deriv]
  field_simp

theorem logDeriv_riemannZeta_eqOn :
    Set.EqOn (logDeriv riemannZeta)
      (fun z : ℂ => logDeriv zetaLaurentUnit z - (z - 1)⁻¹) zetaLaurentDomain := by
  intro s hs
  obtain ⟨hs1, hsU⟩ := hs
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hV := hasDerivAt_sub_one_inv hs1
  have hmul : Set.EqOn riemannZeta (fun z : ℂ => zetaLaurentUnit z * (z - 1)⁻¹)
      zetaLaurentDomain := by
    intro z hz
    rw [riemannZeta_eq_laurentUnit_div hz.1, div_eq_mul_inv]
  have hnhds : zetaLaurentDomain ∈ nhds s := isOpen_zetaLaurentDomain.mem_nhds ⟨hs1, hsU⟩
  have heq : riemannZeta =ᶠ[nhds s] fun z : ℂ => zetaLaurentUnit z * (z - 1)⁻¹ :=
    Filter.eventuallyEq_of_mem hnhds hmul
  have hlog : logDeriv riemannZeta s = logDeriv (fun z : ℂ => zetaLaurentUnit z * (z - 1)⁻¹) s := by
    rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds]
  show logDeriv riemannZeta s = logDeriv zetaLaurentUnit s - (s - 1)⁻¹
  rw [hlog, logDeriv_mul (f := zetaLaurentUnit) (g := fun z : ℂ => (z - 1)⁻¹) s hsU
    (inv_ne_zero hsub) (differentiable_zetaLaurentUnit s) hV.differentiableAt,
    logDeriv_sub_one_inv hs1]
  ring

theorem deriv_logDeriv_riemannZeta_eq {s : ℂ} (hs : s ∈ zetaLaurentDomain) :
    zetaFisherMetric s = deriv (logDeriv zetaLaurentUnit) s + (s - 1)⁻¹ ^ 2 := by
  have hnhds : zetaLaurentDomain ∈ nhds s := isOpen_zetaLaurentDomain.mem_nhds hs
  have heq : logDeriv riemannZeta =ᶠ[nhds s]
      fun z : ℂ => logDeriv zetaLaurentUnit z - (z - 1)⁻¹ :=
    Filter.eventuallyEq_of_mem hnhds logDeriv_riemannZeta_eqOn
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs.1
  have hV := hasDerivAt_sub_one_inv hs.1
  have hU : DifferentiableAt ℂ (logDeriv zetaLaurentUnit) s := by
    have hana : AnalyticAt ℂ zetaLaurentUnit s :=
      (differentiable_zetaLaurentUnit.differentiableOn.analyticOnNhd isOpen_univ) s
        (Set.mem_univ s)
    have hlog : AnalyticAt ℂ (logDeriv zetaLaurentUnit) s := by
      have hfun : logDeriv zetaLaurentUnit
          = fun z : ℂ => deriv zetaLaurentUnit z / zetaLaurentUnit z := by
        funext z; exact logDeriv_apply _ _
      rw [hfun]
      exact hana.deriv.div hana hs.2
    exact hlog.differentiableAt
  have hTotal : HasDerivAt (fun z : ℂ => logDeriv zetaLaurentUnit z - (z - 1)⁻¹)
      (deriv (logDeriv zetaLaurentUnit) s - (-1 / (s - 1) ^ 2)) s := hU.hasDerivAt.sub hV
  rw [zetaFisherMetric, heq.deriv_eq, hTotal.deriv]
  field_simp

/-! ### The blow-up at the wall -/

theorem continuousAt_deriv_logDeriv_zetaLaurentUnit :
    ContinuousAt (deriv (logDeriv zetaLaurentUnit)) 1 := by
  have hana : AnalyticAt ℂ zetaLaurentUnit 1 :=
    (differentiable_zetaLaurentUnit.differentiableOn.analyticOnNhd isOpen_univ) 1 (Set.mem_univ 1)
  have hne : zetaLaurentUnit 1 ≠ 0 := by rw [zetaLaurentUnit_one]; exact one_ne_zero
  have hlog : AnalyticAt ℂ (logDeriv zetaLaurentUnit) 1 := by
    have hfun : logDeriv zetaLaurentUnit
        = fun z : ℂ => deriv zetaLaurentUnit z / zetaLaurentUnit z := by
      funext z; exact logDeriv_apply _ _
    rw [hfun]
    exact hana.deriv.div hana hne
  exact hlog.deriv.continuousAt

theorem eventually_mem_zetaLaurentDomain :
    ∀ᶠ s : ℂ in nhdsWithin 1 {(1 : ℂ)}ᶜ, s ∈ zetaLaurentDomain := by
  have hne : zetaLaurentUnit 1 ≠ 0 := by rw [zetaLaurentUnit_one]; exact one_ne_zero
  have hU : ∀ᶠ s : ℂ in nhds (1 : ℂ), zetaLaurentUnit s ≠ 0 :=
    (differentiable_zetaLaurentUnit.continuous.continuousAt).eventually_ne hne
  filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with s hs1 hs2
  exact ⟨hs2, hs1⟩

/-- **The Fisher horizon.**  `(s-1)² (log ζ)''(s) → 1` as `s → 1`: the information metric blows up
like `1/(s-1)²` at the pole of `ζ`, i.e. like `1/(2σ-1)²` at the critical line. -/
theorem tendsto_sub_one_sq_mul_zetaFisherMetric :
    Tendsto (fun s : ℂ => (s - 1) ^ 2 * zetaFisherMetric s) (nhdsWithin 1 {(1 : ℂ)}ᶜ)
      (nhds 1) := by
  have hsub : Tendsto (fun s : ℂ => (s - 1) ^ 2) (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds 0) := by
    have h : Tendsto (fun s : ℂ => s - 1) (nhds (1 : ℂ)) (nhds 0) := by
      simpa using (continuous_sub_right (1 : ℂ)).tendsto (1 : ℂ)
    simpa using (h.pow 2).mono_left nhdsWithin_le_nhds
  have hcont : Tendsto (deriv (logDeriv zetaLaurentUnit)) (nhdsWithin 1 {(1 : ℂ)}ᶜ)
      (nhds (deriv (logDeriv zetaLaurentUnit) 1)) :=
    continuousAt_deriv_logDeriv_zetaLaurentUnit.tendsto.mono_left nhdsWithin_le_nhds
  have hprod : Tendsto (fun s : ℂ => (s - 1) ^ 2 * deriv (logDeriv zetaLaurentUnit) s)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds 0) := by
    simpa using hsub.mul hcont
  have hone : Tendsto (fun _ : ℂ => (1 : ℂ)) (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds 1) :=
    tendsto_const_nhds
  have hsum := hprod.add hone
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_mem_zetaLaurentDomain] with s hs
  have hsub0 : s - 1 ≠ 0 := sub_ne_zero.mpr hs.1
  rw [deriv_logDeriv_riemannZeta_eq hs]
  field_simp

end RHTower
