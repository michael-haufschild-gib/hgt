import GaloisForLFunctions.RHTower.CanonicalCutoffTorsionSeam
import GaloisForLFunctions.RHTower.WindingXi
import GaloisForLFunctions.RHTower.WeldZeroGenerator
import GaloisForLFunctions.RHTower.RHLadderTheory
import GaloisForLFunctions.RHTower.CompletedLogDerivStrip
import GaloisForLFunctions.RHTower.BornTemperatureFactorType

/-!
# Normalized prime-flux residue and canonical Fitting seam scalar

The infinite von Mangoldt source is `-ζ'/ζ` on `Re s > 1`; its meromorphic continuation has
normalized residue `-1` at every zero in the open critical strip, with no simple-zero hypothesis.
At the actual `xi` multiplicity depth, the separately defined canonical cutoff seam also has
constant boundary jet `[-1]`.

This file proves both statements and the resulting scalar coincidence.  It does **not** construct a
map from the Euler source into the Fitting quotient: normalization forces the analytic scalar to be
`-1`, while the canonical seam was defined with boundary `-1`.  The coincidence is bridge
infrastructure, not a completed attachment or an RH-facing compatibility theorem.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- Local factorization of the normalized logarithmic derivative of `xi` at an arbitrary point. -/
theorem exists_xi_normalizedLogDeriv_factorization (ρ : ℂ) :
    ∃ R > 0, ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (ball ρ R) ∧
      (∀ z ∈ ball ρ R, h z ≠ 0) ∧
      (∀ z ∈ ball ρ R, z ≠ ρ →
        (z - ρ) * logDeriv xi z =
          ((analyticOrderAt xi ρ).toNat : ℂ) + (z - ρ) * logDeriv h z) := by
  obtain ⟨R, hR, h, hhan, hh0, hfact⟩ := xi_peel_ball ρ
  refine ⟨R, hR, h, hhan, hh0, ?_⟩
  intro z hz hzne
  let p : ℂ → ℂ := fun w => (w - ρ) ^ (analyticOrderAt xi ρ).toNat
  have hball : ball ρ R ∈ nhds z := isOpen_ball.mem_nhds hz
  have heq : xi =ᶠ[nhds z] fun w => p w * h w := by
    filter_upwards [hball] with w hw
    exact hfact w hw
  have hval : xi z = p z * h z := heq.eq_of_nhds
  have hderiv : deriv xi z = deriv (fun w => p w * h w) z := heq.deriv_eq
  have hp0 : p z ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hzne)
  have hpdiff : DifferentiableAt ℂ p z := by
    dsimp [p]
    fun_prop
  have hhdiff : DifferentiableAt ℂ h z := (hhan z hz).differentiableAt
  have hlogmul := logDeriv_mul z hp0 (hh0 z hz) hpdiff hhdiff
  have hlogeq : logDeriv xi z = logDeriv p z + logDeriv h z := by
    rw [logDeriv_apply, hderiv, hval]
    exact hlogmul
  rw [hlogeq]
  have hp : logDeriv p z = ((analyticOrderAt xi ρ).toNat : ℂ) / (z - ρ) := by
    dsimp [p]
    rw [logDeriv_fun_pow (by fun_prop)]
    rw [logDeriv_apply]
    have hd : deriv (fun w : ℂ => w - ρ) z = 1 := by
      simp
    rw [hd]
    ring
  rw [hp]
  field_simp [sub_ne_zero.mpr hzne]

/-- The normalized logarithmic derivative of `xi` tends to its full vanishing order. -/
theorem xi_normalizedLogDeriv_tendsto_order (ρ : ℂ) :
    Tendsto (fun z : ℂ => (z - ρ) * logDeriv xi z) (nhdsWithin ρ ({ρ}ᶜ))
      (nhds ((analyticOrderAt xi ρ).toNat : ℂ)) := by
  obtain ⟨R, hR, h, hhan, hh0, hlocal⟩ := exists_xi_normalizedLogDeriv_factorization ρ
  have hρball : ρ ∈ ball ρ R := mem_ball_self hR
  have hha : AnalyticAt ℂ h ρ := hhan ρ hρball
  have hlogcont : ContinuousAt (logDeriv h) ρ := by
    rw [show logDeriv h = fun z => deriv h z / h z by funext z; rw [logDeriv_apply]]
    exact hha.deriv.continuousAt.div hha.continuousAt (hh0 ρ hρball)
  have hrem : Tendsto (fun z : ℂ => (z - ρ) * logDeriv h z) (nhds ρ) (nhds 0) := by
    have hcont : ContinuousAt (fun z : ℂ => (z - ρ) * logDeriv h z) ρ :=
      (continuousAt_id.sub continuousAt_const).mul hlogcont
    simpa using hcont.tendsto
  have hsum : Tendsto
      (fun z : ℂ => ((analyticOrderAt xi ρ).toNat : ℂ) + (z - ρ) * logDeriv h z)
      (nhdsWithin ρ ({ρ}ᶜ)) (nhds ((analyticOrderAt xi ρ).toNat : ℂ)) := by
    simpa using (tendsto_nhdsWithin_of_tendsto_nhds hrem).const_add
      ((analyticOrderAt xi ρ).toNat : ℂ)
  apply hsum.congr'
  have hball : ball ρ R ∈ nhds ρ := isOpen_ball.mem_nhds hρball
  filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with z hz hzne
  exact (hlocal z hz hzne).symm

/-- At every `xi` zero, its multiplicity-normalized negative log derivative has residue `-1`. -/
theorem xi_negative_normalizedLogDeriv_tendsto_neg_one {ρ : ℂ} (hzero : xi ρ = 0) :
    Tendsto
      (fun z : ℂ => -((z - ρ) * logDeriv xi z) /
        ((analyticOrderAt xi ρ).toNat : ℂ))
      (nhdsWithin ρ ({ρ}ᶜ)) (nhds (-1 : ℂ)) := by
  have hm : ((analyticOrderAt xi ρ).toNat : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (xi_order_toNat_ne_zero hzero)
  have h := (xi_normalizedLogDeriv_tendsto_order ρ).neg.div_const
    ((analyticOrderAt xi ρ).toNat : ℂ)
  simpa [hm] using h

/-- In the open strip, the archimedean factor is a unit, so `xi` and `ζ` have equal orders. -/
theorem xi_analyticOrderAt_eq_riemannZeta_of_mem_strip {ρ : ℂ}
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) :
    analyticOrderAt xi ρ = analyticOrderAt riemannZeta ρ := by
  let U : Set ℂ := {z | 0 < z.re ∧ z.re < 1}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hρU : ρ ∈ U := hstrip
  have hev : xi =ᶠ[nhds ρ] fun z => archFactor z * riemannZeta z := by
    filter_upwards [hUopen.mem_nhds hρU] with z hz
    exact xi_eq_archFactor_mul_zeta
      (by intro h; subst z; simpa using hz.1)
      (by intro h; subst z; simpa using hz.2)
      (Gammaℝ_ne_zero_of_re_pos hz.1)
  have harch : AnalyticAt ℂ archFactor ρ := by
    have hpoly : AnalyticAt ℂ (fun z : ℂ => z * (z - 1) / 2) ρ := by fun_prop
    exact hpoly.mul (Gammaℝ_analyticAt (Gammaℝ_ne_zero_of_re_pos hstrip.1))
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h] at hstrip
    norm_num at hstrip
  have hzeta : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ1
  rw [analyticOrderAt_congr hev]
  change analyticOrderAt (archFactor * riemannZeta) ρ = analyticOrderAt riemannZeta ρ
  rw [analyticOrderAt_mul harch hzeta,
    harch.analyticOrderAt_eq_zero.mpr (archFactor_ne_zero_strip hstrip), zero_add]

/-- Local factorization of `ζ'/ζ` at a strip point, measured by the equal `xi` order. -/
theorem exists_riemannZeta_normalizedLogDeriv_factorization_of_mem_strip {ρ : ℂ}
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) :
    ∃ R > 0, ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (ball ρ R) ∧
      (∀ z ∈ ball ρ R, h z ≠ 0) ∧
      ∀ z ∈ ball ρ R, z ≠ ρ →
        (z - ρ) * logDeriv riemannZeta z =
          ((analyticOrderAt xi ρ).toNat : ℂ) + (z - ρ) * logDeriv h z := by
  let U : Set ℂ := {z | 0 < z.re ∧ z.re < 1}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hρU : ρ ∈ U := hstrip
  have hzetaU : AnalyticOnNhd ℂ riemannZeta U := by
    exact analyticOn_riemannZeta.mono (by
      intro z hz
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (show z ≠ 1 by
          intro h
          subst z
          exact (lt_irrefl 1 hz.2)))
  have horder := xi_analyticOrderAt_eq_riemannZeta_of_mem_strip hstrip
  have hm : analyticOrderAt riemannZeta ρ =
      ((analyticOrderAt xi ρ).toNat : ℕ∞) := by
    rw [← horder]
    exact (ENat.coe_toNat (xi_order_ne_top ρ)).symm
  obtain ⟨h, hhan, hh0, hfact, _⟩ := exists_peel hUopen hzetaU hρU hm
  have hnonzero : {z : ℂ | h z ≠ 0} ∈ nhds ρ :=
    (hhan ρ hρU).continuousAt.eventually_ne hh0
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hUopen.mem_nhds hρU) hnonzero)
  have hballU : ball ρ R ⊆ U := fun z hz => (hRsub hz).1
  have hhball : ∀ z ∈ ball ρ R, h z ≠ 0 := fun z hz => (hRsub hz).2
  refine ⟨R, hR, h, hhan.mono hballU, hhball, ?_⟩
  intro z hz hzne
  let p : ℂ → ℂ := fun w => (w - ρ) ^ (analyticOrderAt xi ρ).toNat
  have hUmem : U ∈ nhds z := hUopen.mem_nhds (hballU hz)
  have heq : riemannZeta =ᶠ[nhds z] fun w => p w * h w := by
    filter_upwards [hUmem] with w hw
    exact hfact w hw
  have hval : riemannZeta z = p z * h z := heq.eq_of_nhds
  have hderiv : deriv riemannZeta z = deriv (fun w => p w * h w) z := heq.deriv_eq
  have hp0 : p z ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hzne)
  have hpdiff : DifferentiableAt ℂ p z := by
    dsimp [p]
    fun_prop
  have hhdiff : DifferentiableAt ℂ h z := (hhan z (hballU hz)).differentiableAt
  have hlogmul := logDeriv_mul z hp0 (hhball z hz) hpdiff hhdiff
  have hlogeq : logDeriv riemannZeta z = logDeriv p z + logDeriv h z := by
    rw [logDeriv_apply, hderiv, hval]
    exact hlogmul
  rw [hlogeq]
  have hp : logDeriv p z = ((analyticOrderAt xi ρ).toNat : ℂ) / (z - ρ) := by
    dsimp [p]
    rw [logDeriv_fun_pow (by fun_prop)]
    rw [logDeriv_apply]
    have hd : deriv (fun w : ℂ => w - ρ) z = 1 := by
      simp
    rw [hd]
    ring
  rw [hp]
  field_simp [sub_ne_zero.mpr hzne]

/-- On the strip, the normalized `ζ` logarithmic derivative tends to the equal `xi` order. -/
theorem riemannZeta_normalizedLogDeriv_tendsto_xi_order_of_mem_strip (ρ : ℂ)
    (hstrip : 0 < ρ.re ∧ ρ.re < 1) :
    Tendsto (fun z : ℂ => (z - ρ) * logDeriv riemannZeta z) (nhdsWithin ρ ({ρ}ᶜ))
      (nhds ((analyticOrderAt xi ρ).toNat : ℂ)) := by
  obtain ⟨R, hR, h, hhan, hh0, hlocal⟩ :=
    exists_riemannZeta_normalizedLogDeriv_factorization_of_mem_strip hstrip
  have hρball : ρ ∈ ball ρ R := mem_ball_self hR
  have hha : AnalyticAt ℂ h ρ := hhan ρ hρball
  have hlogcont : ContinuousAt (logDeriv h) ρ := by
    rw [show logDeriv h = fun z => deriv h z / h z by funext z; rw [logDeriv_apply]]
    exact hha.deriv.continuousAt.div hha.continuousAt (hh0 ρ hρball)
  have hrem : Tendsto (fun z : ℂ => (z - ρ) * logDeriv h z) (nhds ρ) (nhds 0) := by
    have hcont : ContinuousAt (fun z : ℂ => (z - ρ) * logDeriv h z) ρ :=
      (continuousAt_id.sub continuousAt_const).mul hlogcont
    simpa using hcont.tendsto
  have hsum : Tendsto
      (fun z : ℂ => ((analyticOrderAt xi ρ).toNat : ℂ) +
        (z - ρ) * logDeriv h z)
      (nhdsWithin ρ ({ρ}ᶜ)) (nhds ((analyticOrderAt xi ρ).toNat : ℂ)) := by
    simpa using (tendsto_nhdsWithin_of_tendsto_nhds hrem).const_add
      ((analyticOrderAt xi ρ).toNat : ℂ)
  apply hsum.congr'
  have hball : ball ρ R ∈ nhds ρ := isOpen_ball.mem_nhds hρball
  filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with z hz hzne
  exact (hlocal z hz hzne).symm

/-- The continued infinite-prime flux has normalized residue `-1` at every `xi` zero.  Open-strip
membership is supplied by the completed functional equation and no longer remains an input. -/
theorem riemannZeta_negative_normalizedLogDeriv_tendsto_neg_one_of_xi_zero
    {ρ : ℂ} (hzero : xi ρ = 0) :
    Tendsto
      (fun z : ℂ => -((z - ρ) * logDeriv riemannZeta z) /
        ((analyticOrderAt xi ρ).toNat : ℂ))
      (nhdsWithin ρ ({ρ}ᶜ)) (nhds (-1 : ℂ)) := by
  have hstrip : 0 < ρ.re ∧ ρ.re < 1 := xi_zero_re_mem_open_unit hzero
  have hm : ((analyticOrderAt xi ρ).toNat : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (xi_order_toNat_ne_zero hzero)
  have h := (riemannZeta_normalizedLogDeriv_tendsto_xi_order_of_mem_strip ρ hstrip).neg.div_const
    ((analyticOrderAt xi ρ).toNat : ℂ)
  simpa [hm] using h

/-- The canonical non-split Fitting seam at a point, at the actual `xi` multiplicity depth. -/
def xiCanonicalFittingSeamAt (ρ : ℂ) :
    TorsionSeamPresentation Unit (Fin 2) ℚ (analyticOrderAt xi ρ).toNat :=
  canonicalCutoffTorsionSeam (analyticOrderAt xi ρ).toNat

/-- Its nontrivial Fitting-boundary interface is equivalent to `xi` vanishing at the point. -/
theorem xiCanonicalFittingSeamAt_hasNontrivialFittingBoundary_iff (ρ : ℂ) :
    HasNontrivialFittingBoundary (analyticOrderAt xi ρ).toNat
      (xiCanonicalFittingSeamAt ρ).A (xiCanonicalFittingSeamAt ρ).Delta ↔
      xi ρ = 0 := by
  constructor
  · intro hboundary
    by_contra hzero
    have hord0 : analyticOrderAt xi ρ = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hzero)
    have hm0 : (analyticOrderAt xi ρ).toNat = 0 := by rw [hord0]; rfl
    rcases hboundary with ⟨p, hp⟩
    cases p
    change (canonicalCutoffTorsionSeam (analyticOrderAt xi ρ).toNat).boundaryClass () ≠ 0 at hp
    rw [canonicalCutoffTorsionSeam_boundaryClass, hm0] at hp
    exact hp ((jetClass_eq_zero_iff_coeff_lt_eq_zero ℚ 0).mpr (by omega))
  · intro hzero
    exact canonicalCutoffTorsionSeam_hasNontrivialFittingBoundary
      (Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hzero))

/-- Its low-coefficient boundary witness exists exactly at the zeros of `xi`. -/
theorem xiCanonicalFittingSeamAt_boundaryCoeffWitness_iff (ρ : ℂ) :
    (xiCanonicalFittingSeamAt ρ).BoundaryCoeffWitness () ↔ xi ρ = 0 := by
  constructor
  · intro hwitness
    apply (xiCanonicalFittingSeamAt_hasNontrivialFittingBoundary_iff ρ).mp
    exact ⟨(), (xiCanonicalFittingSeamAt ρ).boundaryClass_ne_zero_iff_coeffWitness.mpr
      hwitness⟩
  · intro hzero
    exact canonicalCutoffTorsionSeam_boundaryCoeffWitness
      (Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hzero))

/-- Its determinant-transverse-defect interface exists exactly at the zeros of `xi`. -/
theorem xiCanonicalFittingSeamAt_hasDeterminantTransverseDefect_iff (ρ : ℂ) :
    (xiCanonicalFittingSeamAt ρ).HasDeterminantTransverseDefect ↔ xi ρ = 0 := by
  rw [← xiCanonicalFittingSeamAt_hasNontrivialFittingBoundary_iff ρ]
  exact (xiCanonicalFittingSeamAt ρ).hasNontrivialFittingBoundary_iff_hasDeterminantTransverseDefect.symm

/-- The meromorphic continuation of the infinite von Mangoldt prime flux. -/
noncomputable def infinitePrimeFlux (s : ℂ) : ℂ := -logDeriv riemannZeta s

/-- On `Re s > 1`, the infinite prime flux is the von Mangoldt Dirichlet series. -/
theorem infinitePrimeFlux_eq_vonMangoldtLSeries {s : ℂ} (hs : 1 < s.re) :
    infinitePrimeFlux s =
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  rw [infinitePrimeFlux, logDeriv_apply]
  rw [show -(deriv riemannZeta s / riemannZeta s) =
    -deriv riemannZeta s / riemannZeta s by ring]
  exact (GaloisForLFunctions.RHTower.zeta_logDeriv_frequencies_weld hs).1

/-- Every nonzero frequency of the infinite prime flux lies in the prime-log weld lattice. -/
theorem infinitePrimeFlux_frequency_mem_primeLogLattice {n : ℕ}
    (hn : ArithmeticFunction.vonMangoldt n ≠ 0) :
    Real.log n ∈ GaloisForLFunctions.RHTower.primeLogLattice :=
  GaloisForLFunctions.RHTower.vonMangoldt_freq_mem_primeLogLattice hn

/-- At every `xi` zero, the normalized infinite prime-flux residue and the separately defined
canonical non-split Fitting boundary have the same scalar value `-1`.  No morphism between the two
objects is asserted. -/
theorem infinitePrimeFlux_fitting_scalar_coincidence_of_xi_zero
    {ρ : ℂ} (hzero : xi ρ = 0) :
    Tendsto
        (fun z : ℂ => (z - ρ) * infinitePrimeFlux z /
          ((analyticOrderAt xi ρ).toNat : ℂ))
        (nhdsWithin ρ ({ρ}ᶜ)) (nhds (-1 : ℂ)) ∧
      (xiCanonicalFittingSeamAt ρ).boundaryClass () =
        jetClass ℚ (analyticOrderAt xi ρ).toNat (-1) := by
  constructor
  · simpa [infinitePrimeFlux] using
      riemannZeta_negative_normalizedLogDeriv_tendsto_neg_one_of_xi_zero hzero
  · exact canonicalCutoffTorsionSeam_boundaryClass (analyticOrderAt xi ρ).toNat

end

end RHTower
