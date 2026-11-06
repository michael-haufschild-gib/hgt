import GaloisForLFunctions.ZeroConfigurationGeometry.HighDerivativesRecoverARightmostZero
import GaloisForLFunctions.RHTower.ZetaWeakRecurrenceLadderCollapse
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# A finite exceptional layer forces persistent low-height jets

Failure of the asymptotic abscissa law selects an actual rightmost zeta zero.
For the entire residue unit `(s-1)ζ(s)`, normalized logarithmic-derivative jets at
every centre horizontally to its right converge to its positive multiplicity.
The cofactor and its analytic remainder are constructed from the actual function.
-/

open Complex Filter Metric Set Topology RHTower

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- Removing the pole at `1` adds its explicit derivative to every zeta jet. -/
theorem iteratedDeriv_logDeriv_zetaResidueUnit {s : ℂ} (hs : 1 < s.re) (k : ℕ) :
    iteratedDeriv k (logDeriv zetaResidueUnit) s =
      iteratedDeriv k (logDeriv riemannZeta) s +
        (-1 : ℂ) ^ k * (k.factorial : ℂ) / (s - 1) ^ (k + 1) := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have hlocal : logDeriv zetaResidueUnit =ᶠ[𝓝 s]
      fun z => logDeriv riemannZeta z + (z - 1)⁻¹ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    have hz1 : z ≠ 1 := by intro h; rw [h] at hz; norm_num at hz
    have hunit : zetaResidueUnit z ≠ 0 := by
      rw [(zetaResidueUnit_eventuallyEq hz1).eq_of_nhds]
      exact mul_ne_zero (sub_ne_zero.mpr hz1) (riemannZeta_ne_zero_of_one_le_re hz.le)
    exact (eq_sub_iff_add_eq.mp (logDeriv_zeta_eq hz1 hunit)).symm
  have hlog : AnalyticAt ℂ (logDeriv riemannZeta) s :=
    (analyticOn_riemannZeta s hs1).deriv.div (analyticOn_riemannZeta s hs1)
      (riemannZeta_ne_zero_of_one_le_re hs.le)
  have hinv : ContDiffAt ℂ k (fun z : ℂ => (z - 1)⁻¹) s := by
    have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    fun_prop
  rw [hlocal.iteratedDeriv_eq, iteratedDeriv_fun_add hlog.contDiffAt hinv,
    iteratedDeriv_inv_sub 1 k s (sub_ne_zero.mpr hs1)]

/-- Failure of the abscissa law produces an actual zero whose multiplicity is recovered
by all sufficiently high logarithmic-derivative jets of the entire residue unit. -/
theorem not_asymptoticAbscissaLaw_has_persistent_low_jets :
    ¬ AsymptoticAbscissaLaw →
      ∃ (ρ : ℂ) (m : ℕ), 1 / 2 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 ∧
        0 < m ∧ analyticOrderAt zetaResidueUnit ρ = m ∧
        ∀ d : ℝ, 0 < d →
          Tendsto (fun k : ℕ => (d : ℂ) ^ (k + 1) *
            iteratedDeriv k (logDeriv zetaResidueUnit) (ρ + (d : ℂ)) /
            ((-1 : ℂ) ^ k * (k.factorial : ℂ))) atTop (𝓝 (m : ℂ)) := by
  intro hnot
  unfold AsymptoticAbscissaLaw at hnot
  push Not at hnot
  obtain ⟨h, hh, hfin, q, hq⟩ := hnot
  obtain ⟨q₀, hq₀, hqmax⟩ := hfin.exists_maximalFor
    (fun q : XiZeroCopy => (q.1 : ℂ).re)
    {q : XiZeroCopy | 1 / 2 + h < (q.1 : ℂ).re} ⟨q, hq⟩
  have hmax : ∀ q' : XiZeroCopy, (q'.1 : ℂ).re ≤ (q₀.1 : ℂ).re := by
    intro q'
    by_cases hmem : 1 / 2 + h < (q'.1 : ℂ).re
    · by_contra hgt
      exact (not_le.mpr (lt_of_not_ge hgt)) (hqmax hmem (lt_of_not_ge hgt).le)
    · exact (le_of_not_gt hmem).trans (le_of_lt hq₀)
  let ρ : ℂ := (q₀.1 : ℂ)
  have hρhalf : 1 / 2 < ρ.re := by dsimp [ρ]; linarith
  have hρone : ρ.re < 1 := (xi_divisor_support_re_mem_open_unit q₀.1).2
  have hζ : riemannZeta ρ = 0 := riemannZeta_eq_zero_of_xiZeroCopy q₀
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hρone; norm_num at hρone
  have hunit : zetaResidueUnit ρ = 0 := by
    rw [(zetaResidueUnit_eventuallyEq hρ1).eq_of_nhds, hζ, mul_zero]
  have hunitmax : ∀ z : ℂ, zetaResidueUnit z = 0 → z.re ≤ ρ.re := by
    intro z hz
    by_contra hgt
    have hzre : ρ.re < z.re := lt_of_not_ge hgt
    have hz1 : z ≠ 1 := by intro h; rw [h, zetaResidueUnit_one] at hz; norm_num at hz
    have hζz : riemannZeta z = 0 := by
      rw [(zetaResidueUnit_eventuallyEq hz1).eq_of_nhds] at hz
      exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hz1)
    have hzlt : z.re < 1 := by
      by_contra h
      exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h) hζz
    obtain ⟨q', hq'⟩ := exists_xiZeroCopy_of_zeta_eq_zero_strip hζz (by linarith) hzlt
    have hle := hmax q'
    rw [hq'] at hle
    exact (not_le.mpr hzre) hle
  have han : AnalyticOnNhd ℂ zetaResidueUnit univ := fun z _ => analyticAt_zetaResidueUnit z
  have hord : analyticOrderAt zetaResidueUnit ρ ≠ ⊤ := by
    refine han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (x := 1) trivial trivial ?_
    rw [(analyticAt_zetaResidueUnit 1).analyticOrderAt_eq_zero.mpr (by simp)]
    exact ENat.zero_ne_top
  let m : ℕ := (analyticOrderAt zetaResidueUnit ρ).toNat
  have hm : analyticOrderAt zetaResidueUnit ρ = m := (ENat.coe_toNat hord).symm
  have hmpos : 0 < m := by
    apply Nat.pos_of_ne_zero
    intro hm0
    have hzero : analyticOrderAt zetaResidueUnit ρ = 0 := by rw [hm, hm0]; rfl
    exact ((analyticAt_zetaResidueUnit ρ).analyticOrderAt_eq_zero.mp hzero) hunit
  exact ⟨ρ, m, hρhalf, hρone, hζ, hmpos, hm,
    fun d hd => tendsto_logDeriv_jets_at_rightmost_zero analyticAt_zetaResidueUnit hm hunitmax hd⟩

/-- The persistent jets expressed through the actual zeta logarithmic derivative,
with the pole at `1` retained as an explicit geometric term. -/
theorem not_asymptoticAbscissaLaw_has_corrected_zeta_jet_limit :
    ¬ AsymptoticAbscissaLaw →
      ∃ (ρ : ℂ) (m : ℕ), 1 / 2 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 ∧
        0 < m ∧ ∀ d : ℝ, 1 - ρ.re < d →
          Tendsto (fun k : ℕ =>
            (d : ℂ) ^ (k + 1) * iteratedDeriv k (logDeriv riemannZeta) (ρ + (d : ℂ)) /
              ((-1 : ℂ) ^ k * (k.factorial : ℂ)) +
            ((d : ℂ) / (ρ + (d : ℂ) - 1)) ^ (k + 1)) atTop (𝓝 (m : ℂ)) := by
  intro hnot
  obtain ⟨ρ, m, hρhalf, hρone, hζ, hm, _, hlim⟩ :=
    not_asymptoticAbscissaLaw_has_persistent_low_jets hnot
  refine ⟨ρ, m, hρhalf, hρone, hζ, hm, ?_⟩
  intro d hd
  have hdpos : 0 < d := by linarith
  have hs : 1 < (ρ + (d : ℂ)).re := by simp only [Complex.add_re, Complex.ofReal_re]; linarith
  refine (hlim d hdpos).congr' (Filter.Eventually.of_forall fun k => ?_)
  rw [iteratedDeriv_logDeriv_zetaResidueUnit hs k, div_pow]
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp

#print axioms not_asymptoticAbscissaLaw_has_persistent_low_jets
#print axioms not_asymptoticAbscissaLaw_has_corrected_zeta_jet_limit

end GaloisForLFunctions.ZeroConfigurationGeometry
