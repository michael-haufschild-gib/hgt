import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.JointEulerFactorization
import GaloisForLFunctions.RHTower.SquarefreeCarlemanLogExpansion
import GaloisForLFunctions.RHTower.EulerFisherPoincareBoundary

/-!
# The regular part of the prime logarithm

The singularity of `P(s)=Σ_p p^(-s)` at one is exactly `-log(s-1)`.
The regular part is the logarithm of the zeta pole unit minus the
higher-prime-power Euler remainder. This fixes the logarithm branch
needed when the prime phases shift the singularity.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- The analytic regular part of the prime logarithm near one. -/
def primeLogRegularPart (s : ℂ) : ℂ :=
  Complex.log (zetaResidueFactor s) - hullRem s (twist 0)

/-- The prime part and higher-power remainder recover the canonical Euler logarithm. -/
theorem coronaPrimeZeta_add_hullRem {s : ℂ} (hs : 1 < s.re) :
    coronaPrimeZeta s + hullRem s (twist 0) = canonicalEulerLogZeta s := by
  rw [canonicalEulerLogZeta_eq_primeLog hs, coronaPrimeZeta, hullRem,
    ← (summable_coronaPrimeEigenvalue hs).tsum_add
      (summable_localRem (norm_twist_prime 0) (by linarith only [hs]))]
  apply tsum_congr
  intro p
  simp only [coronaPrimeEigenvalue, localRem, eulerVar, powCoeff, twist_trivial,
    mul_one]
  ring

/-- The regular part at one is the negative higher-power prime sum. -/
theorem primeLogRegularPart_one : primeLogRegularPart 1 = -hullRem 1 (twist 0) := by
  simp only [primeLogRegularPart, zetaResidueFactor_one, Complex.log_one, zero_sub]

theorem analyticAt_primeLogRegularPart_one : AnalyticAt ℂ primeLogRegularPart 1 := by
  have hlog : AnalyticAt ℂ (fun s => Complex.log (zetaResidueFactor s)) 1 :=
    (differentiable_zetaResidueFactor.analyticAt 1).clog (by
      rw [zetaResidueFactor_one]
      simp)
  exact hlog.sub (analyticOnNhd_hullRem (norm_twist_prime 0) 1 (by
    change (1 / 2 : ℝ) < 1
    norm_num))

private theorem primeLogRegularPart_real {β : ℝ} (hβ : 1 < β) :
    coronaPrimeZeta (β : ℂ) + Complex.log ((β : ℂ) - 1) =
      primeLogRegularPart (β : ℂ) := by
  have hs : 1 < (β : ℂ).re := hβ
  have hβ1 : (β : ℂ) ≠ 1 := by exact_mod_cast hβ.ne'
  have hpos : 0 < β - 1 := sub_pos.mpr hβ
  have hz : zetaResidueFactor (β : ℂ) =
      (((β - 1) * Real.exp (eulerLogMoment β) : ℝ) : ℂ) := by
    rw [zetaResidueFactor_of_ne hβ1, riemannZeta_ofReal_eq_exp_eulerLogMoment hβ]
    push_cast
    rfl
  have hlog : Complex.log (zetaResidueFactor (β : ℂ)) =
      Complex.log ((β : ℂ) - 1) + canonicalEulerLogZeta (β : ℂ) := by
    have hc : (β : ℂ) - 1 = ((β - 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [hz, hc, ← Complex.ofReal_log hpos.le,
      ← Complex.ofReal_log (mul_pos hpos (Real.exp_pos _)).le,
      Real.log_mul hpos.ne' (Real.exp_ne_zero _), Real.log_exp,
      canonicalEulerLogZeta_ofReal, ofReal_add]
  rw [primeLogRegularPart, hlog, ← coronaPrimeZeta_add_hullRem hs]
  ring


/-- The prime logarithm has a branch-fixed analytic regular part at one. -/
theorem exists_primeLogRegularPart_germ :
    ∃ r : ℝ, 0 < r ∧ AnalyticOnNhd ℂ primeLogRegularPart (ball 1 r) ∧
      ∀ s : ℂ, s ∈ ball 1 r → 1 < s.re →
        coronaPrimeZeta s + Complex.log (s - 1) = primeLogRegularPart s := by
  obtain ⟨r, hr, hG⟩ := analyticAt_primeLogRegularPart_one.exists_ball_analyticOnNhd
  let D : Set ℂ := ball 1 r ∩ {s | 1 < s.re}
  have hF : AnalyticOnNhd ℂ (fun s => coronaPrimeZeta s + Complex.log (s - 1)) D := by
    intro s hs
    have hse : 1 < s.re := hs.2
    have hP : AnalyticAt ℂ coronaPrimeZeta s := by
      let b := (1 + s.re) / 2
      have hb : 1 < b := by dsimp [b]; linarith only [hse]
      have hbs : b < s.re := by dsimp [b]; linarith only [hse]
      exact (differentiableOn_coronaPrimeZeta hb).analyticAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hbs)
    have hslit : s - 1 ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      simpa only [Complex.sub_re, Complex.one_re] using sub_pos.mpr hs.2
    exact hP.add ((analyticAt_id.sub analyticAt_const).clog hslit)
  let m : ℝ := 1 + r / 2
  have hm : 1 < m := by dsimp [m]; linarith only [hr]
  have hmD : (m : ℂ) ∈ D := by
    refine ⟨?_, hm⟩
    rw [mem_ball, dist_eq_norm]
    have he : (m : ℂ) - 1 = ((r / 2 : ℝ) : ℂ) := by dsimp [m]; push_cast; ring
    rw [he, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith only [hr] : 0 < r / 2)]
    linarith only [hr]
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] m) (𝓝[≠] (m : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact fun h => hx (Complex.ofReal_injective h)
  have he : ∀ᶠ x : ℝ in 𝓝[≠] m,
      coronaPrimeZeta (x : ℂ) + Complex.log ((x : ℂ) - 1) = primeLogRegularPart (x : ℂ) := by
    filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds hm)] with x hx
    exact primeLogRegularPart_real hx
  have hid := hF.eqOn_of_preconnected_of_frequently_eq
    (hG.mono inter_subset_left)
    ((convex_ball (1 : ℂ) r).inter (convex_halfSpace_re_gt 1)).isPreconnected
    hmD (ht.frequently he.frequently)
  exact ⟨r, hr, hG, fun s hs hse => hid ⟨hs, hse⟩⟩

#print axioms exists_primeLogRegularPart_germ

end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
