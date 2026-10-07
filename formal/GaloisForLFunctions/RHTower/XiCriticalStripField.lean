import GaloisForLFunctions.HTGeometry.MeromorphicDomainField
import GaloisForLFunctions.RHTower.XiCriticalStripFactorRoots
import Mathlib.Analysis.Convex.PathConnected

/-!
# Exact source square-class collapse on the critical strip

Restriction maps the actual global meromorphic plane field into the field of
all meromorphic functions on the open critical strip. Xi remains nonsquare
there, since an existing odd-order Xi zero lies in the strip. Both signed
source factors become squares, so all marked radicands have the same
nontrivial square class. No condition on zero location beyond the established
open-strip theorem is assumed.
-/

open Complex Filter Topology
namespace RHTower.XiGlobalKummer
open GaloisForLFunctions.HTGeometry

/-- The actual open critical strip as a connected meromorphic domain. -/
def stripDomain : MeromorphicDomainData where
  carrier := criticalStrip
  isOpen := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  isPreconnected := by
    have hc : Convex ℝ criticalStrip :=
      (convex_Ioo (0 : ℝ) 1).linear_preimage Complex.reLm
    exact hc.isPreconnected
  nonempty := ⟨(1 / 2 : ℂ), by constructor <;> norm_num⟩

abbrev StripField := stripDomain.Field

/-- Xi remains nonsquare on the whole critical strip, witnessed by its odd zero. -/
theorem strip_xi_not_isSquare : ¬ IsSquare (algebraMap K StripField xiElement) := by
  intro h
  change IsSquare (stripDomain.ofMeromorphic xi
    (fun z _ => (xi_differentiable.analyticAt z).meromorphicAt)) at h
  obtain ⟨g, hg, hsq⟩ := stripDomain.analytic_sqrt_of_isSquare
    (fun z _ => xi_differentiable.analyticAt z) h
  obtain ⟨z, hz, hodd⟩ := exists_odd_order_zero_xi
  have hzU : z ∈ stripDomain.carrier := xi_zero_re_mem_open_unit hz
  have heq : (fun w => g w ^ 2) =ᶠ[𝓝 z] xi := by
    filter_upwards [stripDomain.isOpen.mem_nhds hzU] with w hw
    exact hsq w hw
  have hord := analyticOrderAt_congr heq
  have heven : Even (analyticOrderAt xi z).toNat := by
    rw [← hord, show (fun w => g w ^ 2) = g ^ (2 : ℕ) by rfl,
      analyticOrderAt_pow (hg z hzU)]
    rw [show (2 • analyticOrderAt g z).toNat = 2 * (analyticOrderAt g z).toNat by
      rw [nsmul_eq_mul, ENat.toNat_mul]
      norm_num]
    exact even_two.mul_right _
  exact (Nat.not_even_iff_odd.mpr hodd) heven

/-- Every negative source factor becomes square under faithful analytic restriction. -/
theorem strip_factor_isSquare {n : ℕ} (hn : 1 ≤ n) :
    IsSquare (algebraMap K StripField (factorElement n)) := by
  refine ⟨stripDomain.ofMeromorphic (deletionStripRoot n)
    (fun z hz => (deletionStripRoot_analytic hn z hz).meromorphicAt), ?_⟩
  change stripDomain.ofMeromorphic (deletionFactor n)
    (fun z _ => ((deletionFactor_differentiable n).analyticAt z).meromorphicAt) = _
  rw [stripDomain.ofMeromorphic_mul]
  apply (stripDomain.ofMeromorphic_eq_iff _ _).mpr
  intro z hz
  filter_upwards [nhdsWithin_le_nhds (stripDomain.isOpen.mem_nhds hz)] with w hw
  simpa only [Pi.mul_apply, pow_two] using (deletionStripRoot_sq hn hw).symm

/-- Every positive source factor also becomes square on the analytic domain. -/
theorem strip_augmentation_isSquare {n : ℕ} (hn : 1 ≤ n) :
    IsSquare (algebraMap K StripField (augmentationElement n)) := by
  refine ⟨stripDomain.ofMeromorphic (augmentationStripRoot n)
    (fun z hz => (augmentationStripRoot_analytic hn z hz).meromorphicAt), ?_⟩
  change stripDomain.ofMeromorphic (augmentationFactor n)
    (fun z _ => ((augmentationFactor_differentiable n).analyticAt z).meromorphicAt) = _
  rw [stripDomain.ofMeromorphic_mul]
  apply (stripDomain.ofMeromorphic_eq_iff _ _).mpr
  intro z hz
  filter_upwards [nhdsWithin_le_nhds (stripDomain.isOpen.mem_nhds hz)] with w hw
  simpa only [Pi.mul_apply, pow_two] using (augmentationStripRoot_sq hn hw).symm

/-- The source's marked radicands still define a genuine quadratic extension. -/
theorem strip_radicand_not_isSquare (n : ℕ) :
    ¬ IsSquare (algebraMap K StripField (radicand n)) := by
  intro h
  have hf := strip_factor_isSquare (n := n + 2) (by omega)
  have hq := h.div hf
  have hne : algebraMap K StripField (factorElement (n + 2)) ≠ 0 := by
    exact (map_ne_zero (algebraMap K StripField)).mpr (factorElement_ne_zero (by omega))
  have he : algebraMap K StripField (radicand n) /
      algebraMap K StripField (factorElement (n + 2)) = algebraMap K StripField xiElement := by
    rw [radicand, map_mul, mul_div_cancel_right₀ _ hne]
  rw [he] at hq
  exact strip_xi_not_isSquare hq

/-- All marked radicands have the same nontrivial square class after restriction. -/
theorem strip_radicand_product_isSquare (m n : ℕ) :
    IsSquare (algebraMap K StripField (radicand m) *
      algebraMap K StripField (radicand n)) := by
  have h := ((IsSquare.sq (algebraMap K StripField xiElement)).mul
    (strip_factor_isSquare (n := m + 2) (by omega))).mul
      (strip_factor_isSquare (n := n + 2) (by omega))
  have he : algebraMap K StripField (radicand m) * algebraMap K StripField (radicand n) =
      (algebraMap K StripField xiElement) ^ 2 *
        algebraMap K StripField (factorElement (m + 2)) *
          algebraMap K StripField (factorElement (n + 2)) := by
    simp only [radicand, map_mul]
    ring
  rw [he]
  exact h

end RHTower.XiGlobalKummer
