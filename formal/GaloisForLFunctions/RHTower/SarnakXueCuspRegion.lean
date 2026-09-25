import GaloisForLFunctions.RHTower.SarnakXueCuspMode
import GaloisForLFunctions.RHTower.MaassFiniteDeckCuspidalTail
import GaloisForLFunctions.RHTower.MaassCongruenceL2

open MeasureTheory UpperHalfPlane ModularGroup Set

/-!
# The cusp region of the modular cell

The trace mass of a `Γ(p)` Maass form over `𝒟 ∩ {y > Y}` (`Y ≥ 1`) equals its tail mass
`∫_Y^∞ (∫_0^1 density) dy/y²` (`fd_above_eq_tailMass`). Combined with the modal cusp estimate, for
`0 < λ < 1/4` and `p = N + 1 ≥ 2`: `p ∫_{𝒟 ∩ {y > p}} density ≤ max(1, p/(4π)) ∫_𝒟 density`
(`fd_cusp_fraction`).
-/

namespace GaloisForLFunctions.RHTower.SarnakXueCuspRegion

open GaloisForLFunctions.RHTower
open GaloisForLFunctions.RHTower.SelbergMaassCongruenceTrace
open GaloisForLFunctions.RHTower.SelbergMaassCongruenceAverage
open GaloisForLFunctions.RHTower.MaassCongruenceL2
open GaloisForLFunctions.RHTower.SelbergMaassMean

variable (N : ℕ) {lam : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- The cusp part of the cell carries exactly the tail mass. -/
theorem fd_above_eq_tailMass {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ z in fd ∩ {z : ℍ | Y < z.im}, density N f z) = tailMass N f Y := by
  have h := MaassFiniteDeckDirichlet.cusp_normSq_tail_eq_iterated (sourceVector N f)
    (sourceVector_continuous N f) (sourceVector_memLp N f) hY
  simp_rw [sourceVector_norm_sq] at h
  rw [h, tailMass]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  have hy0 : 0 < y := lt_of_lt_of_le one_pos (hY.trans (le_of_lt hy))
  have hper := (density_slice_periodic N f hy0).intervalIntegral_add_eq (-(1 / 2 : ℝ)) 0
  simp only [zero_add] at hper
  rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at hper
  simp only
  rw [hper, inv_pow, div_eq_inv_mul]

open SarnakXueCuspMode in
/-- **Cusp fraction of the trace mass.** For `p = N + 1 ≥ 2` and `0 < λ < 1/4`,
`p ∫_{𝒟 ∩ {y > p}} density ≤ max(1, p/(4π)) ∫_𝒟 density`. -/
theorem fd_cusp_fraction (hN : 1 ≤ N) (lam : Ioo (0 : ℝ) (1 / 4))
    (g : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) :
    ((N + 1 : ℕ) : ℝ) * (∫ z in fd ∩ {z : ℍ | ((N + 1 : ℕ) : ℝ) < z.im}, density N g z) ≤
      edge N * ∫ z in fd, density N g z := by
  have hp1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ N + 1 by omega)
  have hp0 : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by linarith
  rw [fd_above_eq_tailMass N g hp1, tailMass_eq_sum N lam g hp0, Finset.mul_sum]
  have h1 : tailMass N g 1 ≤ ∫ z in fd, density N g z := by
    rw [← fd_above_eq_tailMass N g le_rfl]
    exact setIntegral_mono_set (density_integrable N g : IntegrableOn (density N g) fd volume)
      (Filter.Eventually.of_forall (fun z => density_nonneg N g z))
      (Filter.Eventually.of_forall inter_subset_left)
  have h2 : ∑ q : Deck N, ((N + 1 : ℕ) : ℝ) *
      ∫ y in Ioi ((N + 1 : ℕ) : ℝ), SelbergMaassFlux.mass N (quotientForm N g q) y / y ^ (2 : ℕ) ≤
      edge N * tailMass N g 1 := by
    rw [tailMass_eq_sum N lam g one_pos, Finset.mul_sum]
    exact Finset.sum_le_sum (fun q _ => mass_tail_fraction N hN lam (quotientForm N g q))
  exact h2.trans (mul_le_mul_of_nonneg_left h1 (edge_pos N).le)

end GaloisForLFunctions.RHTower.SarnakXueCuspRegion
