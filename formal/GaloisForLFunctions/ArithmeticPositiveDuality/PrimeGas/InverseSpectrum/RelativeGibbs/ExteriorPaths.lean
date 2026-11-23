import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.LineRange
import Mathlib.Analysis.Normed.Module.Connected

/-! # Paths between missing waves

An affine complex line joining two exterior points meets a linear subspace
at most once. A punctured complex plane supplies a path around that point.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set

/-- The exterior of every proper complex linear subspace is path connected, including dense subspaces. -/
theorem pathConnected_subspace_exterior {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (R : Submodule ℂ H) (hn : (Rᶜ : Set H).Nonempty) : IsPathConnected (Rᶜ : Set H) := by
  refine isPathConnected_iff.mpr ⟨hn,?_⟩
  intro u hu v hv
  let m (z : ℂ) := u+z • (v-u)
  have h0 : m 0 = u := by simp [m]
  have h1 : m 1 = v := by simp [m]
  have hm : Continuous m := continuous_const.add (continuous_id.smul continuous_const)
  have unique {z w : ℂ} (hz : m z ∈ R) (hw : m w ∈ R) : z = w := by
    by_contra hne
    have hs : (z-w) • (v-u) ∈ R := by
      have e : (z-w) • (v-u) = m z-m w := by dsimp only [m]; rw [sub_smul]; abel
      rw [e]
      exact R.sub_mem hz hw
    have hd := (R.smul_mem_iff (sub_ne_zero.mpr hne)).mp hs
    exact hu ((R.add_mem_iff_left (R.smul_mem z hd)).mp hz)
  have havoid : ∃ p : ℂ, 0 ≠ p ∧ 1 ≠ p ∧ ∀ z ≠ p, m z ∉ R := by
    by_cases he : ∃ z, m z ∈ R
    · obtain ⟨p,hp⟩ := he
      refine ⟨p,?_,?_,fun z hz hmz => hz (unique hmz hp)⟩
      · rintro rfl
        exact hu (h0 ▸ hp)
      · rintro rfl
        exact hv (h1 ▸ hp)
    · exact ⟨-1,by norm_num,by norm_num,fun z _ hz => he ⟨z,hz⟩⟩
  obtain ⟨p,hp₀,hp₁,hp⟩ := havoid
  have hc := isPathConnected_compl_singleton_of_one_lt_rank (E := ℂ) (by rw [Complex.rank_real_complex]; norm_num) p
  have hj := hc.joinedIn 0 (show (0:ℂ) ∈ ({p}ᶜ : Set ℂ) from hp₀) 1 (show (1:ℂ) ∈ ({p}ᶜ : Set ℂ) from hp₁)
  have him : m '' ({p}ᶜ : Set ℂ) ⊆ (Rᶜ : Set H) := by rintro _ ⟨z,hz,rfl⟩; exact hp z hz
  simpa only [h0,h1] using (hj.map hm).mono him

instance missingWavePathConnected : PathConnectedSpace MissingWave :=
  isPathConnected_iff_pathConnectedSpace.mp (pathConnected_subspace_exterior
    (LinearMap.range criticalOperator.toLinearMap) ⟨reciprocalTail,reciprocalTail_outside⟩)

#print axioms pathConnected_subspace_exterior
#print axioms missingWavePathConnected

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
