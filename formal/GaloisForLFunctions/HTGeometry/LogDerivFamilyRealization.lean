import GaloisForLFunctions.HTGeometry.ExponentialFamilyRealization

/-!
# Every jet point with nonzero value is the jet point of a logarithmic-derivative pair

Prescribing finitely many derivatives of `E` at a point, with nonzero value, is realized by a
polynomial; near the point that polynomial is nonvanishing, so its logarithmic derivative is smooth
and the pair `(E'/E, E)` solves `E' = H E`.

This is the analytic surjectivity for the jet substitution attached to `E' = H E`, the exact
analogue of the exponential realization but without any logarithm: the carrier is produced from the
solution, not the solution from the carrier.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **Realization of logarithmic-derivative jets.**  Any prescription of finitely many derivatives
with nonzero value at the base point is realized on a neighbourhood by a pair `(H, E)` solving
`E' = H E`. -/
theorem exists_logDerivFamily_realizing_jets {m : ℕ} (n : ℕ) (z₀ : ℂ) (y : Fin m → ℕ → ℂ)
    (hy : ∀ i, y i 0 ≠ 0) :
    ∃ (V : Set ℂ) (H E : Fin m → ℂ → ℂ), IsOpen V ∧ z₀ ∈ V ∧
      (∀ i, ∀ w ∈ V, ContDiffAt ℂ (⊤ : ℕ∞) (H i) w) ∧
      (∀ i, ∀ w ∈ V, ContDiffAt ℂ (⊤ : ℕ∞) (E i) w) ∧
      (∀ i, ∀ w ∈ V, E i w ≠ 0) ∧
      (∀ i, ∀ w ∈ V, deriv (E i) w = iteratedDeriv 0 (H i) w * E i w) ∧
      (∀ i, ∀ k ≤ n, iteratedDeriv k (E i) z₀ = y i k) := by
  classical
  choose f hfsmooth hfcont hfjet using fun i : Fin m => exists_smooth_iteratedDeriv_eq n z₀ (y i)
  have hfContDiff : ∀ i, ContDiff ℂ (⊤ : ℕ∞) (f i) := by
    intro i
    rw [contDiff_iff_contDiffAt]
    exact hfsmooth i
  have hfderiv : ∀ i, ContDiff ℂ (⊤ : ℕ∞) (deriv (f i)) := by
    intro i
    exact (contDiff_infty_iff_deriv.1 (hfContDiff i)).2
  have hf0 : ∀ i, f i z₀ = y i 0 := by
    intro i
    have h := hfjet i 0 (Nat.zero_le n)
    rwa [iteratedDeriv_zero] at h
  have hfz0ne : ∀ i, f i z₀ ≠ 0 := by
    intro i
    rw [hf0 i]
    exact hy i
  refine ⟨{w : ℂ | ∀ i, f i w ≠ 0}, fun i w => deriv (f i) w / f i w, f, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hset : {w : ℂ | ∀ i, f i w ≠ 0} = ⋂ i : Fin m, (f i) ⁻¹' ({0}ᶜ) := by
      ext w
      simp [Set.mem_iInter]
    rw [hset]
    exact isOpen_iInter_of_finite fun i =>
      (hfcont i).isOpen_preimage _ isOpen_compl_singleton
  · exact hfz0ne
  · intro i w hw
    exact ((hfderiv i).contDiffAt).div (hfsmooth i w) (hw i)
  · intro i w _
    exact hfsmooth i w
  · intro i w hw
    exact hw i
  · intro i w hw
    rw [iteratedDeriv_zero]
    exact (div_mul_cancel₀ (deriv (f i) w) (hw i)).symm
  · exact hfjet

end

end GaloisForLFunctions.HTGeometry
