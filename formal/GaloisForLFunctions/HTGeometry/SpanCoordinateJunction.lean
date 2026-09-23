/-
# Reading a witness in the interaction basis

A Hamiltonian that lies in the real span of a finite interaction family *is* a shell Hamiltonian:
it has real coefficients in that family.  That is the only step separating a witness produced on an
extension chart from the globalisation over the shell, which is stated in the shell's own
coefficients.

Main results:
* `exists_realCoeff_of_mem_span` — real coordinates in the interaction basis.
* `exists_mem_real_shell_quadraticRate_ne_zero_of_mem_span` — **the globalisation with the witness
  given as a Hamiltonian rather than as a coefficient vector**.
-/
import GaloisForLFunctions.HTGeometry.ShellQuadraticRateGlobalisation

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S] {m : ℕ}

omit [Fintype S] [DecidableEq S] in
private theorem real_smul_matrix (r : ℝ) (N : Matrix S S ℂ) : r • N = ((r : ℂ)) • N := by
  ext x y
  simp [Matrix.smul_apply, Complex.real_smul]

omit [Fintype S] [DecidableEq S] in
/-- **Real coordinates in the interaction basis.**  A member of the real span of a finite family of
matrices is a real combination of them. -/
theorem exists_realCoeff_of_mem_span (P : Fin m → Matrix S S ℂ) {H : Matrix S S ℂ}
    (hH : H ∈ Submodule.span ℝ (Set.range P)) :
    ∃ θ : Fin m → ℝ, H = ∑ a, ((θ a : ℝ) : ℂ) • P a := by
  obtain ⟨θ, hθ⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hH
  refine ⟨θ, ?_⟩
  rw [← hθ]
  exact Finset.sum_congr rfl fun a _ => real_smul_matrix (θ a) (P a)

/-- **The globalisation with the witness given as a Hamiltonian.**  A Hamiltonian in the real span
of the interaction family, carrying a simple spectrum on which no relabeling of the quadratic-rate
relation holds, forces the same failure somewhere inside every nonempty open set of real
coefficients. -/
theorem exists_mem_real_shell_quadraticRate_ne_zero_of_mem_span
    (P : Fin m → Matrix S S ℂ) (c : S → ℂ) (κ : ℂ)
    {H₀ : Matrix S S ℂ} (hspan : H₀ ∈ Submodule.span ℝ (Set.range P))
    {energy₀ : S → ℂ} (hinj₀ : Function.Injective energy₀)
    (hroot₀ : ∀ i, matrixCharpolyRelation (H₀, energy₀ i) = 0)
    (hfail : ∀ σ : Equiv.Perm S,
      (∑ j, c (σ.symm j) * energy₀ j) ^ (2 : ℕ) - κ * ∑ j, energy₀ j ^ (2 : ℕ) ≠ 0)
    {V : Set (Fin m → ℝ)} (hVopen : IsOpen V) (hVne : V.Nonempty) :
    ∃ q ∈ V, ∀ energy : S → ℂ, Function.Injective energy →
      (∀ i, matrixCharpolyRelation (∑ a, ((q a : ℝ) : ℂ) • P a, energy i) = 0) →
      ∀ σ : Equiv.Perm S,
        (∑ j, c (σ.symm j) * energy j) ^ (2 : ℕ) - κ * ∑ j, energy j ^ (2 : ℕ) ≠ 0 := by
  obtain ⟨θ, hθ⟩ := exists_realCoeff_of_mem_span P hspan
  refine exists_mem_real_shell_quadraticRate_ne_zero P c κ (θ₀ := fun a => ((θ a : ℝ) : ℂ))
    hinj₀ ?_ hfail hVopen hVne
  intro i
  rw [← hθ]
  exact hroot₀ i

end

end GaloisForLFunctions.HTGeometry
