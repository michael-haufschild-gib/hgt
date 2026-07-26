import GaloisForLFunctions.HTGeometry.FundamentalParallelogram
import GaloisForLFunctions.HTGeometry.EllipticPrincipalJet

/-!
# Finitely many poles in a fundamental parallelogram

A meromorphic function on `ℂ` has finitely many poles in any compact set, because the analytic
divisor has finite support there.  Applied to the fundamental parallelogram of two `ℝ`-independent
steps, this makes the pole set of a lattice-periodic meromorphic function finite *modulo the
lattice*: every pole is an integer translate of one of finitely many representatives.

That finite list of representatives is what makes the target of the principal-jet map
finite-dimensional, and hence what makes the counting argument work.

* **`finite_poles_of_isCompact`** — finitely many poles in a compact set;
* **`finite_poles_fundamentalParallelogram`** — in particular in the fundamental parallelogram;
* `exists_pole_representative` — every pole is a lattice translate of one of them.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **A meromorphic function has finitely many poles in a compact set.** -/
theorem finite_poles_of_isCompact {f : ℂ → ℂ} (hf : MeromorphicOn f Set.univ)
    {K : Set ℂ} (hK : IsCompact K) :
    {z | z ∈ K ∧ meromorphicOrderAt f z < 0}.Finite := by
  have hfK : MeromorphicOn f K := fun z _ => hf z (Set.mem_univ z)
  refine Set.Finite.subset ((MeromorphicOn.divisor f K).finiteSupport hK) ?_
  rintro z ⟨hzK, hzord⟩
  have hval : (MeromorphicOn.divisor f K) z = (meromorphicOrderAt f z).untopD 0 :=
    MeromorphicOn.divisor_apply hfK hzK
  rw [Function.mem_support, hval]
  have hne : meromorphicOrderAt f z ≠ ⊤ := by
    intro htop
    rw [htop] at hzord
    exact absurd hzord (by simp)
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hne
  rw [← hk] at hzord ⊢
  simp only [WithTop.untopD_coe]
  intro h0
  rw [h0] at hzord
  exact absurd hzord (by simp)

/-- **A meromorphic function has finitely many poles in the fundamental parallelogram.** -/
theorem finite_poles_fundamentalParallelogram {f : ℂ → ℂ} (hf : MeromorphicOn f Set.univ)
    (w₁ w₂ : ℂ) :
    {z | z ∈ fundamentalParallelogram w₁ w₂ ∧ meromorphicOrderAt f z < 0}.Finite :=
  finite_poles_of_isCompact hf (isCompact_fundamentalParallelogram w₁ w₂)

/-- **Every pole is a bounded integer translate of a pole in the fundamental parallelogram**, for a
function whose order is invariant under the two translations. -/
theorem exists_pole_representative {f : ℂ → ℂ} {w₁ w₂ : ℂ}
    (hindep : LinearIndependent ℝ ![w₁, w₂])
    (hord : ∀ (m n : ℤ) (z : ℂ),
      meromorphicOrderAt f (z - (m • w₁ + n • w₂)) = meromorphicOrderAt f z)
    {z : ℂ} (hz : meromorphicOrderAt f z < 0) :
    ∃ (m n : ℤ), z - (m • w₁ + n • w₂) ∈ fundamentalParallelogram w₁ w₂ ∧
      meromorphicOrderAt f (z - (m • w₁ + n • w₂)) < 0 := by
  obtain ⟨C, _, hcov⟩ := exists_bounded_intCombination hindep
  obtain ⟨m, n, hmem, _, _⟩ := hcov z
  exact ⟨m, n, hmem, by rw [hord m n z]; exact hz⟩

end GaloisForLFunctions.HTGeometry
