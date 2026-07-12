import GaloisForLFunctions.HTGeometry.DifferentialOperatorToeplitzRank

/-!
# Finite-support structural operator rows

A finite family of facetwise finitely supported operator coefficients uses one common finite set of
source-orbit coordinates.  Restricting every row to that common support preserves and reflects
linear independence.  Combined with the Toeplitz matroid law, this converts facetwise Laurent or
group-ring coefficients into an exact nonlinear differential-independence statement.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open scoped Differential

noncomputable section

/-- The common coefficient support of a finite family of facetwise finitely supported rows. -/
def finiteFinsuppRowSupport
    {P ι σ G : Type*} [Semiring P] [Fintype ι] [Fintype σ]
    [DecidableEq σ] [DecidableEq G]
    (Q : ι → σ → G →₀ P) : Finset (σ × G) :=
  Finset.univ.biUnion fun i =>
    Finset.univ.biUnion fun s => (Q i s).support.image (Prod.mk s)

/-- Every nonzero row coefficient belongs to the common finite support. -/
theorem mem_finiteFinsuppRowSupport_of_ne
    {P ι σ G : Type*} [Semiring P] [Fintype ι] [Fintype σ]
    [DecidableEq σ] [DecidableEq G]
    (Q : ι → σ → G →₀ P) {i : ι} {s : σ} {g : G}
    (h : Q i s g ≠ 0) :
    (s, g) ∈ finiteFinsuppRowSupport Q := by
  simp only [finiteFinsuppRowSupport, Finset.mem_biUnion, Finset.mem_univ,
    true_and]
  exact ⟨i, s, Finset.mem_image.mpr ⟨g, Finsupp.mem_support_iff.mpr h, rfl⟩⟩

/-- The finite source-orbit index type used by one finite structural operator family. -/
abbrev FiniteFinsuppRowIndex
    {P ι σ G : Type*} [Semiring P] [Fintype ι] [Fintype σ]
    [DecidableEq σ] [DecidableEq G]
    (Q : ι → σ → G →₀ P) :=
  {q : σ × G // q ∈ finiteFinsuppRowSupport Q}

/-- Expand nested facetwise finitely supported coefficients into a finite operator matrix. -/
def finiteFinsuppOperatorRows
    {P ι σ G : Type*} [Semiring P] [Fintype ι] [Fintype σ]
    [DecidableEq σ] [DecidableEq G]
    (Q : ι → σ → G →₀ P) :
    ι → FiniteFinsuppRowIndex Q → P :=
  fun i q => Q i q.1.1 q.1.2

/-- Finite coefficient expansion preserves and reflects polynomial-row independence. -/
theorem linearIndependent_finiteFinsuppOperatorRows_iff
    {P ι σ G : Type*} [Ring P] [Fintype ι] [Fintype σ]
    [DecidableEq ι] [DecidableEq σ] [DecidableEq G]
    (Q : ι → σ → G →₀ P) :
    LinearIndependent P (finiteFinsuppOperatorRows Q) ↔
      LinearIndependent P Q := by
  classical
  rw [Fintype.linearIndependent_iff, Fintype.linearIndependent_iff]
  constructor
  · intro h A hrel i
    apply h A
    funext q
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.zero_apply, finiteFinsuppOperatorRows]
    have hs := congrArg
      (fun f : σ → G →₀ P => f q.1.1 q.1.2) hrel
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
      Finsupp.zero_apply] at hs
    change (Finsupp.lapply (R := P) q.1.2)
      (∑ x, A x • Q x q.1.1) = 0 at hs
    rw [map_sum] at hs
    simpa only [map_smul, finiteFinsuppOperatorRows] using hs
  · intro h A hrel i
    apply h A
    funext s
    apply Finsupp.ext
    intro g
    by_cases hzero : ∀ j, Q j s g = 0
    · simp [hzero]
    · push Not at hzero
      obtain ⟨j, hj⟩ := hzero
      let q : FiniteFinsuppRowIndex Q :=
        ⟨(s, g), mem_finiteFinsuppRowSupport_of_ne Q hj⟩
      have hq := congrArg
        (fun f : FiniteFinsuppRowIndex Q → P => f q) hrel
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
        finiteFinsuppOperatorRows, q] at hq
      rw [Finset.sum_apply]
      simp only [Pi.zero_apply, Finsupp.zero_apply]
      change (Finsupp.lapply (R := P) g) (∑ x, A x • Q x s) = 0
      rw [map_sum]
      simpa only [map_smul] using hq

/-- **Finite-support structural operator law.**  Acting on a differentially independent source
packet, facetwise finitely supported operator rows produce a differentially independent output
family exactly when the original nested coefficient rows are polynomially independent. -/
theorem differentialIndependent_finiteFinsuppOperatorRows_iff
    {C K ι σ G : Type*}
    [Field C] [Field K] [Algebra C K] [Differential K]
    [Fintype ι] [Fintype σ]
    [DecidableEq ι] [DecidableEq σ] [DecidableEq G]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (Q : ι → σ → G →₀ Polynomial C)
    (x : FiniteFinsuppRowIndex Q → K)
    (hx : DifferentialIndependent C x) :
    DifferentialIndependent C
        (differentialOperatorRowApply (finiteFinsuppOperatorRows Q) x) ↔
      LinearIndependent (Polynomial C) Q := by
  rw [differentialIndependent_differentialOperatorRows_iff
    hconst (finiteFinsuppOperatorRows Q) x hx]
  exact linearIndependent_finiteFinsuppOperatorRows_iff Q

end

end GaloisForLFunctions.HTGeometry
