import GaloisForLFunctions.HTGeometry.KolchinSlopeDichotomy

/-!
# The Kolchin jet capacity of one reporter

The finite jet ranks of a reporter are bounded exactly when the reporter is differentially
algebraic, and the least such bound is its Kolchin jet capacity.  Hypertranscendence is the exact
failure of that finiteness: the rank then grows by one at every jet layer.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]

/-- The set of uniform bounds on the finite jet ranks of one reporter. -/
def kolchinJetBoundSet (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential E] (x : E) : Set ℕ :=
  {n : ℕ | ∀ r, kolchinJetRank F x r ≤ n}

/-- **The Kolchin jet capacity**: the least uniform bound on the finite jet ranks. -/
def kolchinJetCapacity (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential E] (x : E) : ℕ :=
  sInf (kolchinJetBoundSet F x)

/-- **Finiteness of the jet capacity is exactly differential algebraicity.** -/
theorem nonempty_kolchinJetBoundSet_iff [Differential F] [DifferentialAlgebra F E] [CharZero E]
    (x : E) :
    (kolchinJetBoundSet F x).Nonempty ↔ DifferentialAlgebraicOver F x := by
  constructor
  · rintro ⟨n, hn⟩
    by_contra hx
    have hht : HypertranscendentalOver F x := hx
    have hrank := kolchinJetRank_eq_of_hypertranscendentalOver hht n
    have := hn n
    rw [hrank] at this
    omega
  · intro hx
    obtain ⟨n, hn⟩ := exists_kolchinJetRank_le_of_differentialAlgebraicOver hx
    exact ⟨n, hn⟩

/-- The jet capacity really bounds every finite jet rank of a differentially algebraic reporter. -/
theorem kolchinJetRank_le_kolchinJetCapacity [Differential F] [DifferentialAlgebra F E]
    [CharZero E] {x : E} (hx : DifferentialAlgebraicOver F x) (r : ℕ) :
    kolchinJetRank F x r ≤ kolchinJetCapacity F x :=
  Nat.sInf_mem ((nonempty_kolchinJetBoundSet_iff x).mpr hx) r

/-- The jet capacity is the least such bound. -/
theorem kolchinJetCapacity_le {x : E} {n : ℕ} (hn : ∀ r, kolchinJetRank F x r ≤ n) :
    kolchinJetCapacity F x ≤ n :=
  Nat.sInf_le hn

/-- **Hypertranscendence is the exact failure of finite jet capacity.**  No natural number bounds
every finite jet rank of a hypertranscendental reporter. -/
theorem not_exists_bound_of_hypertranscendentalOver [Differential F] [DifferentialAlgebra F E]
    [CharZero E] {x : E} (hx : HypertranscendentalOver F x) :
    ¬ ∃ n : ℕ, ∀ r, kolchinJetRank F x r ≤ n := by
  intro h
  exact hx ((nonempty_kolchinJetBoundSet_iff x).mp h)

end

end GaloisForLFunctions.HTGeometry
