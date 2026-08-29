import GaloisForLFunctions.HTGeometry.FlipDiagonalScattering

/-!
# The regular quantum anchor: positive-metric cut and flip conversion

Two exact consequences of the regular anchor `R(0) = -P`.

* Differentiating positive-metric unitarity at the anchor makes the Hamiltonian density
  `H = P R′(0)` anti-Hermitian, hence normal.
* Right multiplication by the flip moves the anchor from `-P` to `-1` and only permutes columns,
  so it leaves the family of matrix entries — and therefore the projective differential field —
  unchanged.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

/-- **The regular Hamiltonian density is anti-Hermitian.**  Differentiating `R(θ)ᴴ R(θ) = 1` at the
anchor gives `Aᴴ P + P A = 0` for `A = R′(0)`; with a self-adjoint anchor this says exactly that
`H = P A` is anti-Hermitian, hence normal. -/
theorem conjTranspose_anchorHamiltonian {n : Type*} [Fintype n] [DecidableEq n]
    {P A : Matrix n n ℂ} (hP : Pᴴ = P) (hcancel : Aᴴ * P + P * A = 0) :
    (P * A)ᴴ = -(P * A) := by
  rw [Matrix.conjTranspose_mul, hP]
  linear_combination (norm := module) hcancel

variable {κ : Type*} [DecidableEq κ] [Fintype κ] {R : Type*} [CommRing R]

/-- Right multiplication by the flip reads an entry at the transposed column pair. -/
theorem mul_pairFlip_apply (A : Matrix (κ × κ) (κ × κ) R) (i j : κ × κ) :
    (A * pairFlip κ R) i j = A i (j.2, j.1) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ((j.2, j.1) : κ × κ)]
  · simp
  · intro b _ hb
    have hne : ¬ (j = (b.2, b.1)) := by
      intro h
      exact hb (by rw [h])
    simp [hne]
  · intro h
    simp at h

/-- **The flip conversion does not change the entry family.**  Hence it does not change the
projective differential field either. -/
theorem range_entries_mul_pairFlip (A : Matrix (κ × κ) (κ × κ) R) :
    (Set.range fun q : (κ × κ) × (κ × κ) => (A * pairFlip κ R) q.1 q.2) =
      Set.range fun q : (κ × κ) × (κ × κ) => A q.1 q.2 := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨(q.1, (q.2.2, q.2.1)), ?_⟩
    show A q.1 (q.2.2, q.2.1) = (A * pairFlip κ R) q.1 q.2
    rw [mul_pairFlip_apply]
  · rintro ⟨q, rfl⟩
    refine ⟨(q.1, (q.2.2, q.2.1)), ?_⟩
    show (A * pairFlip κ R) q.1 (q.2.2, q.2.1) = A q.1 q.2
    rw [mul_pairFlip_apply]

/-- **The anchor moves from `-P` to `-1`.** -/
theorem neg_pairFlip_mul_pairFlip :
    (-pairFlip κ R) * pairFlip κ R = -1 := by
  rw [Matrix.neg_mul, pairFlip_mul_self]

end GaloisForLFunctions.HTGeometry
