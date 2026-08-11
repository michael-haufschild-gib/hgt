import GaloisForLFunctions.HTGeometry.TripticGlobalCoefficient

/-!
# The two transverse coefficient fields

The base-point-free formula splits every Laurent coefficient of a source of vanishing orbital
divisor into a *row* field and a *column* field,

`rowCoeff w = − Σ_{k ≥ 0} c_ℓ(Δ_τ F, w + kτ)`,  `colCoeff w = Σ_{j ≥ 1} c_ℓ(Δ_σ F, w − jσ)`,

with `c_ℓ(F, w) = rowCoeff w + colCoeff w`.  The row field is constant along `σ`-lines and the column
field along `τ`-lines, because the principal parts of the two boundary functions are invariant in
exactly those directions.  Both are `1`-periodic.

These are the coefficients of the line atoms: `rowCoeff` weights the `σ`-line through `w` and
`colCoeff` the `τ`-line.

* `rowCoeff`, `colCoeff`, `laurentCoeff_eq_rowCoeff_add_colCoeff`;
* `rowCoeff_invariant`, `colCoeff_invariant` — constancy along the respective lines;
* `rowCoeff_eq_zero_of_forall`, `colCoeff_eq_zero_of_forall` — where they vanish.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

variable {F : ℂ → ℂ} {τ σ : ℂ}

/-- The row coefficient at `w`: the transverse sum of the `τ`-boundary function along the forward
`τ`-ray. -/
def rowCoeff (F : ℂ → ℂ) (τ : ℂ) (ℓ : ℤ) (w : ℂ) : ℂ :=
  -(∑ᶠ k : ℕ, laurentCoeff (fun z => F (z + τ) - F z) (w + ((k : ℤ) : ℂ) * τ) ℓ)

/-- The column coefficient at `w`: the transverse sum of the `σ`-boundary function along the
backward `σ`-ray. -/
def colCoeff (F : ℂ → ℂ) (σ : ℂ) (ℓ : ℤ) (w : ℂ) : ℂ :=
  ∑ᶠ j : ℕ, laurentCoeff (fun z => F (z + σ) - F z) (w + ((-((j : ℤ) + 1) : ℤ) : ℂ) * σ) ℓ

/-- **The principal part splits into the two transverse fields.** -/
theorem laurentCoeff_eq_rowCoeff_add_colCoeff
    (hF : MeromorphicOn F Set.univ)
    (hper : PeriodicOneGerm F)
    {Cst : ℂ} (hmixed : MixedConstGerm F τ σ Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im)
    (hindep : ∀ n m j : ℤ, (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    {ℓ : ℤ} (hℓ : ℓ < 0) (w : ℂ)
    (hvanish : ∑ᶠ m : ℤ, laurentCoeff (fun z => F (z + σ) - F z) (w + (m : ℂ) * σ) ℓ = 0) :
    laurentCoeff F w ℓ = rowCoeff F τ ℓ w + colCoeff F σ ℓ w :=
  laurentCoeff_eq_transverse_sums hF hper hmixed hτ hσ hindep hℓ w hvanish

/-- **The row field is constant in any direction that preserves the `τ`-boundary principal
parts** — in particular along `σ`-lines. -/
theorem rowCoeff_invariant {ℓ : ℤ} {h : ℂ}
    (hinv : ∀ a : ℂ, laurentCoeff (fun z => F (z + τ) - F z) (a + h) ℓ
      = laurentCoeff (fun z => F (z + τ) - F z) a ℓ) (w : ℂ) :
    rowCoeff F τ ℓ (w + h) = rowCoeff F τ ℓ w := by
  rw [rowCoeff, rowCoeff]
  congr 1
  refine finsum_congr fun k => ?_
  rw [show w + h + ((k : ℤ) : ℂ) * τ = (w + ((k : ℤ) : ℂ) * τ) + h from by ring, hinv]

/-- **The column field is constant in any direction that preserves the `σ`-boundary principal
parts** — in particular along `τ`-lines. -/
theorem colCoeff_invariant {ℓ : ℤ} {h : ℂ}
    (hinv : ∀ a : ℂ, laurentCoeff (fun z => F (z + σ) - F z) (a + h) ℓ
      = laurentCoeff (fun z => F (z + σ) - F z) a ℓ) (w : ℂ) :
    colCoeff F σ ℓ (w + h) = colCoeff F σ ℓ w := by
  rw [colCoeff, colCoeff]
  refine finsum_congr fun j => ?_
  rw [show w + h + ((-((j : ℤ) + 1) : ℤ) : ℂ) * σ
      = (w + ((-((j : ℤ) + 1) : ℤ) : ℂ) * σ) + h from by ring, hinv]

/-- The row field vanishes where the forward `τ`-ray meets no pole. -/
theorem rowCoeff_eq_zero_of_forall {ℓ : ℤ} {w : ℂ}
    (h : ∀ k : ℕ, laurentCoeff (fun z => F (z + τ) - F z) (w + ((k : ℤ) : ℂ) * τ) ℓ = 0) :
    rowCoeff F τ ℓ w = 0 := by
  rw [rowCoeff, finsum_congr h, finsum_zero, neg_zero]

/-- The column field vanishes where the backward `σ`-ray meets no pole. -/
theorem colCoeff_eq_zero_of_forall {ℓ : ℤ} {w : ℂ}
    (h : ∀ j : ℕ, laurentCoeff (fun z => F (z + σ) - F z)
      (w + ((-((j : ℤ) + 1) : ℤ) : ℂ) * σ) ℓ = 0) :
    colCoeff F σ ℓ w = 0 := by
  rw [colCoeff, finsum_congr h, finsum_zero]

/-- A nonzero row coefficient forces a pole of the `τ`-boundary function on the forward ray. -/
theorem exists_ne_zero_of_rowCoeff_ne_zero {ℓ : ℤ} {w : ℂ} (h : rowCoeff F τ ℓ w ≠ 0) :
    ∃ k : ℕ, laurentCoeff (fun z => F (z + τ) - F z) (w + ((k : ℤ) : ℂ) * τ) ℓ ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  exact h (rowCoeff_eq_zero_of_forall hcon)

/-- A nonzero column coefficient forces a pole of the `σ`-boundary function on the backward ray. -/
theorem exists_ne_zero_of_colCoeff_ne_zero {ℓ : ℤ} {w : ℂ} (h : colCoeff F σ ℓ w ≠ 0) :
    ∃ j : ℕ, laurentCoeff (fun z => F (z + σ) - F z)
      (w + ((-((j : ℤ) + 1) : ℤ) : ℂ) * σ) ℓ ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  exact h (colCoeff_eq_zero_of_forall hcon)

end

end GaloisForLFunctions.HTGeometry
