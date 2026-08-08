import GaloisForLFunctions.HTGeometry.TripticLineAtom

/-!
# How the line atoms meet a rank-two orbit

Place a `σ`-line atom so that its poles are the lattice `p + nτ + ℤ + ℤσ`.  Along the orbit
`p + n'τ + m'σ` its residue is `1` exactly on the row `n' = n`, and `0` on every other row —
independently of `m'`.  A `τ`-line atom placed on `p + mσ + ℤ + ℤτ` picks out the column `m' = m` in
the same way.

Both statements are pure `ℚ`-independence bookkeeping on top of the atom's complete principal part:
the incidence is decided by the row index alone because a lattice relation between `τ`, `σ` and `1`
must be trivial.

* `rowAtom`, `colAtom`;
* `laurentCoeff_rowAtom_orbit`, `laurentCoeff_colAtom_orbit` — the incidence laws;
* `laurentCoeff_rowAtom_of_le`, `laurentCoeff_colAtom_of_le` — no deeper coefficients anywhere.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

variable {τ σ p : ℂ}

/-- The atom whose poles are the row `p + nτ + ℤ + ℤσ`. -/
def rowAtom (τ σ p : ℂ) (n : ℤ) : ℂ → ℂ :=
  lineAtom σ (p + (n : ℂ) * τ - thetaHalfPeriod σ)

/-- The atom whose poles are the column `p + mσ + ℤ + ℤτ`. -/
def colAtom (τ σ p : ℂ) (m : ℤ) : ℂ → ℂ :=
  lineAtom τ (p + (m : ℂ) * σ - thetaHalfPeriod τ)

/-- **Row incidence.**  A `σ`-line atom has residue `1` at every orbit point of its own row and
none at any other. -/
theorem laurentCoeff_rowAtom_orbit (hσ : 0 < σ.im)
    (hindep : ∀ n m j : ℤ, (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    (n n' m' : ℤ) :
    laurentCoeff (rowAtom τ σ p n) (p + (n' : ℂ) * τ + (m' : ℂ) * σ) (-1)
      = if n' = n then 1 else 0 := by
  by_cases h : n' = n
  · subst h
    rw [if_pos rfl, rowAtom]
    have hpt : p + (n' : ℂ) * τ + (m' : ℂ) * σ
        = (p + (n' : ℂ) * τ - thetaHalfPeriod σ) + thetaHalfPeriod σ
            + ((0 : ℤ) : ℂ) + ((m' : ℤ) : ℂ) * σ := by
      push_cast
      ring
    rw [hpt]
    exact laurentCoeff_lineAtom_line hσ _ 0 m'
  · rw [if_neg h, rowAtom]
    refine laurentCoeff_lineAtom_of_notMem hσ ?_ (by norm_num)
    rintro ⟨j, k, hjk⟩
    apply h
    have hrel : ((n' - n : ℤ) : ℂ) * τ + ((m' - k : ℤ) : ℂ) * σ + ((-j : ℤ) : ℂ) = 0 := by
      push_cast
      linear_combination hjk
    obtain ⟨h1, _, _⟩ := hindep _ _ _ hrel
    omega

/-- **Column incidence.**  A `τ`-line atom has residue `1` at every orbit point of its own column
and none at any other. -/
theorem laurentCoeff_colAtom_orbit (hτ : 0 < τ.im)
    (hindep : ∀ n m j : ℤ, (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    (m n' m' : ℤ) :
    laurentCoeff (colAtom τ σ p m) (p + (n' : ℂ) * τ + (m' : ℂ) * σ) (-1)
      = if m' = m then 1 else 0 := by
  by_cases h : m' = m
  · subst h
    rw [if_pos rfl, colAtom]
    have hpt : p + (n' : ℂ) * τ + (m' : ℂ) * σ
        = (p + (m' : ℂ) * σ - thetaHalfPeriod τ) + thetaHalfPeriod τ
            + ((0 : ℤ) : ℂ) + ((n' : ℤ) : ℂ) * τ := by
      push_cast
      ring
    rw [hpt]
    exact laurentCoeff_lineAtom_line hτ _ 0 n'
  · rw [if_neg h, colAtom]
    refine laurentCoeff_lineAtom_of_notMem hτ ?_ (by norm_num)
    rintro ⟨j, k, hjk⟩
    apply h
    have hrel : ((n' - k : ℤ) : ℂ) * τ + ((m' - m : ℤ) : ℂ) * σ + ((-j : ℤ) : ℂ) = 0 := by
      push_cast
      linear_combination hjk
    obtain ⟨_, h2, _⟩ := hindep _ _ _ hrel
    omega

theorem laurentCoeff_rowAtom_of_le (hσ : 0 < σ.im) (n : ℤ) (w : ℂ) {ℓ : ℤ} (hℓ : ℓ ≤ -2) :
    laurentCoeff (rowAtom τ σ p n) w ℓ = 0 :=
  laurentCoeff_lineAtom_of_le hσ _ w hℓ

theorem laurentCoeff_colAtom_of_le (hτ : 0 < τ.im) (m : ℤ) (w : ℂ) {ℓ : ℤ} (hℓ : ℓ ≤ -2) :
    laurentCoeff (colAtom τ σ p m) w ℓ = 0 :=
  laurentCoeff_lineAtom_of_le hτ _ w hℓ

theorem meromorphicAt_rowAtom (hσ : 0 < σ.im) (n : ℤ) (z : ℂ) :
    MeromorphicAt (rowAtom τ σ p n) z :=
  meromorphicAt_lineAtom hσ _ z

theorem meromorphicAt_colAtom (hτ : 0 < τ.im) (m : ℤ) (z : ℂ) :
    MeromorphicAt (colAtom τ σ p m) z :=
  meromorphicAt_lineAtom hτ _ z

theorem rowAtom_periodic (n : ℤ) (z : ℂ) : rowAtom τ σ p n (z + 1) = rowAtom τ σ p n z :=
  lineAtom_periodic _ _ z

theorem colAtom_periodic (m : ℤ) (z : ℂ) : colAtom τ σ p m (z + 1) = colAtom τ σ p m z :=
  lineAtom_periodic _ _ z

end

end GaloisForLFunctions.HTGeometry
