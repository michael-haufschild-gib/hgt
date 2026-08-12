import GaloisForLFunctions.HTGeometry.TripticAtomIncidence
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentJet

/-!
# The higher-order line atoms

The `j`-th derivative of a line atom carries the same line of poles, now of order `j+1` and with the
single principal-part coefficient `(-1)ʲ j!`.  It has no other Laurent coefficient of negative index
anywhere: below its own order the base atom contributes nothing, between its order and zero the
falling product of the jet law vanishes, and off the line the base atom is analytic.

The jets are therefore *pure*: an atom of order `j+1` is invisible at every other order, so the
subtraction that normalizes a source order by order does not interfere with itself.

* `jetAtom`, `rowJetAtom`, `colJetAtom`;
* `laurentCoeff_jetAtom_line`, `laurentCoeff_jetAtom_of_ne_order`,
  `laurentCoeff_jetAtom_of_notMem`;
* `laurentCoeff_rowJetAtom_orbit`, `laurentCoeff_colJetAtom_orbit` — the incidence laws at order
  `j+1`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

variable {τ σ p : ℂ}

/-- The atom carrying one full `σ`-line of poles of order `j+1` through `q`. -/
def jetAtom (σ q : ℂ) (j : ℕ) : ℂ → ℂ := iteratedDeriv j (lineAtom σ q)

theorem meromorphicAt_jetAtom (hσ : 0 < σ.im) (q : ℂ) (j : ℕ) (z : ℂ) :
    MeromorphicAt (jetAtom σ q j) z :=
  meromorphicAt_iteratedDeriv (meromorphicAt_lineAtom hσ q z) j

theorem jetAtom_periodic (σ q : ℂ) (j : ℕ) (z : ℂ) :
    jetAtom σ q j (z + 1) = jetAtom σ q j z :=
  iteratedDeriv_periodic_triptic (lineAtom_periodic σ q) j z

theorem laurentCoeff_jetAtom (hσ : 0 < σ.im) (q : ℂ) (j : ℕ) (w : ℂ) (ℓ : ℤ) :
    laurentCoeff (jetAtom σ q j) w ℓ
      = (∏ i ∈ Finset.range j, ((ℓ : ℂ) + (i : ℂ) + 1))
          * laurentCoeff (lineAtom σ q) w (ℓ + (j : ℤ)) :=
  laurentCoeff_iteratedDeriv_eq (meromorphicAt_lineAtom hσ q w) j ℓ

/-- **At its own order the jet atom has coefficient `(-1)ʲ j!` on its line.** -/
theorem laurentCoeff_jetAtom_line (hσ : 0 < σ.im) (q : ℂ) (j : ℕ) (m n : ℤ) :
    laurentCoeff (jetAtom σ q j) (q + thetaHalfPeriod σ + (m : ℂ) + (n : ℂ) * σ)
        (-((j : ℤ) + 1))
      = (-1) ^ j * (j.factorial : ℂ) := by
  rw [laurentCoeff_jetAtom hσ, prod_range_neg_succ j,
    show -((j : ℤ) + 1) + (j : ℤ) = -1 from by ring,
    laurentCoeff_lineAtom_line hσ q m n, mul_one]

/-- **The jet atom is invisible at every other negative order.** -/
theorem laurentCoeff_jetAtom_of_ne_order (hσ : 0 < σ.im) (q : ℂ) (j : ℕ) (w : ℂ) {ℓ : ℤ}
    (hℓ : ℓ < 0) (hne : ℓ ≠ -((j : ℤ) + 1)) :
    laurentCoeff (jetAtom σ q j) w ℓ = 0 := by
  rw [laurentCoeff_jetAtom hσ]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [laurentCoeff_lineAtom_of_le hσ q w (by omega), mul_zero]
  · rw [prod_range_eq_zero_of_mem (by omega : -(j : ℤ) ≤ ℓ) (by omega : ℓ ≤ -1), zero_mul]

/-- **Off its line the jet atom is analytic.** -/
theorem laurentCoeff_jetAtom_of_notMem (hσ : 0 < σ.im) {q w : ℂ} (j : ℕ)
    (hw : ¬ ∃ m n : ℤ, w = q + thetaHalfPeriod σ + (m : ℂ) + (n : ℂ) * σ) {ℓ : ℤ} (hℓ : ℓ < 0) :
    laurentCoeff (jetAtom σ q j) w ℓ = 0 := by
  rw [laurentCoeff_jetAtom hσ]
  by_cases hcase : ℓ ≤ -((j : ℤ) + 1)
  · rw [laurentCoeff_lineAtom_of_notMem hσ hw (by omega : ℓ + (j : ℤ) < 0), mul_zero]
  · rw [prod_range_eq_zero_of_mem (by omega : -(j : ℤ) ≤ ℓ) (by omega : ℓ ≤ -1), zero_mul]

/-! ### Rows and columns at higher order -/

/-- The order-`j+1` atom whose poles are the row `p + nτ + ℤ + ℤσ`. -/
def rowJetAtom (τ σ p : ℂ) (j : ℕ) (n : ℤ) : ℂ → ℂ :=
  jetAtom σ (p + (n : ℂ) * τ - thetaHalfPeriod σ) j

/-- The order-`j+1` atom whose poles are the column `p + mσ + ℤ + ℤτ`. -/
def colJetAtom (τ σ p : ℂ) (j : ℕ) (m : ℤ) : ℂ → ℂ :=
  jetAtom τ (p + (m : ℂ) * σ - thetaHalfPeriod τ) j

/-- **Row incidence at order `j+1`.** -/
theorem laurentCoeff_rowJetAtom_orbit (hσ : 0 < σ.im)
    (hindep : ∀ n m j : ℤ, (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    (j : ℕ) (n n' m' : ℤ) :
    laurentCoeff (rowJetAtom τ σ p j n) (p + (n' : ℂ) * τ + (m' : ℂ) * σ) (-((j : ℤ) + 1))
      = if n' = n then (-1) ^ j * (j.factorial : ℂ) else 0 := by
  by_cases h : n' = n
  · subst h
    rw [if_pos rfl, rowJetAtom]
    have hpt : p + (n' : ℂ) * τ + (m' : ℂ) * σ
        = (p + (n' : ℂ) * τ - thetaHalfPeriod σ) + thetaHalfPeriod σ
            + ((0 : ℤ) : ℂ) + ((m' : ℤ) : ℂ) * σ := by
      push_cast
      ring
    rw [hpt]
    exact laurentCoeff_jetAtom_line hσ _ j 0 m'
  · rw [if_neg h, rowJetAtom]
    refine laurentCoeff_jetAtom_of_notMem hσ j ?_ (by omega)
    rintro ⟨a, b, hab⟩
    apply h
    have hrel : ((n' - n : ℤ) : ℂ) * τ + ((m' - b : ℤ) : ℂ) * σ + ((-a : ℤ) : ℂ) = 0 := by
      push_cast
      linear_combination hab
    obtain ⟨h1, _, _⟩ := hindep _ _ _ hrel
    omega

/-- **Column incidence at order `j+1`.** -/
theorem laurentCoeff_colJetAtom_orbit (hτ : 0 < τ.im)
    (hindep : ∀ n m j : ℤ, (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    (j : ℕ) (m n' m' : ℤ) :
    laurentCoeff (colJetAtom τ σ p j m) (p + (n' : ℂ) * τ + (m' : ℂ) * σ) (-((j : ℤ) + 1))
      = if m' = m then (-1) ^ j * (j.factorial : ℂ) else 0 := by
  by_cases h : m' = m
  · subst h
    rw [if_pos rfl, colJetAtom]
    have hpt : p + (n' : ℂ) * τ + (m' : ℂ) * σ
        = (p + (m' : ℂ) * σ - thetaHalfPeriod τ) + thetaHalfPeriod τ
            + ((0 : ℤ) : ℂ) + ((n' : ℤ) : ℂ) * τ := by
      push_cast
      ring
    rw [hpt]
    exact laurentCoeff_jetAtom_line hτ _ j 0 n'
  · rw [if_neg h, colJetAtom]
    refine laurentCoeff_jetAtom_of_notMem hτ j ?_ (by omega)
    rintro ⟨a, b, hab⟩
    apply h
    have hrel : ((n' - b : ℤ) : ℂ) * τ + ((m' - m : ℤ) : ℂ) * σ + ((-a : ℤ) : ℂ) = 0 := by
      push_cast
      linear_combination hab
    obtain ⟨_, h2, _⟩ := hindep _ _ _ hrel
    omega

theorem laurentCoeff_rowJetAtom_of_ne_order (hσ : 0 < σ.im) (j : ℕ) (n : ℤ) (w : ℂ) {ℓ : ℤ}
    (hℓ : ℓ < 0) (hne : ℓ ≠ -((j : ℤ) + 1)) :
    laurentCoeff (rowJetAtom τ σ p j n) w ℓ = 0 :=
  laurentCoeff_jetAtom_of_ne_order hσ _ j w hℓ hne

theorem laurentCoeff_colJetAtom_of_ne_order (hτ : 0 < τ.im) (j : ℕ) (m : ℤ) (w : ℂ) {ℓ : ℤ}
    (hℓ : ℓ < 0) (hne : ℓ ≠ -((j : ℤ) + 1)) :
    laurentCoeff (colJetAtom τ σ p j m) w ℓ = 0 :=
  laurentCoeff_jetAtom_of_ne_order hτ _ j w hℓ hne

theorem meromorphicAt_rowJetAtom (hσ : 0 < σ.im) (j : ℕ) (n : ℤ) (z : ℂ) :
    MeromorphicAt (rowJetAtom τ σ p j n) z :=
  meromorphicAt_jetAtom hσ _ j z

theorem meromorphicAt_colJetAtom (hτ : 0 < τ.im) (j : ℕ) (m : ℤ) (z : ℂ) :
    MeromorphicAt (colJetAtom τ σ p j m) z :=
  meromorphicAt_jetAtom hτ _ j z

theorem rowJetAtom_periodic (j : ℕ) (n : ℤ) (z : ℂ) :
    rowJetAtom τ σ p j n (z + 1) = rowJetAtom τ σ p j n z :=
  jetAtom_periodic _ _ j z

theorem colJetAtom_periodic (j : ℕ) (m : ℤ) (z : ℂ) :
    colJetAtom τ σ p j m (z + 1) = colJetAtom τ σ p j m z :=
  jetAtom_periodic _ _ j z

end

end GaloisForLFunctions.HTGeometry
