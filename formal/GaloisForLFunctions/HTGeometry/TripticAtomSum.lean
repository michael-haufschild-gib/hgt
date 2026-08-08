import GaloisForLFunctions.HTGeometry.TripticJetAtom
import GaloisForLFunctions.HTGeometry.TripticTransverseCoefficient

/-!
# The weighted atom sum of one order in one direction

Place, at every representative `q` of a finite list `R`, the `σ`-line atom of order `j+1` through
`q`, weighted by the row field at `q` divided by the atom's own principal coefficient `(-1)ʲ j!` and
by the number of members of `R` lying on the same line.  The multiplicity division makes the
construction independent of how many representatives of a line the list happens to contain.

The resulting function has, at every point, exactly the row field as its order-`(j+1)` coefficient —
provided every line carrying a nonzero row field is represented in `R` — and no other Laurent
coefficient of negative index at all, because the jets are pure.

* `rowAtomSum`;
* `laurentCoeff_rowAtomSum_of_ne_order`, `laurentCoeff_rowAtomSum_self`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

open scoped Classical

noncomputable section

variable {F : ℂ → ℂ} {τ σ : ℂ}

/-- Lying on the same `ℤ + ℤσ` line. -/
def sameLine (σ q r : ℂ) : Prop := ∃ a b : ℤ, r - q = (a : ℂ) + (b : ℂ) * σ

theorem sameLine_refl (σ q : ℂ) : sameLine σ q q := ⟨0, 0, by norm_num⟩

theorem sameLine_symm {σ q r : ℂ} (h : sameLine σ q r) : sameLine σ r q := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨-a, -b, by push_cast; linear_combination -hab⟩

theorem sameLine_trans {σ q r s : ℂ} (h₁ : sameLine σ q r) (h₂ : sameLine σ r s) :
    sameLine σ q s := by
  obtain ⟨a, b, hab⟩ := h₁
  obtain ⟨c, d, hcd⟩ := h₂
  exact ⟨a + c, b + d, by push_cast; linear_combination hab + hcd⟩

/-- The order-`(j+1)` coefficient of a placed atom: its own principal coefficient on its line, and
nothing off it. -/
theorem laurentCoeff_jetAtom_placed (hσ : 0 < σ.im) (q : ℂ) (j : ℕ) (w : ℂ) :
    laurentCoeff (jetAtom σ (q - thetaHalfPeriod σ) j) w (-((j : ℤ) + 1))
      = if sameLine σ q w then (-1) ^ j * (j.factorial : ℂ) else 0 := by
  by_cases h : sameLine σ q w
  · rw [if_pos h]
    obtain ⟨a, b, hab⟩ := h
    have hpt : w = (q - thetaHalfPeriod σ) + thetaHalfPeriod σ + (a : ℂ) + (b : ℂ) * σ := by
      linear_combination hab
    rw [hpt]
    exact laurentCoeff_jetAtom_line hσ _ j a b
  · rw [if_neg h]
    refine laurentCoeff_jetAtom_of_notMem hσ j ?_ (by omega)
    rintro ⟨a, b, hab⟩
    exact h ⟨a, b, by linear_combination hab⟩

/-- The multiplicity of a line inside a finite list of representatives. -/
def lineCount (σ : ℂ) (R : Finset ℂ) (q : ℂ) : ℕ := (R.filter (fun r => sameLine σ q r)).card

theorem lineCount_pos {σ : ℂ} {R : Finset ℂ} {q : ℂ} (hq : q ∈ R) : 0 < lineCount σ R q :=
  Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, sameLine_refl σ q⟩⟩

theorem lineCount_congr {σ : ℂ} (R : Finset ℂ) {q r : ℂ} (h : sameLine σ q r) :
    lineCount σ R q = lineCount σ R r := by
  refine congrArg Finset.card (Finset.filter_congr fun s _ => ?_)
  constructor
  · exact fun hs => sameLine_trans (sameLine_symm h) hs
  · exact fun hs => sameLine_trans h hs

/-- The weighted sum of the `σ`-line atoms of order `j+1` placed at a finite list. -/
def rowAtomSum (F : ℂ → ℂ) (τ σ : ℂ) (j : ℕ) (R : Finset ℂ) : ℂ → ℂ :=
  fun z => ∑ q ∈ R,
    (rowCoeff F τ (-((j : ℤ) + 1)) q /
        (((-1 : ℂ) ^ j * (j.factorial : ℂ)) * (lineCount σ R q : ℂ)))
      * jetAtom σ (q - thetaHalfPeriod σ) j z

/-- **The atom sum is invisible at every order but its own.** -/
theorem laurentCoeff_rowAtomSum_of_ne_order (hσ : 0 < σ.im) (j : ℕ) (R : Finset ℂ) (w : ℂ)
    {ℓ : ℤ} (hℓ : ℓ < 0) (hne : ℓ ≠ -((j : ℤ) + 1)) :
    laurentCoeff (rowAtomSum F τ σ j R) w ℓ = 0 := by
  have hmero : ∀ q ∈ R, MeromorphicAt (jetAtom σ (q - thetaHalfPeriod σ) j) w :=
    fun q _ => meromorphicAt_jetAtom hσ _ j w
  have hfun : rowAtomSum F τ σ j R = fun z => ∑ q ∈ R,
      (rowCoeff F τ (-((j : ℤ) + 1)) q /
          (((-1 : ℂ) ^ j * (j.factorial : ℂ)) * (lineCount σ R q : ℂ)))
        * jetAtom σ (q - thetaHalfPeriod σ) j z := rfl
  rw [hfun, laurentCoeff_sum R _ _ w ℓ hmero]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [laurentCoeff_jetAtom_of_ne_order hσ _ j w hℓ hne, mul_zero]

/-- **At its own order the atom sum reproduces the row field**, provided every line carrying a
nonzero row field has a representative in the list. -/
theorem laurentCoeff_rowAtomSum_self (hσ : 0 < σ.im) (j : ℕ) (R : Finset ℂ) (w : ℂ)
    (hinv : ∀ q : ℂ, sameLine σ q w →
      rowCoeff F τ (-((j : ℤ) + 1)) q = rowCoeff F τ (-((j : ℤ) + 1)) w)
    (hcover : rowCoeff F τ (-((j : ℤ) + 1)) w ≠ 0 → ∃ q ∈ R, sameLine σ q w) :
    laurentCoeff (rowAtomSum F τ σ j R) w (-((j : ℤ) + 1))
      = rowCoeff F τ (-((j : ℤ) + 1)) w := by
  classical
  have hmero : ∀ q ∈ R, MeromorphicAt (jetAtom σ (q - thetaHalfPeriod σ) j) w :=
    fun q _ => meromorphicAt_jetAtom hσ _ j w
  have hfun : rowAtomSum F τ σ j R = fun z => ∑ q ∈ R,
      (rowCoeff F τ (-((j : ℤ) + 1)) q /
          (((-1 : ℂ) ^ j * (j.factorial : ℂ)) * (lineCount σ R q : ℂ)))
        * jetAtom σ (q - thetaHalfPeriod σ) j z := rfl
  have hcard : (R.filter (fun q => sameLine σ q w)).card = lineCount σ R w := by
    rw [lineCount]
    refine congrArg Finset.card (Finset.filter_congr fun s _ => ?_)
    exact ⟨fun hs => sameLine_symm hs, fun hs => sameLine_symm hs⟩
  rw [hfun, laurentCoeff_sum R _ _ w (-((j : ℤ) + 1)) hmero]
  have hterm : ∀ q ∈ R,
      (rowCoeff F τ (-((j : ℤ) + 1)) q /
          (((-1 : ℂ) ^ j * (j.factorial : ℂ)) * (lineCount σ R q : ℂ)))
          * laurentCoeff (jetAtom σ (q - thetaHalfPeriod σ) j) w (-((j : ℤ) + 1))
        = if sameLine σ q w then
            rowCoeff F τ (-((j : ℤ) + 1)) w / (lineCount σ R w : ℂ) else 0 := by
    intro q hq
    rw [laurentCoeff_jetAtom_placed hσ q j w]
    by_cases h : sameLine σ q w
    · rw [if_pos h, if_pos h, hinv q h, lineCount_congr R h]
      have hcw : ((lineCount σ R w : ℂ)) ≠ 0 := by
        have hp := lineCount_pos (σ := σ) (R := R) hq
        rw [lineCount_congr R h] at hp
        exact Nat.cast_ne_zero.mpr (by omega)
      have hfac : ((j.factorial : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
      have hsign : ((-1 : ℂ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp
    · rw [if_neg h, if_neg h, mul_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  by_cases hz : rowCoeff F τ (-((j : ℤ) + 1)) w = 0
  · rw [hz]
    simp
  · obtain ⟨q₀, hq₀R, hq₀⟩ := hcover hz
    have hpos : 0 < lineCount σ R w := by
      rw [← hcard]
      exact Finset.card_pos.mpr ⟨q₀, Finset.mem_filter.mpr ⟨hq₀R, hq₀⟩⟩
    have hne : ((lineCount σ R w : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    field_simp

end

end GaloisForLFunctions.HTGeometry
