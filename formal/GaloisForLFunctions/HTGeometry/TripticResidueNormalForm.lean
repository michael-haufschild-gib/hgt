import GaloisForLFunctions.HTGeometry.TripticAtomIncidence
import GaloisForLFunctions.HTGeometry.TripticSeparatedPrincipalPart

/-!
# The residue normal form on one orbit

A finite combination of row and column atoms has, at an orbit point `p + n'τ + m'σ`, residue exactly
`a n' + b m'`: each row atom contributes its coefficient on its own row and nothing elsewhere, and
likewise for the columns.  That is precisely the shape a source of vanishing orbital divisor has, by
the finitely supported separation of its coefficient array.

Hence every mixed-constraint source whose orbital divisor vanishes agrees with an explicit finite
combination of theta-source translates in all its simple residues along the orbit.

* `atomCombination`, `laurentCoeff_atomCombination`;
* `exists_atomCombination_residue_normalForm` — the normal form on one orbit.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

variable {F : ℂ → ℂ} {τ σ p : ℂ}

/-- The row and column atoms of an orbit, indexed jointly. -/
def atomFamily (τ σ p : ℂ) : ℤ ⊕ ℤ → ℂ → ℂ :=
  Sum.elim (rowAtom τ σ p) (colAtom τ σ p)

/-- A finite combination of row and column atoms. -/
def atomCombination (τ σ p : ℂ) (s t : Finset ℤ) (a b : ℤ → ℂ) : ℂ → ℂ :=
  fun z => ∑ i ∈ s.disjSum t, (Sum.elim a b i) * atomFamily τ σ p i z

/-- **The residues of an atom combination along the orbit.** -/
theorem laurentCoeff_atomCombination (hτ : 0 < τ.im) (hσ : 0 < σ.im)
    (hindep : ∀ n m j : ℤ, (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    (s t : Finset ℤ) (a b : ℤ → ℂ) (n' m' : ℤ) :
    laurentCoeff (atomCombination τ σ p s t a b) (p + (n' : ℂ) * τ + (m' : ℂ) * σ) (-1)
      = (if n' ∈ s then a n' else 0) + (if m' ∈ t then b m' else 0) := by
  classical
  have hmero : ∀ i ∈ s.disjSum t,
      MeromorphicAt (atomFamily τ σ p i) (p + (n' : ℂ) * τ + (m' : ℂ) * σ) := by
    rintro (n | m) _
    · exact meromorphicAt_rowAtom hσ n _
    · exact meromorphicAt_colAtom hτ m _
  have hfun : atomCombination τ σ p s t a b
      = fun z => ∑ i ∈ s.disjSum t, (Sum.elim a b i) * atomFamily τ σ p i z := rfl
  rw [hfun, laurentCoeff_sum _ _ _ _ _ hmero, Finset.sum_disjSum]
  have hrow : ∀ n ∈ s, (Sum.elim a b (Sum.inl n)) *
      laurentCoeff (atomFamily τ σ p (Sum.inl n)) (p + (n' : ℂ) * τ + (m' : ℂ) * σ) (-1)
      = if n' = n then a n else 0 := by
    intro n _
    rw [Sum.elim_inl, atomFamily, Sum.elim_inl, laurentCoeff_rowAtom_orbit hσ hindep n n' m']
    split <;> simp
  have hcol : ∀ m ∈ t, (Sum.elim a b (Sum.inr m)) *
      laurentCoeff (atomFamily τ σ p (Sum.inr m)) (p + (n' : ℂ) * τ + (m' : ℂ) * σ) (-1)
      = if m' = m then b m else 0 := by
    intro m _
    rw [Sum.elim_inr, atomFamily, Sum.elim_inr, laurentCoeff_colAtom_orbit hτ hindep m n' m']
    split <;> simp
  rw [Finset.sum_congr rfl hrow, Finset.sum_congr rfl hcol, Finset.sum_ite_eq, Finset.sum_ite_eq]

/-- **The residue normal form on one orbit.**  If the total simple-residue mass of `Δ_σ F` along the
`σ`-orbit through `p` vanishes, then `F` has the same residue as an explicit finite combination of
theta-source translates at every point of the rank-two orbit through `p`. -/
theorem exists_atomCombination_residue_normalForm
    (hF : MeromorphicOn F Set.univ)
    (hper : ∀ z : ℂ, F (z + 1) = F z)
    {Cst : ℂ} (hmixed : ∀ z : ℂ, F (z + τ + σ) - F (z + τ) - F (z + σ) + F z = Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im)
    (hindep : ∀ n m j : ℤ, (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    (p : ℂ)
    (hvanish : ∑ᶠ m : ℤ, laurentCoeff (fun z => F (z + σ) - F z) (p + (m : ℂ) * σ) (-1) = 0) :
    ∃ (s t : Finset ℤ) (a b : ℤ → ℂ), ∀ n' m' : ℤ,
      laurentCoeff F (p + (n' : ℂ) * τ + (m' : ℂ) * σ) (-1)
        = laurentCoeff (atomCombination τ σ p s t a b)
            (p + (n' : ℂ) * τ + (m' : ℂ) * σ) (-1) := by
  classical
  obtain ⟨a, b, hafin, hbfin, hsep⟩ :=
    exists_finiteSupport_separation_of_orbit_sum_eq_zero hF hper hmixed hτ hσ hindep p
      (by norm_num : (-1 : ℤ) < 0) hvanish
  refine ⟨hafin.toFinset, hbfin.toFinset, a, b, fun n' m' => ?_⟩
  rw [hsep n' m', laurentCoeff_atomCombination hτ hσ hindep]
  have ha : (if n' ∈ hafin.toFinset then a n' else 0) = a n' := by
    split
    · rfl
    · rename_i hcon
      have : a n' = 0 := by
        by_contra hne
        exact hcon (hafin.mem_toFinset.mpr hne)
      rw [this]
  have hb : (if m' ∈ hbfin.toFinset then b m' else 0) = b m' := by
    split
    · rfl
    · rename_i hcon
      have : b m' = 0 := by
        by_contra hne
        exact hcon (hbfin.mem_toFinset.mpr hne)
      rw [this]
  rw [ha, hb]

end

end GaloisForLFunctions.HTGeometry
