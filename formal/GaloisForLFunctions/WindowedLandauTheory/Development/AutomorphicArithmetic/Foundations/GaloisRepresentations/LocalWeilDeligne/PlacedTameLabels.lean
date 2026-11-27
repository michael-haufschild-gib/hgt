import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneOperations

/-! At a place of prime residue cardinality, the characteristic polynomial on
wild inertia invariants determines the local prime-field label of a Weil–Deligne class. -/

noncomputable section

open NumberField IsDedekindDomain IsLocalRing Module Polynomial
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal
open WindowedLandauTheory.CyclotomicNorms WindowedLandauTheory.NormalizedTypes
open GlobalTheory.TameKummer

namespace GlobalTheory.WeilDeligne.WD

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {p : ℕ} [Fact p.Prime]
variable {B : ValuationSubring ℂ} {κ : ResidueField B ≃+* Fbar p} {t : Fbar p →* ℂ}
variable (hp : A.valuation (p : Ω) < 1) (hNorm : normV w = p) (ht : IsTeich B κ t)
/-- The label is characterized by its monicity and by lifting its roots into
the inertia polynomial of the wild-invariant part. -/
theorem existsUnique_tameLabel
    (hp : A.valuation (p : Ω) < 1) (hNorm : normV w = p) (ht : IsTeich B κ t)
    (τ : Ine (F := E) A) (x : WD h) :
    ∃! f : (ZMod p)[X], f.Monic ∧ x.lpTame.charpoly (ineIncl h τ) =
      ((rootsBar f).map fun z => X - C (t z)).prod := by
  obtain ⟨n, a, rfl⟩ := exists_rep x
  simpa only [lpTame_mk, charpoly_mk] using a.existsUnique_tame_label hp hNorm ht τ

variable (τ : Ine (F := E) A)

/-- The monic prime-field polynomial of the tame inertia action. -/
def tameLabel (x : WD h) : (ZMod p)[X] :=
  (existsUnique_tameLabel hp hNorm ht τ x).exists.choose

theorem monic_tameLabel (x : WD h) : (tameLabel hp hNorm ht τ x).Monic :=
  (existsUnique_tameLabel hp hNorm ht τ x).exists.choose_spec.1

theorem charpoly_lpTame_eq (x : WD h) :
    x.lpTame.charpoly (ineIncl h τ) =
      ((rootsBar (tameLabel hp hNorm ht τ x)).map fun z => X - C (t z)).prod :=
  (existsUnique_tameLabel hp hNorm ht τ x).exists.choose_spec.2

theorem natDegree_tameLabel (x : WD h) :
    (tameLabel hp hNorm ht τ x).natDegree = x.lpTame.lpDim := by
  have he := charpoly_lpTame_eq hp hNorm ht τ x
  obtain ⟨n, a, rfl⟩ := exists_rep x
  rw [lpTame_mk, charpoly_mk] at he
  rw [lpTame_mk, lpDim_mk]
  exact a.natDegree_eq_finrank_tameSpace τ t he

theorem natDegree_tameLabel_le (x : WD h) :
    (tameLabel hp hNorm ht τ x).natDegree ≤ x.lpDim := by
  rw [natDegree_tameLabel]
  obtain ⟨n, a, rfl⟩ := exists_rep x
  rw [lpTame_mk, lpDim_mk, lpDim_mk]
  exact Submodule.finrank_le a.tameSpace

/-- A full-degree label gives the characteristic polynomial on the whole
space, since wild inertia then fixes the whole space. -/
theorem charpoly_eq_of_full_tameLabel (x : WD h)
    (hx : (tameLabel hp hNorm ht τ x).natDegree = x.lpDim) :
    x.charpoly (ineIncl h τ) =
      ((rootsBar (tameLabel hp hNorm ht τ x)).map fun z => X - C (t z)).prod := by
  rw [natDegree_tameLabel] at hx
  rw [← charpoly_lpTame_eq hp hNorm ht τ]
  obtain ⟨n, a, rfl⟩ := exists_rep x
  rw [lpTame_mk, lpDim_mk, lpDim_mk] at hx
  rw [lpTame_mk, charpoly_mk, charpoly_mk]
  exact WDRep.charpoly_eq_tamePart_of_tame (a.tame_of_finrank_tameSpace hx) _

/-- Full tame rank forces a trivial wild inertia characteristic polynomial. -/
theorem charpoly_wild_of_full_tameLabel (x : WD h)
    (hx : (tameLabel hp hNorm ht τ x).natDegree = x.lpDim) (σ : Weil h)
    (hσ : (σ : G E Ω) ∈ wildInertia A) : x.charpoly σ = (X - 1) ^ x.lpDim := by
  rw [natDegree_tameLabel] at hx
  obtain ⟨n, a, rfl⟩ := exists_rep x
  rw [lpTame_mk, lpDim_mk, lpDim_mk] at hx
  rw [charpoly_mk, lpDim_mk]
  exact WDRep.charpoly_wild_of_tame (a.tame_of_finrank_tameSpace hx) σ hσ

theorem tameLabel_sum (x y : WD h) :
    tameLabel hp hNorm ht τ (lpSum x y) =
      tameLabel hp hNorm ht τ x * tameLabel hp hNorm ht τ y := by
  let f := tameLabel hp hNorm ht τ x
  let g := tameLabel hp hNorm ht τ y
  have hf : f.Monic := monic_tameLabel hp hNorm ht τ x
  have hg : g.Monic := monic_tameLabel hp hNorm ht τ y
  have hfg : (rootsBar (f * g)) = rootsBar f + rootsBar g := by
    unfold rootsBar
    rw [Polynomial.map_mul, roots_mul (mul_ne_zero (hf.map _).ne_zero (hg.map _).ne_zero)]
  apply ((existsUnique_tameLabel hp hNorm ht τ (lpSum x y)).unique
    ⟨monic_tameLabel hp hNorm ht τ (lpSum x y), charpoly_lpTame_eq hp hNorm ht τ (lpSum x y)⟩)
  refine ⟨hf.mul hg, ?_⟩
  rw [lpTame_sum, charpoly_sum, charpoly_lpTame_eq hp hNorm ht τ x,
    charpoly_lpTame_eq hp hNorm ht τ y, hfg, Multiset.map_add, Multiset.prod_add]

theorem tameLabel_unramified_twist (x : WD h) (c : ℂˣ) :
    tameLabel hp hNorm ht τ (lpTwist x (unrChar h c) (isSmooth_unrChar h c)) =
      tameLabel hp hNorm ht τ x := by
  let y := lpTwist x (unrChar h c) (isSmooth_unrChar h c)
  apply ((existsUnique_tameLabel hp hNorm ht τ y).unique
    ⟨monic_tameLabel hp hNorm ht τ y, charpoly_lpTame_eq hp hNorm ht τ y⟩)
  refine ⟨monic_tameLabel hp hNorm ht τ x, ?_⟩
  change (lpTwist x (unrChar h c) (isSmooth_unrChar h c)).lpTame.charpoly (ineIncl h τ) = _
  rw [lpTame_unramified_twist, charpoly_unramified_twist_on_inertia]
  exact charpoly_lpTame_eq hp hNorm ht τ x

end GlobalTheory.WeilDeligne.WD
