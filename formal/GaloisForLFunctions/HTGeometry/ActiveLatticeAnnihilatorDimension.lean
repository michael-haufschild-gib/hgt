import GaloisForLFunctions.HTGeometry.ActiveLatticeRankBound
import GaloisForLFunctions.HTGeometry.DualAnnihilatorRank
import GaloisForLFunctions.HTGeometry.ActivePhaseLattice

/-!
# The dimension of the character stabilizer

The points of the torus whose every phase jet agrees with a given one form the coset of the
subgroup annihilating every active character.  That subgroup is cut out by the active characters,
so its tangent space at the identity is the space of complex vectors killed by all of them.

Its dimension is the codimension of the active lattice: the annihilator dimension plus the rank of
the lattice is the number of coordinates.  The rank of a lattice of integer characters is computed
after base change, first to the rationals — where a maximal independent family spans — and then to
the complex numbers, where independence survives.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-! ### Characters as complex vectors -/

/-- An integer character read as a complex vector. -/
def intCharacterToComplex (m : d → ℤ) : d → ℂ := fun j => (m j : ℂ)

/-- A rational character read as a complex vector. -/
def ratCharacterToComplex : (d → ℚ) →ₗ[ℚ] (d → ℂ) where
  toFun q := fun j => (q j : ℂ)
  map_add' a b := by funext j; exact Rat.cast_add (a j) (b j)
  map_smul' c a := by
    funext j
    simp [Pi.smul_apply, smul_eq_mul, Rat.cast_mul, Rat.smul_def]

omit [Fintype d] [DecidableEq d] in
@[simp] theorem ratCharacterToComplex_apply (q : d → ℚ) (j : d) :
    ratCharacterToComplex q j = (q j : ℂ) := rfl

omit [Fintype d] [DecidableEq d] in
theorem intCharacterToComplex_eq (m : d → ℤ) :
    intCharacterToComplex m = ratCharacterToComplex (intCharacterToRat m) := by
  funext j
  simp only [intCharacterToComplex, ratCharacterToComplex_apply, intCharacterToRat_apply]
  push_cast
  rfl

/-! ### The coordinate pairing -/

/-- The coordinate pairing, sending a vector to the covector it represents. -/
def coordPairing : (d → ℂ) →ₗ[ℂ] Module.Dual ℂ (d → ℂ) where
  toFun c :=
    { toFun := fun v => ∑ j, c j * v j
      map_add' := fun v w => by
        simp only [Pi.add_apply, mul_add]
        exact Finset.sum_add_distrib
      map_smul' := fun a v => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring }
  map_add' c c' := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, Pi.add_apply, add_mul]
    exact Finset.sum_add_distrib
  map_smul' a c := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq d] in
theorem coordPairing_apply (c v : d → ℂ) : coordPairing c v = ∑ j, c j * v j := rfl

theorem coordPairing_single (c : d → ℂ) (i : d) :
    coordPairing c (Pi.single i 1) = c i := by
  rw [coordPairing_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, mul_one]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem coordPairing_injective : Function.Injective (coordPairing (d := d)) := by
  intro c c' h
  funext i
  rw [← coordPairing_single c i, ← coordPairing_single c' i, h]

theorem coordPairing_surjective : Function.Surjective (coordPairing (d := d)) := by
  intro φ
  refine ⟨fun j => φ (Pi.single j 1), LinearMap.ext fun v => ?_⟩
  rw [coordPairing_apply, dual_apply_eq_sum φ v]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- Vectors and covectors are identified by the coordinate pairing. -/
def coordDual : (d → ℂ) ≃ₗ[ℂ] Module.Dual ℂ (d → ℂ) :=
  LinearEquiv.ofBijective coordPairing ⟨coordPairing_injective, coordPairing_surjective⟩

theorem coordDual_apply (c v : d → ℂ) : coordDual c v = ∑ j, c j * v j := rfl

/-! ### The annihilator of a character set -/

/-- **The tangent space of the character stabilizer.**  The complex vectors killed by every
character of the set. -/
def characterAnnihilator (S : Set (d → ℤ)) : Submodule ℂ (d → ℂ) :=
  Submodule.comap coordDual.toLinearMap
    (Submodule.span ℂ (intCharacterToComplex '' S)).dualAnnihilator

theorem mem_characterAnnihilator {S : Set (d → ℤ)} {c : d → ℂ} :
    c ∈ characterAnnihilator S ↔ ∀ m ∈ S, ∑ j, c j * (m j : ℂ) = 0 := by
  rw [characterAnnihilator, Submodule.mem_comap, Submodule.mem_dualAnnihilator]
  constructor
  · intro h m hm
    have hmem : intCharacterToComplex m ∈ Submodule.span ℂ (intCharacterToComplex '' S) :=
      Submodule.subset_span ⟨m, hm, rfl⟩
    simpa [coordDual_apply, intCharacterToComplex] using h _ hmem
  · intro h v hv
    refine Submodule.span_induction (p := fun x _ => coordDual c x = 0) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨m, hm, rfl⟩
      simpa [coordDual_apply, intCharacterToComplex] using h m hm
    · exact map_zero _
    · intro x y _ _ hx hy
      rw [map_add, hx, hy, add_zero]
    · intro a x _ hx
      rw [map_smul, hx, smul_zero]

/-- **Annihilator dimension is complementary to span dimension.** -/
theorem finrank_characterAnnihilator_add_finrank_span (S : Set (d → ℤ)) :
    Module.finrank ℂ (characterAnnihilator S)
        + Module.finrank ℂ (Submodule.span ℂ (intCharacterToComplex '' S))
      = Fintype.card d := by
  have hmap : characterAnnihilator S
      = Submodule.map coordDual.symm.toLinearMap
          (Submodule.span ℂ (intCharacterToComplex '' S)).dualAnnihilator :=
    Submodule.comap_equiv_eq_map_symm coordDual _
  have hfr : Module.finrank ℂ (characterAnnihilator S)
      = Module.finrank ℂ
          ((Submodule.span ℂ (intCharacterToComplex '' S)).dualAnnihilator) := by
    rw [hmap]
    exact LinearEquiv.finrank_map_eq coordDual.symm _
  have hdual := Subspace.finrank_add_finrank_dualAnnihilator_eq
    (Submodule.span ℂ (intCharacterToComplex '' S))
  have hcard : Module.finrank ℂ (d → ℂ) = Fintype.card d :=
    Module.finrank_fintype_fun_eq_card ℂ
  rw [hfr]
  omega

/-! ### The rank of a character lattice survives base change -/

omit [Fintype d] [DecidableEq d] in
theorem injective_ratCharacterToComplex :
    Function.Injective (ratCharacterToComplex : (d → ℚ) → (d → ℂ)) := by
  intro a b h
  funext j
  have := congrFun h j
  simpa using this

omit [Fintype d] [DecidableEq d] in
theorem image_intCharacterToComplex (S : Set (d → ℤ)) :
    intCharacterToComplex '' S = ratCharacterToComplex '' (intCharacterToRat '' S) := by
  rw [Set.image_image]
  exact Set.image_congr' fun m => intCharacterToComplex_eq m

omit [Fintype d] [DecidableEq d] in
/-- The rational scalar action on complex vectors is multiplication by the cast. -/
theorem rat_smul_complexVector (q : ℚ) (y : d → ℂ) : q • y = (q : ℂ) • y := by
  funext j
  simp [Rat.smul_def]

omit [Fintype d] [DecidableEq d] in
/-- A rational span maps into the complex span of the image. -/
theorem ratCharacterToComplex_mem_span {b : Set (d → ℚ)} {v : d → ℚ}
    (hv : v ∈ Submodule.span ℚ b) :
    ratCharacterToComplex v ∈ Submodule.span ℂ (ratCharacterToComplex '' b) := by
  refine Submodule.span_induction
    (p := fun x _ => ratCharacterToComplex x ∈
      Submodule.span ℂ (ratCharacterToComplex '' b)) ?_ ?_ ?_ ?_ hv
  · intro x hx
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro q x _ hx
    rw [map_smul, rat_smul_complexVector]
    exact Submodule.smul_mem _ _ hx

omit [DecidableEq d] in
/-- **The complex dimension of a character span is the rank of the lattice it generates.** -/
theorem finrank_span_intCharacterToComplex (S : Set (d → ℤ)) :
    (Module.finrank ℂ (Submodule.span ℂ (intCharacterToComplex '' S)) : Cardinal)
      = Module.rank ℤ (Submodule.span ℤ S) := by
  classical
  set T : Set (d → ℚ) := intCharacterToRat '' S with hT
  obtain ⟨b, hbT, hspan, hind⟩ := exists_linearIndependent ℚ T
  have hbrank : Module.rank ℚ (Submodule.span ℚ T) = Cardinal.mk b := by
    rw [← hspan]
    exact rank_span_set hind
  have hfin : b.Finite := by
    rw [← Cardinal.lt_aleph0_iff_set_finite, ← hbrank]
    calc Module.rank ℚ (Submodule.span ℚ T)
        ≤ Module.rank ℚ (d → ℚ) := Submodule.rank_le _
      _ = (Fintype.card d : Cardinal) := rank_fun'
      _ < Cardinal.aleph0 := Cardinal.natCast_lt_aleph0
  haveI : Fintype b := hfin.fintype
  -- the integral rank
  have hZmap : Module.rank ℤ (Submodule.span ℤ S)
      = Module.rank ℤ (Submodule.span ℤ T) := by
    rw [hT, ← Submodule.map_span]
    exact (Submodule.equivMapOfInjective _ injective_intCharacterToRat
      (Submodule.span ℤ S)).rank_eq
  have hRHS : Module.rank ℤ (Submodule.span ℤ S) = Cardinal.mk b := by
    rw [hZmap, rank_span_int_eq_rank_span_rat, hbrank]
  -- the complex dimension
  let e : Fin (Fintype.card b) ≃ b := (Fintype.equivFin b).symm
  let w : Fin (Fintype.card b) → (d → ℚ) := fun i => (e i : d → ℚ)
  have hwind : LinearIndependent ℚ w := hind.comp e e.injective
  have hwC : LinearIndependent ℂ (fun i => ratCharacterToComplex (w i)) :=
    linearIndependent_complex_of_rat hwind
  have hrange : Set.range (fun i => ratCharacterToComplex (w i))
      = ratCharacterToComplex '' b := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(e i : d → ℚ), (e i).2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e.symm ⟨x, hx⟩, by simp [w, e]⟩
  have hspanC : Submodule.span ℂ (intCharacterToComplex '' S)
      = Submodule.span ℂ (ratCharacterToComplex '' b) := by
    rw [image_intCharacterToComplex, ← hT]
    refine le_antisymm ?_ ?_
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨v, hv, rfl⟩
      exact ratCharacterToComplex_mem_span (hspan ▸ Submodule.subset_span hv)
    · exact Submodule.span_mono (Set.image_mono hbT)
  have hLHS : Module.finrank ℂ (Submodule.span ℂ (intCharacterToComplex '' S))
      = Fintype.card b := by
    rw [hspanC, ← hrange]
    simpa using finrank_span_eq_card hwC
  rw [hLHS, hRHS, Cardinal.mk_fintype]

/-! ### The stabilizer dimension of the active lattice -/

/-- **The stabilizer has the codimension of the active lattice.**  The all-jet level set through a
torus point is the coset of the subgroup annihilating every active character; the tangent space of
that subgroup has dimension `r - s`, where `r` is the number of phase coordinates and `s` the rank
of the active lattice. -/
theorem finrank_characterAnnihilator_add_rank_activeLattice (F : (d → ℂ) → ℂ) :
    (Module.finrank ℂ (characterAnnihilator (activeSupport F)) : Cardinal)
        + Module.rank ℤ (activeLattice F)
      = (Fintype.card d : Cardinal) := by
  have h := finrank_characterAnnihilator_add_finrank_span (activeSupport F)
  rw [activeLattice, ← finrank_span_intCharacterToComplex (activeSupport F),
    ← Nat.cast_add, h]

end

end GaloisForLFunctions.HTGeometry
