import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.TameLabelRank

/-! Isomorphism classes of finite-dimensional Weil–Deligne representations.
Dimension, monodromy vanishing, inertia and characteristic polynomials descend
to classes. Taking wild inertia invariants also respects isomorphism. -/

noncomputable section

open NumberField IsDedekindDomain Module Polynomial
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.TameKummer

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

namespace WDRep

variable {V V' V'' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
  [AddCommGroup V''] [Module ℂ V''] [FiniteDimensional ℂ V'']

/-- An intertwiner for both the Weil action and monodromy. -/
def Iso (a : WDRep h V) (b : WDRep h V') : Prop :=
  ∃ e : V ≃ₗ[ℂ] V', (∀ σ v, e (a.ρ σ v) = b.ρ σ (e v)) ∧ ∀ v, e (a.N v) = b.N (e v)

omit [IsAlgClosure E Ω] in
theorem Iso.refl (a : WDRep h V) : a.Iso a := ⟨.refl _ _, fun _ _ => rfl, fun _ => rfl⟩

omit [IsAlgClosure E Ω] in
theorem Iso.symm {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) : b.Iso a := by
  obtain ⟨e, hρ, hN⟩ := hab
  exact ⟨e.symm, fun σ v => by simp [e.symm_apply_eq, hρ], fun v => by simp [e.symm_apply_eq, hN]⟩

omit [IsAlgClosure E Ω] in
theorem Iso.trans {a : WDRep h V} {b : WDRep h V'} {c : WDRep h V''}
    (hab : a.Iso b) (hbc : b.Iso c) : a.Iso c := by
  obtain ⟨e, hρ, hN⟩ := hab
  obtain ⟨e', hρ', hN'⟩ := hbc
  exact ⟨e.trans e', fun σ v => by simp [hρ, hρ'], fun v => by simp [hN, hN']⟩

/-- Conjugate the Weil action and monodromy through a linear equivalence. -/
def transport (a : WDRep h V) (e : V ≃ₗ[ℂ] V') : WDRep h V' where
  ρ := (e.conjAlgEquiv ℂ : End ℂ V →* End ℂ V').comp a.ρ
  N := e.conjAlgEquiv ℂ a.N
  smooth := a.smooth.of_le fun σ hσ => by simp [hσ]
  semisimple σ := by
    change (e.conj (a.ρ σ)).IsSemisimple
    refine (e.isSemisimple_iff (a.ρ σ) (e.conj (a.ρ σ)) (LinearMap.ext fun v => ?_)).mp
      (a.semisimple σ)
    simp [LinearEquiv.conj_apply]
  nilpotent := a.nilpotent.map (e.conjAlgEquiv ℂ)
  comm σ := by
    show e.conjAlgEquiv ℂ (a.ρ σ) * _ = _ • (_ * e.conjAlgEquiv ℂ (a.ρ σ))
    rw [← map_mul, a.comm, map_smul, map_mul]

omit [IsAlgClosure E Ω] in
theorem iso_transport (a : WDRep h V) (e : V ≃ₗ[ℂ] V') : a.Iso (a.transport e) :=
  ⟨e, fun σ v => by
    change _ = e.conjAlgEquiv ℂ (a.ρ σ) (e v)
    simp, fun v => by simp [transport]⟩

omit [IsAlgClosure E Ω] in
theorem Iso.finrank_eq {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) :
    finrank ℂ V = finrank ℂ V' := hab.choose.finrank_eq

omit [IsAlgClosure E Ω] in
theorem Iso.charpoly_eq {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) (σ : Weil h) :
    (a.ρ σ).charpoly = (b.ρ σ).charpoly := by
  obtain ⟨e, hρ, -⟩ := hab
  rw [← LinearEquiv.charpoly_conj e]
  congr 1
  ext v
  simp [LinearEquiv.conj_apply, hρ]

omit [IsAlgClosure E Ω] in
theorem Iso.monodromy_eq_zero {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) (ha : a.N = 0) :
    b.N = 0 := by
  obtain ⟨e, -, hN⟩ := hab
  refine LinearMap.ext fun v => ?_
  obtain ⟨v, rfl⟩ := e.surjective v
  rw [← hN, ha]
  simp

omit [IsAlgClosure E Ω] in
theorem Iso.ρ_eq_one {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) {σ : Weil h}
    (ha : a.ρ σ = 1) : b.ρ σ = 1 := by
  obtain ⟨e, hρ, -⟩ := hab
  refine LinearMap.ext fun v => ?_
  obtain ⟨v, rfl⟩ := e.surjective v
  rw [← hρ, ha]
  rfl

/-- An intertwiner restricts to wild inertia invariants. -/
theorem Iso.tamePart {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) : a.tamePart.Iso b.tamePart := by
  obtain ⟨e, hρ, hN⟩ := hab
  have he (x : V) : e x ∈ b.tameSpace ↔ x ∈ a.tameSpace := by
    rw [b.mem_tameSpace, a.mem_tameSpace]
    simp only [← hρ, e.injective.eq_iff]
  let e' : a.tameSpace ≃ₗ[ℂ] b.tameSpace :=
    { toFun := fun x => ⟨e x, (he x).mpr x.2⟩
      invFun := fun y => ⟨e.symm y, (he (e.symm y)).mp (by simpa only [e.apply_symm_apply] using y.2)⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y)
      map_add' := fun x y => Subtype.ext (map_add e (x : V) (y : V))
      map_smul' := fun c x => Subtype.ext (map_smul e c (x : V)) }
  exact ⟨e', fun σ x => Subtype.ext (hρ σ x), fun x => Subtype.ext (hN x)⟩

end WDRep

def isoSetoid (h : IsPlaceOver A w) : Setoid (Σ n : ℕ, WDRep h (Fin n → ℂ)) where
  r a b := a.2.Iso b.2
  iseqv := ⟨fun a => .refl a.2, WDRep.Iso.symm, WDRep.Iso.trans⟩

/-- Weil–Deligne representations up to linear isomorphism. -/
def WD (h : IsPlaceOver A w) : Type := Quotient (isoSetoid h)

namespace WD

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

private def std (a : WDRep h V) : Σ n : ℕ, WDRep h (Fin n → ℂ) :=
  ⟨finrank ℂ V, a.transport (finBasis ℂ V).equivFun⟩

omit [IsAlgClosure E Ω] in
theorem iso_std (a : WDRep h V) : a.Iso (std a).2 := a.iso_transport _

def mk (a : WDRep h V) : WD h := Quotient.mk (isoSetoid h) (std a)

theorem mk_eq_mk {a : WDRep h V} {b : WDRep h V'} : mk a = mk b ↔ a.Iso b := by
  refine Quotient.eq.trans ⟨fun hab => ?_, fun hab => ?_⟩
  · exact ((iso_std a).trans hab).trans (iso_std b).symm
  · exact ((iso_std a).symm.trans hab).trans (iso_std b)

theorem sound {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) : mk a = mk b := mk_eq_mk.mpr hab

private theorem quotientMk_eq (a : Σ n : ℕ, WDRep h (Fin n → ℂ)) :
    Quotient.mk (isoSetoid h) a = mk a.2 := Quotient.sound (iso_std a.2)

theorem exists_rep (x : WD h) : ∃ (n : ℕ) (a : WDRep h (Fin n → ℂ)), mk a = x := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep x
  exact ⟨a.1, a.2, (quotientMk_eq a).symm⟩

@[elab_as_elim]
theorem ind {P : WD h → Prop} (hP : ∀ (n : ℕ) (a : WDRep h (Fin n → ℂ)), P (mk a))
    (x : WD h) : P x := by
  obtain ⟨n, a, rfl⟩ := exists_rep x
  exact hP n a

def lpDim (x : WD h) : ℕ :=
  Quotient.lift (s := isoSetoid h) (fun a => finrank ℂ (Fin a.1 → ℂ))
    (fun _ _ hab => WDRep.Iso.finrank_eq hab) x

@[simp] theorem lpDim_mk (a : WDRep h V) : lpDim (mk a) = finrank ℂ V :=
  (iso_std a).finrank_eq.symm

def charpoly (x : WD h) (σ : Weil h) : ℂ[X] :=
  Quotient.lift (s := isoSetoid h) (fun a => (a.2.ρ σ).charpoly)
    (fun _ _ hab => WDRep.Iso.charpoly_eq hab σ) x

@[simp] theorem charpoly_mk (a : WDRep h V) (σ : Weil h) : charpoly (mk a) σ = (a.ρ σ).charpoly :=
  ((iso_std a).charpoly_eq σ).symm

def mono0 (x : WD h) : Prop :=
  Quotient.lift (s := isoSetoid h) (fun a => a.2.N = 0)
    (fun _ _ hab => propext ⟨WDRep.Iso.monodromy_eq_zero hab, WDRep.Iso.monodromy_eq_zero (WDRep.Iso.symm hab)⟩) x

@[simp] theorem mono0_mk (a : WDRep h V) : mono0 (mk a) ↔ a.N = 0 :=
  ⟨(iso_std a).symm.monodromy_eq_zero, (iso_std a).monodromy_eq_zero⟩

def lpTame (x : WD h) : WD h :=
  Quotient.lift (s := isoSetoid h) (fun a => mk a.2.tamePart)
    (fun _ _ hab => sound (WDRep.Iso.tamePart hab)) x

@[simp] theorem lpTame_mk (a : WDRep h V) : lpTame (mk a) = mk a.tamePart :=
  sound (iso_std a).tamePart.symm

end WD
end GlobalTheory.WeilDeligne
