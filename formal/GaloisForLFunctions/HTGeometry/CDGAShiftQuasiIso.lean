import GaloisForLFunctions.HTGeometry.CDGAShift
import GaloisForLFunctions.HTGeometry.CDGACellInvariance

/-!
# Reading a shift off degree by degree

Above the shift the component of a shifted module is the original module, and the differential, the
action and a shifted morphism all correspond to the originals.  Below the shift everything is
trivial.  These are the computations the invariance of the shift under quasi-isomorphism is made of.

The comparison is stated with the target degree as a *parameter together with an equation* rather
than as the computed expression `j + k`: otherwise `shiftD` lands in degree `j + k + 1` while the
statement wants `(j + 1) + k`, and those are propositionally but not definitionally equal.

* `HTGeometry.shiftEvalAt` : the component above the shift, at an arbitrary witness.
* `HTGeometry.shiftEvalAt_shiftD`, `shiftEvalAt_shiftAct`, `shiftEvalAt_shiftMap` : it intertwines
  every structure map.
* `HTGeometry.shiftCohomology_subsingleton` : below the shift the cohomology vanishes.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]

/-- **The component of a shift above the shift**, at an arbitrary witness of the degree. -/
def shiftEvalAt (k j n : ℕ) (h : j + k = n) : ShiftCarrier M k n ≃ₗ[R] M j where
  toFun f := f ⟨j, h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun m := fun p => Eq.mpr (congrArg M (show p.1 = j by have := p.2; omega)) m
  left_inv f := by
    funext p
    obtain ⟨a, ha⟩ := p
    obtain rfl : a = j := by omega
    rfl
  right_inv _ := rfl

@[simp] theorem shiftEvalAt_apply (k j n : ℕ) (h : j + k = n) (f : ShiftCarrier M k n) :
    shiftEvalAt (R := R) (M := M) k j n h f = f ⟨j, h⟩ := rfl

section Compat

variable (P : CDGAModuleStructure A M)

/-- The differential of a shift is the differential of the module. -/
theorem shiftEvalAt_shiftD (k j n : ℕ) (h : j + k = n) (f : ShiftCarrier M k n) :
    shiftEvalAt (R := R) k (j + 1) (n + 1) (by omega) (shiftD P k n f)
      = P.d j (shiftEvalAt (R := R) k j n h f) := by
  show shiftD P k n f ⟨j + 1, by omega⟩ = P.d j (f ⟨j, h⟩)
  rw [shiftD_succ]

/-- The action on a shift is the action on the module. -/
theorem shiftEvalAt_shiftAct (k : ℕ) {b n m i c : ℕ} (h : b + n = m) (hi : i + k = n)
    (hc : c + k = m) (e : b + i = c) (x : X b) (f : ShiftCarrier M k n) :
    shiftEvalAt (R := R) k c m hc (shiftAct P k h x f)
      = P.act e x (shiftEvalAt (R := R) k i n hi f) := by
  show shiftAct P k h x f ⟨c, hc⟩ = P.act e x (f ⟨i, hi⟩)
  exact shiftAct_apply_eq P k h x f e hi hc

end Compat

section Map

variable {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]
  {P : CDGAModuleStructure A M} {P' : CDGAModuleStructure A M'}

/-- A shifted morphism is the morphism, read off above the shift. -/
theorem shiftEvalAt_shiftMap (φ : CDGAModuleHom P P') (k j n : ℕ) (h : j + k = n)
    (f : ShiftCarrier M k n) :
    shiftEvalAt (R := R) k j n h ((shiftMap φ k).toFun n f)
      = φ.toFun j (shiftEvalAt (R := R) k j n h f) := rfl

end Map

section Trivial

variable (P : CDGAModuleStructure A M)

/-- Below the shift the cocycles are trivial. -/
theorem shiftCocycles_subsingleton {k n : ℕ} (h : n < k) :
    Subsingleton ((shiftModule P k).cocycles n) := by
  haveI := shiftCarrier_subsingleton (M := M) h
  exact ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩

/-- Below the shift the cohomology is trivial. -/
theorem shiftCohomology_subsingleton {k n : ℕ} (h : n + 1 < k) :
    Subsingleton ((shiftModule P k).cohomology n) := by
  haveI := shiftCocycles_subsingleton P h
  exact ⟨fun a b => Quotient.inductionOn₂' a b fun u v => congrArg _ (Subsingleton.elim u v)⟩

end Trivial

section Cocycles

variable (P : CDGAModuleStructure A M)

/-- A component of a shift is a cocycle exactly when it is one in the original module. -/
theorem shiftD_eq_zero_iff (k j n : ℕ) (h : j + k = n) (f : ShiftCarrier M k n) :
    shiftD P k n f = 0 ↔ P.d j (shiftEvalAt (R := R) k j n h f) = 0 := by
  constructor
  · intro hf
    rw [← shiftEvalAt_shiftD P k j n h f, hf, map_zero]
  · intro hf
    refine (shiftEvalAt (R := R) (M := M) k (j + 1) (n + 1) (by omega)).injective ?_
    rw [shiftEvalAt_shiftD P k j n h f, hf, map_zero]

/-- **Above the shift the cocycles are the cocycles.** -/
def shiftCocyclesEquiv (k j n : ℕ) (h : j + k = n) :
    (shiftModule P k).cocycles n ≃ₗ[R] P.cocycles j where
  toFun u := ⟨shiftEvalAt (R := R) k j n h (u : ShiftCarrier M k n),
    (shiftD_eq_zero_iff P k j n h _).1 u.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ⟨(shiftEvalAt (R := R) (M := M) k j n h).symm (v : M j), by
    show shiftD P k n _ = 0
    rw [shiftD_eq_zero_iff P k j n h, LinearEquiv.apply_symm_apply]
    exact v.2⟩
  left_inv u := Subtype.ext (LinearEquiv.symm_apply_apply _ _)
  right_inv v := Subtype.ext (LinearEquiv.apply_symm_apply _ _)

@[simp] theorem shiftCocyclesEquiv_coe (k j n : ℕ) (h : j + k = n)
    (u : (shiftModule P k).cocycles n) :
    ((shiftCocyclesEquiv P k j n h u : P.cocycles j) : M j)
      = shiftEvalAt (R := R) k j n h (u : ShiftCarrier M k n) := rfl

end Cocycles

section Coboundaries

variable (P : CDGAModuleStructure A M)

/-- The coefficient of a cocycle of the shift is a coboundary exactly when it is one. -/
theorem shiftCocyclesEquiv_mem_coboundaries (k j n : ℕ) (h : j + k = n)
    (y : (shiftModule P k).cocycles (n + 1)) :
    y ∈ (shiftModule P k).coboundaries n
      ↔ shiftCocyclesEquiv P k (j + 1) (n + 1) (by omega) y ∈ P.coboundaries j := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨shiftEvalAt (R := R) k j n h m, ?_⟩
    show shiftEvalAt (R := R) k (j + 1) (n + 1) (by omega) (y : ShiftCarrier M k (n + 1))
      = P.d j (shiftEvalAt (R := R) k j n h m)
    rw [← shiftEvalAt_shiftD P k j n h m]
    exact congrArg _ hm
  · rintro ⟨w, hw⟩
    refine ⟨(shiftEvalAt (R := R) (M := M) k j n h).symm w, ?_⟩
    show (y : ShiftCarrier M k (n + 1))
      = shiftD P k n ((shiftEvalAt (R := R) (M := M) k j n h).symm w)
    refine (shiftEvalAt (R := R) (M := M) k (j + 1) (n + 1) (by omega)).injective ?_
    rw [shiftEvalAt_shiftD P k j n h, LinearEquiv.apply_symm_apply]
    exact hw

/-- **Above the shift the cohomology is the cohomology.** -/
noncomputable def shiftCohomologyEquiv (k j n : ℕ) (h : j + k = n) :
    (shiftModule P k).cohomology n ≃ₗ[R] P.cohomology j :=
  Submodule.Quotient.equiv _ _ (shiftCocyclesEquiv P k (j + 1) (n + 1) (by omega)) (by
    ext v
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (shiftCocyclesEquiv_mem_coboundaries P k j n h y).1 hy
    · intro hv
      refine ⟨(shiftCocyclesEquiv P k (j + 1) (n + 1) (by omega)).symm v, ?_,
        LinearEquiv.apply_symm_apply _ _⟩
      refine (shiftCocyclesEquiv_mem_coboundaries P k j n h _).2 ?_
      rwa [LinearEquiv.apply_symm_apply])

@[simp] theorem shiftCohomologyEquiv_mk (k j n : ℕ) (h : j + k = n)
    (u : (shiftModule P k).cocycles (n + 1)) :
    shiftCohomologyEquiv P k j n h (Submodule.Quotient.mk u)
      = Submodule.Quotient.mk (shiftCocyclesEquiv P k (j + 1) (n + 1) (by omega) u) := rfl

end Coboundaries

section CocyclesMap

variable {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]
  {P : CDGAModuleStructure A M} {P' : CDGAModuleStructure A M'}

/-- The comparison of cocycles is natural. -/
theorem shiftCocyclesEquiv_naturality (φ : CDGAModuleHom P P') (k j n : ℕ) (h : j + k = n)
    (u : (shiftModule P k).cocycles n) :
    shiftCocyclesEquiv P' k j n h ((shiftMap φ k).cocyclesMap n u)
      = φ.cocyclesMap j (shiftCocyclesEquiv P k j n h u) :=
  Subtype.ext (shiftEvalAt_shiftMap φ k j n h (u : ShiftCarrier M k n))

end CocyclesMap

/-- A linear map between a subsingleton and a subsingleton is bijective. -/
theorem bijective_of_subsingleton {α β : Type*} [Subsingleton α] [Subsingleton β] [Zero α]
    [Zero β] (f : α → β) : Function.Bijective f :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

/-- A map conjugate to a bijection is a bijection. -/
theorem bijective_of_conj {α β γ δ : Type*} (e₁ : α ≃ γ) (e₂ : β ≃ δ) (f : α → β) (g : γ → δ)
    (hcomm : ∀ a, e₂ (f a) = g (e₁ a)) (hg : Function.Bijective g) : Function.Bijective f := by
  constructor
  · intro a a' haa
    refine e₁.injective (hg.1 ?_)
    rw [← hcomm, ← hcomm, haa]
  · intro b
    obtain ⟨c, hc⟩ := hg.2 (e₂ b)
    refine ⟨e₁.symm c, e₂.injective ?_⟩
    rw [hcomm, Equiv.apply_symm_apply, hc]

section Invariance

variable {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]
  {P : CDGAModuleStructure A M} {P' : CDGAModuleStructure A M'}

/-- The comparison of cohomology is natural. -/
theorem shiftCohomologyEquiv_naturality (φ : CDGAModuleHom P P') (k j n : ℕ) (h : j + k = n)
    (c : (shiftModule P k).cohomology n) :
    shiftCohomologyEquiv P' k j n h ((shiftMap φ k).cohomologyMap n c)
      = φ.cohomologyMap j (shiftCohomologyEquiv P k j n h c) := by
  refine Quotient.inductionOn' c fun u => ?_
  show Submodule.Quotient.mk (shiftCocyclesEquiv P' k (j + 1) (n + 1) (by omega)
      ((shiftMap φ k).cocyclesMap (n + 1) u))
    = Submodule.Quotient.mk
      (φ.cocyclesMap (j + 1) (shiftCocyclesEquiv P k (j + 1) (n + 1) (by omega) u))
  rw [shiftCocyclesEquiv_naturality]

/-- Below the shift there are no coboundaries. -/
theorem shiftCoboundaries_eq_bot (k n : ℕ) (h : n < k) :
    (shiftModule P k).coboundaries n = ⊥ := by
  haveI := shiftCarrier_subsingleton (M := M) h
  refine le_antisymm (fun y hy => ?_) bot_le
  obtain ⟨m, hm⟩ := hy
  have hz : (shiftModule P k).d n (0 : ShiftCarrier M k n) = 0 := by
    have hs := (shiftModule P k).d_smul n (0 : R) (0 : ShiftCarrier M k n)
    rwa [zero_smul, zero_smul] at hs
  refine (Submodule.mem_bot R).2 (Subtype.ext ?_)
  show (y : ShiftCarrier M k (n + 1)) = 0
  rw [hm, show m = 0 from Subsingleton.elim _ _, hz]

/-- At the bottom of the shift the cohomology is the cocycles of the original module in degree
zero — which is exactly the degree that `IsQuasiIsoFull` adds to `IsQuasiIso`. -/
noncomputable def shiftBottomCohomologyEquiv (P : CDGAModuleStructure A M) (k n : ℕ)
    (h : n + 1 = k) : (shiftModule P k).cohomology n ≃ₗ[R] P.cocycles 0 :=
  (Submodule.quotEquivOfEqBot _ (shiftCoboundaries_eq_bot (P := P) k n (by omega))).trans
    (shiftCocyclesEquiv P k 0 (n + 1) (by omega))

theorem shiftBottomCohomologyEquiv_naturality (φ : CDGAModuleHom P P') (k n : ℕ) (h : n + 1 = k)
    (c : (shiftModule P k).cohomology n) :
    shiftBottomCohomologyEquiv P' k n h ((shiftMap φ k).cohomologyMap n c)
      = φ.cocyclesMap 0 (shiftBottomCohomologyEquiv P k n h c) := by
  refine Quotient.inductionOn' c fun u => ?_
  exact Subtype.ext (shiftEvalAt_shiftMap φ k 0 (n + 1) (by omega) (u : ShiftCarrier M k (n + 1)))

/-- **The shift preserves full quasi-isomorphisms.**  The three regimes are matched by the three
parts of `IsQuasiIsoFull`: below the shift everything is trivial, at the bottom the cohomology is
the degree-zero cocycles, and above it is the cohomology of the original module. -/
theorem shiftMap_isQuasiIsoFull (φ : CDGAModuleHom P P') (hφ : φ.IsQuasiIsoFull) (k : ℕ) :
    (shiftMap φ k).IsQuasiIsoFull := by
  constructor
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact bijective_of_conj (shiftCocyclesEquiv P 0 0 0 rfl).toEquiv
        (shiftCocyclesEquiv P' 0 0 0 rfl).toEquiv
        ((shiftMap φ 0).cocyclesMap 0) (φ.cocyclesMap 0)
        (fun u => Subtype.ext (shiftEvalAt_shiftMap φ 0 0 0 rfl
          (u : ShiftCarrier M 0 0))) hφ.1
    · haveI := shiftCocycles_subsingleton P (show (0 : ℕ) < k by omega)
      haveI := shiftCocycles_subsingleton P' (show (0 : ℕ) < k by omega)
      exact bijective_of_subsingleton _
  · intro n
    rcases lt_trichotomy (n + 1) k with hlt | heq | hgt
    · haveI := shiftCohomology_subsingleton P hlt
      haveI := shiftCohomology_subsingleton P' hlt
      exact bijective_of_subsingleton _
    · exact bijective_of_conj (shiftBottomCohomologyEquiv P k n heq).toEquiv
        (shiftBottomCohomologyEquiv P' k n heq).toEquiv _ _
        (fun c => shiftBottomCohomologyEquiv_naturality φ k n heq c) hφ.1
    · obtain ⟨j, hj⟩ : ∃ j, j + k = n := ⟨n - k, by omega⟩
      exact bijective_of_conj (shiftCohomologyEquiv P k j n hj).toEquiv
        (shiftCohomologyEquiv P' k j n hj).toEquiv
        ((shiftMap φ k).cohomologyMap n) (φ.cohomologyMap j)
        (fun c => shiftCohomologyEquiv_naturality φ k j n hj c) (hφ.2 j)

end Invariance

end GaloisForLFunctions.HTGeometry
