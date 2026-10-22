import GaloisForLFunctions.RHTower.Deninger.DeningerCohomologyColimit
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Localization.Module

/-!
# The index category of the cylinder construction

The stages of the cylinder construction are indexed by pairs `(W, L)` — a finite-dimensional
rational subspace and a full lattice in it — but the stage `Z_{W,L} = Hom(L, ℂ^×)` depends only on
`L`, and `W` is recovered as the rational span of `L`.  The index category is therefore the poset of
finitely generated subgroups of a rational vector space.

Every such subgroup is finitely generated and torsion free over `ℤ`, hence free of finite rank, so
it carries a basis; an inclusion of two of them has an integer coordinate matrix in the chosen
bases, and because coordinates are unique these matrices compose.  The covering map they induce on
complex points is injective, because the inclusion is injective over `ℤ` and therefore over `ℚ`,
where a linear injection splits — and the same rational splitting works over `ℂ`.

This supplies every input of `deningerCohomologyDirectLimitEquiv` for the index category itself.

* `RHTower.DeningerIndex` : the index category.
* `RHTower.deningerIndexBasis` : the chosen basis of a stage.
* `RHTower.deningerIndexMatrix` : the exponent matrix of an inclusion.
* `RHTower.deningerIndexMatrix_comp`, `_id` : the cocycle conditions.
* `RHTower.deningerIndexCovering_injective` : the covering maps are injective.
* `RHTower.deningerIndexCohomologyDirectLimitEquiv` : the colimit of the cohomologies of the stages
  is the exterior power of the colimit of the covering spaces.
-/

set_option maxSynthPendingDepth 3

namespace RHTower

open Complex GaloisForLFunctions.HTGeometry

section TorsionFree

variable (V : Type*) [AddCommGroup V] [Module ℚ V]

/-- A rational vector space is torsion free as an abelian group: a nonzero integer is invertible
after passing to `ℚ`. -/
instance deningerRatTorsionFree : Module.IsTorsionFree ℤ V := by
  constructor
  intro r hr
  have hr0 : r ≠ 0 := hr.ne_zero
  intro v w hvw
  have h : r • (v - w) = 0 := by
    rw [smul_sub, show r • v = r • w from hvw, sub_self]
  have h1 : ((r : ℚ)) • (v - w) = 0 := by
    rw [Int.cast_smul_eq_zsmul ℚ r (v - w)]
    exact h
  exact sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_left (Int.cast_ne_zero.2 hr0))

/-- **The index category of the cylinder construction**: the finitely generated subgroups of a
rational vector space, ordered by inclusion.  A pair `(W, L)` of a finite-dimensional subspace and a
full lattice in it is the same datum as `L` alone. -/
abbrev DeningerIndex : Type _ := {L : Submodule ℤ V // L.FG}

variable {V}

instance : Nonempty (DeningerIndex V) := ⟨⟨⊥, Submodule.fg_bot⟩⟩

noncomputable instance : DecidableEq (DeningerIndex V) := Classical.decEq _

/-- **The index category is directed**: the sum of two finitely generated subgroups is finitely
generated. -/
instance deningerIndexDirected : IsDirectedOrder (DeningerIndex V) :=
  ⟨fun i j => ⟨⟨i.1 ⊔ j.1, i.2.sup j.2⟩, le_sup_left, le_sup_right⟩⟩

instance deningerIndexFinite (i : DeningerIndex V) : Module.Finite ℤ i.1 :=
  Module.Finite.iff_fg.2 i.2

instance deningerIndexFree (i : DeningerIndex V) : Module.Free ℤ i.1 :=
  Module.free_of_finite_type_torsion_free'

/-- The rank of a stage: the rank of the lattice, which is the number of complex coordinates of
`Hom(L, ℂ^×)`. -/
noncomputable def deningerIndexRank (i : DeningerIndex V) : ℕ := Module.finrank ℤ i.1

/-- **A chosen basis of a stage.**  Every finitely generated subgroup of a rational vector space is
free of finite rank, being finitely generated and torsion free over a principal ideal domain. -/
noncomputable def deningerIndexBasis (i : DeningerIndex V) :
    Module.Basis (Fin (deningerIndexRank i)) ℤ i.1 := Module.finBasis ℤ i.1

end TorsionFree

section Matrix

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- **The exponent matrix of an inclusion of stages**: the coordinates, in the basis of the larger
lattice, of the basis vectors of the smaller. -/
noncomputable def deningerIndexMatrix {i j : DeningerIndex V} (h : i ≤ j) :
    Fin (deningerIndexRank i) → Fin (deningerIndexRank j) → ℤ :=
  fun a b => LinearMap.toMatrix (deningerIndexBasis i) (deningerIndexBasis j)
    (Submodule.inclusion h) b a

theorem deningerIndexMatrix_apply {i j : DeningerIndex V} (h : i ≤ j)
    (a : Fin (deningerIndexRank i)) (b : Fin (deningerIndexRank j)) :
    deningerIndexMatrix h a b
      = (deningerIndexBasis j).repr (Submodule.inclusion h (deningerIndexBasis i a)) b :=
  LinearMap.toMatrix_apply _ _ _ _ _

/-- **The exponent matrices compose.**  Coordinates in a basis are unique, so the coordinate matrix
of a composite inclusion is the product of the coordinate matrices. -/
theorem deningerIndexMatrix_comp {i j k : DeningerIndex V} (h₁ : i ≤ j) (h₂ : j ≤ k)
    (a : Fin (deningerIndexRank i)) (c : Fin (deningerIndexRank k)) :
    deningerIndexMatrix (h₁.trans h₂) a c
      = ∑ b, deningerIndexMatrix h₁ a b * deningerIndexMatrix h₂ b c := by
  have hcomp : (Submodule.inclusion (le_trans h₁ h₂) : i.1 →ₗ[ℤ] k.1)
      = (Submodule.inclusion h₂ : j.1 →ₗ[ℤ] k.1) ∘ₗ (Submodule.inclusion h₁ : i.1 →ₗ[ℤ] j.1) := rfl
  show LinearMap.toMatrix (deningerIndexBasis i) (deningerIndexBasis k)
      (Submodule.inclusion (le_trans h₁ h₂)) c a = _
  rw [hcomp, LinearMap.toMatrix_comp (deningerIndexBasis i) (deningerIndexBasis j)
    (deningerIndexBasis k)]
  show (∑ b, LinearMap.toMatrix (deningerIndexBasis j) (deningerIndexBasis k)
      (Submodule.inclusion h₂) c b
      * LinearMap.toMatrix (deningerIndexBasis i) (deningerIndexBasis j)
        (Submodule.inclusion h₁) b a) = _
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

/-- **The identity inclusion has the identity exponent matrix.** -/
theorem deningerIndexMatrix_id (i : DeningerIndex V) (a b : Fin (deningerIndexRank i)) :
    deningerIndexMatrix (le_refl i) a b = if a = b then 1 else 0 := by
  have hid : (Submodule.inclusion (le_refl i) : i.1 →ₗ[ℤ] i.1) = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    exact Subtype.ext rfl
  show LinearMap.toMatrix (deningerIndexBasis i) (deningerIndexBasis i)
      (Submodule.inclusion (le_refl i)) b a = _
  rw [hid, LinearMap.toMatrix_id]
  by_cases hab : a = b
  · subst hab
    simp
  · rw [if_neg hab, Matrix.one_apply_ne (Ne.symm hab)]

/-- The defining relation of the exponent matrix, read inside the ambient vector space. -/
theorem deningerIndexBasis_sum {i j : DeningerIndex V} (h : i ≤ j)
    (a : Fin (deningerIndexRank i)) :
    ((deningerIndexBasis i a : i.1) : V)
      = ∑ b, (deningerIndexMatrix h a b : ℚ) • ((deningerIndexBasis j b : j.1) : V) := by
  have hrepr : Submodule.inclusion h (deningerIndexBasis i a)
      = ∑ b, deningerIndexMatrix h a b • deningerIndexBasis j b := by
    refine (Module.Basis.sum_repr (deningerIndexBasis j) _).symm.trans ?_
    exact Finset.sum_congr rfl fun b _ => by rw [deningerIndexMatrix_apply]
  have := congrArg (fun x : j.1 => (x : V)) hrepr
  refine this.trans ?_
  rw [Submodule.coe_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  show ((deningerIndexMatrix h a b • deningerIndexBasis j b : j.1) : V) = _
  rw [Submodule.coe_smul]
  exact (Int.cast_smul_eq_zsmul ℚ _ _).symm

end Matrix

section Injectivity

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- A chosen basis of a stage is rationally independent in the ambient space: an integral
independence in a vector space over the fraction field is a rational one. -/
theorem deningerIndexBasis_linearIndependent (i : DeningerIndex V) :
    LinearIndependent ℚ (fun a => ((deningerIndexBasis i a : i.1) : V)) := by
  refine (LinearIndependent.iff_fractionRing ℤ ℚ).1 ?_
  exact (deningerIndexBasis i).linearIndependent.map' i.1.subtype (Submodule.ker_subtype _)

/-- **The exponent matrix of an inclusion is rationally injective.**  A rational relation among the
columns produces a rational relation among the basis vectors of the smaller lattice. -/
theorem deningerIndexMatrix_rat_injective {i j : DeningerIndex V} (h : i ≤ j)
    (q : Fin (deningerIndexRank i) → ℚ)
    (hq : ∀ b, ∑ a, (deningerIndexMatrix h a b : ℚ) * q a = 0) : q = 0 := by
  have hv : ∑ a, q a • ((deningerIndexBasis i a : i.1) : V) = 0 := by
    have hstep : ∀ a, q a • ((deningerIndexBasis i a : i.1) : V)
        = ∑ b, (q a * (deningerIndexMatrix h a b : ℚ))
            • ((deningerIndexBasis j b : j.1) : V) := by
      intro a
      rw [deningerIndexBasis_sum h a, Finset.smul_sum]
      exact Finset.sum_congr rfl fun b _ => smul_smul _ _ _
    rw [Finset.sum_congr rfl fun a _ => hstep a, Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← Finset.sum_smul]
    have : ∑ a, q a * (deningerIndexMatrix h a b : ℚ) = 0 := by
      rw [← hq b]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    rw [this, zero_smul]
  have := (Fintype.linearIndependent_iff.1 (deningerIndexBasis_linearIndependent i)) q hv
  funext a
  exact this a

/-- The rational linear map given by the exponent matrix. -/
noncomputable def deningerIndexRatMap {i j : DeningerIndex V} (h : i ≤ j) :
    (Fin (deningerIndexRank i) → ℚ) →ₗ[ℚ] (Fin (deningerIndexRank j) → ℚ) where
  toFun w := fun b => ∑ a, (deningerIndexMatrix h a b : ℚ) * w a
  map_add' w w' := by
    funext b
    show (∑ a, (deningerIndexMatrix h a b : ℚ) * (w a + w' a))
      = (∑ a, (deningerIndexMatrix h a b : ℚ) * w a)
        + ∑ a, (deningerIndexMatrix h a b : ℚ) * w' a
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => mul_add _ _ _
  map_smul' c w := by
    funext b
    show (∑ a, (deningerIndexMatrix h a b : ℚ) * (c * w a))
      = c * ∑ a, (deningerIndexMatrix h a b : ℚ) * w a
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring

/-- Every vector is the sum of its coordinates against the standard basis. -/
theorem deningerPi_eq_sum_single {r : ℕ} (v : Fin r → ℚ) :
    v = ∑ b, v b • (Pi.single b 1 : Fin r → ℚ) := by
  funext b'
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single b' (fun b _ hne => by
      show v b • (Pi.single b 1 : Fin r → ℚ) b' = 0
      rw [Pi.single_eq_of_ne (Ne.symm hne), smul_zero])
    (fun hmem => absurd (Finset.mem_univ b') hmem)]
  show v b' = v b' • (Pi.single b' 1 : Fin r → ℚ) b'
  rw [Pi.single_eq_same, smul_eq_mul, mul_one]

/-- **A rational splitting of the exponent matrix.**  Over a field an injective linear map has a
left inverse; written out in coordinates this is a rational matrix `N` with `A · N = 1`. -/
theorem deningerIndexMatrix_exists_leftInverse {i j : DeningerIndex V} (h : i ≤ j) :
    ∃ N : Fin (deningerIndexRank j) → Fin (deningerIndexRank i) → ℚ,
      ∀ a a', ∑ b, (deningerIndexMatrix h a b : ℚ) * N b a' = if a = a' then 1 else 0 := by
  classical
  have hker : (deningerIndexRatMap h).ker = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun w hw => ?_
    refine deningerIndexMatrix_rat_injective h w fun b => ?_
    exact congrFun hw b
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (deningerIndexRatMap h) hker
  refine ⟨fun b a' => g (Pi.single b 1) a', fun a a' => ?_⟩
  have hcol : deningerIndexRatMap h (Pi.single a 1)
      = fun b => (deningerIndexMatrix h a b : ℚ) := by
    funext b
    show (∑ a', (deningerIndexMatrix h a' b : ℚ)
      * (Pi.single a 1 : Fin (deningerIndexRank i) → ℚ) a') = _
    rw [Finset.sum_eq_single a (fun a' _ hne => by rw [Pi.single_eq_of_ne hne, mul_zero])
      (fun hmem => absurd (Finset.mem_univ a) hmem), Pi.single_eq_same, mul_one]
  have hgid : g (fun b => (deningerIndexMatrix h a b : ℚ))
      = (Pi.single a 1 : Fin (deningerIndexRank i) → ℚ) := by
    rw [← hcol]
    exact LinearMap.congr_fun hg (Pi.single a 1)
  have hexp : (fun b => (deningerIndexMatrix h a b : ℚ))
      = ∑ b, (deningerIndexMatrix h a b : ℚ)
          • (Pi.single b 1 : Fin (deningerIndexRank j) → ℚ) :=
    deningerPi_eq_sum_single _
  have hsum : g (fun b => (deningerIndexMatrix h a b : ℚ)) a'
      = ∑ b, (deningerIndexMatrix h a b : ℚ) * g (Pi.single b 1) a' := by
    rw [hexp, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun b _ => by rw [map_smul]; rfl
  rw [← hsum, hgid]
  by_cases haa : a = a'
  · subst haa
    rw [if_pos rfl, Pi.single_eq_same]
  · rw [if_neg haa, Pi.single_eq_of_ne (Ne.symm haa)]

/-- **The covering map of an inclusion of stages is injective.**  The rational splitting of the
exponent matrix is a matrix of rational numbers, so the same matrix splits the map over `ℂ`. -/
theorem deningerIndexCovering_injective {i j : DeningerIndex V} (h : i ≤ j) :
    Function.Injective (deningerCoveringSystem (ι := DeningerIndex V) deningerIndexRank
      (fun _ _ h => deningerIndexMatrix h) i j h) := by
  obtain ⟨N, hN⟩ := deningerIndexMatrix_exists_leftInverse h
  refine LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun w hw => ?_)
  have hw' : ∀ b, ∑ a, (deningerIndexMatrix h a b : ℂ) * w a = 0 := by
    intro b
    have := congrFun hw b
    show (∑ a, (deningerIndexMatrix h a b : ℂ) * w a) = 0
    rw [← deningerMatrixCLM_apply (fun b a => deningerIndexMatrix h a b) w b]
    exact this
  funext a'
  have hzero : ∑ b, ((N b a' : ℚ) : ℂ) * (∑ a, (deningerIndexMatrix h a b : ℂ) * w a) = 0 := by
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [hw' b, mul_zero]
  have hswap : ∑ b, ((N b a' : ℚ) : ℂ) * (∑ a, (deningerIndexMatrix h a b : ℂ) * w a)
      = ∑ a, (∑ b, (deningerIndexMatrix h a b : ℂ) * ((N b a' : ℚ) : ℂ)) * w a := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hdelta : ∀ a, (∑ b, (deningerIndexMatrix h a b : ℂ) * ((N b a' : ℚ) : ℂ))
      = if a = a' then 1 else 0 := by
    intro a
    have hcast : ((∑ b, (deningerIndexMatrix h a b : ℚ) * N b a' : ℚ) : ℂ)
        = ∑ b, (deningerIndexMatrix h a b : ℂ) * ((N b a' : ℚ) : ℂ) := by
      push_cast
      rfl
    rw [← hcast, hN a a']
    by_cases haa : a = a'
    · rw [if_pos haa, if_pos haa, Rat.cast_one]
    · rw [if_neg haa, if_neg haa, Rat.cast_zero]
  rw [hswap, Finset.sum_congr rfl fun a _ => by rw [hdelta a]] at hzero
  rw [Finset.sum_eq_single a' (fun a _ hne => by rw [if_neg hne, zero_mul])
    (fun hmem => absurd (Finset.mem_univ a') hmem), if_pos rfl, one_mul] at hzero
  exact hzero.trans (by rw [Pi.zero_apply])

end Injectivity

section Colimit

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The exponent matrices of the index category form a directed system. -/
instance deningerIndexDirectedSystem :
    DirectedSystem (fun i : DeningerIndex V => Fin (deningerIndexRank i) → ℂ)
      (fun _ _ h => deningerCoveringSystem (ι := DeningerIndex V) deningerIndexRank
        (fun _ _ h => deningerIndexMatrix h) _ _ h) where
  map_self := by
    intro i x
    show deningerMatrixCLM (fun b a => deningerIndexMatrix (le_refl i) a b) x = x
    funext b
    rw [deningerMatrixCLM_apply]
    rw [Finset.sum_congr rfl fun a _ => by
      rw [show deningerIndexMatrix (le_refl i) a b = if a = b then 1 else 0 from
        deningerIndexMatrix_id i a b]]
    rw [Finset.sum_eq_single b (fun a _ hne => by rw [if_neg hne, Int.cast_zero, zero_mul])
      (fun hmem => absurd (Finset.mem_univ b) hmem), if_pos rfl, Int.cast_one, one_mul]
  map_map := by
    intro i j k h₁ h₂ x
    show deningerMatrixCLM (fun c b => deningerIndexMatrix h₂ b c)
        (deningerMatrixCLM (fun b a => deningerIndexMatrix h₁ a b) x)
      = deningerMatrixCLM (fun c a => deningerIndexMatrix (h₁.trans h₂) a c) x
    funext c
    rw [deningerMatrixCLM_apply, deningerMatrixCLM_apply]
    rw [Finset.sum_congr rfl fun b _ => by rw [deningerMatrixCLM_apply]]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [deningerIndexMatrix_comp h₁ h₂ a c]
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring

/-- **The colimit of the cohomologies of the stages of the cylinder construction is the exterior
power of the colimit of the covering spaces.**  This is the comparison `(6)` for the index category
itself: the finitely generated subgroups of a rational vector space, with their inclusions. -/
noncomputable def deningerIndexCohomologyDirectLimitEquiv (n : ℕ) :
    Module.DirectLimit (fun i : DeningerIndex V => deningerCohomology (deningerIndexRank i) n)
        (deningerCohomologySystem deningerIndexRank
          (fun _ _ h => deningerIndexMatrix h) n) ≃ₗ[ℂ]
      ⋀[ℂ]^(n + 1) (Module.DirectLimit (fun i : DeningerIndex V => Fin (deningerIndexRank i) → ℂ)
        (deningerCoveringSystem deningerIndexRank (fun _ _ h => deningerIndexMatrix h))) :=
  deningerCohomologyDirectLimitEquiv deningerIndexRank (fun _ _ h => deningerIndexMatrix h) n
    (fun _ _ h => deningerIndexCovering_injective h)

end Colimit

end RHTower
