import GaloisForLFunctions.HTGeometry.SourceFaceObservationExcess
import GaloisForLFunctions.HTGeometry.PrincipalQuotientBaseChangeTor

/-!
# One-face kernel/cokernel transmutation

For a linear observation `f : M → N` over a commutative ring and a scalar `x` acting
injectively on `N`, division by `x` identifies the excess intersection

`(range f ∩ xN) / f(xM)`

with the `x`-torsion of `coker f`. Composing with the source-face born-gauge theorem gives the
one-face Bockstein law: boundary-born ambiguity is exactly pre-existing attainment torsion.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]
variable {N : Type w} [AddCommGroup N] [Module A N]

/-- Multiplication by one scalar on a module. -/
def sourceFaceScalarMul (x : A) (V : Type*) [AddCommGroup V] [Module A V] :
    V →ₗ[A] V where
  toFun v := x • v
  map_add' _ _ := smul_add _ _ _
  map_smul' c v := by
    simp only [RingHom.id_apply, smul_smul]
    rw [mul_comm x c]

@[simp]
theorem sourceFaceScalarMul_apply (x : A) (v : N) :
    sourceFaceScalarMul x N v = x • v := rfl

/-- The layer `xM` discarded by restriction to the face `x = 0`. -/
abbrev sourceFaceScalarLayer (x : A) (V : Type*) [AddCommGroup V] [Module A V] :
    Submodule A V :=
  LinearMap.range (sourceFaceScalarMul x V)

/-- Generic attainment defect. -/
abbrev sourceFaceObservationCokernel (f : M →ₗ[A] N) :=
  N ⧸ LinearMap.range f

/-- Multiplication by `x` descended to the generic cokernel. -/
def sourceFaceCokernelScalarMul (x : A) (f : M →ₗ[A] N) :
    sourceFaceObservationCokernel f →ₗ[A] sourceFaceObservationCokernel f :=
  (LinearMap.range f).mapQ (LinearMap.range f) (sourceFaceScalarMul x N) <| by
    rintro _ ⟨m, rfl⟩
    exact ⟨x • m, by simp⟩

@[simp]
theorem sourceFaceCokernelScalarMul_mkQ (x : A) (f : M →ₗ[A] N) (n : N) :
    sourceFaceCokernelScalarMul x f ((LinearMap.range f).mkQ n) =
      (LinearMap.range f).mkQ (x • n) :=
  rfl

/-- Classes of the generic attainment defect killed by the face equation. -/
abbrev sourceFaceCokernelTorsion (x : A) (f : M →ₗ[A] N) :
    Submodule A (sourceFaceObservationCokernel f) :=
  LinearMap.ker (sourceFaceCokernelScalarMul x f)

/-- If multiplication by `x` is injective, it identifies a module with its range. -/
def sourceFaceScalarRangeEquiv (x : A)
    (hx : Function.Injective (sourceFaceScalarMul x N)) :
    N ≃ₗ[A] sourceFaceScalarLayer x N :=
  LinearEquiv.ofInjective (sourceFaceScalarMul x N) hx

/-- Divide an element of `range(f) ∩ xN` by `x`, then take its cokernel class. -/
def sourceFaceRangeIntersectionToScalarLayer (x : A) (f : M →ₗ[A] N) :
    sourceFaceRangeIntersection f (sourceFaceScalarLayer x N) →ₗ[A]
      sourceFaceScalarLayer x N where
  toFun y := ⟨y.1, y.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def sourceFaceRangeIntersectionToCokernel (x : A) (f : M →ₗ[A] N)
    (hx : Function.Injective (sourceFaceScalarMul x N)) :
    sourceFaceRangeIntersection f (sourceFaceScalarLayer x N) →ₗ[A]
      sourceFaceObservationCokernel f :=
  (LinearMap.range f).mkQ.comp <|
    (sourceFaceScalarRangeEquiv x hx).symm.toLinearMap.comp <|
      sourceFaceRangeIntersectionToScalarLayer x f

/-- The divided cokernel class is killed by `x`. -/
theorem sourceFaceRangeIntersectionToCokernel_mem_torsion
    (x : A) (f : M →ₗ[A] N)
    (hx : Function.Injective (sourceFaceScalarMul x N))
    (y : sourceFaceRangeIntersection f (sourceFaceScalarLayer x N)) :
    sourceFaceRangeIntersectionToCokernel x f hx y ∈
      sourceFaceCokernelTorsion x f := by
  rw [LinearMap.mem_ker]
  change (LinearMap.range f).mkQ
      (x • ((sourceFaceScalarRangeEquiv x hx).symm ⟨y.1, y.2.2⟩)) = 0
  have hdiv := (sourceFaceScalarRangeEquiv x hx).apply_symm_apply ⟨y.1, y.2.2⟩
  have hval : x • ((sourceFaceScalarRangeEquiv x hx).symm ⟨y.1, y.2.2⟩) = y.1 :=
    congrArg Subtype.val hdiv
  rw [hval]
  exact Submodule.Quotient.mk_eq_zero (LinearMap.range f) |>.2 y.2.1

/-- Division by `x`, with codomain restricted to cokernel `x`-torsion. -/
def sourceFaceRangeIntersectionToCokernelTorsion
    (x : A) (f : M →ₗ[A] N)
    (hx : Function.Injective (sourceFaceScalarMul x N)) :
    sourceFaceRangeIntersection f (sourceFaceScalarLayer x N) →ₗ[A]
      sourceFaceCokernelTorsion x f :=
  (sourceFaceRangeIntersectionToCokernel x f hx).codRestrict
    (sourceFaceCokernelTorsion x f)
    (sourceFaceRangeIntersectionToCokernel_mem_torsion x f hx)

/-- Kernel of divided cokernel projection is exactly the already-attained source layer `f(xM)`. -/
theorem ker_sourceFaceRangeIntersectionToCokernelTorsion
    (x : A) (f : M →ₗ[A] N)
    (hx : Function.Injective (sourceFaceScalarMul x N)) :
    LinearMap.ker (sourceFaceRangeIntersectionToCokernelTorsion x f hx) =
      sourceFaceAttainmentLayer f (sourceFaceScalarLayer x M)
        (sourceFaceScalarLayer x N) := by
  ext y
  constructor
  · intro hy
    rw [LinearMap.mem_ker] at hy
    have hyq : (LinearMap.range f).mkQ
        ((sourceFaceScalarRangeEquiv x hx).symm ⟨y.1, y.2.2⟩) = 0 :=
      congrArg Subtype.val hy
    have hrange : (sourceFaceScalarRangeEquiv x hx).symm ⟨y.1, y.2.2⟩ ∈
        LinearMap.range f :=
      Submodule.Quotient.mk_eq_zero (LinearMap.range f) |>.1 hyq
    rcases hrange with ⟨m, hm⟩
    change y.1 ∈ (sourceFaceScalarLayer x M).map f
    refine ⟨x • m, ⟨m, rfl⟩, ?_⟩
    have hdiv := (sourceFaceScalarRangeEquiv x hx).apply_symm_apply ⟨y.1, y.2.2⟩
    have hval : x • ((sourceFaceScalarRangeEquiv x hx).symm ⟨y.1, y.2.2⟩) = y.1 :=
      congrArg Subtype.val hdiv
    rw [← hval, ← hm, map_smul]
  · intro hy
    change y.1 ∈ (sourceFaceScalarLayer x M).map f at hy
    rcases hy with ⟨m, ⟨m₀, hm₀⟩, hmy⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change (LinearMap.range f).mkQ
        ((sourceFaceScalarRangeEquiv x hx).symm ⟨y.1, y.2.2⟩) = 0
    apply Submodule.Quotient.mk_eq_zero (LinearMap.range f) |>.2
    refine ⟨m₀, ?_⟩
    apply hx
    have hdiv := (sourceFaceScalarRangeEquiv x hx).apply_symm_apply ⟨y.1, y.2.2⟩
    have hval : x • ((sourceFaceScalarRangeEquiv x hx).symm ⟨y.1, y.2.2⟩) = y.1 :=
      congrArg Subtype.val hdiv
    calc
      sourceFaceScalarMul x N (f m₀) = x • f m₀ := rfl
      _ = f (x • m₀) := (map_smul f x m₀).symm
      _ = f m := congrArg f hm₀
      _ = y.1 := hmy
      _ = x • ((sourceFaceScalarRangeEquiv x hx).symm ⟨y.1, y.2.2⟩) := hval.symm
      _ = sourceFaceScalarMul x N
          ((sourceFaceScalarRangeEquiv x hx).symm ⟨y.1, y.2.2⟩) := rfl

/-- The attained layer is killed by division followed by cokernel projection. -/
theorem sourceFaceAttainmentLayer_le_ker_divideToCokernelTorsion
    (x : A) (f : M →ₗ[A] N)
    (hx : Function.Injective (sourceFaceScalarMul x N)) :
    sourceFaceAttainmentLayer f (sourceFaceScalarLayer x M)
        (sourceFaceScalarLayer x N) ≤
      LinearMap.ker (sourceFaceRangeIntersectionToCokernelTorsion x f hx) := by
  rw [ker_sourceFaceRangeIntersectionToCokernelTorsion]

/-- The canonical map from range excess to cokernel torsion. -/
def sourceFaceRangeExcessToCokernelTorsion
    (x : A) (f : M →ₗ[A] N)
    (hx : Function.Injective (sourceFaceScalarMul x N)) :
    (sourceFaceRangeIntersection f (sourceFaceScalarLayer x N) ⧸
        sourceFaceAttainmentLayer f (sourceFaceScalarLayer x M)
          (sourceFaceScalarLayer x N)) →ₗ[A]
      sourceFaceCokernelTorsion x f :=
  (sourceFaceAttainmentLayer f (sourceFaceScalarLayer x M)
      (sourceFaceScalarLayer x N)).liftQ
    (sourceFaceRangeIntersectionToCokernelTorsion x f hx)
    (sourceFaceAttainmentLayer_le_ker_divideToCokernelTorsion x f hx)

/-- Quotienting by the exact kernel makes the range-excess map injective. -/
theorem sourceFaceRangeExcessToCokernelTorsion_injective
    (x : A) (f : M →ₗ[A] N)
    (hx : Function.Injective (sourceFaceScalarMul x N)) :
    Function.Injective (sourceFaceRangeExcessToCokernelTorsion x f hx) := by
  rw [← LinearMap.ker_eq_bot]
  rw [sourceFaceRangeExcessToCokernelTorsion, Submodule.ker_liftQ]
  rw [ker_sourceFaceRangeIntersectionToCokernelTorsion]
  exact Submodule.mkQ_map_self _

/-- Every cokernel class killed by `x` arises by dividing an element of `range(f) ∩ xN`. -/
theorem sourceFaceRangeExcessToCokernelTorsion_surjective
    (x : A) (f : M →ₗ[A] N)
    (hx : Function.Injective (sourceFaceScalarMul x N)) :
    Function.Surjective (sourceFaceRangeExcessToCokernelTorsion x f hx) := by
  rintro ⟨c, hc⟩
  induction c using Quotient.inductionOn with
  | _ n =>
      have hxn : x • n ∈ LinearMap.range f := by
        apply Submodule.Quotient.mk_eq_zero (LinearMap.range f) |>.1
        have hc₀ := LinearMap.mem_ker.1 hc
        change sourceFaceCokernelScalarMul x f ((LinearMap.range f).mkQ n) = 0 at hc₀
        rw [sourceFaceCokernelScalarMul_mkQ] at hc₀
        exact hc₀
      let y : sourceFaceRangeIntersection f (sourceFaceScalarLayer x N) :=
        ⟨x • n, hxn, ⟨n, rfl⟩⟩
      refine ⟨(sourceFaceAttainmentLayer f (sourceFaceScalarLayer x M)
        (sourceFaceScalarLayer x N)).mkQ y, ?_⟩
      apply Subtype.ext
      change (LinearMap.range f).mkQ
          ((sourceFaceScalarRangeEquiv x hx).symm ⟨x • n, ⟨n, rfl⟩⟩) =
        (LinearMap.range f).mkQ n
      congr 1
      apply hx
      have hdiv := (sourceFaceScalarRangeEquiv x hx).apply_symm_apply
        ⟨x • n, ⟨n, rfl⟩⟩
      exact congrArg Subtype.val hdiv

/-- **One-face range-excess/torsion equivalence.** -/
noncomputable def sourceFaceRangeExcessEquivCokernelTorsion
    (x : A) (f : M →ₗ[A] N)
    (hx : Function.Injective (sourceFaceScalarMul x N)) :
    (sourceFaceRangeIntersection f (sourceFaceScalarLayer x N) ⧸
        sourceFaceAttainmentLayer f (sourceFaceScalarLayer x M)
          (sourceFaceScalarLayer x N)) ≃ₗ[A]
      sourceFaceCokernelTorsion x f :=
  LinearEquiv.ofBijective (sourceFaceRangeExcessToCokernelTorsion x f hx)
    ⟨sourceFaceRangeExcessToCokernelTorsion_injective x f hx,
      sourceFaceRangeExcessToCokernelTorsion_surjective x f hx⟩

/-- A linear observation carries `xM` into `xN`. -/
theorem sourceFaceScalarLayer_le_comap (x : A) (f : M →ₗ[A] N) :
    sourceFaceScalarLayer x M ≤ (sourceFaceScalarLayer x N).comap f := by
  rintro _ ⟨m, rfl⟩
  exact ⟨f m, by simp⟩

/-- **One-face Bockstein transmutation.** Modulo inherited kernel and discarded source layer,
boundary-born ambiguity is canonically the `x`-torsion of the generic attainment defect. -/
noncomputable def sourceFaceBornGaugeEquivCokernelTorsion
    (x : A) (f : M →ₗ[A] N)
    (hx : Function.Injective (sourceFaceScalarMul x N)) :
    (sourceFaceObservationPreimage f (sourceFaceScalarLayer x N) ⧸
        sourceFaceInheritedGauge f (sourceFaceScalarLayer x M)
          (sourceFaceScalarLayer x N)) ≃ₗ[A]
      sourceFaceCokernelTorsion x f :=
  (sourceFaceBornGaugeEquivRangeExcess f
      (sourceFaceScalarLayer x M) (sourceFaceScalarLayer x N)
      (sourceFaceScalarLayer_le_comap x f)).trans
    (sourceFaceRangeExcessEquivCokernelTorsion x f hx)

/-! ## Cokernel base change -/

/-- Attainment defect after quotienting source and target layers. -/
abbrev sourceFaceBoundaryCokernel
    (f : M →ₗ[A] N) (P : Submodule A M) (Q : Submodule A N)
    (hPQ : P ≤ Q.comap f) :=
  (N ⧸ Q) ⧸ LinearMap.range (sourceFaceQuotientObservation f P Q hPQ)

/-- The boundary observation range is the image of the generic range in the target quotient. -/
theorem range_sourceFaceQuotientObservation
    (f : M →ₗ[A] N) (P : Submodule A M) (Q : Submodule A N)
    (hPQ : P ≤ Q.comap f) :
    LinearMap.range (sourceFaceQuotientObservation f P Q hPQ) =
      (LinearMap.range f).map Q.mkQ := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    induction x using Quotient.inductionOn with
    | _ m => exact ⟨f m, ⟨m, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
    exact ⟨P.mkQ m, rfl⟩

/-- The boundary cokernel is canonically the quotient by `Q + range(f)`. -/
noncomputable def sourceFaceBoundaryCokernelEquivSup
    (f : M →ₗ[A] N) (P : Submodule A M) (Q : Submodule A N)
    (hPQ : P ≤ Q.comap f) :
    sourceFaceBoundaryCokernel f P Q hPQ ≃ₗ[A]
      N ⧸ (Q ⊔ LinearMap.range f) := by
  change ((N ⧸ Q) ⧸ LinearMap.range (sourceFaceQuotientObservation f P Q hPQ)) ≃ₗ[A]
    N ⧸ (Q ⊔ LinearMap.range f)
  rw [range_sourceFaceQuotientObservation]
  have hmap : (Q ⊔ LinearMap.range f).map Q.mkQ =
      (LinearMap.range f).map Q.mkQ := by
    rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]
  rw [← hmap]
  exact Submodule.quotientQuotientEquivQuotient Q
    (Q ⊔ LinearMap.range f) le_sup_left

/-- Generic cokernel after quotienting by its `x`-multiple layer. -/
abbrev sourceFaceCokernelModuloScalar (x : A) (f : M →ₗ[A] N) :=
  sourceFaceObservationCokernel f ⧸ LinearMap.range (sourceFaceCokernelScalarMul x f)

/-- The range of multiplication on the cokernel is the image of `xN`. -/
theorem range_sourceFaceCokernelScalarMul (x : A) (f : M →ₗ[A] N) :
    LinearMap.range (sourceFaceCokernelScalarMul x f) =
      (sourceFaceScalarLayer x N).map (LinearMap.range f).mkQ := by
  ext c
  constructor
  · rintro ⟨z, rfl⟩
    induction z using Quotient.inductionOn with
    | _ n => exact ⟨x • n, ⟨n, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨(LinearMap.range f).mkQ n, rfl⟩

/-- The generic cokernel modulo `x` is canonically the same quotient by `xN + range(f)`. -/
noncomputable def sourceFaceCokernelModuloScalarEquivSup
    (x : A) (f : M →ₗ[A] N) :
    sourceFaceCokernelModuloScalar x f ≃ₗ[A]
      N ⧸ (sourceFaceScalarLayer x N ⊔ LinearMap.range f) := by
  change ((sourceFaceObservationCokernel f) ⧸
      LinearMap.range (sourceFaceCokernelScalarMul x f)) ≃ₗ[A]
    N ⧸ (sourceFaceScalarLayer x N ⊔ LinearMap.range f)
  rw [range_sourceFaceCokernelScalarMul]
  have hmap : (sourceFaceScalarLayer x N ⊔ LinearMap.range f).map
      (LinearMap.range f).mkQ =
        (sourceFaceScalarLayer x N).map (LinearMap.range f).mkQ := by
    rw [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
  rw [← hmap]
  exact Submodule.quotientQuotientEquivQuotient (LinearMap.range f)
    (sourceFaceScalarLayer x N ⊔ LinearMap.range f) le_sup_right

/-- **Cokernel base-change law.** The cokernel after restricting to `x = 0` is canonically the
generic cokernel modulo `x`. -/
noncomputable def sourceFaceBoundaryCokernelEquivCokernelModuloScalar
    (x : A) (f : M →ₗ[A] N) :
    sourceFaceBoundaryCokernel f (sourceFaceScalarLayer x M)
        (sourceFaceScalarLayer x N) (sourceFaceScalarLayer_le_comap x f) ≃ₗ[A]
      sourceFaceCokernelModuloScalar x f :=
  (sourceFaceBoundaryCokernelEquivSup f
      (sourceFaceScalarLayer x M) (sourceFaceScalarLayer x N)
      (sourceFaceScalarLayer_le_comap x f)).trans
    (sourceFaceCokernelModuloScalarEquivSup x f).symm

/-! ## The regular-face two-term Tor package -/

/-- Differential obtained after tensoring the regular-element resolution
`0 → A --x→ A → A/(x) → 0` with an `A`-module `C`. -/
abbrev regularFaceBaseChangeDifferential
    (x : A) (C : Type*) [AddCommGroup C] [Module A C] : C →ₗ[A] C :=
  sourceFaceScalarMul x C

/-- Homology of the base-changed length-one regular-face resolution. -/
abbrev regularFaceTor
    (x : A) (C : Type*) [AddCommGroup C] [Module A C] : ℕ → Type _
  | 0 => C ⧸ LinearMap.range (regularFaceBaseChangeDifferential x C)
  | 1 => LinearMap.ker (regularFaceBaseChangeDifferential x C)
  | _ + 2 => PUnit

/-- A nonzero regular element of a domain supplies the free resolution used by `regularFaceTor`. -/
theorem regularFace_freeResolution_exact
    {R : Type*} [CommRing R] [IsDomain R] (x : R) (hx : x ≠ 0) :
    Function.Injective (principalResolutionDifferential x) ∧
      LinearMap.range (principalResolutionDifferential x) =
        LinearMap.ker (principalResolutionAugmentation x) ∧
      Function.Surjective (principalResolutionAugmentation x) :=
  principalQuotient_freeResolution_exact x hx

/-- Degree one is exactly scalar torsion. -/
noncomputable def regularFaceTorOneEquivTorsion
    (x : A) (C : Type*) [AddCommGroup C] [Module A C] :
    regularFaceTor x C 1 ≃ₗ[A] LinearMap.ker (sourceFaceScalarMul x C) :=
  LinearEquiv.refl A _

/-- Degree zero is exactly quotient modulo the scalar multiple layer. -/
noncomputable def regularFaceTorZeroEquivQuotient
    (x : A) (C : Type*) [AddCommGroup C] [Module A C] :
    regularFaceTor x C 0 ≃ₗ[A]
      C ⧸ LinearMap.range (sourceFaceScalarMul x C) :=
  LinearEquiv.refl A _

/-- Every degree at least two vanishes for the length-one resolution. -/
theorem regularFaceTor_subsingleton_of_two_le
    (x : A) (C : Type*) [AddCommGroup C] [Module A C]
    (i : ℕ) (hi : 2 ≤ i) : Subsingleton (regularFaceTor x C i) := by
  cases i with
  | zero => simp at hi
  | succ i =>
      cases i with
      | zero => simp at hi
      | succ k =>
          change Subsingleton PUnit
          infer_instance

/-- Descended cokernel multiplication is ordinary scalar multiplication. -/
theorem sourceFaceCokernelScalarMul_eq_scalarMul (x : A) (f : M →ₗ[A] N) :
    sourceFaceCokernelScalarMul x f =
      sourceFaceScalarMul x (sourceFaceObservationCokernel f) := by
  apply LinearMap.ext
  intro c
  induction c using Quotient.inductionOn with
  | _ n => rfl

/-- The born boundary gauge is the literal degree-one Tor group of the generic cokernel. -/
noncomputable def sourceFaceBornGaugeEquivRegularFaceTorOne
    (x : A) (f : M →ₗ[A] N)
    (hx : Function.Injective (sourceFaceScalarMul x N)) :
    (sourceFaceObservationPreimage f (sourceFaceScalarLayer x N) ⧸
        sourceFaceInheritedGauge f (sourceFaceScalarLayer x M)
          (sourceFaceScalarLayer x N)) ≃ₗ[A]
      regularFaceTor x (sourceFaceObservationCokernel f) 1 := by
  change (sourceFaceObservationPreimage f (sourceFaceScalarLayer x N) ⧸
      sourceFaceInheritedGauge f (sourceFaceScalarLayer x M)
        (sourceFaceScalarLayer x N)) ≃ₗ[A]
    LinearMap.ker (sourceFaceScalarMul x (sourceFaceObservationCokernel f))
  exact (sourceFaceBornGaugeEquivCokernelTorsion x f hx).trans <|
    LinearEquiv.ofEq _ _ <|
      congrArg LinearMap.ker (sourceFaceCokernelScalarMul_eq_scalarMul x f)

/-- Quotients by equal submodules are canonically linearly equivalent. -/
noncomputable def sourceFaceQuotientEquivOfEq
    {C : Type*} [AddCommGroup C] [Module A C]
    (P Q : Submodule A C) (h : P = Q) : (C ⧸ P) ≃ₗ[A] (C ⧸ Q) := by
  subst Q
  exact LinearEquiv.refl A _

/-- Boundary attainment defect is the literal degree-zero Tor group of the generic cokernel. -/
noncomputable def sourceFaceBoundaryCokernelEquivRegularFaceTorZero
    (x : A) (f : M →ₗ[A] N) :
    sourceFaceBoundaryCokernel f (sourceFaceScalarLayer x M)
        (sourceFaceScalarLayer x N) (sourceFaceScalarLayer_le_comap x f) ≃ₗ[A]
      regularFaceTor x (sourceFaceObservationCokernel f) 0 := by
  change sourceFaceBoundaryCokernel f (sourceFaceScalarLayer x M)
      (sourceFaceScalarLayer x N) (sourceFaceScalarLayer_le_comap x f) ≃ₗ[A]
    sourceFaceObservationCokernel f ⧸
      LinearMap.range (sourceFaceScalarMul x (sourceFaceObservationCokernel f))
  exact (sourceFaceBoundaryCokernelEquivCokernelModuloScalar x f).trans <|
    sourceFaceQuotientEquivOfEq _ _ <|
      congrArg LinearMap.range (sourceFaceCokernelScalarMul_eq_scalarMul x f)

end

end GaloisForLFunctions.HTGeometry
