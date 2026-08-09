import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.StructuredMorita
import Mathlib.LinearAlgebra.Prod

/-!
# Nomological Gauss--Codazzi decomposition

An arbitrary connection on a split section module `K × H` has four blocks.  Squaring it with the
Lie-bracket correction gives the Gauss--Codazzi--Ricci identities, including both second
fundamental forms.  The development also retains metric compatibility, the exact parallel-split
criterion, the induced block holonomy law, compatibility with a cyclic square-zero differential,
and covariance under adapted block gauges.
-/

namespace HTGeometry.NomologicalHomotopyGeometry.NomologicalGaussCodazzi

open Module

universe u

variable {k D K H : Type u} [Field k]
variable [AddCommGroup K] [Module k K] [AddCommGroup H] [Module k H]

/-- An endomorphism in four blocks relative to `K × H`. -/
def blockEnd (P : Module.End k K) (B : H →ₗ[k] K) (A : K →ₗ[k] H)
    (S : Module.End k H) : Module.End k (K × H) where
  toFun x := (P x.1 + B x.2, A x.1 + S x.2)
  map_add' x y := by
    ext <;> simp <;> abel
  map_smul' a x := by
    ext <;> simp [smul_add]

@[simp]
theorem blockEnd_apply_fst (P : Module.End k K) (B : H →ₗ[k] K) (A : K →ₗ[k] H)
    (S : Module.End k H) (x : K × H) :
    (blockEnd P B A S x).1 = P x.1 + B x.2 :=
  rfl

@[simp]
theorem blockEnd_apply_snd (P : Module.End k K) (B : H →ₗ[k] K) (A : K →ₗ[k] H)
    (S : Module.End k H) (x : K × H) :
    (blockEnd P B A S x).2 = A x.1 + S x.2 :=
  rfl

/-- Split connection: diagonal induced connections and two second fundamental forms. -/
structure BlockConnection where
  Kconn : D → Module.End k K
  Hconn : D → Module.End k H
  A : D → K →ₗ[k] H
  B : D → H →ₗ[k] K

namespace BlockConnection

/-- Total connection on the split section module. -/
def total (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (X : D) : Module.End k (K × H) :=
  blockEnd (C.Kconn X) (C.B X) (C.A X) (C.Hconn X)

/-- Curvature of a connection represented by covariant derivative operators. -/
def curvature (bracket : D → D → D) (N : D → Module.End k (K × H))
    (X Y : D) : Module.End k (K × H) :=
  (N X).comp (N Y) - (N Y).comp (N X) - N (bracket X Y)

/-- Curvature of the induced `K`-connection. -/
def curvatureK (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (bracket : D → D → D) (X Y : D) : Module.End k K :=
  (C.Kconn X).comp (C.Kconn Y) - (C.Kconn Y).comp (C.Kconn X) -
    C.Kconn (bracket X Y)

/-- Curvature of the induced `H`-connection. -/
def curvatureH (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (bracket : D → D → D) (X Y : D) : Module.End k H :=
  (C.Hconn X).comp (C.Hconn Y) - (C.Hconn Y).comp (C.Hconn X) -
    C.Hconn (bracket X Y)

/-- `B ∧ A`, the hidden-sector quadratic correction. -/
def wedgeBA (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (X Y : D) : Module.End k K :=
  (C.B X).comp (C.A Y) - (C.B Y).comp (C.A X)

/-- `A ∧ B`, the observed-sector quadratic correction. -/
def wedgeAB (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (X Y : D) : Module.End k H :=
  (C.A X).comp (C.B Y) - (C.A Y).comp (C.B X)

/-- Covariant exterior derivative of `B`. -/
def covDerivativeB (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (bracket : D → D → D) (X Y : D) : H →ₗ[k] K :=
  (C.Kconn X).comp (C.B Y) + (C.B X).comp (C.Hconn Y) -
    (C.Kconn Y).comp (C.B X) - (C.B Y).comp (C.Hconn X) - C.B (bracket X Y)

/-- Covariant exterior derivative of `A`. -/
def covDerivativeA (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (bracket : D → D → D) (X Y : D) : K →ₗ[k] H :=
  (C.Hconn X).comp (C.A Y) + (C.A X).comp (C.Kconn Y) -
    (C.Hconn Y).comp (C.A X) - (C.A Y).comp (C.Kconn X) - C.A (bracket X Y)

/-- Gauss component of total curvature. -/
theorem curvature_total_fst
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (bracket : D → D → D) (X Y : D) (s : K × H) :
    (curvature bracket C.total X Y s).1 =
      (curvatureK C bracket X Y + wedgeBA C X Y) s.1 +
        covDerivativeB C bracket X Y s.2 := by
  simp [curvature, total, blockEnd, curvatureK, wedgeBA, covDerivativeB]
  abel

/-- Ricci component of total curvature. -/
theorem curvature_total_snd
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (bracket : D → D → D) (X Y : D) (s : K × H) :
    (curvature bracket C.total X Y s).2 =
      covDerivativeA C bracket X Y s.1 +
        (curvatureH C bracket X Y + wedgeAB C X Y) s.2 := by
  simp [curvature, total, blockEnd, curvatureH, wedgeAB, covDerivativeA]
  abel

/-- Full observer Gauss--Codazzi--Ricci block identity. -/
theorem curvature_total_eq_block
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (bracket : D → D → D) (X Y : D) :
    curvature bracket C.total X Y =
      blockEnd (curvatureK C bracket X Y + wedgeBA C X Y)
        (covDerivativeB C bracket X Y) (covDerivativeA C bracket X Y)
        (curvatureH C bracket X Y + wedgeAB C X Y) := by
  apply LinearMap.ext
  intro s
  apply Prod.ext
  · exact curvature_total_fst C bracket X Y s
  · exact curvature_total_snd C bracket X Y s

/-! ## Flat total connection -/

/-- A flat total connection has covariantly closed second fundamental form `A`. -/
theorem covDerivativeA_eq_zero_of_flat
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (bracket : D → D → D) (hflat : ∀ X Y, curvature bracket C.total X Y = 0)
    (X Y : D) : covDerivativeA C bracket X Y = 0 := by
  apply LinearMap.ext
  intro x
  have h := congrArg (fun T : Module.End k (K × H) ↦ (T (x, 0)).2) (hflat X Y)
  simpa [curvature_total_snd] using h

/-- A flat total connection has covariantly closed second fundamental form `B`. -/
theorem covDerivativeB_eq_zero_of_flat
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (bracket : D → D → D) (hflat : ∀ X Y, curvature bracket C.total X Y = 0)
    (X Y : D) : covDerivativeB C bracket X Y = 0 := by
  apply LinearMap.ext
  intro x
  have h := congrArg (fun T : Module.End k (K × H) ↦ (T (0, x)).1) (hflat X Y)
  simpa [curvature_total_fst] using h

/-- Gauss equation for a flat total connection. -/
theorem curvatureK_eq_neg_wedgeBA_of_flat
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (bracket : D → D → D) (hflat : ∀ X Y, curvature bracket C.total X Y = 0)
    (X Y : D) : curvatureK C bracket X Y = -wedgeBA C X Y := by
  apply LinearMap.ext
  intro x
  have h := congrArg (fun T : Module.End k (K × H) ↦ (T (x, 0)).1) (hflat X Y)
  have hz : (curvatureK C bracket X Y + wedgeBA C X Y) x = 0 := by
    simpa [curvature_total_fst] using h
  exact eq_neg_of_add_eq_zero_left hz

/-- Ricci equation for a flat total connection. -/
theorem curvatureH_eq_neg_wedgeAB_of_flat
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (bracket : D → D → D) (hflat : ∀ X Y, curvature bracket C.total X Y = 0)
    (X Y : D) : curvatureH C bracket X Y = -wedgeAB C X Y := by
  apply LinearMap.ext
  intro x
  have h := congrArg (fun T : Module.End k (K × H) ↦ (T (0, x)).2) (hflat X Y)
  have hz : (curvatureH C bracket X Y + wedgeAB C X Y) x = 0 := by
    simpa [curvature_total_snd] using h
  exact eq_neg_of_add_eq_zero_left hz

/-! ## Polar metric and parallel splitting -/

/-- Block-orthogonal bilinear pairing on `K × H`. -/
def productPairing (gK : K →ₗ[k] K →ₗ[k] k) (gH : H →ₗ[k] H →ₗ[k] k) :
    (K × H) →ₗ[k] (K × H) →ₗ[k] k where
  toFun x :=
    { toFun := fun y ↦ gK x.1 y.1 + gH x.2 y.2
      map_add' := by intro y z; simp; abel
      map_smul' := by intro a y; simp [mul_add] }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    simp
    abel
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    simp [mul_add]

/-- Left and right nondegeneracy, in the exact form used by the polar argument. -/
structure Nondegenerate (g : K →ₗ[k] K →ₗ[k] k) : Prop where
  left : ∀ x, (∀ y, g x y = 0) → x = 0
  right : ∀ y, (∀ x, g x y = 0) → y = 0

/-- Metric compatibility of every covariant derivative operator. -/
def IsMetricCompatible
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (gK : K →ₗ[k] K →ₗ[k] k) (gH : H →ₗ[k] H →ₗ[k] k) : Prop :=
  ∀ X u v, productPairing gK gH (C.total X u) v +
    productPairing gK gH u (C.total X v) = 0

/-- Metric compatibility makes the two second fundamental forms negative adjoints. -/
theorem secondFundamental_adjoint
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (gK : K →ₗ[k] K →ₗ[k] k) (gH : H →ₗ[k] H →ₗ[k] k)
    (hmetric : IsMetricCompatible C gK gH) (X : D) (h : H) (x : K) :
    gK (C.B X h) x + gH h (C.A X x) = 0 := by
  simpa [IsMetricCompatible, productPairing, total] using hmetric X (0, h) (x, 0)

/-- Under a nondegenerate polar metric, `A` vanishes exactly when `B` vanishes. -/
theorem A_eq_zero_iff_B_eq_zero
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (gK : K →ₗ[k] K →ₗ[k] k) (gH : H →ₗ[k] H →ₗ[k] k)
    (hK : Nondegenerate gK) (hH : Nondegenerate gH)
    (hmetric : IsMetricCompatible C gK gH) :
    (∀ X, C.A X = 0) ↔ ∀ X, C.B X = 0 := by
  constructor
  · intro hA X
    apply LinearMap.ext
    intro h
    apply hK.left
    intro x
    have hm := secondFundamental_adjoint C gK gH hmetric X h x
    rw [hA X] at hm
    simpa using hm
  · intro hB X
    apply LinearMap.ext
    intro x
    apply hH.right
    intro h
    have hm := secondFundamental_adjoint C gK gH hmetric X h x
    rw [hB X] at hm
    simpa using hm

/-- The hidden summand is parallel exactly when `A = 0`. -/
def KParallel (C : BlockConnection (k := k) (D := D) (K := K) (H := H)) : Prop :=
  ∀ X x, (C.total X (x, 0)).2 = 0

/-- The observed summand is parallel exactly when `B = 0`. -/
def HParallel (C : BlockConnection (k := k) (D := D) (K := K) (H := H)) : Prop :=
  ∀ X h, (C.total X (0, h)).1 = 0

/-- Connection preserves the adapted splitting. -/
def SplittingParallel (C : BlockConnection (k := k) (D := D) (K := K) (H := H)) : Prop :=
  KParallel C ∧ HParallel C

theorem kParallel_iff
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H)) :
    KParallel C ↔ ∀ X, C.A X = 0 := by
  simp only [KParallel, total, blockEnd_apply_snd, map_zero, add_zero]
  constructor
  · intro h X
    ext x
    exact h X x
  · intro h X x
    rw [h X]
    rfl

theorem hParallel_iff
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H)) :
    HParallel C ↔ ∀ X, C.B X = 0 := by
  simp only [HParallel, total, blockEnd_apply_fst, map_zero, zero_add]
  constructor
  · intro h X
    ext x
    exact h X x
  · intro h X x
    rw [h X]
    simp

/-- Exact parallel-observer equivalence of both summands and both second fundamental forms. -/
theorem parallelObserver_criterion
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (gK : K →ₗ[k] K →ₗ[k] k) (gH : H →ₗ[k] H →ₗ[k] k)
    (hK : Nondegenerate gK) (hH : Nondegenerate gH)
    (hmetric : IsMetricCompatible C gK gH) :
    KParallel C ↔ HParallel C := by
  rw [kParallel_iff, hParallel_iff]
  exact A_eq_zero_iff_B_eq_zero C gK gH hK hH hmetric

/-- Five equivalent forms of the exact parallel-observer criterion. -/
theorem parallelObserver_tfae
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (gK : K →ₗ[k] K →ₗ[k] k) (gH : H →ₗ[k] H →ₗ[k] k)
    (hK : Nondegenerate gK) (hH : Nondegenerate gH)
    (hmetric : IsMetricCompatible C gK gH) :
    List.TFAE [KParallel C, HParallel C, (∀ X, C.A X = 0),
      (∀ X, C.B X = 0), SplittingParallel C] := by
  tfae_have 1 ↔ 3 := kParallel_iff C
  tfae_have 2 ↔ 4 := hParallel_iff C
  tfae_have 3 ↔ 4 := A_eq_zero_iff_B_eq_zero C gK gH hK hH hmetric
  tfae_have 5 ↔ 1 := by
    constructor
    · exact And.left
    · intro hKP
      exact ⟨hKP, (parallelObserver_criterion C gK gH hK hH hmetric).mp hKP⟩
  tfae_finish

/-- Block-diagonal endomorphism predicate. -/
def IsBlockDiagonal (T : Module.End k (K × H)) : Prop :=
  (∀ x, (T (x, 0)).2 = 0) ∧ (∀ h, (T (0, h)).1 = 0)

theorem isBlockDiagonal_id : IsBlockDiagonal (LinearMap.id : Module.End k (K × H)) := by
  constructor <;> intro <;> rfl

theorem IsBlockDiagonal.comp {S T : Module.End k (K × H)}
    (hS : IsBlockDiagonal S) (hT : IsBlockDiagonal T) : IsBlockDiagonal (S.comp T) := by
  constructor
  · intro x
    have hTx : (T (x, 0)).2 = 0 := hT.1 x
    have hSx : (S ((T (x, 0)).1, 0)).2 = 0 := hS.1 _
    have hTeq : T (x, 0) = ((T (x, 0)).1, 0) := Prod.ext rfl hTx
    rw [LinearMap.comp_apply, hTeq]
    exact hSx
  · intro h
    have hTh : (T (0, h)).1 = 0 := hT.2 h
    have hSh : (S (0, (T (0, h)).2)).1 = 0 := hS.2 _
    have hTeq : T (0, h) = (0, (T (0, h)).2) := Prod.ext hTh rfl
    rw [LinearMap.comp_apply, hTeq]
    exact hSh

/-- Word transport generated by connection operators; its block law is the algebraic holonomy
reduction statement. -/
def transportWord (C : BlockConnection (k := k) (D := D) (K := K) (H := H)) :
    List D → Module.End k (K × H)
  | [] => LinearMap.id
  | X :: w => (C.total X).comp (transportWord C w)

theorem transportWord_blockDiagonal
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (hsplit : SplittingParallel C) : ∀ w, IsBlockDiagonal (transportWord C w) := by
  intro w
  induction w with
  | nil => exact isBlockDiagonal_id
  | cons X w ih =>
      apply IsBlockDiagonal.comp
      · exact ⟨hsplit.1 X, hsplit.2 X⟩
      · exact ih

/-! ## Compatibility with a cyclic differential -/

/-- Invariance of the hidden summand under an endomorphism. -/
def KInvariant (Q : Module.End k (K × H)) : Prop :=
  ∀ x, (Q (x, 0)).2 = 0

/-- Invariance of the observed summand under an endomorphism. -/
def HInvariant (Q : Module.End k (K × H)) : Prop :=
  ∀ h, (Q (0, h)).1 = 0

/-- Cyclicity with an explicit graded sign scalar `ε` (normally `1` or `-1`). -/
def IsCyclic (gK : K →ₗ[k] K →ₗ[k] k) (gH : H →ₗ[k] H →ₗ[k] k)
    (ε : k) (Q : Module.End k (K × H)) : Prop :=
  ∀ u v, productPairing gK gH (Q u) v = ε * productPairing gK gH u (Q v)

/-- Cyclicity and nondegeneracy force invariance of the orthogonal complement. -/
theorem hInvariant_of_cyclic_of_kInvariant
    (gK : K →ₗ[k] K →ₗ[k] k) (gH : H →ₗ[k] H →ₗ[k] k)
    (hK : Nondegenerate gK) (ε : k) (Q : Module.End k (K × H))
    (hcyclic : IsCyclic gK gH ε Q) (hQK : KInvariant Q) : HInvariant Q := by
  intro h
  apply hK.left
  intro x
  have hc := hcyclic (0, h) (x, 0)
  change gK (Q (0, h)).1 x + gH (Q (0, h)).2 0 =
    ε * (gK 0 (Q (x, 0)).1 + gH h (Q (x, 0)).2) at hc
  simp only [map_zero, add_zero] at hc
  rw [hQK x] at hc
  simpa using hc

/-- Differential induced on the hidden summand. -/
def restrictK (Q : Module.End k (K × H)) : Module.End k K where
  toFun x := (Q (x, 0)).1
  map_add' x y := by
    have h := congrArg Prod.fst (map_add Q (x, 0) (y, 0))
    simpa using h
  map_smul' a x := by
    have h := congrArg Prod.fst (map_smul Q a (x, 0))
    simpa using h

/-- Differential induced on the observed summand. -/
def restrictH (Q : Module.End k (K × H)) : Module.End k H where
  toFun h := (Q (0, h)).2
  map_add' x y := by
    have h := congrArg Prod.snd (map_add Q (0, x) (0, y))
    simpa using h
  map_smul' a x := by
    have h := congrArg Prod.snd (map_smul Q a (0, x))
    simpa using h

/-- A block-diagonal endomorphism is the product of its two restrictions. -/
theorem blockDiagonal_apply (Q : Module.End k (K × H)) (hQ : IsBlockDiagonal Q)
    (x : K) (h : H) : Q (x, h) = (restrictK Q x, restrictH Q h) := by
  have hsum : (x, h) = (x, 0) + (0, h) := by ext <;> simp
  rw [hsum, map_add]
  apply Prod.ext
  · simp only [Prod.fst_add, restrictK]
    rw [hQ.2 h, add_zero]
    rfl
  · simp only [Prod.snd_add, restrictH]
    rw [hQ.1 x, zero_add]
    rfl

/-- Square-zero descends to the hidden differential. -/
theorem restrictK_sq_zero (Q : Module.End k (K × H)) (hQ : IsBlockDiagonal Q)
    (hsq : Q.comp Q = 0) : (restrictK Q).comp (restrictK Q) = 0 := by
  apply LinearMap.ext
  intro x
  have h := congrArg Prod.fst (LinearMap.congr_fun hsq (x, 0))
  change (Q (Q (x, 0))).1 = 0 at h
  rw [blockDiagonal_apply Q hQ x 0] at h
  simp only [map_zero] at h
  rw [blockDiagonal_apply Q hQ (restrictK Q x) 0] at h
  simpa [LinearMap.comp_apply] using h

/-- Square-zero descends to the observed differential. -/
theorem restrictH_sq_zero (Q : Module.End k (K × H)) (hQ : IsBlockDiagonal Q)
    (hsq : Q.comp Q = 0) : (restrictH Q).comp (restrictH Q) = 0 := by
  apply LinearMap.ext
  intro x
  have h := congrArg Prod.snd (LinearMap.congr_fun hsq (0, x))
  change (Q (Q (0, x))).2 = 0 at h
  rw [blockDiagonal_apply Q hQ 0 x] at h
  simp only [map_zero] at h
  rw [blockDiagonal_apply Q hQ 0 (restrictH Q x)] at h
  simpa [LinearMap.comp_apply] using h

/-- Four blockwise chain-map identities. -/
structure BlockIntertwines (Q : Module.End k (K × H))
    (P : Module.End k K) (B : H →ₗ[k] K) (A : K →ₗ[k] H)
    (S : Module.End k H) : Prop where
  Kdiag : P.comp (restrictK Q) = (restrictK Q).comp P
  Bmap : B.comp (restrictH Q) = (restrictK Q).comp B
  Amap : A.comp (restrictK Q) = (restrictH Q).comp A
  Hdiag : S.comp (restrictH Q) = (restrictH Q).comp S

/-- Commutation of a block operator with a block-diagonal `Q` implies all four chain-map laws. -/
theorem blockIntertwines_of_commutes (Q : Module.End k (K × H))
    (hQ : IsBlockDiagonal Q) (P : Module.End k K) (B : H →ₗ[k] K)
    (A : K →ₗ[k] H) (S : Module.End k H)
    (hcomm : (blockEnd P B A S).comp Q = Q.comp (blockEnd P B A S)) :
    BlockIntertwines Q P B A S := by
  constructor
  · apply LinearMap.ext
    intro x
    have h := congrArg Prod.fst (LinearMap.congr_fun hcomm (x, 0))
    simpa [LinearMap.comp_apply, blockDiagonal_apply Q hQ, blockEnd] using h
  · apply LinearMap.ext
    intro h
    have h' := congrArg Prod.fst (LinearMap.congr_fun hcomm (0, h))
    simpa [LinearMap.comp_apply, blockDiagonal_apply Q hQ, blockEnd] using h'
  · apply LinearMap.ext
    intro x
    have h := congrArg Prod.snd (LinearMap.congr_fun hcomm (x, 0))
    simpa [LinearMap.comp_apply, blockDiagonal_apply Q hQ, blockEnd] using h
  · apply LinearMap.ext
    intro h
    have h' := congrArg Prod.snd (LinearMap.congr_fun hcomm (0, h))
    simpa [LinearMap.comp_apply, blockDiagonal_apply Q hQ, blockEnd] using h'

/-- Every connection block intertwines the induced `Q`-complexes. -/
theorem connectionBlockIntertwines
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (Q : Module.End k (K × H)) (hQ : IsBlockDiagonal Q)
    (hcomm : ∀ X, (C.total X).comp Q = Q.comp (C.total X)) (X : D) :
    BlockIntertwines Q (C.Kconn X) (C.B X) (C.A X) (C.Hconn X) :=
  blockIntertwines_of_commutes Q hQ _ _ _ _ (hcomm X)

/-- Curvature commutes with `Q` whenever the connection does. -/
theorem curvature_commutes
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (bracket : D → D → D) (Q : Module.End k (K × H))
    (hcomm : ∀ X, (C.total X).comp Q = Q.comp (C.total X)) (X Y : D) :
    (curvature bracket C.total X Y).comp Q = Q.comp (curvature bracket C.total X Y) := by
  apply LinearMap.ext
  intro z
  have hX (w : K × H) : C.total X (Q w) = Q (C.total X w) := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun (hcomm X) w
  have hY (w : K × H) : C.total Y (Q w) = Q (C.total Y w) := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun (hcomm Y) w
  have hXY (w : K × H) : C.total (bracket X Y) (Q w) =
      Q (C.total (bracket X Y) w) := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun (hcomm (bracket X Y)) w
  simp only [curvature, LinearMap.comp_apply, LinearMap.sub_apply]
  rw [hY z, hX (C.total Y z), hX z, hY (C.total X z), hXY z, map_sub, map_sub]

/-- Every Gauss, Codazzi, and Ricci curvature block is a morphism of the induced `Q`-complexes. -/
theorem curvatureBlockIntertwines
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (bracket : D → D → D) (Q : Module.End k (K × H))
    (hQ : IsBlockDiagonal Q)
    (hcomm : ∀ X, (C.total X).comp Q = Q.comp (C.total X)) (X Y : D) :
    BlockIntertwines Q
      (curvatureK C bracket X Y + wedgeBA C X Y)
      (covDerivativeB C bracket X Y) (covDerivativeA C bracket X Y)
      (curvatureH C bracket X Y + wedgeAB C X Y) := by
  apply blockIntertwines_of_commutes Q hQ
  rw [← curvature_total_eq_block C bracket X Y]
  exact curvature_commutes C bracket Q hcomm X Y

/-- Complete `Q`-compatibility output for the observer splitting. -/
structure QCompatibilityResult
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (bracket : D → D → D) (Q : Module.End k (K × H)) : Prop where
  H_invariant : HInvariant Q
  K_square_zero : (restrictK Q).comp (restrictK Q) = 0
  H_square_zero : (restrictH Q).comp (restrictH Q) = 0
  connection_blocks : ∀ X,
    BlockIntertwines Q (C.Kconn X) (C.B X) (C.A X) (C.Hconn X)
  curvature_blocks : ∀ X Y,
    BlockIntertwines Q
      (curvatureK C bracket X Y + wedgeBA C X Y)
      (covDerivativeB C bracket X Y) (covDerivativeA C bracket X Y)
      (curvatureH C bracket X Y + wedgeAB C X Y)

/-- Cyclic square-zero `Q`, hidden-sector invariance, and connection commutation force every
connection and Gauss--Codazzi--Ricci block to be a morphism of the induced `Q`-complexes. -/
theorem qCompatibility
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (bracket : D → D → D)
    (gK : K →ₗ[k] K →ₗ[k] k) (gH : H →ₗ[k] H →ₗ[k] k)
    (hK : Nondegenerate gK) (ε : k) (Q : Module.End k (K × H))
    (hcyclic : IsCyclic gK gH ε Q) (hQK : KInvariant Q)
    (hsq : Q.comp Q = 0)
    (hcomm : ∀ X, (C.total X).comp Q = Q.comp (C.total X)) :
    QCompatibilityResult C bracket Q := by
  have hQH := hInvariant_of_cyclic_of_kInvariant gK gH hK ε Q hcyclic hQK
  have hdiag : IsBlockDiagonal Q := ⟨hQK, hQH⟩
  exact
    { H_invariant := hQH
      K_square_zero := restrictK_sq_zero Q hdiag hsq
      H_square_zero := restrictH_sq_zero Q hdiag hsq
      connection_blocks := fun X ↦ connectionBlockIntertwines C Q hdiag hcomm X
      curvature_blocks := fun X Y ↦ curvatureBlockIntertwines C bracket Q hdiag hcomm X Y }

/-! ## Adapted block-gauge covariance -/

/-- Adapted gauge on the split total module. -/
def blockGauge (eK : K ≃ₗ[k] K) (eH : H ≃ₗ[k] H) : (K × H) ≃ₗ[k] (K × H) where
  toFun x := (eK x.1, eH x.2)
  invFun x := (eK.symm x.1, eH.symm x.2)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_smul' a x := by ext <;> simp

/-- Conjugation of a diagonal connection block. -/
def conjugateEnd (e : K ≃ₗ[k] K) (T : Module.End k K) : Module.End k K :=
  e.toLinearMap.comp (T.comp e.symm.toLinearMap)

/-- Tensorial transport of an off-diagonal block. -/
def conjugateHom (e₁ : K ≃ₗ[k] K) (e₂ : H ≃ₗ[k] H) (T : K →ₗ[k] H) : K →ₗ[k] H :=
  e₂.toLinearMap.comp (T.comp e₁.symm.toLinearMap)

/-- Connection in an adapted block gauge. -/
def gauge (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (eK : K ≃ₗ[k] K) (eH : H ≃ₗ[k] H) :
    BlockConnection (k := k) (D := D) (K := K) (H := H) where
  Kconn X := conjugateEnd eK (C.Kconn X)
  Hconn X := conjugateEnd eH (C.Hconn X)
  A X := conjugateHom eK eH (C.A X)
  B X := conjugateHom eH eK (C.B X)

/-- The total connection transforms by conjugation under every adapted block gauge. -/
theorem total_gauge_intertwines
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (eK : K ≃ₗ[k] K) (eH : H ≃ₗ[k] H) (X : D) :
    StructuredMorita.Intertwines (blockGauge eK eH) (C.total X)
      ((gauge C eK eH).total X) := by
  apply LinearMap.ext
  rintro ⟨x, h⟩
  apply Prod.ext <;>
    simp [blockGauge, gauge, total, blockEnd,
      conjugateEnd, conjugateHom, LinearMap.comp_apply]

/-- Full curvature transforms by conjugation. -/
theorem curvature_gauge_intertwines
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (bracket : D → D → D) (eK : K ≃ₗ[k] K) (eH : H ≃ₗ[k] H)
    (X Y : D) :
    StructuredMorita.Intertwines (blockGauge eK eH)
      (curvature bracket C.total X Y)
      (curvature bracket (gauge C eK eH).total X Y) := by
  apply StructuredMorita.intertwines_sub
  · apply StructuredMorita.intertwines_sub
    · exact StructuredMorita.intertwines_comp _
        (total_gauge_intertwines C eK eH X) (total_gauge_intertwines C eK eH Y)
    · exact StructuredMorita.intertwines_comp _
        (total_gauge_intertwines C eK eH Y) (total_gauge_intertwines C eK eH X)
  · exact total_gauge_intertwines C eK eH (bracket X Y)

/-- The hidden diagonal curvature transforms tensorially. -/
theorem curvatureK_gauge
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (bracket : D → D → D) (eK : K ≃ₗ[k] K) (eH : H ≃ₗ[k] H)
    (X Y : D) :
    curvatureK (gauge C eK eH) bracket X Y =
      conjugateEnd eK (curvatureK C bracket X Y) := by
  apply LinearMap.ext
  intro x
  simp [curvatureK, gauge, conjugateEnd, LinearMap.comp_apply]

/-- The observed diagonal curvature transforms tensorially. -/
theorem curvatureH_gauge
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (bracket : D → D → D) (eK : K ≃ₗ[k] K) (eH : H ≃ₗ[k] H)
    (X Y : D) :
    curvatureH (gauge C eK eH) bracket X Y =
      conjugateEnd eH (curvatureH C bracket X Y) := by
  apply LinearMap.ext
  intro x
  simp [curvatureH, gauge, conjugateEnd, LinearMap.comp_apply]

/-- Tensorial transport is zero exactly when the original off-diagonal block is zero. -/
theorem conjugateHom_eq_zero_iff (e₁ : K ≃ₗ[k] K) (e₂ : H ≃ₗ[k] H) (T : K →ₗ[k] H) :
    conjugateHom e₁ e₂ T = 0 ↔ T = 0 := by
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    apply e₂.injective
    have hx := LinearMap.congr_fun h (e₁ x)
    simpa [conjugateHom, LinearMap.comp_apply] using hx
  · rintro rfl
    apply LinearMap.ext
    intro x
    simp [conjugateHom]

/-- Vanishing of `A` is adapted-frame invariant. -/
theorem gauge_A_eq_zero_iff
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (eK : K ≃ₗ[k] K) (eH : H ≃ₗ[k] H) (X : D) :
    (gauge C eK eH).A X = 0 ↔ C.A X = 0 :=
  conjugateHom_eq_zero_iff eK eH (C.A X)

/-- Vanishing of `B` is adapted-frame invariant. -/
theorem gauge_B_eq_zero_iff
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (eK : K ≃ₗ[k] K) (eH : H ≃ₗ[k] H) (X : D) :
    (gauge C eK eH).B X = 0 ↔ C.B X = 0 :=
  conjugateHom_eq_zero_iff eH eK (C.B X)

/-- Rank of `A` is adapted-frame invariant. -/
theorem gauge_A_finrank_range
    [FiniteDimensional k K] [FiniteDimensional k H]
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (eK : K ≃ₗ[k] K) (eH : H ≃ₗ[k] H) (X : D) :
    finrank k (LinearMap.range (C.A X)) =
      finrank k (LinearMap.range ((gauge C eK eH).A X)) := by
  apply StructuredMorita.map_finrank_range_eq eK eH
  apply LinearMap.ext
  intro x
  simp [gauge, conjugateHom, LinearMap.comp_apply]

/-- Rank of `B` is adapted-frame invariant. -/
theorem gauge_B_finrank_range
    [FiniteDimensional k K] [FiniteDimensional k H]
    (C : BlockConnection (k := k) (D := D) (K := K) (H := H))
    (eK : K ≃ₗ[k] K) (eH : H ≃ₗ[k] H) (X : D) :
    finrank k (LinearMap.range (C.B X)) =
      finrank k (LinearMap.range ((gauge C eK eH).B X)) := by
  apply StructuredMorita.map_finrank_range_eq eH eK
  apply LinearMap.ext
  intro x
  simp [gauge, conjugateHom, LinearMap.comp_apply]

/-- Adapted gauge carries block-diagonal transport operators to block-diagonal ones. -/
theorem blockDiagonal_conjugate
    (eK : K ≃ₗ[k] K) (eH : H ≃ₗ[k] H) (T : Module.End k (K × H))
    (hT : IsBlockDiagonal T) :
    IsBlockDiagonal
      ((blockGauge eK eH).toLinearMap.comp
        (T.comp (blockGauge eK eH).symm.toLinearMap)) := by
  constructor
  · intro x
    simp only [LinearMap.comp_apply, blockGauge]
    simpa using hT.1 (eK.symm x)
  · intro h
    simp only [LinearMap.comp_apply, blockGauge]
    simpa using hT.2 (eH.symm h)

end BlockConnection

end HTGeometry.NomologicalHomotopyGeometry.NomologicalGaussCodazzi
