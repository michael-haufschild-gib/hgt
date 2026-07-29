import GaloisForLFunctions.HTGeometry.DisconnectedAffineSpectralLaw
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Exact tensor factorization of finite local matrix generators

This file supplies the concrete locality layer missing from the abstract generator-support law.
A matrix on a finite site packet is lifted to the full product-configuration space by tensoring
with the identity outside that packet. Reindexing configurations into inside/outside coordinates
recovers that tensor product exactly. Additive onsite energies split as a Kronecker sum across the
same cut. No self-adjointness, normality, or positivity assumption is used.
-/

open scoped Kronecker BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- Product configurations restricted to a finite site packet. -/
abbrev LocalConfiguration
    {V : Type*} (A : V → Type*) (S : Finset V) :=
  ∀ v : S, A v.1

/-- Product configurations outside a finite site packet. -/
abbrev OutsideConfiguration
    {V : Type*} (A : V → Type*) (S : Finset V) :=
  ∀ v : {v : V // v ∉ S}, A v.1

def restrictLocalConfiguration
    {V : Type*} {A : V → Type*} (S : Finset V)
    (x : ∀ v, A v) : LocalConfiguration A S :=
  fun v => x v.1

def restrictOutsideConfiguration
    {V : Type*} {A : V → Type*} (S : Finset V)
    (x : ∀ v, A v) : OutsideConfiguration A S :=
  fun v => x v.1

/-- Canonical equivalence between a full product configuration and its inside/outside pieces. -/
def configurationSplitEquiv
    {V : Type*} [DecidableEq V] (A : V → Type*) (S : Finset V) :
    (∀ v, A v) ≃ LocalConfiguration A S × OutsideConfiguration A S where
  toFun x := (restrictLocalConfiguration S x, restrictOutsideConfiguration S x)
  invFun p v :=
    if hv : v ∈ S then p.1 ⟨v, hv⟩ else p.2 ⟨v, hv⟩
  left_inv x := by
    funext v
    by_cases hv : v ∈ S <;> simp [restrictLocalConfiguration,
      restrictOutsideConfiguration, hv]
  right_inv p := by
    apply Prod.ext
    · funext v
      simp [restrictLocalConfiguration]
    · funext v
      simp [restrictOutsideConfiguration, v.2]

/-- Lift a matrix on `S` to the full product space, acting as the identity outside `S`. -/
def liftLocalMatrix
    {V R : Type*} [Fintype V] [DecidableEq V] [Zero R]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    (S : Finset V)
    (M : Matrix (LocalConfiguration A S) (LocalConfiguration A S) R) :
    Matrix (∀ v, A v) (∀ v, A v) R :=
  fun x y =>
    if restrictOutsideConfiguration S x =
        restrictOutsideConfiguration S y
    then M (restrictLocalConfiguration S x) (restrictLocalConfiguration S y)
    else 0

/-- **Exact local tensor factorization.** Reindexing a lifted local generator into
inside/outside configurations makes it literally `M ⊗ I`. -/
theorem reindex_liftLocalMatrix_eq_kronecker_one
    {V R : Type*} [Fintype V] [DecidableEq V] [CommRing R]
    {A : V → Type*}
    [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    (S : Finset V)
    (M : Matrix (LocalConfiguration A S) (LocalConfiguration A S) R) :
    Matrix.reindex (configurationSplitEquiv A S) (configurationSplitEquiv A S)
        (liftLocalMatrix S M) =
      M ⊗ₖ (1 : Matrix (OutsideConfiguration A S)
        (OutsideConfiguration A S) R) := by
  ext ⟨x, xout⟩ ⟨y, yout⟩
  let e := configurationSplitEquiv A S
  have hx := e.apply_symm_apply (x, xout)
  have hy := e.apply_symm_apply (y, yout)
  have hxlocal :
      restrictLocalConfiguration S (e.symm (x, xout)) = x :=
    congrArg Prod.fst hx
  have hxout :
      restrictOutsideConfiguration S (e.symm (x, xout)) = xout :=
    congrArg Prod.snd hx
  have hylocal :
      restrictLocalConfiguration S (e.symm (y, yout)) = y :=
    congrArg Prod.fst hy
  have hyout :
      restrictOutsideConfiguration S (e.symm (y, yout)) = yout :=
    congrArg Prod.snd hy
  change liftLocalMatrix S M (e.symm (x, xout)) (e.symm (y, yout)) =
    M x y * (1 : Matrix (OutsideConfiguration A S)
      (OutsideConfiguration A S) R) xout yout
  rw [liftLocalMatrix, hxlocal, hxout, hylocal, hyout]
  by_cases h : xout = yout
  · subst yout
    simp
  · simp [h]

/-- Restrict an `S`-configuration to a subpacket `T ⊆ S`. -/
def restrictSupersetConfiguration
    {V : Type*} {A : V → Type*} {T S : Finset V}
    (hTS : T ⊆ S) (x : LocalConfiguration A S) :
    LocalConfiguration A T :=
  fun v => x ⟨v.1, hTS v.2⟩

/-- Coordinates in `S` but outside its subpacket `T`. -/
abbrev RelativeOutsideConfiguration
    {V : Type*} (A : V → Type*) (T S : Finset V) :=
  ∀ v : {v : S // v.1 ∉ T}, A v.1.1

def restrictRelativeOutsideConfiguration
    {V : Type*} {A : V → Type*} (T S : Finset V)
    (x : LocalConfiguration A S) :
    RelativeOutsideConfiguration A T S :=
  fun v => x v.1

/-- Lift a `T`-local matrix to a larger local packet `S`. -/
def liftLocalMatrixToSuperset
    {V R : Type*} [Fintype V] [DecidableEq V] [Zero R]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    {T S : Finset V} (hTS : T ⊆ S)
    (M : Matrix (LocalConfiguration A T) (LocalConfiguration A T) R) :
    Matrix (LocalConfiguration A S) (LocalConfiguration A S) R :=
  fun x y =>
    if restrictRelativeOutsideConfiguration T S x =
        restrictRelativeOutsideConfiguration T S y
    then M (restrictSupersetConfiguration hTS x)
      (restrictSupersetConfiguration hTS y)
    else 0

/-- **Nested locality is exact.** Lifting from `T` to `S` and then to the full product space is
identical to lifting directly from `T`. -/
theorem liftLocalMatrix_liftLocalMatrixToSuperset
    {V R : Type*} [Fintype V] [DecidableEq V] [Zero R]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    {T S : Finset V} (hTS : T ⊆ S)
    (M : Matrix (LocalConfiguration A T) (LocalConfiguration A T) R) :
    liftLocalMatrix S (liftLocalMatrixToSuperset hTS M) =
      liftLocalMatrix T M := by
  ext x y
  have hrestrict :
      restrictSupersetConfiguration hTS (restrictLocalConfiguration S x) =
        restrictLocalConfiguration T x := rfl
  have hrestrictY :
      restrictSupersetConfiguration hTS (restrictLocalConfiguration S y) =
        restrictLocalConfiguration T y := rfl
  by_cases hT :
      restrictOutsideConfiguration T x =
        restrictOutsideConfiguration T y
  · have hS :
        restrictOutsideConfiguration S x =
          restrictOutsideConfiguration S y := by
      funext v
      have hvT : v.1 ∉ T := fun hv => v.2 (hTS hv)
      exact congrFun hT ⟨v.1, hvT⟩
    have hrel :
        restrictRelativeOutsideConfiguration T S
            (restrictLocalConfiguration S x) =
          restrictRelativeOutsideConfiguration T S
            (restrictLocalConfiguration S y) := by
      funext v
      exact congrFun hT ⟨v.1.1, v.2⟩
    simp [liftLocalMatrix, liftLocalMatrixToSuperset, hT, hS, hrel,
      hrestrict, hrestrictY]
  · by_cases hS :
        restrictOutsideConfiguration S x =
          restrictOutsideConfiguration S y
    · have hrel :
          restrictRelativeOutsideConfiguration T S
              (restrictLocalConfiguration S x) ≠
            restrictRelativeOutsideConfiguration T S
              (restrictLocalConfiguration S y) := by
        intro hrelEq
        apply hT
        funext v
        by_cases hvS : v.1 ∈ S
        · exact congrFun hrelEq ⟨⟨v.1, hvS⟩, v.2⟩
        · exact congrFun hS ⟨v.1, hvS⟩
      simp [liftLocalMatrix, liftLocalMatrixToSuperset, hT, hS, hrel]
    · simp [liftLocalMatrix, hT, hS]

/-- Configurations outside both disjoint packets `S` and `T`. -/
abbrev OutsideBothConfiguration
    {V : Type*} (A : V → Type*) (S T : Finset V) :=
  ∀ v : {v : V // v ∉ S ∧ v ∉ T}, A v.1

/-- Read a `T`-configuration from the outside of a disjoint packet `S`. -/
def restrictDisjointLocalConfiguration
    {V : Type*} {A : V → Type*} {S T : Finset V}
    (hdisj : Disjoint S T) (x : OutsideConfiguration A S) :
    LocalConfiguration A T :=
  fun v => x ⟨v.1, fun hvS =>
    Finset.disjoint_left.mp hdisj hvS v.2⟩

def restrictOutsideBothConfiguration
    {V : Type*} {A : V → Type*} (S T : Finset V)
    (x : OutsideConfiguration A S) :
    OutsideBothConfiguration A S T :=
  fun v => x ⟨v.1, v.2.1⟩

/-- A `T`-local matrix, represented within the outside sector of a disjoint packet `S`. -/
def liftLocalMatrixOutsideDisjoint
    {V R : Type*} [Fintype V] [DecidableEq V] [Zero R]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    {S T : Finset V} (hdisj : Disjoint S T)
    (M : Matrix (LocalConfiguration A T) (LocalConfiguration A T) R) :
    Matrix (OutsideConfiguration A S) (OutsideConfiguration A S) R :=
  fun x y =>
    if restrictOutsideBothConfiguration S T x =
        restrictOutsideBothConfiguration S T y
    then M (restrictDisjointLocalConfiguration hdisj x)
      (restrictDisjointLocalConfiguration hdisj y)
    else 0

/-- **Disjoint locality becomes the opposite tensor factor.** After splitting configurations over
`S`, a matrix supported on a disjoint packet `T` is literally `I ⊗ M_T`. -/
theorem reindex_liftLocalMatrix_disjoint_eq_one_kronecker
    {V R : Type*} [Fintype V] [DecidableEq V] [CommRing R]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    {S T : Finset V} (hdisj : Disjoint S T)
    (M : Matrix (LocalConfiguration A T) (LocalConfiguration A T) R) :
    Matrix.reindex (configurationSplitEquiv A S) (configurationSplitEquiv A S)
        (liftLocalMatrix T M) =
      (1 : Matrix (LocalConfiguration A S) (LocalConfiguration A S) R) ⊗ₖ
        liftLocalMatrixOutsideDisjoint hdisj M := by
  ext ⟨x, xout⟩ ⟨y, yout⟩
  let e := configurationSplitEquiv A S
  have hx := e.apply_symm_apply (x, xout)
  have hy := e.apply_symm_apply (y, yout)
  have hxlocal :
      restrictLocalConfiguration S (e.symm (x, xout)) = x :=
    congrArg Prod.fst hx
  have hxout :
      restrictOutsideConfiguration S (e.symm (x, xout)) = xout :=
    congrArg Prod.snd hx
  have hylocal :
      restrictLocalConfiguration S (e.symm (y, yout)) = y :=
    congrArg Prod.fst hy
  have hyout :
      restrictOutsideConfiguration S (e.symm (y, yout)) = yout :=
    congrArg Prod.snd hy
  have hxT :
      restrictLocalConfiguration T (e.symm (x, xout)) =
        restrictDisjointLocalConfiguration hdisj xout := by
    funext v
    have hvS : v.1 ∉ S := fun hv =>
      Finset.disjoint_left.mp hdisj hv v.2
    exact congrFun hxout ⟨v.1, hvS⟩
  have hyT :
      restrictLocalConfiguration T (e.symm (y, yout)) =
        restrictDisjointLocalConfiguration hdisj yout := by
    funext v
    have hvS : v.1 ∉ S := fun hv =>
      Finset.disjoint_left.mp hdisj hv v.2
    exact congrFun hyout ⟨v.1, hvS⟩
  have houtside_iff :
      restrictOutsideConfiguration T (e.symm (x, xout)) =
          restrictOutsideConfiguration T (e.symm (y, yout)) ↔
        x = y ∧
          restrictOutsideBothConfiguration S T xout =
            restrictOutsideBothConfiguration S T yout := by
    constructor
    · intro hglobal
      constructor
      · funext v
        have hvT : v.1 ∉ T := fun hv =>
          Finset.disjoint_left.mp hdisj v.2 hv
        have hv := congrFun hglobal ⟨v.1, hvT⟩
        have hxv := congrFun hxlocal v
        have hyv := congrFun hylocal v
        exact hxv.symm.trans (hv.trans hyv)
      · funext v
        have hv := congrFun hglobal ⟨v.1, v.2.2⟩
        have hxv := congrFun hxout ⟨v.1, v.2.1⟩
        have hyv := congrFun hyout ⟨v.1, v.2.1⟩
        exact hxv.symm.trans (hv.trans hyv)
    · rintro ⟨hxy, hout⟩
      funext v
      by_cases hvS : v.1 ∈ S
      · have hxv := congrFun hxlocal ⟨v.1, hvS⟩
        have hyv := congrFun hylocal ⟨v.1, hvS⟩
        exact hxv.trans ((congrFun hxy ⟨v.1, hvS⟩).trans hyv.symm)
      · have hv := congrFun hout ⟨v.1, hvS, v.2⟩
        have hxv := congrFun hxout ⟨v.1, hvS⟩
        have hyv := congrFun hyout ⟨v.1, hvS⟩
        exact hxv.trans (hv.trans hyv.symm)
  change liftLocalMatrix T M (e.symm (x, xout)) (e.symm (y, yout)) =
    (1 : Matrix (LocalConfiguration A S) (LocalConfiguration A S) R) x y *
      liftLocalMatrixOutsideDisjoint hdisj M xout yout
  rw [liftLocalMatrix, hxT, hyT]
  by_cases hxy : x = y
  · subst y
    by_cases hout :
        restrictOutsideBothConfiguration S T xout =
          restrictOutsideBothConfiguration S T yout
    · rw [if_pos (houtside_iff.mpr ⟨rfl, hout⟩)]
      simp [liftLocalMatrixOutsideDisjoint, hout]
    · rw [if_neg (fun h => hout (houtside_iff.mp h).2)]
      simp [liftLocalMatrixOutsideDisjoint, hout]
  · rw [if_neg (fun h => hxy (houtside_iff.mp h).1)]
    simp [liftLocalMatrixOutsideDisjoint, hxy]

/-- Additive energy of a finite product configuration. -/
def onsiteProductEnergy
    {V : Type*} [Fintype V]
    {A : V → Type*} {R : Type*} [AddCommMonoid R]
    (onsite : ∀ v, A v → R) (x : ∀ v, A v) : R :=
  ∑ v, onsite v (x v)

def localOnsiteEnergy
    {V : Type*} {A : V → Type*} {R : Type*} [AddCommMonoid R]
    (onsite : ∀ v, A v → R) (S : Finset V)
    (x : LocalConfiguration A S) : R :=
  ∑ v : S, onsite v.1 (x v)

def outsideOnsiteEnergy
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} {R : Type*} [AddCommMonoid R]
    (onsite : ∀ v, A v → R) (S : Finset V)
    (x : OutsideConfiguration A S) : R :=
  ∑ v : {v : V // v ∉ S}, onsite v.1 (x v)

theorem onsiteProductEnergy_configurationSplit
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} {R : Type*} [AddCommMonoid R]
    (onsite : ∀ v, A v → R) (S : Finset V)
    (x : LocalConfiguration A S) (xout : OutsideConfiguration A S) :
    onsiteProductEnergy onsite ((configurationSplitEquiv A S).symm (x, xout)) =
      localOnsiteEnergy onsite S x + outsideOnsiteEnergy onsite S xout := by
  classical
  let e := configurationSplitEquiv A S
  have hx := e.apply_symm_apply (x, xout)
  have hxlocal :
      restrictLocalConfiguration S (e.symm (x, xout)) = x :=
    congrArg Prod.fst hx
  have hxout :
      restrictOutsideConfiguration S (e.symm (x, xout)) = xout :=
    congrArg Prod.snd hx
  rw [onsiteProductEnergy, ← Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset V)) (p := fun v => v ∈ S)]
  congr 1
  · rw [localOnsiteEnergy]
    calc
      ∑ v with v ∈ S, onsite v (e.symm (x, xout) v) =
          ∑ v : S, onsite v.1 (e.symm (x, xout) v.1) := by
            apply Finset.sum_subtype
            simp
      _ = ∑ v : S, onsite v.1 (x v) := by
        apply Finset.sum_congr rfl
        intro v hv
        have heq := congrFun hxlocal v
        exact congrArg (onsite v.1) heq
  · rw [outsideOnsiteEnergy]
    calc
      ∑ v with v ∉ S, onsite v (e.symm (x, xout) v) =
          ∑ v : {v : V // v ∉ S}, onsite v.1 (e.symm (x, xout) v.1) := by
            apply Finset.sum_subtype
            simp
      _ = ∑ v : {v : V // v ∉ S}, onsite v.1 (xout v) := by
        apply Finset.sum_congr rfl
        intro v hv
        have heq := congrFun hxout v
        exact congrArg (onsite v.1) heq

/-- **Exact onsite tensor cut.** Every additive product energy is a Kronecker sum across every
site partition. -/
theorem reindex_diagonal_onsiteProductEnergy_eq_kroneckerSum
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    {R : Type*} [CommRing R]
    (onsite : ∀ v, A v → R) (S : Finset V) :
    Matrix.reindex (configurationSplitEquiv A S) (configurationSplitEquiv A S)
        (Matrix.diagonal (onsiteProductEnergy onsite)) =
      kroneckerSum
        (Matrix.diagonal (localOnsiteEnergy onsite S))
        (Matrix.diagonal (outsideOnsiteEnergy onsite S)) := by
  ext ⟨x, xout⟩ ⟨y, yout⟩
  by_cases hxy : x = y
  · subst y
    by_cases hout : xout = yout
    · subst yout
      simp [Matrix.reindex_apply, kroneckerSum,
        onsiteProductEnergy_configurationSplit]
    · simp [Matrix.reindex_apply, kroneckerSum, hout]
  · simp [Matrix.reindex_apply, kroneckerSum, hxy]

/-- **Concrete local affine factorization.** A finite affine generator supported on `S`, together
with arbitrary additive onsite terms, is exactly the Kronecker sum of its active `S`-sector and
the uncoupled outside sector. -/
theorem reindex_affine_liftLocalMatrix_eq_kroneckerSum
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    (onsite : ∀ v, A v → ℂ) (S : Finset V)
    (interaction :
      E → Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ)
    (coupling : E → ℂ) :
    Matrix.reindex (configurationSplitEquiv A S) (configurationSplitEquiv A S)
        (affineMatrixFamily
          (Matrix.diagonal (onsiteProductEnergy onsite))
          (fun label => liftLocalMatrix S (interaction label))
          coupling) =
      kroneckerSum
        (affineMatrixFamily
          (Matrix.diagonal (localOnsiteEnergy onsite S))
          interaction coupling)
        (Matrix.diagonal (outsideOnsiteEnergy onsite S)) := by
  let e := configurationSplitEquiv A S
  change Matrix.reindexAlgEquiv ℂ ℂ e
      (affineMatrixFamily
        (Matrix.diagonal (onsiteProductEnergy onsite))
        (fun label => liftLocalMatrix S (interaction label))
        coupling) = _
  rw [affineMatrixFamily, map_add, map_sum]
  simp_rw [map_smul]
  rw [Matrix.reindexAlgEquiv_apply,
    reindex_diagonal_onsiteProductEnergy_eq_kroneckerSum]
  dsimp only [e]
  simp_rw [Matrix.reindexAlgEquiv_apply,
    reindex_liftLocalMatrix_eq_kronecker_one]
  ext ⟨x, xout⟩ ⟨y, yout⟩
  by_cases hout : xout = yout
  · subst yout
    simp [kroneckerSum, affineMatrixFamily, Matrix.sum_apply,
      Matrix.smul_apply]
    ring
  · simp [kroneckerSum, affineMatrixFamily, Matrix.sum_apply,
      Matrix.smul_apply, hout]

end GaloisForLFunctions.HTGeometry
