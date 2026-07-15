import GaloisForLFunctions.HTGeometry.OrbitBalanceAdditive

/-!
# Exact topological classification of finite shift-orbit defects

The earlier orbit-balance theorem proves that a finite shift coboundary has total charge zero.
This file proves the converse and therefore identifies the complete quotient, not just an
obstruction.

Regard a finitely supported function `D : ℤ →₀ A` as a finite zero-chain on the integer
translation orbit.  The map `intOrbitCellularBoundary` is the cellular boundary of a finite
one-chain, and `additiveOrbitSum` is augmentation.  The resulting sequence is exact:

```text
(ℤ →₀ A) --boundary--> (ℤ →₀ A) --total charge--> A --> 0.
```

Consequently every datum has a canonical charge normal form modulo finite shift gauges, and two
data are gauge-equivalent exactly when their charges agree.  For integer Gamma exponents this is
the algebraic core of the shift-orbit superselection lattice.  It is a static constraint topology,
not a flow or a numerical computation.
-/

namespace GaloisForLFunctions

open scoped BigOperators

noncomputable section

/-- The predecessor embedding indexing the terminal vertex of each oriented edge of the integer
translation orbit. -/
def intOrbitPredEmbedding : ℤ ↪ ℤ where
  toFun z := z - 1
  inj' := by
    intro x y h
    exact sub_left_injective h

/-- Cellular boundary of a finite one-chain on the integer translation orbit.  An edge with
coefficient `a` at `z` has boundary `a[z-1]-a[z]`. -/
def intOrbitCellularBoundary {A : Type*} [AddCommGroup A] :
    (ℤ →₀ A) →+ (ℤ →₀ A) where
  toFun E := E.embDomain intOrbitPredEmbedding - E
  map_zero' := by simp
  map_add' E F := by
    rw [Finsupp.embDomain_add]
    abel

@[simp]
theorem intOrbitCellularBoundary_single {A : Type*} [AddCommGroup A]
    (z : ℤ) (a : A) :
    intOrbitCellularBoundary (Finsupp.single z a) =
      Finsupp.single (z - 1) a - Finsupp.single z a := by
  simp [intOrbitCellularBoundary, intOrbitPredEmbedding]

/-- A finite oriented path from the origin to `z`, with sign chosen so its boundary is
`a[z]-a[0]`. -/
def intOrbitPathPrimitive {A : Type*} [AddCommGroup A] : ℤ → A → (ℤ →₀ A)
  | .ofNat n, a => -((Finset.range n).sum fun i =>
      Finsupp.single ((i + 1 : ℕ) : ℤ) a)
  | .negSucc n, a => (Finset.range (n + 1)).sum fun i =>
      Finsupp.single (-(i : ℤ)) a

/-- The finite path primitive has exactly its two endpoint charges as boundary. -/
theorem intOrbitCellularBoundary_pathPrimitive {A : Type*} [AddCommGroup A]
    (z : ℤ) (a : A) :
    intOrbitCellularBoundary (intOrbitPathPrimitive z a) =
      Finsupp.single z a - Finsupp.single 0 a := by
  cases z with
  | ofNat n =>
      induction n with
      | zero => simp [intOrbitPathPrimitive]
      | succ n ih =>
          rw [show intOrbitPathPrimitive (Int.ofNat (n + 1)) a =
              intOrbitPathPrimitive (Int.ofNat n) a -
                Finsupp.single ((n + 1 : ℕ) : ℤ) a by
            simp [intOrbitPathPrimitive, Finset.sum_range_succ]; abel]
          rw [map_sub, ih, intOrbitCellularBoundary_single]
          have hn : Int.ofNat n = (n : ℤ) := rfl
          have hs : Int.ofNat (n + 1) = (n : ℤ) + 1 := by simp
          rw [hn, hs]
          simp only [Nat.cast_add, Nat.cast_one]
          abel_nf
  | negSucc n =>
      induction n with
      | zero => simp [intOrbitPathPrimitive, intOrbitCellularBoundary_single]
      | succ n ih =>
          rw [show intOrbitPathPrimitive (Int.negSucc (n + 1)) a =
              intOrbitPathPrimitive (Int.negSucc n) a +
                Finsupp.single (-((n + 1 : ℕ) : ℤ)) a by
            simp [intOrbitPathPrimitive, Finset.sum_range_succ]]
          rw [map_add, ih, intOrbitCellularBoundary_single]
          have hn : Int.negSucc n = -(n : ℤ) - 1 := by
            simp [Int.negSucc_eq]
            ring
          have hs : Int.negSucc (n + 1) = -(n : ℤ) - 2 := by
            simp [Int.negSucc_eq]
            ring
          rw [hn, hs]
          simp only [Nat.cast_add, Nat.cast_one]
          abel_nf
          congr 2

/-- Sum the origin-to-site path primitives for every coefficient of an orbit datum. -/
def intOrbitPrimitive {A : Type*} [AddCommGroup A] (D : ℤ →₀ A) : ℤ →₀ A :=
  D.sum fun z a => intOrbitPathPrimitive z a

/-- Explicit chain contraction to the origin: the boundary of the canonical primitive is the
datum minus its entire charge concentrated at `0`. -/
theorem intOrbitCellularBoundary_orbitPrimitive {A : Type*} [AddCommGroup A]
    (D : ℤ →₀ A) :
    intOrbitCellularBoundary (intOrbitPrimitive D) =
      D - Finsupp.single 0 (additiveOrbitSum D) := by
  classical
  rw [intOrbitPrimitive]
  change intOrbitCellularBoundary
      (D.support.sum fun z => intOrbitPathPrimitive z (D z)) = _
  rw [map_sum]
  simp_rw [intOrbitCellularBoundary_pathPrimitive]
  rw [Finset.sum_sub_distrib]
  change D.sum Finsupp.single -
      D.sum (fun _ a => Finsupp.single 0 a) = _
  rw [Finsupp.sum_single, ← Finsupp.single_sum]
  rfl

/-- Augmentation is invariant under an injective relabelling of a finitely supported datum. -/
theorem additiveOrbitSum_embDomain {ι κ A : Type*} [AddCommGroup A]
    (f : ι ↪ κ) (D : ι →₀ A) :
    additiveOrbitSum (D.embDomain f) = additiveOrbitSum D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add i a D _ _ ih =>
      rw [Finsupp.embDomain_add, additiveOrbitSum_add, additiveOrbitSum_add, ih]
      simp

/-- The support-sum coboundary used by the analytic orbit-balance files is exactly the cellular
boundary above. -/
theorem additiveIntShiftCoboundary_eq_intOrbitCellularBoundary
    {A : Type*} [AddCommGroup A] (E : ℤ →₀ A) :
    additiveIntShiftCoboundary E = intOrbitCellularBoundary E := by
  classical
  unfold additiveIntShiftCoboundary
  change E.sum (fun z a =>
      Finsupp.single (z - 1) a - Finsupp.single z a) =
    intOrbitCellularBoundary E
  conv_rhs => rw [← Finsupp.sum_single E]
  change E.support.sum (fun z =>
      Finsupp.single (z - 1) (E z) - Finsupp.single z (E z)) =
    intOrbitCellularBoundary (E.support.sum fun z => Finsupp.single z (E z))
  rw [map_sum]
  simp only [intOrbitCellularBoundary_single]

/-- Exactness at finite orbit data: vanishing total charge is not merely necessary but sufficient
for a datum to be a finite shift boundary. -/
theorem additiveOrbitSum_eq_zero_iff_exists_intOrbitCellularBoundary
    {A : Type*} [AddCommGroup A] (D : ℤ →₀ A) :
    additiveOrbitSum D = 0 ↔ ∃ E, D = intOrbitCellularBoundary E := by
  constructor
  · intro h
    refine ⟨intOrbitPrimitive D, ?_⟩
    rw [intOrbitCellularBoundary_orbitPrimitive, h]
    simp
  · rintro ⟨E, rfl⟩
    change additiveOrbitSum (E.embDomain intOrbitPredEmbedding - E) = 0
    rw [additiveOrbitSum_sub, additiveOrbitSum_embDomain]
    abel

/-- Positive normal-form theorem: every finite orbit defect is a single topological charge plus a
finite gauge boundary. -/
theorem intOrbitData_charge_normalForm
    {A : Type*} [AddCommGroup A] (D : ℤ →₀ A) :
    ∃ E, D = Finsupp.single 0 (additiveOrbitSum D) +
      intOrbitCellularBoundary E := by
  refine ⟨intOrbitPrimitive D, ?_⟩
  rw [intOrbitCellularBoundary_orbitPrimitive]
  abel

/-- Complete superselection law: two finite defects differ by a finite shift gauge exactly when
their total orbit charges agree. -/
theorem intOrbitData_sameCharge_iff_boundary
    {A : Type*} [AddCommGroup A] (D F : ℤ →₀ A) :
    additiveOrbitSum D = additiveOrbitSum F ↔
      ∃ E, D - F = intOrbitCellularBoundary E := by
  rw [← sub_eq_zero, ← additiveOrbitSum_sub]
  exact additiveOrbitSum_eq_zero_iff_exists_intOrbitCellularBoundary (D - F)

end

end GaloisForLFunctions
