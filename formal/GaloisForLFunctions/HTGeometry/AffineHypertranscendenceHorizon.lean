import GaloisForLFunctions.HTGeometry.DirectionalDerivationLawSpace
import GaloisForLFunctions.HTGeometry.AlgebraicIndependentLinearForms
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.RingTheory.Derivation.Lie

/-!
# Affine hypertranscendence horizon

Translation and dilation form the nonabelian two-dimensional affine law algebra.  If their
commutator has weight `w` and an element is fixed by dilation, its translation jets are weight
vectors.  Every mixed affine law therefore acts triangularly on the translation-jet filtration.

This file formalizes the unconditional Ward-filtration core.  The exact algebraic-independence
transfer across the resulting lower-triangular jet matrices is developed next in the same module.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

/-- Translation plus dilation in the two-dimensional affine law algebra. -/
def affineLawDerivation (T E : Derivation k L L) (a b : k) :
    Derivation k L L :=
  a • T + b • E

@[simp]
theorem affineLawDerivation_apply
    (T E : Derivation k L L) (a b : k) (y : L) :
    affineLawDerivation T E a b y = a • T y + b • E y := by
  rfl

/-- A scale-fixed vector generates a translation jet of pure affine weight `n * w`. -/
theorem euler_iterate_of_commutator
    (T E : Derivation k L L) (w : k) (x : L)
    (hET : ∀ y : L, E (T y) - T (E y) = w • T y)
    (hEx : E x = 0) (n : ℕ) :
    E ((T : L → L)^[n] x) = ((n : k) * w) • ((T : L → L)^[n] x) := by
  induction n with
  | zero => simpa using hEx
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have h := hET ((T : L → L)^[n] x)
      rw [sub_eq_iff_eq_add] at h
      rw [h, ih, Derivation.map_smul]
      push_cast
      module

/-- An affine direction raises translation order by one and has a diagonal Ward-weight term. -/
theorem affineLawDerivation_iterate_translation
    (T E : Derivation k L L) (w a b : k) (x : L)
    (hET : ∀ y : L, E (T y) - T (E y) = w • T y)
    (hEx : E x = 0) (n : ℕ) :
    affineLawDerivation T E a b ((T : L → L)^[n] x) =
      a • ((T : L → L)^[n + 1] x) +
        (b * ((n : k) * w)) • ((T : L → L)^[n] x) := by
  rw [affineLawDerivation_apply,
    euler_iterate_of_commutator T E w x hET hEx n]
  rw [Function.iterate_succ_apply']
  simp [smul_smul]

/-- Recursive lower-triangular coefficient of `T^[j] x` in the `n`-th affine-law jet. -/
def affineJetCoeff (a q : k) : ℕ → ℕ → k
  | 0, j => if j = 0 then 1 else 0
  | n + 1, j =>
      a * (if j = 0 then 0 else affineJetCoeff a q n (j - 1)) +
        q * (j : k) * affineJetCoeff a q n j

/-- The affine jet coefficients vanish strictly above the diagonal. -/
theorem affineJetCoeff_eq_zero_of_lt (a q : k) :
    ∀ {n j : ℕ}, n < j → affineJetCoeff a q n j = 0 := by
  intro n
  induction n with
  | zero =>
      intro j hj
      simp [affineJetCoeff, Nat.ne_zero_of_lt hj]
  | succ n ih =>
      intro j hj
      have hj0 : j ≠ 0 := by omega
      have hnj : n < j := by omega
      have hnpred : n < j - 1 := by omega
      rw [affineJetCoeff, ih hnj, ih hnpred]
      simp [hj0]

/-- The diagonal coefficient of the `n`-th affine jet is `a^n`. -/
@[simp]
theorem affineJetCoeff_diagonal (a q : k) : ∀ n : ℕ,
    affineJetCoeff a q n n = a ^ n := by
  intro n
  induction n with
  | zero => simp [affineJetCoeff]
  | succ n ih =>
      rw [affineJetCoeff]
      have hzero := affineJetCoeff_eq_zero_of_lt a q (Nat.lt_succ_self n)
      rw [hzero]
      simp [ih, pow_succ, mul_comm]

/-- Reindexing identity that advances one row of the affine jet triangle. -/
theorem affineJet_sum_step
    (n : ℕ) (C : ℕ → k) (Y : ℕ → L) (a q : k)
    (hC : C (n + 1) = 0) :
    (∑ j ∈ Finset.range (n + 1),
      C j • (a • Y (j + 1) + (q * (j : k)) • Y j)) =
    ∑ j ∈ Finset.range (n + 2),
      (a * (if j = 0 then 0 else C (j - 1)) + q * (j : k) * C j) • Y j := by
  have hshift :
      (∑ j ∈ Finset.range (n + 1), (C j * a) • Y (j + 1)) =
      ∑ j ∈ Finset.range (n + 2),
        (a * (if j = 0 then 0 else C (j - 1))) • Y j := by
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [if_pos, mul_zero, zero_smul, Nat.succ_ne_zero, if_false,
      Nat.add_sub_cancel]
    rw [add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_comm]
  have hdiag :
      (∑ j ∈ Finset.range (n + 1), (C j * (q * (j : k))) • Y j) =
      ∑ j ∈ Finset.range (n + 2), (q * (j : k) * C j) • Y j := by
    conv_rhs => rw [Finset.sum_range_succ]
    rw [hC]
    simp only [mul_zero, zero_smul, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    ring
  calc
    (∑ j ∈ Finset.range (n + 1),
        C j • (a • Y (j + 1) + (q * (j : k)) • Y j)) =
      (∑ j ∈ Finset.range (n + 1), (C j * a) • Y (j + 1)) +
        ∑ j ∈ Finset.range (n + 1), (C j * (q * (j : k))) • Y j := by
          simp only [smul_add, smul_smul, Finset.sum_add_distrib]
    _ = (∑ j ∈ Finset.range (n + 2),
          (a * (if j = 0 then 0 else C (j - 1))) • Y j) +
        ∑ j ∈ Finset.range (n + 2), (q * (j : k) * C j) • Y j := by
          rw [hshift, hdiag]
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [add_smul]

/-- The finite lower-triangular expansion of an affine-law jet in translation jets. -/
def affineJetExpansion
    (T : Derivation k L L) (a q : k) (x : L) (n : ℕ) : L :=
  ∑ j ∈ Finset.range (n + 1),
    affineJetCoeff a q n j • ((T : L → L)^[j] x)

/-- Every iterated affine-law jet has the recursive lower-triangular translation expansion. -/
theorem affineLaw_iterate_eq_expansion
    (T E : Derivation k L L) (w a b : k) (x : L)
    (hET : ∀ y : L, E (T y) - T (E y) = w • T y)
    (hEx : E x = 0) : ∀ n : ℕ,
    ((affineLawDerivation T E a b : L → L)^[n] x) =
      affineJetExpansion T a (b * w) x n := by
  intro n
  induction n with
  | zero => simp [affineJetExpansion, affineJetCoeff]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [affineJetExpansion, map_sum, Derivation.map_smul]
      have haction : ∀ j : ℕ,
          affineLawDerivation T E a b ((T : L → L)^[j] x) =
            a • ((T : L → L)^[j + 1] x) +
              ((b * w) * (j : k)) • ((T : L → L)^[j] x) := by
        intro j
        have h := affineLawDerivation_iterate_translation T E w a b x hET hEx j
        convert h using 1
        ring_nf
      simp_rw [haction]
      have hzero : affineJetCoeff a (b * w) n (n + 1) = 0 :=
        affineJetCoeff_eq_zero_of_lt a (b * w) (Nat.lt_succ_self n)
      exact affineJet_sum_step n (affineJetCoeff a (b * w) n)
        (fun j => ((T : L → L)^[j] x)) a (b * w) hzero

/-- The finite affine-law conversion matrix on the first `N` translation jets. -/
def affineJetMatrix (a q : k) (N : ℕ) : Matrix (Fin N) (Fin N) k :=
  fun i j => affineJetCoeff a q i j

/-- The finite affine jet matrix is lower triangular. -/
theorem affineJetMatrix_lowerTriangular (a q : k) (N : ℕ) :
    (affineJetMatrix a q N).BlockTriangular
      (fun i : Fin N => OrderDual.toDual i) := by
  intro i j hij
  exact affineJetCoeff_eq_zero_of_lt a q (OrderDual.toDual_lt_toDual.mp hij)

/-- The finite affine jet matrix has diagonal `a^i`. -/
@[simp]
theorem affineJetMatrix_diag (a q : k) (N : ℕ) (i : Fin N) :
    affineJetMatrix a q N i i = a ^ (i : ℕ) := by
  exact affineJetCoeff_diagonal a q i

/-- A nonzero translation coefficient makes every finite affine jet matrix nonsingular. -/
theorem affineJetMatrix_det_ne_zero {a q : k} (ha : a ≠ 0) (N : ℕ) :
    (affineJetMatrix a q N).det ≠ 0 := by
  rw [Matrix.det_of_lowerTriangular _ (affineJetMatrix_lowerTriangular a q N)]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  rw [affineJetMatrix_diag]
  exact pow_ne_zero _ ha

/-- The finite affine-law jet packet is exactly the matrix image of the translation packet. -/
theorem affineJetPacket_eq_matrixLinearForms
    (T E : Derivation k L L) (w a b : k) (x : L)
    (hET : ∀ y : L, E (T y) - T (E y) = w • T y)
    (hEx : E x = 0) (N : ℕ) (i : Fin N) :
    ((affineLawDerivation T E a b : L → L)^[(i : ℕ)] x) =
      matrixLinearForms (affineJetMatrix a (b * w) N)
        (fun j : Fin N => ((T : L → L)^[(j : ℕ)] x)) i := by
  rw [affineLaw_iterate_eq_expansion T E w a b x hET hEx i]
  simp only [affineJetExpansion, matrixLinearForms, affineJetMatrix]
  rw [Fin.sum_univ_eq_sum_range
    (fun j => algebraMap k L (affineJetCoeff a (b * w) (i : ℕ) j) *
      ((T : L → L)^[j] x)) N]
  simp only [Algebra.smul_def]
  apply Finset.sum_subset
  · intro j hj
    exact Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hj) i.isLt)
  · intro j hjN hji
    have hij : (i : ℕ) < j := by
      exact Nat.lt_of_not_ge (by simpa [Finset.mem_range] using hji)
    rw [affineJetCoeff_eq_zero_of_lt a (b * w) hij]
    simp

/-- Algebraic independence of a finite translation packet transfers to every affine direction
with nonzero translation coefficient. -/
theorem affineJetPacket_algebraicIndependent
    (T E : Derivation k L L) (w a b : k) (x : L)
    (hET : ∀ y : L, E (T y) - T (E y) = w • T y)
    (hEx : E x = 0) (ha : a ≠ 0) (N : ℕ)
    (hT : AlgebraicIndependent k
      (fun j : Fin N => ((T : L → L)^[(j : ℕ)] x))) :
    AlgebraicIndependent k
      (fun i : Fin N => ((affineLawDerivation T E a b : L → L)^[(i : ℕ)] x)) := by
  have hrows : LinearIndependent k (affineJetMatrix a (b * w) N).row :=
    Matrix.linearIndependent_rows_of_det_ne_zero
      (affineJetMatrix_det_ne_zero ha N)
  have hforms := algebraicIndependent_matrixLinearForms_of_linearIndependent_rows
    (affineJetMatrix a (b * w) N) hrows
    (fun j : Fin N => ((T : L → L)^[(j : ℕ)] x)) hT
  have hpacket :
      (fun i : Fin N =>
        ((affineLawDerivation T E a b : L → L)^[(i : ℕ)] x)) =
        matrixLinearForms (affineJetMatrix a (b * w) N)
          (fun j : Fin N => ((T : L → L)^[(j : ℕ)] x)) := by
    funext i
    exact affineJetPacket_eq_matrixLinearForms T E w a b x hET hEx N i
  rw [hpacket]
  exact hforms

/-- A hypertranscendental translation orbit remains algebraically independent for every affine
law with nonzero translation coefficient. -/
theorem affineLaw_jet_algebraicIndependent
    (T E : Derivation k L L) (w a b : k) (x : L)
    (hET : ∀ y : L, E (T y) - T (E y) = w • T y)
    (hEx : E x = 0) (ha : a ≠ 0)
    (hT : AlgebraicIndependent k
      (fun n : ℕ => ((T : L → L)^[n] x))) :
    AlgebraicIndependent k
      (fun n : ℕ => ((affineLawDerivation T E a b : L → L)^[n] x)) := by
  apply algebraicIndependent_of_finite_type
  intro s hs
  letI : Fintype s := hs.fintype
  let N : ℕ := s.toFinset.sup id + 1
  let e : s → Fin N := fun i =>
    ⟨i.1, Nat.lt_succ_of_le (Finset.le_sup (f := id)
      (show i.1 ∈ s.toFinset by simpa using i.2))⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Subtype.ext
    exact Fin.ext_iff.mp hij
  have hTfin : AlgebraicIndependent k
      (fun j : Fin N => ((T : L → L)^[(j : ℕ)] x)) := by
    exact hT.comp (fun j : Fin N => (j : ℕ)) Fin.val_injective
  have hDfin := affineJetPacket_algebraicIndependent
    T E w a b x hET hEx ha N hTfin
  have hsub := hDfin.comp e he
  simpa [Function.comp_def, e] using hsub

/-- Exact affine horizon: under translation hypertranscendence and scale invariance, the complete
mixed jet tower is algebraically independent exactly off the pure dilation ray. -/
theorem affineLaw_jet_algebraicIndependent_iff
    (T E : Derivation k L L) (w a b : k) (x : L)
    (hET : ∀ y : L, E (T y) - T (E y) = w • T y)
    (hEx : E x = 0)
    (hT : AlgebraicIndependent k
      (fun n : ℕ => ((T : L → L)^[n] x))) :
    AlgebraicIndependent k
        (fun n : ℕ => ((affineLawDerivation T E a b : L → L)^[n] x)) ↔
      a ≠ 0 := by
  constructor
  · intro h ha
    subst a
    have hz : ((affineLawDerivation T E 0 b : L → L)^[1] x) = 0 := by
      simp [affineLawDerivation_apply, hEx]
    exact h.ne_zero 1 hz
  · intro ha
    exact affineLaw_jet_algebraicIndependent T E w a b x hET hEx ha hT

section CoefficientField

variable {K : Type*} [Field K] [Algebra k K] [Algebra K L]
  [IsScalarTower k K L]

/-- The affine jet conversion matrix after extending coefficients from the derivation-constant
field `k` to an arbitrary intermediate coefficient field `K`. -/
def affineJetMatrixBaseChange (a q : k) (N : ℕ) : Matrix (Fin N) (Fin N) K :=
  (affineJetMatrix a q N).map (algebraMap k K)

/-- A nonzero translation coefficient remains the exact nonsingularity condition after extending
the coefficient field. -/
theorem affineJetMatrixBaseChange_det_ne_zero {a q : k} (ha : a ≠ 0) (N : ℕ) :
    (affineJetMatrixBaseChange (K := K) a q N).det ≠ 0 := by
  have hmap := (algebraMap k K).map_det (affineJetMatrix a q N)
  change algebraMap k K (affineJetMatrix a q N).det =
    (affineJetMatrixBaseChange (K := K) a q N).det at hmap
  rw [← hmap]
  exact (map_ne_zero_iff (algebraMap k K)
    (FaithfulSMul.algebraMap_injective k K)).mpr
      (affineJetMatrix_det_ne_zero ha N)

/-- The finite affine-law jet packet is the base-changed matrix image of the translation packet
over every intermediate coefficient field. -/
theorem affineJetPacket_eq_matrixLinearForms_baseChange
    (T E : Derivation k L L) (w a b : k) (x : L)
    (hET : ∀ y : L, E (T y) - T (E y) = w • T y)
    (hEx : E x = 0) (N : ℕ) (i : Fin N) :
    ((affineLawDerivation T E a b : L → L)^[(i : ℕ)] x) =
      matrixLinearForms (affineJetMatrixBaseChange (K := K) a (b * w) N)
        (fun j : Fin N => ((T : L → L)^[(j : ℕ)] x)) i := by
  rw [affineJetPacket_eq_matrixLinearForms T E w a b x hET hEx N i]
  simp [matrixLinearForms, affineJetMatrixBaseChange,
    IsScalarTower.algebraMap_apply k K L]

/-- Finite affine-law jets inherit algebraic independence over the actual coefficient field `K`,
even though the derivations need only be linear over the smaller constant field `k`. -/
theorem affineJetPacket_algebraicIndependent_baseChange
    (T E : Derivation k L L) (w a b : k) (x : L)
    (hET : ∀ y : L, E (T y) - T (E y) = w • T y)
    (hEx : E x = 0) (ha : a ≠ 0) (N : ℕ)
    (hT : AlgebraicIndependent K
      (fun j : Fin N => ((T : L → L)^[(j : ℕ)] x))) :
    AlgebraicIndependent K
      (fun i : Fin N => ((affineLawDerivation T E a b : L → L)^[(i : ℕ)] x)) := by
  have hrows : LinearIndependent K
      (affineJetMatrixBaseChange (K := K) a (b * w) N).row :=
    Matrix.linearIndependent_rows_of_det_ne_zero
      (affineJetMatrixBaseChange_det_ne_zero (K := K) ha N)
  have hforms := algebraicIndependent_matrixLinearForms_of_linearIndependent_rows
    (affineJetMatrixBaseChange (K := K) a (b * w) N) hrows
    (fun j : Fin N => ((T : L → L)^[(j : ℕ)] x)) hT
  have hpacket :
      (fun i : Fin N =>
        ((affineLawDerivation T E a b : L → L)^[(i : ℕ)] x)) =
        matrixLinearForms (affineJetMatrixBaseChange (K := K) a (b * w) N)
          (fun j : Fin N => ((T : L → L)^[(j : ℕ)] x)) := by
    funext i
    exact affineJetPacket_eq_matrixLinearForms_baseChange
      T E w a b x hET hEx N i
  rw [hpacket]
  exact hforms

/-- Translation hypertranscendence over an arbitrary intermediate coefficient field transfers to
every affine law having nonzero translation symbol. -/
theorem affineLaw_jet_algebraicIndependent_baseChange
    (T E : Derivation k L L) (w a b : k) (x : L)
    (hET : ∀ y : L, E (T y) - T (E y) = w • T y)
    (hEx : E x = 0) (ha : a ≠ 0)
    (hT : AlgebraicIndependent K
      (fun n : ℕ => ((T : L → L)^[n] x))) :
    AlgebraicIndependent K
      (fun n : ℕ => ((affineLawDerivation T E a b : L → L)^[n] x)) := by
  apply algebraicIndependent_of_finite_type
  intro s hs
  letI : Fintype s := hs.fintype
  let N : ℕ := s.toFinset.sup id + 1
  let e : s → Fin N := fun i =>
    ⟨i.1, Nat.lt_succ_of_le (Finset.le_sup (f := id)
      (show i.1 ∈ s.toFinset by simpa using i.2))⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Subtype.ext
    exact Fin.ext_iff.mp hij
  have hTfin : AlgebraicIndependent K
      (fun j : Fin N => ((T : L → L)^[(j : ℕ)] x)) := by
    exact hT.comp (fun j : Fin N => (j : ℕ)) Fin.val_injective
  have hDfin := affineJetPacket_algebraicIndependent_baseChange
    T E w a b x hET hEx ha N hTfin
  have hsub := hDfin.comp e he
  simpa [Function.comp_def, e] using hsub

/-- Exact coefficient-field affine horizon: under translation hypertranscendence over `K`, the
complete mixed jet tower is algebraically independent over `K` exactly off pure dilation. -/
theorem affineLaw_jet_algebraicIndependent_baseChange_iff
    (T E : Derivation k L L) (w a b : k) (x : L)
    (hET : ∀ y : L, E (T y) - T (E y) = w • T y)
    (hEx : E x = 0)
    (hT : AlgebraicIndependent K
      (fun n : ℕ => ((T : L → L)^[n] x))) :
    AlgebraicIndependent K
        (fun n : ℕ => ((affineLawDerivation T E a b : L → L)^[n] x)) ↔
      a ≠ 0 := by
  constructor
  · intro h ha
    subst a
    have hz : ((affineLawDerivation T E 0 b : L → L)^[1] x) = 0 := by
      simp [affineLawDerivation_apply, hEx]
    exact h.ne_zero 1 hz
  · intro ha
    exact affineLaw_jet_algebraicIndependent_baseChange
      T E w a b x hET hEx ha hT

end CoefficientField

end

end GaloisForLFunctions.HTGeometry
