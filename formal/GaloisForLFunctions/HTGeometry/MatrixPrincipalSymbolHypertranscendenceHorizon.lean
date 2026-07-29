import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolDeterminantHorizon
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Matrix principal-symbol hypertranscendence horizon

This file identifies the complete joint algebraic-dependence spectrum of a filtered finite-rank
observable packet with the singular set of its matrix principal symbols.  The finite core is an
exact block-triangular criterion: linear forms in an algebraically independent source packet are
algebraically independent precisely when every diagonal block is nonsingular.

When the layer symbols also satisfy the flat consecutive-square law, the entire countable
dependence spectrum collapses to either the whole law space or one first-layer determinantal
hypersurface.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set

variable {K L g ι : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype ι] [DecidableEq ι]

/-- Reverse layer order: a block-triangular matrix for this order is lower triangular in the
ordinary filtration order, so layer `n` may depend on layers `< n` but not on layers `> n`. -/
def matrixPrincipalLayerOrder {N : ℕ} : Fin N × ι → OrderDual (Fin N) :=
  fun p ↦ OrderDual.toDual p.1

/-- The canonical coordinates on one layer fiber of `matrixPrincipalLayerOrder`. -/
def matrixPrincipalLayerEquiv {N : ℕ} (n : Fin N) :
    ι ≃ {p : Fin N × ι // matrixPrincipalLayerOrder p = OrderDual.toDual n} where
  toFun i := ⟨(n, i), rfl⟩
  invFun p := p.1.2
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext (congrArg OrderDual.ofDual p.2).symm rfl

/-- A complete packet `y` is realized by matrix principal symbols relative to a source packet `u`
if every finite initial segment is obtained by a block-triangular linear transformation whose
diagonal-block determinants are the prescribed symbol determinants.  This is the intrinsic finite
principal-symbol interface needed by the complete algebraic-independence theorem. -/
def MatrixPrincipalPacketRealization
    (u y : ℕ → ι → L) (symbol : ℕ → Matrix ι ι K) : Prop :=
  ∀ N : ℕ, ∃ M : Matrix (Fin N × ι) (Fin N × ι) K,
    (fun p : Fin N × ι ↦ y p.1 p.2) =
        matrixLinearForms M (fun p : Fin N × ι ↦ u p.1 p.2) ∧
      M.BlockTriangular matrixPrincipalLayerOrder ∧
      ∀ n : Fin N,
        M.toSquareBlock matrixPrincipalLayerOrder (OrderDual.toDual n) =
          Matrix.reindex (matrixPrincipalLayerEquiv n) (matrixPrincipalLayerEquiv n) (symbol n)

/-- **Finite block principal-symbol criterion.**  A block-triangular square transformation of an
algebraically independent packet preserves algebraic independence exactly when every diagonal
block is nonsingular. -/
theorem algebraicIndependent_matrixLinearForms_blockTriangular_iff
    {N : ℕ} (M : Matrix (Fin N × ι) (Fin N × ι) K)
    (x : Fin N × ι → L) (hx : AlgebraicIndependent K x)
    (hM : M.BlockTriangular matrixPrincipalLayerOrder) :
    AlgebraicIndependent K (matrixLinearForms M x) ↔
      ∀ n : Fin N,
        (M.toSquareBlock matrixPrincipalLayerOrder (OrderDual.toDual n)).det ≠ 0 := by
  constructor
  · intro hy n
    have hyli : LinearIndependent K (matrixLinearForms M x) :=
      hy.linearIndependent
    have hcomp :
        (Fintype.linearCombination K x) ∘ M.row = matrixLinearForms M x := by
      funext i
      simp [Fintype.linearCombination_apply,
        matrixLinearForms, Algebra.smul_def]
    have hrows : LinearIndependent K M.row := by
      apply LinearIndependent.of_comp (Fintype.linearCombination K x)
      rw [hcomp]
      exact hyli
    obtain ⟨R, hMR⟩ :=
      exists_matrix_rightInverse_of_linearIndependent_rows M hrows
    have hdet : M.det ≠ 0 := by
      intro hzero
      have hdetEq := congrArg Matrix.det hMR
      simp [Matrix.det_mul, hzero] at hdetEq
    rw [hM.det_fintype] at hdet
    exact (Finset.prod_ne_zero_iff.mp hdet) (OrderDual.toDual n)
      (Finset.mem_univ (OrderDual.toDual n))
  · intro hblocks
    have hdet : M.det ≠ 0 := by
      rw [hM.det_fintype]
      exact Finset.prod_ne_zero_iff.mpr fun n _ ↦ hblocks (OrderDual.ofDual n)
    exact algebraicIndependent_matrixLinearForms_of_linearIndependent_rows
      M (Matrix.linearIndependent_rows_of_det_ne_zero hdet) x hx

/-- **Complete matrix principal-symbol criterion.**  For a complete finite-rank filtered packet,
joint algebraic independence is equivalent to nonsingularity of every matrix principal symbol.
Thus the countable union of determinant horizons is not merely a formal characteristic set: it is
the exact joint dependence spectrum. -/
theorem matrixPrincipalPacket_algebraicIndependent_iff
    (u y : ℕ → ι → L) (symbol : ℕ → Matrix ι ι K)
    (hreal : MatrixPrincipalPacketRealization u y symbol)
    (hu : AlgebraicIndependent K (fun p : ℕ × ι ↦ u p.1 p.2)) :
    AlgebraicIndependent K (fun p : ℕ × ι ↦ y p.1 p.2) ↔
      ∀ n : ℕ, (symbol n).det ≠ 0 := by
  constructor
  · intro hy n
    obtain ⟨M, hpacket, htri, hdiag⟩ := hreal (n + 1)
    let e : Fin (n + 1) × ι → ℕ × ι := fun p ↦ ((p.1 : ℕ), p.2)
    have he : Function.Injective e := by
      intro p q hpq
      apply Prod.ext
      · exact Fin.ext (congrArg Prod.fst hpq)
      · exact congrArg (fun z : ℕ × ι ↦ z.2) hpq
    have huN : AlgebraicIndependent K
        (fun p : Fin (n + 1) × ι ↦ u p.1 p.2) := by
      simpa [e, Function.comp_def] using hu.comp e he
    have hyN : AlgebraicIndependent K
        (fun p : Fin (n + 1) × ι ↦ y p.1 p.2) := by
      simpa [e, Function.comp_def] using hy.comp e he
    rw [hpacket] at hyN
    have hblocks :=
      (algebraicIndependent_matrixLinearForms_blockTriangular_iff
        M (fun p : Fin (n + 1) × ι ↦ u p.1 p.2) huN htri).mp hyN
    have hn := hblocks (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))
    rw [hdiag ⟨n, Nat.lt_succ_self n⟩, Matrix.det_reindex_self] at hn
    exact hn
  · intro hsymbols
    apply algebraicIndependent_of_finite_type
    intro t ht
    letI : Fintype t := ht.fintype
    let N : ℕ := t.toFinset.sup (fun p : ℕ × ι ↦ p.1) + 1
    let e : t → Fin N × ι := fun p ↦
      (⟨p.1.1, Nat.lt_succ_of_le (Finset.le_sup
        (f := fun q : ℕ × ι ↦ q.1)
        (show p.1 ∈ t.toFinset by simp [p.2]))⟩, p.1.2)
    have he : Function.Injective e := by
      intro p q hpq
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun z : Fin N × ι ↦ (z.1 : ℕ)) hpq
      · exact congrArg (fun z : Fin N × ι ↦ z.2) hpq
    obtain ⟨M, hpacket, htri, hdiag⟩ := hreal N
    let sourceN : Fin N × ι → L := fun p ↦ u p.1 p.2
    have hsourceN : AlgebraicIndependent K sourceN := by
      let inc : Fin N × ι → ℕ × ι := fun p ↦ ((p.1 : ℕ), p.2)
      have hinc : Function.Injective inc := by
        intro p q hpq
        apply Prod.ext
        · exact Fin.ext (congrArg Prod.fst hpq)
        · exact congrArg (fun z : ℕ × ι ↦ z.2) hpq
      simpa [sourceN, inc, Function.comp_def] using hu.comp inc hinc
    have hpacketAI : AlgebraicIndependent K
        (fun p : Fin N × ι ↦ y p.1 p.2) := by
      rw [hpacket]
      apply (algebraicIndependent_matrixLinearForms_blockTriangular_iff
        M sourceN hsourceN htri).mpr
      intro n
      rw [hdiag n, Matrix.det_reindex_self]
      exact hsymbols n
    simpa [e, Function.comp_def] using hpacketAI.comp e he

/-- Law directions whose complete matrix packet is algebraically dependent. -/
def matrixPacketDependentSet
    (jet : g → ℕ → ι → L) : Set g :=
  {A | ¬ AlgebraicIndependent K (fun p : ℕ × ι ↦ jet A p.1 p.2)}

/-- The complete dependence spectrum of realized matrix-principal packets is exactly the union of
the layerwise determinant horizons. -/
theorem matrixPacketDependentSet_eq_characteristicSet
    (u : ℕ → ι → L) (jet : g → ℕ → ι → L)
    (symbol : ℕ → g → Matrix ι ι K)
    (hreal : ∀ A, MatrixPrincipalPacketRealization u (jet A) (fun n ↦ symbol n A))
    (hu : AlgebraicIndependent K (fun p : ℕ × ι ↦ u p.1 p.2)) :
    matrixPacketDependentSet (K := K) jet = matrixSymbolCharacteristicSet symbol := by
  ext A
  change (¬ AlgebraicIndependent K (fun p : ℕ × ι ↦ jet A p.1 p.2)) ↔
    ∃ n, (symbol n A).det = 0
  rw [matrixPrincipalPacket_algebraicIndependent_iff
    u (jet A) (fun n ↦ symbol n A) (hreal A) hu]
  push Not
  rfl

/-- **Holographic determinant horizon.**  In a flat matrix-principal law system with one regular
direction, the exact complete joint dependence spectrum is the single first-layer determinantal
locus. -/
theorem matrixPacketDependentSet_eq_firstSingularSet_of_flat
    (u : ℕ → ι → L) (jet : g → ℕ → ι → L)
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixPrincipalSymbolFlat symbol)
    (A₀ : g) (hA₀ : ∀ n, (symbol n A₀).det ≠ 0)
    (hreal : ∀ A, MatrixPrincipalPacketRealization u (jet A) (fun n ↦ symbol n A))
    (hu : AlgebraicIndependent K (fun p : ℕ × ι ↦ u p.1 p.2)) :
    matrixPacketDependentSet (K := K) jet = matrixSymbolSingularSet symbol 0 := by
  rw [matrixPacketDependentSet_eq_characteristicSet u jet symbol hreal hu]
  exact matrixSymbolCharacteristicSet_eq_firstSingularSet symbol hflat A₀ hA₀

/-- **Exact flat finite-rank dichotomy.**  The complete joint dependence spectrum of a realized
flat matrix-principal system is either every law direction, or one first-layer determinantal
horizon supporting a nonempty algebraically independent phase. -/
theorem matrixPrincipalPacket_flat_dependenceSpectrum_dichotomy
    (u : ℕ → ι → L) (jet : g → ℕ → ι → L)
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixPrincipalSymbolFlat symbol)
    (hreal : ∀ A, MatrixPrincipalPacketRealization u (jet A) (fun n ↦ symbol n A))
    (hu : AlgebraicIndependent K (fun p : ℕ × ι ↦ u p.1 p.2)) :
    matrixPacketDependentSet (K := K) jet = Set.univ ∨
      ∃ A₀ : g, (∀ n, (symbol n A₀).det ≠ 0) ∧
        matrixPacketDependentSet (K := K) jet = matrixSymbolSingularSet symbol 0 := by
  rw [matrixPacketDependentSet_eq_characteristicSet u jet symbol hreal hu]
  exact matrixPrincipalSymbolFlat_characteristicSet_dichotomy symbol hflat

end

end GaloisForLFunctions.HTGeometry
