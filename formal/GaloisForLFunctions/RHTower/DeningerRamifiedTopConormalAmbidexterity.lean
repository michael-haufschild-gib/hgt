import GaloisForLFunctions.RHTower.DeningerPowerMapFiniteFree
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Ramified top-conormal ambidexterity

For the ramified power map, raw pullback occupies residue class `0`, whereas Grothendieck
residue extracts the final residue class.  This file constructs the corrected source map

`g(X) ↦ X^(n-1) g(X^n)`

and proves its exact power-semigroup coherence.  On finite Hilbert blocks, final-coordinate
embedding has final-coordinate extraction as its literal adjoint; after scaling by `√n`, their
composite is `n • id`.  The raw power embedding is instead transpose to final-coordinate
extraction for the anti-diagonal Frobenius residue pairing.

The capstone classification proves that a coherent monomial shift for every positive power
degree is forced to be either `0` (raw pullback) or `n-1` (top conormal).  No Xi divisor or
purity hypothesis enters any statement.
-/

namespace GaloisForLFunctions

noncomputable section

open Polynomial

/-! ## Algebraic shifted power sectors -/

/-- Power pullback shifted into residue class `r`: `g(X) ↦ X^r g(X^n)`. -/
def deningerShiftedPowerPullback (n r : ℕ) (f : Polynomial ℤ) : Polynomial ℤ :=
  Polynomial.expand ℤ n f * Polynomial.X ^ r

/-- Extraction of the same residue class is a left inverse to shifted power pullback. -/
theorem powerMapResidueComponent_deningerShiftedPowerPullback
    {n r : ℕ} (hn : 0 < n) (hr : r < n) (f : Polynomial ℤ) :
    powerMapResidueComponent n (deningerShiftedPowerPullback n r f) ⟨r, hr⟩ = f := by
  ext k
  rw [powerMapResidueComponent_coeff hn]
  simp only [deningerShiftedPowerPullback, Polynomial.coeff_mul_X_pow']
  rw [if_pos (by omega : r ≤ n * k + r)]
  rw [show n * k + r - r = n * k by omega]
  rw [Polynomial.coeff_expand hn, if_pos ⟨k, rfl⟩]
  congr 1
  exact Nat.mul_div_cancel_left k hn

/-- Shifted power sectors compose by the affine radix law `r ↦ m*r+s`. -/
theorem deningerShiftedPowerPullback_comp (m n r s : ℕ) (f : Polynomial ℤ) :
    deningerShiftedPowerPullback m s (deningerShiftedPowerPullback n r f) =
      deningerShiftedPowerPullback (m * n) (m * r + s) f := by
  simp only [deningerShiftedPowerPullback]
  rw [map_mul, powerMap_tower, map_pow, Polynomial.expand_X]
  rw [← pow_mul]
  rw [mul_assoc, ← pow_add]

/-- The corrected ramified source map occupies the top-conormal residue class. -/
def deningerTopConormalPowerPullback (n : ℕ) (f : Polynomial ℤ) : Polynomial ℤ :=
  deningerShiftedPowerPullback n (n - 1) f

/-- Top-conormal power pullbacks compose strictly for all positive degrees. -/
theorem deningerTopConormalPowerPullback_comp {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (f : Polynomial ℤ) :
    deningerTopConormalPowerPullback m (deningerTopConormalPowerPullback n f) =
      deningerTopConormalPowerPullback (m * n) f := by
  rw [deningerTopConormalPowerPullback, deningerTopConormalPowerPullback,
    deningerShiftedPowerPullback_comp, deningerTopConormalPowerPullback]
  congr 1
  have hle : m ≤ m * n := Nat.le_mul_of_pos_right m hn
  rw [Nat.mul_sub_left_distrib]
  omega

/-- The top residue component recovers the source polynomial exactly. -/
theorem powerMapResidueComponent_deningerTopConormalPowerPullback
    {n : ℕ} (hn : 0 < n) (f : Polynomial ℤ) :
    powerMapResidueComponent n (deningerTopConormalPowerPullback n f)
      ⟨n - 1, by omega⟩ = f := by
  exact powerMapResidueComponent_deningerShiftedPowerPullback hn (by omega) f

/-! ## Classification of strict coherent monomial sectors -/

/-- **Only raw and top-conormal monomial sectors are coherent.**

If `r n` is a residue-class shift for every positive degree, lies in `[0,n)`, and obeys the
strict composition law `r(mn)=m*r(n)+r(m)`, then it is identically `0` or identically `n-1`.
-/
theorem deningerCoherentPowerShift_eq_raw_or_topConormal (r : ℕ → ℕ)
    (hrange : ∀ n, 0 < n → r n < n)
    (hcomp : ∀ m n, 0 < m → 0 < n → r (m * n) = m * r n + r m) :
    (∀ n, 0 < n → r n = 0) ∨ (∀ n, 0 < n → r n = n - 1) := by
  have hr2 : r 2 = 0 ∨ r 2 = 1 := by
    have h := hrange 2 (by omega)
    omega
  rcases hr2 with h0 | h1
  · left
    intro n hn
    have h2n := hcomp 2 n (by omega) hn
    have hn2 := hcomp n 2 hn (by omega)
    have heq : 2 * r n + r 2 = n * r 2 + r n := by
      calc
        2 * r n + r 2 = r (2 * n) := h2n.symm
        _ = r (n * 2) := by rw [Nat.mul_comm]
        _ = n * r 2 + r n := hn2
    rw [h0] at heq
    omega
  · right
    intro n hn
    have h2n := hcomp 2 n (by omega) hn
    have hn2 := hcomp n 2 hn (by omega)
    have heq : 2 * r n + r 2 = n * r 2 + r n := by
      calc
        2 * r n + r 2 = r (2 * n) := h2n.symm
        _ = r (n * 2) := by rw [Nat.mul_comm]
        _ = n * r 2 + r n := hn2
    rw [h1] at heq
    omega

end

end GaloisForLFunctions

namespace RHTower

noncomputable section

/-! ## Finite ramified Hilbert blocks -/

/-- Finite coefficient Hilbert space with its standard coordinate metric. -/
abbrev DeningerRamifiedBlockHilbert (ι : Type*) [Fintype ι] :=
  PiLp 2 (fun _ : ι => ℂ)

/-- Embed a finite source packet into the final residue coordinate of a ramified block. -/
def deningerTopConormalEmbedding {ι : Type*} [Fintype ι] (n : ℕ)
    (x : DeningerRamifiedBlockHilbert ι) :
    DeningerRamifiedBlockHilbert (ι × Fin (n + 1)) :=
  WithLp.toLp 2 (fun p => if p.2 = Fin.last n then x.ofLp p.1 else 0)

/-- Extract the final residue coordinate from a ramified block. -/
def deningerTopConormalResidue {ι : Type*} [Fintype ι] (n : ℕ)
    (y : DeningerRamifiedBlockHilbert (ι × Fin (n + 1))) :
    DeningerRamifiedBlockHilbert ι :=
  WithLp.toLp 2 (fun i => y.ofLp (i, Fin.last n))

/-- Raw power pullback occupies residue coordinate zero. -/
def deningerRawPowerEmbedding {ι : Type*} [Fintype ι] (n : ℕ)
    (x : DeningerRamifiedBlockHilbert ι) :
    DeningerRamifiedBlockHilbert (ι × Fin (n + 1)) :=
  WithLp.toLp 2 (fun p => if p.2 = 0 then x.ofLp p.1 else 0)

/-- Extract residue coordinate zero.  Multiplication by the rank gives the coordinate model of
the ordinary module trace on a ramified power block. -/
def deningerRawPowerResidue {ι : Type*} [Fintype ι] (n : ℕ)
    (y : DeningerRamifiedBlockHilbert (ι × Fin (n + 1))) :
    DeningerRamifiedBlockHilbert ι :=
  WithLp.toLp 2 (fun i => y.ofLp (i, 0))

/-- Anti-diagonal Frobenius residue pairing on a truncated monomial block. -/
def deningerFiniteResiduePair (n : ℕ)
    (x y : DeningerRamifiedBlockHilbert (Fin (n + 1))) : ℂ :=
  ∑ i, x.ofLp i * y.ofLp i.rev

/-- Product-block form of the anti-diagonal Frobenius residue pairing. -/
def deningerFiniteBlockResiduePair (k n : ℕ)
    (x y : DeningerRamifiedBlockHilbert (Fin (k + 1) × Fin (n + 1))) : ℂ :=
  ∑ i, ∑ r, x.ofLp (i, r) * y.ofLp (i.rev, r.rev)

/-- **Grothendieck residue transpose.** Raw power pullback is transpose, for the
anti-diagonal Frobenius pairings, to final-residue extraction. -/
theorem deningerFiniteBlockResiduePair_rawPowerEmbedding
    (k n : ℕ) (x : DeningerRamifiedBlockHilbert (Fin (k + 1)))
    (y : DeningerRamifiedBlockHilbert (Fin (k + 1) × Fin (n + 1))) :
    deningerFiniteBlockResiduePair k n (deningerRawPowerEmbedding n x) y =
      deningerFiniteResiduePair k x (deningerTopConormalResidue n y) := by
  simp only [deningerFiniteBlockResiduePair, deningerRawPowerEmbedding,
    deningerFiniteResiduePair, deningerTopConormalResidue, WithLp.ofLp_toLp]
  congr 1
  funext i
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- For a genuinely ramified block, raw and top-conormal sectors are disjoint. -/
theorem deningerTopConormalResidue_rawPowerEmbedding_eq_zero
    {ι : Type*} [Fintype ι] {n : ℕ} (hn : 0 < n)
    (x : DeningerRamifiedBlockHilbert ι) :
    deningerTopConormalResidue n (deningerRawPowerEmbedding n x) = 0 := by
  have hne : (Fin.last n : Fin (n + 1)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  ext i
  simp [deningerTopConormalResidue, deningerRawPowerEmbedding, hne]

/-- Coordinate form of the different `degree * x^(degree-1)`: it moves coordinate zero to the
top-conormal coordinate and multiplies it by the degree. -/
def deningerRamifiedDifferentAction {ι : Type*} [Fintype ι] (n : ℕ)
    (y : DeningerRamifiedBlockHilbert (ι × Fin (n + 1))) :
    DeningerRamifiedBlockHilbert (ι × Fin (n + 1)) :=
  deningerTopConormalEmbedding n
    (((n + 1 : ℕ) : ℂ) • deningerRawPowerResidue n y)

/-- **Top-conormal dagger law.** Final-residue extraction is the literal Hilbert adjoint of
final-coordinate embedding. -/
theorem inner_deningerTopConormalEmbedding_left
    {ι : Type*} [Fintype ι] (n : ℕ)
    (x : DeningerRamifiedBlockHilbert ι)
    (y : DeningerRamifiedBlockHilbert (ι × Fin (n + 1))) :
    inner ℂ (deningerTopConormalEmbedding n x) y =
      inner ℂ x (deningerTopConormalResidue n y) := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_prod_type]
  simp only [deningerTopConormalEmbedding, deningerTopConormalResidue,
    WithLp.ofLp_toLp, RCLike.inner_apply]
  congr 1
  funext i
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- Top-conormal residue is a left inverse of top-conormal embedding. -/
@[simp]
theorem deningerTopConormalResidue_embedding
    {ι : Type*} [Fintype ι] (n : ℕ) (x : DeningerRamifiedBlockHilbert ι) :
    deningerTopConormalResidue n (deningerTopConormalEmbedding n x) = x := by
  ext i
  simp [deningerTopConormalResidue, deningerTopConormalEmbedding]

/-- **Trace equals different times residue.** Top residue after the ramified different is rank
times coordinate-zero extraction. -/
theorem deningerTopConormalResidue_differentAction
    {ι : Type*} [Fintype ι] (n : ℕ)
    (y : DeningerRamifiedBlockHilbert (ι × Fin (n + 1))) :
    deningerTopConormalResidue n (deningerRamifiedDifferentAction n y) =
      ((n + 1 : ℕ) : ℂ) • deningerRawPowerResidue n y := by
  rw [deningerRamifiedDifferentAction, deningerTopConormalResidue_embedding]

/-- Final-coordinate embedding is an isometry for the standard finite Hilbert metrics. -/
theorem inner_deningerTopConormalEmbedding
    {ι : Type*} [Fintype ι] (n : ℕ)
    (x y : DeningerRamifiedBlockHilbert ι) :
    inner ℂ (deningerTopConormalEmbedding n x) (deningerTopConormalEmbedding n y) =
      inner ℂ x y := by
  rw [inner_deningerTopConormalEmbedding_left,
    deningerTopConormalResidue_embedding]

/-- Final-residue extraction commutes with scalar multiplication. -/
theorem deningerTopConormalResidue_smul
    {ι : Type*} [Fintype ι] (n : ℕ) (c : ℂ)
    (y : DeningerRamifiedBlockHilbert (ι × Fin (n + 1))) :
    deningerTopConormalResidue n (c • y) =
      c • deningerTopConormalResidue n y := by
  ext i
  simp [deningerTopConormalResidue]

/-- Rank-half-density normalized top-conormal power transfer, of degree `n+1`. -/
def deningerTopConormalTransfer {ι : Type*} [Fintype ι] (n : ℕ)
    (x : DeningerRamifiedBlockHilbert ι) :
    DeningerRamifiedBlockHilbert (ι × Fin (n + 1)) :=
  ((Real.sqrt (n + 1) : ℝ) : ℂ) • deningerTopConormalEmbedding n x

/-- Rank-half-density normalized residue cotransfer, of degree `n+1`. -/
def deningerTopConormalCotransfer {ι : Type*} [Fintype ι] (n : ℕ)
    (y : DeningerRamifiedBlockHilbert (ι × Fin (n + 1))) :
    DeningerRamifiedBlockHilbert ι :=
  ((Real.sqrt (n + 1) : ℝ) : ℂ) • deningerTopConormalResidue n y

/-- The normalized residue cotransfer is the Hilbert adjoint of normalized conormal transfer. -/
theorem deningerTopConormalTransfer_adjoint
    {ι : Type*} [Fintype ι] (n : ℕ)
    (x : DeningerRamifiedBlockHilbert ι)
    (y : DeningerRamifiedBlockHilbert (ι × Fin (n + 1))) :
    inner ℂ (deningerTopConormalTransfer n x) y =
      inner ℂ x (deningerTopConormalCotransfer n y) := by
  rw [deningerTopConormalTransfer, deningerTopConormalCotransfer,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    inner_deningerTopConormalEmbedding_left]

/-- **Ramified degree law.** Normalized residue after normalized conormal transfer is
`(n+1) • id`. -/
theorem deningerTopConormalCotransfer_transfer
    {ι : Type*} [Fintype ι] (n : ℕ)
    (x : DeningerRamifiedBlockHilbert ι) :
    deningerTopConormalCotransfer n (deningerTopConormalTransfer n x) =
      ((n + 1 : ℕ) : ℂ) • x := by
  rw [deningerTopConormalCotransfer, deningerTopConormalTransfer,
    deningerTopConormalResidue_smul, deningerTopConormalResidue_embedding, smul_smul]
  congr 1
  norm_cast
  exact Real.mul_self_sqrt (Nat.cast_nonneg _)

end

end RHTower
