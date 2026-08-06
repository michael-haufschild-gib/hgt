import GaloisForLFunctions.HTGeometry.MatrixCompound
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators

/-!
# Subset products of the spectrum of a pencil are submultiplicative

For positive-definite `P` and `Q` the numbers `α` diagonalising `S Q S`, where `S` is the inverse
square root of `P`, are the spectrum of the pencil `(P, Q)`.  Writing `Π_k` for the largest product
of `k` of them, the content of this file is

```text
Π_k (P, R) ≤ Π_k (P, Q) · Π_k (Q, R),
```

the multiplicative Ky Fan inequality.  The mechanism is entirely elementary: on the `k`-th compound
the largest subset product becomes a single largest eigenvalue, and the comparison of two
positive-definite forms `x ↦ x* Q x ≤ a · x* P x` is transitive with multiplicative constants.

Everything is stated through explicit unitary diagonalisations, so no eigenvalue-uniqueness theory
is needed.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

/-! ## The quadratic form of a matrix -/

/-- The Hermitian form of a matrix, evaluated on the diagonal. -/
def matQuadForm {κ : Type*} [Fintype κ] (M : Matrix κ κ ℂ) (x : κ → ℂ) : ℂ :=
  star x ⬝ᵥ (M *ᵥ x)

/-- The diagonal matrix of a real tuple. -/
def rdiag {κ : Type*} [DecidableEq κ] (d : κ → ℝ) : Matrix κ κ ℂ :=
  Matrix.diagonal fun i => (d i : ℂ)

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
theorem matQuadForm_eq_sum (M : Matrix κ κ ℂ) (x : κ → ℂ) :
    matQuadForm M x = ∑ i, star (x i) * (M *ᵥ x) i := rfl

theorem star_mul_self_complex (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [show star z * z = ((starRingEnd ℂ) z) * z from rfl, RCLike.conj_mul]
  norm_cast

omit [DecidableEq κ] in
theorem matQuadForm_congr (M A : Matrix κ κ ℂ) (x : κ → ℂ) :
    matQuadForm (Aᴴ * M * A) x = matQuadForm M (A *ᵥ x) := by
  rw [matQuadForm, matQuadForm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]

theorem matQuadForm_one_re (x : κ → ℂ) :
    (matQuadForm (1 : Matrix κ κ ℂ) x).re = ∑ i, ‖x i‖ ^ 2 := by
  rw [matQuadForm_eq_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.one_mulVec, star_mul_self_complex, Complex.ofReal_re]

theorem matQuadForm_rdiag_re (d : κ → ℝ) (x : κ → ℂ) :
    (matQuadForm (rdiag d) x).re = ∑ i, d i * ‖x i‖ ^ 2 := by
  rw [matQuadForm_eq_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rdiag, Matrix.mulVec_diagonal,
    show star (x i) * ((d i : ℂ) * x i) = ((d i : ℂ)) * (star (x i) * x i) from by ring,
    star_mul_self_complex, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem matQuadForm_rdiag_le {d : κ → ℝ} {c : ℝ} (hd : ∀ i, d i ≤ c)
    (x : κ → ℂ) :
    (matQuadForm (rdiag d) x).re ≤ c * (matQuadForm (1 : Matrix κ κ ℂ) x).re := by
  rw [matQuadForm_rdiag_re, matQuadForm_one_re, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hd i) (sq_nonneg _)

theorem matQuadForm_one_unitary {U : Matrix κ κ ℂ}
    (hU : U ∈ Matrix.unitaryGroup κ ℂ) (x : κ → ℂ) :
    matQuadForm (1 : Matrix κ κ ℂ) (U *ᵥ x) = matQuadForm (1 : Matrix κ κ ℂ) x := by
  rw [← matQuadForm_congr]
  congr 1
  rw [mul_one]
  rw [Matrix.mem_unitaryGroup_iff'] at hU
  rw [Matrix.star_eq_conjTranspose] at hU
  exact hU

/-! ## Comparison of compound forms -/

variable {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

theorem compound_quadForm_conj {k : ℕ} {S M : Matrix ι ι ℂ} (hS : S.IsHermitian)
    (u : Set.powersetCard ι k → ℂ) :
    matQuadForm (compound k M) (compound k S *ᵥ u) = matQuadForm (compound k (S * M * S)) u := by
  rw [← matQuadForm_congr, compound_isHermitian hS, compound_mul, compound_mul]

theorem compound_rdiag {k : ℕ} (d : ι → ℝ) :
    compound k (rdiag d)
      = rdiag (fun s : Set.powersetCard ι k => ∏ i ∈ (s : Finset ι), d i) := by
  rw [rdiag, compound_diagonal, rdiag]
  congr 1
  ext s
  rw [Complex.ofReal_prod]

/-- **The comparison of two observer forms on the compound.**  If `S` is Hermitian with
`S P S = 1` and `S Q S` is unitarily diagonal with entries `α`, then on the `k`-th compound the
form of `Q` is at most any bound `a` for the `k`-fold subset products of `α` times the form of
`P`. -/
theorem compound_quadForm_le {k : ℕ} {P Q S V : Matrix ι ι ℂ} {α : ι → ℝ} {a : ℝ}
    (hS : S.IsHermitian) (hSP : S * P * S = 1)
    (hSQ : S * Q * S = Vᴴ * rdiag α * V) (hV : V ∈ Matrix.unitaryGroup ι ℂ)
    (ha : ∀ s : Set.powersetCard ι k, ∏ i ∈ (s : Finset ι), α i ≤ a)
    (x : Set.powersetCard ι k → ℂ) :
    (matQuadForm (compound k Q) x).re ≤ a * (matQuadForm (compound k P) x).re := by
  obtain ⟨u, rfl⟩ := compound_mulVec_surjective (B := P * S) (by rw [← mul_assoc]; exact hSP) x
  have hP : (matQuadForm (compound k P) (compound k S *ᵥ u)).re
      = (matQuadForm (1 : Matrix (Set.powersetCard ι k) (Set.powersetCard ι k) ℂ) u).re := by
    rw [compound_quadForm_conj hS, hSP, compound_one]
  have hQ : (matQuadForm (compound k Q) (compound k S *ᵥ u)).re
      = (matQuadForm (rdiag (fun s : Set.powersetCard ι k => ∏ i ∈ (s : Finset ι), α i))
          (compound k V *ᵥ u)).re := by
    rw [compound_quadForm_conj hS, hSQ, compound_mul, compound_mul, compound_conjTranspose,
      matQuadForm_congr, compound_rdiag]
  rw [hP, hQ]
  calc (matQuadForm (rdiag (fun s : Set.powersetCard ι k => ∏ i ∈ (s : Finset ι), α i))
        (compound k V *ᵥ u)).re
      ≤ a * (matQuadForm (1 : Matrix (Set.powersetCard ι k) (Set.powersetCard ι k) ℂ)
        (compound k V *ᵥ u)).re := matQuadForm_rdiag_le ha _
    _ = a * (matQuadForm (1 : Matrix (Set.powersetCard ι k) (Set.powersetCard ι k) ℂ) u).re := by
        rw [matQuadForm_one_unitary (compound_unitary hV)]

/-- **The converse reading.**  A bound between the compound forms of `R` and `P` bounds every
`k`-fold subset product of the spectrum of the pencil `(P, R)`. -/
theorem prod_le_of_compound_quadForm_le {k : ℕ} {P R S Z : Matrix ι ι ℂ} {γ : ι → ℝ} {c : ℝ}
    (hS : S.IsHermitian) (hSP : S * P * S = 1)
    (hSR : S * R * S = Zᴴ * rdiag γ * Z) (hZ : Z ∈ Matrix.unitaryGroup ι ℂ)
    (h : ∀ x, (matQuadForm (compound k R) x).re ≤ c * (matQuadForm (compound k P) x).re)
    (s : Set.powersetCard ι k) :
    ∏ i ∈ (s : Finset ι), γ i ≤ c := by
  classical
  set e : Set.powersetCard ι k → ℂ := Pi.single s 1 with he
  set u : Set.powersetCard ι k → ℂ := (compound k Z)ᴴ *ᵥ e with hu
  have hZC : compound k Z ∈ Matrix.unitaryGroup (Set.powersetCard ι k) ℂ := compound_unitary hZ
  have hZe : compound k Z *ᵥ u = e := by
    rw [hu, Matrix.mulVec_mulVec]
    rw [Matrix.mem_unitaryGroup_iff] at hZC
    rw [Matrix.star_eq_conjTranspose] at hZC
    rw [hZC, Matrix.one_mulVec]
  have hnorm : (matQuadForm (1 : Matrix (Set.powersetCard ι k) (Set.powersetCard ι k) ℂ) u).re
      = 1 := by
    have hstar : (compound k Z)ᴴ ∈ Matrix.unitaryGroup (Set.powersetCard ι k) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hZC
      exact hZC
    rw [hu, matQuadForm_one_unitary hstar, matQuadForm_one_re, he]
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb]
      simp
    · intro hcon
      exact absurd (Finset.mem_univ s) hcon
  have hR : (matQuadForm (compound k R) (compound k S *ᵥ u)).re
      = ∏ i ∈ (s : Finset ι), γ i := by
    rw [compound_quadForm_conj hS, hSR, compound_mul, compound_mul, compound_conjTranspose,
      matQuadForm_congr, compound_rdiag, hZe, matQuadForm_rdiag_re, he]
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb]
      simp
    · intro hcon
      exact absurd (Finset.mem_univ s) hcon
  have hP : (matQuadForm (compound k P) (compound k S *ᵥ u)).re = 1 := by
    rw [compound_quadForm_conj hS, hSP, compound_one, hnorm]
  have := h (compound k S *ᵥ u)
  rw [hR, hP, mul_one] at this
  exact this

/-- **The multiplicative Ky Fan inequality for a pencil.**  Every `k`-fold subset product of the
spectrum of `(P, R)` is bounded by the product of bounds for the `k`-fold subset products of the
spectra of `(P, Q)` and `(Q, R)`. -/
theorem prod_le_mul_of_compound {k : ℕ} {P Q R S T V W Z : Matrix ι ι ℂ} {α β γ : ι → ℝ}
    {a b : ℝ}
    (hS : S.IsHermitian) (hSP : S * P * S = 1)
    (hSQ : S * Q * S = Vᴴ * rdiag α * V) (hV : V ∈ Matrix.unitaryGroup ι ℂ)
    (hSR : S * R * S = Zᴴ * rdiag γ * Z) (hZ : Z ∈ Matrix.unitaryGroup ι ℂ)
    (hT : T.IsHermitian) (hTQ : T * Q * T = 1)
    (hTR : T * R * T = Wᴴ * rdiag β * W) (hW : W ∈ Matrix.unitaryGroup ι ℂ)
    (ha : ∀ s : Set.powersetCard ι k, ∏ i ∈ (s : Finset ι), α i ≤ a)
    (hb : ∀ s : Set.powersetCard ι k, ∏ i ∈ (s : Finset ι), β i ≤ b) (hb0 : 0 ≤ b)
    (s : Set.powersetCard ι k) :
    ∏ i ∈ (s : Finset ι), γ i ≤ b * a := by
  refine prod_le_of_compound_quadForm_le hS hSP hSR hZ (fun x => ?_) s
  calc (matQuadForm (compound k R) x).re
      ≤ b * (matQuadForm (compound k Q) x).re := compound_quadForm_le hT hTQ hTR hW hb x
    _ ≤ b * (a * (matQuadForm (compound k P) x).re) :=
        mul_le_mul_of_nonneg_left (compound_quadForm_le hS hSP hSQ hV ha x) hb0
    _ = b * a * (matQuadForm (compound k P) x).re := by ring

end GaloisForLFunctions.HTGeometry
