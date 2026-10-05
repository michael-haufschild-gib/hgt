import GaloisForLFunctions.HTGeometry.HankelMomentTransform
import GaloisForLFunctions.HTGeometry.HankelApolarity

/-!
# The moved charts cover the rank-exactly-`r` locus

Let `A = K[x]/I_r` and `J ⊆ A` the image of `I_{r−1}`, the ideal of the maximal `r`-minors.  For a
prime `P` of `A` not containing `J`, some moved chart `δ_t` (`t = 0, …, r`) lies outside `P`.

Pass to the field `L = Frac(A/P)` and the point `x̄ ∈ L^N`: every maximal `(r+1)`-minor vanishes
there and some maximal `r`-minor does not.  The image of `δ_t` in `L` is the leading `r × r` Hankel
minor of the moved point `chartPoint x̄ t`, which `exists_chartPoint_det_ne_zero` makes nonzero for
some `t ≤ r`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable {K : Type} [Field K] {L : Type*} [Field L]

theorem momentEval_map (φ : MvPolynomial (Fin N) K →+* L) (f : Polynomial K) :
    φ (momentEval K N f) =
      momentFunctional (fun n => φ (X n)) (f.map (φ.comp MvPolynomial.C)) := by
  rw [momentEval_apply, map_sum, momentFunctional_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, map_mul, Polynomial.coeff_map, RingHom.comp_apply, mul_comm]

theorem momentChartEquiv_X_map (φ : MvPolynomial (Fin N) K →+* L) (t : K) (n : Fin N) :
    φ (momentChartEquiv K N t (X n)) = chartPoint (fun n => φ (X n)) (φ (C t)) n := by
  rw [momentChartEquiv_X, momentEval_map, chartPoint]
  congr 1
  simp

/-- The image of the moved chart `δ_t` under a ring map out of `K[x]` is the leading Hankel minor
of the moved point. -/
theorem map_momentChartEquiv_leadMinor (φ : MvPolynomial (Fin N) K →+* L) {r : ℕ} (hrN : 2 * r ≤ N)
    (t : K) :
    φ (momentChartEquiv K N t (hankelLeadMinor K N r)) =
      Matrix.det (fun i j : Fin r => chartPoint (fun n => φ (X n)) (φ (C t))
        ⟨i + j, by have := i.isLt; have := j.isLt; omega⟩) := by
  rw [hankelLeadMinor]
  rw [show ((momentChartEquiv K N t : MvPolynomial (Fin N) K ≃ₐ[K] _) :
      MvPolynomial (Fin N) K → MvPolynomial (Fin N) K) =
      ((momentChartEquiv K N t : MvPolynomial (Fin N) K ≃ₐ[K] _) : MvPolynomial (Fin N) K →+* _)
      from rfl, RingHom.map_det, RingHom.map_det]
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hankelCoord]
  rw [dif_pos (by have := i.isLt; have := j.isLt; omega)]
  exact momentChartEquiv_X_map φ t _

variable (K)

/-- **Some moved chart avoids every prime off the singular locus.**  For the rank-`(s+1)` secant
ring and a prime `P` not containing the image of the ideal of maximal `(s+1)`-minors, some moved
chart `δ_t`, `t ≤ s + 1`, lies outside `P`. -/
theorem exists_hankelChartElemAt_notMem [CharZero K] {N s : ℕ} (hsN : 2 * (s + 1) < N)
    (P : Ideal (HankelSecantRing K N (s + 1))) [P.IsPrime]
    (hJ : ¬ (RHTower.finiteHankelSecantIdeal K N s).map (Ideal.Quotient.mk _) ≤ P) :
    ∃ t ∈ Finset.range (s + 2), hankelChartElemAt K N (s + 1) (t : K) ∉ P := by
  classical
  set A := HankelSecantRing K N (s + 1)
  set φ : MvPolynomial (Fin N) K →+* FractionRing (A ⧸ P) :=
    (algebraMap A (FractionRing (A ⧸ P))).comp
      (Ideal.Quotient.mk (RHTower.finiteHankelSecantIdeal K N (s + 1))) with hφ
  have hφinj : ∀ a : A, algebraMap A (FractionRing (A ⧸ P)) a = 0 → a ∈ P := by
    intro a ha
    rw [IsScalarTower.algebraMap_apply A (A ⧸ P) (FractionRing (A ⧸ P))] at ha
    have h0 := IsFractionRing.injective (A ⧸ P) (FractionRing (A ⧸ P)) (ha.trans (map_zero _).symm)
    rw [Ideal.Quotient.algebraMap_eq] at h0
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  have hφzero : ∀ a ∈ P, algebraMap A (FractionRing (A ⧸ P)) a = 0 := by
    intro a ha
    rw [IsScalarTower.algebraMap_apply A (A ⧸ P) (FractionRing (A ⧸ P)),
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  haveI : CharZero (FractionRing (A ⧸ P)) :=
    charZero_of_injective_algebraMap (R := K) (RingHom.injective _)
  set x : Fin N → FractionRing (A ⧸ P) := fun n => φ (X n) with hx
  -- the `(s+2)`-minors vanish
  have hmin : ∀ (c : Fin (s + 1 + 1) → ℕ) (hbound : ∀ j, (s + 1 + 1) + c j ≤ N), StrictMono c →
      Matrix.det (fun i j : Fin (s + 1 + 1) => x (RHTower.finiteHankelIndex c hbound i j)) = 0 := by
    intro c hbound hc
    have hmem : RHTower.finiteHankelMaximalMinorOver K c hbound ∈
        RHTower.finiteHankelSecantIdeal K N (s + 1) := Ideal.subset_span ⟨c, hbound, hc, rfl⟩
    have h0 : φ (RHTower.finiteHankelMaximalMinorOver K c hbound) = 0 := by
      rw [hφ, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
    rw [RHTower.finiteHankelMaximalMinorOver, RingHom.map_det] at h0
    exact h0
  -- some `(s+1)`-minor does not
  obtain ⟨c, hbound, hc, hcP⟩ : ∃ (c : Fin (s + 1) → ℕ) (hbound : ∀ j, (s + 1) + c j ≤ N),
      StrictMono c ∧ Ideal.Quotient.mk (RHTower.finiteHankelSecantIdeal K N (s + 1))
        (RHTower.finiteHankelMaximalMinorOver K c hbound) ∉ P := by
    by_contra hall
    push Not at hall
    apply hJ
    rw [show RHTower.finiteHankelSecantIdeal K N s =
        Ideal.span (RHTower.finiteHankelMaximalMinorSetOver K N (s + 1)) from rfl,
      Ideal.map_span, Ideal.span_le]
    rintro _ ⟨p, ⟨c, hbound, hc, rfl⟩, rfl⟩
    exact hall c hbound hc
  have hdet : Matrix.det (fun i j : Fin (s + 1) => x (RHTower.finiteHankelIndex c hbound i j)) ≠
      0 := by
    intro h0
    apply hcP
    apply hφinj
    have := RingHom.map_det φ (fun i j : Fin (s + 1) => X (RHTower.finiteHankelIndex c hbound i j))
    exact this.trans h0
  obtain ⟨t, ht, htdet⟩ := exists_chartPoint_det_ne_zero x hsN hmin c hbound hdet
  refine ⟨t, ht, fun hmem => htdet ?_⟩
  have hC : φ (C (t : K)) = (t : FractionRing (A ⧸ P)) := by
    simp only [map_natCast]
  rw [← hC, ← map_momentChartEquiv_leadMinor φ (by omega)]
  rw [hankelChartElemAt_eq] at hmem
  rw [hφ, RingHom.comp_apply]
  exact hφzero _ hmem

end

end GaloisForLFunctions.HTGeometry
