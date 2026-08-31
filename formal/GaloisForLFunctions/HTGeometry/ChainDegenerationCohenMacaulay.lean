import GaloisForLFunctions.HTGeometry.ChainShapeInduction

/-!
# The monomial degeneration of the Hankel secant ring is Cohen–Macaulay

A regular sequence on `R ⧸ I` consisting of elements of `R` becomes, after passing to images, a
ring-regular sequence inside `R ⧸ I` itself.  The transfer is the double quotient identification
again, now as a ring isomorphism:

```text
mem_nonZeroDivisors_ringEquiv   nonzerodivisors transport along a ring isomorphism
isRegularOn_map_mk_iff          regularity modulo `I ⊔ J` is regularity of the image modulo `J`
map_mk_eq_top_iff               and the image ideal is everything exactly when `I ⊔ J` is
isRingRegularSeq_map_mk         ** the images form a ring-regular sequence **
isCohenMacaulayRing_of_isRegular_quotient
                                ** length equal to the dimension gives Cohen–Macaulayness **
```

Applied to the chain complex this closes the degeneration:

```text
hasRegSeq_chainFaceFinset                     a regular sequence of length min N (2r)
isCohenMacaulayRing_finiteHankelChainQuotient ** the degeneration is Cohen–Macaulay **
```

The Krull dimension of the degeneration is `2r`, so for `2r ≤ N` the sequence produced by the
two-shape induction is a system of parameters and the ring is Cohen–Macaulay.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Pointwise

universe u
variable {R : Type u} [CommRing R]

theorem mem_nonZeroDivisors_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (a : A) : a ∈ nonZeroDivisors A ↔ e a ∈ nonZeroDivisors B := by
  rw [mem_nonZeroDivisors_iff, mem_nonZeroDivisors_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · have hz : a * e.symm y = 0 := by
        apply e.injective
        rw [map_mul, e.apply_symm_apply, map_zero, hy]
      simpa using congrArg e (h1 _ hz)
    · have hz : e.symm y * a = 0 := by
        apply e.injective
        rw [map_mul, e.apply_symm_apply, map_zero, hy]
      simpa using congrArg e (h2 _ hz)
  · rintro ⟨h1, h2⟩
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · have hz : e a * e y = 0 := by rw [← map_mul, hy, map_zero]
      simpa using congrArg e.symm (h1 _ hz)
    · have hz : e y * e a = 0 := by rw [← map_mul, hy, map_zero]
      simpa using congrArg e.symm (h2 _ hz)

/-- Regularity modulo `I ⊔ J` upstairs is regularity of the image modulo the image of `J`. -/
theorem isRegularOn_map_mk_iff (I J : Ideal R) (x : R) :
    IsRegularOn (Ideal.map (Ideal.Quotient.mk I) J) (Ideal.Quotient.mk I x)
      ↔ IsRegularOn (I ⊔ J) x := by
  rw [IsRegularOn, IsRegularOn,
    mem_nonZeroDivisors_ringEquiv (DoubleQuot.quotQuotEquivQuotSup I J)]
  exact Iff.of_eq (congrArg (· ∈ nonZeroDivisors (R ⧸ (I ⊔ J)))
    (DoubleQuot.quotQuotEquivQuotSup_quotQuotMk I J x))

theorem ofList_map_mk (I : Ideal R) (l : List R) :
    Ideal.ofList (l.map (Ideal.Quotient.mk I))
      = Ideal.map (Ideal.Quotient.mk I) (Ideal.ofList l) := by
  rw [Ideal.ofList, Ideal.ofList, Ideal.map_span]
  congr 1
  ext y
  simp

theorem map_mk_eq_top_iff (I J : Ideal R) :
    Ideal.map (Ideal.Quotient.mk I) J = ⊤ ↔ I ⊔ J = ⊤ := by
  rw [← Extra.smul_top_eq_top_iff I J, smul_top_eq_map_quotient]
  constructor
  · intro h
    rw [h, Submodule.restrictScalars_top]
  · intro h
    refine Ideal.ext fun z => ⟨fun _ => trivial, fun _ => ?_⟩
    have hz : z ∈ Submodule.restrictScalars R (Ideal.map (Ideal.Quotient.mk I) J) := by
      rw [← h]; trivial
    exact hz

/-- The images of a regular sequence on `R ⧸ I` form a ring-regular sequence in `R ⧸ I`. -/
theorem isRingRegularSeq_map_mk (I : Ideal R) (rs : List R)
    (h : RingTheory.Sequence.IsRegular (R ⧸ I) rs) :
    IsRingRegularSeq (rs.map (Ideal.Quotient.mk I)) := by
  constructor
  · intro i hi
    rw [List.length_map] at hi
    have hreg := h.regular_mod_prev i hi
    rw [isSMulRegular_congr (quotSMulTopIdealEquiv I (Ideal.ofList (rs.take i)))] at hreg
    have hup := (isSMulRegular_quotient_iff _ _).mp hreg
    rw [← List.map_take, ofList_map_mk, List.getElem_map]
    exact (isRegularOn_map_mk_iff I (Ideal.ofList (rs.take i)) rs[i]).mpr hup
  · rw [ofList_map_mk]
    intro htop
    exact h.top_ne_smul ((Extra.smul_top_eq_top_iff I (Ideal.ofList rs)).mpr
      ((map_mk_eq_top_iff I (Ideal.ofList rs)).mp htop))

/-- **A regular sequence on `R ⧸ I` of the length of its dimension makes it Cohen–Macaulay.** -/
theorem isCohenMacaulayRing_of_isRegular_quotient {I : Ideal R} {rs : List R}
    (h : RingTheory.Sequence.IsRegular (R ⧸ I) rs)
    (hdim : ((rs.length : ℕ∞) : WithBot ℕ∞) = ringKrullDim (R ⧸ I)) :
    IsCohenMacaulayRing (R ⧸ I) :=
  ⟨rs.map (Ideal.Quotient.mk I), isRingRegularSeq_map_mk I rs h, by
    rw [List.length_map]; exact hdim⟩

section Chain

open MvPolynomial

variable {K : Type u} [Field K]

theorem intervalFinset_zero (N : ℕ) : intervalFinset N 0 (N - 0) = Finset.univ := by
  ext i
  rw [mem_intervalFinset]
  simp only [Nat.zero_le, Nat.sub_zero, Nat.zero_add, Finset.mem_univ, iff_true, true_and]
  exact i.isLt

theorem faceFamilyIdeal_chainFaceFinset (K : Type u) [Field K] (N r : ℕ) :
    faceFamilyIdeal K (chainFaceFinset N r) = finiteHankelChainIdeal K N r :=
  (finiteHankelChainIdeal_eq_inf K N r).symm

/-- **The chain complex carries a regular sequence of length `min N (2r)`.** -/
theorem hasRegSeq_chainFaceFinset (K : Type u) [Field K] (N r : ℕ) :
    HasRegSeq K (chainFaceFinset N r) (min N (2 * r)) := by
  classical
  have h := hasRegSeq_shapeI (r := r) K N 0 rfl (Nat.zero_le N) (∅ : Finset (Fin N))
    (fun a ha => absurd ha (Finset.notMem_empty a))
    (fun x hx => by simp [chainGreedy_empty] at hx)
    (by simp [chainGreedy_empty])
  rw [intervalFinset_zero, chainForcedOn_univ, chainForcedFamily_empty] at h
  simpa [chainGreedy_empty] using h

/-- **The monomial degeneration of the Hankel secant ring is Cohen–Macaulay.**  Its Stanley–Reisner
complex is the chain complex, whose regular sequence has length `2r`, and that is its Krull
dimension. -/
theorem isCohenMacaulayRing_finiteHankelChainQuotient (K : Type u) [Field K] (N r : ℕ)
    (h : 2 * r ≤ N) :
    IsCohenMacaulayRing (MvPolynomial (Fin N) K ⧸ finiteHankelChainIdeal K N r) := by
  obtain ⟨rs, hlen, -, hreg⟩ := hasRegSeq_chainFaceFinset (K := K) N r
  rw [faceFamilyIdeal_chainFaceFinset] at hreg
  refine isCohenMacaulayRing_of_isRegular_quotient hreg ?_
  rw [hlen, ringKrullDim_quotient_finiteHankelChainIdeal K N r h, min_eq_right h]

end Chain

end GaloisForLFunctions.HTGeometry
