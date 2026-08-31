import GaloisForLFunctions.HTGeometry.HankelChainFaces
import GaloisForLFunctions.HTGeometry.CoordinatePrimeRegular
import GaloisForLFunctions.HTGeometry.KrullDimInfPrimes
import GaloisForLFunctions.HTGeometry.CoordinateQuotient

/-!
# The Hankel degeneration is a Stanley–Reisner ring of dimension `2r`

The initial monomial ideal of the Hankel secant ideal is the Stanley–Reisner ideal of the chain
complex `Δ_r = {S : S contains no r+1 elements pairwise at distance ≥ 2}`: a monomial fails to be
chain-reduced exactly when its support is contained in no face, and faces are downward closed.

```text
IsChainFace, IsChainFace.subset               the faces and their downward closure
finiteHankelChainReduced_iff_isChainFace      reduced exponents are exactly the faces
finiteHankelChainIdeal_eq_inf
    ** the chain ideal is ⋂ over faces of the complementary coordinate ideal **
card_le_two_mul_of_isChainFace                every face has at most 2r vertices
ringKrullDim_quotient_span_X_compl            dim of one piece is the size of the face
ringKrullDim_quotient_finiteHankelChainIdeal
    ** the degeneration has Krull dimension exactly 2r **
```

The dimension is the card's `(11)` on the monomial side, and it completes the chain
`stanleyReisnerIdeal = ⋂ P_F` → `isPrime_span_X_image` → `ringKrullDim_quotient_inf_primes` →
`ringKrullDim_quotient_span_X_image` → the face bound of `HankelChainFaces.lean`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial RHTower

universe u
variable {K : Type u} [Field K]

/-- A finite set of indices is a face of the Hankel chain complex when it contains no `(r+1)`-chain.
-/
def IsChainFace (N r : ℕ) (S : Finset (Fin N)) : Prop :=
  ¬ ∃ J : Finset ℕ, J.card = r + 1 ∧
    (↑J : Set ℕ).Pairwise hankelChainGraph.Adj ∧ J ⊆ S.image Fin.val

theorem finiteHankelChainReduced_iff_isChainFace {N r : ℕ} (e : Fin N →₀ ℕ) :
    FiniteHankelChainReduced N r e ↔ IsChainFace N r e.support := by
  classical
  rw [FiniteHankelChainReduced, HankelChainReduced, IsChainFace,
    Finsupp.mapDomain_support_of_injective Fin.val_injective]

theorem IsChainFace.subset {N r : ℕ} {S T : Finset (Fin N)} (hT : IsChainFace N r T)
    (hST : S ⊆ T) : IsChainFace N r S := by
  rintro ⟨J, hcard, hpair, hsub⟩
  exact hT ⟨J, hcard, hpair, hsub.trans (Finset.image_subset_image hST)⟩

theorem isChainFace_empty (N r : ℕ) : IsChainFace N r (∅ : Finset (Fin N)) := by
  rintro ⟨J, hcard, -, hsub⟩
  simp only [Finset.image_empty, Finset.subset_empty] at hsub
  rw [hsub] at hcard
  simp at hcard

theorem mem_span_X_compl_iff {N : ℕ} {S : Finset (Fin N)} {p : MvPolynomial (Fin N) K} :
    p ∈ Ideal.span (X '' (↑(Sᶜ) : Set (Fin N)) : Set (MvPolynomial (Fin N) K)) ↔
      ∀ e ∈ p.support, ¬ e.support ⊆ S := by
  classical
  rw [MvPolynomial.mem_ideal_span_X_image]
  constructor
  · intro h e he hsub
    obtain ⟨i, hi, hne⟩ := h e he
    have hiS : i ∈ S := hsub (Finsupp.mem_support_iff.mpr hne)
    simp only [Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe] at hi
    exact hi hiS
  · intro h e he
    have := h e he
    rw [Finset.not_subset] at this
    obtain ⟨i, hi, hiS⟩ := this
    refine ⟨i, ?_, Finsupp.mem_support_iff.mp hi⟩
    simp only [Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe]
    exact hiS

open scoped Classical in
/-- The faces of the Hankel chain complex, as a finset. -/
noncomputable def chainFaceFinset (N r : ℕ) : Finset (Finset (Fin N)) :=
  Finset.univ.filter (fun S : Finset (Fin N) => IsChainFace N r S)

open scoped Classical in
theorem mem_chainFaceFinset {N r : ℕ} {S : Finset (Fin N)} :
    S ∈ chainFaceFinset N r ↔ IsChainFace N r S := by
  simp [chainFaceFinset]

/-- **The chain ideal is the Stanley–Reisner ideal of the chain complex.** -/
theorem finiteHankelChainIdeal_eq_inf (K : Type u) [Field K] (N r : ℕ) :
    finiteHankelChainIdeal K N r
      = (chainFaceFinset N r).inf
        (fun S => Ideal.span (X '' (↑(Sᶜ) : Set (Fin N)))) := by
  classical
  ext p
  rw [mem_finiteHankelChainIdeal_iff]
  simp only [Finset.inf_eq_iInf, Submodule.mem_iInf, mem_chainFaceFinset]
  constructor
  · intro h S hS
    rw [mem_span_X_compl_iff]
    intro e he hsub
    exact h e he ((finiteHankelChainReduced_iff_isChainFace e).mpr (hS.subset hsub))
  · intro h e he hred
    have hface : IsChainFace N r e.support :=
      (finiteHankelChainReduced_iff_isChainFace e).mp hred
    have h2 := h e.support hface
    rw [mem_span_X_compl_iff] at h2
    exact h2 e he (subset_refl _)

/-! ## The dimension of the degeneration -/

/-- The squarefree exponent of a finite set of variables. -/
noncomputable def indicatorExponent {N : ℕ} (S : Finset (Fin N)) : Fin N →₀ ℕ :=
  ∑ i ∈ S, Finsupp.single i 1

@[simp] theorem indicatorExponent_apply {N : ℕ} (S : Finset (Fin N)) (i : Fin N) :
    indicatorExponent S i = if i ∈ S then 1 else 0 := by
  classical
  rw [indicatorExponent, Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply, Finset.sum_ite_eq']

theorem support_indicatorExponent {N : ℕ} (S : Finset (Fin N)) :
    (indicatorExponent S).support = S := by
  classical
  ext i
  simp [Finsupp.mem_support_iff]

theorem card_le_two_mul_of_isChainFace {N r : ℕ} {S : Finset (Fin N)}
    (hS : IsChainFace N r S) : S.card ≤ 2 * r := by
  have hred : FiniteHankelChainReduced N r (indicatorExponent S) := by
    rw [finiteHankelChainReduced_iff_isChainFace, support_indicatorExponent]
    exact hS
  have := card_support_le_two_mul_of_finiteChainReduced hred
  rwa [support_indicatorExponent] at this

theorem ringKrullDim_quotient_span_X_compl (K : Type u) [Field K] {N : ℕ} (S : Finset (Fin N)) :
    ringKrullDim (MvPolynomial (Fin N) K ⧸
        Ideal.span (X '' (↑(Sᶜ) : Set (Fin N)) : Set (MvPolynomial (Fin N) K)))
      = (S.card : ℕ) := by
  classical
  rw [ringKrullDim_quotient_span_X_image K (↑(Sᶜ) : Set (Fin N))]
  congr 1
  rw [Finset.coe_compl, compl_compl]
  simp

/-- **The monomial degeneration of the Hankel secant ring has Krull dimension `2r`.**  It is the
Stanley–Reisner ring of the chain complex, whose largest face is `{0, …, 2r-1}`. -/
theorem ringKrullDim_quotient_finiteHankelChainIdeal (K : Type u) [Field K] (N r : ℕ)
    (h : 2 * r ≤ N) :
    ringKrullDim (MvPolynomial (Fin N) K ⧸ finiteHankelChainIdeal K N r) = ((2 * r : ℕ) : ℕ∞) := by
  classical
  set S₀ : Finset (Fin N) := Finset.univ.filter (fun i : Fin N => (i : ℕ) < 2 * r) with hS₀
  have hface₀ : IsChainFace N r S₀ := by
    have := finiteHankelChainReduced_initialSegment N r
    rw [finiteHankelChainReduced_iff_isChainFace, support_initialSegmentExponent] at this
    exact this
  have hcard₀ : S₀.card = 2 * r := by
    have := card_support_initialSegmentExponent N r h
    rwa [support_initialSegmentExponent] at this
  refine ringKrullDim_quotient_inf_primes (finiteHankelChainIdeal_eq_inf K N r) ?_
    (i₀ := S₀) (mem_chainFaceFinset.mpr hface₀) ?_
  · intro S hS
    rw [ringKrullDim_quotient_span_X_compl K S]
    exact_mod_cast Nat.cast_le.mpr (card_le_two_mul_of_isChainFace (mem_chainFaceFinset.mp hS))
  · rw [ringKrullDim_quotient_span_X_compl K S₀, hcard₀]
    norm_cast


end GaloisForLFunctions.HTGeometry
