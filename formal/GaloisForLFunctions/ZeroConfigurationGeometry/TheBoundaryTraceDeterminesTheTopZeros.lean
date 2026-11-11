import GaloisForLFunctions.ZeroConfigurationGeometry.ThePrimeErrorKeepsItsBoundaryTrace

/-!
# The spectrum of the prime-error boundary

Conjugation makes the boundary carrier real. Every attained top ordinate
has a nonzero Bohr coefficient, since its reciprocal amplitudes have one
strict real sign. A finite trigonometric boundary therefore has finitely
many top zeros, with multiplicities retained.
-/

open Complex Filter Topology Set
open _root_.RHTower

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

private theorem boundaryAmplitude_conj (β : ℝ) (q : XiZeroCopy) :
    primeErrorBoundaryAmplitude β (xiZeroCopyConjEquiv q) =
      (starRingEnd ℂ) (primeErrorBoundaryAmplitude β q) := by
  change (if ((starRingEnd ℂ) (q.1 : ℂ)).re = β then
    -((starRingEnd ℂ) (q.1 : ℂ))⁻¹ else 0) = _
  rw [Complex.conj_re]
  by_cases hq : (q.1 : ℂ).re = β <;> simp [primeErrorBoundaryAmplitude, hq]

private theorem expChar_conj (ω u : ℝ) :
    (starRingEnd ℂ) (expChar ω u) = expChar (-ω) u := by
  rw [expChar, expChar, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The complex boundary carrier is exactly the real trace embedded in `ℂ`. -/
theorem ofReal_primeErrorBoundaryTrace (β u : ℝ) :
    (primeErrorBoundaryTrace β u : ℂ) =
      expSeriesCarrier (primeErrorBoundaryAmplitude β) xiCopyOrdinate u := by
  let f := fun q : XiZeroCopy => primeErrorBoundaryAmplitude β q * expChar (xiCopyOrdinate q) u
  have hf (q : XiZeroCopy) : (starRingEnd ℂ) (f q) = f (xiZeroCopyConjEquiv q) := by
    dsimp [f]
    rw [map_mul, boundaryAmplitude_conj, expChar_conj]
    have hi : xiCopyOrdinate (xiZeroCopyConjEquiv q) = -xiCopyOrdinate q := by
      change ((starRingEnd ℂ) (q.1 : ℂ)).im = -(q.1 : ℂ).im
      exact Complex.conj_im _
    rw [hi]
  have hc : (starRingEnd ℂ) (∑' q, f q) = ∑' q, f q := by
    rw [Complex.conj_tsum]
    calc
      _ = ∑' q, f (xiZeroCopyConjEquiv q) := tsum_congr hf
      _ = _ := xiZeroCopyConjEquiv.tsum_eq f
  have him : (∑' q, f q).im = 0 := by
    have h := congrArg Complex.im hc
    rw [Complex.conj_im] at h
    linarith only [h]
  apply Complex.ext
  · exact primeErrorBoundaryTrace_eq_re_expSeries β u
  · simpa only [Complex.ofReal_im, expSeriesCarrier, f] using him.symm

private theorem finite_ordinate_fiber (ω : ℝ) :
    {q : XiZeroCopy | xiCopyOrdinate q = ω}.Finite := by
  refine (finite_xiOrdinateWindow |ω| 0).subset fun q hq => ?_
  rw [mem_xiOrdinateWindow_iff, sub_zero]
  change |xiCopyOrdinate q| ≤ |ω|
  rw [hq]

private theorem bohrCoefficient_expSeries_finite_fiber {ι : Type*}
    {a : ι → ℂ} (ha : Summable fun i => ‖a i‖) (ω : ι → ℝ) (ξ : ℝ)
    (F : Finset ι) (hF : ∀ i, i ∈ F ↔ ω i = ξ) :
    bohrCoefficient (expSeriesCarrier a ω) ξ = ∑ i ∈ F, a i := by
  classical
  have hc := continuous_expSeriesCarrier ha ω
  have hp := isBohrAlmostPeriodic_expSeriesCarrier ha ω
  apply eq_of_sub_eq_zero
  apply norm_le_zero_iff.mp
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨S, hS⟩ := exists_finset_tsum_compl_lt ha hε
  let T := S ∪ F
  have hST : S ⊆ T := Finset.subset_union_left
  have hFT : F ⊆ T := Finset.subset_union_right
  have hclose : ∀ u, ‖expSeriesCarrier a ω u - ∑ i ∈ T, a i * expChar (ω i) u‖ ≤ ε :=
    fun u => (norm_expSeriesCarrier_sub_partial_le ha ω T u).trans (hS T hST).le
  have hcoef : bohrCoefficient (fun u => ∑ i ∈ T, a i * expChar (ω i) u) ξ =
      ∑ i ∈ F, a i := by
    rw [bohrCoefficient_sum_expChar, ← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => (hF i).mpr h.2, fun h => ⟨hFT h, (hF i).mp h⟩⟩
  have hlip := norm_bohrCoefficient_sub_le hc hp
    (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_expChar _))
    (isBohrAlmostPeriodic_sum _ (fun i _ => continuous_const.mul (continuous_expChar _))
      (fun i _ => isBohrAlmostPeriodic_const_mul (a i) (isBohrAlmostPeriodic_expChar _)))
    hclose ξ
  change ‖bohrCoefficient (expSeriesCarrier a ω) ξ -
    bohrCoefficient (fun u => ∑ i ∈ T, a i * expChar (ω i) u) ξ‖ ≤ ε at hlip
  rw [hcoef] at hlip
  simpa only [zero_add] using hlip

/-- Every attained top ordinate has a nonzero Bohr coefficient. Copies at
the same ordinate cannot cancel their strictly negative real amplitudes. -/
theorem bohrCoefficient_boundary_ne_zero {β : ℝ} (hβ : 1 / 2 < β)
    (q : XiZeroCopy) (hq : (q.1 : ℂ).re = β) :
    bohrCoefficient (fun u => (primeErrorBoundaryTrace β u : ℂ)) (xiCopyOrdinate q) ≠ 0 := by
  classical
  let F := (finite_ordinate_fiber (xiCopyOrdinate q)).toFinset
  have hF : ∀ p : XiZeroCopy, p ∈ F ↔ xiCopyOrdinate p = xiCopyOrdinate q := by
    intro p
    exact Set.Finite.mem_toFinset _
  have hcarrier : (fun u => (primeErrorBoundaryTrace β u : ℂ)) =
      expSeriesCarrier (primeErrorBoundaryAmplitude β) xiCopyOrdinate :=
    funext (ofReal_primeErrorBoundaryTrace β)
  rw [hcarrier, bohrCoefficient_expSeries_finite_fiber
    (summable_primeErrorBoundaryAmplitude hβ) xiCopyOrdinate (xiCopyOrdinate q) F hF]
  have hn (p : XiZeroCopy) : 0 ≤ -(primeErrorBoundaryAmplitude β p).re := by
    by_cases hp : (p.1 : ℂ).re = β
    · simp only [primeErrorBoundaryAmplitude, hp, if_true, Complex.neg_re, neg_neg,
        Complex.inv_re]
      exact div_nonneg (by linarith only [hβ]) (Complex.normSq_nonneg _)
    · simp only [primeErrorBoundaryAmplitude, hp, if_false, Complex.zero_re, neg_zero, le_refl]
  have hpos : 0 < -(primeErrorBoundaryAmplitude β q).re := by
    simp only [primeErrorBoundaryAmplitude, hq, if_true, Complex.neg_re, neg_neg,
      Complex.inv_re]
    exact div_pos (by linarith only [hβ]) (Complex.normSq_pos.mpr (xiZeroCopy_ne_zero q))
  have hle := Finset.single_le_sum (fun p (_ : p ∈ F) => hn p) ((hF q).mpr rfl)
  intro hz
  have hzR := congrArg Complex.re hz
  simp only [Complex.re_sum, Complex.zero_re] at hzR
  rw [Finset.sum_neg_distrib, hzR, neg_zero] at hle
  exact (not_le_of_gt hpos) hle

/-- A finite trigonometric polynomial has finitely many frequencies. -/
def BoundaryTraceIsFinitePolynomial (β : ℝ) : Prop :=
  ∃ (S : Finset ℝ) (c : ℝ → ℂ), ∀ u : ℝ,
    (primeErrorBoundaryTrace β u : ℂ) = ∑ ω ∈ S, c ω * expChar ω u

/-- A finite-polynomial boundary forces a finite top layer, including all copies. -/
theorem finite_top_of_boundaryTraceIsFinitePolynomial {β : ℝ} (hβ : 1 / 2 < β)
    (h : BoundaryTraceIsFinitePolynomial β) :
    {q : XiZeroCopy | (q.1 : ℂ).re = β}.Finite := by
  classical
  obtain ⟨S, c, hS⟩ := h
  have hfreq (q : XiZeroCopy) (hq : (q.1 : ℂ).re = β) : xiCopyOrdinate q ∈ S := by
    by_contra hnot
    apply bohrCoefficient_boundary_ne_zero hβ q hq
    rw [show (fun u => (primeErrorBoundaryTrace β u : ℂ)) =
      (fun u => ∑ ω ∈ S, c ω * expChar ω u) from funext hS,
      bohrCoefficient_sum_expChar]
    apply Finset.sum_eq_zero
    intro ω hω
    have hn : ω ≠ xiCopyOrdinate q := fun he => hnot (he ▸ hω)
    exact if_neg hn
  refine (S.finite_toSet.biUnion fun ω _ => finite_ordinate_fiber ω).subset ?_
  intro q hq
  exact Set.mem_iUnion.mpr ⟨xiCopyOrdinate q, Set.mem_iUnion.mpr ⟨hfreq q hq, rfl⟩⟩

/-- A finite top layer gives the polynomial whose coefficients are its
negative reciprocal multiplicities. -/
theorem boundaryTraceIsFinitePolynomial_of_finite_top {β : ℝ}
    (h : {q : XiZeroCopy | (q.1 : ℂ).re = β}.Finite) :
    BoundaryTraceIsFinitePolynomial β := by
  classical
  let F := h.toFinset
  let S := F.image xiCopyOrdinate
  let A := fun ω : ℝ => -1 / ((β : ℂ) + I * (ω : ℂ))
  let c := fun ω : ℝ => ((F.filter fun q => xiCopyOrdinate q = ω).card : ℂ) * A ω
  have hF (q : XiZeroCopy) : q ∈ F ↔ (q.1 : ℂ).re = β := Set.Finite.mem_toFinset h
  refine ⟨S, c, fun u => ?_⟩
  rw [ofReal_primeErrorBoundaryTrace, expSeriesCarrier,
    tsum_eq_sum (s := F) fun q hq => by
      simp only [primeErrorBoundaryAmplitude, if_neg ((not_congr (hF q)).mp hq), zero_mul]]
  have hterm (q : XiZeroCopy) (hq : q ∈ F) :
      primeErrorBoundaryAmplitude β q * expChar (xiCopyOrdinate q) u =
        A (xiCopyOrdinate q) * expChar (xiCopyOrdinate q) u := by
    have hqβ := (hF q).mp hq
    have he : (q.1 : ℂ) = (β : ℂ) + I * (xiCopyOrdinate q : ℂ) := by
      apply Complex.ext <;> simp [xiCopyOrdinate, hqβ]
    rw [primeErrorBoundaryAmplitude, if_pos hqβ, he]
    simp only [A, neg_div, one_div]
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_comp (s := F) (g := xiCopyOrdinate) (fun ω => A ω * expChar ω u)]
  apply Finset.sum_congr rfl
  intro ω _
  rw [nsmul_eq_mul]
  dsimp [c]
  ring

/-- The boundary is a finite trigonometric polynomial exactly when its top
layer is finite. An infinite attained top retains an infinite spectrum. -/
theorem boundaryTraceIsFinitePolynomial_iff_finite_top {β : ℝ} (hβ : 1 / 2 < β) :
    BoundaryTraceIsFinitePolynomial β ↔ {q : XiZeroCopy | (q.1 : ℂ).re = β}.Finite :=
  ⟨finite_top_of_boundaryTraceIsFinitePolynomial hβ, boundaryTraceIsFinitePolynomial_of_finite_top⟩

end GaloisForLFunctions.ZeroConfigurationGeometry
