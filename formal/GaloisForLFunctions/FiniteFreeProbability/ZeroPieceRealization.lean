import GaloisForLFunctions.FiniteFreeProbability.ZeroFreeStrictStability
import GaloisForLFunctions.FiniteFreeProbability.MollifiedJensenCriterion
import GaloisForLFunctions.RHTower.Deninger.DeningerDivisorFlow

/-!
# The canonical finite free realization of the Jensen polynomials of `Ξ`

The route of §2.4 asks for the reversed Jensen polynomials `R_d(Ξ)` as finite free convolutions of
real-rooted pieces. There is a canonical unconditional realization by rank-one pieces, one for
each zero `a_q` of `Ξ` (with multiplicity):

`R_d(Ξ)/Ξ(0) = lim_n ⊞_{q∈G_n} R_d(1 − w/a_q)`,   `R_d(1 − w/a) = X^{d−1}(X − d/a)`,

coefficientwise, along an exhaustion `G_n` of the zeros by finite sets closed under the
functional-equation reflection `a ↦ −a`. The genus-one Hadamard product `Ξ = Ξ(0) Π E₁(z/a_q)`
gives the partial products `Π_{G} (1 − w/a_q)·e^{w Σ_G 1/a_q}`, and the reflection symmetry makes
`Σ_G 1/a_q = 0`, so no exponential (translation) factor survives.

Each piece `X^{d−1}(X − d/a_q)` is real-rooted exactly when `a_q` is real. Hence:

**Theorem.** The canonical pieces are all real-rooted iff RH. Under RH, `R_d(Ξ)` is a limit of
finite free convolutions of real-rooted rank-one polynomials, and the route is realized; the
pieces are zeros of `Ξ`, not Euler or Gamma data, whose own pieces are never stable (pole pieces,
`ζ(σ + iw)`, `Γ(1/4 + iw/2)`).
-/

open Polynomial Filter Topology Complex
open GaloisForLFunctions.HTGeometry RHTower

namespace FiniteFreeProbability

noncomputable section

/-! ## Symmetric exhaustions -/

/-- Closing a finite set of zero copies under the reflection `a ↦ −a`. -/
def reflectClosure (F : Finset XiZeroCopy) : Finset XiZeroCopy :=
  F ∪ F.map xiZeroCopyReflectEquiv.toEmbedding

theorem reflect_mem_reflectClosure {F : Finset XiZeroCopy} {q : XiZeroCopy}
    (hq : q ∈ reflectClosure F) : xiZeroCopyReflectEquiv q ∈ reflectClosure F := by
  classical
  simp only [reflectClosure, Finset.mem_union, Finset.mem_map_equiv] at hq ⊢
  rcases hq with hq | hq
  · right; rwa [xiZeroCopyReflectEquiv_symm_apply, xiZeroCopyReflectEquiv_apply_apply]
  · left; rwa [xiZeroCopyReflectEquiv_symm_apply] at hq

/-- On a reflection-closed set the exponential drift `Σ 1/a_q` vanishes. -/
theorem sum_inv_reflectClosure (F : Finset XiZeroCopy) :
    ∑ q ∈ reflectClosure F, 1 / xiSpectralPoint q = 0 := by
  have h : ∑ q ∈ reflectClosure F, 1 / xiSpectralPoint q =
      ∑ q ∈ reflectClosure F, 1 / xiSpectralPoint (xiZeroCopyReflectEquiv q) :=
    Finset.sum_nbij' xiZeroCopyReflectEquiv xiZeroCopyReflectEquiv
      (fun q hq => reflect_mem_reflectClosure hq) (fun q hq => reflect_mem_reflectClosure hq)
      (fun q _ => xiZeroCopyReflectEquiv_apply_apply q)
      (fun q _ => xiZeroCopyReflectEquiv_apply_apply q)
      (fun q _ => by rw [xiZeroCopyReflectEquiv_apply_apply])
  simp only [xiSpectralPoint_reflect, one_div, inv_neg, Finset.sum_neg_distrib] at h
  simp only [one_div]
  exact self_eq_neg.1 h

/-! ## The realization -/

theorem shiftedFactorPoly_zero (a : ℂ) : shiftedFactorPoly 0 a = 1 - C (1 / a) * X := by
  simp [shiftedFactorPoly]

theorem taylorPS_shiftedPartialProduct_reflectClosure (F : Finset XiZeroCopy) :
    taylorPS (shiftedPartialProduct 0 (reflectClosure F)) =
      ((∏ q ∈ reflectClosure F, (1 - C (1 / xiSpectralPoint q) * X) : ℂ[X]) : PowerSeries ℂ) := by
  rw [taylorPS_shiftedPartialProduct, sum_inv_reflectClosure]
  simp only [shiftedFactorPoly_zero]
  have h1 : expSeries (0 : ℂ) = 1 := by
    ext k; rw [expSeries, PowerSeries.coeff_mk, PowerSeries.coeff_one]; rcases k with _ | k <;> simp
  rw [h1, mul_one]

theorem xiShiftCoeff_half (k : ℕ) :
    xiShiftCoeff (1 / 2) k = PowerSeries.coeff k xiSeries := by
  rw [xiShiftCoeff, xiSeries, PowerSeries.coeff_mk, ofReal_realTaylorCoeff (fun z => XiC_conj z)]
  rw [show (fun w : ℂ => xi (((1 / 2 : ℝ) : ℂ) + I * w)) = XiC from funext fun w => by
    rw [XiC]; congr 1; push_cast; ring]
  ring

/-- **Canonical realization.** Along a reflection-closed exhaustion `G_n` of the zeros of `Ξ`, the
finite free products of the rank-one pieces `R_d(1 − w/a_q)` converge coefficientwise to
`R_d(Ξ)/Ξ(0)`, for every degree. -/
theorem exists_zeroPiece_realization :
    ∃ G : ℕ → Finset XiZeroCopy, Tendsto G atTop atTop ∧
      (∀ n q, q ∈ G n → xiZeroCopyReflectEquiv q ∈ G n) ∧
      ∀ d j, Tendsto (fun n => (jensenRev d
        ((∏ q ∈ G n, (1 - C (1 / xiSpectralPoint q) * X) : ℂ[X]) : PowerSeries ℂ)).coeff j)
        atTop (𝓝 ((jensenRev d xiSeries).coeff j / XiC 0)) := by
  obtain ⟨F, hF⟩ := Filter.exists_seq_tendsto (atTop : Filter (Finset XiZeroCopy))
  refine ⟨fun n => reflectClosure (F n),
    tendsto_atTop_mono (fun n => Finset.subset_union_left) hF,
    fun n q hq => reflect_mem_reflectClosure hq, fun d j => ?_⟩
  have hG : Tendsto (fun n => reflectClosure (F n)) atTop atTop :=
    tendsto_atTop_mono (fun n => Finset.subset_union_left) hF
  rcases le_or_gt j d with hj | hj
  · simp only [coeff_jensenRev d _ hj, ← taylorPS_shiftedPartialProduct_reflectClosure]
    have h := ((tendsto_coeff_taylorPS_shiftedPartialProduct 0 (d - j)).comp hG).mul_const
      ((d.descFactorial (d - j) : ℂ))
    rw [show (1 / 2 : ℝ) + 0 = 1 / 2 by ring, xiShiftCoeff_half] at h
    refine h.congr' (Eventually.of_forall fun n => rfl) |>.trans (le_of_eq ?_)
    congr 1; ring
  · simp only [coeff_jensenRev_of_lt d _ hj, zero_div]
    exact tendsto_const_nhds

/-- Each canonical piece `R_d(1 − w/a) = X^{d−1}(X − d/a)` is real-rooted iff `a` is real. -/
theorem isRoot_jensenRev_piece_iff (a : ℂ) (m : ℕ) (x : ℂ) :
    (jensenRev (m + 1) ((1 - C (1 / a) * X : ℂ[X]) : PowerSeries ℂ)).IsRoot x ↔
      x = 0 ∧ m ≠ 0 ∨ x = (m + 1) / a := by
  rw [IsRoot, eval_jensenRev_linear, mul_eq_zero, pow_eq_zero_iff', sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right; rw [h]; ring
  · rintro (h | h)
    · exact Or.inl h
    · right; rw [h]; ring

/-- **The route and RH.** All canonical pieces `R_d(1 − w/a_q)` (`d ≥ 1`) are real-rooted iff RH. -/
theorem riemannHypothesis_iff_zeroPieces_realRooted :
    RiemannHypothesis ↔ ∀ q : XiZeroCopy, ∀ m : ℕ, ∀ x,
      (jensenRev (m + 1) ((1 - C (1 / xiSpectralPoint q) * X : ℂ[X]) : PowerSeries ℂ)).IsRoot x →
        x.im = 0 := by
  constructor
  · intro hRH q m x hx
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
    rcases (isRoot_jensenRev_piece_iff _ m x).1 hx with h | h
    · rw [h.1]; simp
    · rw [h, ht]
      have : ((m : ℂ) + 1) / (t : ℂ) = (((m + 1 : ℝ) / t : ℝ) : ℂ) := by push_cast; ring
      rw [this, ofReal_im]
  · intro h
    refine riemannHypothesis_iff_XiC_zeros_real.2 fun z hz => ?_
    obtain ⟨q, rfl⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z).1 hz
    have ha := xiSpectralPoint_ne_zero q
    have hr := h q 0 (1 / xiSpectralPoint q)
      ((isRoot_jensenRev_piece_iff _ 0 _).2 (Or.inr (by push_cast; ring)))
    rw [one_div, inv_im, div_eq_zero_iff, neg_eq_zero] at hr
    rcases hr with hr | hr
    · exact hr
    · exact absurd (Complex.normSq_eq_zero.1 hr) ha

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.exists_zeroPiece_realization
#print axioms FiniteFreeProbability.riemannHypothesis_iff_zeroPieces_realRooted
