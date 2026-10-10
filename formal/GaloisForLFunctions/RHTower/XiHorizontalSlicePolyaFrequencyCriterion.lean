import GaloisForLFunctions.RHTower.XiHorizontalSlicePolyaFrequencyCone
import GaloisForLFunctions.RHTower.XiHorizontalSliceTaylorPositivityConverse
import GaloisForLFunctions.RHTower.XiSliceFiniteOrderReduction

/-!
# The Riemann hypothesis as total positivity of every horizontal slice

The slice `g_t(x) = ξ(½ + x + it)·ξ(½ − x + it)` satisfies `conj (g_t (conj x)) = g_t x`
(`xiSliceProduct_conj`, from `ξ(s̄) = conj ξ(s)` and `ξ(1 − s) = ξ(s)`), so its Taylor coefficients are real (`xiSliceCoeff_im_eq_zero`).  For real
`x` it is `|ξ(½ + x + it)|²`.

**Criterion** (`riemannHypothesis_iff_forall_pfSeq_xiSliceCoeff`): RH holds iff for every height
`t` and every order `k` the coefficients `c_{2n}(t)` of `g_t` in `y = x²` form a `PF_k` sequence.
Under RH every zero lies on the axis of every visibility cone, so the cone law gives `PF_k` for all
`k`.  Conversely `PF_1` is coefficient positivity, which is the slice Taylor-positivity criterion.
The hierarchy is therefore exhaustive: order `1` already decides RH when imposed at every height,
and each finite order at a single height is a zero-free cone of half-angle `π/(2k+2)`.
-/

open Complex
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The `1 × 1` minors of a `PF_1` sequence: its terms are nonnegative. -/
theorem PFSeq.nonneg_of_one {a : ℕ → ℝ} (h : PFSeq 1 a) (n : ℕ) : 0 ≤ a n := by
  have := h 1 le_rfl (fun _ => 0) (fun _ => n) (Subsingleton.strictMono _)
    (Subsingleton.strictMono _)
  simpa [toeplitzMinor, Matrix.det_unique, zext_natCast] using this

/-- Iterated derivatives commute with the conjugation `f ↦ conj ∘ f ∘ conj`. -/
theorem iteratedDeriv_conj_comp_conj (f : ℂ → ℂ) : ∀ n : ℕ,
    iteratedDeriv n ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) =
      (starRingEnd ℂ) ∘ iteratedDeriv n f ∘ (starRingEnd ℂ)
  | 0 => by simp only [iteratedDeriv_zero]
  | n + 1 => by
    rw [iteratedDeriv_succ, iteratedDeriv_conj_comp_conj f n, deriv_conj_conj,
      ← iteratedDeriv_succ]

/-- **The slice Taylor coefficients are real.** -/
theorem xiSliceCoeff_im_eq_zero (t : ℝ) (n : ℕ) : (xiSliceCoeff t n).im = 0 := by
  have hsym : (starRingEnd ℂ) ∘ xiSliceProduct t ∘ (starRingEnd ℂ) = xiSliceProduct t := by
    funext x
    simp only [Function.comp_apply, xiSliceProduct_conj, Complex.conj_conj]
  have h := congrFun (iteratedDeriv_conj_comp_conj (xiSliceProduct t) n) 0
  rw [hsym] at h
  simp only [Function.comp_apply, map_zero] at h
  have him : (iteratedDeriv n (xiSliceProduct t) 0).im = 0 := by
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    linarith
  unfold xiSliceCoeff
  rw [Complex.mul_im, him, mul_zero, zero_add]
  have : (((n.factorial : ℂ))⁻¹).im = 0 := by
    rw [show ((n.factorial : ℂ))⁻¹ = (((n.factorial : ℝ))⁻¹ : ℝ) by push_cast; rfl]
    exact Complex.ofReal_im _
  rw [this, zero_mul]

/-- **The Riemann hypothesis is total positivity of every horizontal slice.**  RH holds iff for
every height `t` and order `k`, every Toeplitz minor of order `≤ k` with increasing rows and
columns of the slice coefficients `c_{2n}(t)` is nonnegative. -/
theorem riemannHypothesis_iff_forall_pfSeq_xiSliceCoeff :
    RiemannHypothesis ↔ ∀ t : ℝ, ∀ k : ℕ, PFSeq k (fun n => (xiSliceCoeff t (2 * n)).re) := by
  constructor
  · intro hRH t k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · intro m hm i j _ _
      obtain rfl : m = 0 := Nat.le_zero.mp hm
      simp [toeplitzMinor, Matrix.det_isEmpty]
    · refine xiSliceCoeff_pfSeq_of_cone hk fun q => ?_
      rw [xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q, sub_self]
      have hc := Real.cos_le_one (Real.pi / ((k : ℝ) + 1))
      have hs := sq_nonneg ((q.1 : ℂ).im - t)
      nlinarith
  · intro h
    refine riemannHypothesis_of_xiSliceCoeff_nonneg fun t n => ?_
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · exact Complex.nonneg_iff.mpr ⟨PFSeq.nonneg_of_one (h t 1) m,
        (xiSliceCoeff_im_eq_zero t (2 * m)).symm⟩
    · rw [xiSliceCoeff_odd_eq_zero]

end

end RHTower
