import GaloisForLFunctions.RHTower.Suzuki.SuzukiExteriorWienerAlphabet

/-!
# Unit-phase evaluation is an algebra map on the valuation Wiener algebra

The valuation lattice carries the unit characters `ν ↦ exp (i ξ ⟨ν⟩)`, where `⟨ν⟩` is the
logarithmic seam coordinate.  Evaluating a coefficient family against such a character turns
discrete convolution into multiplication whenever one factor is `ℓ¹` and the other is finitely
supported — which is exactly the situation of Suzuki's symbol, whose prime block is a finite sum of
atoms.  Absolute evaluation is therefore legal, and the Neumann inverse of the symbol evaluates to
the reciprocal of the symbol.
-/

open Set Filter Topology
open scoped ENNReal

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The unit character of the valuation lattice at frequency `ξ`. -/
def suzukiWienerChar (ξ : ℝ) (ν : SuzukiSeamValuation) : ℂ :=
  Complex.exp (Complex.I * (ξ * primeSeamCoordinate ν : ℝ))

theorem suzukiWienerEval_eq (ξ : ℝ) (t : SuzukiSeamValuation → ℂ) :
    suzukiWienerEval ξ t = ∑' ν, t ν * suzukiWienerChar ξ ν := rfl

theorem norm_suzukiWienerChar (ξ : ℝ) (ν : SuzukiSeamValuation) :
    ‖suzukiWienerChar ξ ν‖ = 1 := by
  rw [suzukiWienerChar, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem suzukiWienerChar_zero (ξ : ℝ) : suzukiWienerChar ξ 0 = 1 := by
  rw [suzukiWienerChar, map_zero]
  norm_num

theorem suzukiWienerChar_add (ξ : ℝ) (ν μ : SuzukiSeamValuation) :
    suzukiWienerChar ξ (ν + μ) = suzukiWienerChar ξ ν * suzukiWienerChar ξ μ := by
  rw [suzukiWienerChar, suzukiWienerChar, suzukiWienerChar, ← Complex.exp_add, map_add]
  congr 1
  push_cast
  ring

theorem suzukiWienerChar_sub_add (ξ : ℝ) (ν σ : SuzukiSeamValuation) :
    suzukiWienerChar ξ ν = suzukiWienerChar ξ σ * suzukiWienerChar ξ (ν - σ) := by
  rw [← suzukiWienerChar_add]
  congr 1
  abel

/-- Evaluation of the unit atom. -/
theorem suzukiWienerEval_discreteDelta (ξ : ℝ) :
    suzukiWienerEval ξ discreteDelta = 1 := by
  rw [suzukiWienerEval_eq]
  have hzero : ∀ ν ∉ ({0} : Finset SuzukiSeamValuation),
      discreteDelta ν * suzukiWienerChar ξ ν = 0 := by
    intro ν hν
    have : ν ≠ 0 := by simpa using hν
    rw [discreteDelta, if_neg this, zero_mul]
  rw [tsum_eq_sum hzero, Finset.sum_singleton, discreteDelta, if_pos rfl,
    suzukiWienerChar_zero, one_mul]

/-- Evaluation of a scalar multiple of the unit atom. -/
theorem suzukiWienerEval_const_mul_delta (ξ : ℝ) (c : ℂ) :
    suzukiWienerEval ξ (fun ν => c * discreteDelta ν) = c := by
  rw [suzukiWienerEval_eq]
  have hzero : ∀ ν ∉ ({0} : Finset SuzukiSeamValuation),
      c * discreteDelta ν * suzukiWienerChar ξ ν = 0 := by
    intro ν hν
    have : ν ≠ 0 := by simpa using hν
    rw [discreteDelta, if_neg this, mul_zero, zero_mul]
  rw [tsum_eq_sum hzero, Finset.sum_singleton, discreteDelta, if_pos rfl,
    suzukiWienerChar_zero, mul_one, mul_one]

/-- Evaluation is additive on absolutely summable families. -/
theorem suzukiWienerEval_add {x y : SuzukiSeamValuation → ℂ}
    (hx : Summable fun ν => ‖x ν‖) (hy : Summable fun ν => ‖y ν‖) (ξ : ℝ) :
    suzukiWienerEval ξ (fun ν => x ν + y ν)
      = suzukiWienerEval ξ x + suzukiWienerEval ξ y := by
  have hxs : Summable fun ν => x ν * suzukiWienerChar ξ ν := by
    apply Summable.of_norm
    simpa [norm_mul, norm_suzukiWienerChar] using hx
  have hys : Summable fun ν => y ν * suzukiWienerChar ξ ν := by
    apply Summable.of_norm
    simpa [norm_mul, norm_suzukiWienerChar] using hy
  rw [suzukiWienerEval_eq, suzukiWienerEval_eq, suzukiWienerEval_eq, ← hxs.tsum_add hys]
  congr 1
  funext ν
  ring

/-- A finitely supported family has a finite convolution sum. -/
theorem discreteConv_eq_sum {x y : SuzukiSeamValuation → ℂ} {T : Finset SuzukiSeamValuation}
    (hy : ∀ σ ∉ T, y σ = 0) (ν : SuzukiSeamValuation) :
    discreteConv x y ν = ∑ σ ∈ T, x (ν - σ) * y σ := by
  have hzero : ∀ μ ∉ T.image (fun σ => ν - σ), x μ * y (ν - μ) = 0 := by
    intro μ hμ
    have hnot : ν - μ ∉ T := by
      intro hmem
      exact hμ (Finset.mem_image.mpr ⟨ν - μ, hmem, by abel⟩)
    rw [hy _ hnot, mul_zero]
  rw [discreteConv, tsum_eq_sum hzero]
  rw [Finset.sum_image (fun p _ q _ h => by
    have : ν - (ν - p) = ν - (ν - q) := by rw [h]
    simpa using this)]
  refine Finset.sum_congr rfl ?_
  intro σ _
  congr 2
  abel

/-- **Evaluation turns discrete convolution into multiplication.**  One factor is `ℓ¹`, the other
finitely supported: this is Suzuki's situation, where the prime block is a finite atom sum. -/
theorem suzukiWienerEval_discreteConv {x y : SuzukiSeamValuation → ℂ}
    {T : Finset SuzukiSeamValuation} (hx : Summable fun ν => ‖x ν‖)
    (hy : ∀ σ ∉ T, y σ = 0) (ξ : ℝ) :
    suzukiWienerEval ξ (discreteConv x y)
      = suzukiWienerEval ξ x * suzukiWienerEval ξ y := by
  have hxs : ∀ σ : SuzukiSeamValuation,
      Summable fun ν => x (ν - σ) * suzukiWienerChar ξ (ν - σ) := by
    intro σ
    have hshift : Summable fun ν : SuzukiSeamValuation => ‖x (ν - σ)‖ := by
      have := (Equiv.subRight σ).summable_iff (f := fun ν => ‖x ν‖)
      exact this.mpr hx
    apply Summable.of_norm
    simpa [norm_mul, norm_suzukiWienerChar] using hshift
  have hterm : ∀ ν : SuzukiSeamValuation,
      discreteConv x y ν * suzukiWienerChar ξ ν
        = ∑ σ ∈ T, (y σ * suzukiWienerChar ξ σ) * (x (ν - σ) * suzukiWienerChar ξ (ν - σ)) := by
    intro ν
    rw [discreteConv_eq_sum hy, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro σ _
    rw [suzukiWienerChar_sub_add ξ ν σ]
    ring
  rw [suzukiWienerEval_eq]
  rw [tsum_congr hterm]
  rw [Summable.tsum_finsetSum (fun σ _ => ((hxs σ).mul_left (y σ * suzukiWienerChar ξ σ)))]
  have hinner : ∀ σ ∈ T,
      (∑' ν, (y σ * suzukiWienerChar ξ σ) * (x (ν - σ) * suzukiWienerChar ξ (ν - σ)))
        = (y σ * suzukiWienerChar ξ σ) * suzukiWienerEval ξ x := by
    intro σ _
    rw [tsum_mul_left, suzukiWienerEval_eq]
    congr 1
    exact (Equiv.subRight σ).tsum_eq (fun ν => x ν * suzukiWienerChar ξ ν)
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul]
  have hy' : suzukiWienerEval ξ y = ∑ σ ∈ T, y σ * suzukiWienerChar ξ σ := by
    rw [suzukiWienerEval_eq]
    apply tsum_eq_sum
    intro σ hσ
    rw [hy σ hσ, zero_mul]
  rw [hy', mul_comm]

end

end GaloisForLFunctions.RHTower
