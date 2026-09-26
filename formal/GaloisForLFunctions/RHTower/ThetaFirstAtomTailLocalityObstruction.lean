import GaloisForLFunctions.RHTower.ThetaTailAnalyticLocality
import GaloisForLFunctions.RHTower.ThetaFirstAtomTailCenterObstruction

/-!
# First-atom all-rank positivity fails on every real tail

The exact first atom has a strip envelope, so its negative incoming diagonal
is transported by analytic density to finite real Gram witnesses beyond every
threshold. The complete theta sum is not replaced by its first atom: no complete
source sign follows from this obstruction.
-/

open Set
noncomputable section
namespace RHTower.FirstAtomStripEnvelope

private theorem exp_tail_bound {c : ℝ} (hc : 0<c) (x : ℝ) :
    Real.exp (5*x)*Real.exp (-c*Real.exp (2*x)) ≤ (6/c^3)*Real.exp (-x) := by
  have hp := Real.pow_div_factorial_le_exp (c*Real.exp (2*x)) (by positivity) 3
  norm_num only [Nat.factorial, Nat.cast_mul, Nat.cast_ofNat] at hp
  have hmul := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-c*Real.exp (2*x))).le
  have hex : Real.exp (c*Real.exp (2*x))*Real.exp (-c*Real.exp (2*x)) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hex, mul_pow] at hmul
  have hb : Real.exp (2*x)^3*Real.exp (-c*Real.exp (2*x)) ≤ 6/c^3 := by
    apply (le_div_iff₀ (pow_pos hc 3)).2
    nlinarith
  have he : Real.exp (5*x) = Real.exp (2*x)^3*Real.exp (-x) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_right hb (Real.exp_pos (-x)).le]

/-- The exact first atom has exponential decay on every closed substrip. -/
theorem exists_norm_firstAtom_le {δ : ℝ} (hδ0 : 0≤δ) (hδ4 : 2*δ<Real.pi/2) :
    ∃ C : ℝ, 0≤C ∧ ∀ z : ℂ, |z.im|≤δ →
      ‖thetaCuspComplexTerm z 1‖ ≤ C*Real.exp (-|z.re|) := by
  let c := Real.pi*Real.cos (2*δ)
  have hc : 0<c := by
    have hcos := Real.cos_pos_of_mem_Ioo (show 2*δ ∈ Ioo (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [Real.pi_pos])
    exact mul_pos Real.pi_pos hcos
  let A := 2*Real.pi*(2*Real.pi+3)
  have hA : 0≤A := by dsimp [A]; positivity
  let B := 6/c^3
  have hB : 0≤B := by dsimp [B]; positivity
  refine ⟨A*(1+B), by positivity, ?_⟩
  intro z hz
  have h := norm_thetaCuspComplexTerm_le_pointwise hδ4.le hz 1
  norm_num only [Nat.cast_one, one_pow, mul_one] at h
  change ‖thetaCuspComplexTerm z 1‖ ≤
    Real.exp (z.re/2)*(2*Real.pi)*(2*Real.pi*Real.exp (4*z.re)+3*Real.exp (2*z.re))*
      Real.exp (-c*Real.exp (2*z.re)) at h
  by_cases hx : 0≤z.re
  · have hpoly : Real.exp (z.re/2)*(2*Real.pi)*
        (2*Real.pi*Real.exp (4*z.re)+3*Real.exp (2*z.re)) ≤ A*Real.exp (5*z.re) := by
      have h1 : Real.exp (z.re/2)*Real.exp (4*z.re) ≤ Real.exp (5*z.re) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      have h2 : Real.exp (z.re/2)*Real.exp (2*z.re) ≤ Real.exp (5*z.re) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      dsimp [A]
      nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left h1 (show 0≤4*Real.pi^2 by positivity),
        mul_le_mul_of_nonneg_left h2 (show 0≤6*Real.pi by positivity)]
    have ht := exp_tail_bound hc z.re
    have htot : ‖thetaCuspComplexTerm z 1‖ ≤ A*B*Real.exp (-z.re) := by
      calc
        _ ≤ (A*Real.exp (5*z.re))*Real.exp (-c*Real.exp (2*z.re)) :=
          h.trans (mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le)
        _ ≤ A*B*Real.exp (-z.re) := by
          dsimp [B]
          nlinarith [mul_le_mul_of_nonneg_left ht hA]
    rw [abs_of_nonneg hx]
    nlinarith [mul_nonneg hA (Real.exp_pos (-z.re)).le]
  · have hx' := le_of_not_ge hx
    have hg : Real.exp (-c*Real.exp (2*z.re)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (Real.exp_pos _).le)
    have hpoly : Real.exp (z.re/2)*(2*Real.pi)*
        (2*Real.pi*Real.exp (4*z.re)+3*Real.exp (2*z.re)) ≤ A*Real.exp z.re := by
      have h1 : Real.exp (z.re/2)*Real.exp (4*z.re) ≤ Real.exp z.re := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      have h2 : Real.exp (z.re/2)*Real.exp (2*z.re) ≤ Real.exp z.re := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      dsimp [A]
      nlinarith [mul_le_mul_of_nonneg_left h1 (show 0≤4*Real.pi^2 by positivity),
        mul_le_mul_of_nonneg_left h2 (show 0≤6*Real.pi by positivity)]
    have htot : ‖thetaCuspComplexTerm z 1‖ ≤ A*Real.exp z.re := by
      apply h.trans
      calc
        _ ≤ Real.exp (z.re/2)*(2*Real.pi)*
            (2*Real.pi*Real.exp (4*z.re)+3*Real.exp (2*z.re))*1 :=
          mul_le_mul_of_nonneg_left hg (by positivity)
        _ ≤ _ := by simpa using hpoly
    rw [abs_of_nonpos hx', neg_neg]
    nlinarith [mul_nonneg (mul_nonneg hA hB) (Real.exp_pos z.re).le]
end RHTower.FirstAtomStripEnvelope

noncomputable section
namespace RHTower.DominatedL2Sections

def firstAtomSource : StripSource where
  phi := fun z => thetaCuspComplexTerm z 1
  realValue := fun x => thetaCuspSourceTerm x 1
  ofReal := fun x => thetaCuspComplexTerm_ofReal x 1
  holomorphic := (differentiable_thetaCuspComplexTerm 1).differentiableOn
  decay := fun _ h0 h4 => FirstAtomStripEnvelope.exists_norm_firstAtom_le h0 h4

end RHTower.DominatedL2Sections

namespace RHTower.FirstAtomTailAudit
open RHTower.DominatedL2Sections

/-- Exact first-atom negativity persists arbitrarily far along the positive real axis. -/
theorem exists_finite_negative_tail (a : ℝ) :
    ∃ (n : ℕ) (x b : Fin n → ℝ), (∀ i, a < x i) ∧
      (∑ i, ∑ j, b i*b j*kernel (x i) (x j)) < 0 := by
  obtain ⟨x, hx⟩ := exists_tailDiagonal_neg
  have hk : firstAtomSource.realKernel x x < 0 := by
    change kernel x x < 0
    rw [kernel_diag]
    exact hx
  exact firstAtomSource.exists_finite_negative_tail_of_negative_diagonal hk a

/-- No real tail has positive semidefinite first-atom Gram matrices at all ranks. -/
theorem not_tail_posSemidef (a : ℝ) :
    ¬ ∀ (n : ℕ) (x : Fin n → ℝ), (∀ i, a < x i) →
      (Matrix.of (fun i j => kernel (x i) (x j))).PosSemidef := by
  intro h
  obtain ⟨n, x, b, hx, hb⟩ := exists_finite_negative_tail a
  have hp := (h n x hx).dotProduct_mulVec_nonneg b
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
    Matrix.of_apply, Finset.mul_sum] at hp
  have he : (∑ i, ∑ j, b i * (kernel (x i) (x j) * b j)) =
      ∑ i, ∑ j, b i*b j*kernel (x i) (x j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at hp
  exact (not_le_of_gt hb) hp

end RHTower.FirstAtomTailAudit
