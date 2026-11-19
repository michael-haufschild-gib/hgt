import GaloisForLFunctions.FiniteFreeProbability.GammaThetaSzegoFactorization
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Complete sign law for two-shift theta Turán forms

Shi's extended Turán expressions pair opposite ends of a binomial row.
For raw theta moments the entire form is a moment of the difference of two
independent squared coordinates. Even orders are strictly positive at all
pairs of shifts. At odd order the sign is precisely the sign of the shift
difference, including equality on the diagonal.
-/

open Finset MeasureTheory Filter
open GaloisForLFunctions.SignAlternation RHTower RHTower.DeBruijn

namespace FiniteFreeProbability

noncomputable section

local notation "M" => thetaCuspRawEvenMoment

/-- A signed binomial row pairing two independently shifted raw theta moment sequences. -/
def thetaTuranForm (a b d : ℕ) : ℝ :=
  ∑ j ∈ range (d+1), ((d.choose j : ℝ)*(-1)^j) * (M (a+j)*M (b+(d-j)))

private def density (a : ℕ) (x : ℝ) := x^(2*a)*riemannKernelReal x
private def pairKernel (a b d : ℕ) (p : ℝ × ℝ) :=
  density a p.1 * density b p.2 * (p.2^2-p.1^2)^d

private theorem pair_expand (a b d : ℕ) (p : ℝ × ℝ) :
    pairKernel a b d p = ∑ j ∈ range (d+1), ((d.choose j : ℝ)*(-1)^j) *
      (density (a+j) p.1 * density (b+(d-j)) p.2) := by
  rw [pairKernel, show p.2^2-p.1^2 = (-1)*p.1^2+p.2^2 by ring, add_pow, mul_sum]
  apply sum_congr rfl
  intro j _
  simp only [density, mul_pow]
  ring

private theorem kernel_int (a b d : ℕ) : Integrable (pairKernel a b d) := by
  rw [funext (pair_expand a b d)]
  exact integrable_finsetSum _ fun j _ => ((integrable_pow_mul_riemannKernel (a+j)).mul_prod
    (integrable_pow_mul_riemannKernel (b+(d-j)))).const_mul _

/-- Product-kernel representation, with the original theta density in both coordinates. -/
theorem thetaTuranForm_integral (a b d : ℕ) :
    thetaTuranForm a b d = ∫ p : ℝ × ℝ, (p.1^(2*a)*riemannKernelReal p.1) *
      (p.2^(2*b)*riemannKernelReal p.2) * (p.2^2-p.1^2)^d := by
  change _ = ∫ p, pairKernel a b d p
  have hterm (j : ℕ) : Integrable (fun p : ℝ × ℝ =>
      ((d.choose j : ℝ)*(-1)^j) * (density (a+j) p.1 * density (b+(d-j)) p.2))
      (volume.prod volume) :=
    ((integrable_pow_mul_riemannKernel (a+j)).mul_prod
      (integrable_pow_mul_riemannKernel (b+(d-j)))).const_mul _
  rw [MeasureTheory.Measure.volume_eq_prod, funext (pair_expand a b d),
    integral_finsetSum (range (d+1)) (fun j _ => hterm j)]
  simp only [thetaTuranForm, integral_const_mul]
  apply sum_congr rfl
  intro j _
  rw [integral_prod_mul (density (a+j)) (density (b+(d-j)))]
  simp only [density, ← thetaCuspRawEvenMoment_eq_integral]

private theorem integral_form (a b d : ℕ) : (∫ p, pairKernel a b d p) = thetaTuranForm a b d :=
  (thetaTuranForm_integral a b d).symm

private theorem density_nn (a : ℕ) (x : ℝ) : 0 ≤ density a x :=
  mul_nonneg ((even_two_mul a).pow_nonneg _) (riemannKernel_superExp.nonneg _)

private theorem density_pos {x : ℝ} (hx : 0 < x) (a : ℕ) : 0 < density a x :=
  mul_pos (pow_pos hx _) (riemannKernelReal_pos _)

/-- Every even contrast has strictly positive mass, also for unequal shifts. -/
theorem thetaTuranForm_even_pos (a b k : ℕ) : 0 < thetaTuranForm a b (2*k) := by
  rw [← integral_form]
  have hd (j : ℕ) : Continuous (density j) := (continuous_pow _).mul riemannKernel_superExp.continuous
  apply integral_pos_of_integrable_nonneg_nonzero (x := ((1,2) : ℝ × ℝ))
    (((hd a).comp continuous_fst |>.mul ((hd b).comp continuous_snd)).mul
      ((continuous_snd.pow 2 |>.sub (continuous_fst.pow 2)).pow _)) (kernel_int _ _ _)
    (fun p => mul_nonneg (mul_nonneg (density_nn a p.1) (density_nn b p.2))
      ((even_two_mul k).pow_nonneg _))
  exact (mul_pos (mul_pos (density_pos one_pos a) (density_pos (by norm_num : (0 : ℝ)<2) b))
    (pow_pos (by norm_num : (0 : ℝ)<2^2-1^2) _)).ne'

/-- Exchanging the two shifts changes precisely the odd signs. -/
theorem thetaTuranForm_swap (a b d : ℕ) : thetaTuranForm b a d = (-1 : ℝ)^d*thetaTuranForm a b d := by
  rw [← integral_form, ← integral_form, ← integral_const_mul]
  change (∫ p, pairKernel b a d p ∂(volume.prod volume)) = _
  rw [← integral_prod_swap (pairKernel b a d)]
  apply integral_congr_ae
  filter_upwards with p
  simp only [pairKernel, Prod.swap]
  rw [show p.1^2-p.2^2 = (-1)*(p.2^2-p.1^2) by ring, mul_pow]
  ring

/-- Increasing the contrast order is a first difference between the two shifts. -/
theorem thetaTuranForm_succ (a b d : ℕ) :
    thetaTuranForm a b (d+1) = thetaTuranForm a (b+1) d - thetaTuranForm (a+1) b d := by
  simp only [← integral_form]
  rw [← integral_sub (kernel_int _ _ _) (kernel_int _ _ _)]
  apply integral_congr_ae
  filter_upwards with p
  simp only [pairKernel, density, pow_succ]
  ring

private theorem odd_swap (a b k : ℕ) : thetaTuranForm b a (2*k+1) = -thetaTuranForm a b (2*k+1) := by
  rw [thetaTuranForm_swap, pow_succ, (even_two_mul k).neg_one_pow, one_mul, neg_one_mul]

theorem thetaTuranForm_odd_diagonal (a k : ℕ) : thetaTuranForm a a (2*k+1) = 0 := by
  linarith only [odd_swap a a k]

private theorem odd_increasing (k : ℕ) : ∀ r a : ℕ, 0 < thetaTuranForm a (a+r+1) (2*k+1) := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro a
    have step (x y : ℕ) : thetaTuranForm (x+1) y (2*k+1) < thetaTuranForm x (y+1) (2*k+1) := by
      have h := thetaTuranForm_even_pos x y (k+1)
      rw [show 2*(k+1) = (2*k+1)+1 by omega, thetaTuranForm_succ] at h
      exact sub_pos.mp h
    cases r with
    | zero =>
      have h := step a a
      rw [odd_swap a (a+1) k] at h
      simp only [Nat.add_zero]
      linarith only [h]
    | succ r =>
      cases r with
      | zero =>
        have h := step a (a+1)
        rw [thetaTuranForm_odd_diagonal] at h
        exact h
      | succ r =>
        have h := ih r (by omega) (a+1)
        have h' := step a (a+(r+2))
        have hlo : 0 < thetaTuranForm (a+1) (a+(r+2)) (2*k+1) := by
          simpa only [show a+1+r+1 = a+(r+2) by omega] using h
        exact hlo.trans h'

/-- At odd order positivity is equivalent to the strict ordering of the shifts. -/
theorem thetaTuranForm_odd_pos_iff (a b k : ℕ) : 0 < thetaTuranForm a b (2*k+1) ↔ a < b := by
  have hpos {x y : ℕ} (h : x < y) : 0 < thetaTuranForm x y (2*k+1) := by
    obtain ⟨r,hr⟩ : ∃ r, y = x+r+1 := ⟨y-x-1, by omega⟩
    rw [hr]
    exact odd_increasing k r x
  refine ⟨fun h => ?_, hpos⟩
  rcases lt_trichotomy a b with hab | hab | hab
  · exact hab
  · subst b
    rw [thetaTuranForm_odd_diagonal] at h
    exact (lt_irrefl _ h).elim
  · have h' := hpos hab
    rw [odd_swap a b k] at h'
    linarith only [h,h']

#print axioms thetaTuranForm_integral
#print axioms thetaTuranForm_even_pos
#print axioms thetaTuranForm_odd_pos_iff

end

end FiniteFreeProbability
