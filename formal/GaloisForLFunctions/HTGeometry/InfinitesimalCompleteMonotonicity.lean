import GaloisForLFunctions.HTGeometry.BernsteinWidder
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Infinitesimal extraction of a bounded positive Laplace generator from all its exponential times. -/

noncomputable section
open Set Filter Topology
open scoped ComplexOrder
namespace GaloisForLFunctions.HTGeometry

lemma right_derivative_nonneg {f : ℝ → ℝ} {a : ℝ}
    (hd : HasDerivAt f a 0) (h0 : f 0 = 0) (hp : ∀ t, 0 < t → 0 ≤ f t) : 0 ≤ a := by
  apply ge_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [zero_add, h0, sub_zero, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr ht.le) (hp t ht)

lemma im_eq_zero_of_exp_nonneg {z : ℂ}
    (h : ∀ t : ℝ, 0 < t → 0 ≤ Complex.exp ((t : ℂ) * z)) : z.im = 0 := by
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * z)) z 0 := by
    simpa [← Complex.exp_eq_exp_ℂ, Complex.real_smul] using
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) z 0)
  have hi : HasDerivAt (fun t : ℝ => (Complex.exp ((t : ℂ) * z)).im) z.im 0 :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hd
  have hp : ∀ t : ℝ, 0 < t → (Complex.exp ((t : ℂ) * z)).im = 0 := by
    intro t ht
    exact (Complex.le_def.mp (h t ht)).2.symm
  apply le_antisymm
  · have hn := right_derivative_nonneg hi.neg (by simp) (fun t ht => by simpa only [Pi.neg_apply, hp t ht, neg_zero] using (le_refl (0 : ℝ)))
    linarith
  · exact right_derivative_nonneg hi (by simp) (fun t ht => (hp t ht).ge)

lemma hasDerivAt_fwdDiff_exp_zero (a : ℝ → ℝ) (δ x : ℝ) (n : ℕ) :
    HasDerivAt (fun t : ℝ => (fwdDiff δ)^[n] (fun y => Real.exp (t * a y)) x)
      ((fwdDiff δ)^[n] a x) 0 := by
  induction n generalizing x with
  | zero => simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (a x)).exp
  | succ n ih =>
      simpa only [Function.iterate_succ_apply', fwdDiff, Pi.sub_apply] using! (ih (x + δ)).sub (ih x)

lemma fwdDiff_iter_const_pos (δ c : ℝ) {n : ℕ} (hn : 0 < n) :
    (fwdDiff δ)^[n] (fun _ : ℝ => c) = fun _ => 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  clear hn
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, fwdDiff_const]

/-- Positivity at every time exposes all positive-order alternating differences of its exponent. -/
theorem completelyMonotoneDiff_infinitesimal {a : ℝ → ℝ} {M : ℝ}
    (hbound : ∀ x, 0 < x → -M ≤ a x)
    (h : ∀ t : ℝ, 0 < t → CompletelyMonotoneDiff (fun x => Real.exp (t * a x))) :
    CompletelyMonotoneDiff (fun x => a x + M) := by
  intro n δ hδ x hx
  cases n with
  | zero => simpa using (show 0 ≤ a x + M by linarith [hbound x hx])
  | succ n =>
      have hd := (hasDerivAt_fwdDiff_exp_zero a δ x (n+1)).const_mul ((-1 : ℝ)^(n+1))
      have h0 : (-1 : ℝ)^(n+1) *
          (fwdDiff δ)^[n+1] (fun y => Real.exp (0 * a y)) x = 0 := by
        simp only [zero_mul, Real.exp_zero, fwdDiff_iter_const_pos δ 1 (Nat.succ_pos n), mul_zero]
      have hn := right_derivative_nonneg hd h0 (fun t ht => h t ht (n+1) δ hδ x hx)
      have he : (fwdDiff δ)^[n+1] (fun y => a y + M) = (fwdDiff δ)^[n+1] a := by
        change (fwdDiff δ)^[n+1] (a + fun _ => M) = _
        rw [fwdDiff_iter_add, fwdDiff_iter_const_pos δ M (Nat.succ_pos n)]
        funext y
        exact add_zero _
      rwa [he]

end GaloisForLFunctions.HTGeometry
