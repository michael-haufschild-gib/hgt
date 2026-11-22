import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedShift.AffineTaylor
import Mathlib.Analysis.Calculus.Taylor

/-!
# Uniform affine heat expansion

Dividing a child label by its parent places the expansion parameter in the
unit interval. Each extra Taylor coefficient gains a full power of the label.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedVariance

open BalancedShift Metric Set

/-- Coefficient of the kth derivative of a negative power. -/
def falling (s : ℂ) : ℕ → ℂ
  | 0 => 1
  | k+1 => falling s k * (-(s+(k:ℂ)))

theorem falling_entire (k : ℕ) : Differentiable ℂ (fun s => falling s k) := by
  induction k with
  | zero => exact differentiable_const _
  | succ k ih => exact ih.mul (differentiable_id.add_const _).neg

private def jet (b a : ℝ) (s : ℂ) (k : ℕ) (y : ℝ) :=
  (a:ℂ)^k * falling s k * weight (b+a*y) (s+(k:ℂ))

private theorem affine_derivative {b a y : ℝ} (hy : 0 < b+a*y) (s : ℂ) :
    HasDerivAt (fun x : ℝ => weight (b+a*x) s) ((a:ℂ)*(-s)*weight (b+a*y) (s+1)) y := by
  have hd : HasDerivAt (fun x => weight x s) (-s*weight (b+a*y) (s+1)) (b+a*y) := by
    rcases eq_or_ne s 0 with rfl | hs
    · simpa [weight] using (hasDerivAt_const (b+a*y) (1:ℂ))
    · simpa only [weight,neg_add_rev,sub_eq_add_neg,add_comm (-1:ℂ)] using
        hasDerivAt_ofReal_cpow_const hy.ne' (neg_ne_zero.mpr hs)
  simpa only [Function.comp_def,id_eq,mul_one,Complex.real_smul,mul_assoc] using
    hd.scomp y (((hasDerivAt_id y).const_mul a).const_add b)

private theorem iterated_jet {b a : ℝ} (hb : 0 < b) (he : 0 < b+a) (s : ℂ) (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun y => weight (b+a*y) s) (Icc 0 1)) (jet b a s k) (Icc 0 1) := by
  induction k with
  | zero => intro y _; simp [jet,falling]
  | succ k ih =>
    intro y hy
    rw [iteratedDerivWithin_succ,derivWithin_congr ih (ih hy)]
    have hd := (affine_derivative (affine_pos hb he hy) (s+(k:ℂ))).const_mul ((a:ℂ)^k * falling s k)
    have h := hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one y hy)
    change derivWithin (jet b a s k) (Icc 0 1) y = _
    rw [show derivWithin (jet b a s k) (Icc 0 1) y = _ from h]
    simp only [jet,falling,pow_succ,Nat.cast_succ,← add_assoc]
    ring

private theorem affine_smooth {b a : ℝ} (hb : 0 < b) (he : 0 < b+a) (s : ℂ) (n : ℕ) :
    ContDiffOn ℝ n (fun y => weight (b+a*y) s) (Icc 0 1) := by
  have hlog := (by fun_prop : ContDiffOn ℝ n (fun y : ℝ => b+a*y) (Icc 0 1)).log
    (fun y hy => (affine_pos hb he hy).ne')
  have hcast := Complex.ofRealCLM.contDiff.comp_contDiffOn hlog
  apply ((hcast.mul contDiffOn_const).cexp (f := fun y => (Real.log (b+a*y):ℂ)*(-s))).congr
  intro y hy
  rw [weight,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (affine_pos hb he hy).ne'),
    Complex.ofReal_log (affine_pos hb he hy).le]

/-- Taylor coefficient before inserting the inverse parent label. -/
def term (b a : ℝ) (s : ℂ) (k : ℕ) :=
  (k.factorial:ℂ)⁻¹ * (a:ℂ)^k * falling s k * weight b (s+(k:ℂ))

def poly (b a : ℝ) (s : ℂ) (m : ℕ) (u : ℝ) :=
  ∑ k ∈ Finset.range (m+1), term b a s k * (u:ℂ)^k

/-- Uniform Taylor remainder on temperature disks, valid at every finite order. -/
theorem normalized_bound {b a : ℝ} (hb : 0 < b) (he : 0 < b+a) (w : ℂ) (R : ℝ) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ closedBall w R, ∀ u ∈ Icc (0:ℝ) 1,
      ‖weight (b+a*u) s-poly b a s m u‖ ≤ K*u^(m+1) := by
  let S := closedBall w R ×ˢ Icc (0:ℝ) 1
  let k := m+1
  have hbase : ContinuousOn (fun p : ℂ × ℝ => ((b+a*p.2:ℝ):ℂ)) S := by fun_prop
  have hw : ContinuousOn (fun p : ℂ × ℝ => weight (b+a*p.2) (p.1+(k:ℂ))) S :=
    hbase.cpow (by fun_prop) (fun p hp => Complex.ofReal_mem_slitPlane.mpr (affine_pos hb he hp.2))
  have hf : Continuous (fun p : ℂ × ℝ => falling p.1 k) := (falling_entire k).continuous.comp continuous_fst
  have hjet : ContinuousOn (fun p : ℂ × ℝ => jet b a p.1 k p.2) S :=
    ((continuousOn_const.mul hf.continuousOn).mul hw)
  obtain ⟨M,hM⟩ := ((isCompact_closedBall w R).prod isCompact_Icc).exists_bound_of_continuousOn hjet
  refine ⟨max M 0/(m.factorial:ℝ),by positivity,?_⟩
  intro s hs u hu
  let f (y : ℝ) := weight (b+a*y) s
  have H := taylor_mean_remainder_bound (f := f) (n := m) zero_le_one
    (by simpa only [Nat.cast_succ] using affine_smooth hb he s (m+1)) hu
    (fun y hy => (by rw [iterated_jet hb he s (m+1) hy]; exact (hM (s,y) ⟨hs,hy⟩).trans (le_max_left M 0) :
       ‖iteratedDerivWithin (m+1) f (Icc 0 1) y‖ ≤ max M 0))
  have ht : taylorWithinEval f m (Icc 0 1) 0 u = poly b a s m u := by
    rw [taylor_within_apply,poly]
    apply Finset.sum_congr rfl
    intro i _
    rw [iterated_jet hb he s i (show (0:ℝ) ∈ Icc 0 1 from ⟨le_rfl,zero_le_one⟩)]
    simp only [sub_zero,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_pow,
      Complex.ofReal_natCast,jet,mul_zero,add_zero,term]
    ring
  rw [ht,sub_zero] at H
  exact H.trans_eq (by ring)

#print axioms normalized_bound

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedVariance
