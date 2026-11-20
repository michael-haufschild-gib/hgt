import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# One-sided higher differences on the whole integer line

A bounded sequence with a one-signed difference of order at least two
is constant. For order two its slopes are monotone, so a single nonzero
slope forces linear growth on one of the two rays. Higher orders descend
by applying the same argument to the bounded first difference.
-/

noncomputable section
open scoped ContDiff
namespace GaloisForLFunctions.ArithmeticPositiveDuality

private theorem constant_of_zero_step {f : ℤ → ℝ} (h : ∀ z, f (z+1)=f z) :
    ∀ z, f z=f 0 := by
  have hm := monotone_int_of_le_succ fun z => (h z).ge
  have hn := antitone_int_of_succ_le fun z => (h z).le
  intro z
  rcases le_total z 0 with hz | hz
  · exact le_antisymm (hm hz) (hn hz)
  · exact le_antisymm (hn hz) (hm hz)

private theorem bounded_convex_steps {f : ℤ → ℝ} {M : ℝ} (hb : ∀ z, |f z| ≤ M)
    (hm : Monotone (fwdDiff 1 f)) : ∀ z, f (z+1)=f z := by
  let d := fwdDiff 1 f
  -- Every secant slope lies between the slopes at its two ends.
  have hsec (n : ℕ) (z : ℤ) : (n:ℝ)*d z ≤ f (z+n)-f z ∧
      f (z+n)-f z ≤ (n:ℝ)*d (z+n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hs : d z ≤ d (z+n) := hm (by omega)
      have ht : d (z+n) ≤ d (z+(n+1:ℕ)) := hm (by omega)
      have he : f (z+(n+1:ℕ))=f (z+n)+d (z+n) := by
        simp [d,fwdDiff,add_assoc]
      rw [he,Nat.cast_succ]
      constructor
      · linarith only [ih.1,hs]
      · nlinarith only [ih.2,ht,mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg n : 0 ≤ (n:ℝ))]
  intro z
  have hlim (n : ℕ) : (n:ℝ)*d z ≤ 2*M ∧ (n:ℝ)*(-d z) ≤ 2*M := by
    have hl := (hsec n (z-n)).2
    rw [sub_add_cancel] at hl
    constructor
    · linarith only [(hsec n z).1,(abs_le.mp (hb (z+n))).2,(abs_le.mp (hb z)).1]
    · linarith only [hl,(abs_le.mp (hb z)).1,(abs_le.mp (hb (z-n))).2]
  have notpos (v : ℝ) (h : ∀ n : ℕ, (n:ℝ)*v ≤ 2*M) : v ≤ 0 := by
    by_contra! hp
    obtain ⟨n,hn⟩ := exists_nat_gt (2*M/v)
    exact ((div_lt_iff₀ hp).mp hn).not_ge (h n)
  have hd := le_antisymm (notpos _ fun n => (hlim n).1)
    (neg_nonpos.mp (notpos _ fun n => (hlim n).2))
  exact sub_eq_zero.mp hd

/-- On the full integer line a bounded sequence with any globally nonnegative
difference of order two or higher is constant. Both rays are essential. -/
theorem bounded_int_higher_difference_rigidity (n : ℕ) (f : ℤ → ℝ)
    (hb : ∃ M : ℝ, ∀ z, |f z| ≤ M)
    (h : ∀ z, 0 ≤ (fwdDiff 1)^[n+2] f z) : ∀ z, f z=f 0 := by
  induction n generalizing f with
  | zero =>
    apply constant_of_zero_step
    obtain ⟨M,hM⟩ := hb
    exact bounded_convex_steps hM (monotone_int_of_le_succ fun z => sub_nonneg.mp (h z))
  | succ n ih =>
    obtain ⟨M,hM⟩ := hb
    have hd (z : ℤ) : |fwdDiff 1 f z| ≤ 2*M :=
      (abs_sub _ _).trans (by linarith only [hM (z+1),hM z])
    have hc := ih (fwdDiff 1 f) ⟨2*M,hd⟩ h
    apply constant_of_zero_step
    exact bounded_convex_steps hM (fun i j _ => ((hc i).trans (hc j).symm).le)

/-- The order-n finite differences of a smooth function inherit the sign
of its order-n derivative at every nonnegative step. -/
theorem higher_difference_nonneg_of_derivative (n : ℕ) {h : ℝ} (hh : 0 ≤ h)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hs : ∀ x, 0 ≤ iteratedDeriv n f x) :
    ∀ x, 0 ≤ (fwdDiff h)^[n] f x := by
  induction n generalizing f with
  | zero => simpa only [iteratedDeriv_zero,Function.iterate_zero, id_eq] using hs
  | succ n ih =>
    have hshift : ContDiff ℝ ∞ (fun x => f (x+h)) := hf.comp (contDiff_id.add contDiff_const)
    have hn : (n : ℕ∞ω) < ∞ := WithTop.coe_lt_coe.mpr (ENat.coe_lt_top n)
    have hm := monotone_of_deriv_nonneg (hf.differentiable_iteratedDeriv n hn)
      (fun x => by simpa only [iteratedDeriv_succ] using hs x)
    apply ih (fwdDiff h f) (hshift.sub hf)
    intro x
    change 0 ≤ iteratedDeriv n ((fun y => f (y+h))-f) x
    rw [iteratedDeriv_sub (contDiff_infty.mp hshift n).contDiffAt (contDiff_infty.mp hf n).contDiffAt,
      iteratedDeriv_comp_add_const]
    exact sub_nonneg.mpr (hm (by linarith))

/-- Restriction to an affine lattice commutes with every iterated difference. -/
theorem sample_higher_difference (n : ℕ) (f : ℝ → ℝ) (a h : ℝ) (z : ℤ) :
    (fwdDiff 1)^[n] (fun k : ℤ => f (a+k*h)) z = (fwdDiff h)^[n] f (a+z*h) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply',fwdDiff,ih,Int.cast_add,Int.cast_one,
      show ∀ z : ℤ, a+((z:ℝ)+1)*h=a+z*h+h by intro z; ring]

/-- A one-dimensional sign descent in the spirit of Wei, Xu and Yang,
Lemma 2.3 (arXiv:2611.20600). Boundedness on both rays forces equality
throughout: a one-signed higher derivative forces a constant function. -/
theorem bounded_higher_derivative_rigidity (n : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M) (hs : ∀ x, 0 ≤ iteratedDeriv (n+2) f x) :
    ∀ x, f x=f 0 := by
  obtain ⟨M,hM⟩ := hb
  have hstep (a : ℝ) {h : ℝ} (hh : 0 ≤ h) : f (a+h)=f a := by
    have hr := bounded_int_higher_difference_rigidity n (fun k : ℤ => f (a+k*h))
      ⟨M,fun z => hM _⟩ (fun z => by
        rw [sample_higher_difference]
        exact higher_difference_nonneg_of_derivative _ hh f hf hs _)
    simpa only [Int.cast_one,one_mul,Int.cast_zero,zero_mul,add_zero] using hr 1
  intro x
  rcases le_total 0 x with hx | hx
  · simpa only [zero_add] using hstep 0 hx
  · simpa only [add_neg_cancel] using (hstep x (neg_nonneg.mpr hx)).symm

#print axioms bounded_int_higher_difference_rigidity
#print axioms bounded_higher_derivative_rigidity

end GaloisForLFunctions.ArithmeticPositiveDuality
