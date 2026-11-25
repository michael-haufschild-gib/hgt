import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.TransitionCount.ExponentialWords
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.MonoidAlgebra.Support

/-! # Term counts and bandwidth of polynomial tests along an orbit -/

open Finset
open scoped Pointwise
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.TransitionCount.UniformEntries
noncomputable section

/-- Bound both the number of frequencies and their imaginary parts.
Coincident exponents are counted only after collecting their coefficients. -/
def wordBounds (m : ℕ) (B : ℝ) (w : Word) : Prop :=
  w.coeff.support.card ≤ m ∧ ∀ y∈w.coeff.support, |y.im| ≤ B

theorem wordBounds.single (y c : ℂ) : wordBounds 1 |y.im| (AddMonoidAlgebra.single y c) := by
  classical
  have hs : (AddMonoidAlgebra.single y c : Word).coeff.support⊆{y} := by
    rw [AddMonoidAlgebra.coeff_single]
    exact Finsupp.support_single_subset
  exact ⟨(Finset.card_le_card hs).trans_eq (Finset.card_singleton y),
    fun z hz => (Finset.mem_singleton.mp (hs hz)) ▸ le_rfl⟩

theorem wordBounds.constant (c : ℂ) : wordBounds 1 0 (algebraMap ℂ Word c) := by
  simpa only [AddMonoidAlgebra.coe_algebraMap,Function.comp_apply,Complex.zero_im,abs_zero] using
    wordBounds.single 0 c

theorem wordBounds.add {m n : ℕ} {B C : ℝ} {u v : Word}
    (hu : wordBounds m B u) (hv : wordBounds n C v) :
    wordBounds (m+n) (max B C) (u+v) := by
  classical
  have hs : (u+v).coeff.support ⊆ u.coeff.support∪v.coeff.support := by
    rw [AddMonoidAlgebra.coeff_add]
    exact Finsupp.support_add
  refine ⟨(card_le_card hs).trans ((card_union_le ..).trans (Nat.add_le_add hu.1 hv.1)),?_⟩
  intro y hy
  exact (mem_union.mp (hs hy)).elim (fun h => (hu.2 y h).trans (le_max_left ..))
    (fun h => (hv.2 y h).trans (le_max_right ..))

theorem wordBounds.mul {m n : ℕ} {B C : ℝ} {u v : Word}
    (hu : wordBounds m B u) (hv : wordBounds n C v) :
    wordBounds (m*n) (B+C) (u*v) := by
  classical
  have hs := AddMonoidAlgebra.support_coeff_mul_subset u v
  refine ⟨(card_le_card hs).trans ((Finset.card_add_le ..).trans (Nat.mul_le_mul hu.1 hv.1)),?_⟩
  intro y hy
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp (hs hy)
  exact (abs_add_le a.im b.im).trans (add_le_add (hu.2 a ha) (hv.2 b hb))

theorem wordBounds.mono {m n : ℕ} {B C : ℝ} {u : Word} (hu : wordBounds m B u)
    (hm : m≤n) (hB : B≤C) : wordBounds n C u :=
  ⟨hu.1.trans hm,fun y hy => (hu.2 y hy).trans hB⟩

/-- The zero count charges interval length times bandwidth. The intercept
and slope depend only on the number of retained terms. -/
theorem bounded_word_zeros {m : ℕ} {B : ℝ} {w : Word} (hw : wordBounds m B w)
    (hB : 0≤B) (hr : ∀ t, (evaluate t w).im=0) (hne : ∃ t, evaluate t w≠0) :
    ∀ a b : ℝ, a<b → ∀ Z : Finset ℝ, (∀ t∈Z, t∈Set.Icc a b) →
      (∀ t∈Z, evaluate t w=0) →
      (Z.card:ℝ) ≤ (3:ℝ)^m*(m+2)*(1+(b-a)*B) := by
  classical
  intro a b hab Z hZ hz
  let S := w.coeff.support
  have he (t : ℝ) : evaluate t w=∑ y∈S, w.coeff y*Complex.exp (y*t) := by
    rw [evaluate,AddMonoidAlgebra.lift_apply']
    rfl
  have hs : S.Nonempty := by
    obtain ⟨t,ht⟩ := hne
    by_contra h
    rw [he,Finset.not_nonempty_iff_eq_empty.mp h,Finset.sum_empty] at ht
    exact ht rfl
  have hh := card_zeros_le_expPoly (S:=S) (C:=w.coeff) hs (fun _ h => Finsupp.mem_support_iff.mp h)
    hw.2 (fun t => by rw [←he]; exact hr t) hab Z hZ (fun t ht => by rw [←he,hz t ht,Complex.zero_re])
  have ht : 0≤(b-a)*B := mul_nonneg (sub_nonneg.mpr hab.le) hB
  have hπ : 2*((b-a)*B/Real.pi) ≤ (b-a)*B := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ Real.pi_pos).mpr
    exact (mul_comm ..).trans_le (mul_le_mul_of_nonneg_left
      ((by norm_num : (2:ℝ)≤3).trans Real.pi_gt_three.le) ht)
  have hc : (S.card:ℝ)≤m := by exact_mod_cast hw.1
  have hpow : (3:ℝ)^S.card ≤ 3^m := pow_le_pow_right₀ (by norm_num) hw.1
  have hrem : 0≤2*((b-a)*B/Real.pi)+1 := by positivity
  apply hh.trans
  apply (sub_le_self _ hrem).trans
  have hbr : (S.card:ℝ)+2*((b-a)*B/Real.pi)+1≤((m:ℝ)+2)*(1+(b-a)*B) := by
    nlinarith only [hc,hπ,ht,mul_nonneg (Nat.cast_nonneg m : 0≤(m:ℝ)) ht]
  exact (mul_le_mul hpow hbr (by positivity) (by positivity)).trans_eq (mul_assoc ..).symm

#print axioms bounded_word_zeros
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.TransitionCount.UniformEntries
