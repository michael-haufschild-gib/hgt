import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Boundary rigidity of actual bounded holomorphic interpolation

An interpolable disk datum with one unimodular coordinate is constant.
Consequently a datum whose coordinatewise exponential lies in the
bounded interpolation set for every real time is a real constant vector.
This realizes the Hermitian-element mechanism of arXiv:2610.28972 using
actual holomorphic interpolants and the maximum modulus principle.
-/

open Complex Metric Set
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.DiskInterpolation
noncomputable section

abbrev DiskPoint := {z : ℂ // ‖z‖ < 1}

/-- Values realized by genuine holomorphic functions bounded by one on the disk. -/
def boundedData {n : ℕ} (z : Fin (n + 1) → DiskPoint) : Set (Fin (n + 1) → ℂ) :=
  {w | ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (ball 0 1) ∧
    (∀ x ∈ ball (0 : ℂ) 1, ‖f x‖ ≤ 1) ∧ ∀ i, f (z i) = w i}

private theorem node_mem {n : ℕ} (z : Fin (n + 1) → DiskPoint) (i : Fin (n + 1)) :
    (z i : ℂ) ∈ ball (0 : ℂ) 1 := by
  simpa only [mem_ball, dist_zero_right] using (z i).property

theorem norm_le_one {n : ℕ} (z : Fin (n + 1) → DiskPoint)
    {w : Fin (n + 1) → ℂ} (hw : w ∈ boundedData z) (i : Fin (n + 1)) : ‖w i‖ ≤ 1 := by
  obtain ⟨f, _, hb, he⟩ := hw
  rw [← he i]
  exact hb (z i) (node_mem z i)

/-- A single unimodular interior value forces every interpolation coordinate to agree. -/
theorem boundary_rigid {n : ℕ} (z : Fin (n + 1) → DiskPoint)
    {w : Fin (n + 1) → ℂ} (hw : w ∈ boundedData z)
    (k : Fin (n + 1)) (hk : ‖w k‖ = 1) : ∀ i, w i = w k := by
  obtain ⟨f, hf, hb, he⟩ := hw
  have hm : IsMaxOn (norm ∘ f) (ball (0 : ℂ) 1) (z k) := by
    intro x hx
    change ‖f x‖ ≤ ‖f (z k)‖
    rw [he k, hk]
    exact hb x hx
  have hc := Complex.eq_const_of_exists_max hf (node_mem z k) hm
  intro i
  simpa only [Function.const, he i, he k] using hc (node_mem z i)

/-- Unimodular interpolation data are exactly constant unimodular vectors. -/
theorem unimodular_data_iff {n : ℕ} (z : Fin (n + 1) → DiskPoint)
    (w : Fin (n + 1) → ℂ) :
    (w ∈ boundedData z ∧ ∀ i, ‖w i‖ = 1) ↔
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ i, w i = c := by
  constructor
  · rintro ⟨hw, hn⟩
    exact ⟨w 0, hn 0, boundary_rigid z hw 0 (hn 0)⟩
  · rintro ⟨c, hc, he⟩
    refine ⟨⟨fun _ => c, differentiableOn_const, fun _ _ => hc.le,
      fun i => (he i).symm⟩, ?_⟩
    intro i
    rw [he i, hc]

private theorem exponential_norm (t : ℝ) (w : ℂ) :
    ‖Complex.exp ((t : ℂ) * Complex.I * w)‖ = Real.exp (-t * w.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, mul_one, zero_add]
  ring

private theorem exponential_hasDerivAt_zero (w : ℂ) :
    HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I * w)) (Complex.I * w) 0 := by
  have h : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
  simpa only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul] using
    ((h.mul_const Complex.I).mul_const w).cexp

/-- The only data generating bounded holomorphic interpolation at every imaginary time
are real constant vectors. -/
theorem exponential_data_iff_real_constant {n : ℕ}
    (z : Fin (n + 1) → DiskPoint) (w : Fin (n + 1) → ℂ) :
    (∀ t : ℝ, (fun i => Complex.exp ((t : ℂ) * Complex.I * w i)) ∈ boundedData z) ↔
      ∃ r : ℝ, ∀ i, w i = (r : ℂ) := by
  constructor
  · intro h
    have him (i : Fin (n + 1)) : (w i).im = 0 := by
      have hp := norm_le_one z (h 1) i
      have hn := norm_le_one z (h (-1)) i
      rw [exponential_norm, Real.exp_le_one_iff] at hp hn
      norm_num only [neg_one_mul, neg_neg, one_mul] at hp hn
      linarith only [hp, hn]
    have he (i : Fin (n + 1)) : w i = w 0 := by
      have hfun : (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I * w i)) =
          fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I * w 0) := by
        funext t
        apply boundary_rigid z (h t) 0 ?_ i
        rw [exponential_norm, him 0, mul_zero, Real.exp_zero]
      have hd := exponential_hasDerivAt_zero (w i)
      rw [hfun] at hd
      exact mul_left_cancel₀ (by norm_num : (Complex.I : ℂ) ≠ 0)
        (hd.unique (exponential_hasDerivAt_zero (w 0)))
    refine ⟨(w 0).re, fun i => (he i).trans ?_⟩
    apply Complex.ext
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im, him 0]
  · rintro ⟨r, hr⟩ t
    refine ⟨fun _ => Complex.exp ((t : ℂ) * Complex.I * (r : ℂ)),
      differentiableOn_const, ?_, ?_⟩
    · intro x _
      rw [exponential_norm, Complex.ofReal_im, mul_zero, Real.exp_zero]
    · intro i
      rw [hr i]

#print axioms boundary_rigid
#print axioms unimodular_data_iff
#print axioms exponential_data_iff_real_constant
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.DiskInterpolation
