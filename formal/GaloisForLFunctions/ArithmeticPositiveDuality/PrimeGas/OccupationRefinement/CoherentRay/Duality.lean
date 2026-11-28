import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay.Readings
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities.Isometry

/-! # Three occupations identify the unique dual of an associative prime splitter -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay

open ModeCapacities CoassociativeSplitting Finset
open scoped ComplexConjugate

def triple (w s : ℂ) (u v : ℕ → ℝ) (p : Nat.Primes) :=
  rayOverlap w s u v p 1=1 ∧ rayOverlap w s u v p 2=1 ∧ rayOverlap w s u v p 3=1

private theorem unit_polynomials (z a b : ℂ) (ha : a≠0) (hb : b≠0) :
    (polynomial z a b 1=1 ∧ polynomial z a b 2=1 ∧ polynomial z a b 3=1) ↔
      z=1 ∧ a+b=1 := by
  rw [polynomial_one,polynomial_two,polynomial_three]
  constructor
  · rintro ⟨h1,h2,h3⟩
    have two : (power z 2-2)*(a*b)=0 := by
      calc _ = (a^2+power z 2*a*b+b^2)-(a+b)^2 := by ring
           _ = 0 := by rw [h2,h1]; norm_num
    have three : (power z 3-3)*(a*b*(a+b))=0 := by
      calc _ = (a^3+power z 3*(a^2*b+a*b^2)+b^3)-(a+b)^3 := by ring
           _ = 0 := by rw [h3,h1]; norm_num
    rw [h1,mul_one] at three
    have nz := mul_ne_zero ha hb
    exact ⟨two_three z (sub_eq_zero.mp ((mul_eq_zero.mp two).resolve_right nz))
      (sub_eq_zero.mp ((mul_eq_zero.mp three).resolve_right nz)),h1⟩
  · rintro ⟨rfl,h⟩
    have two : power 1 2=2 := by simpa only [Complex.ofReal_ofNat] using power_at_one (by norm_num : 0<(2:ℝ))
    have three : power 1 3=3 := by simpa only [Complex.ofReal_ofNat] using power_at_one (by norm_num : 0<(3:ℝ))
    rw [two,three]
    refine ⟨h,?_,?_⟩
    · calc _ = (a+b)^2 := by ring
           _ = 1 := by rw [h,one_pow]
    · calc _ = (a+b)^3 := by ring
           _ = 1 := by rw [h,one_pow]

/-- The physical prime can be arbitrary. The two independent phase references
arise from occupation multiplicities at that same prime. -/
theorem triple_iff (w s : ℂ) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) (p : Nat.Primes) :
    triple w s u v p ↔ w=1-conj s := by
  simp only [triple,ray_polynomial w s hu hv,unit_polynomials _ _ _ (power_ne _ _) (power_ne _ _)]
  constructor
  · rintro ⟨h,_⟩
    have hw : conj w=1-s := eq_sub_of_add_eq h
    simpa only [Complex.conj_conj,map_sub,map_one] using congrArg conj hw
  · rintro rfl
    simp only [map_sub,map_one,Complex.conj_conj,sub_add_cancel,true_and,
      power_at_one (share_pos hu hv p),power_at_one (share_pos hv hu p),←Complex.ofReal_add,
      share_sum hu hv p,Complex.ofReal_one]

/-- A splitter is its own measured dual exactly when it is isometric. -/
theorem self_iff (s : ℂ) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) (p : Nat.Primes) :
    triple s s u v p ↔ isometric (kernel s u v) := by
  rw [triple_iff s s hu hv p,conserving_iff s hu hv]
  constructor
  · intro fixed
    have re := congrArg Complex.re fixed
    simp only [Complex.sub_re,Complex.one_re,Complex.conj_re] at re
    linarith only [re]
  · intro re
    apply Complex.ext
    · simp only [Complex.sub_re,Complex.one_re,Complex.conj_re]
      linarith only [re]
    · simp

/-- Coherent overlap of two finite output columns at a general integer label. -/
def overlap (w s : ℂ) (u v : ℕ → ℝ) (n : ℕ+) :=
  ∑ d : n.val.divisorsAntidiagonal,
    let x := divisorsAntidiagonalFactors n d
    conj (kernel w u v x.1 x.2)*kernel s u v x.1 x.2

theorem reflected_overlap (s : ℂ) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) (n : ℕ+) :
    overlap (1-conj s) s u v n=1 := by
  have paired (a b : ℕ+) : conj (kernel (1-conj s) u v a b)*kernel s u v a b =
      (branch u v a.val b.val:ℂ) := by
    change conj (power _ _)*power _ _=_
    rw [paired_power,map_sub,map_one,Complex.conj_conj,sub_add_cancel,power_at_one (branch_pos hu hv a b)]
  have H : (∑ d : n.val.divisorsAntidiagonal, branch u v d.val.1 d.val.2)=1 := by
    rw [univ_eq_attach,sum_attach _ (fun d : ℕ × ℕ => branch u v d.1 d.2),branch_sum hu hv]
  simp only [overlap,paired]
  change (∑ d : n.val.divisorsAntidiagonal, (branch u v d.val.1 d.val.2:ℂ))=1
  exact_mod_cast H

/-- Local duality at one prime selects the reflection of the completed
partition function and the partner on the entire integer spectrum. -/
theorem partition_partner (s : ℂ) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) (p : Nat.Primes) :
    ∃! w : ℂ, triple w s u v p ∧ (∀ n, overlap w s u v n=1) ∧
      completedRiemannZeta (conj w)=completedRiemannZeta s := by
  refine ⟨1-conj s,⟨(triple_iff _ _ hu hv p).mpr rfl,reflected_overlap s hu hv,?_⟩,
    fun w h => (triple_iff w s hu hv p).mp h.1⟩
  simp only [map_sub,map_one,Complex.conj_conj,completedRiemannZeta_one_sub]

#print axioms triple_iff
#print axioms self_iff
#print axioms reflected_overlap
#print axioms partition_partner

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay
