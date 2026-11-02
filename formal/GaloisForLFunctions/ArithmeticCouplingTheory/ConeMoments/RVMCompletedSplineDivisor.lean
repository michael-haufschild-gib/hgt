import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.RVMCompletionSeries
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.ZeroExponentSplineQuartets

/-!
# Exact spline divisors with the Riemann–von Mangoldt count

Critical-line completion preserves the sparse off-axis core and bounded
two-prime cone coupling while imposing the full two-term counting law.
The divisor is simple, sign and conjugation invariant, and has an
unattained positive horizontal width.
-/

set_option autoImplicit false
noncomputable section
open Finset Complex Filter Topology
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

lemma signedSplineAtom_conjugate {α : Type*} (w : α → ℂ)
    (hr : ∀ a,∃ b,w b= -(starRingEnd ℂ) (w a)) (a : α × Bool) :
    ∃ b : α × Bool,signedSplineAtom w b=(starRingEnd ℂ) (signedSplineAtom w a) := by
  obtain ⟨c,hc⟩ := hr a.1
  refine ⟨(c,!a.2),?_⟩
  rcases a with ⟨a,b⟩
  cases b <;> simp [signedSplineAtom,hc]

lemma rvmCompletion_kernel_real {ι : Type*} (z : ι → ℂ)
    (hall : ∀ t : ℝ,Summable (fun i => splineMomentCoefficient (z i)*Complex.exp ((t:ℂ)*z i)))
    (t : ℝ) : star (prescribedSplineLaplace (signedSplineAtom (rvmCompletionPositiveAtom z)) t)=
      prescribedSplineLaplace (signedSplineAtom (rvmCompletionPositiveAtom z)) t := by
  simp only [rvmCompletion_kernel_decomposition z hall,star_add,star_rvmCriticalSlot_pairKernel,
    ← prescribedSplineQuartetKernel_hermitian,prescribedSplineQuartetKernel_neg]

lemma rvmCompletion_kernel_even {ι : Type*} (z : ι → ℂ)
    (hall : ∀ t : ℝ,Summable (fun i => splineMomentCoefficient (z i)*Complex.exp ((t:ℂ)*z i)))
    (t : ℝ) : prescribedSplineLaplace (signedSplineAtom (rvmCompletionPositiveAtom z)) (-t)=
      prescribedSplineLaplace (signedSplineAtom (rvmCompletionPositiveAtom z)) t := by
  simp only [rvmCompletion_kernel_decomposition z hall,
    prescribedSplineQuartetKernel_neg,prescribedSplinePairKernel_neg]

lemma rvmCompletion_coupling_bound {ι : Type*} (z : ι → ℂ)
    (hall : ∀ t : ℝ,Summable (fun i => splineMomentCoefficient (z i)*Complex.exp ((t:ℂ)*z i)))
    (x y : ℝ)
    (hc : ‖prescribedSplineQuartetKernel z (x+y)-prescribedSplineQuartetKernel z x-
      prescribedSplineQuartetKernel z y+prescribedSplineQuartetKernel z 0‖≤20) :
    ‖prescribedSplineLaplace (signedSplineAtom (rvmCompletionPositiveAtom z)) (x+y)-
      prescribedSplineLaplace (signedSplineAtom (rvmCompletionPositiveAtom z)) x-
      prescribedSplineLaplace (signedSplineAtom (rvmCompletionPositiveAtom z)) y+
      prescribedSplineLaplace (signedSplineAtom (rvmCompletionPositiveAtom z)) 0‖≤
      20+8*∑' i,‖splineMomentCoefficient (rvmCriticalSlotAtom (rvmCompletionCriticalCount z)
        (rvmCompletionCriticalCount_le z) i)‖ := by
  simp only [rvmCompletion_kernel_decomposition z hall]
  have he (a b c d e f g h : ℂ) : (a+b)-(c+d)-(e+f)+(g+h)=
      (a-c-e+g)+(b-d-f+h) := by ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hc
    (rvmCriticalSlot_pair_coupling_le _ (rvmCompletionCriticalCount_le z) x y))

/-- Exact spline weights and the full Riemann–von Mangoldt counting law do not
force zero width from bounded natural two-prime cone coupling. -/
theorem exists_two_prime_rvm_prescribed_spline_divisor {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) {d D : ℝ}
    (hd : 0<d) (hdD : d<D) :
    ∃ (α : Type) (_ : Countable α) (w : α → ℂ),
      Function.Injective w ∧
      (∀ a,|(w a).re|<D ∧ 1≤|(w a).im|) ∧
      (∀ r : ℝ,r<D → ∃ a,r<(w a).re) ∧
      (∀ a,∃ b,w b= -w a) ∧
      (∀ a,∃ b,w b=(starRingEnd ℂ) (w a)) ∧
      (∀ a,splineMomentCoefficient (w a)≠0) ∧
      Summable (fun a => ‖splineMomentCoefficient (w a)‖) ∧
      (∀ t : ℝ,Summable (fun a => splineMomentCoefficient (w a)*Complex.exp ((t:ℂ)*w a))) ∧
      (∀ t : ℝ,prescribedSplineLaplace w (-t)=prescribedSplineLaplace w t ∧
        star (prescribedSplineLaplace w t)=prescribedSplineLaplace w t) ∧
      (∀ T : ℝ,Finite {a : α // 0<(w a).im ∧ (w a).im≤T}) ∧
      (∃ C : ℝ,0<C ∧ ∀ᶠ T : ℝ in atTop,
        |(Nat.card {a : α // 0<(w a).im ∧ (w a).im≤T}:ℝ)-_root_.RHTower.routeKSmoothRVMCount T|≤C*Real.log T) ∧
      (∃ B : ℝ,0<B ∧ ∀ m n : ℕ,
        ‖prescribedSplineLaplace w (m*Real.log p+n*Real.log q)-
          prescribedSplineLaplace w (m*Real.log p)-prescribedSplineLaplace w (n*Real.log q)+
          prescribedSplineLaplace w 0‖≤B) := by
  obtain ⟨ι,hι,z,hinj,hquartet,hstrip,him,hwidth,hcoeff,hs,hmass,hcount,hlocal,
    hquartetLocal,hinverse,hquartetInverse,hall,hzero,hcoupling⟩ :=
    exists_two_prime_zero_exponent_prescribed_spline_cone_model hp hq hpq hd hdD
  letI (j : ℕ) := splineCoreBlockFintype z him hlocal j
  letI (j : ℕ) : Fintype (RVMCompletionBlock z j) :=
    inferInstanceAs (Fintype ((SplineCoreBlock z j × Bool) ⊕ Fin (rvmCompletionCriticalCount z j)))
  let A := (j : ℕ) × RVMCompletionBlock z j
  let v : A → ℂ := rvmCompletionPositiveAtom z
  let w : A × Bool → ℂ := signedSplineAtom v
  have hvim (a : A) : 1≤(v a).im := by
    have hh := (rvmCompletionPositiveAtom_bounds z him a.1 a.2).1
    have hj := Nat.cast_nonneg (α := ℝ) a.1
    change (a.1:ℝ)+1≤(v a).im at hh
    linarith only [hh,hj]
  have hvpos (a : A) : 0<(v a).im := zero_lt_one.trans_le (hvim a)
  have hval : ∀ t : ℝ,Summable (fun a => splineMomentCoefficient (v a)*Complex.exp ((t:ℂ)*v a)) :=
    summable_rvmCompletionPositive_moment z hall
  have hwall : ∀ t : ℝ,Summable (fun a => splineMomentCoefficient (w a)*Complex.exp ((t:ℂ)*w a)) :=
    summable_signedSplineAtom_moment v hval
  refine ⟨A × Bool,inferInstance,w,
    signedSplineAtom_injective v (rvmCompletionPositiveAtom_injective z him
      (fun i => hd.trans_le (hstrip i).1) hquartet) hvpos,?_,?_,?_,?_,?_,?_,hwall,?_,?_,?_,?_⟩
  · intro a
    constructor
    · change |(signedSplineAtom v a).re|<D
      rw [signedSplineAtom_abs_re]
      exact rvmCompletionPositiveAtom_width z (hd.trans hdD)
        (fun i => ⟨hd.le.trans (hstrip i).1,(hstrip i).2⟩) a.1
    · rcases a with ⟨a,b⟩
      cases b <;> simpa only [w,signedSplineAtom,Bool.false_eq_true,if_false,if_true,Complex.neg_im,abs_neg,
        abs_of_pos (hvpos a)] using hvim a
  · intro r hr
    obtain ⟨a,ha⟩ := rvmCompletionPositiveAtom_width_cofinal z hwidth r hr
    exact ⟨(a,false),ha⟩
  · intro a
    exact ⟨(a.1,!a.2),signedSplineAtom_neg v a⟩
  · exact signedSplineAtom_conjugate v (rvmCompletionPositiveAtom_reflection z)
  · exact signedSplineAtom_coefficient_ne_zero v (rvmCompletionPositiveAtom_coefficient_ne_zero z hcoeff)
  · simpa only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one] using (hwall 0).norm
  · intro t
    exact ⟨rvmCompletion_kernel_even z hall t,rvmCompletion_kernel_real z hall t⟩
  · intro T
    letI := finite_rvmCompletionPositive_truncation z him hlocal T
    exact Finite.of_injective (signedSplineCountEquiv v hvpos T).symm
      (signedSplineCountEquiv v hvpos T).symm.injective
  · obtain ⟨C,hC,hCbound⟩ := exists_rvmCompletionPositiveAtom_count z him hlocal
    refine ⟨C,hC,?_⟩
    filter_upwards [hCbound] with T hT
    have he := Nat.card_congr (signedSplineCountEquiv v hvpos T)
    change Nat.card {a : A // (v a).im≤T}=
      Nat.card {a : A × Bool // 0<(w a).im ∧ (w a).im≤T} at he
    rw [← he]
    exact hT
  · refine ⟨20+8*∑' i,‖splineMomentCoefficient (rvmCriticalSlotAtom
        (rvmCompletionCriticalCount z) (rvmCompletionCriticalCount_le z) i)‖,?_,?_⟩
    · have hh : 0≤∑' i,‖splineMomentCoefficient (rvmCriticalSlotAtom
          (rvmCompletionCriticalCount z) (rvmCompletionCriticalCount_le z) i)‖ :=
        tsum_nonneg fun _ => norm_nonneg _
      positivity
    · intro m n
      exact rvmCompletion_coupling_bound z hall _ _ (hcoupling m n)

#print axioms exists_two_prime_rvm_prescribed_spline_divisor
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
