import GaloisForLFunctions.RHTower.BourgainPartialSummation

/-!
# Exact norm of a multiplier on bounded complex prefixes

Abel summation expresses the output as independent prefix readings. Aligning
each reading with its own coefficient realizes the entire disk given by the
variation bound. For an increasing real multiplier the exact radius is twice
its last value minus its first. This gives the cost of undoing a positive
decreasing taper when all its prefixes are observed.
-/

noncomputable section
open Finset Complex
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

/-- Last coefficient and all interior differences on the first N+1 terms. -/
def prefixMultiplierVariation (a : ℕ → ℂ) (N : ℕ) : ℝ :=
  ‖a (N+1)‖ + ∑ n ∈ Ioc 0 N, ‖a n-a (n+1)‖

private theorem abel_last (a f : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Ioc 0 (N+1), a n*f n) =
      a (N+1)*(∑ j ∈ Ioc 0 (N+1), f j)+
        ∑ n ∈ Ioc 0 N, (a n-a (n+1))*(∑ j ∈ Ioc 0 n, f j) := by
  rw [sum_Ioc_succ_top (Nat.zero_le N),_root_.RHTower.sum_Ioc_weight_mul_eq f a (Nat.zero_le N),
    sum_Ioc_succ_top (Nat.zero_le N)]
  ring

/-- Each prefix can have its own upper bound. The boundary and every
interior difference are charged at the prefix where they occur. -/
theorem prefix_multiplier_norm_le_weighted_variation (a f : ℕ → ℂ) (N : ℕ) (B : ℕ → ℝ)
    (hf : ∀ n ∈ Ioc 0 (N+1), ‖∑ j ∈ Ioc 0 n, f j‖ ≤ B n) :
    ‖∑ n ∈ Ioc 0 (N+1), a n*f n‖ ≤ ‖a (N+1)‖*B (N+1)+
      ∑ n ∈ Ioc 0 N, ‖a n-a (n+1)‖*B n := by
  rw [abel_last]
  refine (norm_add_le _ _).trans (add_le_add ?_ ((norm_sum_le _ _).trans ?_))
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hf _ (mem_Ioc.mpr ⟨by omega,le_rfl⟩)) (norm_nonneg _)
  · apply sum_le_sum
    intro n hn
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (hf n (mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1,(mem_Ioc.mp hn).2.trans (Nat.le_succ N)⟩)) (norm_nonneg _)

/-- A bound for every observed prefix controls the weighted endpoint. -/
theorem prefix_multiplier_norm_le (a f : ℕ → ℂ) (N : ℕ) {B : ℝ}
    (hf : ∀ n ∈ Ioc 0 (N+1), ‖∑ j ∈ Ioc 0 n, f j‖ ≤ B) :
    ‖∑ n ∈ Ioc 0 (N+1), a n*f n‖ ≤ prefixMultiplierVariation a N*B := by
  simpa only [prefixMultiplierVariation,add_mul,sum_mul] using
    prefix_multiplier_norm_le_weighted_variation a f N (fun _ => B) hf

private def extremalPhase (z : ℂ) : ℂ := (‖z‖:ℂ)/z

private theorem extremalPhase_norm (z : ℂ) : ‖extremalPhase z‖ ≤ 1 := by
  by_cases hz : z=0
  · simp [extremalPhase,hz]
  · simp [extremalPhase,Complex.norm_real,div_self (norm_ne_zero_iff.mpr hz)]

private theorem mul_extremalPhase (z : ℂ) : z*extremalPhase z=(‖z‖:ℂ) := by
  by_cases hz : z=0
  · simp [hz]
  · unfold extremalPhase; field_simp

private theorem prefix_increments (p : ℕ → ℂ) (n : ℕ) :
    (∑ j ∈ Ioc 0 n, (p j-p (j-1))) = p n-p 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le n),ih]
    simp only [Nat.add_sub_cancel]
    ring

private theorem extremal_increments (a : ℕ → ℂ) (N : ℕ) :
    ∃ f : ℕ → ℂ, (∀ n ∈ Ioc 0 (N+1), ‖∑ j ∈ Ioc 0 n, f j‖ ≤ 1) ∧
      (∑ n ∈ Ioc 0 (N+1), a n*f n) = (prefixMultiplierVariation a N:ℂ) := by
  let p (n : ℕ) : ℂ := if n=0 then 0 else
    if n=N+1 then extremalPhase (a n) else extremalPhase (a n-a (n+1))
  have hp0 : p 0=0 := by simp [p]
  let f (n : ℕ) := p n-p (n-1)
  have hf (n : ℕ) : (∑ j ∈ Ioc 0 n, f j)=p n := by
    rw [show (∑ j ∈ Ioc 0 n, f j)=p n-p 0 from prefix_increments p n,hp0,sub_zero]
  refine ⟨f,?_,?_⟩
  · intro n hn
    rw [hf]
    simp only [p,if_neg (Nat.ne_of_gt (mem_Ioc.mp hn).1)]
    split <;> exact extremalPhase_norm _
  · rw [abel_last]
    simp_rw [hf]
    have hend : p (N+1)=extremalPhase (a (N+1)) := by simp [p]
    rw [hend,mul_extremalPhase,prefixMultiplierVariation,ofReal_add,ofReal_sum]
    congr 1
    apply sum_congr rfl
    intro n hn
    have h := mem_Ioc.mp hn
    simp only [p,if_neg (Nat.ne_of_gt h.1),if_neg (show n ≠ N+1 by omega),mul_extremalPhase]

/-- The weighted endpoint attainable from complex prefixes in the unit disk
is exactly the closed disk of radius equal to the discrete variation. -/
theorem attainable_prefix_multiplier_iff (a : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    (∃ f : ℕ → ℂ, (∀ n ∈ Ioc 0 (N+1), ‖∑ j ∈ Ioc 0 n, f j‖ ≤ 1) ∧
      (∑ n ∈ Ioc 0 (N+1), a n*f n)=z) ↔ ‖z‖ ≤ prefixMultiplierVariation a N := by
  constructor
  · rintro ⟨f,hf,rfl⟩
    simpa only [mul_one] using prefix_multiplier_norm_le a f N hf
  · intro hz
    obtain ⟨f,hf,he⟩ := extremal_increments a N
    let V := prefixMultiplierVariation a N
    have hV : 0 ≤ V := by dsimp [V,prefixMultiplierVariation]; positivity
    by_cases hzero : V=0
    · have hz0 : z=0 := norm_le_zero_iff.mp (hz.trans_eq hzero)
      exact ⟨fun _ => 0,by simp,by simp [hz0]⟩
    let c : ℂ := z/(V:ℂ)
    have hc : ‖c‖ ≤ 1 := by
      rw [show ‖c‖=‖z‖/V by simp [c,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hV]]
      exact (div_le_one (lt_of_le_of_ne hV (Ne.symm hzero))).mpr hz
    refine ⟨fun n => c*f n,fun n hn => ?_,?_⟩
    · rw [←mul_sum,norm_mul]
      exact (mul_le_mul hc (hf n hn) (norm_nonneg _) zero_le_one).trans_eq (mul_one _)
    · calc (∑ n ∈ Ioc 0 (N+1), a n*(c*f n)) = c*∑ n ∈ Ioc 0 (N+1), a n*f n := by
             rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
        _ = z := by rw [he]; exact div_mul_cancel₀ z (Complex.ofReal_ne_zero.mpr hzero)

/-- Increasing nonnegative weights incur an exact factor of 2a(N+1)-a(1).
In particular this applies to reciprocals of any positive decreasing taper. -/
theorem increasing_prefix_multiplier_variation (a : ℕ → ℝ) (ha : Monotone a)
    (h0 : 0 ≤ a 1) (N : ℕ) :
    prefixMultiplierVariation (fun n => (a n:ℂ)) N = 2*a (N+1)-a 1 := by
  have hend := h0.trans (ha (show 1 ≤ N+1 by omega))
  have hdiff (n : ℕ) : ‖(a n:ℂ)-(a (n+1):ℂ)‖ = -(a n-a (n+1)) := by
    rw [←ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr (ha (Nat.le_succ n)))]
  simp only [prefixMultiplierVariation,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hend,hdiff,
    sum_neg_distrib,_root_.RHTower.sum_Ioc_sub_succ a (Nat.zero_le N),Nat.zero_add]
  ring

/-- Recovering an untapered sum from all tapered prefixes at this cutoff. -/
theorem untapered_endpoint_le (w : ℕ → ℝ) (hw : ∀ n, 0 < w n) (hm : Antitone w)
    (f : ℕ → ℂ) (N : ℕ) {B : ℝ}
    (hB : ∀ n ∈ Ioc 0 (N+1), ‖∑ j ∈ Ioc 0 n, (w j:ℂ)*f j‖ ≤ B) :
    ‖∑ j ∈ Ioc 0 (N+1), f j‖ ≤ (2*(w (N+1))⁻¹-(w 1)⁻¹)*B := by
  let v (n : ℕ) := (w n)⁻¹
  have hv : Monotone v := fun i j hij => inv_anti₀ (hw j) (hm hij)
  have hmul (n : ℕ) : (v n:ℂ)*(w n:ℂ)=1 := by
    rw [show (v n:ℂ)=(w n:ℂ)⁻¹ from ofReal_inv _,inv_mul_cancel₀ (ofReal_ne_zero.mpr (hw n).ne')]
  have h := prefix_multiplier_norm_le (fun n => (v n:ℂ)) (fun n => (w n:ℂ)*f n) N hB
  rw [increasing_prefix_multiplier_variation v hv (inv_nonneg.mpr (hw 1).le)] at h
  simpa only [←mul_assoc,hmul,one_mul] using h

/-- The optimal converse to the decreasing-taper inequality. Every point
of the disk is attained with the same taper and cutoff. -/
theorem attainable_untapered_endpoint_iff (w : ℕ → ℝ) (hw : ∀ n, 0 < w n)
    (hm : Antitone w) (N : ℕ) (z : ℂ) :
    (∃ f : ℕ → ℂ, (∀ n ∈ Ioc 0 (N+1), ‖∑ j ∈ Ioc 0 n, (w j:ℂ)*f j‖ ≤ 1) ∧
      (∑ n ∈ Ioc 0 (N+1), f n)=z) ↔ ‖z‖ ≤ 2*(w (N+1))⁻¹-(w 1)⁻¹ := by
  let v (n : ℕ) := (w n)⁻¹
  have hv : Monotone v := fun i j hij => inv_anti₀ (hw j) (hm hij)
  have hmul (n : ℕ) : (v n:ℂ)*(w n:ℂ)=1 := by
    rw [show (v n:ℂ)=(w n:ℂ)⁻¹ from ofReal_inv _,inv_mul_cancel₀ (ofReal_ne_zero.mpr (hw n).ne')]
  have he := attainable_prefix_multiplier_iff (fun n => (v n:ℂ)) N z
  rw [increasing_prefix_multiplier_variation v hv (inv_nonneg.mpr (hw 1).le)] at he
  constructor
  · rintro ⟨f,hf,hs⟩
    apply he.mp
    refine ⟨fun n => (w n:ℂ)*f n,hf,?_⟩
    simpa only [←mul_assoc,hmul,one_mul] using hs
  · intro hz
    obtain ⟨g,hg,hs⟩ := he.mpr hz
    refine ⟨fun n => (v n:ℂ)*g n,fun n hn => ?_,hs⟩
    have hrev (j : ℕ) : (w j:ℂ)*(v j:ℂ)=1 := (mul_comm _ _).trans (hmul j)
    simpa only [←mul_assoc,hrev,one_mul] using hg n hn

#print axioms attainable_untapered_endpoint_iff
#print axioms attainable_prefix_multiplier_iff
#print axioms increasing_prefix_multiplier_variation

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
