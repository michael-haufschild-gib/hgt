import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheIntegralOnTheRescaledProductShell

/-!
# Sampling at the moving conductor endpoints

A lower product threshold picks a terminal interval of conductors. Rounding
the lower endpoint and including the last conductor cost two samples. A
two-ended power shell is a signed difference of two such intervals.
-/

noncomputable section
open Finset MeasureTheory
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The tail beyond any real lower conductor cut. Clamping to M gives the
zero integral when the entire terminal block lies below the cut. -/
def realTailStart (N M : ℕ) (l : ℝ) := min (M:ℝ) (max (N:ℝ) l)

/-- Both rounding corrections in the discrete conductor tail are bounded
uniformly in the real product boundary, the mesh and the product. -/
theorem real_tail_sampling_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {N M : ℕ}, 0 < N → N ≤ M → ∀ (b : ℕ) {q : ℝ},
      0 < q → ∀ l : ℝ,
      |(∑ n ∈ Ioc N M with l ≤ (n:ℝ), (n:ℝ)*quotientMeshProfile b (q/(n:ℝ)^2)) -
        ∫ x in realTailStart N M l..M, x*quotientMeshProfile b (q/x^2)| ≤ K*(M+1:ℕ) := by
  obtain ⟨C,hC,hmesh⟩ := real_conductor_mesh_sampling
  obtain ⟨D,hD,hsamp⟩ := conductor_mesh_integral_error
  refine ⟨D+2*C,by positivity,fun {N M} hN hNM b q hq l => ?_⟩
  let F := fun x : ℝ => x*quotientMeshProfile b (q/x^2)
  have hN' : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hNM' : (N:ℝ) ≤ M := Nat.cast_le.mpr hNM
  have hMM : (M:ℝ) ≤ (M+1:ℕ) := Nat.cast_le.mpr (Nat.le_succ _)
  have hint {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : IntervalIntegrable F volume x y := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht0 := (lt_min hx hy).trans_le ht.1
    obtain ⟨_,_,hd⟩ := (hmesh b hq ht0).2
    exact hd.continuousAt.continuousWithinAt
  by_cases hl : l ≤ (M:ℝ)
  swap
  · have hem : ((Ioc N M).filter (fun n => l ≤ (n:ℝ))) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro n hn
      exact hl ((mem_filter.mp hn).2.trans (Nat.cast_le.mpr (mem_Ioc.mp (mem_filter.mp hn).1).2))
    rw [hem,sum_empty,realTailStart,min_eq_left ((le_of_not_ge hl).trans (le_max_right _ _)),
      intervalIntegral.integral_same,sub_self,abs_zero]
    positivity
  let r := max (N:ℝ) l
  let a := max (N+1) ⌈r⌉₊
  have hrN : (N:ℝ) ≤ r := le_max_left _ _
  have hrM : r ≤ M := max_le hNM' hl
  have haN : N+1 ≤ a := le_max_left _ _
  have ha : a ≤ M+1 := max_le (Nat.succ_le_succ hNM)
    ((Nat.ceil_le.mpr hrM).trans (Nat.le_succ M))
  have ha0 : 0 < a := (Nat.succ_pos _).trans_le haN
  have har : r ≤ a := (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right (N+1) ⌈r⌉₊))
  have har1 : (a:ℝ) ≤ r+1 := by
    dsimp only [a]
    rw [Nat.cast_max]
    apply max_le
    · push_cast; linarith only [hrN]
    · exact (Nat.ceil_lt_add_one (hN'.trans_le hrN).le).le
  have he : ((Ioc N M).filter fun n => l ≤ (n:ℝ)) = Ico a (M+1) := by
    ext n
    simp only [a,r,mem_filter,mem_Ioc,mem_Ico,max_le_iff,Nat.ceil_le]
    constructor
    · rintro ⟨⟨hlo,hu⟩,hl⟩
      exact ⟨⟨hlo,Nat.cast_le.mpr hlo.le,hl⟩,Nat.lt_succ_of_le hu⟩
    · rintro ⟨⟨hlo,_,hl⟩,hu⟩
      exact ⟨⟨hlo,Nat.le_of_lt_succ hu⟩,hl⟩
  have hprice {x y : ℝ} (hx : N ≤ x) (hxy : x ≤ y) (hy : y ≤ (M+1:ℕ))
      (hlen : y-x ≤ 1) : |∫ t in x..y, F t| ≤ C*(M+1:ℕ) := by
    have hb (t : ℝ) (ht : t ∈ Set.uIoc x y) : ‖F t‖ ≤ C*(M+1:ℕ) := by
      rw [Set.uIoc_of_le hxy] at ht
      exact ((hmesh b hq ((hN'.trans_le hx).trans ht.1)).1).trans
        (mul_le_mul_of_nonneg_left (ht.2.trans hy) hC)
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hxy)] at hh
    exact hh.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hlen (by positivity : 0 ≤ C*(M+1:ℕ)))
  have hlow := hprice hrN har (Nat.cast_le.mpr ha) (by linarith only [har1])
  have hhigh := hprice hNM' hMM le_rfl (by push_cast; ring_nf; exact le_rfl)
  have hM0 := hN'.trans_le hNM'
  have hd0 : (0:ℝ) < (M+1:ℕ) := hM0.trans_le hMM
  have hr0 := hN'.trans_le hrN
  have ha0' := hr0.trans_le har
  have hjoin1 := intervalIntegral.integral_add_adjacent_intervals (hint hr0 ha0') (hint ha0' hd0)
  have hjoin2 := intervalIntegral.integral_add_adjacent_intervals (hint hr0 hM0) (hint hM0 hd0)
  change |(∑ n ∈ (Ioc N M).filter (fun n => l ≤ (n:ℝ)), F n) - ∫ x in realTailStart N M l..M, F x| ≤ _
  rw [he,realTailStart,min_eq_right hrM]
  have hid : (∑ n ∈ Ico a (M+1), F n) - ∫ x in r..M, F x =
      ((∑ n ∈ Ico a (M+1), F n) - ∫ x in (a:ℝ)..((M+1:ℕ):ℝ), F x) +
      (∫ x in (M:ℝ)..((M+1:ℕ):ℝ), F x) - ∫ x in r..a, F x := by linarith only [hjoin1,hjoin2]
  rw [hid]
  apply (abs_sub _ _).trans ((add_le_add ((abs_add_le _ _).trans
    (add_le_add (hsamp ha0 ha b hq) hhigh)) hlow).trans _)
  have hlen' := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.sub_le (M+1) a) :
    ((M+1-a:ℕ):ℝ) ≤ (M+1:ℕ)) hD
  linarith only [hlen']

#print axioms real_tail_sampling_error
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
