import GaloisForLFunctions.HeightHomotopyArithmeticCounts.WeightedTorsionLimit
import GaloisForLFunctions.HeightHomotopyArithmeticCounts.InfiniteSpacingConvergence

/-!
# Infinite torsion forms on weighted probes

Finite absolute kernel estimates pass to the whole pair series through square
conductor windows. Applying the estimate to `|x|+|y|` also controls mixed probes.
The actual scalar-renormalized torsion form is absolutely convergent, and its
quadratic difference from the arithmetic limit retains the uniform power rate.
-/

noncomputable section
open Finset Filter Topology
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts
open ArithmeticEffectivityTheory ArithmeticIntersectionTheory

/-- A uniform finite-support bound controls the whole absolute kernel series. -/
theorem kernel_infinite_absolute_of_finite_bound (δ C : ℝ) (hC : 0 ≤ C)
    (K : ℕ → ℕ → ℝ)
    (hbound : ∀ (S : Finset ℕ) (x : ℕ → ℝ), (∀ n ∈ S, 0 < n) →
      (∑ m ∈ S, ∑ n ∈ S, |x m*x n*K m n|) ≤ C*∑ n ∈ S, (n:ℝ)^δ*(x n)^2)
    (x : ℕ → ℝ) (hx0 : x 0=0)
    (hx : Summable (fun n : ℕ => (n:ℝ)^δ*(x n)^2)) :
    Summable (fun p : ℕ×ℕ => |x p.1*x p.2*K p.1 p.2|) ∧
    (∑' p : ℕ×ℕ, |x p.1*x p.2*K p.1 p.2|) ≤ C*∑' n : ℕ, (n:ℝ)^δ*(x n)^2 := by
  classical
  have hfinite (u : Finset (ℕ×ℕ)) :
      (∑ p ∈ u, |x p.1*x p.2*K p.1 p.2|) ≤ 
        C*(∑' n : ℕ, (n:ℝ)^δ*(x n)^2) := by
    let N := u.sup (fun p => max p.1 p.2)
    have hN (p : ℕ×ℕ) (hp : p∈u) : p.1 ≤ N ∧ p.2 ≤ N :=
      ⟨(le_max_left _ _).trans (Finset.le_sup (f := fun p => max p.1 p.2) hp),
       (le_max_right _ _).trans (Finset.le_sup (f := fun p => max p.1 p.2) hp)⟩
    let v := u.filter (fun p => 0 < p.1 ∧ 0 < p.2)
    have hremove : (∑ p ∈ v, |x p.1*x p.2*K p.1 p.2|) =
        ∑ p ∈ u, |x p.1*x p.2*K p.1 p.2| := by
      apply sum_subset (filter_subset _ _)
      intro p hp hnot
      have hbad : ¬(0 < p.1 ∧ 0 < p.2) := fun h => hnot (mem_filter.mpr ⟨hp, h⟩)
      have hzero : p.1=0 ∨ p.2=0 := by omega
      rcases hzero with h | h
      · rw [h, hx0, zero_mul, zero_mul, abs_zero]
      · rw [h, hx0, mul_zero, zero_mul, abs_zero]
    have hsub : v ⊆ Icc 1 N ×ˢ Icc 1 N := by
      intro p hp
      obtain ⟨hpu, hp1, hp2⟩ := mem_filter.mp hp
      exact mem_product.mpr ⟨mem_Icc.mpr ⟨hp1, (hN p hpu).1⟩,
        mem_Icc.mpr ⟨hp2, (hN p hpu).2⟩⟩
    calc (∑ p ∈ u, |x p.1*x p.2*K p.1 p.2|) =
          ∑ p ∈ v, |x p.1*x p.2*K p.1 p.2| := hremove.symm
         _ ≤ ∑ p ∈ Icc 1 N ×ˢ Icc 1 N,
          |x p.1*x p.2*K p.1 p.2| :=
          sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
         _ = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
          |x m*x n*K m n| := by rw [sum_product]
         _ ≤ C*∑ n ∈ Icc 1 N, (n:ℝ)^δ*(x n)^2 :=
          hbound (Icc 1 N) x (fun n hn => (mem_Icc.mp hn).1)
         _ ≤ _ := mul_le_mul_of_nonneg_left
          (hx.sum_le_tsum _ (fun n _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _)))
          hC
  exact ⟨summable_of_sum_le (fun _ => abs_nonneg _) hfinite,
    Real.tsum_le_of_sum_le (fun _ => abs_nonneg _) hfinite⟩

/-- Finite quadratic absolute bounds also control mixed infinite probes. -/
theorem kernel_infinite_mixed_of_finite_bound (δ C : ℝ) (hC : 0 ≤ C)
    (K : ℕ → ℕ → ℝ)
    (hbound : ∀ (S : Finset ℕ) (x : ℕ → ℝ), (∀ n ∈ S, 0 < n) →
      (∑ m ∈ S, ∑ n ∈ S, |x m*x n*K m n|) ≤ C*∑ n ∈ S, (n:ℝ)^δ*(x n)^2)
    (x y : ℕ → ℝ) (hx0 : x 0=0) (hy0 : y 0=0)
    (hx : Summable (fun n : ℕ => (n:ℝ)^δ*(x n)^2))
    (hy : Summable (fun n : ℕ => (n:ℝ)^δ*(y n)^2)) :
    Summable (fun p : ℕ×ℕ => |x p.1*y p.2*K p.1 p.2|) ∧
    (∑' p : ℕ×ℕ, |x p.1*y p.2*K p.1 p.2|) ≤
      2*C*((∑' n : ℕ, (n:ℝ)^δ*(x n)^2)+(∑' n : ℕ, (n:ℝ)^δ*(y n)^2)) := by
  let z : ℕ → ℝ := fun n => |x n|+|y n|
  have hz0 : z 0=0 := by simp only [z, hx0, hy0, abs_zero, add_zero]
  have hzpos (n : ℕ) : 0 ≤ z n := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hzbound (n : ℕ) : (n:ℝ)^δ*(z n)^2 ≤
      2*((n:ℝ)^δ*(x n)^2+(n:ℝ)^δ*(y n)^2) := by
    have hs : (z n)^2 ≤ 2*((x n)^2+(y n)^2) := by
      dsimp only [z]
      nlinarith only [sq_nonneg (|x n|-|y n|), sq_abs (x n), sq_abs (y n)]
    have h := mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg (Nat.cast_nonneg n) δ)
    calc (n:ℝ)^δ*(z n)^2 ≤ (n:ℝ)^δ*(2*((x n)^2+(y n)^2)) := h
         _ = _ := by ring
  have hmajor := (hx.add hy).mul_left 2
  have hz : Summable (fun n : ℕ => (n:ℝ)^δ*(z n)^2) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg n) δ) (sq_nonneg _)) hzbound hmajor
  have hzmass : (∑' n : ℕ, (n:ℝ)^δ*(z n)^2) ≤
      2*((∑' n : ℕ, (n:ℝ)^δ*(x n)^2)+(∑' n : ℕ, (n:ℝ)^δ*(y n)^2)) := by
    calc _ ≤ ∑' n : ℕ, 2*((n:ℝ)^δ*(x n)^2+(n:ℝ)^δ*(y n)^2) :=
          hz.tsum_le_tsum hzbound hmajor
         _ = _ := by rw [tsum_mul_left, hx.tsum_add hy]
  obtain ⟨hZ, hZbound⟩ := kernel_infinite_absolute_of_finite_bound δ C hC K hbound z hz0 hz
  have hpoint (p : ℕ×ℕ) : |x p.1*y p.2*K p.1 p.2| ≤ |z p.1*z p.2*K p.1 p.2| := by
    simp only [abs_mul, abs_of_nonneg (hzpos _)]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    exact mul_le_mul (le_add_of_nonneg_right (abs_nonneg _))
      (le_add_of_nonneg_left (abs_nonneg _)) (abs_nonneg _) (hzpos _)
  have hxy := Summable.of_nonneg_of_le (fun p => abs_nonneg (x p.1*y p.2*K p.1 p.2)) hpoint hZ
  refine ⟨hxy, ?_⟩
  calc _ ≤ ∑' p : ℕ×ℕ, |z p.1*z p.2*K p.1 p.2| := hxy.tsum_le_tsum hpoint hZ
       _ ≤ C*∑' n : ℕ, (n:ℝ)^δ*(z n)^2 := hZbound
       _ ≤ C*(2*((∑' n : ℕ, (n:ℝ)^δ*(x n)^2)+(∑' n : ℕ, (n:ℝ)^δ*(y n)^2))) :=
        mul_le_mul_of_nonneg_left hzmass hC
       _ = _ := by ring

/-- The actual limiting arithmetic kernel is absolutely summable on every weighted probe. -/
theorem spacingLimitKernel_infinite_absolute_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℕ → ℝ), x 0=0 →
      Summable (fun n : ℕ => (n:ℝ)^δ*(x n)^2) →
      Summable (fun p : ℕ×ℕ => |x p.1*x p.2*spacingLimitKernel p.1 p.2|) ∧
      (∑' p : ℕ×ℕ, |x p.1*x p.2*spacingLimitKernel p.1 p.2|) ≤
        C*∑' n : ℕ, (n:ℝ)^δ*(x n)^2 := by
  obtain ⟨C, hC, hfinite⟩ := spacingLimitKernel_weighted_absolute_bound δ hδ
  exact ⟨C, hC, fun x hx0 hx =>
    kernel_infinite_absolute_of_finite_bound δ C hC.le spacingLimitKernel hfinite x hx0 hx⟩

/-- The original spacing entry with its universal scalar diagonal counterterm. -/
def spacingRenormalizedKernel (ε : ℝ) (m n : ℕ) : ℝ :=
  twistedEnergy (spacingRadius ε m n) m n + if m=n then Real.log (2*ε) else 0

/-- The regularized kernel splits into its arithmetic limit and the controlled error. -/
theorem spacingRenormalizedKernel_eq (ε : ℝ) (m n : ℕ) :
    spacingRenormalizedKernel ε m n=spacingLimitKernel m n+spacingKernelError ε m n := by
  unfold spacingRenormalizedKernel spacingLimitKernel spacingKernelError
  by_cases h : m=n <;> simp only [h, if_true, if_false] <;> ring

/-- Swapping primitive orbits preserves the original torsion energy. -/
theorem torsionEnergy_comm (r : ℝ) (m n : ℕ) : torsionEnergy r m n=torsionEnergy r n m := by
  rw [ArithmeticElectrostatics.torsionEnergy_eq_bilinear,
    ArithmeticElectrostatics.torsionEnergy_eq_bilinear, sum_comm]
  apply sum_congr rfl
  intro z hz
  apply sum_congr rfl
  intro w hw
  rw [mul_comm z w]

/-- The spacing-regulated kernel is symmetric before and after scalar subtraction. -/
theorem spacingRenormalizedKernel_comm (ε : ℝ) (m n : ℕ) :
    spacingRenormalizedKernel ε m n=spacingRenormalizedKernel ε n m := by
  have hr : spacingRadius ε m n=spacingRadius ε n m := by
    simp only [spacingRadius, add_comm]
  unfold spacingRenormalizedKernel twistedEnergy
  rw [hr, gcdTwist_eq m n, gcdTwist_eq n m, Nat.gcd_comm m n,
    torsionEnergy_comm _ m n, mul_comm (m:ℝ) (n:ℝ)]
  by_cases h : m=n
  · subst n; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- The infinite limit is defined directly by the arithmetic kernel. -/
def infiniteSpacingLimit (x y : ℕ → ℝ) : ℝ :=
  ∑' p : ℕ×ℕ, x p.1*y p.2*spacingLimitKernel p.1 p.2

/-- The infinite scalar-renormalized spacing pairing uses the original torsion energy. -/
def infiniteRenormalizedSpacing (ε : ℝ) (x y : ℕ → ℝ) : ℝ :=
  ∑' p : ℕ×ℕ, x p.1*y p.2*spacingRenormalizedKernel ε p.1 p.2

/-- Both full kernels are absolutely summable, and their infinite quadratic difference is exact. -/
theorem infiniteSpacing_difference (δ : ℝ) (hδ : 0 < δ)
    (ε : ℝ) (hε : 0 < ε) (x : ℕ → ℝ) (hx0 : x 0=0)
    (hx : Summable (fun n : ℕ => (n:ℝ)^δ*(x n)^2)) :
    Summable (fun p : ℕ×ℕ => |x p.1*x p.2*spacingRenormalizedKernel ε p.1 p.2|) ∧
    infiniteRenormalizedSpacing ε x x-infiniteSpacingLimit x x =
      ∑' p : ℕ×ℕ, x p.1*x p.2*spacingKernelError ε p.1 p.2 := by
  obtain ⟨A, _hA, hL⟩ := spacingLimitKernel_infinite_absolute_bound δ hδ
  obtain ⟨C, _hC, hE⟩ := spacingKernelError_infinite_absolute_bound δ hδ
  have hLs := (hL x hx0 hx).1.of_abs
  have hEs := (hE ε x hε hx0 hx).1.of_abs
  have hsplit (p : ℕ×ℕ) : x p.1*x p.2*spacingRenormalizedKernel ε p.1 p.2 =
      x p.1*x p.2*spacingLimitKernel p.1 p.2+x p.1*x p.2*spacingKernelError ε p.1 p.2 := by
    rw [spacingRenormalizedKernel_eq, mul_add]
  have hRs := (hLs.add hEs).congr (fun p => (hsplit p).symm)
  refine ⟨hRs.abs, ?_⟩
  unfold infiniteRenormalizedSpacing infiniteSpacingLimit
  simp_rw [hsplit]
  rw [hLs.tsum_add hEs]
  ring

/-- The infinite scalar-renormalized quadratic forms obey the same uniform weighted rate. -/
theorem infiniteSpacing_weighted_error_rate (δ α : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hgap : 2*α < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (x : ℕ → ℝ), 0 < ε → x 0=0 →
      Summable (fun n : ℕ => (n:ℝ)^δ*(x n)^2) →
      |infiniteRenormalizedSpacing ε x x-infiniteSpacingLimit x x| ≤
        C*ε^α*∑' n : ℕ, (n:ℝ)^δ*(x n)^2 := by
  have hδ : 0 < δ := lt_trans (mul_pos (by norm_num) hα) hgap
  obtain ⟨C, hC, hE⟩ := spacingKernelError_infinite_absolute_rate δ α hα hα1 hgap
  refine ⟨C, hC, ?_⟩
  intro ε x hε hx0 hx
  rw [(infiniteSpacing_difference δ hδ ε hε x hx0 hx).2]
  have hs := (hE ε x hε hx0 hx).1
  have habs : |∑' p : ℕ×ℕ, x p.1*x p.2*spacingKernelError ε p.1 p.2| ≤
      ∑' p : ℕ×ℕ, |x p.1*x p.2*spacingKernelError ε p.1 p.2| := by
    simpa only [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun p : ℕ×ℕ =>
        x p.1*x p.2*spacingKernelError ε p.1 p.2) hs
  exact habs.trans (hE ε x hε hx0 hx).2

#print axioms kernel_infinite_mixed_of_finite_bound
#print axioms spacingRenormalizedKernel_comm
#print axioms spacingLimitKernel_infinite_absolute_bound
#print axioms infiniteSpacing_difference
#print axioms infiniteSpacing_weighted_error_rate
end GaloisForLFunctions.HeightHomotopyArithmeticCounts
