import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.Spacing.GaussianRows

/-! # Gaussian quadratic forms and collision mass in unit frequency bins -/
open Finset Real
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
open private gaussian_floor_weight dyadic_integer_sum from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.Spacing.GaussianRows
noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]

private def fiberMass (c : I → J) (a : I → ℝ) (j : J) := ∑ i ∈ univ.filter (c · = j), a i

private theorem sum_by_bins (c : I → J) (a : I → ℝ) (f : J → ℝ) :
    ∑ i, a i*f (c i)=∑ j, fiberMass c a j*f j := by
  rw [←sum_fiberwise univ c (fun i => a i*f (c i))]
  apply sum_congr rfl
  intro j _
  rw [fiberMass,sum_mul]
  exact sum_congr rfl fun i hi => congrArg (a i * ·) (congrArg f (mem_filter.mp hi).2)

private theorem kernel_by_bins (c : I → J) (a : I → ℝ) (K : J → J → ℝ) :
    ∑ i, ∑ l, a i*a l*K (c i) (c l)=∑ u, ∑ v, fiberMass c a u*fiberMass c a v*K u v := by
  let m := fiberMass c a
  calc _ = ∑ i, a i*(∑ l, a l*K (c i) (c l)) := by simp only [mul_sum,mul_assoc]
       _ = ∑ i, a i*(∑ v, m v*K (c i) v) := by
         apply sum_congr rfl
         exact fun i _ => congrArg (a i * ·) (sum_by_bins c a (K (c i)))
       _ = ∑ u, m u*(∑ v, m v*K u v) := sum_by_bins c a (fun u => ∑ v, m v*K u v)
       _ = _ := by simp only [m,mul_sum,mul_assoc]

private theorem forward_bin_kernel {x y : ℝ} (h : ⌊x⌋ ≤ ⌊y⌋) :
    exp (-(x-y)^2/2) ≤ 4*(1/2:ℝ)^(⌊x⌋-⌊y⌋).natAbs := by
  have hz : ⌊x-y⌋ ≤ ⌊x⌋-⌊y⌋ := by
    apply Int.lt_add_one_iff.mp
    apply Int.floor_lt.mpr
    push_cast
    linarith only [Int.lt_floor_add_one x,Int.floor_le y]
  have hab : |⌊x⌋-⌊y⌋| ≤ |⌊x-y⌋| := by
    rw [abs_of_nonpos (sub_nonpos.mpr h),abs_of_nonpos (hz.trans (sub_nonpos.mpr h))]
    exact neg_le_neg hz
  have hn : (⌊x⌋-⌊y⌋).natAbs ≤ ⌊x-y⌋.natAbs := by
    exact_mod_cast (show ((⌊x⌋-⌊y⌋).natAbs:ℤ) ≤ (⌊x-y⌋.natAbs:ℤ) by
      simpa only [Int.natCast_natAbs] using hab)
  exact (gaussian_floor_weight _).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn) (by norm_num))

private theorem bin_kernel (x y : ℝ) :
    exp (-(x-y)^2/2) ≤ 4*(1/2:ℝ)^(⌊x⌋-⌊y⌋).natAbs := by
  rcases le_total ⌊x⌋ ⌊y⌋ with h|h
  · exact forward_bin_kernel h
  · rw [sub_sq_comm x y,Int.natAbs_sub_comm]
    exact forward_bin_kernel h

private abbrev Bins (F : I → ℝ) := ↥(univ.image (fun i => ⌊F i⌋))
private def binOf (F : I → ℝ) (i : I) : Bins F := ⟨_,mem_image_of_mem _ (mem_univ i)⟩

/-- Sum of squared total amplitudes in the occupied unit intervals. -/
def binCollision (F a : I → ℝ) := ∑ j : Bins F, (fiberMass (binOf F) a j)^2

/-- The Gaussian moment lies between two universal multiples of the
binned collision mass, with no separation or multiplicity assumption. -/
theorem gaussian_energy_bins (F a : I → ℝ) (ha : ∀ i, 0 ≤ a i) :
    let Q := ∑ i, ∑ l, a i*a l*exp (-(F i-F l)^2/2)
    exp (-1/2)*binCollision F a ≤ Q ∧ Q ≤ 12*binCollision F a := by
  classical
  intro Q
  let c := binOf F
  let m := fiberMass c a
  have hm (j : Bins F) : 0 ≤ m j := sum_nonneg fun i _ => ha i
  let lo (u v : Bins F) : ℝ := if u=v then exp (-1/2) else 0
  let hi (u v : Bins F) : ℝ := 4*(1/2:ℝ)^(u.val-v.val).natAbs
  have hl (i l : I) : lo (c i) (c l) ≤ exp (-(F i-F l)^2/2) := by
    unfold lo
    split_ifs with h
    · have he : (⌊F i⌋:ℝ)=(⌊F l⌋:ℝ) := congrArg (fun j : Bins F => (j.val:ℝ)) h
      have hd : |F i-F l| ≤ 1 := abs_le.mpr
        ⟨by linarith only [he,Int.floor_le (F i),Int.lt_floor_add_one (F l)],
         by linarith only [he,Int.floor_le (F l),Int.lt_floor_add_one (F i)]⟩
      apply exp_le_exp.mpr
      have hs := pow_le_pow_left₀ (abs_nonneg _) hd 2
      rw [sq_abs,one_pow] at hs
      linarith only [hs]
    · exact (exp_pos _).le
  constructor
  · calc _ = ∑ u : Bins F, ∑ v : Bins F, m u*m v*lo u v := by
           rw [binCollision,mul_sum]
           apply sum_congr rfl
           intro u _
           rw [sum_eq_single u]
           · simp only [lo,if_pos rfl,m,fiberMass,pow_two,c]; ring
           · intro v _ hne
             simp [lo,Ne.symm hne]
           · simp
         _ = _ := (kernel_by_bins c a lo).symm
         _ ≤ Q := sum_le_sum fun i _ => sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hl i l)
           (mul_nonneg (ha i) (ha l))
  · have hrow (u : Bins F) : ∑ v, hi u v ≤ 12 := by
      let code (v : Bins F) := u.val-v.val
      have hinj : Function.Injective code := by
        intro v w h
        change u.val-v.val=u.val-w.val at h
        exact Subtype.ext (by omega)
      let d (z : ℤ) := (1/2:ℝ)^z.natAbs
      have hd : ∑ v, d (code v) ≤ 3 := by
        rw [←Finset.sum_image hinj.injOn]
        exact (dyadic_integer_sum.summable.sum_le_tsum _ (fun _ _ => pow_nonneg (by norm_num) _)).trans_eq
          dyadic_integer_sum.tsum_eq
      change ∑ v, 4*d (code v) ≤ 12
      rw [←mul_sum]
      linarith only [hd]
    have hSchur := weighted_double_sum_le_rowBound (b:=m) (K:=hi)
      (fun u v => by simp only [hi,Int.natAbs_sub_comm u.val v.val])
      (fun u v => by dsimp only [hi]; positivity) hrow
    simp only [abs_of_nonneg (hm _)] at hSchur
    calc Q ≤ ∑ i, ∑ l, a i*a l*hi (c i) (c l) := sum_le_sum fun i _ => sum_le_sum fun l _ =>
           mul_le_mul_of_nonneg_left (bin_kernel _ _) (mul_nonneg (ha i) (ha l))
         _ = _ := kernel_by_bins c a hi
         _ ≤ _ := hSchur

#print axioms gaussian_energy_bins
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
