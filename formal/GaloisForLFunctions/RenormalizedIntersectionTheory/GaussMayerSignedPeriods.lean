import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerSourceParameterHolomorphy

/-!
# Period relations of all signed Mayer solutions

The actual branch differences telescope even when the branch series itself
diverges. Constant forcing disappears from this identity. Every solution of
`L_w f - ε f = constant`, with `ε² = 1`, therefore has signed inversion parity
and satisfies the Lewis three-term relation on the real disc segment.
-/

open Complex Set Filter Metric Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerParameter
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerSignedPeriods

/-- The period coordinate of an actual disc-algebra function. -/
def period (f : DiscSpace) (a : ℝ) : ℂ := plane f ((a : ℂ)-1)

private theorem point_mem {a : ℝ} (ha : a ∈ Icc (1/2 : ℝ) (7/2)) :
    (a : ℂ)-1 ∈ outer := by
  have he : ((a : ℂ)-1)-1=((a-2 : ℝ) : ℂ) := by push_cast; ring
  rw [outer,mem_closedBall,dist_eq_norm,he,Complex.norm_real,Real.norm_eq_abs,abs_le]
  constructor <;> linarith only [ha.1,ha.2]

private theorem branch_tendsto_zero {w : ℂ} (hw : 0 < w.re)
    (f : DiscSpace) (z : Disc) :
    Tendsto (fun n : ℕ => evaluation z (branch w hw (n+1) (Nat.succ_pos n) f))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hp : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)^(-w.re)) atTop (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_atTop_mono (fun n => by exact_mod_cast Nat.le_succ n)
        tendsto_natCast_atTop_atTop
    exact (tendsto_rpow_neg_atTop hw).comp hn
  have ht := (hp.const_mul (powerBound w)).mul_const ‖f‖
  simp only [mul_zero,zero_mul] at ht
  apply squeeze_zero (fun _ => norm_nonneg _) _ ht
  intro n
  exact (ContinuousMap.norm_coe_le_norm (branch w hw (n+1) (Nat.succ_pos n) f).1 z).trans
    ((ContinuousLinearMap.le_opNorm _ f).trans
      (mul_le_mul_of_nonneg_right (norm_branch_le hw (Nat.succ_pos n)) (norm_nonneg f)))

/-- Adjacent evaluations of the actual operator differ by exactly its first branch. -/
theorem operator_shift {w : ℂ} (hw : 0 < w.re) (f : DiscSpace)
    (z z' : Disc) (hzz : z'.1=z.1+1) :
    evaluation z (regularized w hw f)-evaluation z' (regularized w hw f)=
      (1+z.1)^(-w)*plane f ((1+z.1)⁻¹) := by
  let B : ℕ → ℂ := fun n => evaluation z (branch w hw (n+1) (Nat.succ_pos n) f)
  have hshift (n : ℕ) :
      evaluation z' (branch w hw (n+1) (Nat.succ_pos n) f)=B (n+1) := by
    simp only [B,evaluation_apply,branch_apply,hzz]
    congr 2 <;> push_cast <;> ring
  let E : DiscSpace →L[ℂ] ℂ := evaluation z-evaluation z'
  have hs := (E.comp (ContinuousLinearMap.apply ℂ DiscSpace f)).hasSum
    (remainder_locallyUniform.summable hw).hasSum
  change HasSum (fun n => E (entireRemainder n w f)) (E (remainder w f)) at hs
  have he (n : ℕ) : E (entireRemainder n w f)=B n-B (n+1) := by
    rw [entireRemainder_eq hw,branchRemainder]
    change (evaluation z (branch w hw (n+1) (Nat.succ_pos n) f)-
      ((n+1 : ℕ) : ℂ)^(-w)*f.1 zeroPoint)-
      (evaluation z' (branch w hw (n+1) (Nat.succ_pos n) f)-
      ((n+1 : ℕ) : ℂ)^(-w)*f.1 zeroPoint)=B n-B (n+1)
    rw [hshift]
    change (B n-_)-(B (n+1)-_)=_
    ring
  have hs' : HasSum (fun n => B n-B (n+1)) (E (remainder w f)) := by
    simpa only [he] using hs
  have hfinite (N : ℕ) : (∑ n ∈ Finset.range N, (B n-B (n+1)))=B 0-B N := by
    induction N with
    | zero => simp only [Finset.range_zero,Finset.sum_empty,sub_self]
    | succ N ih => rw [Finset.sum_range_succ,ih]; ring
  have hlim : Tendsto (fun N => B 0-B N) atTop (𝓝 (B 0)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub (branch_tendsto_zero hw f z)
  have hrem : E (remainder w f)=B 0 :=
    tendsto_nhds_unique (by simpa only [hfinite] using hs'.tendsto_sum_nat) hlim
  rw [← source_eq hw,source]
  change (riemannZeta w*f.1 zeroPoint+evaluation z (remainder w f))-
    (riemannZeta w*f.1 zeroPoint+evaluation z' (remainder w f))=_
  change evaluation z (remainder w f)-evaluation z' (remainder w f)=B 0 at hrem
  have hfirst : B 0=(1+z.1)^(-w)*plane f ((1+z.1)⁻¹) := by
    simp only [B,evaluation_apply,branch_apply,Nat.zero_add,Nat.cast_one]
  rw [← hfirst]
  linear_combination hrem

private theorem shift_points {a : ℝ} (ha : a ∈ Icc (1/2 : ℝ) (5/2)) :
    a ∈ Icc (1/2 : ℝ) (7/2) ∧ a+1 ∈ Icc (1/2 : ℝ) (7/2) := by
  constructor <;> constructor <;> linarith only [ha.1,ha.2]

/-- The signed renewal identity holds for every actual constant-forced solution. -/
theorem period_shift {w ε c : ℂ} (hw : 0 < w.re) (hε : ε^2=1)
    (f : DiscSpace) (hf : regularized w hw f=ε • f+constant c)
    {a : ℝ} (ha : a ∈ Icc (1/2 : ℝ) (5/2)) :
    period f a=period f (a+1)+ε*(a : ℂ)^(-w)*plane f ((a : ℂ)⁻¹) := by
  let z : Disc := ⟨(a : ℂ)-1,point_mem (shift_points ha).1⟩
  let z' : Disc := ⟨((a+1 : ℝ) : ℂ)-1,point_mem (shift_points ha).2⟩
  have hzz : z'.1=z.1+1 := by dsimp [z,z']; push_cast; ring
  have ht := operator_shift hw f z z' hzz
  rw [hf,map_add,map_add,map_smul,map_smul] at ht
  have hza : 1+z.1=(a : ℂ) := by dsimp [z]; ring
  rw [hza] at ht
  simp only [smul_eq_mul] at ht
  rw [show evaluation z f=period f a from (plane_eq f z).symm,
    show evaluation z' f=period f (a+1) from (plane_eq f z').symm] at ht
  change (ε*period f a+c)-(ε*period f (a+1)+c)=
    (a : ℂ)^(-w)*plane f ((a : ℂ)⁻¹) at ht
  linear_combination ε*ht-(period f a-period f (a+1))*hε

private theorem reciprocal_points {a : ℝ} (ha : a ∈ Icc (1/2 : ℝ) 2) :
    1/a ∈ Icc (1/2 : ℝ) 2 := by
  have hp : 0<a := by linarith only [ha.1]
  constructor
  · exact (le_div_iff₀ hp).mpr (by linarith only [ha.2])
  · exact (div_le_iff₀ hp).mpr (by linarith only [ha.1])

private theorem reciprocal_power {a : ℝ} (ha : 0<a) (w : ℂ) :
    (a : ℂ)^(-w)*((1/a : ℝ) : ℂ)^(-w)=1 := by
  rw [← Complex.mul_cpow_ofReal_nonneg ha.le (one_div_pos.mpr ha).le,
    ← Complex.ofReal_mul,mul_one_div_cancel ha.ne',Complex.ofReal_one,Complex.one_cpow]

/-- Every signed Mayer eigenfunction has its corresponding inversion parity.
The same holds with arbitrary constant forcing. -/
theorem reciprocity {w ε c : ℂ} (hw : 0 < w.re) (hε : ε^2=1)
    (f : DiscSpace) (hf : regularized w hw f=ε • f+constant c)
    {a : ℝ} (ha : a ∈ Icc (1/2 : ℝ) 2) :
    period f a=ε*(a : ℂ)^(-w)*period f (1/a) := by
  have hi := reciprocal_points ha
  have hp : 0<a := by linarith only [ha.1]
  have ht := period_shift hw hε f hf (a := a) ⟨ha.1,by linarith only [ha.2]⟩
  have ht' := period_shift hw hε f hf (a := 1/a) ⟨hi.1,by linarith only [hi.2]⟩
  have he : plane f ((a : ℂ)⁻¹)=period f (1/a+1) := by
    unfold period
    congr 1
    push_cast
    ring
  have he' : plane f (((1/a : ℝ) : ℂ)⁻¹)=period f (a+1) := by
    unfold period
    congr 1
    push_cast
    field_simp
    ring
  rw [he] at ht
  rw [he'] at ht'
  have hm := reciprocal_power hp w
  linear_combination ht-ε*(a : ℂ)^(-w)*ht'-
    period f (a+1)*(ε^2*hm+hε)

/-- Every actual signed solution with constant forcing satisfies the Lewis relation. -/
theorem three_term {w ε c : ℂ} (hw : 0 < w.re) (hε : ε^2=1)
    (f : DiscSpace) (hf : regularized w hw f=ε • f+constant c)
    {a : ℝ} (ha : a ∈ Icc (1 : ℝ) 2) :
    period f a=period f (a+1)+((a+1 : ℝ) : ℂ)^(-w)*period f (a/(a+1)) := by
  have hp : 0<a := lt_of_lt_of_le zero_lt_one ha.1
  have hi0 : 0<1+1/a := add_pos zero_lt_one (one_div_pos.mpr hp)
  have hi : 1+1/a ∈ Icc (1/2 : ℝ) 2 := by
    have hb : 1/a≤1 := (div_le_iff₀ hp).mpr (by linarith only [ha.1])
    constructor <;> linarith only [one_div_pos.mpr hp,hb]
  have he : plane f ((a : ℂ)⁻¹)=period f (1+1/a) := by
    unfold period
    congr 1
    push_cast
    ring
  have hr : 1/(1+1/a)=a/(a+1) := by
    field_simp [hp.ne',ne_of_gt (by linarith only [hp] : 0<a+1)]
  have hm : a*(1+1/a)=a+1 := by field_simp [hp.ne']
  rw [period_shift hw hε f hf ⟨by linarith only [ha.1],by linarith only [ha.2]⟩,
    he,reciprocity hw hε f hf hi,hr]
  have hc : (a : ℂ)^(-w)*((1+1/a : ℝ) : ℂ)^(-w)=((a+1 : ℝ) : ℂ)^(-w) := by
    rw [← Complex.mul_cpow_ofReal_nonneg hp.le hi0.le,← Complex.ofReal_mul,hm]
  linear_combination period f (a/(a+1))*(ε^2*hc+((a+1 : ℝ) : ℂ)^(-w)*hε)

/-- Every negative-signed constant-forced solution is invisible to evaluation at zero,
including all actual negative-unit eigenvectors at complex source parameters. -/
theorem negative_solution_zero_at_origin {w c : ℂ} (hw : 0 < w.re)
    (f : DiscSpace) (hf : regularized w hw f=-f+constant c) :
    evaluation zeroPoint f=0 := by
  have he : regularized w hw f=(-1 : ℂ) • f+constant c := by
    simpa only [neg_one_smul] using hf
  have h := period_shift hw (by norm_num : (-1 : ℂ)^2=1) f he
    (a := 1) (by constructor <;> norm_num)
  norm_num [period] at h
  change f.1 zeroPoint=0
  rw [← plane_eq f zeroPoint]
  exact h

#print axioms negative_solution_zero_at_origin

/-- The negative resolvent boundary value is fixed by two source evaluations,
for every actual solution, including at parameters where the inverse is singular. -/
theorem negative_forced_boundary {w : ℂ} (hw : 0 < w.re) (f g : DiscSpace)
    (hf : regularized w hw f+f=g) :
    plane f 0=plane g 0-plane g 1 := by
  let z : Disc := ⟨1,by norm_num [outer,mem_closedBall]⟩
  have ht := operator_shift hw f zeroPoint z (by simp only [z,zeroPoint,zero_add])
  change evaluation zeroPoint (regularized w hw f)-evaluation z (regularized w hw f)=
    (1+0 : ℂ)^(-w)*plane f ((1+0 : ℂ)⁻¹) at ht
  simp only [add_zero,one_cpow,inv_one,one_mul] at ht
  rw [plane_eq f z] at ht
  change evaluation zeroPoint (regularized w hw f)-evaluation z (regularized w hw f)=
    evaluation z f at ht
  have h0 := congrArg (evaluation zeroPoint) hf
  have h1 := congrArg (evaluation z) hf
  rw [map_add] at h0 h1
  change plane f (zeroPoint : ℂ)=plane g (zeroPoint : ℂ)-plane g (z : ℂ)
  rw [plane_eq f zeroPoint,plane_eq g zeroPoint,plane_eq g z]
  change evaluation zeroPoint f=evaluation zeroPoint g-evaluation z g
  linear_combination h0-h1-ht

#print axioms negative_forced_boundary

#print axioms operator_shift
#print axioms period_shift
#print axioms reciprocity
#print axioms three_term

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerSignedPeriods
