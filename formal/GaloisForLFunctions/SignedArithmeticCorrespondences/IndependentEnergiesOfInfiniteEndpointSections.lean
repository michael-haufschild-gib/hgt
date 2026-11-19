import GaloisForLFunctions.SignedArithmeticCorrespondences.ThePoleDefectOfFullIntegralPrefixes
import GaloisForLFunctions.SignedArithmeticCorrespondences.OppositeSectionsOfTheIntegralGraphGauge
import GaloisForLFunctions.RHTower.CausalMobiusThetaSmoothGauge

/-!
# Infinite endpoint intersections from the two divisors' own energies

The ordinary-prime curvature and the real-place metric have summable rows.
This controls both double series absolutely on all square-summable endpoint
sequences, including sections whose generating functions diverge at one.
-/

noncomputable section
namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open Finset MeasureTheory Filter Topology _root_.RHTower

/-- Sum of absolute mixed intersections of two endpoint sections. -/
def absoluteIntersection (A u v : ℕ → ℝ) : ℝ :=
  ∑' p : ℕ × ℕ, |u p.1*v p.2*A (p.1+p.2)|

private def cell (n : ℕ+) (j : ℕ) : ℝ := 1/(((n:ℝ)+j)*((n:ℝ)+j+1))

private def outer (f g : ℕ → ℝ) (p : ℕ × ℕ) : ℝ := f p.1*g p.2

private theorem outer_series (f g : ℕ → ℝ) (hf : Summable f) (hg : Summable g) :
    Summable (outer f g) ∧ (∑' p, outer f g p) = (∑' i, f i)*(∑' j, g j) :=
  ⟨summable_mul_of_summable_norm (f := f) (g := g) hf.norm hg.norm,
   (tsum_mul_tsum_of_summable_norm (f := f) (g := g) hf.norm hg.norm).symm⟩

/-- Charge each half of a mixed entry to the row of one of its two sections. -/
private theorem mixed_entry_price (u v z C a b : ℝ) (hz₁ : |z| ≤ C*a) (hz₂ : |z| ≤ C*b) :
    |u*v*z| ≤ (C/2)*(u^2*a+b*v^2) := by
  have hprod : |u| * |v| ≤ (u^2+v^2)/2 := by
    nlinarith only [sq_nonneg (|u| - |v|),sq_abs u,sq_abs v]
  rw [abs_mul,abs_mul]
  calc _ ≤ ((u^2+v^2)/2)*|z| := mul_le_mul_of_nonneg_right hprod (abs_nonneg z)
       _ = (u^2 * |z| + |z| * v^2)/2 := by ring
       _ ≤ (u^2*(C*a)+(C*b)*v^2)/2 :=
         div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left hz₁ (sq_nonneg u))
           (mul_le_mul_of_nonneg_right hz₂ (sq_nonneg v))) (by norm_num)
       _ = _ := by ring

/-- A summable row majorant prices an infinite Hankel intersection by the
two individual square energies. Each row is charged before gluing. -/
theorem absoluteIntersection_le_row_sum {A B : ℕ → ℝ} {C : ℝ} (hB : Summable B)
    (hA : ∀ j k : ℕ, j≤k → |A k| ≤ C*B j)
    (u v : ℕ → ℝ) (hu : Summable (fun i => u i^2)) (hv : Summable (fun j => v j^2)) :
    Summable (fun p : ℕ × ℕ => |u p.1*v p.2*A (p.1+p.2)|) ∧
      absoluteIntersection A u v ≤ (C/2)*((∑' i, u i^2)+(∑' j, v j^2))*(∑' j, B j) := by
  let M (p : ℕ × ℕ) := (C/2)*(u p.1^2*B p.2+B p.1*v p.2^2)
  have hdom (p : ℕ × ℕ) : |u p.1*v p.2*A (p.1+p.2)| ≤ M p :=
    mixed_entry_price (u p.1) (v p.2) (A (p.1+p.2)) C (B p.2) (B p.1)
      (hA p.2 (p.1+p.2) (Nat.le_add_left ..)) (hA p.1 (p.1+p.2) (Nat.le_add_right ..))
  obtain ⟨h₁,e₁⟩ := outer_series (fun i => u i^2) B hu hB
  obtain ⟨h₂,e₂⟩ := outer_series B (fun j => v j^2) hB hv
  have ht : Summable M := (h₁.add h₂).mul_left (C/2)
  have hs := Summable.of_nonneg_of_le (fun p : ℕ × ℕ => abs_nonneg (u p.1*v p.2*A (p.1+p.2))) hdom ht
  refine ⟨hs,(hs.tsum_le_tsum hdom ht).trans_eq ?_⟩
  change (∑' p, (C/2)*(outer (fun i => u i^2) B p+outer B (fun j => v j^2) p)) = _
  rw [tsum_mul_left,h₁.tsum_add h₂,e₁,e₂]
  ring

private theorem energy_bound (n : ℕ+) {A : ℕ → ℝ} {C : ℝ} (hC : 0≤C)
    (hA : ∀ j k : ℕ, j≤k → |A k| ≤ C*cell n j)
    (u v : ℕ → ℝ) (hu : Summable (fun i => u i^2)) (hv : Summable (fun j => v j^2)) :
    Summable (fun p : ℕ × ℕ => |u p.1*v p.2*A (p.1+p.2)|) ∧
      absoluteIntersection A u v ≤ C/(2*(n:ℝ))*((∑' i, u i^2)+(∑' j, v j^2)) := by
  obtain ⟨ht,hcell⟩ := telescoping_cell_le n n.pos
  have h := absoluteIntersection_le_row_sum (B := cell n) ht hA u v hu hv
  refine ⟨h.1,h.2.trans ?_⟩
  calc _ ≤ C/2*((∑' i, u i^2)+(∑' j, v j^2))*(1/(n:ℝ)) :=
         mul_le_mul_of_nonneg_left hcell (mul_nonneg (by positivity)
           (add_nonneg (tsum_nonneg fun i => sq_nonneg (u i)) (tsum_nonneg fun j => sq_nonneg (v j))))
       _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev]; ring

#print axioms absoluteIntersection_le_row_sum

/-- Degree-n block curvature on actual integral graphs, shifted by k. -/
def shiftedBlockCurvature (d n : ℕ+) (k : ℕ) : ℝ :=
  blockHeight d ((n:ℕ)+k+2)-2*blockHeight d ((n:ℕ)+k+1)+blockHeight d ((n:ℕ)+k)

/-- Both sections may have infinite support. The cost is their individual
square energy times d²/(n(n+1)); it tends to zero for d=o(n). -/
theorem infinite_block_energy (d n : ℕ+) (u v : ℕ → ℝ)
    (hu : Summable (fun i => u i^2)) (hv : Summable (fun i => v i^2)) :
    Summable (fun p : ℕ × ℕ => |u p.1*v p.2*shiftedBlockCurvature d n (p.1+p.2)|) ∧
      absoluteIntersection (shiftedBlockCurvature d n) u v ≤
        (d:ℝ)^2/((n:ℝ)*((n:ℝ)+1))*((∑' i, u i^2)+(∑' j, v j^2)) := by
  have hn : 0 < (n:ℝ) := Nat.cast_pos.mpr n.pos
  let C := 2*(d:ℝ)^2/((n:ℝ)+1)
  have hA (j k : ℕ) (hjk : j ≤ k) : |shiftedBlockCurvature d n k| ≤ C*cell n j := by
    have h := block_curvature_bounds d ((n:ℕ)+k) (n.pos.trans_le (Nat.le_add_right _ _))
    change 0 ≤ shiftedBlockCurvature d n k ∧ shiftedBlockCurvature d n k ≤ _ at h
    rw [abs_of_nonneg h.1]
    refine h.2.trans ?_
    rw [Nat.cast_add]
    have hjk' : (j:ℝ) ≤ k := by exact_mod_cast hjk
    change 2*(d:ℝ)^2/((n:ℝ)+k+1)^3 ≤ C*cell n j
    dsimp only [C,cell]
    rw [div_mul_div_comm,mul_one]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have h₁ : (n:ℝ)+1 ≤ (n:ℝ)+k+1 := by linarith only [Nat.cast_nonneg (α := ℝ) k]
    have h₂ : (n:ℝ)+j ≤ (n:ℝ)+k+1 := by linarith only [hjk']
    have h₃ : (n:ℝ)+j+1 ≤ (n:ℝ)+k+1 := by linarith only [hjk']
    calc _ ≤ ((n:ℝ)+k+1)*(((n:ℝ)+k+1)*((n:ℝ)+k+1)) :=
           mul_le_mul h₁ (mul_le_mul h₂ h₃ (by positivity) (by positivity)) (by positivity) (by positivity)
         _ = _ := by ring
  have h := energy_bound n (by dsimp [C]; positivity) hA u v hu hv
  have hc : C/(2*(n:ℝ)) = (d:ℝ)^2/((n:ℝ)*((n:ℝ)+1)) := by
    dsimp only [C]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rwa [hc] at h

private theorem real_endpoint_bounds (d : ℕ+) (k : ℕ) :
    0 ≤ 2*realEndpoint d k ∧ 2*realEndpoint d k ≤ (d:ℝ)^2/(((k:ℝ)+1)*((k:ℝ)+2)) := by
  rw [realEndpoint_moment _ _ d.pos]
  have hs (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) : (∑ a ∈ range (d:ℕ), x^a)^2 ≤ (d:ℝ)^2 := by
    have h : (∑ a ∈ range (d:ℕ), x^a) ≤ (d:ℝ) := by
      simpa using sum_le_sum (s := range (d:ℕ)) fun a _ => pow_le_one₀ hx.1 hx.2 (n := a)
    exact pow_le_pow_left₀ (sum_nonneg fun a _ => pow_nonneg hx.1 a) h _
  constructor
  · exact intervalIntegral.integral_nonneg zero_le_one fun x hx =>
      mul_nonneg (mul_nonneg (pow_nonneg hx.1 _) (sub_nonneg.mpr hx.2)) (sq_nonneg _)
  calc _ ≤ ∫ x in (0:ℝ)..1, x^k*(1-x)*(d:ℝ)^2 := by
         apply intervalIntegral.integral_mono_on zero_le_one
           (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)
         intro x hx
         exact mul_le_mul_of_nonneg_left (hs x hx) (mul_nonneg (pow_nonneg hx.1 _) (sub_nonneg.mpr hx.2))
       _ = _ := by rw [intervalIntegral.integral_mul_const,sectionMass]; ring

/-- The same square energies control the full double series of metric
corrections at the real place, with its own separation loss d²/(2n). -/
theorem infinite_real_energy (d n : ℕ+) (u v : ℕ → ℝ)
    (hu : Summable (fun i => u i^2)) (hv : Summable (fun i => v i^2)) :
    let A := fun k : ℕ => 2*realEndpoint d ((n:ℕ)+k)
    Summable (fun p : ℕ × ℕ => |u p.1*v p.2*A (p.1+p.2)|) ∧
      absoluteIntersection A u v ≤ (d:ℝ)^2/(2*(n:ℝ))*((∑' i, u i^2)+(∑' j, v j^2)) := by
  intro A
  apply energy_bound n (sq_nonneg _) _ u v hu hv
  intro j k hjk
  have hn : 0 < (n:ℝ) := Nat.cast_pos.mpr n.pos
  have hjk' : (j:ℝ) ≤ k := by exact_mod_cast hjk
  have h := real_endpoint_bounds d ((n:ℕ)+k)
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  rw [Nat.cast_add,cell,mul_one_div]
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  exact mul_le_mul (by linarith only [hjk']) (by linarith only [hjk']) (by positivity) (by positivity)

/-- Round a section towards zero at multiplicity N+1. This preserves both
sign and the individual absolute majorant, also for arbitrarily small jumps. -/
def roundedJump (N : ℕ) (x : ℝ) : ℤ :=
  if x<0 then -(⌊((N:ℝ)+1)*|x|⌋₊ : ℤ) else (⌊((N:ℝ)+1)*|x|⌋₊ : ℤ)

private theorem rounded_bounds (N : ℕ) (x : ℝ) :
    let y := (roundedJump N x:ℝ)/((N:ℝ)+1)
    |y| ≤ |x| ∧ |y-x| ≤ 1/((N:ℝ)+1) := by
  intro y
  let s := (N:ℝ)+1
  let k := ⌊s*|x|⌋₊
  let a := (k:ℝ)/s
  have hs : 0<s := by dsimp [s]; positivity
  have ha : 0≤a := div_nonneg (Nat.cast_nonneg _) hs.le
  have hk₀ : (k:ℝ) ≤ s*|x| := Nat.floor_le (mul_nonneg hs.le (abs_nonneg x))
  have hk₁ : s*|x| < (k:ℝ)+1 := Nat.lt_floor_add_one _
  have he : a≤|x| := (div_le_iff₀ hs).mpr ((mul_comm s |x|) ▸ hk₀)
  have hd : |x| - a ≤ 1/s := by
    change |x| - (k:ℝ)/s ≤ 1/s
    rw [show |x| - (k:ℝ)/s=(s*|x| - k)/s by field_simp]
    exact div_le_div_of_nonneg_right (by linarith only [hk₁]) hs.le
  by_cases hx : x<0
  · have hy : y = -a := by simp only [y,roundedJump,if_pos hx,Int.cast_neg,Int.cast_natCast,neg_div,a,k,s]
    rw [hy,abs_neg,abs_of_nonneg ha]
    refine ⟨he,?_⟩
    rwa [show -a-x = |x| - a by rw [abs_of_neg hx]; ring,abs_of_nonneg (sub_nonneg.mpr he)]
  · have hy : y = a := by simp only [y,roundedJump,if_neg hx,Int.cast_natCast,a,k,s]
    rw [hy,abs_of_nonneg ha]
    refine ⟨he,?_⟩
    rw [abs_of_nonneg (le_of_not_gt hx)] at he hd
    rwa [abs_of_nonpos (sub_nonpos.mpr he),neg_sub]

/-- Finite endpoint intersection of actual integer multiplicities, divided
by their two common scales. The lower and upper supports exhaust together. -/
def roundedIntersection (N : ℕ) (A u v : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range N, ∑ j ∈ range N, ((roundedJump N (u i):ℝ)/((N:ℝ)+1))*
    ((roundedJump N (v j):ℝ)/((N:ℝ)+1))*A (i+j)

private def roundedSection (N : ℕ) (u : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i<N then (roundedJump N (u i):ℝ)/((N:ℝ)+1) else 0

private theorem rounded_limit (u : ℕ → ℝ) (i : ℕ) :
    Tendsto (fun N => roundedSection N u i) atTop (𝓝 (u i)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _ tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [eventually_gt_atTop i] with N hi
  simpa only [Real.dist_eq,roundedSection,if_pos hi] using (rounded_bounds N (u i)).2

/-- Absolute summability lets the same rounded integral endpoints exhaust the mixed kernel. -/
theorem roundedIntersection_tendsto (A u v : ℕ → ℝ)
    (h : Summable (fun p : ℕ × ℕ => |u p.1*v p.2*A (p.1+p.2)|)) :
    Tendsto (fun N => roundedIntersection N A u v) atTop (𝓝 (∑' p : ℕ × ℕ, u p.1*v p.2*A (p.1+p.2))) := by
  let F (N : ℕ) (p : ℕ × ℕ) := roundedSection N u p.1*roundedSection N v p.2*A (p.1+p.2)
  have hlim (p : ℕ × ℕ) : Tendsto (fun N => F N p) atTop (𝓝 (u p.1*v p.2*A (p.1+p.2))) :=
    ((rounded_limit u _).mul (rounded_limit v _)).mul_const _
  have hb (N : ℕ) (w : ℕ → ℝ) (i : ℕ) : |roundedSection N w i| ≤ |w i| := by
    by_cases hi : i<N
    · simpa only [roundedSection,if_pos hi] using (rounded_bounds N (w i)).1
    · simpa only [roundedSection,if_neg hi,abs_zero] using abs_nonneg (w i)
  have hdom (N : ℕ) (p : ℕ × ℕ) : ‖F N p‖ ≤ |u p.1*v p.2*A (p.1+p.2)| := by
    simp only [F,Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hb N u _) (hb N v _) (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  have ht := tendsto_tsum_of_dominated_convergence h hlim (Eventually.of_forall hdom)
  apply ht.congr
  intro N
  change (∑' p, F N p) = roundedIntersection N A u v
  rw [tsum_eq_sum (s := (range N)×ˢ(range N)) (fun p hp => by
    by_cases h₁ : p.1<N
    · have h₂ : ¬p.2<N := fun h₂ => hp (mem_product.mpr ⟨mem_range.mpr h₁,mem_range.mpr h₂⟩)
      simp [F,roundedSection,h₂]
    · simp [F,roundedSection,h₁]),sum_product]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  simp only [F,roundedSection,if_pos (mem_range.mp hi),if_pos (mem_range.mp hj)]

/-- Every square-summable pair is realized at both places by the same
sequence of scaled integral divisors. This also covers sections with no
bounded continuous generating function. -/
theorem integral_sections_realize_both_completions (d n : ℕ+) (u v : ℕ → ℝ)
    (hu : Summable (fun i => u i^2)) (hv : Summable (fun i => v i^2)) :
    let K := shiftedBlockCurvature d n
    let D := fun k : ℕ => 2*realEndpoint d ((n:ℕ)+k)
    Tendsto (fun N => roundedIntersection N K u v) atTop (𝓝 (∑' p : ℕ × ℕ,u p.1*v p.2*K (p.1+p.2))) ∧
    Tendsto (fun N => roundedIntersection N D u v) atTop (𝓝 (∑' p : ℕ × ℕ,u p.1*v p.2*D (p.1+p.2))) := by
  exact ⟨roundedIntersection_tendsto _ u v (infinite_block_energy d n u v hu hv).1,
    roundedIntersection_tendsto _ u v (infinite_real_energy d n u v hu hv).1⟩

/-- The two effective square forms survive completion for every real
square-summable endpoint sequence, through the same integral approximants. -/
theorem completed_squares_effective (d n : ℕ+) (u : ℕ → ℝ) (hu : Summable (fun i => u i^2)) :
    (0 ≤ ∑' p : ℕ × ℕ,u p.1*u p.2*shiftedBlockCurvature d n (p.1+p.2)) ∧
      (0 ≤ ∑' p : ℕ × ℕ,u p.1*u p.2*(2*realEndpoint d ((n:ℕ)+(p.1+p.2)))) := by
  have ht := integral_sections_realize_both_completions d n u u hu hu
  constructor
  · apply ge_of_tendsto ht.1
    apply Eventually.of_forall
    intro N
    let w (i : ℕ) := (roundedJump N (u i):ℝ)/((N:ℝ)+1)
    have he := sectionIntersection_square_nonneg d n (endpointPolynomial (range N) w)
    rw [sectionIntersection_gluing] at he
    simpa only [roundedIntersection,shiftedBlockCurvature,w,Nat.add_assoc] using he
  · apply ge_of_tendsto ht.2
    apply Eventually.of_forall
    intro N
    let w (i : ℕ) := (roundedJump N (u i):ℝ)/((N:ℝ)+1)
    have he := realEndpoint_hankel_nonneg d n d.pos (range N) w
    have h : roundedIntersection N (fun k => 2*realEndpoint d ((n:ℕ)+k)) u u =
        2*∑ i ∈ range N, ∑ j ∈ range N, w i*w j*realEndpoint d ((n:ℕ)+i+j) := by
      simp only [roundedIntersection,mul_sum,Nat.add_assoc]
      exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by dsimp only [w]; ring
    rw [h]
    exact mul_nonneg (by norm_num) he

#print axioms infinite_block_energy
#print axioms infinite_real_energy
#print axioms integral_sections_realize_both_completions
#print axioms completed_squares_effective

/-- The mixed, pole-subtracted ordinary prefix extends to every pair of
square-summable sections through actual scaled integer multiplicities.
The separate real Weil energies control its signed value. The sum of the
absolute entries decays at rate 1/n for bounded individual square energies. -/
theorem infinite_pole_defect_from_integral_divisors (n : ℕ+) (u v : ℕ → ℝ)
    (hu : Summable (fun i => u i^2)) (hv : Summable (fun i => v i^2)) :
    let G := fun k : ℕ => prefixDefectCurvature ((n:ℕ)+k)
    let D := fun k : ℕ => realEndpoint 1 ((n:ℕ)+k)
    let H := ∑' p : ℕ × ℕ, u p.1*v p.2*G (p.1+p.2)
    Summable (fun p : ℕ × ℕ => |u p.1*v p.2*G (p.1+p.2)|) ∧
      absoluteIntersection G u v ≤ 1/(2*(n:ℝ))*((∑' i, u i^2)+(∑' j, v j^2)) ∧
      Tendsto (fun N => roundedIntersection N G u v) atTop (𝓝 H) ∧
      |H| ≤ (∑' p : ℕ × ℕ,u p.1*u p.2*D (p.1+p.2))+
        (∑' p : ℕ × ℕ,v p.1*v p.2*D (p.1+p.2)) := by
  intro G D H
  have hmetric (k : ℕ) : 0≤D k := by
    have h := (real_endpoint_bounds 1 ((n:ℕ)+k)).1
    change 0≤2*D k at h
    linarith only [h]
  have hg (k : ℕ) : D k ≤ G k ∧ G k ≤ 2*D k := by
    simpa only [sum_singleton,mul_one,one_mul,Nat.add_zero,D,G] using
      prefix_defect_between_weil_metrics ((n:ℕ)+k) {0} (fun _ => 1)
  have dom (a b A : ℕ → ℝ) (hA : ∀ k, 0≤A k ∧ A k≤2*D k) (p : ℕ × ℕ) :
      |a p.1*b p.2*A (p.1+p.2)| ≤ |a p.1*b p.2*(2*D (p.1+p.2))| := by
    rw [abs_mul (a p.1*b p.2),abs_mul (a p.1*b p.2),abs_of_nonneg (hA _).1,
      abs_of_nonneg (mul_nonneg (by norm_num) (hmetric _))]
    exact mul_le_mul_of_nonneg_left (hA _).2 (abs_nonneg _)
  have hs (a b : ℕ → ℝ) (ha : Summable (fun i => a i^2)) (hb : Summable (fun j => b j^2))
      (A : ℕ → ℝ) (hA : ∀ k, 0≤A k ∧ A k≤2*D k) :
      Summable (fun p : ℕ × ℕ => |a p.1*b p.2*A (p.1+p.2)|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (dom a b A hA) (infinite_real_energy 1 n a b ha hb).1
  have hGentry (k : ℕ) : 0≤G k ∧ G k≤2*D k := ⟨(hmetric k).trans (hg k).1,(hg k).2⟩
  have hG := hs u v hu hv G hGentry
  have hD (k : ℕ) : 0≤D k ∧ D k≤2*D k := ⟨hmetric k,by linarith only [hmetric k]⟩
  have hI := roundedIntersection_tendsto G u v hG
  have hr := infinite_real_energy 1 n u v hu hv
  have hprice : absoluteIntersection G u v ≤ absoluteIntersection (fun k => 2*D k) u v :=
    hG.tsum_le_tsum (dom u v G hGentry) hr.1
  refine ⟨hG,hprice.trans (by simpa using hr.2),hI,?_⟩
  apply le_of_tendsto_of_tendsto' hI.abs ((roundedIntersection_tendsto D u u (hs u u hu hu D hD)).add
    (roundedIntersection_tendsto D v v (hs v v hv hv D hD)))
  intro N
  let a (i : ℕ) := (roundedJump N (u i):ℝ)/((N:ℝ)+1)
  let b (j : ℕ) := (roundedJump N (v j):ℝ)/((N:ℝ)+1)
  simpa only [roundedIntersection,G,D,a,b,Nat.add_assoc] using
    prefix_mixed_defect_le_weil_energies n (range N) (range N) a b

#print axioms infinite_pole_defect_from_integral_divisors
end GaloisForLFunctions.SignedArithmeticCorrespondences
