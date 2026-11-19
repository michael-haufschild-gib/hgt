import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.SeventhDifferencesAcrossTheSignedCofactors
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.FourCofactorCapsAtAZetaZero

/-!
# Cancellation in the long cofactor interval

Past its unit exception the cofactor stencil is periodic of mean zero.
Seven periodic summations by parts retain at most seven samples at the
sharp lower boundary and an inverse seventh power in the interior.
-/

noncomputable section
open Finset
open GaloisForLFunctions.BezoutValuationIncidence
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem cofactor_period_four {n : ℕ} (hn : 2≤n) : innerJump 1 (n+4)=innerJump 1 n := by
  rcases Nat.even_or_odd n with ⟨k,hk⟩ | ⟨k,hk⟩
  · have hpos : 0<k := by omega
    obtain ⟨u,hu⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [show n+4=2*(u+2)+2 by omega,show n=2*u+2 by omega,(innerJump_dyadic_pair (u+2)).2,
      (innerJump_dyadic_pair u).2,pow_add]
    norm_num
  · rw [show n+4=2*(k+2)+1 by omega,show n=2*k+1 by omega,(innerJump_dyadic_pair (k+2)).1,
      (innerJump_dyadic_pair k).1,if_neg (by omega : k+2≠0),if_neg (by omega : k≠0)]

private theorem shifted_cofactor_mean : ∑ v ∈ range 4, innerJump 1 (v+4) = 0 := by
  have h4 := (innerJump_dyadic_pair 1).2
  have h5 := (innerJump_dyadic_pair 2).1
  have h6 := (innerJump_dyadic_pair 2).2
  have h7 := (innerJump_dyadic_pair 3).1
  norm_num at h4 h5 h6 h7
  rw [show 4=3+1 by decide,Finset.sum_range_succ,show 3=2+1 by decide,Finset.sum_range_succ,
    show 2=1+1 by decide,Finset.sum_range_succ,Finset.sum_range_one]
  change innerJump 1 4+innerJump 1 5+innerJump 1 6+innerJump 1 7=0
  linarith only [h4,h5,h6,h7]

private theorem difference_congr_on (k : ℕ) (f g : ℕ → ℝ) (v : ℕ)
    (h : ∀ i ≤ k, f (v+i)=g (v+i)) : bdiff^[k] f v=bdiff^[k] g v := by
  induction k generalizing v with
  | zero => simpa only [Function.iterate_zero_apply,Nat.add_zero] using h 0 le_rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply',bdiff]
    have shifted (i : ℕ) (hi : i ≤ k) : f ((v+1)+i) = g ((v+1)+i) := by
      rw [show (v+1)+i=v+(i+1) by omega]
      exact h (i+1) (Nat.succ_le_succ hi)
    rw [ih v (fun i hi => h i (hi.trans (Nat.le_succ k))), ih (v+1) shifted]

/-- Every omitted endpoint sample is retained explicitly. The estimate
is uniform in the prime spacing, the far quotient, and the terminal cofactor. -/
theorem signed_cofactor_tail_with_endpoints :
    ∃ C : ℝ, 0≤C ∧ ∀ (b m r : ℕ), 7 ≤ r → ∀ {h : ℝ}, 0<h → 4*Real.exp 8 < (m+1:ℕ)*h →
      |∑ v ∈ Ioc r m, innerJump 1 v*positiveCofactorProfile b h v| ≤
        C*(1/(h*(r:ℝ)^7)+∑ i ∈ Ioc r (r+7), |positiveCofactorProfile b h i|) := by
  obtain ⟨A,hA,htail⟩ := positive_cofactor_tail_variation
  let B := 2*(1+mass (1+1))
  have hB : 0≤B := (abs_nonneg _).trans (innerJump_pointwise_bound 1 0)
  let W (v : ℕ) := innerJump 1 (v+4)
  have hmean : ∑ i ∈ range 4, W i=0 := shifted_cofactor_mean
  have hper (i : ℕ) : W (i+4)=W i := cofactor_period_four (by omega : 2 ≤ i+4)
  have hweight (i : ℕ) : |W i|≤B := innerJump_pointwise_bound 1 (i+4)
  let K := (2*(4:ℝ))^7 * B
  have hK : 0≤K := by dsimp only [K]; positivity
  refine ⟨K*(A+7*2^7),by positivity,fun b m r hr h hh hend => ?_⟩
  let V := positiveCofactorProfile b h
  let X (v : ℕ) := if r<v then V v else 0
  let E := ∑ i ∈ Ioc r (r+7), |V i|
  have hE : 0≤E := sum_nonneg fun i _ => abs_nonneg _
  have hfar (v : ℕ) (hv : m+1≤v) : V v=0 := by
    have hx := hend.trans_le (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hv) hh.le)
    change quotientMeshProfile b (v*h)-quotientMeshProfile 1 (v*h)=0
    rw [quotient_mesh_after_support b hx,quotient_mesh_after_support 1 hx,sub_self]
  have he : (∑ v ∈ range (m+1), X v*W v) =
      ∑ v ∈ Ioc r m, innerJump 1 v*V v := by
    have hi : (range (m+1)).filter (r < ·) = Ioc r m := by
      ext v; simp only [mem_filter,mem_range,mem_Ioc]; omega
    simp only [X,ite_mul,zero_mul,←sum_filter,hi]
    exact sum_congr rfl fun v hv => by
      dsimp only [W]; rw [cofactor_period_four (by have := (mem_Ioc.mp hv).1; omega),mul_comm]
  rw [←he]
  have hp := abs_sum_mul_periodic_le_iter (by decide : 0<4) 6 W B hper hmean hweight X (m+1)
    (fun i hi => if_neg (by omega)) (fun i hi => by simp only [X,hfar i hi,ite_self])
  change |∑ v ∈ range (m+1), X v*W v| ≤ K*∑ v ∈ range (m+1), |bdiff^[7] X v| at hp
  apply hp.trans
  have hparts := sum_filter_add_sum_filter_not (range (m+1)) (· ≤ r) (fun v => |bdiff^[7] X v|)
  have above : (range (m+1)).filter (fun v => ¬v ≤ r) = Ioc r m := by
    ext v; simp only [mem_filter,mem_range,mem_Ioc]; omega
  rw [above] at hparts
  have hkeep : (∑ v ∈ Ioc r m, |bdiff^[7] X v|) ≤ A/(h*(r:ℝ)^7) := by
    rw [sum_congr rfl (fun v hv => congrArg abs (difference_congr_on 7 X V v (fun i _ =>
      if_pos ((mem_Ioc.mp hv).1.trans_le (Nat.le_add_right v i)))))]
    exact htail b m (by omega) hh
  let T := (range (m+1)).filter (· ≤ r)
  let S := T.filter (fun v => r < v+7)
  have hshort : ∑ v ∈ S, |bdiff^[7] X v| = ∑ v ∈ T, |bdiff^[7] X v| := by
    apply sum_subset (filter_subset _ _)
    intro v hv hvS
    have hj := le_of_not_gt fun h => hvS (mem_filter.mpr ⟨hv,h⟩)
    exact le_antisymm ((cofactor_difference_local_bound 7 X v (A := 0) (fun i hi => by
      rw [show X (v+i)=0 from if_neg (by omega),abs_zero])).trans_eq (mul_zero _)) (abs_nonneg _)
  have hcard : S.card ≤ 7 := by
    have hsub : S ⊆ Ioc (r-7) r := fun v hv => by
      obtain ⟨hT,hv7⟩ := mem_filter.mp hv
      exact mem_Ioc.mpr ⟨by omega,(mem_filter.mp hT).2⟩
    exact (card_le_card hsub).trans (by rw [Nat.card_Ioc]; omega)
  have hedge : ∑ v ∈ T, |bdiff^[7] X v| ≤ 7*(2^7*E) := by
    rw [←hshort]
    calc _ ≤ ∑ _v ∈ S, (2^7*E) := by
              apply sum_le_sum
              intro v hv
              have hvr := (mem_filter.mp (mem_filter.mp hv).1).2
              apply cofactor_difference_local_bound
              intro i hi
              by_cases hh' : r<v+i
              · simp only [X,if_pos hh']
                exact single_le_sum (fun t _ => abs_nonneg (V t)) (mem_Ioc.mpr ⟨hh',by omega⟩)
              · simpa only [X,if_neg hh',abs_zero] using hE
         _ ≤ _ := by rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right
                       (by exact_mod_cast hcard) (by positivity)
  rw [←hparts]
  apply (mul_le_mul_of_nonneg_left (add_le_add hedge hkeep) hK).trans
  have hf : 0≤1/(h*(r:ℝ)^7) := by positivity
  have him := add_nonneg (mul_nonneg hA hE) (mul_nonneg (by norm_num : (0:ℝ)≤7*2^7) hf)
  apply le_of_eq_of_le (by ring : K*(7*(2^7*E)+A/(h*(r:ℝ)^7)) =
    K*(7*2^7*E+A*(1/(h*(r:ℝ)^7))))
  rw [mul_assoc K]
  exact mul_le_mul_of_nonneg_left (by linarith only [him]) hK

private theorem first_quotient_profile_small {x : ℝ} (hx : x < Real.exp (-8)) :
    quotientMeshProfile 1 x=0 := by
  have hx' := dyadicSpline_eq_zero_outside (fun hz => hx.not_ge hz.1)
  have h0 : dyadicSpline 0=0 := if_neg (lt_irrefl _)
  simp [quotientMeshProfile,h0,hx']

/-- Splitting at a cofactor D retains its true lower-product correction.
The three terms are the small cofactor sum, the oscillating tail, and the
at most seven samples across its first admissible index. -/
theorem signed_cofactor_two_scale_bound :
    ∃ C : ℝ, 0≤C ∧ ∀ (b l m D : ℕ), 7≤D → ∀ {h : ℝ}, 0<h →
      4*Real.exp 8 < b*h → 4*Real.exp 8 < (m+1:ℕ)*h →
      7*(((max l D+7:ℕ):ℝ)*h) < Real.exp (-8) →
      |∑ v ∈ Ioc l m, innerJump 1 v*positiveCofactorProfile b h v| ≤
        C*((D:ℝ)^8*h^7 + 1/(h*(D:ℝ)^7) + (((max l D+7:ℕ):ℝ)*h)^7) := by
  obtain ⟨A,hA,hsmall⟩ := quotientMeshProfile_seventh
  obtain ⟨B,hB,htail⟩ := signed_cofactor_tail_with_endpoints
  let G := 2*(1+mass (1+1))
  have hG : 0≤G := (abs_nonneg _).trans (innerJump_pointwise_bound 1 0)
  let C := G*A+B+7*B*A
  have hC : 0≤C := by dsimp only [C]; positivity
  refine ⟨C,hC,fun b l m D hD h hh hbh hmh hcut => ?_⟩
  let r := max l D
  let V := positiveCofactorProfile b h
  let F (v : ℕ) := innerJump 1 v*V v
  have hpos (v : ℕ) (hv : 0<v) (hu : v ≤ r+7) : |V v|≤A*((v:ℝ)*h)^7 := by
    have x0 : 0<(v:ℝ)*h := mul_pos (Nat.cast_pos.mpr hv) hh
    have x1 := (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hu) hh.le)
      (by norm_num : (0:ℝ)≤7)).trans_lt hcut
    have xb := hbh.trans_le (mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_left hh.le (Nat.one_le_cast.mpr hv)) (Nat.cast_nonneg b))
    change |quotientMeshProfile b (v*h)-quotientMeshProfile 1 (v*h)|≤_
    rw [first_quotient_profile_small (by linarith only [x1,x0] : (v:ℝ)*h < Real.exp (-8)),sub_zero]
    exact hsmall x0 x1 b xb
  have boundary : (∑ i ∈ Ioc r (r+7), |V i|) ≤ 7*A*(((r+7:ℕ):ℝ)*h)^7 := by
    calc _ ≤ ∑ _i ∈ Ioc r (r+7), A*(((r+7:ℕ):ℝ)*h)^7 := by
              apply sum_le_sum
              intro i hi
              obtain ⟨hl,hu⟩ := mem_Ioc.mp hi
              exact (hpos i ((Nat.zero_le r).trans_lt hl) hu).trans
                (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
                  (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hu) hh.le) 7) hA)
         _ = _ := by rw [sum_const,Nat.card_Ioc,show r+7-r=7 by omega,nsmul_eq_mul]; norm_num; ring
  let lo := (Ioc l m).filter (· ≤ D)
  have low : |∑ v ∈ lo, F v| ≤ G*A*((D:ℝ)^8*h^7) := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc _ ≤ ∑ _v ∈ lo, G*(A*((D:ℝ)*h)^7) := by
              apply sum_le_sum
              intro v hv
              obtain ⟨hi,hu⟩ := mem_filter.mp hv
              dsimp only [F]
              rw [abs_mul]
              apply mul_le_mul (innerJump_pointwise_bound 1 v) _ (abs_nonneg _) hG
              exact (hpos v ((Nat.zero_le l).trans_lt (mem_Ioc.mp hi).1)
                (hu.trans ((le_max_right l D).trans (Nat.le_add_right r 7)))).trans
                (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
                  (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hu) hh.le) 7) hA)
         _ ≤ (D:ℝ)*(G*(A*((D:ℝ)*h)^7)) := by
              rw [sum_const,nsmul_eq_mul]
              have hcard : lo ⊆ Ioc 0 D := fun v hv => mem_Ioc.mpr
                ⟨(Nat.zero_le l).trans_lt (mem_Ioc.mp (mem_filter.mp hv).1).1,(mem_filter.mp hv).2⟩
              have hc := card_le_card hcard
              rw [Nat.card_Ioc,Nat.sub_zero] at hc
              exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (by positivity)
         _ = _ := by ring
  have hr := hD.trans (le_max_right l D)
  have hi := htail b m r hr hh hmh
  have hfrac : 1/(h*(r:ℝ)^7) ≤ 1/(h*(D:ℝ)^7) := by
    apply one_div_le_one_div_of_le (mul_pos hh (pow_pos (Nat.cast_pos.mpr (by omega : 0<D)) 7))
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg D)
      (Nat.cast_le.mpr (le_max_right l D)) 7) hh.le
  have hi' := hi.trans (mul_le_mul_of_nonneg_left (add_le_add hfrac boundary) hB)
  have hsplit := sum_filter_add_sum_filter_not (Ioc l m) (· ≤ D) F
  have hs : (Ioc l m).filter (fun v => ¬v≤D)=Ioc r m := by
    ext v; simp only [r,mem_filter,mem_Ioc,max_lt_iff]; omega
  rw [hs] at hsplit
  change |∑ v ∈ Ioc l m, F v| ≤ _
  rw [←hsplit]
  apply (abs_add_le _ _).trans ((add_le_add low hi').trans _)
  let X := (D:ℝ)^8*h^7
  let Y := 1/(h*(D:ℝ)^7)
  let Z := (((r+7:ℕ):ℝ)*h)^7
  have hX : 0≤X := by dsimp only [X]; positivity
  have hY : 0≤Y := by dsimp only [Y]; positivity
  have hZ : 0≤Z := by dsimp only [Z]; positivity
  change G*A*X+B*(Y+7*A*Z) ≤ C*(X+Y+Z)
  have h₁ : G*A≤C := by dsimp only [C]; linarith only [hB,mul_nonneg hB hA]
  have h₂ : B≤C := by dsimp only [C]; linarith only [mul_nonneg hG hA,mul_nonneg hB hA]
  have h₃ : 7*B*A≤C := by dsimp only [C]; linarith only [hB,mul_nonneg hG hA]
  linarith only [mul_le_mul_of_nonneg_right h₁ hX,mul_le_mul_of_nonneg_right h₂ hY,
    mul_le_mul_of_nonneg_right h₃ hZ]

/-- On a fine mesh, the square-root splitting point pays five powers of
the square root of the mesh. Only the true lower cofactor contributes
the additional seventh-power endpoint term. -/
theorem signed_cofactor_fine_mesh :
    ∃ C : ℝ, 0≤C ∧ ∀ (b l m : ℕ) {h : ℝ}, 0<h → Real.sqrt h≤1/8 →
      112*max ((l:ℝ)*h) (Real.sqrt h) < Real.exp (-8) →
      4*Real.exp 8 < b*h → 4*Real.exp 8 < (m+1:ℕ)*h →
      |∑ v ∈ Ioc l m, innerJump 1 v*positiveCofactorProfile b h v| ≤
        C*((Real.sqrt h)^5+((l:ℝ)*h)^7) := by
  obtain ⟨C,hC,h⟩ := signed_cofactor_two_scale_bound
  refine ⟨C*(2^8+1+16^7),by positivity,fun b l m {h₀} hh ht8 hcut hb hm => ?_⟩
  let t := Real.sqrt h₀
  let D := ⌈1/t⌉₊
  let u := (l:ℝ)*h₀
  let z := max u t
  have ht : 0<t := Real.sqrt_pos.mpr hh
  have ht1 : t≤1 := by linarith only [ht8]
  have ht2 : t^2=h₀ := Real.sq_sqrt hh.le
  have hu : 0≤u := mul_nonneg (Nat.cast_nonneg l) hh.le
  have hz := ht.le.trans (le_max_right u t)
  have hlo : 1 ≤ (D:ℝ)*t := (div_le_iff₀ ht).mp (Nat.le_ceil _)
  have dhi := Nat.ceil_lt_add_one (by positivity : 0≤1/t)
  have hhi : (D:ℝ)*t ≤ 2 := by
    have hj := mul_lt_mul_of_pos_right dhi ht
    rw [add_mul,div_mul_cancel₀ _ ht.ne',one_mul] at hj
    linarith only [hj,ht1]
  have hD : 7≤D := by
    by_contra! hn
    have hs : (D:ℝ)≤6 := by exact_mod_cast (by omega : D≤6)
    linarith only [hlo,mul_le_mul_of_nonneg_right hs ht.le,ht8]
  have hD0 : (0:ℝ)<D := Nat.cast_pos.mpr (by omega)
  have htn : h₀ ≤ t := by rw [←ht2,sq]; exact mul_le_of_le_one_right ht.le ht1
  have hDh : (D:ℝ)*h₀ ≤ 2*t := by
    rw [←ht2,sq,←mul_assoc]
    exact mul_le_mul_of_nonneg_right hhi ht.le
  have hend : ((max l D+7:ℕ):ℝ)*h₀ ≤ 16*z := by
    push_cast
    rw [add_mul,max_mul_of_nonneg _ _ hh.le]
    have hM : max u ((D:ℝ)*h₀) ≤ 2*z := max_le (by linarith only [le_max_left u t,hz])
      (hDh.trans (mul_le_mul_of_nonneg_left (le_max_right u t) (by norm_num)))
    linarith only [hM,htn,le_max_right u t,hz]
  have hborn := (mul_le_mul_of_nonneg_left hend (by norm_num : (0:ℝ)≤7)).trans_lt
    ((le_of_eq (by ring : 7*(16*z)=112*z)).trans_lt hcut)
  have ht65 : t^6 ≤ t^5 := by rw [pow_succ t 5]; exact mul_le_of_le_one_right (pow_nonneg ht.le _) ht1
  have ht75 : t^7 ≤ t^5 := by
    rw [pow_succ t 6]
    exact (mul_le_of_le_one_right (pow_nonneg ht.le _) ht1).trans ht65
  have hlow : (D:ℝ)^8*h₀^7 ≤ 2^8*t^5 := by
    have hp := pow_le_pow_left₀ (mul_nonneg hD0.le ht.le) hhi 8
    rw [←ht2,show (D:ℝ)^8*(t^2)^7=((D:ℝ)*t)^8*t^6 by ring]
    exact mul_le_mul hp ht65 (pow_nonneg ht.le _) (by norm_num)
  have htail : 1/(h₀*(D:ℝ)^7)≤t^5 := by
    apply (div_le_iff₀ (mul_pos hh (pow_pos hD0 7))).mpr
    have hp : 1≤((D:ℝ)*t)^7 := one_le_pow₀ hlo
    rw [←ht2]
    exact hp.trans_eq (by ring)
  have hzp : z^7 ≤ u^7+t^5 := by
    rcases le_total u t with hle | hle
    · rw [show z=t from max_eq_right hle]
      exact ht75.trans (le_add_of_nonneg_left (pow_nonneg hu _))
    · rw [show z=u from max_eq_left hle]
      exact le_add_of_nonneg_right (pow_nonneg ht.le _)
  have hedge : (((max l D+7:ℕ):ℝ)*h₀)^7 ≤ 16^7*(u^7+t^5) := by
    apply (pow_le_pow_left₀ (by positivity) hend 7).trans
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hzp (by norm_num)
  apply (h b l m D hD hh hb hm hborn).trans
  rw [mul_assoc C]
  apply mul_le_mul_of_nonneg_left _ hC
  change _ ≤ (2^8+1+16^7)*(t^5+u^7)
  linarith only [hlow,htail,hedge,pow_nonneg hu 7]

#print axioms signed_cofactor_fine_mesh
#print axioms signed_cofactor_two_scale_bound
#print axioms signed_cofactor_tail_with_endpoints
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
