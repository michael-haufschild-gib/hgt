import GaloisForLFunctions.CountingHolography.Sections.TheJetsOfMovingIntegerTranslates
import GaloisForLFunctions.CountingHolography.Sections.StabilityOfArchimedeanJetsOnACompactWindow
import GaloisForLFunctions.CountingHolography.Sections.TheFullPrimeIdealAtDiagonalScale

/-!
# The archimedean jet on the three square conductors

In coordinates relative to the middle conductor, the two upper spline
atoms approach a fixed pair with relative dilation four.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open AbsoluteGeometryOfSpecZ Filter Topology Finset BiScaleUncertainty.ChebyshevGauge Zeta23

private def squareAtom (u : ℝ) := cubicSpline (u-(Real.log 3+5))

private def upperPacket (t u : ℝ) := 2*squareAtom u-squareAtom (u-t)


private def atomEnd := ⌈Real.exp (Real.log 3+5+4)⌉₊+1
private def clusterEnd := 9*atomEnd
private def squareShift (n : ℕ) := Real.log ((2+(n:ℝ)⁻¹)^2)
private def squareHorizon (n : ℕ) := 3*windowEnd ((2*n+1)^2+1)

private theorem atomEnd_pos : 0 < atomEnd := Nat.succ_pos _
private theorem clusterEnd_pos : 0 < clusterEnd := Nat.mul_pos (by decide) atomEnd_pos

private theorem atom_support (u : ℝ) (h : u ≤ Real.log 3 ∨ Real.log atomEnd ≤ u) :
    squareAtom u=0 := by
  apply cubicSpline_eq_zero
  rcases h with hl | hu
  · linarith only [neg_le_abs (u-(Real.log 3+5)),hl]
  have hceil := Nat.le_ceil (Real.exp (Real.log 3+5+4))
  have hh : Real.exp (Real.log 3+5+4) < (atomEnd : ℝ) := by
    unfold atomEnd
    push_cast
    linarith only [hceil]
  have hk := (Real.lt_log_iff_exp_lt (Nat.cast_pos.mpr atomEnd_pos)).mpr hh
  linarith only [le_abs_self (u-(Real.log 3+5)),hk,hu]

private theorem upper_support {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ Real.log 9) (u : ℝ)
    (hu : u ≤ Real.log 3 ∨ Real.log clusterEnd ≤ u) : upperPacket t u=0 := by
  have hlog : Real.log clusterEnd=Real.log 9+Real.log atomEnd := by
    rw [clusterEnd,Nat.cast_mul,Real.log_mul (by norm_num) (Nat.cast_pos.mpr atomEnd_pos : 0 < (atomEnd:ℝ)).ne']
    norm_num
  have h₉ : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have hab : u ≤ Real.log 3 ∨ Real.log atomEnd ≤ u :=
    hu.imp id (fun h => by linarith only [hlog,h,h₉])
  have has : u-t ≤ Real.log 3 ∨ Real.log atomEnd ≤ u-t :=
    hu.imp (fun h => by linarith only [h,ht]) (fun h => by linarith only [hlog,h,ht'])
  simp only [upperPacket,atom_support _ hab,atom_support _ has,mul_zero,sub_zero]

private theorem shift_bounds {n : ℕ} (hn : 0 < n) :
    0 ≤ squareShift n ∧ squareShift n ≤ Real.log 9 := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h₀ : 0 ≤ (n:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have h₁ : (n:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn'
  have ha : 1 ≤ (2+(n:ℝ)⁻¹)^2 := one_le_pow₀ (by linarith only [h₀])
  have hb : (2+(n:ℝ)⁻¹)^2 ≤ 9 := by
    exact (pow_le_pow_left₀ (by linarith only [h₀] : 0 ≤ 2+(n:ℝ)⁻¹)
      (by linarith only [h₁] : 2+(n:ℝ)⁻¹ ≤ 3) 2).trans_eq (by norm_num)
  exact ⟨Real.log_nonneg ha,Real.log_le_log (zero_lt_one.trans_le ha) hb⟩

private theorem shift_limit : Tendsto squareShift atTop (𝓝 (Real.log 4)) := by
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) := tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have h : Tendsto (fun n : ℕ => 2+(n:ℝ)⁻¹) atTop (𝓝 (2+(0:ℝ))) := tendsto_const_nhds.add hi
  have hp := h.pow 2
  have hv : (2+(0:ℝ))^2 ≠ 0 := by norm_num
  change Tendsto (Real.log ∘ (fun n : ℕ => (2+(n:ℝ)⁻¹)^2)) atTop (𝓝 (Real.log 4))
  simpa only [add_zero,show (2:ℝ)^2=4 by norm_num] using (Real.continuousAt_log hv).tendsto.comp hp

private theorem square_packet_clusters {n : ℕ} (hn : 0 < n) (u : ℝ) :
    packet (successorSquareTriple n) u =
      squareAtom u+upperPacket (squareShift n) (u-Real.log (n^2:ℕ)) := by
  let F := fun d : ℝ => cubicSpline (u-(Real.log 3+5)-Real.log d)
  change (∑ i, (successorSquareTriple n i:ℝ)*F ((i:ℝ)+1)) = _
  rw [show (∑ i, (successorSquareTriple n i:ℝ)*F ((i:ℝ)+1)) =
    ∑ i : Fin ((2*n+1)^2+1), F ((i:ℝ)+1)*(successorSquareTriple n i:ℝ) from
      sum_congr rfl fun _ _ => mul_comm _ _,sum_successorSquareTriple hn F]
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hr : 0 < 2+(n:ℝ)⁻¹ := by positivity
  have hb : (((2*n+1:ℕ):ℝ)^2)=(n:ℝ)^2*(2+(n:ℝ)⁻¹)^2 := by
    push_cast
    field_simp
  have hl : Real.log (((2*n+1:ℕ):ℝ)^2)=Real.log ((n:ℝ)^2)+squareShift n := by
    rw [hb,Real.log_mul (sq_pos_of_pos hn').ne' (sq_pos_of_pos hr).ne',squareShift]
  simp only [F,upperPacket,squareAtom,Real.log_one,sub_zero,Nat.cast_pow,hl]
  rw [show u-Real.log ((n:ℝ)^2)-(Real.log 3+5)=u-(Real.log 3+5)-Real.log ((n:ℝ)^2) by ring,
    show u-Real.log ((n:ℝ)^2)-squareShift n-(Real.log 3+5)=
      u-(Real.log 3+5)-(Real.log ((n:ℝ)^2)+squareShift n) by ring]
  ring

private theorem actual_window_cover {n : ℕ} (hn : 0 < n) :
    atomEnd ≤ 1+squareHorizon n ∧ clusterEnd*n^2 ≤ 1+squareHorizon n := by
  let E := Real.exp (Real.log 3+5+5)
  let N := (2*n+1)^2+1
  have hbase : 3 ≤ Real.exp (Real.log 3+5+4) := by
    linarith only [Real.add_one_le_exp (Real.log 3+5+4),Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)]
  have hK : (atomEnd:ℝ) ≤ E := by
    have hc := Nat.ceil_lt_add_one (Real.exp_pos (Real.log 3+5+4)).le
    have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp 1) (Real.exp_pos (Real.log 3+5+4)).le
    unfold E atomEnd
    rw [Nat.cast_add,Nat.cast_one,show Real.log 3+5+5=(Real.log 3+5+4)+1 by ring,
      Real.exp_add (Real.log 3+5+4) 1]
    linarith only [hbase,hc,hh]
  have he : E*((N:ℝ)+1) ≤ windowEnd N := by
    change _ ≤ (⌈Real.exp (Real.log 3+5+Real.log ((N:ℝ)+1)+5)⌉₊:ℝ)
    rw [show Real.log 3+5+Real.log ((N:ℝ)+1)+5=(Real.log 3+5+5)+Real.log ((N:ℝ)+1) by ring,
      Real.exp_add,Real.exp_log (by positivity)]
    exact Nat.le_ceil _
  have hl : 3*(n:ℝ)^2 ≤ (N:ℝ)+1 := by
    dsimp only [N]; push_cast; nlinarith only [sq_nonneg (n:ℝ),Nat.cast_nonneg (α := ℝ) n]
  have hq : clusterEnd*n^2 ≤ squareHorizon n := by
    change 9*atomEnd*n^2 ≤ 3*windowEnd N
    have h := mul_le_mul_of_nonneg_left hl (show 0 ≤ E from (Real.exp_pos _).le)
    have h' := mul_le_mul_of_nonneg_right hK (sq_nonneg (n:ℝ))
    have hn' : 9*(atomEnd:ℝ)*(n:ℝ)^2 ≤ 3*(windowEnd N:ℝ) := by linarith only [he,h,h']
    exact_mod_cast hn'
  have hx : atomEnd ≤ clusterEnd*n^2 :=
    (Nat.le_mul_of_pos_left _ (by decide : 0 < 9)).trans (Nat.le_mul_of_pos_right _ (pow_pos hn 2))
  exact ⟨by omega,by omega⟩


private theorem atom_smooth : ContDiff ℝ 2 squareAtom :=
  contDiff_cubicSpline.comp (contDiff_id.sub contDiff_const)

private theorem atom_compact : HasCompactSupport squareAtom :=
  hasCompactSupport_cubicSpline.comp_homeomorph (Homeomorph.subRight _)

private theorem upper_smooth (t : ℝ) : ContDiff ℝ 2 (upperPacket t) :=
  (contDiff_const.mul atom_smooth).sub (atom_smooth.comp (contDiff_id.sub contDiff_const))

private theorem upper_compact (t : ℝ) : HasCompactSupport (upperPacket t) :=
  (atom_compact.mul_left (f := fun _ => (2:ℝ))).sub (atom_compact.comp_homeomorph (Homeomorph.subRight t))

private theorem atom_bound (u : ℝ) : |squareAtom u| ≤ 1 := by
  unfold squareAtom
  rw [abs_of_nonneg (cubicSpline_nonneg _)]
  exact (cubicSpline_le_half _).trans (by norm_num)

private theorem upper_bound (t u : ℝ) : |upperPacket t u| ≤ 3 := by
  refine (abs_sub _ _).trans ?_
  rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  linarith only [atom_bound u,atom_bound (u-t)]

private theorem upper_limit :
    ∃ z : ℝ, ∀ ν r : ℕ → ℕ, Tendsto ν atTop atTop → Tendsto r atTop atTop →
      Tendsto (fun n => degreeForm (upperPacket (squareShift (ν n))) (3*clusterEnd) (r n)) atTop (𝓝 z) := by
  let t := Real.log 4
  have ht : 0 ≤ t := Real.log_nonneg (by norm_num)
  have ht' : t ≤ Real.log 9 := Real.log_le_log (by norm_num) (by norm_num)
  obtain ⟨A,hA⟩ := atom_smooth.lipschitzWith_of_hasCompactSupport atom_compact (by norm_num)
  have hLip (u v : ℝ) : |squareAtom u-squareAtom v| ≤ (A:ℝ)*|u-v| := by
    simpa only [Real.dist_eq] using hA.dist_le_mul u v
  let B := 3+3*(A:ℝ)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hU (s u v : ℝ) : |upperPacket s u-upperPacket s v| ≤ B*|u-v| := by
    change |(2*squareAtom u-squareAtom (u-s))-(2*squareAtom v-squareAtom (v-s))| ≤ _
    rw [show (2*squareAtom u-squareAtom (u-s))-(2*squareAtom v-squareAtom (v-s))=
      2*(squareAtom u-squareAtom v)-(squareAtom (u-s)-squareAtom (v-s)) by ring]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have h := hLip (u-s) (v-s)
    rw [show u-s-(v-s)=u-v by ring] at h
    dsimp only [B]
    linarith only [h,hLip u v,abs_nonneg (u-v)]
  let F := (packetTest (upperPacket t) (upper_smooth t) (upper_compact t)).1
  let z := -(_root_.RHTower.WeilOneSided.weilArchRe (EF.weilTest F F)-(_root_.RHTower.weilPoleTerm (EF.weilTest F F)).re)
  refine ⟨z,fun ν r hν hr => ?_⟩
  let e := fun n => (A:ℝ)*|squareShift (ν n)-t|
  have he : Tendsto e atTop (𝓝 0) := by
    change Tendsto (fun n => (A:ℝ)*|squareShift (ν n)-Real.log 4|) atTop (𝓝 0)
    simpa only [Function.comp_apply,sub_self,abs_zero,mul_zero] using
      (((shift_limit.comp hν).sub_const (Real.log 4)).abs).const_mul (A:ℝ)
  refine tendsto_degreeForm_varying_compact_packets clusterEnd_pos (upper_smooth t)
    (upper_compact t) (upper_support ht ht') _ r hr hB he ?_
  filter_upwards [hν.eventually_ge_atTop 1] with n hn
  have hbn (s u : ℝ) : |upperPacket s u| ≤ B := (upper_bound s u).trans (by
    dsimp only [B]; linarith only [A.coe_nonneg])
  refine ⟨mul_nonneg A.coe_nonneg (abs_nonneg _),fun u => ⟨hbn _ _,hbn _ _,?_⟩,
    fun u v => ⟨hU _ u v,hU _ u v⟩,fun u hu => ?_⟩
  · have h := hLip (u-t) (u-squareShift (ν n))
    change |(2*squareAtom u-squareAtom (u-squareShift (ν n)))-(2*squareAtom u-squareAtom (u-t))| ≤ _
    rw [show (2*squareAtom u-squareAtom (u-squareShift (ν n)))-(2*squareAtom u-squareAtom (u-t))=
      squareAtom (u-t)-squareAtom (u-squareShift (ν n)) by ring]
    rwa [show u-t-(u-squareShift (ν n))=squareShift (ν n)-t by ring] at h
  · rw [upper_support (shift_bounds hn).1 (shift_bounds hn).2 u hu,upper_support ht ht' u hu]

/-- A nonzero sample of an integer translate lies in its multiplicative
support interval, independently of the chosen surrounding window. -/
private theorem sample_band {f : ℝ → ℝ} {K r d : ℕ} (hK : 0 < K) (hr : 0 < r) (hd : 0 < d)
    (hs : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u=0) (j : ℕ)
    (hj : degreeSample (fun u => f (u-Real.log d)) r j ≠ 0) :
    (r:ℝ)*d ≤ j ∧ (j:ℝ) ≤ K*(r*d) := by
  let x := Real.log ((j:ℝ)/r)-Real.log d
  have hx : f x ≠ 0 := hj
  have h₁ : Real.log 3 < x := lt_of_not_ge fun h => hx (hs _ (Or.inl h))
  have h₂ : x < Real.log K := lt_of_not_ge fun h => hx (hs _ (Or.inr h))
  have hr' : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  have hd' : 0 < (d:ℝ) := Nat.cast_pos.mpr hd
  have hld : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd)
  have h₃ : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hj' : 0 < j := by
    by_contra! hh
    have hj₀ : j=0 := Nat.eq_zero_of_le_zero hh
    simp only [x,hj₀,Nat.cast_zero,zero_div,Real.log_zero,zero_sub] at h₁
    linarith only [h₃,hld,h₁]
  have hlog : x=Real.log ((j:ℝ)/((r:ℝ)*d)) := by
    rw [← div_div,Real.log_div (div_pos (Nat.cast_pos.mpr hj') hr').ne' hd'.ne']
  rw [hlog] at h₁ h₂
  have hjr := div_pos (Nat.cast_pos.mpr hj' : 0 < (j:ℝ)) (mul_pos hr' hd')
  have hl := (lt_div_iff₀ (mul_pos hr' hd')).mp ((Real.log_lt_log_iff (by norm_num) hjr).mp h₁)
  have hu := (div_lt_iff₀ (mul_pos hr' hd')).mp ((Real.log_lt_log_iff hjr (Nat.cast_pos.mpr hK)).mp h₂)
  exact ⟨by linarith only [hl,mul_pos hr' hd'],hu.le⟩

private theorem atom_sample_mass {f : ℝ → ℝ} {K r d : ℕ} (hK : 0 < K) (hr : 0 < r) (hd : 0 < d)
    (hs : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u=0) (hb : ∀ u, |f u| ≤ 3) (S : Finset ℕ) :
    (∑ j ∈ S, |degreeSample (fun u => f (u-Real.log d)) r j| / j) ≤ 3*K := by
  let v := degreeSample (fun u => f (u-Real.log d)) r
  have h := harmonicSample_le S (X := (r:ℝ)*d) (D := (K:ℝ)) (f := fun j => |v j| / 3)
    (mul_pos (Nat.cast_pos.mpr hr) (Nat.cast_pos.mpr hd)) (Nat.cast_nonneg _)
    (fun j => (div_le_one (by norm_num)).mpr (hb _))
    (fun j hj => sample_band hK hr hd hs j (fun hz => hj (by simp only [v,hz,abs_zero,zero_div])))
  have he : (∑ j ∈ S, |v j| / 3 / j) = (∑ j ∈ S, |v j| / j)/3 := by
    rw [sum_div]
    exact sum_congr rfl fun j _ => by ring
  rw [he] at h
  linarith only [h]


private theorem mixed_square_error : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ {r : ℕ}, 0 < r →
    let L := squareHorizon n
    let g := fun u => upperPacket (squareShift n) (u-Real.log (n^2:ℕ))
    |degreeForm (packet (successorSquareTriple n)) L r-degreeForm squareAtom L r-degreeForm g L r| ≤ C/n := by
  let K := (clusterEnd:ℝ)
  have hK : 1 ≤ K := by dsimp only [K]; exact_mod_cast (show 1 ≤ clusterEnd from clusterEnd_pos)
  have hK' : 0 < K := zero_lt_one.trans_le hK
  let C := 4*K*(3*K)^2
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  filter_upwards [eventually_ge_atTop (2*clusterEnd),eventually_ge_atTop 1] with n hn hn₁
  intro r hr
  let S := Ioc r (r+squareHorizon n*r)
  let g := fun u => upperPacket (squareShift n) (u-Real.log (n^2:ℕ))
  let H := (n:ℝ)/K
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn₁
  have hd : 0 < n^2 := pow_pos hn₁ _
  have hr' : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  have hH : 2 ≤ H := (le_div_iff₀ hK').mpr (by dsimp only [K]; exact_mod_cast hn)
  have hH' : 0 < H := lt_of_lt_of_le (by norm_num) hH
  have hs₀ (u : ℝ) (h : u ≤ Real.log 3 ∨ Real.log clusterEnd ≤ u) : squareAtom u=0 := by
    apply atom_support u
    exact h.imp id (fun h => (Real.log_le_log (Nat.cast_pos.mpr atomEnd_pos)
      (by exact_mod_cast (show atomEnd ≤ clusterEnd from Nat.le_mul_of_pos_left _ (by decide : 0 < 9)))).trans h)
  have hshape := upper_support (shift_bounds hn₁).1 (shift_bounds hn₁).2
  have hsep {i j : ℕ} (hv : degreeSample squareAtom r i ≠ 0) (hw : degreeSample g r j ≠ 0) :
      H^2*i ≤ j := by
    have hv' : degreeSample (fun u => squareAtom (u-Real.log (1:ℕ))) r i ≠ 0 := by simpa using hv
    have hi := (sample_band clusterEnd_pos hr (d := 1) (by decide) hs₀ i hv').2
    simp only [Nat.cast_one,mul_one] at hi
    have hj := (sample_band clusterEnd_pos hr hd hshape j hw).1
    rw [Nat.cast_pow] at hj
    calc H^2*(i:ℝ) ≤ H^2*(K*r) := mul_le_mul_of_nonneg_left hi (sq_nonneg _)
      _ = ((n:ℝ)^2*r)/K := by dsimp only [H]; field_simp
      _ ≤ (n:ℝ)^2*r := div_le_self (by positivity) hK
      _ ≤ _ := (mul_comm _ _).le.trans hj
  have hmix := degreeForm_separated_mixed_bound (L := squareHorizon n) squareAtom g hr hH
    (fun _ _ _ _ hi hj => hsep hi hj)
  have hv := atom_sample_mass clusterEnd_pos hr (d := 1) (by decide) hs₀
    (fun u => (atom_bound u).trans (by norm_num)) S
  simp only [Nat.cast_one,Real.log_one,sub_zero] at hv
  have hw := atom_sample_mass clusterEnd_pos hr hd hshape (upper_bound _) S
  have hap : ∑ i ∈ S, |degreeSample squareAtom r i| / i ≥ 0 := sum_nonneg fun _ _ => by positivity
  have hbp : ∑ j ∈ S, |degreeSample g r j| / j ≥ 0 := sum_nonneg fun _ _ => by positivity
  have hp := mul_le_mul hv hw hbp (show 0 ≤ 3*K by positivity)
  have h := mul_le_mul_of_nonneg_left hp (show 0 ≤ 4/H by positivity)
  have he : packet (successorSquareTriple n) = fun u => squareAtom u+g u := funext (square_packet_clusters hn₁)
  dsimp only
  rw [he]
  exact hmix.trans (by
    change (4/H)*_ * _ ≤ C/n
    rw [mul_assoc]
    refine h.trans_eq ?_
    change 4/H*(3*K*(3*K))=C/n
    dsimp only [C,H]
    field_simp [hK'.ne',hn'.ne'])

/-- The original three-square jet has a common finite limit along every
sequence of resolutions tending to infinity with the conductor. -/
theorem successorSquare_archimedean_jet_limit :
    ∃ z : ℝ, ∀ ν r : ℕ → ℕ, Tendsto ν atTop atTop → Tendsto r atTop atTop →
      Tendsto (fun n => degreeForm (packet (successorSquareTriple (ν n))) (3*windowEnd ((2*ν n+1)^2+1)) (r n))
        atTop (𝓝 z) := by
  obtain ⟨z₀,h₀⟩ : ∃ z : ℝ, Tendsto (degreeForm squareAtom (3*atomEnd)) atTop (𝓝 z) :=
    ⟨_,tendsto_degreeForm atom_smooth atom_compact atomEnd_pos atom_support⟩
  obtain ⟨z₁,h₁⟩ := upper_limit
  obtain ⟨C,_,hmix⟩ := mixed_square_error
  refine ⟨z₀+z₁,fun ν r hν hr => ?_⟩
  let g := fun (n : ℕ) (u : ℝ) => upperPacket (squareShift (ν n)) (u-Real.log ((ν n)^2:ℕ))
  have hlo : Tendsto (fun n => degreeForm squareAtom (squareHorizon (ν n)) (r n)) atTop (𝓝 z₀) := by
    apply (h₀.comp hr).congr'
    filter_upwards [hν.eventually_ge_atTop 1,hr.eventually_ge_atTop 1] with n hn hR
    have hcov : atomEnd*1 ≤ 1+squareHorizon (ν n) := by simpa using (actual_window_cover hn).1
    have hh := degreeForm_log_dilate (fun u hu => atom_support u
      (hu.imp (fun h => h.trans (Real.log_nonneg (by norm_num))) id)) atomEnd_pos (d := 1) (by decide) hR hcov
    simpa only [Nat.cast_one,Real.log_one,sub_zero,one_mul,Function.comp_apply] using hh.symm
  have hr' : Tendsto (fun n => (ν n)^2*r n) atTop atTop := by
    apply tendsto_atTop_mono' _ _ hr
    filter_upwards [hν.eventually_ge_atTop 1] with n hn
    exact Nat.le_mul_of_pos_left _ (pow_pos hn 2)
  have hhi : Tendsto (fun n => degreeForm (g n) (squareHorizon (ν n)) (r n)) atTop (𝓝 z₁) := by
    apply (h₁ ν _ hν hr').congr'
    filter_upwards [hν.eventually_ge_atTop 1,hr.eventually_ge_atTop 1] with n hn hR
    exact (degreeForm_log_dilate (fun u hu => upper_support (shift_bounds hn).1 (shift_bounds hn).2 u
      (hu.imp (fun h => h.trans (Real.log_nonneg (by norm_num))) id)) clusterEnd_pos (pow_pos hn 2) hR
        (actual_window_cover hn).2).symm
  have hm : Tendsto (fun n => degreeForm (packet (successorSquareTriple (ν n))) (squareHorizon (ν n)) (r n)-
      degreeForm squareAtom (squareHorizon (ν n)) (r n)-degreeForm (g n) (squareHorizon (ν n)) (r n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun n : ℕ => C/(ν n:ℝ)) _ (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hν))
    filter_upwards [hν.eventually hmix,hr.eventually_ge_atTop 1] with n hn hR
    rw [Real.norm_eq_abs]
    exact hn hR
  simpa only [squareHorizon,sub_add_cancel,zero_add,add_comm z₁ z₀] using (hm.add hhi).add hlo

#print axioms successorSquare_archimedean_jet_limit

end GaloisForLFunctions.CountingHolography.Sections
