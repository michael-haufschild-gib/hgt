import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCoupledOddNeutral

/-!
# A common coupled odd-four coefficient interval on the adverse ray

The exact complete-source compensation bounds preserve half the unloaded
coercive reserve for every fixed coefficient between zero and ten trillion.
This covers the entire negative-compensation region. The positive-region
small-scale source sign remains a separate obligation.
-/

namespace RHTower.ThetaCuspCoupledOddLoaded
noncomputable section
open Matrix ThetaCuspOddCentral ThetaCuspOddCentralTail ThetaCuspCoupledOddNeutral

private theorem middle_budget {q : ℝ} (hq : 5 ≤ q) :
    0 < 8*43008^2*q^7/112+
      10000000000000*(101/100:ℝ)^2*(1+9*q/5-2*q^2/5) := by
  by_cases h6 : q ≤ 6
  · let u := 6-q
    let v := q-5
    have hu : 0 ≤ u := by dsimp [u]; linarith
    have hv : 0 ≤ v := by dsimp [v]; linarith
    have hs : u+v=1 := by dsimp [u,v]; ring
    have he : 5*u+6*v=q := by dsimp [u,v]; ring
    have hp : 0 < 8*43008^2*(5*u+6*v)^7/112+
        10000000000000*(101/100:ℝ)^2*((u+v)^2+
          9*(5*u+6*v)*(u+v)/5-2*(5*u+6*v)^2/5)*(u+v)^5 := by
      have huv : 0 < u ∨ 0 < v := by
        by_cases hh : 0 < u
        · exact Or.inl hh
        · exact Or.inr (by linarith)
      rcases huv with hu0 | hv0
      all_goals ring_nf; positivity
    simpa only [he,hs,one_pow,mul_one] using hp
  · let v := q-6
    have hv : 0 ≤ v := by dsimp [v]; linarith
    have he : q=6+v := by dsimp [v]; ring
    rw [he]
    ring_nf
    positivity

private theorem center_lower_middle {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 8) :
    -(8*43008^2*thetaCuspSingleAtomReflectionScale 1 x^7*
        thetaCuspSourceTerm x 1^2)/112 ≤
      10000000000000*thetaCuspCenterCompensationSource x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let F := thetaCuspFullSource x
  let B := 1+9*q/5-2*q^2/5
  have hql : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hF : 0 < F := thetaCuspFullSource_pos_all x
  have hB : B ≤ 0 := by
    have he : B=(5-q)*(2*q+1)/5 := by dsimp [B]; ring
    rw [he]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by dsimp [q]; linarith)
        (by dsimp [q]; linarith)) (by norm_num)
  have hm := pow_le_pow_left₀ hF.le (thetaCuspFullSource_mass_bounds_middle hql).2 2
  have hg := thetaCuspCenterCompensationSource_quadratic_lower_eight hql hqu
  have hb := mul_le_mul_of_nonpos_left hm hB
  have hh : B*((101/100)*f)^2 ≤ thetaCuspCenterCompensationSource x := by
    dsimp [B,q,f,F] at hb ⊢
    nlinarith only [hb,hg]
  have hL := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 10000000000000)
  have hp := mul_nonneg (middle_budget hq).le (sq_nonneg f)
  change (0:ℝ) ≤ (8*43008^2*q^7/112+
    10000000000000*(101/100:ℝ)^2*(1+9*q/5-2*q^2/5))*f^2 at hp
  change -(8*43008^2*q^7*f^2)/112 ≤ _
  dsimp [B] at hL
  nlinarith only [hL,hp]

private theorem center_lower_far {x : ℝ}
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    -(8*43008^2*thetaCuspSingleAtomReflectionScale 1 x^7*
        thetaCuspSourceTerm x 1^2)/112 ≤
      10000000000000*thetaCuspCenterCompensationSource x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos
    (thetaCusp_pos_of_thirtySevenTenths_le (by linarith)) (by norm_num : 0 < (1:ℕ))
  have hg := thetaCuspCenterCompensationSource_scaleSeven_normalized_lower
    (show 7 ≤ thetaCuspSingleAtomReflectionScale 1 x by linarith)
  change -(13/50:ℝ)/7^3 ≤ thetaCuspCenterCompensationSource x/(f^2*q^5) at hg
  have hraw := (le_div_iff₀ (show 0 < f^2*q^5 by positivity)).mp hg
  have hq2 : (64:ℝ) ≤ q^2 := by nlinarith [sq_nonneg (q-8)]
  have hpoly : 0 ≤ (8*43008^2:ℝ)*q^2/112-10000000000000*(13/50)/7^3 := by
    nlinarith only [hq2]
  have hm := mul_nonneg hpoly (show 0 ≤ f^2*q^5 by positivity)
  change -(8*43008^2*q^7*f^2)/112 ≤ _
  nlinarith only [hraw,hm]


private theorem center_lower {C x : ℝ} (hC : 0 ≤ C) (hCU : C ≤ 10000000000000)
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    -(8*43008^2*thetaCuspSingleAtomReflectionScale 1 x^7*
        thetaCuspSourceTerm x 1^2)/112 ≤ C*thetaCuspCenterCompensationSource x := by
  have hbase : -(8*43008^2*thetaCuspSingleAtomReflectionScale 1 x^7*
        thetaCuspSourceTerm x 1^2)/112 ≤
      10000000000000*thetaCuspCenterCompensationSource x := by
    by_cases hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 8
    · exact center_lower_middle hq hqu
    · exact center_lower_far (le_of_not_ge hqu)
  by_cases hG : 0 ≤ thetaCuspCenterCompensationSource x
  · have hq0 : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
    exact (show -(8*43008^2*thetaCuspSingleAtomReflectionScale 1 x^7*
        thetaCuspSourceTerm x 1^2)/112 ≤ 0 by
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by norm_num)).trans (mul_nonneg hC hG)
  · exact hbase.trans (mul_le_mul_of_nonpos_right hCU (le_of_not_ge hG))

/-- A common fixed-coefficient interval preserves a reserve on the entire scale-five ray. -/
theorem native_loaded_coercive {C x : ℝ} (hC : 0 ≤ C) (hCU : C ≤ 10000000000000)
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) (y : Fin 4 → ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let c := (centralBasis (1/q)).mulVec y
    (8*q*thetaCuspSourceTerm x 1^2)/112*(∑ i : Fin 4,y i^2) ≤ coupledOddFourEnergy C x c := by
  dsimp only
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let c := (centralBasis (1/q)).mulVec y
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hc3 : c 3 = -y 3/(43008*q^3) := by
    norm_num [c,centralBasis,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
      Matrix.cons_val_two,Matrix.cons_val_three,
      show (Fin.succ (2:Fin 3) : Fin 4)=3 by rfl]
    field_simp [hq0.ne']
  have hraw := mul_le_mul_of_nonneg_right (center_lower hC hCU hq) (sq_nonneg (c 3))
  have he : -(8*43008^2*q^7*f^2)/112*(c 3)^2 = -(8*q*f^2)/112*(y 3)^2 := by
    rw [hc3]
    field_simp [hq0.ne']
  change -(8*43008^2*q^7*f^2)/112*(c 3)^2 ≤ _ at hraw
  rw [he] at hraw
  have hsum : (y 3)^2 ≤ ∑ i : Fin 4,y i^2 :=
    Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) => sq_nonneg (y i))
      (Finset.mem_univ 3)
  have hdebit := mul_le_mul_of_nonpos_left hsum
    (show -(8*q*f^2)/112 ≤ 0 by
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by norm_num))
  have hbase := native_coupled_coercive hq y
  dsimp only at hbase
  have hE : coupledOddFourEnergy C x c =
      coupledOddFourEnergy 0 x c+C*thetaCuspCenterCompensationSource x*(c 3)^2 := by
    unfold coupledOddFourEnergy
    ring
  change (8*q*f^2)/112*(∑ i : Fin 4,y i^2) ≤ coupledOddFourEnergy C x c
  rw [hE]
  change (8*q*f^2)/56*(∑ i : Fin 4,y i^2) ≤ coupledOddFourEnergy 0 x c at hbase
  linarith only [hbase,hraw,hdebit]


/-- Every coefficient in the common interval repairs the whole scale-five ray. -/
theorem coupledOddFourEnergy_pos_of_scale_five {C x : ℝ}
    (hC : 0 ≤ C) (hCU : C ≤ 10000000000000)
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) (c : Fin 4 → ℝ) (hc : c ≠ 0) :
    0 < coupledOddFourEnergy C x c := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let y := coordinates q c
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hcy : (centralBasis (1/q)).mulVec y=c := by
    funext i
    fin_cases i <;>
      norm_num [y,coordinates,centralBasis,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
        Matrix.cons_val_two,Matrix.cons_val_three,
        show (Fin.succ (2:Fin 3) : Fin 4)=3 by rfl]
    all_goals
      field_simp [hq0.ne']
      ring_nf <;> rfl
  have hy : y ≠ 0 := by
    intro hy
    apply hc
    rw [← hcy,hy]
    simp
  have hsum : 0 < ∑ i : Fin 4,y i^2 := by
    by_contra hn
    have hs : (∑ i : Fin 4,y i^2) ≤ 0 := le_of_not_gt hn
    have hz (i : Fin 4) : y i=0 := by
      have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) =>
        sq_nonneg (y j)) (Finset.mem_univ i)
      nlinarith only [hi,hs,sq_nonneg (y i)]
    exact hy (funext hz)
  have hx := thetaCusp_pos_of_thirtySevenTenths_le (show 37/10 ≤
    thetaCuspSingleAtomReflectionScale 1 x by linarith)
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1:ℕ))
  have hpos : 0 < (8*q*thetaCuspSourceTerm x 1^2)/112*(∑ i : Fin 4,y i^2) := by positivity
  have h := native_loaded_coercive hC hCU hq y
  dsimp only at h
  change (8*q*thetaCuspSourceTerm x 1^2)/112*(∑ i : Fin 4,y i^2) ≤
    coupledOddFourEnergy C x ((centralBasis (1/q)).mulVec y) at h
  rw [hcy] at h
  exact hpos.trans_le h

/-- The same fixed coefficient interval is admissible on the entire adverse source region. -/
theorem coupledOddFourEnergy_pos_of_compensation_neg {C x : ℝ}
    (hC : 0 ≤ C) (hCU : C ≤ 10000000000000) (hx : 0 ≤ x)
    (hG : thetaCuspCenterCompensationSource x < 0) (c : Fin 4 → ℝ) (hc : c ≠ 0) :
    0 < coupledOddFourEnergy C x c :=
  coupledOddFourEnergy_pos_of_scale_five hC hCU
    (ThetaCuspCoupledOddRayModel.five_lt_scale_of_compensation_neg hx hG).le c hc

end
end RHTower.ThetaCuspCoupledOddLoaded
