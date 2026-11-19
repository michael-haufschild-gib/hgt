import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheIntegralOnTheRescaledProductShell
import GaloisForLFunctions.RHTower.SquarefreeCountingAsymptotic

/-!
# Seventh differences across the signed cofactors

For one cofactor v the seventh difference of a quotient mesh on spacing h
costs at most a constant divided by h v⁸. Only quotient samples j up to
the end of the spline support divided by vh can occur.
-/

noncomputable section
open Finset Filter
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.SignedWindowCriticality
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- An iterated difference uses exactly the adjacent samples through v+k. -/
theorem cofactor_difference_local_bound (k : ℕ) (f : ℕ → ℝ) (v : ℕ) {A : ℝ}
    (h : ∀ i ≤ k, |f (v+i)| ≤ A) : |bdiff^[k] f v| ≤ 2^k*A := by
  induction k generalizing v with
  | zero => simpa only [Function.iterate_zero_apply,pow_zero,one_mul,Nat.add_zero] using h 0 le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    apply (abs_sub _ _).trans
    have hl := ih v (fun i hi => h i (hi.trans (Nat.le_succ k)))
    have shifted (i : ℕ) (hi : i ≤ k) : |f ((v+1)+i)| ≤ A := by
      rw [show (v+1)+i=v+(i+1) by omega]
      exact h (i+1) (Nat.succ_le_succ hi)
    have hr := ih (v+1) shifted
    exact (add_le_add hl hr).trans_eq (by rw [pow_succ]; ring)

private theorem seventh_spline_difference :
    ∃ C : ℝ, 0≤C ∧ ∀ {d : ℝ}, 0<d → ∀ v : ℕ,
      |bdiff^[7] (fun i : ℕ => dyadicSpline (i*d)) v| ≤ C*d^7 := by
  obtain ⟨K,hK⟩ := lipschitz_iteratedDeriv_six_dyadicSpline
  refine ⟨7*K,by positivity,fun {d} hd v => ?_⟩
  let x := (v:ℝ)*d
  rw [bdiff_iter_sample_eq,abs_mul]
  norm_num only [abs_pow,abs_neg,abs_one,one_pow,one_mul]
  have he : (fwdDiff d)^[7] dyadicSpline x =
      (fwdDiff d)^[6] dyadicSpline (x+d) - (fwdDiff d)^[6] dyadicSpline x := by
    rw [show 7=6+1 by decide,Function.iterate_succ_apply']; rfl
  obtain ⟨u,hu,heu⟩ := exists_fwdDiff_iter_eq 6 contDiff_six_dyadicSpline hd (x+d)
  obtain ⟨t,ht,het⟩ := exists_fwdDiff_iter_eq 6 contDiff_six_dyadicSpline hd x
  change |(fwdDiff d)^[7] dyadicSpline x| ≤ _
  rw [he,heu,het,←mul_sub,abs_mul,abs_of_pos (pow_pos hd 6)]
  have hdist : |u-t| ≤ 7*d := by
    rw [abs_le]
    have hu' := hu.2
    have ht' := ht.2
    norm_num only [Nat.cast_ofNat] at hu' ht'
    constructor <;> linarith only [hu.1,ht.1,hu',ht',hd]
  have hL : |iteratedDeriv 6 dyadicSpline u-iteratedDeriv 6 dyadicSpline t| ≤ K*|u-t| := by
    simpa only [Real.dist_eq] using hK.dist_le_mul u t
  exact (mul_le_mul_of_nonneg_left (hL.trans (mul_le_mul_of_nonneg_left hdist K.coe_nonneg))
    (pow_nonneg hd.le 6)).trans_eq (by ring)

private theorem bdiff_weighted_sub (k : ℕ) (f g : ℕ → ℝ) (a : ℝ) (v : ℕ) :
    bdiff^[k] (fun i => (f i-g i)*a) v = (bdiff^[k] f v-bdiff^[k] g v)*a := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply',bdiff,ih]
    ring

/-- The cost of a seventh difference decreases like the eighth inverse
power of the cofactor, uniformly in the far quotient endpoint. -/
theorem quotient_mesh_seventh_cofactor_difference :
    ∃ C : ℝ, 0≤C ∧ ∀ (b : ℕ) {h : ℝ}, 0<h → ∀ {v : ℕ}, 0<v →
      |bdiff^[7] (fun i : ℕ => quotientMeshProfile b (i*h)) v| ≤ C/((v:ℝ)^8*h) := by
  obtain ⟨A,hA,ha⟩ := seventh_spline_difference
  obtain ⟨B,hB,hweight⟩ := centeredPrimeWeight_uniform
  let R := 4*Real.exp 8
  have hR : 0<R := by dsimp only [R]; positivity
  have hW (j : ℕ) : |centeredPrimeWeight 1 j| ≤ B := by
    simpa only [Nat.cast_one,mul_one] using hweight (R := 1) le_rfl j
  refine ⟨4*A*B*R^8,by positivity,fun b {h} hh {v} hv => ?_⟩
  have hv' : (0:ℝ)<v := Nat.cast_pos.mpr hv
  let G (j i : ℕ) := dyadicSpline ((i:ℝ)*((j:ℝ)*h))
  let D (j : ℕ) := bdiff^[7] (G j) v
  let H (j : ℕ) := (D j - D (j+1))*centeredPrimeWeight 1 j
  let X := R/((v:ℝ)*h)
  have hX : 0<X := div_pos hR (mul_pos hv' hh)
  have he : (fun i : ℕ => quotientMeshProfile b (i*h)) = fun i =>
      ∑ j ∈ range b, (G j i-G (j+1) i)*centeredPrimeWeight 1 j := by
    funext i
    unfold quotientMeshProfile
    exact sum_congr rfl fun j _ => by dsimp only [G]; rw [mul_left_comm (j:ℝ),mul_left_comm ((j+1:ℕ):ℝ)]
  have zero (j : ℕ) (hj : j=0 ∨ X<j) : D j=0 := by
    apply abs_nonpos_iff.mp
    apply (cofactor_difference_local_bound 7 (G j) v (A := 0) ?_).trans_eq (mul_zero _)
    intro i _
    suffices G j (v+i)=0 by rw [this,abs_zero]
    dsimp only [G]
    rcases hj with rfl | hj
    · rw [Nat.cast_zero,zero_mul,mul_zero]
      apply dyadicSpline_eq_zero_outside
      exact fun hz => (Real.exp_pos (-8)).not_ge hz.1
    apply dyadicSpline_eq_zero_outside
    have hbig := (div_lt_iff₀ (mul_pos hv' hh)).mp hj
    have hinc := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.le_add_right v i) :
      (v:ℝ)≤(v+i:ℕ)) (mul_nonneg (Nat.cast_nonneg j) hh.le)
    exact fun hz => (hbig.trans_le ((le_of_eq (by ring : (j:ℝ)*(v*h)=v*(j*h))).trans hinc)).not_ge hz.2
  have bd (j : ℕ) : |D j| ≤ A*(R/v)^7 := by
    by_cases hj : 0<j ∧ (j:ℝ)≤X
    · have hj' := (le_div_iff₀ (mul_pos hv' hh)).mp hj.2
      have hstep : (j:ℝ)*h ≤ R/v := (le_div_iff₀ hv').mpr (by linarith only [hj'])
      exact (ha (mul_pos (Nat.cast_pos.mpr hj.1) hh) v).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg j) hh.le) hstep 7) hA)
    · rw [zero j (by rcases Nat.eq_zero_or_pos j with h | h
                     · exact Or.inl h
                     · exact Or.inr (lt_of_not_ge (fun hle => hj ⟨h,hle⟩))),abs_zero]
      positivity
  rw [he,bdiff_iter_sum]
  have hsum : (∑ j ∈ range b, bdiff^[7]
      (fun i => (G j i-G (j+1) i)*centeredPrimeWeight 1 j) v) = ∑ j ∈ range b, H j :=
    sum_congr rfl fun j _ => bdiff_weighted_sub 7 (G j) (G (j+1)) _ v
  change |∑ j ∈ range b, bdiff^[7]
    (fun i => (G j i-G (j+1) i)*centeredPrimeWeight 1 j) v| ≤ _
  rw [hsum]
  by_cases h₁ : 1≤X
  swap
  · have zpos (j : ℕ) (hj : 0<j) : D j=0 := zero j (Or.inr ((lt_of_not_ge h₁).trans_le
        (Nat.one_le_cast.mpr hj)))
    have zall (j : ℕ) : D j=0 := (Nat.eq_zero_or_pos j).elim (fun h => zero j (Or.inl h)) (zpos j)
    simp only [H,zall,sub_self,zero_mul,sum_const_zero,abs_zero]
    positivity
  let S := (range b).filter (· ≤ ⌊X⌋₊)
  have ht : ∑ j ∈ S, H j = ∑ j ∈ range b, H j := by
    apply sum_subset (filter_subset _ _)
    intro j hj hjS
    have hj' := lt_of_not_ge fun h => hjS (mem_filter.mpr ⟨hj,h⟩)
    have hxj := (Nat.floor_lt hX.le).mp hj'
    have hxjs := hxj.trans_le (Nat.cast_le.mpr (Nat.le_succ j))
    simp only [H,zero j (Or.inr hxj),zero (j+1) (Or.inr hxjs),sub_self,zero_mul]
  have hc : (S.card:ℝ) ≤ 2*X := by
    have hsub : S ⊆ range (⌊X⌋₊+1) := fun j hj => mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hj).2)
    have hn := (card_le_card hsub).trans_eq (card_range _)
    have hnr : (S.card:ℝ)≤(⌊X⌋₊:ℝ)+1 := by exact_mod_cast hn
    linarith only [hnr,Nat.floor_le hX.le,h₁]
  let U := (2*(A*(R/v)^7))*B
  have hU : 0≤U := by dsimp only [U]; positivity
  rw [←ht]
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ _j ∈ S, U := by
            apply sum_le_sum
            intro j _
            dsimp only [H]
            rw [abs_mul]
            exact mul_le_mul ((abs_sub _ _).trans ((add_le_add (bd j) (bd (j+1))).trans_eq (by ring)))
              (hW j) (abs_nonneg _) (by positivity)
       _ ≤ 2*X*U := by rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hc hU
       _ = _ := by dsimp only [U,X]; field_simp [hh.ne',hv'.ne']; ring

/-- Beyond the spline support every quotient sample vanishes. -/
theorem quotient_mesh_after_support (b : ℕ) {x : ℝ} (hx : 4*Real.exp 8<x) :
    quotientMeshProfile b x=0 := by
  have hx0 : 0<x := (by positivity : 0<4*Real.exp 8).trans hx
  have hz (j : ℕ) : dyadicSpline (j*x)=0 := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [dyadicSpline]
    · exact dyadicSpline_eq_zero_outside fun h => (hx.trans_le
        (le_mul_of_one_le_left hx0.le (Nat.one_le_cast.mpr hj))).not_ge h.2
  unfold quotientMeshProfile
  exact sum_eq_zero fun j _ => by rw [hz,hz,sub_self,zero_mul]

/-- The first positive quotient returns the one-cell spline sample. -/
def positiveCofactorProfile (b : ℕ) (h : ℝ) (v : ℕ) :=
  quotientMeshProfile b (v*h)-quotientMeshProfile 1 (v*h)

/-- Summing the seventh cofactor differences above a sharp lower endpoint
costs its seventh inverse power, with the returned first sample included. -/
theorem positive_cofactor_tail_variation :
    ∃ A : ℝ, 0≤A ∧ ∀ b m : ℕ, ∀ {D : ℕ}, 0<D → ∀ {h : ℝ}, 0<h →
      (∑ v ∈ Ioc D m, |bdiff^[7] (positiveCofactorProfile b h) v|) ≤ A/(h*(D:ℝ)^7) := by
  obtain ⟨C,hC,hdiff⟩ := quotient_mesh_seventh_cofactor_difference
  refine ⟨2*C,by positivity,fun b m {D} hD {h} hh => ?_⟩
  have hd : (0:ℝ)<D := Nat.cast_pos.mpr hD
  let A := (2*C)/((D:ℝ)^6*h)
  have hA : 0≤A := by dsimp only [A]; positivity
  have cell (v : ℕ) (hv : v ∈ Ioc D m) :
      |bdiff^[7] (positiveCofactorProfile b h) v| ≤ A*(1/(v:ℝ)^2) := by
    have hDv := (mem_Ioc.mp hv).1
    have hv0 := hD.trans hDv
    have hv' : (0:ℝ)<v := Nat.cast_pos.mpr hv0
    have he := bdiff_weighted_sub 7 (fun i : ℕ => quotientMeshProfile b (i*h))
      (fun i : ℕ => quotientMeshProfile 1 (i*h)) 1 v
    simp only [mul_one] at he
    change |bdiff^[7] (fun i : ℕ => quotientMeshProfile b (i*h)-quotientMeshProfile 1 (i*h)) v| ≤ _
    rw [he]
    apply (abs_sub _ _).trans ((add_le_add (hdiff b hh hv0) (hdiff 1 hh hv0)).trans _)
    have hpow := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd.le (Nat.cast_le.mpr hDv.le) 6)
      (sq_nonneg (v:ℝ))
    have hden : (D:ℝ)^6*(v:ℝ)^2*h ≤ (v:ℝ)^8*h := by
      exact mul_le_mul_of_nonneg_right (hpow.trans_eq (by ring)) hh.le
    calc _ = (2*C)/((v:ℝ)^8*h) := by ring
         _ ≤ (2*C)/((D:ℝ)^6*(v:ℝ)^2*h) := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
         _ = _ := by dsimp only [A]; field_simp [hd.ne',hv'.ne',hh.ne']
  apply (sum_le_sum cell).trans
  rw [←mul_sum]
  have he : Ioc D m = Icc (D+1) m := by ext v; simp only [mem_Ioc,mem_Icc]; omega
  rw [he]
  exact (mul_le_mul_of_nonneg_left (_root_.RHTower.sum_inv_sq_tail_le hD m) hA).trans_eq
    (by dsimp only [A]; field_simp [hd.ne',hh.ne'])

#print axioms positive_cofactor_tail_variation
#print axioms quotient_mesh_seventh_cofactor_difference
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
