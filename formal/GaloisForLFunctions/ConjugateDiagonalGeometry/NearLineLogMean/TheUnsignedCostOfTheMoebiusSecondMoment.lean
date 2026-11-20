import GaloisForLFunctions.ArithmeticCountingPositivity.SquarefreePairsAtEveryShortOrdinaryLag
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PrimitiveSpectrumOfTheMoebiusGram
import GaloisForLFunctions.RHTower.DirichletPolynomialSincEnergy
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Short lags force linear unsigned Möbius off-diagonal cost

In the exact second moment on [1,T], a squarefree pair whose lower
index is at least T times its separation has a positive cosine kernel.
There are enough such pairs at every short separation to force total
absolute off-diagonal mass comparable to the length of the polynomial.
-/
noncomputable section
open Finset Filter MeasureTheory
open _root_.RHTower
open GaloisForLFunctions.ArithmeticCountingPositivity
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram

/-- Absolute size of one off-diagonal term after integration in time. -/
def absoluteWindowTerm (T : ℝ) (m n : ℕ) : ℝ :=
  |coeff m*coeff n*cosInt (Real.log (m:ℝ)-Real.log (n:ℝ)) 1 (T-1)|

def absoluteMoebiusOffDiagonal (N : ℕ) (T : ℝ) : ℝ :=
  ∑ m ∈ Icc 1 N,∑ n ∈ (Icc 1 N).erase m,absoluteWindowTerm T m n

private theorem cosine_window_lower {u T : ℝ} (hT : 1≤T) (hu : 0≤u) (hus : u*T≤1) :
    (T-1)/2 ≤ cosInt u 1 (T-1) := by
  rw [←integral_cos_lin_eq,show 1+(T-1)=T by ring]
  have hpt (t : ℝ) (ht : t∈Set.Icc 1 T) : 1/2≤Real.cos (u*t) := by
    have hh : u*t≤1 := (mul_le_mul_of_nonneg_left ht.2 hu).trans hus
    rw [←Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg hu (zero_le_one.trans ht.1))
      (by linarith only [Real.pi_pos]) (by linarith only [hh,Real.pi_gt_three])
  have h := intervalIntegral.integral_mono_on hT
    (intervalIntegrable_const (μ:=volume) (c:=(1/2:ℝ)))
    ((by fun_prop : Continuous (fun t : ℝ => Real.cos (u*t))).intervalIntegrable _ _) hpt
  simpa only [intervalIntegral.integral_const,smul_eq_mul,div_eq_mul_inv,one_mul] using h

private theorem abs_coeff_squarefree {n : ℕ} (hn : Squarefree n) : |coeff n|=1/Real.sqrt n := by
  have h : |mobiusRealCoefficient n|=1 := by
    unfold mobiusRealCoefficient
    exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree hn
  rw [coeff,abs_div,h,abs_of_nonneg (Real.sqrt_nonneg _)]

/-- Every squarefree pair in the near-diagonal band has the same
time-kernel sign and a termwise lower bound at the final scale N. -/
theorem absolute_window_term_on_squarefree_band {N b J m : ℕ} {T : ℝ}
    (hT : 1≤T) (hb : (T+1)*(b:ℝ)≤J) (hm : m∈squarefreeShiftEndpoints N b J) :
    (T-1)/(2*N) ≤ absoluteWindowTerm T m (m-b) := by
  obtain ⟨hn,hmN,hJ,hs,hs'⟩ := mem_squarefree_shift_endpoints.mp hm
  let n := m-b
  have h1 : 0<(n:ℝ) := Nat.cast_pos.mpr hn
  have hm1 : 0<(m:ℝ) := Nat.cast_pos.mpr (by omega : 0 < m)
  have hN1 : 0<(N:ℝ) := Nat.cast_pos.mpr (by omega : 0<N)
  have hnm : (n:ℝ) ≤ m := Nat.cast_le.mpr (Nat.sub_le _ _)
  have hnm' : (n:ℝ)+b=m := by exact_mod_cast (show n+b=m by dsimp only [n]; omega)
  let u := Real.log (m:ℝ)-Real.log (n:ℝ)
  have hu : 0≤u := sub_nonneg.mpr (Real.log_le_log h1 hnm)
  have hlog : u ≤ (b:ℝ)/n := by
    have h := Real.log_le_sub_one_of_pos (div_pos hm1 h1)
    rw [Real.log_div hm1.ne' h1.ne'] at h
    apply h.trans_eq
    field_simp; linarith only [hnm']
  have hJm : (J:ℝ) ≤ m := Nat.cast_le.mpr hJ
  have hnj : T*(b:ℝ) ≤ n := by linarith only [hb,hJm,hnm']
  have hus : u*T≤1 := by
    have h := mul_le_mul_of_nonneg_right hlog (zero_le_one.trans hT)
    exact h.trans (by rw [div_mul_eq_mul_div,div_le_one h1]; linarith only [hnj])
  have hk := cosine_window_lower hT hu hus
  have den := mul_pos (Real.sqrt_pos.mpr hm1) (Real.sqrt_pos.mpr h1)
  have hden : Real.sqrt (m:ℝ)*Real.sqrt (n:ℝ) ≤ N := by
    rw [←Real.sqrt_mul hm1.le]
    have h := Real.sqrt_le_sqrt (mul_le_mul (Nat.cast_le.mpr hmN)
      (hnm.trans (Nat.cast_le.mpr hmN)) h1.le hN1.le)
    simpa only [←sq,Real.sqrt_sq hN1.le] using h
  have hw := one_div_le_one_div_of_le den hden
  have hkn := (by linarith only [hT] : 0≤(T-1)/2).trans hk
  change _ ≤ |coeff m*coeff n*cosInt u 1 (T-1)|
  rw [abs_mul,abs_mul,abs_coeff_squarefree hs,abs_coeff_squarefree hs',abs_of_nonneg hkn]
  calc _ = (1/(N:ℝ))*((T-1)/2) := by field_simp
       _ ≤ 1/(Real.sqrt (m:ℝ)*Real.sqrt (n:ℝ))*cosInt u 1 (T-1) :=
          mul_le_mul hw hk (by linarith only [hT]) (one_div_nonneg.mpr den.le)
       _ = _ := by ring

/-- At every affordable lag the unsigned contribution of genuine
integer pairs is at least the squarefree surplus times their minimum
integrated weight. -/
theorem unsigned_moebius_cost_at_each_lag {N b J : ℕ} {T : ℝ}
    (hT : 1≤T) (hb : (T+1)*(b:ℝ)≤J) :
    ((N:ℝ)/36-b-J)*((T-1)/(2*N)) ≤
      ∑ m ∈ squarefreeShiftEndpoints N b J,absoluteWindowTerm T m (m-b) := by
  have hn : 0≤(T-1)/(2*N) := div_nonneg (sub_nonneg.mpr hT) (by positivity)
  have h := sum_le_sum (s:=squarefreeShiftEndpoints N b J) (fun m hm =>
    absolute_window_term_on_squarefree_band hT hb hm)
  rw [sum_const,nsmul_eq_mul] at h
  exact (mul_le_mul_of_nonneg_right (squarefree_shift_endpoints_lower N b J) hn).trans h

private theorem lag_sum_le_absolute (N L J : ℕ) (T : ℝ) :
    (∑ b ∈ Icc 1 L,∑ m ∈ squarefreeShiftEndpoints N b J,absoluteWindowTerm T m (m-b)) ≤
      absoluteMoebiusOffDiagonal N T := by
  classical
  let S := Icc 1 N
  let B := Icc 1 L
  let P := fun b => squarefreeShiftEndpoints N b J
  have hsub (b : ℕ) : P b ⊆ S := by
    intro m hm
    obtain ⟨hn,hmN,_,_,_⟩ := mem_squarefree_shift_endpoints.mp hm
    exact mem_Icc.mpr ⟨by omega,hmN⟩
  have hmask (b : ℕ) : ∑ m ∈ P b,absoluteWindowTerm T m (m-b) =
      ∑ m ∈ S, if m∈P b then absoluteWindowTerm T m (m-b) else 0 := by
    rw [←sum_filter]
    have he : S.filter (fun m => m∈P b)=P b := by
      ext m; exact mem_filter.trans ⟨And.right,fun h => ⟨hsub b h,h⟩⟩
    rw [he]
  change (∑ b ∈ B,∑ m ∈ P b,_) ≤ ∑ m ∈ S,∑ n ∈ S.erase m,_
  simp_rw [hmask]
  rw [sum_comm]
  refine sum_le_sum fun m hm => ?_
  rw [←sum_filter]
  let D := B.filter (fun b => m∈P b)
  have hinj : Set.InjOn (fun b => m-b) (↑D : Set ℕ) := by
    intro a ha b hb he
    change m-a=m-b at he
    have ha' := (mem_squarefree_shift_endpoints.mp (mem_filter.mp ha).2).1
    have hb' := (mem_squarefree_shift_endpoints.mp (mem_filter.mp hb).2).1
    omega
  have hd : D.image (fun b => m-b) ⊆ S.erase m := by
    intro n hn
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hn
    have hbpos := (mem_Icc.mp (mem_filter.mp hb).1).1
    have hnpos := (mem_squarefree_shift_endpoints.mp (mem_filter.mp hb).2).1
    have hmN := (mem_Icc.mp hm).2
    exact mem_erase.mpr ⟨by omega,mem_Icc.mpr ⟨hnpos,by omega⟩⟩
  calc (∑ b ∈ D,absoluteWindowTerm T m (m-b)) =
         ∑ n ∈ D.image (fun b => m-b),absoluteWindowTerm T m n := (sum_image hinj).symm
       _ ≤ _ := sum_le_sum_of_subset_of_nonneg hd (fun _ _ _ => abs_nonneg _)

/-- At all long enough lengths, even the exact integrated cosine
coefficients have unsigned off-diagonal cost at least N/165888. -/
theorem linear_unsigned_moebius_window_cost {N : ℕ} {T : ℝ} (hT : 2≤T)
    (hN : 288*(T+1)≤N) : (N:ℝ)/165888 ≤ absoluteMoebiusOffDiagonal N T := by
  let X := (N:ℝ)/(144*(T+1))
  let L := ⌊X⌋₊
  let J := N/72
  have ht1 : 0<T+1 := by linarith only [hT]
  have nt : 0<(N:ℝ) := by linarith only [hT,hN]
  have hx : 2≤X := (le_div_iff₀ (by positivity : 0<144*(T+1))).mpr (by linarith only [hN])
  have hL : X/2 ≤ (L:ℝ) := by linarith only [Nat.lt_floor_add_one X,hx]
  have hL' : (L:ℝ) ≤ X := Nat.floor_le (by linarith only [hx])
  have hpaid := (le_div_iff₀ (by positivity : 0<144*(T+1))).mp hL'
  have hJ : (N:ℝ)/144 ≤ J := by
    have hN' : 144≤N := by exact_mod_cast (show (144:ℝ)≤N by linarith only [hN,hT])
    have hm : (N:ℝ) ≤ 144*J := by exact_mod_cast (show N≤144*J by dsimp only [J]; omega)
    exact (div_le_iff₀ (by norm_num : (0:ℝ)<144)).mpr (by linarith only [hm])
  have hJ' : (J:ℝ) ≤ (N:ℝ)/72 := by
    exact (Nat.cast_div_le : ((N/72:ℕ):ℝ) ≤ (N:ℝ)/((72:ℕ):ℝ))
  have hrow (b : ℕ) (hb : b∈Icc 1 L) : (T-1)/192 ≤
      ∑ m ∈ squarefreeShiftEndpoints N b J,absoluteWindowTerm T m (m-b) := by
    have hbl : (b:ℝ) ≤ L := Nat.cast_le.mpr (mem_Icc.mp hb).2
    have hbs : (T+1)*(b:ℝ)≤N/144 := by
      linarith only [mul_le_mul_of_nonneg_left hbl ht1.le,hpaid]
    have hbnd : (b:ℝ)≤(N:ℝ)/288 := by
      nlinarith only [hbs,mul_nonneg (Nat.cast_nonneg (α:=ℝ) b) (by linarith only [hT] : 0≤T-1)]
    have hs := unsigned_moebius_cost_at_each_lag (N:=N) (by linarith only [hT]) (hbs.trans hJ)
    have hc : (N:ℝ)/96 ≤ (N:ℝ)/36-b-J := by linarith only [hbnd,hJ']
    have hf := mul_le_mul_of_nonneg_right hc (div_nonneg (by linarith only [hT] : 0≤T-1)
      (by positivity : 0≤2*(N:ℝ)))
    exact (show (T-1)/192=((N:ℝ)/96)*((T-1)/(2*N)) by field_simp; ring).le.trans (hf.trans hs)
  have hsum := sum_le_sum hrow
  rw [sum_const,nsmul_eq_mul,Nat.card_Icc] at hsum
  simp only [Nat.add_sub_cancel] at hsum
  have hbal : (T+1)/3 ≤ T-1 := by linarith only [hT]
  have hmul := mul_le_mul hL hbal (by positivity : 0≤(T+1)/3) (Nat.cast_nonneg L)
  have heq : (X/2)*((T+1)/3)=(N:ℝ)/864 := by dsimp only [X]; field_simp; norm_num
  rw [heq] at hmul
  exact (by linarith only [hmul] : (N:ℝ)/165888 ≤ (L:ℝ)*((T-1)/192)).trans
    (hsum.trans (lag_sum_le_absolute N L J T))

/-- Pricing exact off-diagonal terms separately cannot give a height
exponent independent of length in the polynomial-length experiment.
The failure holds at every sufficiently large real height. -/
theorem every_polynomial_height_cost_fails_unsigned {θ K : ℝ} (hθ : 1<θ) (hK : K<θ) (C : ℝ) :
    ∀ᶠ T : ℝ in atTop, C*T^K < absoluteMoebiusOffDiagonal ⌊T^θ⌋₊ T := by
  filter_upwards [eventually_ge_atTop (2:ℝ),
    (tendsto_rpow_atTop (sub_pos.mpr hθ)).eventually_ge_atTop 1152,
    (tendsto_rpow_atTop (sub_pos.mpr hK)).eventually_gt_atTop (331776*|C|)] with T hT hwide hprice
  have hp : 0<T := by linarith only [hT]
  have hgrow := mul_le_mul_of_nonneg_right hwide hp.le
  change 1152*T ≤ T^(θ-1)*T at hgrow
  have hlarge : 1152*T≤T^θ := by
    calc _ ≤ T^(θ-1)*T := hgrow
         _ = T^(θ-1)*T^(1:ℝ) := by rw [Real.rpow_one]
         _ = _ := by rw [←Real.rpow_add hp,sub_add_cancel]
  have hhalf : T^θ/2 ≤ (⌊T^θ⌋₊:ℝ) := by linarith only [Nat.lt_floor_add_one (T^θ),hlarge,hT]
  have hfit : 288*(T+1) ≤ (⌊T^θ⌋₊:ℝ) := by linarith only [hhalf,hlarge,hT]
  have hpaid := mul_lt_mul_of_pos_right hprice (Real.rpow_pos_of_pos hp K)
  change 331776 * |C| * T^K < T^(θ-K)*T^K at hpaid
  rw [←Real.rpow_add hp,sub_add_cancel] at hpaid
  have hC := mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hp.le K)
  exact (by linarith only [hpaid,hhalf,hC] : C*T^K < (⌊T^θ⌋₊:ℝ)/165888).trans_le
    (linear_unsigned_moebius_window_cost hT hfit)

#print axioms every_polynomial_height_cost_fails_unsigned
#print axioms absolute_window_term_on_squarefree_band
#print axioms unsigned_moebius_cost_at_each_lag
#print axioms linear_unsigned_moebius_window_cost
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
