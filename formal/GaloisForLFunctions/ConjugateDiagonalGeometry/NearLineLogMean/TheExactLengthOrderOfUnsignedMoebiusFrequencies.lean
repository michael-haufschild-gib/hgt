import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheUnsignedCostOfTheMoebiusSecondMoment
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheArchimedeanCrossEnergyIsOneSided
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import GaloisForLFunctions.HTGeometry.GammaRootAsymptotic

/-!
# The upper order of the absolute Möbius frequency cost

The arithmetic-geometric mean inequality separates the two coefficients
of a cosine atom. The reciprocal logarithmic gaps then enter through
a single row sum, giving a bound uniform over all placements in time.
-/
noncomputable section
open Filter Finset Topology
open _root_.RHTower _root_.RHTower.Sieve
open GaloisForLFunctions.ArithmeticLorentzianGeometry
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram

private def gapReciprocal (m n : ℕ) := 1 / |Real.log (n:ℝ)-Real.log (m:ℝ)|

private theorem gap_symmetric (m n : ℕ) : gapReciprocal m n=gapReciprocal n m := by
  unfold gapReciprocal; rw [abs_sub_comm]

private theorem row_le {m N : ℕ} (hm : m ∈ Icc 1 N) :
    ∑ n ∈ Icc 1 N,gapReciprocal m n ≤ 2*m*(1+Real.log ((N:ℝ)+1))+N := by
  refine Eq.trans_le ?_ (sum_inv_abs_log_sub_le hm)
  refine sum_congr rfl fun n _ => ?_
  by_cases he : m=n
  · simp [he,gapReciprocal]
  · simp [he,gapReciprocal]

private theorem coefficient_sq_le (n : ℕ) : |coeff n|^2 ≤ 1/(n:ℝ) := by
  have h : |mobiusRealCoefficient n| ≤ 1 := by
    unfold mobiusRealCoefficient; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hs := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs,one_pow] at hs
  rw [sq_abs,coeff,div_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right hs (Nat.cast_nonneg _)

private theorem absolute_term_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (he : m≠n) (T : ℝ) :
    absoluteWindowTerm T m n ≤ (1/(m:ℝ)+1/(n:ℝ))*gapReciprocal m n := by
  have hg : Real.log (m:ℝ)-Real.log (n:ℝ) ≠ 0 := by
    intro hh
    apply he
    exact_mod_cast Real.log_injOn_pos (Set.mem_Ioi.mpr (Nat.cast_pos.mpr hm))
      (Set.mem_Ioi.mpr (Nat.cast_pos.mpr hn)) (sub_eq_zero.mp hh)
  have hk := abs_cosInt_le _ 1 (T-1) hg
  have hcoeff : 2*(|coeff m| * |coeff n|) ≤ 1/(m:ℝ)+1/(n:ℝ) := by
    linarith only [sq_nonneg (|coeff m|-|coeff n|),coefficient_sq_le m,coefficient_sq_le n]
  rw [absoluteWindowTerm,abs_mul,abs_mul]
  refine (mul_le_mul_of_nonneg_left hk (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans ?_
  have h := mul_le_mul_of_nonneg_right hcoeff (show 0 ≤ gapReciprocal m n by unfold gapReciprocal; positivity)
  unfold gapReciprocal at h ⊢
  rw [abs_sub_comm (Real.log (m:ℝ)) (Real.log (n:ℝ))]
  calc
    _ = 2*(|coeff m| * |coeff n|)*(1/|Real.log (n:ℝ)-Real.log (m:ℝ)|) := by
      simp only [div_eq_mul_inv,one_mul]
      ring
    _ ≤ _ := h

/-- Uniform upper bound for the absolute values of already integrated
off-diagonal terms. Only one logarithm of the polynomial length is lost. -/
theorem absolute_moebius_frequency_cost_upper {N : ℕ} (hn : 1 ≤ N) (T : ℝ) :
    absoluteMoebiusOffDiagonal N T ≤ 6*(N:ℝ)*(1+Real.log ((N:ℝ)+1)) := by
  let S := Icc 1 N
  let w := fun m : ℕ => 1/(m:ℝ)
  let B := 1+Real.log ((N:ℝ)+1)
  have wpos (m : ℕ) : 0 ≤ w m := one_div_nonneg.mpr (Nat.cast_nonneg _)
  have one_row (m : ℕ) (hm : m ∈ S) :
      ∑ n ∈ S.erase m,absoluteWindowTerm T m n ≤
        ∑ n ∈ S,(w m+w n)*gapReciprocal m n := by
    have hc := sum_le_sum (s:=S.erase m) (fun n hh => absolute_term_le (mem_Icc.mp hm).1
      (mem_Icc.mp (mem_of_mem_erase hh)).1 (ne_of_mem_erase hh).symm T)
    refine hc.trans (sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun n _ _ => ?_))
    exact mul_nonneg (add_nonneg (wpos m) (wpos n)) (one_div_nonneg.mpr (abs_nonneg _))
  have hs : (∑ m ∈ S,∑ n ∈ S,w n*gapReciprocal m n) =
      ∑ m ∈ S,∑ n ∈ S,w m*gapReciprocal m n := by
    rw [sum_comm]
    exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => congrArg (w m * ·) (gap_symmetric n m)
  have hcalc : (∑ m ∈ S,∑ n ∈ S,(w m+w n)*gapReciprocal m n) =
      2*∑ m ∈ S,w m*(∑ n ∈ S,gapReciprocal m n) := by
    simp_rw [add_mul,sum_add_distrib]
    rw [hs,←two_mul]
    congr 1
    exact sum_congr rfl fun m _ => by rw [mul_sum]
  have hsingle (m : ℕ) (hm : m ∈ S) :
      w m*(∑ n ∈ S,gapReciprocal m n) ≤ 2*B+(N:ℝ)*w m := by
    have hp : 0 < (m:ℝ) := Nat.cast_pos.mpr (mem_Icc.mp hm).1
    refine (mul_le_mul_of_nonneg_left (row_le hm) (wpos m)).trans_eq ?_
    change (1/(m:ℝ))*(2*m*B+N)=2*B+N*(1/(m:ℝ))
    field_simp
  have hsub := sum_le_sum hsingle
  rw [sum_add_distrib,sum_const,nsmul_eq_mul,←mul_sum] at hsub
  have hc : S.card=N := by dsimp [S]; rw [Nat.card_Icc]; omega
  rw [hc] at hsub
  have hH : ∑ n ∈ S,w n ≤ B :=
    (sum_Icc_one_div_le_one_add_log N).trans (add_le_add le_rfl
      (Real.log_le_log (Nat.cast_pos.mpr hn) (by linarith only [] : (N:ℝ) ≤ N+1)))
  have h := sum_le_sum one_row
  rw [hcalc] at h
  change absoluteMoebiusOffDiagonal N T ≤ 2*∑ m ∈ S,w m*(∑ n ∈ S,gapReciprocal m n) at h
  change absoluteMoebiusOffDiagonal N T ≤ 6*(N:ℝ)*B
  linarith only [h,hsub,mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg N)]

/-- The unsigned cost has logarithmic order one in the length,
uniformly even when the height moves with the cutoff. -/
theorem unsigned_cost_length_order {ι : Type*} {l : Filter ι} {n : ι → ℕ} {t : ι → ℝ}
    (hn : Tendsto n l atTop) (ht : ∀ᶠ i in l, 2 ≤ t i)
    (hfit : ∀ᶠ i in l, 288*(t i+1) ≤ (n i:ℝ)) :
    Tendsto (fun i => Real.log (absoluteMoebiusOffDiagonal (n i) (t i)) /
      Real.log ((n i:ℝ)+1)) l (𝓝 1) := by
  let X := fun i => (n i:ℝ)+1
  have hx : Tendsto X l atTop := tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.comp hn)
  have hl := Real.tendsto_log_atTop.comp hx
  have hconst (c : ℝ) : Tendsto (fun i => c/Real.log (X i)) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop hl
  have hlog := (GaloisForLFunctions.HTGeometry.tendsto_log_linear_div (c:=1) zero_lt_one 1).comp hl
  have hlog' : Tendsto (fun i => Real.log (1+Real.log (X i))/Real.log (X i)) l (𝓝 0) := by
    change Tendsto (fun i => Real.log (1*Real.log (X i)+1)/Real.log (X i)) l (𝓝 0) at hlog
    simpa only [one_mul,add_comm (Real.log _) 1] using hlog
  have hlo := (tendsto_const_nhds (x:=1) (f:=l)).sub (hconst (Real.log 331776))
  have hup := ((tendsto_const_nhds (x:=1) (f:=l)).add (hconst (Real.log 6))).add hlog'
  rw [sub_zero] at hlo
  rw [add_zero,add_zero] at hup
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
  · filter_upwards [hn.eventually_ge_atTop 1,ht,hfit] with i hN hT hF
    have hr : (1:ℝ) ≤ n i := Nat.one_le_cast.mpr hN
    have hx1 : 1 < X i := by dsimp [X]; linarith only [hr]
    have hx0 := zero_lt_one.trans hx1
    have hpaid := linear_unsigned_moebius_window_cost hT hF
    have hlow : X i/331776 ≤ absoluteMoebiusOffDiagonal (n i) (t i) := by
      dsimp only [X]; linarith only [hpaid,hr]
    have h := Real.log_le_log (div_pos hx0 (by norm_num)) hlow
    rw [Real.log_div hx0.ne' (by norm_num)] at h
    have hdiv := div_le_div_of_nonneg_right h (Real.log_pos hx1).le
    rw [sub_div,div_self (Real.log_pos hx1).ne'] at hdiv
    exact hdiv
  · filter_upwards [hn.eventually_ge_atTop 1,ht,hfit] with i hN hT hF
    have hp : 0 < (n i:ℝ) := Nat.cast_pos.mpr hN
    have hx1 : 1 < X i := by dsimp [X]; linarith only [hp]
    have hxpos := zero_lt_one.trans hx1
    have hL := Real.log_pos hx1
    have hb : 0 < 1+Real.log (X i) := by linarith only [hL]
    have hpos := (div_pos hp (by norm_num : (0:ℝ)<165888)).trans_le (linear_unsigned_moebius_window_cost hT hF)
    have hcap := absolute_moebius_frequency_cost_upper hN (t i)
    have hnx : (n i:ℝ) ≤ X i := by dsimp [X]; linarith only []
    have hcap' : absoluteMoebiusOffDiagonal (n i) (t i) ≤ 6*X i*(1+Real.log (X i)) :=
      hcap.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnx (by norm_num)) hb.le)
    have h := Real.log_le_log hpos hcap'
    rw [Real.log_mul (by positivity : 6*X i≠0) hb.ne',Real.log_mul (by norm_num) (zero_lt_one.trans hx1).ne'] at h
    have hd := div_le_div_of_nonneg_right h hL.le
    rw [add_div,add_div,div_self hL.ne'] at hd
    linarith only [hd]

/-- At every fixed polynomial length exponent above one the exact
unsigned time exponent equals that length exponent. -/
theorem unsigned_cost_polynomial_order {θ : ℝ} (hθ : 1 < θ) :
    Tendsto (fun T : ℝ => Real.log (absoluteMoebiusOffDiagonal ⌊T^θ⌋₊ T)/Real.log T) atTop (𝓝 θ) := by
  have hθ0 := zero_lt_one.trans hθ
  have hg := tendsto_rpow_atTop hθ0
  have hn := tendsto_nat_floor_atTop.comp hg
  have hfit : ∀ᶠ T : ℝ in atTop, 288*(T+1) ≤ (⌊T^θ⌋₊:ℝ) := by
    filter_upwards [eventually_ge_atTop (2:ℝ),
      (tendsto_rpow_atTop (sub_pos.mpr hθ)).eventually_ge_atTop 1152] with T ht h
    have hp := (by linarith only [ht] : 0 < T)
    have hw := mul_le_mul_of_nonneg_right h hp.le
    change 1152*T ≤ T^(θ-1)*T at hw
    have he : T^(θ-1)*T = T^θ := by
      calc _ = T^(θ-1)*T^(1:ℝ) := by rw [Real.rpow_one]
           _ = _ := by rw [←Real.rpow_add hp,sub_add_cancel]
    rw [he] at hw
    linarith only [Nat.lt_floor_add_one (T^θ),hw,ht]
  have hc := unsigned_cost_length_order (n:=fun T : ℝ => ⌊T^θ⌋₊) (t:=id) hn
    (eventually_ge_atTop 2) hfit
  have hl : Tendsto (fun T : ℝ => Real.log ((⌊T^θ⌋₊:ℝ)+1)/Real.log T) atTop (𝓝 θ) := by
    have hzero : Tendsto (fun T : ℝ => Real.log 2/Real.log T) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    have hup := (tendsto_const_nhds (x:=θ) (f:=atTop)).add hzero
    rw [add_zero] at hup
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    · filter_upwards [eventually_gt_atTop (1:ℝ)] with T ht
      have hp := zero_lt_one.trans ht
      have hh := Real.log_le_log (Real.rpow_pos_of_pos hp θ) (Nat.lt_floor_add_one (T^θ)).le
      rw [Real.log_rpow hp] at hh
      exact (le_div_iff₀ (Real.log_pos ht)).mpr hh
    · filter_upwards [eventually_gt_atTop (1:ℝ)] with T ht
      have hp := zero_lt_one.trans ht
      have hfloor := Nat.floor_le (Real.rpow_nonneg hp.le θ)
      have hpow := Real.one_le_rpow ht.le hθ0.le
      have h := Real.log_le_log (by positivity : 0 < (⌊T^θ⌋₊:ℝ)+1)
        (show (⌊T^θ⌋₊:ℝ)+1 ≤ 2*T^θ by linarith only [hfloor,hpow])
      rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hp θ).ne',Real.log_rpow hp] at h
      have h' := div_le_div_of_nonneg_right h (Real.log_pos ht).le
      rw [add_div,mul_div_cancel_right₀ _ (Real.log_pos ht).ne'] at h'
      linarith only [h']
  have h := hc.mul hl
  rw [one_mul] at h
  apply h.congr'
  filter_upwards [hn.eventually_ge_atTop 1] with T hT
  have hp : 0 < (⌊T^θ⌋₊:ℝ) := Nat.cast_pos.mpr hT
  have hP := (Real.log_pos (by linarith only [hp] : 1 < (⌊T^θ⌋₊:ℝ)+1)).ne'
  change (_/Real.log ((⌊T^θ⌋₊:ℝ)+1))*(Real.log ((⌊T^θ⌋₊:ℝ)+1)/Real.log T) = _
  exact div_mul_div_cancel₀ hP

#print axioms absolute_moebius_frequency_cost_upper
#print axioms unsigned_cost_length_order
#print axioms unsigned_cost_polynomial_order
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
