import GaloisForLFunctions.ExceptionalLayerTheory.AveragingTheCoprimeComplementaryTail

/-!
# Tapering the complementary factor at both Vaughan widths

The complementary cutoff starts strictly below the square root. Its
averaging length is the square root divided by that cutoff, rounded up.
The power margin in the first prime makes the original lower product
cutoff inactive throughout the discarded tail.
-/

noncomputable section
open Finset ArithmeticFunction RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Beginning of the taper in the complementary factor. -/
def complementTaperStart (X : ℕ) := ⌊(X : ℝ)^(499999999/1000000000 : ℝ)⌋₊

/-- The far end of the taper stays within three times the lower power
scale, including the rounding in its length. -/
theorem complementTaper_endpoint {X : ℕ} (hx : 1≤X) :
    let A := complementTaperStart X
    let S := ⌊Real.sqrt X/(A+1 : ℕ)⌋₊+1
    ((A+S : ℕ) : ℝ)≤3*(X : ℝ)^(499999999/1000000000 : ℝ) := by
  intro A S
  let P (s : ℝ) := (X : ℝ)^s
  let u : ℝ := 499999999/1000000000
  let v : ℝ := 1/1000000000
  have hx₁ : (1 : ℝ)≤X := by exact_mod_cast hx
  have ha : (A : ℝ)≤P u := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg X) u)
  have ha' : P u≤((A+1 : ℕ) : ℝ) := by push_cast; exact (Nat.lt_floor_add_one _).le
  have hprod : P v*P u=Real.sqrt X := by
    dsimp only [P]
    rw [←Real.rpow_add (zero_lt_one.trans_le hx₁),show v+u=1/2 by norm_num [u,v],Real.sqrt_eq_rpow]
  have hq : Real.sqrt X/(A+1 : ℕ)≤P v :=
    (div_le_iff₀ (by positivity : (0 : ℝ)<(A+1 : ℕ))).mpr
      (hprod.symm.le.trans (mul_le_mul_of_nonneg_left ha' (by dsimp [P]; positivity)))
  have hs : (S : ℝ)≤P v+1 := by
    dsimp only [S]; rw [Nat.cast_add,Nat.cast_one]
    exact add_le_add ((Nat.floor_le (by positivity)).trans hq) le_rfl
  have hpow : P v≤P u := Real.rpow_le_rpow_of_exponent_le hx₁ (by norm_num [u,v])
  have hone : 1≤P u := Real.one_le_rpow hx₁ (by norm_num [u])
  push_cast; change (A : ℝ)+(S : ℝ)≤3*P u
  linarith only [ha,hs,hpow,hone]

/-- Original coprime prime-product row with the complementary cut averaged
over consecutive integers just above the taper start. -/
def taperedProductRow (X : ℕ) : ℝ :=
  let D := ⌊1+Real.log X⌋₊
  let F := max (2*(D+1)) ⌊(X : ℝ)^(1/200 : ℝ)⌋₊
  let A := complementTaperStart X
  let S := ⌊Real.sqrt X/(A+1 : ℕ)⌋₊+1
  complementAverage A S (cappedComplementaryRow D D X F (max (productLower D X) (squareRootProductUpper X)))

private theorem row_bound :
    ∃ K : ℝ, 0≤K ∧ ∀ {X : ℕ}, 1≤X →
      |aboveSquareRootProductRow X-taperedProductRow X|≤K*(1+Real.log X)^6*Real.sqrt X := by
  obtain ⟨C,hC,h⟩ := averaged_coprime_tail
  obtain ⟨Z,hZ⟩ := Filter.eventually_atTop.mp (Sieve.eventually_const_mul_one_add_log_pow_le_rpow
    (by norm_num : (0 : ℝ)<1/25000000) (by norm_num : (0 : ℝ)<64) 1)
  let E := ∑ n ∈ Icc 1 ⌈Z⌉₊, |aboveSquareRootProductRow n-taperedProductRow n|
  have hE : 0≤E := sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨4*C+E,by positivity,?_⟩
  intro X hx
  let J := 1+Real.log X
  let D := ⌊J⌋₊
  let A := complementTaperStart X
  let P (t : ℝ) := (X : ℝ)^t
  let F := max (2*(D+1)) ⌊P (1/200)⌋₊
  let Y := max (productLower D X) (squareRootProductUpper X)
  have hJ : 1≤J := le_add_of_nonneg_right (Real.log_natCast_nonneg X)
  have hj := zero_le_one.trans hJ
  have hx₁ : (1 : ℝ)≤X := by exact_mod_cast hx
  have hx₀ := zero_lt_one.trans_le hx₁
  have hd₁ : 1≤D := (Nat.one_le_floor_iff _).mpr hJ
  have hd : (D : ℝ)≤J := Nat.floor_le hj
  have hd' : ((D+1 : ℕ) : ℝ)≤2*J := by push_cast; linarith only [hd,hJ]
  have root := Real.one_le_sqrt.mpr hx₁
  by_cases hZX : Z≤X
  swap
  · have hb : |aboveSquareRootProductRow X-taperedProductRow X|≤E :=
      single_le_sum (fun n (_ : n ∈ Icc 1 ⌈Z⌉₊) => abs_nonneg (aboveSquareRootProductRow n-taperedProductRow n))
        (mem_Icc.mpr ⟨hx,by exact_mod_cast (le_of_not_ge hZX).trans (Nat.le_ceil Z)⟩)
    have ht : E≤4*C+E := by linarith only [hC]
    exact hb.trans (ht.trans ((le_mul_of_one_le_right (by positivity) (one_le_pow₀ hJ)).trans
      (le_mul_of_one_le_right (by positivity) root)))
  have hz : 64*J≤P (1/25000000) := by simpa only [pow_one] using hZ (X : ℝ) hZX
  have hbig : 64≤P (1/25000000) := by linarith only [hz,hJ]
  have hlog : ((2*(D+1) : ℕ) : ℝ)≤P (1/25000000) := by
    push_cast; push_cast at hd'; linarith only [hz,hd',hj]
  have hD' : ((D+1 : ℕ) : ℝ)≤P (1/25000000) := by
    have hh : D+1 ≤ 2*(D+1) := by omega
    exact (by exact_mod_cast hh : ((D+1 : ℕ) : ℝ) ≤ ((2*(D+1) : ℕ) : ℝ)).trans hlog
  have mono {s t : ℝ} (hst : s≤t) : P s≤P t := Real.rpow_le_rpow_of_exponent_le hx₁ hst
  have mul (s t : ℝ) : P s*P t=P (s+t) := (Real.rpow_add hx₀ s t).symm
  have hF : ⌊P (1/1000000)⌋₊≤F := (Nat.floor_mono (mono (by norm_num : (1/1000000 : ℝ)≤1/200))).trans (le_max_right ..)
  have ha : 1≤A := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hx₁ (by norm_num))
  have ha' : P (499999999/1000000000)<((A+1 : ℕ) : ℝ) := by push_cast; exact Nat.lt_floor_add_one _
  have hp' : P (1/200)<((F+1 : ℕ) : ℝ) := by
    have hf : ⌊P (1/200)⌋₊ ≤ F := le_max_right ..
    have hr : (⌊P (1/200)⌋₊ : ℝ) ≤ (F : ℝ) := by exact_mod_cast hf
    rw [Nat.cast_add,Nat.cast_one]
    exact (Nat.lt_floor_add_one _).trans_le (add_le_add hr le_rfl)
  have ht : P (499999999/1000000000+1/200)<((A+1 : ℕ) : ℝ)*(F+1 : ℕ) := by
    rw [←mul]
    exact (mul_le_mul_of_nonneg_right ha'.le (by dsimp [P]; positivity)).trans_lt
      (mul_lt_mul_of_pos_left hp' (by positivity))
  have hprod : Y/(F+1)≤A := by
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos F)).mpr
    have hY : (Y : ℝ)≤P (499999999/1000000000+1/200) := by
      dsimp only [Y]; rw [Nat.cast_max]
      apply max_le
      · have hlo : productLower D X≤(D+1)*⌊Real.sqrt X⌋₊ := min_le_right ..
        apply (by exact_mod_cast hlo : ((productLower D X : ℕ) : ℝ)≤((D+1 : ℕ) : ℝ)*(⌊Real.sqrt X⌋₊ : ℕ)).trans
        apply (mul_le_mul hD' (Nat.floor_le (Real.sqrt_nonneg _)) (Nat.cast_nonneg _) (by dsimp [P]; positivity)).trans
        rw [Real.sqrt_eq_rpow,mul]; exact mono (by norm_num)
      · exact (Nat.floor_le (by positivity : 0≤P (500000001/1000000000))).trans (mono (by norm_num))
    exact_mod_cast hY.trans_lt ht
  have hu : ((X/(A+1) : ℕ) : ℝ)≤P (500000001/1000000000) := by
    apply Nat.cast_div_le.trans
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<(A+1 : ℕ))).mpr
    have eq : P (500000001/1000000000)*P (499999999/1000000000)=X := by
      rw [mul,show (500000001/1000000000 : ℝ)+499999999/1000000000=1 by norm_num]; exact Real.rpow_one _
    exact eq.symm.le.trans (mul_le_mul_of_nonneg_left ha'.le (by dsimp [P]; positivity))
  have hh := h hd₁ hd₁ hx (le_max_left (2*(D+1)) ⌊P (1/200)⌋₊) hbig hlog hF ha hprod hu
  apply hh.trans
  have hb := mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg (D+1)) hd' 2) hd (Nat.cast_nonneg D) (by positivity)
  have he := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hC)
    (pow_nonneg hj 3)) (Real.sqrt_nonneg (X : ℝ))
  have hs := mul_le_mul_of_nonneg_right (show 4*C≤4*C+E by linarith only [hE])
    (mul_nonneg (pow_nonneg hj 6) (Real.sqrt_nonneg (X : ℝ)))
  change C*((D+1 : ℕ) : ℝ)^2*D*J^3*Real.sqrt X ≤ (4*C+E)*J^6*Real.sqrt X
  linarith only [he,hs]

/-- At both Vaughan widths, and in fact at every width, the complementary
factor may be tapered strictly below the square root at square-root cost. -/
theorem tapered_complement_cofactors :
    ∃ K : ℝ, 0≤K ∧ ∀ V W N : ℕ,
      |cofactorCountError V W N-∑ d ∈ Icc 1 (min N W), Sieve.typeIIShort V d*taperedProductRow (N/d)| ≤
        (∑ d ∈ Icc 1 W, |Sieve.typeIIShort V d|)*(K*(1+Real.log N)^6*Real.sqrt N) := by
  obtain ⟨C,hC,hprev⟩ := above_square_root_product_cofactors
  obtain ⟨K,hK,h⟩ := row_bound
  refine ⟨C+K,by positivity,fun V W N => ?_⟩
  let f (x : ℕ) := aboveSquareRootProductRow x-taperedProductRow x
  let g (x : ℕ) := K*(1+Real.log x)^6*Real.sqrt x
  have hg (x : ℕ) : 0≤g x := by dsimp [g]; have := Real.log_natCast_nonneg x; positivity
  have mono (x n : ℕ) (hx : 1≤x) (hxn : x≤n) : g x≤g n := by
    have hl := Real.log_le_log (by exact_mod_cast hx : (0 : ℝ)<x) (by exact_mod_cast hxn : (x : ℝ)≤n)
    have hz := Real.log_natCast_nonneg x
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (add_le_add (le_refl (1 : ℝ)) hl) 6) hK) (Real.sqrt_le_sqrt (by exact_mod_cast hxn))
      (Real.sqrt_nonneg _) (by have := Real.log_natCast_nonneg n; positivity)
  have hh := cofactor_sum_majorant f g hg mono (fun _ hx => h hx) V W N
  let I := Icc 1 (min N W)
  let w := Sieve.typeIIShort V
  have eq : cofactorCountError V W N-(∑ d ∈ I, w d*taperedProductRow (N/d)) =
      (cofactorCountError V W N-(∑ d ∈ I, w d*aboveSquareRootProductRow (N/d)))+
      (∑ d ∈ I, w d*f (N/d)) := by simp only [f,mul_sub,sum_sub_distrib]; ring
  rw [eq]
  exact (abs_add_le _ _).trans ((add_le_add (hprev V W N) hh).trans_eq (by dsimp [g]; ring))

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
