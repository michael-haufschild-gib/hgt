import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheFixedPrimeCutAfterSummingConductors
import GaloisForLFunctions.RHTower.Sieve.Mertens

/-!
# Fine variation of the centered fixed prime cut

Evaluate the variation functional of Ghosh–Shuin on consecutive
integer cutoffs. Below the first spline knot the unit increments of
the centered tail are independent of the endpoint conductor. Their
quadratic sum retains a power saving at the seventeen-ninths cut.
Even composite steps already force quadratic absolute variation.
-/

noncomputable section
open Finset Filter GaloisForLFunctions.CountingHolography.Sections
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Cost of moving the terminal prime cutoff across the integer n. -/
def innerCutIncrement (n : ℕ) : ℝ :=
  innerPrimeSlope*n*(1-(if n.Prime then Real.log n else 0))

/-- On the inner linear segment, changing the cutoff changes the actual
complex tail by a real increment independent of the conductor. -/
theorem centered_fixed_cut_step {N k : ℕ} (hN : 0<N)
    (hk : (↑(k+1):ℝ)≤Real.exp (-8)*(N:ℝ)^2) :
    centeredFixedPrimeTail N (k+1)-centeredFixedPrimeTail N k=(innerCutIncrement (k+1):ℂ) := by
  let H := ⌊((N:ℝ)/squareConductorBVWindow.lower)^2⌋₊
  let f (p : ℕ) := (Real.log p:ℂ)*squarePrefixPrimeWeight ((p:ℝ)/(N:ℝ)^2)
  let n := k+1
  let S := (ordinaryPrimeLags H).filter (k<·)
  let R := (ordinaryPrimeLags H).filter (n<·)
  have nr : 0<(n:ℝ) := Nat.cast_pos.mpr (Nat.succ_pos k)
  have xn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have he : Real.exp (-8)≤1 := Real.exp_le_one_iff.mpr (by norm_num)
  have horizon : n≤H := Nat.le_floor (hk.trans ((mul_le_of_le_one_left (sq_nonneg (N:ℝ)) he).trans
    (pow_le_pow_left₀ xn.le (le_div_self xn.le squareConductorBVWindow.lower_pos he) 2)))
  have rest : S.filter (·≠n)=R := by
    ext i
    simp only [S,R,mem_filter]
    dsimp only [n]
    constructor
    · rintro ⟨⟨hm,lo⟩,ne⟩
      exact ⟨hm,by omega⟩
    · rintro ⟨hm,lo⟩
      exact ⟨⟨hm,by omega⟩,by omega⟩
  have atom : S.filter (·=n)=if n.Prime then {n} else ∅ := by
    ext i
    by_cases h : n.Prime
    · rw [if_pos h]
      simp only [S,ordinaryPrimeLags,mem_filter,mem_Icc,mem_singleton]
      constructor
      · exact fun q => q.2
      · rintro rfl
        exact ⟨⟨⟨⟨h.two_le,horizon⟩,h⟩,Nat.lt_succ_self k⟩,rfl⟩
    · rw [if_neg h]
      simp only [S,ordinaryPrimeLags,mem_filter,notMem_empty,iff_false]
      rintro ⟨⟨⟨_,hp⟩,_⟩,rfl⟩
      exact h hp
  have split := sum_filter_add_sum_filter_not S (·=n) f
  rw [rest,atom] at split
  have early := squarePrefixPrimeWeight_before_first_knot (div_pos nr (sq_pos_of_pos xn))
    ((div_le_iff₀ (sq_pos_of_pos xn)).mpr hk)
  have price : (N:ℂ)^2*f n=(innerPrimeSlope:ℂ)*n*Real.log n := by
    dsimp only [f]
    rw [early,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast,Complex.ofReal_natCast]
    field_simp [(Nat.cast_ne_zero.mpr hN.ne' : (N:ℂ)≠0)] <;> ring
  have drift : (↑(innerPrimeSlope*((n:ℝ)*(n+1)/2)):ℂ)-
      (↑(innerPrimeSlope*((k:ℝ)*(k+1)/2)):ℂ)=(innerPrimeSlope:ℂ)*n := by
    dsimp only [n]
    push_cast
    ring
  change (N:ℂ)^2*(∑ p ∈ R,f p)+(↑(innerPrimeSlope*((n:ℝ)*(n+1)/2)):ℂ)-
    ((N:ℂ)^2*(∑ p ∈ S,f p)+(↑(innerPrimeSlope*((k:ℝ)*(k+1)/2)):ℂ))=(innerCutIncrement n:ℂ)
  unfold innerCutIncrement
  by_cases prime : n.Prime
  · simp only [prime,if_true,sum_singleton] at split ⊢
    rw [←split,mul_add,price]
    push_cast
    push_cast at drift
    linear_combination drift
  · simp only [prime,if_false,sum_empty,zero_add] at split ⊢
    rw [split]
    push_cast
    push_cast at drift
    linear_combination drift

private theorem increment_abs_le {n K : ℕ} (hp : 0<n) (hl : n≤K) :
    |innerCutIncrement n|≤innerPrimeSlope*K*(1+Real.log K) := by
  have hλ := innerPrimeSlope_pos
  have hg : |1-(if n.Prime then Real.log n else 0)|≤1+Real.log K := by
    by_cases h : n.Prime
    · simp only [h,if_true]
      have tri := abs_sub (1:ℝ) (Real.log n)
      rw [abs_one,abs_of_nonneg (Real.log_natCast_nonneg n)] at tri
      exact tri.trans (add_le_add le_rfl (Real.log_le_log (Nat.cast_pos.mpr hp) (Nat.cast_le.mpr hl)))
    · simp only [h,if_false,sub_zero,abs_one]
      linarith only [Real.log_natCast_nonneg K]
  unfold innerCutIncrement
  rw [abs_mul,abs_of_nonneg (mul_nonneg hλ.le (Nat.cast_nonneg n))]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hl) hλ.le) hg (abs_nonneg _)
    (mul_nonneg hλ.le (Nat.cast_nonneg K))

/-- The finite quadratic variation of the original complex cutoff
curve is controlled at every cutoff below the first knot. -/
theorem centered_fixed_cut_quadratic_variation {N K : ℕ} (hN : 0<N)
    (hk : (K:ℝ)≤Real.exp (-8)*(N:ℝ)^2) :
    (∑ k ∈ range K, ‖centeredFixedPrimeTail N (k+1)-centeredFixedPrimeTail N k‖^2)≤
      innerPrimeSlope^2*(K:ℝ)^3*(1+Real.log K)^2 := by
  let B := innerPrimeSlope*K*(1+Real.log K)
  have hard : (∑ k ∈ range K, ‖centeredFixedPrimeTail N (k+1)-centeredFixedPrimeTail N k‖^2)≤
      ∑ _ ∈ range K, B^2 := by
    apply sum_le_sum
    intro k h
    have hi := Nat.succ_le_of_lt (mem_range.mp h)
    rw [centered_fixed_cut_step hN ((Nat.cast_le.mpr hi).trans hk),Complex.norm_real,Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (increment_abs_le (Nat.succ_pos k) hi) 2
  rw [sum_const,card_range,nsmul_eq_mul] at hard
  exact hard.trans_eq (by dsimp only [B]; ring)

private theorem absolute_even_steps (t : ℕ) (ht : 1≤t) :
    innerPrimeSlope*((t:ℝ)*(t+1)-2)≤∑ k ∈ range (2*t), |innerCutIncrement (k+1)| := by
  induction t,ht using Nat.le_induction with
  | base =>
    simp only [Nat.cast_one,show (1:ℝ)*(1+1)-2=0 by norm_num,mul_zero]
    exact sum_nonneg (fun _ _ => abs_nonneg _)
  | succ t ht ih =>
    have no : ¬ (2*(t+1)).Prime := by
      intro pp
      have div : 2∣2*(t+1) := dvd_mul_right 2 _
      have eq := (Nat.prime_dvd_prime_iff_eq Nat.prime_two pp).mp div
      omega
    have last : |innerCutIncrement (2*t+1+1)|=innerPrimeSlope*(2*(t+1)) := by
      rw [show 2*t+1+1=2*(t+1) by omega,innerCutIncrement,if_neg no,sub_zero,mul_one,
        abs_of_nonneg (mul_nonneg innerPrimeSlope_pos.le (Nat.cast_nonneg _))]
      push_cast
      ring
    rw [show 2*(t+1)=2*t+1+1 by omega,sum_range_succ,sum_range_succ,last]
    push_cast
    linarith only [ih,abs_nonneg (innerCutIncrement (2*t+1))]

/-- Absolute variation costs at most a constant times K². The sum of
prime log weights supplies the constant without a logarithmic loss. -/
theorem centered_fixed_cut_absolute_ceiling {N K : ℕ} (hN : 0<N)
    (hk : (K:ℝ)≤Real.exp (-8)*(N:ℝ)^2) :
    (∑ k ∈ range K, ‖centeredFixedPrimeTail N (k+1)-centeredFixedPrimeTail N k‖)≤
      innerPrimeSlope*(1+Real.log 4)*(K:ℝ)^2 := by
  let w (n : ℕ) := if n.Prime then Real.log (n:ℝ) else 0
  have pos (n : ℕ) : 0≤w n := by unfold w; split_ifs <;> first | exact Real.log_natCast_nonneg n | exact le_rfl
  have cap : (∑ k ∈ range K,w (k+1))≤K*Real.log 4 := by
    have full : (∑ n ∈ range (K+1),w n)=∑ k ∈ range K,w (k+1) := by
      rw [sum_range_succ',show w 0=0 by simp [w],add_zero]
    rw [←full]
    unfold w
    rw [←sum_filter]
    exact _root_.RHTower.Sieve.sum_log_primesLE_le K
  have top : (∑ k ∈ range K, ‖centeredFixedPrimeTail N (k+1)-centeredFixedPrimeTail N k‖)≤
      ∑ k ∈ range K, (innerPrimeSlope*K)*(1+w (k+1)) := by
    apply sum_le_sum
    intro k hm
    have hi := Nat.succ_le_of_lt (mem_range.mp hm)
    rw [centered_fixed_cut_step hN ((Nat.cast_le.mpr hi).trans hk),Complex.norm_real,Real.norm_eq_abs]
    change |innerPrimeSlope*(↑(k+1):ℝ)*(1-w (k+1))|≤_
    rw [abs_mul,abs_of_nonneg (mul_nonneg innerPrimeSlope_pos.le (Nat.cast_nonneg _))]
    have one := abs_sub (1:ℝ) (w (k+1))
    rw [abs_one,abs_of_nonneg (pos _)] at one
    exact mul_le_mul (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hi) innerPrimeSlope_pos.le) one
      (abs_nonneg _) (mul_nonneg innerPrimeSlope_pos.le (Nat.cast_nonneg K))
  apply top.trans
  rw [←mul_sum,sum_add_distrib,sum_const,card_range,nsmul_eq_mul,mul_one]
  linarith only [mul_le_mul_of_nonneg_left cap (mul_nonneg innerPrimeSlope_pos.le (Nat.cast_nonneg K))]

/-- For every real order q≥1, only q−1 powers of the logarithm appear
in the unit-mesh q-th power sum. -/
theorem centered_fixed_cut_fine_power {N K : ℕ} {q : ℝ} (hq : 1≤q) (hN : 0<N)
    (hk : (K:ℝ)≤Real.exp (-8)*(N:ℝ)^2) :
    (∑ k ∈ range K, ‖centeredFixedPrimeTail N (k+1)-centeredFixedPrimeTail N k‖^q)≤
      (innerPrimeSlope*K*(1+Real.log K))^(q-1)*(innerPrimeSlope*(1+Real.log 4)*(K:ℝ)^2) := by
  let J (k : ℕ) := ‖centeredFixedPrimeTail N (k+1)-centeredFixedPrimeTail N k‖
  let B := innerPrimeSlope*K*(1+Real.log K)
  have pB : 0≤B := mul_nonneg (mul_nonneg innerPrimeSlope_pos.le (Nat.cast_nonneg K))
      (add_nonneg zero_le_one (Real.log_natCast_nonneg K))
  have bound : (∑ k ∈ range K,(J k)^q)≤∑ k ∈ range K,B^(q-1)*J k := by
    apply sum_le_sum
    intro k h
    have hi := Nat.succ_le_of_lt (mem_range.mp h)
    have cap : J k≤B := by
      unfold J
      rw [centered_fixed_cut_step hN ((Nat.cast_le.mpr hi).trans hk),Complex.norm_real,Real.norm_eq_abs]
      exact increment_abs_le (Nat.succ_pos k) hi
    by_cases z : J k=0
    · rw [z,Real.zero_rpow (zero_lt_one.trans_le hq).ne',mul_zero]
    have p : 0<J k := lt_of_le_of_ne (norm_nonneg _) (Ne.symm z)
    have calc_pow : (J k)^q=(J k)^(q-1)*J k := by
      simpa only [sub_add_cancel,Real.rpow_one] using Real.rpow_add p (q-1) 1
    rw [calc_pow]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow p.le cap (sub_nonneg.mpr hq)) p.le
  rw [←mul_sum] at bound
  exact bound.trans (mul_le_mul_of_nonneg_left (centered_fixed_cut_absolute_ceiling hN hk) (Real.rpow_nonneg pB _))

/-- The same curve has at least quadratic absolute variation, already
on even composite steps. At an even cutoff 2t the explicit coefficient
is the sum of the positive drifts from 4 through 2t. -/
theorem centered_fixed_cut_absolute_variation {N t : ℕ} (hN : 0<N) (ht : 1≤t)
    (hk : (↑(2*t):ℝ)≤Real.exp (-8)*(N:ℝ)^2) :
    innerPrimeSlope*((t:ℝ)*(t+1)-2)≤
      ∑ k ∈ range (2*t), ‖centeredFixedPrimeTail N (k+1)-centeredFixedPrimeTail N k‖ := by
  apply (absolute_even_steps t ht).trans_eq
  apply sum_congr rfl
  intro k h
  have hi := Nat.succ_le_of_lt (mem_range.mp h)
  rw [centered_fixed_cut_step hN ((Nat.cast_le.mpr hi).trans hk),Complex.norm_real,Real.norm_eq_abs]

/-- Eventually the prescribed product cutoff is between N and the
first spline knot. -/
theorem seventeen_ninths_inside_first_knot :
    ∀ᶠ N : ℕ in atTop, N≤⌊(N:ℝ)^(17/9:ℝ)⌋₊ ∧
      (⌊(N:ℝ)^(17/9:ℝ)⌋₊:ℝ)≤Real.exp (-8)*(N:ℝ)^2 := by
  have late : ∀ᶠ n : ℕ in atTop, Real.exp 8≤(n:ℝ)^(1/9:ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/9)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [late,eventually_ge_atTop 1] with N hn hN
  have x1 : 1≤(N:ℝ) := Nat.one_le_cast.mpr hN
  have xp := zero_lt_one.trans_le x1
  constructor
  · apply Nat.le_floor
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le x1 (by norm_num : (1:ℝ)≤17/9)
  · apply (Nat.floor_le (Real.rpow_nonneg xp.le (17/9:ℝ))).trans
    rw [Real.exp_neg,inv_mul_eq_div,le_div_iff₀ (Real.exp_pos 8)]
    have hh := mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg xp.le (17/9:ℝ))
    rwa [←Real.rpow_add xp,show (17/9:ℝ)+1/9=2 by norm_num,Real.rpow_two] at hh

/-- At the seventeen-ninths cutoff the sum of absolute increments is
supercubic. The sum of their squares is smaller than N^6 by a power,
so the diagonal of the squared cumulative variation is subcubic after
taking its square root. -/
theorem variation_at_the_seventeen_ninths_cut {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop,
      let K := ⌊(N:ℝ)^(17/9:ℝ)⌋₊
      let jump := fun k => ‖centeredFixedPrimeTail N (k+1)-centeredFixedPrimeTail N k‖
      innerPrimeSlope/16*(N:ℝ)^(34/9:ℝ)≤∑ k ∈ range K, jump k ∧
      (∑ k ∈ range K, (jump k)^2)≤C*(N:ℝ)^(17/3+ε) := by
  let u := ε/2
  have pu : 0<u := div_pos hε (by norm_num)
  let D := 1+(17/9:ℝ)/u
  have pD : 0<D := add_pos zero_lt_one (div_pos (by norm_num) pu)
  refine ⟨innerPrimeSlope^2*D^2,mul_pos (sq_pos_of_pos innerPrimeSlope_pos) (sq_pos_of_pos pD),?_⟩
  filter_upwards [seventeen_ninths_inside_first_knot,eventually_ge_atTop 8] with N geo hN
  let x := (N:ℝ)
  let Y := x^(17/9:ℝ)
  let K := ⌊Y⌋₊
  let t := K/2
  let jump (k : ℕ) := ‖centeredFixedPrimeTail N (k+1)-centeredFixedPrimeTail N k‖
  have x1 : 1≤x := Nat.one_le_cast.mpr (by omega)
  have xp := zero_lt_one.trans_le x1
  have pY : 0<Y := Real.rpow_pos_of_pos xp _
  have Klo : (K:ℝ)≤Y := Nat.floor_le pY.le
  have hK : 8≤K := hN.trans geo.1
  have knot : (K:ℝ)≤Real.exp (-8)*x^2 := geo.2
  have pc : 0<N := by omega
  have twice : 2*t≤K := by dsimp only [t]; omega
  have tl : 2≤t := by dsimp only [t]; omega
  have tlr : 2≤(t:ℝ) := by exact_mod_cast tl
  have big : Y≤4*t := by
    have geom : K≤2*t+1 := by dsimp only [t]; omega
    have geomR : (K:ℝ)≤2*(t:ℝ)+1 := by exact_mod_cast geom
    linarith only [Nat.lt_floor_add_one Y,geomR,tlr]
  have pow₂ : Y^2=x^(34/9:ℝ) := by
    rw [←Real.rpow_two,←Real.rpow_mul xp.le,show (17/9:ℝ)*2=34/9 by norm_num]
  have pow₃ : Y^3=x^(17/3:ℝ) := by
    rw [←Real.rpow_natCast Y 3,←Real.rpow_mul xp.le,show (17/9:ℝ)*(3:ℕ)=17/3 by norm_num]
  change innerPrimeSlope/16*x^(34/9:ℝ)≤∑ k ∈ range K,jump k ∧
    (∑ k ∈ range K,(jump k)^2)≤innerPrimeSlope^2*D^2*x^(17/3+ε)
  constructor
  · have hard := centered_fixed_cut_absolute_variation pc (show 1≤t by omega)
      ((Nat.cast_le.mpr twice).trans knot)
    have extend : (∑ k ∈ range (2*t),jump k)≤∑ k ∈ range K,jump k :=
      sum_le_sum_of_subset_of_nonneg (range_mono twice) (fun _ _ _ => norm_nonneg _)
    have shape : Y^2/16≤(t:ℝ)*(t+1)-2 := by
      linarith only [pow_le_pow_left₀ pY.le big 2,tlr]
    rw [←pow₂]
    exact (by linarith only [mul_le_mul_of_nonneg_left shape innerPrimeSlope_pos.le] :
      innerPrimeSlope/16*Y^2≤innerPrimeSlope*((t:ℝ)*(t+1)-2)).trans (hard.trans extend)
  · have raw := centered_fixed_cut_quadratic_variation pc knot
    have Kp : 0<(K:ℝ) := Nat.cast_pos.mpr (by omega)
    have logK := Real.log_le_log Kp Klo
    change Real.log (K:ℝ)≤Real.log (x^(17/9:ℝ)) at logK
    rw [Real.log_rpow xp] at logK
    have logu := Real.log_le_rpow_div xp.le pu
    have price : 1+Real.log K≤D*x^u := by
      dsimp only [D]
      simp only [div_eq_mul_inv] at logu ⊢
      linarith only [logK,mul_le_mul_of_nonneg_left logu (by norm_num : (0:ℝ)≤17/9),Real.one_le_rpow x1 pu.le]
    have cube := (pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) K) Klo 3).trans_eq pow₃
    have lsq := pow_le_pow_left₀ (add_nonneg zero_le_one (Real.log_natCast_nonneg K)) price 2
    have mul := mul_le_mul (mul_le_mul_of_nonneg_left cube (sq_nonneg innerPrimeSlope)) lsq
      (sq_nonneg _) (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg xp.le _))
    apply raw.trans (mul.trans_eq ?_)
    have q : (x^u)^2=x^ε := by
      rw [←Real.rpow_two,←Real.rpow_mul xp.le,show u*2=ε by dsimp [u]; ring]
    rw [mul_pow,q,Real.rpow_add xp]
    ring

#print axioms variation_at_the_seventeen_ninths_cut
#print axioms centered_fixed_cut_step
#print axioms centered_fixed_cut_quadratic_variation
#print axioms centered_fixed_cut_absolute_ceiling
#print axioms centered_fixed_cut_fine_power
#print axioms centered_fixed_cut_absolute_variation
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
