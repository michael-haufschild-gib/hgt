import GaloisForLFunctions.ExceptionalLayerTheory.ALocalPrimeWaveAtEveryRightZero
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheSeventeenNinthsConductorPrefix
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.PositiveWeightsForTheReciprocalPrimeOctave

/-!
# Both signs of the reciprocal prime octave

Differencing two dilates of the alternating divisor test makes it bounded
without losing its zero frequency. Abel summation can then act on the
ordinary reciprocal octave at a uniformly bounded cost per index. Averaging
positive parity weights over integer terminals separates its two signs.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- A complete odd quotient block gives unit weight throughout the whole
unit interval, including its two original endpoints. -/
private theorem weight_of_complete_odd_cell {n j Y : ℕ} (hj : j%2=1)
    (hl : j*(n+1)≤Y) (hu : Y<(j+1)*n) : octaveParityWeight Y n=1 := by
  have hjY := (Nat.le_mul_of_pos_right j (Nat.succ_pos n)).trans hl
  have hrow (d : ℕ) (hd : d∈Icc 1 Y) : alternatingDivisorCoeff d*octaveUnitClip ((Y:ℝ)/d-n) =
      if d≤j then alternatingDivisorCoeff d else 0 := by
    have hd0 : (0:ℝ)<d := Nat.cast_pos.mpr (mem_Icc.mp hd).1
    by_cases h : d≤j
    · have hN : d*(n+1)≤Y := (Nat.mul_le_mul_right _ h).trans hl
      have hx : (n:ℝ)+1 ≤ (Y:ℝ)/d := (le_div_iff₀ hd0).mpr (by
        exact_mod_cast (show (n+1)*d≤Y by simpa only [Nat.mul_comm] using hN))
      rw [if_pos h,show octaveUnitClip ((Y:ℝ)/d-n)=1 by unfold octaveUnitClip; grind,mul_one]
    · have hN : Y≤d*n := hu.le.trans (Nat.mul_le_mul_right _ (by omega))
      have hx : (Y:ℝ)/d≤n := (div_le_iff₀ hd0).mpr (by
        exact_mod_cast (show Y≤n*d by simpa only [Nat.mul_comm] using hN))
      rw [if_neg h,show octaveUnitClip ((Y:ℝ)/d-n)=0 by unfold octaveUnitClip; grind,mul_zero]
  have hs : (Icc 1 Y).filter (· ≤ j) = Icc 1 j := by ext d; simp only [mem_filter,mem_Icc]; omega
  rw [octaveParityWeight,sum_congr rfl hrow,←sum_filter,hs,prefix_alternatingDivisorCoeff,hj,Nat.cast_one]

/-- A uniform positive fraction of actual integer terminals give full
weight at each index above the square-root transition and below N/2. -/
theorem octave_parity_terminal_mass {n N : ℕ} (hn : 2≤n) (hsq : 2*N≤n*n)
    (hN : 2*n≤N) : (N:ℝ) ≤ 16*∑ Y ∈ Icc 1 N, octaveParityWeight Y n := by
  classical
  let K := N/(2*n)
  let R := n/2
  let S := (range K) ×ˢ (range R)
  let j (k : ℕ) := 2*k+1
  let r (l : ℕ) := n-R+l
  let f (z : ℕ×ℕ) := j z.1*n+r z.2
  have hn0 : 0<n := by omega
  have h2n : 0<2*n := by omega
  have hK : 1≤K := (Nat.one_le_div_iff h2n).mpr hN
  have hR : 1≤R := (Nat.one_le_div_iff (by decide : 0<2)).mpr hn
  have hKn : K*(2*n)≤N := Nat.div_mul_le_self N (2*n)
  have hR' : R*2≤n := Nat.div_mul_le_self n 2
  have cell (z : ℕ×ℕ) (hz : z∈S) : 0<f z ∧ f z≤N ∧ j z.1*(n+1)≤f z ∧ f z<(j z.1+1)*n := by
    obtain ⟨hk,hh⟩ := mem_product.mp hz
    have hk' := mem_range.mp hk
    have hh' := mem_range.mp hh
    have hju : j z.1+1≤2*K := by dsimp only [j]; omega
    have hmul : (j z.1+1)*n ≤ N :=
      (Nat.mul_le_mul_right n hju).trans ((show (2*K)*n=K*(2*n) by ring).le.trans hKn)
    have htmp : (2*j z.1)*n≤n*n := calc
      _ = 2*(j z.1*n) := Nat.mul_assoc ..
      _ ≤ 2*N := Nat.mul_le_mul_left 2 ((Nat.mul_le_mul_right n (Nat.le_succ _)).trans hmul)
      _ ≤ _ := hsq
    have hsmall : 2*j z.1≤n := Nat.le_of_mul_le_mul_right htmp hn0
    have hrl : j z.1≤r z.2 := by dsimp only [r]; omega
    have hru : r z.2<n := by dsimp only [r]; omega
    have hjpos : 0<j z.1 := Nat.succ_pos _
    have hjn : 0<j z.1*n := Nat.mul_pos hjpos hn0
    have hup : f z<(j z.1+1)*n := by
      change j z.1*n+r z.2 < (j z.1+1)*n
      rw [Nat.add_mul (j z.1) 1 n,Nat.one_mul]
      exact Nat.add_lt_add_left hru _
    refine ⟨by dsimp only [f]; omega,hup.le.trans hmul,?_,hup⟩
    dsimp only [f]; rw [Nat.mul_add,Nat.mul_one]; omega
  have quotient (z : ℕ×ℕ) (hz : z∈S) : f z/n=j z.1 := by
    have hc := cell z hz
    apply Nat.le_antisymm (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hn0).mpr hc.2.2.2))
    exact (Nat.le_div_iff_mul_le hn0).mpr (Nat.le_add_right _ _)
  have inj : ∀ z∈S, ∀ q∈S, f z=f q → z=q := by
    intro z hz q hq he
    have h := congrArg (· /n) he
    rw [quotient z hz,quotient q hq] at h
    have hfst : z.1=q.1 := by dsimp only [j] at h; omega
    apply Prod.ext hfst
    dsimp only [f,r] at he
    rw [hfst] at he
    omega
  have hsub : S.image f ⊆ Icc 1 N := by
    intro Y hY
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hY
    exact mem_Icc.mpr ⟨(cell z hz).1,(cell z hz).2.1⟩
  have hsum : ((K*R:ℕ):ℝ) ≤ ∑ Y ∈ Icc 1 N, octaveParityWeight Y n := by
    calc _ = ∑ z ∈ S, (1:ℝ) := by simp [S]
         _ = ∑ Y ∈ S.image f, octaveParityWeight Y n := by
           rw [sum_image inj]
           apply sum_congr rfl
           intro z hz
           exact (weight_of_complete_odd_cell (j := j z.1) (by dsimp only [j]; omega)
             (cell z hz).2.2.1 (cell z hz).2.2.2).symm
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun Y _ _ => (octave_parity_weight_range Y n).1)
  have hb : N<(K+1)*(2*n) := by rw [Nat.mul_comm (K+1)]; exact Nat.lt_mul_div_succ N h2n
  have hrb : n<(R+1)*2 := by simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ n (by decide : 0<2)
  have hu : N≤16*(K*R) := calc
    _ ≤ (2*K)*(2*n) := hb.le.trans (Nat.mul_le_mul_right _ (by omega))
    _ = 4*K*n := by ring
    _ ≤ 4*K*(4*R) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring
  exact (show (N:ℝ)≤16*((K*R:ℕ):ℝ) by exact_mod_cast hu).trans
    (mul_le_mul_of_nonneg_left hsum (by norm_num))

#print axioms octave_parity_terminal_mass

private theorem kernel_before_one (a : ArithmeticFunction ℝ) (w : ℝ → ℂ) (hw : w 1=0) {x : ℝ} (hx : x≤1) :
    arithmeticKernel a w x = 0 := by
  rcases hx.lt_or_eq with h | rfl
  · have hh : ⌊x⌋₊=0 := by
      by_contra hn
      exact h.not_ge ((Nat.one_le_floor_iff _).mp (Nat.one_le_iff_ne_zero.mpr hn))
    simp [arithmeticKernel,hh]
  · simp [arithmeticKernel,hw]

private theorem log_increment_above_zero {H : ℝ → ℂ} {C : ℝ} (hC : 0≤C)
    (hzero : ∀ x≤1,H x=0)
    (h : ∀ x y : ℝ, 1≤x → x≤y → ‖H y-H x‖≤C*(Real.log y-Real.log x))
    {x y : ℝ} (hx : 0<x) (hxy : x≤y) : ‖H y-H x‖≤C*(Real.log y-Real.log x) := by
  by_cases hx1 : 1≤x
  · exact h _ _ hx1 hxy
  have hxl := Real.log_nonpos hx.le (le_of_not_ge hx1)
  rw [hzero x (le_of_not_ge hx1)]
  by_cases hy1 : 1≤y
  · have hu := h 1 y le_rfl hy1
    simp only [hzero 1 le_rfl,Real.log_one,sub_zero] at hu
    rw [sub_zero]
    exact hu.trans (mul_le_mul_of_nonneg_left (by linarith only [hxl] : Real.log y ≤ Real.log y - Real.log x) hC)
  · rw [hzero y (le_of_not_ge hy1),sub_self,norm_zero]
    exact mul_nonneg hC (sub_nonneg.mpr (Real.log_le_log hx hxy))

private theorem kernel_dilate_two (a : ArithmeticFunction ℝ) (H : ℝ → ℂ) (hH : ∀ y≤1,H y=0)
    {x : ℝ} (hx : 0≤x) :
    arithmeticKernel a (fun u => H (u/2)) x = arithmeticKernel a H (x/2) := by
  have hs : Icc 1 ⌊x/2⌋₊ ⊆ Icc 1 ⌊x⌋₊ := Icc_subset_Icc le_rfl (Nat.floor_mono (by linarith only [hx]))
  have ho : ∀ n∈Icc 1 ⌊x⌋₊, n∉Icc 1 ⌊x/2⌋₊ → a n • H ((x/2)/n)=0 := by
    intro n hn hcut
    have hn0 : (0:ℝ)<n := Nat.cast_pos.mpr (mem_Icc.mp hn).1
    have hg : ⌊x/2⌋₊<n := lt_of_not_ge (fun hh => hcut (mem_Icc.mpr ⟨(mem_Icc.mp hn).1,hh⟩))
    have hh := (Nat.floor_lt (by positivity : 0 ≤ x/2)).mp hg
    rw [hH _ ((div_le_one hn0).mpr hh.le),smul_zero]
  unfold arithmeticKernel
  rw [sum_subset hs ho]
  exact sum_congr rfl fun n _ => congrArg (fun y => a n • H y) (div_right_comm x (n:ℝ) 2)

private def dyadicDifference (H : ℝ → ℂ) (y : ℝ) := H y-H (y/2)

private theorem kernel_dyadic_difference (a : ArithmeticFunction ℝ) (H : ℝ → ℂ)
    (hH : ∀ y≤1,H y=0) {x : ℝ} (hx : 0≤x) : arithmeticKernel a (dyadicDifference H) x =
      arithmeticKernel a H x-arithmeticKernel a H (x/2) := by
  rw [←kernel_dilate_two a H hH hx]
  simp only [arithmeticKernel,dyadicDifference,smul_sub,sum_sub_distrib]

private theorem dyadic_test_bounds {H : ℝ → ℂ} {C : ℝ} (hC : 0≤C) (hH : ∀ y≤1,H y=0)
    (h : ∀ x y : ℝ, 1≤x → x≤y → ‖H y-H x‖≤C*(Real.log y-Real.log x)) :
    (∀ y≤1,dyadicDifference H y=0) ∧ (∀ y : ℝ, 0<y → ‖dyadicDifference H y‖≤C*Real.log 2) ∧
    ∀ {x y : ℝ}, 0<x → x≤y → ‖dyadicDifference H y-dyadicDifference H x‖≤2*C*(Real.log y-Real.log x) := by
  refine ⟨fun y hy => ?_,fun y hy => ?_,fun {x y} hx hxy => ?_⟩
  · rw [dyadicDifference,hH y hy,hH (y/2) (by linarith only [hy]),sub_self]
  · have hb := log_increment_above_zero hC hH h (half_pos hy) (by linarith only [hy] : y/2≤y)
    rw [Real.log_div hy.ne' (by norm_num : (2:ℝ)≠0)] at hb
    exact hb.trans_eq (by ring)
  · have h₁ := log_increment_above_zero hC hH h hx hxy
    have h₂ := log_increment_above_zero hC hH h (half_pos hx) (div_le_div_of_nonneg_right hxy (by norm_num : (0:ℝ)≤2))
    rw [Real.log_div (hx.trans_le hxy).ne' (by norm_num : (2:ℝ)≠0),
      Real.log_div hx.ne' (by norm_num : (2:ℝ)≠0)] at h₂
    rw [dyadicDifference,dyadicDifference,show H y-H (y/2)-(H x-H (x/2))=(H y-H x)-(H (y/2)-H (x/2)) by abel]
    exact (norm_sub_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))

private theorem dyadic_wave_factor {ρ : ℂ} (hhalf : 1/2<ρ.re) (hone : ρ.re<1) :
    (1-(2:ℂ)^(-ρ))*(1-2*(2:ℂ)^(-ρ)) ≠ 0 := by
  have hab : ‖(2:ℂ)^(-ρ)‖=(2:ℝ)^(-ρ.re) := by
    simpa only [Complex.neg_re,Complex.ofReal_ofNat] using Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<2) (-ρ)
  have h₁ : (2:ℝ)^(-ρ.re)<1 := by
    simpa only [Real.rpow_zero] using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2)
      (by linarith only [hhalf] : -ρ.re<0)
  have h₂ : 1<2*(2:ℝ)^(-ρ.re) := by
    rw [show (2:ℝ)*(2:ℝ)^(-ρ.re)=(2:ℝ)^(1-ρ.re) by
      rw [sub_eq_add_neg,Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_one]]
    exact Real.one_lt_rpow (by norm_num) (sub_pos.mpr hone)
  apply mul_ne_zero <;> apply sub_ne_zero.mpr
  · intro hz
    have hn := congrArg norm hz
    rw [norm_one,hab] at hn
    linarith only [hn,h₁]
  · intro hz
    have hn := congrArg norm hz
    rw [norm_one,norm_mul,hab] at hn
    norm_num at hn
    linarith only [hn,h₂]

private theorem activated_wave (d ρ : ℂ) {x : ℝ} (hx : 0<x) :
    ((x:ℂ)^ρ*d-((x/2:ℝ):ℂ)^ρ*d) -
        2*(((x/2:ℝ):ℂ)^ρ*d-((x/2/2:ℝ):ℂ)^ρ*d) =
      (x:ℂ)^ρ*(d*((1-(2:ℂ)^(-ρ))*(1-2*(2:ℂ)^(-ρ)))) := by
  rw [_root_.RHTower.Sieve.ofReal_div_cpow_eq_mul_cpow_neg (half_pos hx) (by norm_num : (0:ℝ)<2),
    _root_.RHTower.Sieve.ofReal_div_cpow_eq_mul_cpow_neg hx (by norm_num : (0:ℝ)<2)]
  push_cast
  ring

/-- At an integer terminal the alternating Dirichlet kernel has bounded
mass against a bounded test with bounded logarithmic increments. -/
private theorem alternating_bounded_test {J : ℝ → ℂ} {C : ℝ}
    (hj : ∀ y≤1,J y=0) (hi : ∀ {x y : ℝ}, 0<x → x≤y → ‖J y-J x‖≤C*(Real.log y-Real.log x))
    (N : ℕ) (hN : 0<N) : ‖arithmeticKernel alternatingDivisorCoeff J N‖ ≤ C*Real.log (N+1) := by
  rw [arithmeticKernel_eq_prefix_differences _ J hj]
  simp only [prefix_alternatingDivisorCoeff]
  have hsum := norm_sum_le (Icc 1 N) (fun n : ℕ => ((n%2:ℕ):ℝ) • (J ((N:ℝ)/n)-J ((N:ℝ)/(n+1))))
  apply hsum.trans
  have hnR : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hrow (n : ℕ) (hn : n∈Icc 1 N) :
      ‖((n%2:ℕ):ℝ) • (J ((N:ℝ)/n)-J ((N:ℝ)/(n+1)))‖ ≤ C*(Real.log (n+1)-Real.log n) := by
    have hn0 : (0:ℝ)<n := Nat.cast_pos.mpr (mem_Icc.mp hn).1
    have h := hi (div_pos hnR (by positivity : 0<(n:ℝ)+1))
      (div_le_div_of_nonneg_left hnR.le hn0 (by linarith : (n:ℝ)≤n+1))
    rw [Real.log_div hnR.ne' hn0.ne',Real.log_div hnR.ne' (by positivity : (n:ℝ)+1≠0)] at h
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
    apply (mul_le_of_le_one_left (norm_nonneg _) (show ((n%2:ℕ):ℝ)≤1 by
      exact_mod_cast (show n%2≤1 by omega))).trans
    exact h.trans_eq (by ring)
  have htel (m : ℕ) : (∑ n ∈ Icc 1 m, (Real.log (n+1)-Real.log n)) = Real.log (m+1) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_Icc_succ_top (show 1 ≤ m+1 by omega),ih,Nat.cast_succ]
      ring
  exact (sum_le_sum hrow).trans_eq (by rw [←mul_sum,htel])

private theorem atom_as_dyadic_dilation {n : ℕ} (hn : 0<n) :
    reciprocalOctaveAtom n = (dyadicCountDifference*vonMangoldt) n -
      (if n=1 then Real.log 2 else 0) := by
  have ha (k : ℕ) : dyadicCountDifference k = (if k=1 then 1 else 0)-(if k=2 then 2 else 0) := rfl
  have h1 : 1∈n.divisors := Nat.mem_divisors.mpr ⟨one_dvd _,hn.ne'⟩
  have h2 : 2∈n.divisors ↔ 2∣n := ⟨fun h => (Nat.mem_divisors.mp h).1,fun h => Nat.mem_divisors.mpr ⟨h,hn.ne'⟩⟩
  rw [reciprocalOctaveAtom,ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal
    (f := fun d j => dyadicCountDifference d*vonMangoldt j)]
  simp only [ha,sub_mul,ite_mul,zero_mul,one_mul,sum_sub_distrib,sum_ite_eq',if_pos h1,Nat.div_one,h2,
    mul_ite,mul_zero]

private theorem dyadic_kernel_two {x : ℝ} (hx : 2≤x) (F : ℝ → ℂ) :
    arithmeticKernel dyadicCountDifference F x = F x-2*F (x/2) := by
  have h2 : 2≤⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have h1m : 1∈Icc 1 ⌊x⌋₊ := mem_Icc.mpr ⟨le_rfl,by omega⟩
  have h2m : 2∈Icc 1 ⌊x⌋₊ := mem_Icc.mpr ⟨by decide,h2⟩
  have ha (k : ℕ) : dyadicCountDifference k = (if k=1 then 1 else 0)-(if k=2 then 2 else 0) := rfl
  simp only [arithmeticKernel,ha,sub_smul,ite_smul,one_smul,zero_smul,sum_sub_distrib,sum_ite_eq',
    if_pos h1m,if_pos h2m,Nat.cast_one,Nat.cast_ofNat,div_one,Complex.real_smul,Complex.ofReal_ofNat]

private abbrev primeExcessCoeff := vonMangoldt-(zeta : ArithmeticFunction ℝ)

private theorem whole_atom_test {N : ℕ} (hN : 2≤N) (J : ℝ → ℂ) :
    (∑ k ∈ Icc 1 N, reciprocalOctaveAtom k • J ((N:ℝ)/k)) =
      arithmeticKernel primeExcessCoeff J N-2*arithmeticKernel primeExcessCoeff J ((N:ℝ)/2)+
        arithmeticKernel alternatingDivisorCoeff J N-(Real.log 2:ℝ) • J N := by
  have h1m : 1∈Icc 1 N := mem_Icc.mpr ⟨le_rfl,by omega⟩
  have hcoeff : dyadicCountDifference*vonMangoldt =
      dyadicCountDifference*primeExcessCoeff+alternatingDivisorCoeff := by
    rw [primeExcessCoeff,alternatingDivisorCoeff,mul_sub,sub_add_cancel]
  have hr (k : ℕ) (hk : k∈Icc 1 N) := atom_as_dyadic_dilation (n := k) (mem_Icc.mp hk).1
  rw [sum_congr (s₁ := Icc 1 N) rfl (fun (k : ℕ) hk => congrArg (fun u : ℝ => u • J ((N:ℝ)/k)) (hr k hk))]
  simp only [sub_smul,ite_smul,
    zero_smul,sum_sub_distrib,sum_ite_eq',if_pos h1m,Nat.cast_one,div_one]
  rw [hcoeff]
  simp only [ArithmeticFunction.add_apply,add_smul,sum_add_distrib]
  have hf (a : ArithmeticFunction ℝ) :
      (∑ k ∈ Icc 1 N, a k • J ((N:ℝ)/k))=arithmeticKernel a J N := by rw [arithmeticKernel,Nat.floor_natCast]
  rw [hf,hf,arithmeticKernel_mul,dyadic_kernel_two (by exact_mod_cast hN)]

private theorem atom_test_bound {N : ℕ} (hN : 0<N) (J : ℝ → ℂ)
    {P L : ℝ} (hp : ∀ y : ℝ, 0<y → ‖J y‖≤P) (hz : ∀ y≤1,J y=0)
    (hi : ∀ {x y : ℝ}, 0<x → x≤y → ‖J y-J x‖≤L*(Real.log y-Real.log x)) (hL : 0≤L) :
    ‖∑ k ∈ Icc 1 N, reciprocalOctaveAtom k • J ((N:ℝ)/k)‖ ≤
      (P+L)*∑ n ∈ Icc 1 N, |reciprocalOctaveError n| := by
  let V (n : ℕ) : ℂ := (n:ℝ) • J ((N:ℝ)/n)
  have hnR : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have he (n : ℕ) (hn : n∈Icc 1 N) :
      (reciprocalOctaveAtom n/n) • V n = reciprocalOctaveAtom n • J ((N:ℝ)/n) := by
    dsimp only [V]
    rw [smul_smul,div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (show 0<n from (mem_Icc.mp hn).1).ne')]
  have hV0 : V (N+1)=0 := by
    dsimp only [V]
    rw [hz _ ((div_le_one (by positivity : 0<((N+1:ℕ):ℝ))).mpr (by exact_mod_cast Nat.le_succ N)),smul_zero]
  have ht := sum_smul_eq_prefix_differences (fun n : ℕ => reciprocalOctaveAtom n/n) V N
  rw [sum_congr rfl he,hV0,smul_zero,zero_add] at ht
  have hr (n : ℕ) (hn : n∈Icc 1 N) : (∑ j ∈ Icc 1 n, reciprocalOctaveAtom j/j) = reciprocalOctaveError n := by
    rw [show Icc 1 n=Ioc 0 n by ext j; simp only [mem_Icc,mem_Ioc]; omega,
      octave_atom_weighted_prefix (mem_Icc.mp hn).1,reciprocalOctaveError]
  rw [ht,mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n hn
  rw [hr n hn,norm_smul,Real.norm_eq_abs,mul_comm (P+L)]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hn0 : (0:ℝ)<n := Nat.cast_pos.mpr (mem_Icc.mp hn).1
  let x := (N:ℝ)/(n+1)
  let y := (N:ℝ)/n
  have hx : 0<x := div_pos hnR (by positivity)
  have hxy : x≤y := div_le_div_of_nonneg_left hnR.le hn0 (by linarith)
  have hd := hi hx hxy
  have hl : (n:ℝ)*(Real.log y-Real.log x)≤1 := by
    dsimp only [x,y]; rw [Real.log_div hnR.ne' hn0.ne',Real.log_div hnR.ne' (by positivity : (n:ℝ)+1≠0)]
    have hu := Real.log_le_sub_one_of_pos (div_pos (by positivity : 0<(n:ℝ)+1) hn0)
    rw [Real.log_div (by positivity : (n:ℝ)+1≠0) hn0.ne'] at hu
    have hv := mul_le_mul_of_nonneg_left hu hn0.le
    rw [show (n:ℝ)*((n+1)/n-1)=1 by field_simp [hn0.ne']; ring] at hv
    linarith only [hv]
  have hi' : (n:ℝ)*‖J y-J x‖≤L := calc
    _ ≤ (n:ℝ)*(L*(Real.log y-Real.log x)) := mul_le_mul_of_nonneg_left hd hn0.le
    _ = L*((n:ℝ)*(Real.log y-Real.log x)) := by ring
    _ ≤ L := mul_le_of_le_one_right hL hl
  have eqn : V n-V (n+1) = (n:ℝ) • (J y-J x)-J x := by
    dsimp only [V,x,y]
    rw [Nat.cast_add,Nat.cast_one,add_smul,one_smul,smul_sub]; abel
  rw [eqn]
  apply (norm_sub_le _ _).trans
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hn0]
  linarith only [hi',hp _ hx]

private theorem wave_error_four {F : ℝ → ℂ} {ρ d : ℂ} {C x : ℝ}
    (hC : 0≤C) (hx : 4≤x) (h : ∀ u : ℝ,1≤u → ‖F u-(u:ℂ)^ρ*d‖≤C*Real.sqrt u) :
    ‖(F x-F (x/2))-2*(F (x/2)-F (x/2/2)) -
      (x:ℂ)^ρ*(d*((1-(2:ℂ)^(-ρ))*(1-2*(2:ℂ)^(-ρ))))‖ ≤ 6*C*Real.sqrt x := by
  let E (u : ℝ) := F u-(u:ℂ)^ρ*d
  have a : ‖E x‖≤C*Real.sqrt x := h _ (by linarith)
  have b := (h (x/2) (by linarith only [hx])).trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (by linarith only [hx] : x/2≤x)) hC)
  have c := (h (x/2/2) (by linarith only [hx])).trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (by linarith only [hx] : x/2/2≤x)) hC)
  change ‖E (x/2)‖≤_ at b
  change ‖E (x/2/2)‖≤_ at c
  rw [←activated_wave d ρ (by linarith only [hx] : 0<x)]
  have eqn : (F x-F (x/2))-2*(F (x/2)-F (x/2/2)) -
      (((x:ℂ)^ρ*d-((x/2:ℝ):ℂ)^ρ*d)-2*(((x/2:ℝ):ℂ)^ρ*d-((x/2/2:ℝ):ℂ)^ρ*d)) =
      (E x-E (x/2))-2*(E (x/2)-E (x/2/2)) := by dsimp only [E]; ring
  rw [eqn]
  apply (norm_sub_le _ _).trans
  rw [norm_mul,show ‖(2:ℂ)‖=(2:ℝ) by norm_num]
  linarith only [a,b,c,norm_sub_le (E x) (E (x/2)),norm_sub_le (E (x/2)) (E (x/2/2))]

/-- Any right zero forces absolute mass in the actual reciprocal prime
octaves at every terminal; the analytic test has fixed, nonzero amplitude. -/
theorem reciprocal_octave_mass_at_right_zero {ρ : ℂ} (hhalf : 1/2<ρ.re) (hone : ρ.re<1)
    (hz : riemannZeta ρ=0) : ∃ a C : ℝ, 0<a ∧ 0≤C ∧ ∀ N : ℕ, 4≤N →
      a*(N:ℝ)^ρ.re ≤ C*(Real.sqrt N+Real.log (N+1)+1+∑ n ∈ Icc 1 N, |reciprocalOctaveError n|) := by
  obtain ⟨k,d,C,hd,hC,hinc,hwave⟩ := exists_alternating_prime_kernel_at_zero hhalf hone hz
  let H := arithmeticKernel alternatingDivisorCoeff (centeredDirichletTest k ρ)
  let J := dyadicDifference H
  let G := arithmeticKernel primeExcessCoeff H
  let v := d*((1-(2:ℂ)^(-ρ))*(1-2*(2:ℂ)^(-ρ)))
  have hv : v≠0 := mul_ne_zero hd (dyadic_wave_factor hhalf hone)
  have hG (x : ℝ) (hx : 1≤x) : ‖G x-(x:ℂ)^ρ*d‖≤C*Real.sqrt x := by
    have hs := hwave x hx
    rw [alternatingPrimeExcess,mul_comm,arithmeticKernel_mul] at hs
    exact hs
  have hH (x : ℝ) (hx : x≤1) : H x=0 :=
    kernel_before_one _ _ (by simp [centeredDirichletTest]) hx
  obtain ⟨hJ,hJb,hJi⟩ := dyadic_test_bounds hC hH hinc
  have hlog := Real.log_nonneg (by norm_num : (1:ℝ)≤2)
  let P := C*Real.log 2
  let L := 2*C
  let T := C*6+L+Real.log 2*P+(P+L)
  have hP : 0≤P := mul_nonneg hC hlog
  have hL : 0≤L := by dsimp only [L]; positivity
  have hLP := mul_nonneg hlog hP
  have hT : 0≤T := by dsimp only [T]; positivity
  refine ⟨‖v‖,T,norm_pos_iff.mpr hv,hT,fun N hN => ?_⟩
  have hN0 : 0<N := by omega
  have hnR : (0:ℝ)<N := Nat.cast_pos.mpr hN0
  have hN4 : (4:ℝ)≤N := by exact_mod_cast hN
  let S := ∑ n ∈ Icc 1 N, |reciprocalOctaveError n|
  let A := ∑ n ∈ Icc 1 N, reciprocalOctaveAtom n • J ((N:ℝ)/n)
  let U := arithmeticKernel alternatingDivisorCoeff J N
  let Z := (Real.log 2:ℝ) • J N
  let V := (G N-G ((N:ℝ)/2))-2*(G ((N:ℝ)/2)-G ((N:ℝ)/2/2))
  let W := ((N:ℝ):ℂ)^ρ*v
  have hA : ‖A‖≤(P+L)*S := atom_test_bound hN0 J hJb hJ hJi hL
  have hU : ‖U‖≤L*Real.log (N+1) := alternating_bounded_test hJ hJi N hN0
  have hZ : ‖Z‖≤Real.log 2*P := by
    dsimp only [Z]; rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hlog]
    exact mul_le_mul_of_nonneg_left (hJb _ hnR) hlog
  have hV : ‖V-W‖≤6*C*Real.sqrt N := wave_error_four hC hN4 hG
  have eqn : A = V+U-Z := by
    change (∑ n ∈ Icc 1 N, reciprocalOctaveAtom n • J ((N:ℝ)/n))=_
    rw [whole_atom_test (by omega : 2≤N),show J=dyadicDifference H by rfl,
      kernel_dyadic_difference primeExcessCoeff H hH hnR.le,
      kernel_dyadic_difference primeExcessCoeff H hH (by positivity : 0 ≤ (N:ℝ)/2)]
  have hW : ‖W‖≤(P+L)*S+L*Real.log (N+1)+Real.log 2*P+6*C*Real.sqrt N := by
    have he : W=A-U+Z-(V-W) := by rw [eqn]; abel
    calc ‖W‖ = ‖A-U+Z-(V-W)‖ := congrArg norm he
         _ ≤ _ := by linarith only [norm_sub_le (A-U+Z) (V-W),norm_add_le (A-U) Z,norm_sub_le A U,hA,hU,hZ,hV]
  have hSw : ‖W‖=‖v‖*(N:ℝ)^ρ.re := by
    dsimp only [W]; rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hnR,mul_comm]
  rw [hSw] at hW
  have hsum : 0≤S := sum_nonneg (fun n _ => abs_nonneg _)
  have hln : 0≤Real.log ((N:ℝ)+1) := Real.log_nonneg (by linarith only [hnR])
  have aT : P+L≤T := by dsimp only [T]; linarith only [hC,hL,hLP]
  have bT : L≤T := by dsimp only [T]; linarith only [hC,hL,hLP,hP]
  have cT : Real.log 2*P≤T := by dsimp only [T]; linarith only [hC,hL,hP]
  have dT : 6*C≤T := by dsimp only [T]; linarith only [hL,hP,hLP]
  change _ ≤ T*(Real.sqrt N+Real.log (N+1)+1+S)
  linarith only [hW,mul_le_mul_of_nonneg_right aT hsum,mul_le_mul_of_nonneg_right bT hln,
    cT,mul_le_mul_of_nonneg_right dT (Real.sqrt_nonneg N)]

#print axioms reciprocal_octave_mass_at_right_zero

private theorem weight_after_terminal {Y n : ℕ} (hn : Y≤n) : octaveParityWeight Y n=0 := by
  unfold octaveParityWeight
  apply sum_eq_zero
  intro d hd
  have hu := (div_le_self (Nat.cast_nonneg Y) (Nat.one_le_cast.mpr (mem_Icc.mp hd).1 : 1≤(d:ℝ))).trans (Nat.cast_le.mpr hn)
  simp only [octaveUnitClip,max_eq_left (sub_nonpos.mpr hu),min_eq_right (by norm_num : (0:ℝ)≤1),mul_zero]

private theorem weighted_absolute_octave {ε : ℝ} (he : |ε|=1) (Y : ℕ) :
    (∑ n ∈ Icc 1 Y, |reciprocalOctaveError n| * octaveParityWeight Y n) ≤ Real.log Y+Real.log 2+
      2*∑ n ∈ Icc 1 Y, max (-(ε*reciprocalOctaveError n)) 0 := by
  let e := reciprocalOctaveError
  let w := octaveParityWeight Y
  have hs : ε*(∑ n ∈ Icc 1 Y, e n*w n) ≤ Real.log Y+Real.log 2 := by
    apply (le_abs_self _).trans
    rw [abs_mul,he,one_mul]
    exact abs_reciprocal_octave_parity_mean Y
  have row (n : ℕ) : |e n| *w n ≤ ε*(e n*w n)+2*max (-(ε*e n)) 0 := by
    have ha : |ε*e n|=|e n| := by rw [abs_mul,he,one_mul]
    have hd : |e n|=ε*e n+2*max (-(ε*e n)) 0 := by
      rw [←ha]; by_cases h : 0≤ε*e n
      · rw [abs_of_nonneg h,max_eq_right (neg_nonpos.mpr h)]; ring
      · rw [abs_of_nonpos (le_of_not_ge h),max_eq_left (neg_nonneg.mpr (le_of_not_ge h))]; ring
    rw [hd,add_mul,mul_assoc,mul_assoc]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (le_max_right _ _)
      (octave_parity_weight_range Y n).2) (by norm_num : (0:ℝ)≤2))
  have hh := sum_le_sum (s := Icc 1 Y) (fun n _ => row n)
  rw [sum_add_distrib,←mul_sum,←mul_sum] at hh
  exact hh.trans (add_le_add hs le_rfl)

/-- Integer terminal averaging controls every middle index by the total
of either sign on the original prefix, with a uniform loss. -/
theorem reciprocal_octave_middle_abs_from_one_sign {N : ℕ} (hN : 0<N) {ε : ℝ} (he : |ε|=1) :
    (∑ n ∈ (Icc 2 (N/2)).filter (fun n => 2*N≤n*n), |reciprocalOctaveError n|) ≤
      16*(Real.log N+Real.log 2+2*∑ n ∈ Icc 1 N, max (-(ε*reciprocalOctaveError n)) 0) := by
  let S := (Icc 2 (N/2)).filter (fun n => 2*N≤n*n)
  let T := Icc 1 N
  let e := reciprocalOctaveError
  let F (n : ℕ) (Y : ℕ) := |e n| *octaveParityWeight Y n
  let B := Real.log N+Real.log 2+2*∑ n ∈ T,max (-(ε*e n)) 0
  have non (n Y : ℕ) : 0≤F n Y := mul_nonneg (abs_nonneg _) (octave_parity_weight_range Y n).1
  have lower (n : ℕ) (hn : n∈S) : (N:ℝ)*|e n| ≤ 16*∑ Y ∈ T, F n Y := by
    obtain ⟨hm,hs⟩ := mem_filter.mp hn
    obtain ⟨hl,hu⟩ := mem_Icc.mp hm
    have hb := octave_parity_terminal_mass hl hs (by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le (by decide : 0<2)).mp hu)
    dsimp only [F,T]; rw [←mul_sum]
    exact (mul_le_mul_of_nonneg_right hb (abs_nonneg _)).trans_eq (by ring)
  have upper (Y : ℕ) (hY : Y∈T) : (∑ n ∈ S,F n Y)≤B := by
    have hyt := (mem_Icc.mp hY).2
    have hys : Icc 1 Y ⊆ T := Icc_subset_Icc le_rfl hyt
    have hst : S ⊆ T := fun n hn => by
      obtain ⟨h,_⟩ := mem_filter.mp hn
      obtain ⟨hl,hu⟩ := mem_Icc.mp h
      exact mem_Icc.mpr ⟨by omega,hu.trans (Nat.div_le_self N 2)⟩
    have hr : (∑ n ∈ Icc 1 Y,F n Y) = ∑ n ∈ T,F n Y := by
      apply sum_subset hys
      intro n hn hny
      have hnY : Y≤n := le_of_not_gt (fun hg => hny (mem_Icc.mpr ⟨(mem_Icc.mp hn).1,hg.le⟩))
      dsimp only [F]; rw [weight_after_terminal hnY,mul_zero]
    have hsmall := sum_le_sum_of_subset_of_nonneg hys (f := fun n => max (-(ε*e n)) 0) (fun n _ _ => le_max_right _ _)
    calc _ ≤ ∑ n ∈ T,F n Y := sum_le_sum_of_subset_of_nonneg hst (fun n _ _ => non n Y)
         _ = _ := hr.symm
         _ ≤ _ := weighted_absolute_octave he Y
         _ ≤ B := by
           dsimp only [B]
           linarith only [hsmall,Real.log_le_log (Nat.cast_pos.mpr (mem_Icc.mp hY).1) (Nat.cast_le.mpr hyt)]
  have lo := sum_le_sum lower
  rw [←mul_sum,←mul_sum,sum_comm] at lo
  have up := sum_le_sum upper
  rw [sum_const,nsmul_eq_mul,show T.card=N by simp [T,Nat.card_Icc]] at up
  have hN0 : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have bound : (N:ℝ)*(∑ n ∈ S, |e n|) ≤ (N:ℝ)*(16*B) :=
    lo.trans ((mul_le_mul_of_nonneg_left up (by norm_num : (0:ℝ)≤16)).trans_eq (by ring))
  exact (mul_le_mul_iff_right₀ hN0).mp bound

#print axioms reciprocal_octave_middle_abs_from_one_sign


private theorem octave_error_bounded {n : ℕ} (hn : 0<n) : |reciprocalOctaveError n|≤15 := by
  let S := Ioc (n/2) n
  let A := ∑ k ∈ S, vonMangoldt k/(k:ℝ)
  have hn0 : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hA : 0≤A := sum_nonneg (fun k _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))
  have hrow (k : ℕ) (hk : k∈S) : vonMangoldt k/(k:ℝ) ≤ (2/(n:ℝ))*vonMangoldt k := by
    have hilo := (mem_Ioc.mp hk).1
    have hk0 : 0<k := (Nat.zero_le _).trans_lt hilo
    have ht : n≤2*k := by omega
    have hh : (1:ℝ)/k ≤ 2/(n:ℝ) :=
      (div_le_div_iff₀ (Nat.cast_pos.mpr hk0) hn0).mpr (by simpa only [one_mul] using (show (n:ℝ)≤2*k by exact_mod_cast ht))
    rw [show vonMangoldt k/(k:ℝ)=((1:ℝ)/k)*vonMangoldt k by ring]
    exact mul_le_mul_of_nonneg_right hh vonMangoldt_nonneg
  have hsub : S ⊆ Icc 1 n := fun k hk => mem_Icc.mpr
    ⟨(Nat.zero_le _).trans_lt (mem_Ioc.mp hk).1,(mem_Ioc.mp hk).2⟩
  have hmass := (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => vonMangoldt_nonneg)).trans
    (_root_.RHTower.sum_vonMangoldt_Icc_le_seven n)
  have hA' : A≤14 := (sum_le_sum hrow).trans (by
    rw [←mul_sum]
    exact (mul_le_mul_of_nonneg_left hmass (by positivity : 0≤2/(n:ℝ))).trans_eq (by field_simp [hn0.ne']; norm_num))
  change |A-Real.log 2|≤15
  rw [abs_le]
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hl0 := Real.log_nonneg (by norm_num : (1:ℝ)≤2)
  constructor <;> linarith only [hA,hA',hl,hl0]

/-- Total cost of indices up to the square-root transition. -/
private theorem early_octave_abs (N M : ℕ) :
    (∑ n ∈ (Icc 1 M).filter (fun n => n*n≤2*N), |reciprocalOctaveError n|) ≤ 15*Real.sqrt (2*N) := by
  let T := (Icc 1 M).filter (fun n => n*n≤2*N)
  have hs : T ⊆ Icc 1 ⌊Real.sqrt (2*N)⌋₊ := by
    intro n hn
    obtain ⟨hn,ht⟩ := mem_filter.mp hn
    have hr : (n:ℝ)≤Real.sqrt (2*N) := Real.le_sqrt_of_sq_le (by exact_mod_cast (by simpa only [sq] using ht : n^2≤2*N))
    exact mem_Icc.mpr ⟨(mem_Icc.mp hn).1,Nat.le_floor hr⟩
  have hcard : (T.card:ℝ)≤Real.sqrt (2*N) := by
    apply le_trans _ (Nat.floor_le (Real.sqrt_nonneg _))
    exact_mod_cast (show T.card≤⌊Real.sqrt (2*N)⌋₊ by simpa [Nat.card_Icc] using card_le_card hs)
  have ht := sum_le_sum (s := T) (fun n hn => octave_error_bounded (n := n) (mem_Icc.mp (mem_filter.mp hn).1).1)
  rw [sum_const,nsmul_eq_mul] at ht
  exact ht.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hcard (by norm_num : (0:ℝ)≤15))


/-- Mass of one sign of the genuine reciprocal octave on a square-root window. -/
def reciprocalOctaveSignMass (ε : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 N).filter (fun n => N<n*n), max (ε*reciprocalOctaveError n) 0

private theorem half_abs_from_window_sign {N : ℕ} (hN : 0<N) {ε : ℝ} (he : |ε|=1) :
    (∑ n ∈ Icc 1 (N/2), |reciprocalOctaveError n|) ≤ 15*Real.sqrt (2*N)+
      16*(Real.log N+Real.log 2+2*(15*Real.sqrt (2*N)+reciprocalOctaveSignMass ε N)) := by
  let S := (Icc 2 (N/2)).filter (fun n => 2*N≤n*n)
  let e := reciprocalOctaveError
  let s (n : ℕ) := max (ε*e n) 0
  have hpos (n : ℕ) : s n≤|e n| := by
    apply max_le _ (abs_nonneg _)
    exact (le_abs_self _).trans_eq (by rw [abs_mul,he,one_mul])
  have small : (∑ n ∈ (Icc 1 N).filter (fun n => ¬N<n*n),s n) ≤ 15*Real.sqrt (2*N) := by
    apply (sum_le_sum fun n _ => hpos n).trans
    apply le_trans _ (early_octave_abs N N)
    apply sum_le_sum_of_subset_of_nonneg _ (fun n _ _ => abs_nonneg _)
    intro n hn
    obtain ⟨hn,hm⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hn,by omega⟩
  have hall : (∑ n ∈ Icc 1 N,s n) ≤ 15*Real.sqrt (2*N)+reciprocalOctaveSignMass ε N := by
    rw [←sum_filter_add_sum_filter_not (Icc 1 N) (fun n => N<n*n)]
    change reciprocalOctaveSignMass ε N+_≤_
    linarith only [small]
  have hbound := reciprocal_octave_middle_abs_from_one_sign hN (ε := -ε) (by rwa [abs_neg])
  simp only [neg_mul,neg_neg] at hbound
  have hsub : ((Icc 1 (N/2)).filter (fun n => ¬n*n≤2*N)) ⊆ S := by
    intro n hn
    obtain ⟨hn,hh⟩ := mem_filter.mp hn
    obtain ⟨hl,hu⟩ := mem_Icc.mp hn
    have hn2 : 2≤n := by
      by_contra! hc
      have h1 : n=1 := by omega
      rw [h1,one_mul] at hh
      omega
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hn2,hu⟩,(lt_of_not_ge hh).le⟩
  have hhi := (sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => abs_nonneg (e n))).trans hbound
  have hlow := early_octave_abs N (N/2)
  rw [←sum_filter_add_sum_filter_not (Icc 1 (N/2)) (fun n => n*n≤2*N)]
  change _ ≤ 15*Real.sqrt (2*N)+16*(Real.log N+Real.log 2+2*(15*Real.sqrt (2*N)+reciprocalOctaveSignMass ε N))
  change _ ≤ 16*(Real.log N+Real.log 2+2*∑ n ∈ Icc 1 N,s n) at hhi
  linarith only [hlow,hhi,hall]

/-- Every actual right zero forces both signs on every sufficiently large
square-root window. The constants are uniform in sign and terminal. -/
theorem both_reciprocal_octave_signs_at_right_zero {ρ : ℂ} (hhalf : 1/2<ρ.re) (hone : ρ.re<1)
    (hz : riemannZeta ρ=0) : ∃ a C : ℝ, 0<a ∧ 0≤C ∧ ∀ N : ℕ, 8≤N → ∀ ε : ℝ, |ε|=1 →
      a*(N:ℝ)^ρ.re ≤ C*(Real.sqrt (2*N)+Real.log (N+1)+1+reciprocalOctaveSignMass ε N) := by
  obtain ⟨a,C,ha,hC,h⟩ := reciprocal_octave_mass_at_right_zero hhalf hone hz
  refine ⟨a/4,500*C,by positivity,by positivity,fun N hN ε he => ?_⟩
  let M := N/2
  have hM : 4≤M := by dsimp only [M]; omega
  have hmN : M≤N := Nat.div_le_self _ _
  have hn0 : 0<N := by omega
  have hgap : (N:ℝ)≤4*(M:ℝ) := by exact_mod_cast (show N≤4*M by dsimp only [M]; omega)
  have hβ : 0≤ρ.re := by linarith only [hhalf]
  have hx : (N:ℝ)^ρ.re≤4*(M:ℝ)^ρ.re := calc
    _ ≤ (4*(M:ℝ))^ρ.re := Real.rpow_le_rpow (Nat.cast_nonneg _) hgap hβ
    _ = (4:ℝ)^ρ.re*(M:ℝ)^ρ.re := Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right ((Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤4) hone.le).trans_eq
      (Real.rpow_one 4)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  let P := Real.sqrt (2*N)+Real.log (N+1)+1+reciprocalOctaveSignMass ε N
  have hs := half_abs_from_window_sign hn0 he
  have hs0 : 0≤reciprocalOctaveSignMass ε N := sum_nonneg (fun n _ => le_max_right _ _)
  have hsq : Real.sqrt M≤Real.sqrt (2*N) := Real.sqrt_le_sqrt (by exact_mod_cast (show M≤2*N by omega))
  have hln : Real.log ((M:ℝ)+1)≤Real.log ((N:ℝ)+1) :=
    Real.log_le_log (by positivity) (add_le_add (Nat.cast_le.mpr hmN) le_rfl)
  have hlg := Real.log_le_log (Nat.cast_pos.mpr hn0 : (0:ℝ)<N) (by linarith : (N:ℝ)≤N+1)
  have hlg0 := Real.log_nonneg (by linarith only [(Nat.cast_nonneg N : (0:ℝ)≤N)] : (1:ℝ)≤(N:ℝ)+1)
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have htotal : Real.sqrt M+Real.log (M+1)+1+(∑ n ∈ Icc 1 M,|reciprocalOctaveError n|)≤500*P := by
    dsimp only [P]
    linarith only [hs,hsq,hln,hlg,hlg0,hl2,Real.sqrt_nonneg (2*(N:ℝ)),hs0]
  calc _ ≤ a*(M:ℝ)^ρ.re := by linarith only [mul_le_mul_of_nonneg_left hx ha.le]
       _ ≤ _ := h M hM
       _ ≤ _ := (mul_le_mul_of_nonneg_left htotal hC).trans_eq (by ring)

#print axioms both_reciprocal_octave_signs_at_right_zero


private theorem octave_arch_cost {b : ℝ} (hb : 1/2≤b) {N : ℕ} (hN : 0<N) :
    Real.sqrt (2*N)+Real.log (N+1)+1≤7*(N:ℝ)^b := by
  have hn1 : (1:ℝ)≤N := Nat.one_le_cast.mpr hN
  have hn0 : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hs : Real.sqrt N≤(N:ℝ)^b := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hn1 hb
  have ht : Real.sqrt (2*N)≤2*Real.sqrt N := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩) (Real.sqrt_nonneg _)
  have hh := Real.log_le_sub_one_of_pos (Real.sqrt_pos_of_pos (by positivity : 0<(N:ℝ)+1))
  rw [Real.log_sqrt (by positivity : 0≤(N:ℝ)+1)] at hh
  have hu := Real.sqrt_le_sqrt (by linarith only [hn1] : (N:ℝ)+1≤2*N)
  have hh1 := Real.one_le_sqrt.mpr hn1
  linarith only [hs,ht,hh,hu,hh1]

open Filter Topology in
/-- A one-sided budget for the combined error on arbitrarily large windows
bounds every actual zero. Each sign has its own cofinal test. -/
theorem zero_abscissa_of_cofinal_reciprocal_octave_mass {b ε : ℝ} (hb : 1/2≤b) (he : |ε|=1)
    (h : ∃ A : ℝ, ∃ᶠ N : ℕ in atTop, reciprocalOctaveSignMass ε N≤A*(N:ℝ)^b) :
    _root_.RHTower.zetaZeroAbscissa≤b := by
  obtain ⟨A,hA⟩ := h
  apply csSup_le _root_.RHTower.zetaZeroReSet_nonempty
  rintro x ⟨ρ,hz,rfl⟩
  by_contra! hρ
  have hone : ρ.re<1 := lt_of_not_ge (fun hh => riemannZeta_ne_zero_of_one_le_re hh hz)
  obtain ⟨a,K,ha,hK,hw⟩ := both_reciprocal_octave_signs_at_right_zero (hb.trans_lt hρ) hone hz
  let B := K*(7+A)
  have hlim : Tendsto (fun n : ℕ => B*(n:ℝ)^(-(ρ.re-b))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (sub_pos.mpr hρ)).comp tendsto_natCast_atTop_atTop).const_mul B
  obtain ⟨N,hs,hn8,hgap⟩ := (hA.and_eventually ((eventually_ge_atTop 8).and (hlim.eventually_lt_const ha))).exists
  have hn : 0<N := by omega
  have hnR : (0:ℝ)<N := Nat.cast_pos.mpr hn
  have hsmall : a*(N:ℝ)^ρ.re≤B*(N:ℝ)^b := (hw N hn8 ε he).trans (by
    apply le_trans (mul_le_mul_of_nonneg_left (add_le_add (octave_arch_cost hb hn) hs) hK)
    apply le_of_eq
    dsimp only [B]; ring)
  have hlt : B*(N:ℝ)^b<a*(N:ℝ)^ρ.re := calc
    _ = (B*(N:ℝ)^(-(ρ.re-b)))*(N:ℝ)^ρ.re := by
        rw [mul_assoc B ((N:ℝ)^(-(ρ.re-b))) ((N:ℝ)^ρ.re),←Real.rpow_add hnR,show -(ρ.re-b)+ρ.re=b by ring]
    _ < _ := mul_lt_mul_of_pos_right hgap (Real.rpow_pos_of_pos hnR _)
  exact hlt.not_ge hsmall

open Filter in
/-- A five-sixths bound for just the negative reciprocal-octave mass on
cofinally many windows pays the original signed prefix at every endpoint. -/
theorem eleven_thirds_of_cofinal_reciprocal_octave_deficit
    (h : ∃ A : ℝ, ∃ᶠ N : ℕ in atTop, reciprocalOctaveSignMass (-1) N≤A*(N:ℝ)^(5/6:ℝ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, |seventeenNinthsConductorPrefix N|≤C*(N:ℝ)^(11/3:ℝ) :=
  five_sixths_iff_seventeenNinthsConductorPrefix.mp
    (zero_abscissa_of_cofinal_reciprocal_octave_mass (by norm_num) (by norm_num) h)

#print axioms eleven_thirds_of_cofinal_reciprocal_octave_deficit

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
