import GaloisForLFunctions.RHTower.Sieve.MoebiusHarmonicArbitraryLogRate

/-!
# Cancellation of the literal Möbius hyperbolic coefficient

Square-root hyperbola inclusion-exclusion retains every common-divisor pair
and subtracts the exact square overlap. The corpus's unconditional log-squared
Mertens saving pays the harmonic short-row count, giving zero mean for the
literal coefficient sum over d*e<=M. This is the constant-profile input to the
Route RP signed pair-sector argument; the variable-profile assembly remains.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

private lemma sum_cutoff (m n : ℕ) (hn : n ≤ m) (f : ℕ → ℝ) :
    (∑ i ∈ Icc 1 m, if i ≤ n then f i else 0) = ∑ i ∈ Icc 1 n, f i := by
  rw [← sum_filter]
  congr 1
  ext i
  simp only [mem_filter,mem_Icc]
  omega

private lemma hyperbola_row (M d : ℕ) (hd : 0 < d) (f : ℕ → ℝ) :
    (∑ e ∈ Icc 1 M, if d*e ≤ M then f d*f e else 0) =
      f d*(∑ e ∈ Icc 1 (M/d), f e) := by
  rw [← sum_filter]
  have hf : {e ∈ Icc 1 M | d*e ≤ M} = Icc 1 (M/d) := by
    ext e
    simp only [mem_filter,mem_Icc]
    have hdiv : e ≤ M/d ↔ d*e ≤ M := by
      rw [Nat.le_div_iff_mul_le hd,Nat.mul_comm]
    have hMd := Nat.div_le_self M d
    omega
  rw [hf,mul_sum]

/-- Exact square-root hyperbola decomposition, with the square overlap retained. -/
theorem routeP_hyperbola_square_identity (M : ℕ) (f : ℕ → ℝ) :
    (∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M,
      if d*e ≤ M then f d*f e else 0) =
    2*(∑ d ∈ Icc 1 (Nat.sqrt M), f d*(∑ e ∈ Icc 1 (M/d), f e))-
      (∑ d ∈ Icc 1 (Nat.sqrt M), f d)^2 := by
  let r := Nat.sqrt M
  let L := fun d e => if d ≤ r then (if d*e ≤ M then f d*f e else 0) else 0
  let Q := fun d e => if d ≤ r then (if e ≤ r then f d*f e else 0) else 0
  have hrr : r*r ≤ M := Nat.sqrt_le M
  have hnext : M < (r+1)*(r+1) := Nat.lt_succ_sqrt M
  have hpoint (d e : ℕ) :
      (if d*e ≤ M then f d*f e else 0) = L d e+L e d-Q d e := by
    by_cases hd : d ≤ r <;> by_cases he : e ≤ r
    · have hp : d*e ≤ M := (Nat.mul_le_mul hd he).trans hrr
      simp [L,Q,hd,he,hp,mul_comm]
    · simp [L,Q,hd,he]
    · simp [L,Q,hd,he,mul_comm]
    · have hp : ¬d*e ≤ M := by
        have h := Nat.mul_le_mul (show r+1 ≤ d by omega) (show r+1 ≤ e by omega)
        omega
      simp [L,Q,hd,he,hp]
  have hL : (∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M, L d e) =
      ∑ d ∈ Icc 1 r, f d*(∑ e ∈ Icc 1 (M/d), f e) := by
    have hp (d : ℕ) : (∑ e ∈ Icc 1 M, L d e) =
        if d ≤ r then (∑ e ∈ Icc 1 M, if d*e ≤ M then f d*f e else 0) else 0 := by
      by_cases hd : d ≤ r <;> simp [L,hd]
    simp_rw [hp]
    rw [sum_cutoff M r (Nat.sqrt_le_self M)]
    apply sum_congr rfl
    intro d hd
    exact hyperbola_row M d (mem_Icc.mp hd).1 f
  have hQ : (∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M, Q d e) =
      (∑ d ∈ Icc 1 r, f d)^2 := by
    have hp (d : ℕ) : (∑ e ∈ Icc 1 M, Q d e) =
        if d ≤ r then f d*(∑ e ∈ Icc 1 r, f e) else 0 := by
      by_cases hd : d ≤ r
      · simp only [Q,if_pos hd]
        rw [sum_cutoff M r (Nat.sqrt_le_self M),mul_sum]
      · simp [Q,hd]
    simp_rw [hp]
    rw [sum_cutoff M r (Nat.sqrt_le_self M),← sum_mul,pow_two]
  have hswap : (∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M, L e d) =
      ∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M, L d e := sum_comm
  simp_rw [hpoint,sum_sub_distrib,sum_add_distrib]
  rw [hswap,hL,hQ]
  ring

/-- Literal Möbius pair coefficient; common-divisor pairs are included. -/
def routePMobiusHyperbolaCoefficient (M : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M,
    if d*e ≤ M then (ArithmeticFunction.moebius d:ℝ)*(ArithmeticFunction.moebius e:ℝ) else 0

private lemma moebius_sum_Icc (N : ℕ) :
    (∑ n ∈ Icc 1 N, (ArithmeticFunction.moebius n:ℝ)) = Sieve.mertensM N := by
  rw [Sieve.mertensM,sum_range_succ',← Ico_add_one_right_eq_Icc,sum_Ico_eq_sum_range]
  simp [add_comm]

/-- The literal pair coefficient has the exact Mertens hyperbola decomposition. -/
theorem routeP_mobius_hyperbola_identity (M : ℕ) :
    routePMobiusHyperbolaCoefficient M =
      2*(∑ d ∈ Icc 1 (Nat.sqrt M),
        (ArithmeticFunction.moebius d:ℝ)*Sieve.mertensM (M/d))-
        (Sieve.mertensM (Nat.sqrt M))^2 := by
  unfold routePMobiusHyperbolaCoefficient
  rw [routeP_hyperbola_square_identity]
  simp_rw [moebius_sum_Icc]

private lemma short_row_bound (M d : ℕ) (hd : d ∈ Icc 1 (Nat.sqrt M))
    (hr : 2 ≤ Nat.sqrt M) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ N : ℕ, Nat.sqrt M ≤ N →
      |Sieve.mertensM N| ≤ B*(N:ℝ)/(Real.log N)^2) :
    |(ArithmeticFunction.moebius d:ℝ)*Sieve.mertensM (M/d)| ≤
      (B*(M:ℝ)/(Real.log (Nat.sqrt M))^2)*(1/(d:ℝ)) := by
  have hd0 : 0 < d := (mem_Icc.mp hd).1
  have hdR : (0:ℝ) < d := by exact_mod_cast hd0
  have hrQ : Nat.sqrt M ≤ M/d := by
    apply (Nat.le_div_iff_mul_le hd0).mpr
    exact (Nat.mul_le_mul_left (Nat.sqrt M) (mem_Icc.mp hd).2).trans (Nat.sqrt_le M)
  have hrR : (1:ℝ) < Nat.sqrt M := by exact_mod_cast hr
  have hl : 0 < Real.log (Nat.sqrt M) := Real.log_pos hrR
  have hlog := Real.log_le_log (by linarith : (0:ℝ)<Nat.sqrt M)
    (show (Nat.sqrt M:ℝ) ≤ (M/d:ℕ) by exact_mod_cast hrQ)
  have hlogs : (Real.log (Nat.sqrt M))^2 ≤ (Real.log (M/d:ℕ))^2 := by
    nlinarith only [hlog,hl]
  have hmuf : |(ArithmeticFunction.moebius d:ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=d))
  have hfloor : ((M/d:ℕ):ℝ)*(d:ℝ) ≤ M := by exact_mod_cast Nat.div_mul_le_self M d
  calc
    _ ≤ |Sieve.mertensM (M/d)| := by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hmuf (abs_nonneg _)
    _ ≤ B*((M/d:ℕ):ℝ)/(Real.log (M/d:ℕ))^2 := hbound _ hrQ
    _ ≤ B*((M/d:ℕ):ℝ)/(Real.log (Nat.sqrt M))^2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hl) hlogs
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hfloor hB
      rw [mul_one_div,div_le_div_iff₀ (sq_pos_of_pos hl) hdR]
      field_simp
      nlinarith only [h]

private lemma mobius_hyperbola_bound (M : ℕ) (hr : 2 ≤ Nat.sqrt M)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ N : ℕ, Nat.sqrt M ≤ N →
      |Sieve.mertensM N| ≤ B*(N:ℝ)/(Real.log N)^2) :
    |routePMobiusHyperbolaCoefficient M|/(M:ℝ) ≤
      2*B*((harmonic (Nat.sqrt M):ℚ):ℝ)/(Real.log (Nat.sqrt M))^2+
        (B/(Real.log (Nat.sqrt M))^2)^2 := by
  have hmN : 1 ≤ M := (show 1 ≤ Nat.sqrt M by omega).trans (Nat.sqrt_le_self M)
  have hm : (0:ℝ) < M := by exact_mod_cast hmN
  have hrR : (1:ℝ) < Nat.sqrt M := by exact_mod_cast hr
  have hl : 0 < Real.log (Nat.sqrt M) := Real.log_pos hrR
  have hs : |∑ d ∈ Icc 1 (Nat.sqrt M),
        (ArithmeticFunction.moebius d:ℝ)*Sieve.mertensM (M/d)| ≤
      (B*(M:ℝ)/(Real.log (Nat.sqrt M))^2)*((harmonic (Nat.sqrt M):ℚ):ℝ) := by
    calc
      _ ≤ ∑ d ∈ Icc 1 (Nat.sqrt M),
          |(ArithmeticFunction.moebius d:ℝ)*Sieve.mertensM (M/d)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc 1 (Nat.sqrt M),
          (B*(M:ℝ)/(Real.log (Nat.sqrt M))^2)*(1/(d:ℝ)) :=
        sum_le_sum (fun d hd => short_row_bound M d hd hr B hB hbound)
      _ = _ := by
        rw [← mul_sum]
        simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
  have hmr := hbound (Nat.sqrt M) le_rfl
  have hcoef : 0 ≤ B/(Real.log (Nat.sqrt M))^2 := by positivity
  have hmr' : |Sieve.mertensM (Nat.sqrt M)| ≤
      (B/(Real.log (Nat.sqrt M))^2)*(Nat.sqrt M:ℝ) := by
    convert hmr using 1
    ring
  have hsq : (Sieve.mertensM (Nat.sqrt M))^2 ≤
      (B/(Real.log (Nat.sqrt M))^2)^2*(M:ℝ) := by
    have h := mul_self_le_mul_self (abs_nonneg _) hmr'
    have hn : (Nat.sqrt M:ℝ)^2 ≤ M := by exact_mod_cast Nat.sqrt_le' M
    have hn' := mul_le_mul_of_nonneg_left hn (sq_nonneg (B/(Real.log (Nat.sqrt M))^2))
    nlinarith only [h,hn',sq_abs (Sieve.mertensM (Nat.sqrt M))]
  rw [div_le_iff₀ hm,routeP_mobius_hyperbola_identity]
  calc
    _ ≤ |2*(∑ d ∈ Icc 1 (Nat.sqrt M),
        (ArithmeticFunction.moebius d:ℝ)*Sieve.mertensM (M/d))|+
        |(Sieve.mertensM (Nat.sqrt M))^2| := abs_sub _ _
    _ ≤ 2*((B*(M:ℝ)/(Real.log (Nat.sqrt M))^2)*((harmonic (Nat.sqrt M):ℚ):ℝ))+
        (B/(Real.log (Nat.sqrt M))^2)^2*(M:ℝ) := by
      rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2),
        abs_of_nonneg (sq_nonneg (Sieve.mertensM (Nat.sqrt M)))]
      exact add_le_add (mul_le_mul_of_nonneg_left hs (by norm_num)) hsq
    _ = _ := by ring

private lemma sqrt_atTop : Tendsto Nat.sqrt atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (b*b)] with M hM
  exact Nat.le_sqrt.mpr hM

/-- The literal Möbius convolution has zero mean, with every common-divisor
pair and the complete square overlap retained. -/
theorem routeP_mobius_hyperbola_div_tendsto_zero :
    Tendsto (fun M : ℕ => routePMobiusHyperbolaCoefficient M/(M:ℝ)) atTop (𝓝 0) := by
  obtain ⟨B,hB,hbound⟩ := Sieve.deningerMertensM_log_pow_rate 2
  obtain ⟨K,hK⟩ := eventually_atTop.mp hbound
  have hl : Tendsto (fun M : ℕ => Real.log (Nat.sqrt M)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp sqrt_atTop)
  have hi : Tendsto (fun M : ℕ => (Real.log (Nat.sqrt M))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hl
  have hg : Tendsto (fun M : ℕ =>
      2*B*((Real.log (Nat.sqrt M))⁻¹^2+(Real.log (Nat.sqrt M))⁻¹)+
        (B*(Real.log (Nat.sqrt M))⁻¹^2)^2) atTop (𝓝 0) := by
    simpa using (((hi.pow 2).add hi).const_mul (2*B)).add (((hi.pow 2).const_mul B).pow 2)
  have habs : Tendsto (fun M : ℕ => |routePMobiusHyperbolaCoefficient M|/(M:ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun M =>
      div_nonneg (abs_nonneg _) (Nat.cast_nonneg M))) _ hg
    filter_upwards [sqrt_atTop.eventually (eventually_ge_atTop (max K 2))] with M hM
    have hr : 2 ≤ Nat.sqrt M := (le_max_right _ _).trans hM
    have hKr : K ≤ Nat.sqrt M := (le_max_left _ _).trans hM
    have hrR : (1:ℝ) < Nat.sqrt M := by exact_mod_cast hr
    have hlog : 0 < Real.log (Nat.sqrt M) := Real.log_pos hrR
    calc
      _ ≤ 2*B*((harmonic (Nat.sqrt M):ℚ):ℝ)/(Real.log (Nat.sqrt M))^2+
          (B/(Real.log (Nat.sqrt M))^2)^2 :=
        mobius_hyperbola_bound M hr B hB (fun N hN => hK N (hKr.trans hN))
      _ ≤ 2*B*(1+Real.log (Nat.sqrt M))/(Real.log (Nat.sqrt M))^2+
          (B/(Real.log (Nat.sqrt M))^2)^2 := by
        apply add_le_add _ le_rfl
        have h := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log (Nat.sqrt M))
          (show 0 ≤ 2*B/(Real.log (Nat.sqrt M))^2 by positivity)
        convert h using 1 <;> ring
      _ = _ := by field_simp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  convert habs using 1
  funext M
  rw [Real.norm_eq_abs,abs_div,
    show |(M:ℝ)| = (M:ℝ) from abs_of_nonneg (Nat.cast_nonneg M)]

end RHTower
