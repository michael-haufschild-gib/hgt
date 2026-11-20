import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.UniformCancellationOnTruncatedOddQuotientIntervals
import GaloisForLFunctions.ExceptionalLayerTheory.GrowingQuotientBandsInBinomialCarries

/-!
# A power saving on every odd-quotient denominator interval

On an octave of denominators starting at u, a Chebyshev error of order
u^b costs O(H u^(b−1)) after accounting for the variation of the
quotient digit. Those octave costs are geometrically summable. Cutting at
H^(1/(2−b)) balances them against the absolute mass of small denominators.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open _root_.RHTower

private theorem octave_bound {b C : ℝ} (hb : 0≤b) (hb1 : b<1) (hC : 0≤C)
    (theta : ∀ n : ℕ, 1≤n → |Chebyshev.theta n-(n:ℝ)| ≤ C*(n:ℝ)^b)
    {H u v : ℕ} (hu : 0<u) (huv : u≤v) (hvH : v≤H) (hv : v≤2*u) :
    |oddQuotientPrimeExcess (Ioc u v) H| ≤ 6*C*H*(u:ℝ)^(b-1) := by
  have ur : 0<(u:ℝ) := Nat.cast_pos.mpr hu
  let E := C*(2*(u:ℝ))^b
  have pos : 0≤E := mul_nonneg hC (Real.rpow_nonneg (by positivity) _)
  have paid := odd_quotient_tail_variation_bound H u v hu huv E (fun k hk =>
    (theta k (hu.trans_le (mem_Icc.mp hk).1)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg k) (by exact_mod_cast (mem_Icc.mp hk).2.trans hv) hb) hC))
  have pow2 : (2:ℝ)^b ≤ 2 := (Real.rpow_le_rpow_of_exponent_le (by norm_num) hb1.le).trans_eq (Real.rpow_one _)
  have e : E ≤ 2*C*(u:ℝ)^b := by
    dsimp only [E]
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) ur.le]
    have p := mul_le_mul_of_nonneg_right pow2 (mul_nonneg hC (Real.rpow_nonneg ur.le b))
    linarith only [p]
  have quo : (↑(H/u):ℝ) ≤ (H:ℝ)/u := (le_div_iff₀ ur).mpr (by exact_mod_cast Nat.div_mul_le_self H u)
  have one : 1≤(H:ℝ)/u := (one_le_div ur).mpr (Nat.cast_le.mpr (huv.trans hvH))
  have drop : 2+(↑(H/u):ℝ)-(↑(H/v):ℝ) ≤ 3*((H:ℝ)/u) := by
    linarith only [quo,one,Nat.cast_nonneg (α:=ℝ) (H/v)]
  calc _ ≤ E*(3*((H:ℝ)/u)) := paid.trans (mul_le_mul_of_nonneg_left drop pos)
       _ ≤ (2*C*(u:ℝ)^b)*(3*((H:ℝ)/u)) := mul_le_mul_of_nonneg_right e (by positivity)
       _ = _ := by rw [Real.rpow_sub ur,Real.rpow_one]; ring

private theorem tail_bound {b C : ℝ} (hb : 0≤b) (hb1 : b<1) (hC : 0≤C)
    (theta : ∀ n : ℕ, 1≤n → |Chebyshev.theta n-(n:ℝ)| ≤ C*(n:ℝ)^b) :
    ∃ K : ℝ, 0<K ∧ ∀ H u v : ℕ, 0<u → u≤v → v≤H →
      |oddQuotientPrimeExcess (Ioc u v) H| ≤ K*H*(u:ℝ)^(b-1) := by
  let ρ := (2:ℝ)^(b-1)
  have hρ : 0<ρ := Real.rpow_pos_of_pos (by norm_num) _
  have hr : ρ<1 := by
    calc ρ < (2:ℝ)^(0:ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (sub_neg.mpr hb1)
         _ = _ := Real.rpow_zero _
  let K := (6*C+1)/(1-ρ)
  have hk : 0<K := div_pos (by positivity) (sub_pos.mpr hr)
  have id : K*(1-ρ)=6*C+1 := div_mul_cancel₀ _ (sub_pos.mpr hr).ne'
  have budget : 6*C+K*ρ ≤ K := by linarith only [id]
  have alone : 6*C ≤ K := by linarith only [id,mul_pos hk hρ]
  have cover (j : ℕ) : ∀ H u v : ℕ, 0<u → u≤v → v≤H → v≤2^j*u →
      |oddQuotientPrimeExcess (Ioc u v) H| ≤ K*H*(u:ℝ)^(b-1) := by
    induction j with
    | zero =>
      intro H u v hu huv hvH cap
      have eq : v=u := le_antisymm (by simpa using cap) huv
      rw [eq,Ioc_self,oddQuotientPrimeExcess,sum_empty,abs_zero]
      positivity
    | succ j ih =>
      intro H u v hu huv hvH cap
      have p0 : 0≤(H:ℝ)*(u:ℝ)^(b-1) := by positivity
      by_cases h : v≤2*u
      · have bound := octave_bound hb hb1 hC theta hu huv hvH h
        linarith only [bound,mul_le_mul_of_nonneg_right alone p0]
      have split : 2*u≤v := le_of_not_ge h
      have low := octave_bound hb hb1 hC theta hu (show u≤2*u by omega) (split.trans hvH) le_rfl
      have top := ih H (2*u) v (by omega) split hvH (by simpa only [pow_succ,Nat.mul_assoc] using cap)
      have factor : ((2*u:ℕ):ℝ)^(b-1)=ρ*(u:ℝ)^(b-1) := by
        push_cast
        exact Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
      rw [factor] at top
      have add : oddQuotientPrimeExcess (Ioc u (2*u)) H+oddQuotientPrimeExcess (Ioc (2*u) v) H=
          oddQuotientPrimeExcess (Ioc u v) H := sum_Ioc_consecutive _ (by omega) split
      rw [←add]
      apply (abs_add_le ..).trans
      linarith only [low,top,mul_le_mul_of_nonneg_right budget p0]
  refine ⟨K,hk,fun H u v hu huv hvH => cover H H u v hu huv hvH ?_⟩
  exact hvH.trans ((Nat.lt_two_pow_self (n:=H)).le.trans (Nat.le_mul_of_pos_right _ hu))

/-- Each Chebyshev error exponent b above the zero abscissa transfers to
1/(2−b) for every interval of denominators, uniformly at fixed H. -/
theorem odd_quotient_interval_above_abscissa {b : ℝ} (hw : zeroReSup<b) (hb1 : b<1) :
    ∃ D : ℝ, 0<D ∧ ∀ H : ℕ, 1≤H → ∀ x y : ℕ,
      |oddQuotientPrimeExcess (Ioc x y) H| ≤ D*(H:ℝ)^(1/(2-b)) := by
  have half := half_le_zeroReSup.trans_lt hw
  have hb : 0<b := lt_trans (by norm_num : (0:ℝ)<1/2) half
  obtain ⟨A,hA,psi⟩ := exists_abs_chebyshevPsi_sub_le_rpow hw
  obtain ⟨B,hB⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let C := A+|B|
  have hC : 0≤C := add_nonneg hA (abs_nonneg B)
  have theta (n : ℕ) (hn : 1≤n) : |Chebyshev.theta n-(n:ℝ)| ≤ C*(n:ℝ)^b := by
    have h1 : 1≤(n:ℝ) := Nat.one_le_cast.mpr hn
    have root : Real.sqrt n ≤ (n:ℝ)^b := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le h1 half.le
    have d := (hB (n:ℝ)).trans (mul_le_mul (le_abs_self B) root (Real.sqrt_nonneg _) (abs_nonneg _))
    have h := abs_sub_le (Chebyshev.theta n) (Chebyshev.psi n) (n:ℝ)
    rw [abs_sub_comm (Chebyshev.theta n) (Chebyshev.psi n),
      abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _))] at h
    dsimp only [C]
    linarith only [h,d,psi n h1]
  obtain ⟨K,hK,tail⟩ := tail_bound hb.le hb1 hC theta
  refine ⟨8+K,by positivity,fun H hH x y => ?_⟩
  rw [←odd_quotient_interval_clip H x y]
  let v := min y H
  let X := (H:ℝ)^(1/(2-b))
  let M := ⌈X⌉₊
  have hHr : 1≤(H:ℝ) := Nat.one_le_cast.mpr hH
  have hp : 0<2-b := by linarith only [hb1]
  have x1 : 1≤X := Real.one_le_rpow hHr (by positivity)
  have xpos : 0<X := zero_lt_one.trans_le x1
  have Mlo : X≤(M:ℝ) := Nat.le_ceil _
  have Mhi : (M:ℝ) ≤ 2*X := by linarith only [Nat.ceil_lt_add_one xpos.le,x1]
  have xpow : X^(2-b)=(H:ℝ) := by
    dsimp only [X]
    rw [←Real.rpow_mul (zero_le_one.trans hHr),show (1/(2-b))*(2-b)=1 by field_simp [hp.ne'],Real.rpow_one]
  have scale : (H:ℝ)*X^(b-1)=X := by
    rw [←xpow,←Real.rpow_add xpos,show 2-b+(b-1)=1 by ring,Real.rpow_one]
  have head {t : ℕ} (ht : t≤M) : |oddQuotientPrimeExcess (Ioc x t) H| ≤ 8*X := by
    have bound := oddQuotientPrimeExcess_le (Ioc x t) M H (fun n hn =>
      mem_Ioc.mpr ⟨(Nat.zero_le _).trans_lt (mem_Ioc.mp hn).1,(mem_Ioc.mp hn).2.trans ht⟩)
    have const : 1+Real.log 4≤4 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
    linarith only [bound,mul_le_mul_of_nonneg_right const (Nat.cast_nonneg (α:=ℝ) M),Mhi]
  change |oddQuotientPrimeExcess (Ioc x v) H| ≤ (8+K)*X
  by_cases hvx : v≤x
  · rw [Ioc_eq_empty_of_le hvx,oddQuotientPrimeExcess,sum_empty,abs_zero]
    positivity
  by_cases hm : v≤M
  · linarith only [head hm,mul_pos hK xpos]
  let u := max x M
  have uv : u≤v := max_le (le_of_not_ge hvx) (le_of_not_ge hm)
  have ul : X≤(u:ℝ) := Mlo.trans (Nat.cast_le.mpr (le_max_right ..))
  have pu := Real.rpow_le_rpow_of_nonpos xpos ul (sub_nonpos.mpr hb1.le)
  have bound := tail H u v (Nat.cast_pos.mp (xpos.trans_le ul)) uv (min_le_right ..)
  have paid : |oddQuotientPrimeExcess (Ioc u v) H| ≤ K*X := by
    have gg := mul_le_mul_of_nonneg_left pu (mul_nonneg hK.le (Nat.cast_nonneg (α:=ℝ) H))
    calc _ ≤ _ := bound.trans gg
         _ = K*X := by rw [mul_assoc,scale]
  have lo : |oddQuotientPrimeExcess (Ioc x u) H| ≤ 8*X := by
    rcases le_total x M with hs|hs
    · rw [show u=M from max_eq_right hs]
      exact head le_rfl
    · simp only [u,max_eq_left hs,Ioc_self,oddQuotientPrimeExcess,sum_empty,abs_zero]
      positivity
  have add : oddQuotientPrimeExcess (Ioc x u) H+oddQuotientPrimeExcess (Ioc u v) H=
      oddQuotientPrimeExcess (Ioc x v) H := sum_Ioc_consecutive _ (le_max_left ..) uv
  rw [←add]
  exact (abs_add_le ..).trans (by linarith only [lo,paid])

/-- The existing sub-seven-eighths zero bound gives the exact exponent
8/9 simultaneously for every truncated odd-quotient interval. -/
theorem all_odd_quotient_intervals_eight_ninths :
    ∃ D : ℝ, 0<D ∧ ∀ H : ℕ, 1≤H → ∀ x y : ℕ,
      |oddQuotientPrimeExcess (Ioc x y) H| ≤ D*(H:ℝ)^(8/9:ℝ) := by
  have width : zeroReSup < 7/8 := by
    linarith only [ExceptionalLayerTheory.zeroReSup_le_sub_seven_eighths]
  simpa only [show (1:ℝ)/(2-7/8)=8/9 by norm_num] using
    odd_quotient_interval_above_abscissa width (by norm_num)

/-- Every exponent strictly above 24000/27001 is available from the
corpus bound on the zero abscissa. -/
theorem all_odd_quotient_intervals_sub_eight_ninths {c : ℝ} (hc : 24000/27001<c) :
    ∃ D : ℝ, 0<D ∧ ∀ H : ℕ, 1≤H → ∀ x y : ℕ,
      |oddQuotientPrimeExcess (Ioc x y) H| ≤ D*(H:ℝ)^c := by
  by_cases h : c < 1
  · have cp : 0<c := lt_trans (by norm_num : (0:ℝ)<24000/27001) hc
    have width : zeroReSup < 2-1/c := by
      apply ExceptionalLayerTheory.zeroReSup_le_sub_seven_eighths.trans_lt
      have q : 1/c < 2-20999/24000 := (div_lt_iff₀ cp).mpr (by linarith only [hc])
      linarith only [q]
    have h1 : 2-1/c < 1 := by
      have inv : 1<1/c := (lt_div_iff₀ cp).mpr (by simpa only [one_mul] using h)
      linarith only [inv]
    have exp : 1/(2-(2-1/c))=c := by rw [sub_sub_cancel]; simp
    simpa only [exp] using odd_quotient_interval_above_abscissa width h1
  · obtain ⟨D,hD,hd⟩ := all_odd_quotient_intervals_eight_ninths
    refine ⟨D,hD,fun H hH x y => (hd H hH x y).trans ?_⟩
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hH)
      ((by norm_num : (8/9:ℝ)≤1).trans (le_of_not_gt h))) hD.le

end GaloisForLFunctions.ExclusionOfTheCriticalState
