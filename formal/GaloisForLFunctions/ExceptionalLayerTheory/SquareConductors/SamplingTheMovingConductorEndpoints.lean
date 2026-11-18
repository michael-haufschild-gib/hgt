import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheIntegralOnTheRescaledProductShell

/-!
# Sampling at the moving conductor endpoints

A lower product threshold picks a terminal interval of conductors. Rounding
the lower endpoint and including the last conductor cost two samples. A
two-ended power shell is a signed difference of two such intervals.
-/

noncomputable section
open Finset MeasureTheory ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The tail beyond any real lower conductor cut. Clamping to M gives the
zero integral when the entire terminal block lies below the cut. -/
def realTailStart (N M : ℕ) (l : ℝ) := min (M:ℝ) (max (N:ℝ) l)

/-- Both rounding corrections in the discrete conductor tail are bounded
uniformly in the real product boundary, the mesh and the product. -/
theorem real_tail_sampling_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {N M : ℕ}, 0 < N → N ≤ M → ∀ (b : ℕ) {q : ℝ},
      0 < q → ∀ l : ℝ,
      |(∑ n ∈ Ioc N M with l ≤ (n:ℝ), (n:ℝ)*quotientMeshProfile b (q/(n:ℝ)^2)) -
        ∫ x in realTailStart N M l..M, x*quotientMeshProfile b (q/x^2)| ≤ K*(M+1:ℕ) := by
  obtain ⟨C,hC,hmesh⟩ := real_conductor_mesh_sampling
  obtain ⟨D,hD,hsamp⟩ := conductor_mesh_integral_error
  refine ⟨D+2*C,by positivity,fun {N M} hN hNM b q hq l => ?_⟩
  let F := fun x : ℝ => x*quotientMeshProfile b (q/x^2)
  have hN' : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hNM' : (N:ℝ) ≤ M := Nat.cast_le.mpr hNM
  have hMM : (M:ℝ) ≤ (M+1:ℕ) := Nat.cast_le.mpr (Nat.le_succ _)
  have hint {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : IntervalIntegrable F volume x y := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht0 := (lt_min hx hy).trans_le ht.1
    obtain ⟨_,_,hd⟩ := (hmesh b hq ht0).2
    exact hd.continuousAt.continuousWithinAt
  by_cases hl : l ≤ (M:ℝ)
  swap
  · have hem : ((Ioc N M).filter (fun n => l ≤ (n:ℝ))) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro n hn
      exact hl ((mem_filter.mp hn).2.trans (Nat.cast_le.mpr (mem_Ioc.mp (mem_filter.mp hn).1).2))
    rw [hem,sum_empty,realTailStart,min_eq_left ((le_of_not_ge hl).trans (le_max_right _ _)),
      intervalIntegral.integral_same,sub_self,abs_zero]
    positivity
  let r := max (N:ℝ) l
  let a := max (N+1) ⌈r⌉₊
  have hrN : (N:ℝ) ≤ r := le_max_left _ _
  have hrM : r ≤ M := max_le hNM' hl
  have haN : N+1 ≤ a := le_max_left _ _
  have ha : a ≤ M+1 := max_le (Nat.succ_le_succ hNM)
    ((Nat.ceil_le.mpr hrM).trans (Nat.le_succ M))
  have ha0 : 0 < a := (Nat.succ_pos _).trans_le haN
  have har : r ≤ a := (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right (N+1) ⌈r⌉₊))
  have har1 : (a:ℝ) ≤ r+1 := by
    dsimp only [a]
    rw [Nat.cast_max]
    apply max_le
    · push_cast; linarith only [hrN]
    · exact (Nat.ceil_lt_add_one (hN'.trans_le hrN).le).le
  have he : ((Ioc N M).filter fun n => l ≤ (n:ℝ)) = Ico a (M+1) := by
    ext n
    simp only [a,r,mem_filter,mem_Ioc,mem_Ico,max_le_iff,Nat.ceil_le]
    constructor
    · rintro ⟨⟨hlo,hu⟩,hl⟩
      exact ⟨⟨hlo,Nat.cast_le.mpr hlo.le,hl⟩,Nat.lt_succ_of_le hu⟩
    · rintro ⟨⟨hlo,_,hl⟩,hu⟩
      exact ⟨⟨hlo,Nat.le_of_lt_succ hu⟩,hl⟩
  have hprice {x y : ℝ} (hx : N ≤ x) (hxy : x ≤ y) (hy : y ≤ (M+1:ℕ))
      (hlen : y-x ≤ 1) : |∫ t in x..y, F t| ≤ C*(M+1:ℕ) := by
    have hb (t : ℝ) (ht : t ∈ Set.uIoc x y) : ‖F t‖ ≤ C*(M+1:ℕ) := by
      rw [Set.uIoc_of_le hxy] at ht
      exact ((hmesh b hq ((hN'.trans_le hx).trans ht.1)).1).trans
        (mul_le_mul_of_nonneg_left (ht.2.trans hy) hC)
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hxy)] at hh
    exact hh.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hlen (by positivity : 0 ≤ C*(M+1:ℕ)))
  have hlow := hprice hrN har (Nat.cast_le.mpr ha) (by linarith only [har1])
  have hhigh := hprice hNM' hMM le_rfl (by push_cast; ring_nf; exact le_rfl)
  have hM0 := hN'.trans_le hNM'
  have hd0 : (0:ℝ) < (M+1:ℕ) := hM0.trans_le hMM
  have hr0 := hN'.trans_le hrN
  have ha0' := hr0.trans_le har
  have hjoin1 := intervalIntegral.integral_add_adjacent_intervals (hint hr0 ha0') (hint ha0' hd0)
  have hjoin2 := intervalIntegral.integral_add_adjacent_intervals (hint hr0 hM0) (hint hM0 hd0)
  change |(∑ n ∈ (Ioc N M).filter (fun n => l ≤ (n:ℝ)), F n) - ∫ x in realTailStart N M l..M, F x| ≤ _
  rw [he,realTailStart,min_eq_right hrM]
  have hid : (∑ n ∈ Ico a (M+1), F n) - ∫ x in r..M, F x =
      ((∑ n ∈ Ico a (M+1), F n) - ∫ x in (a:ℝ)..((M+1:ℕ):ℝ), F x) +
      (∫ x in (M:ℝ)..((M+1:ℕ):ℝ), F x) - ∫ x in r..a, F x := by linarith only [hjoin1,hjoin2]
  rw [hid]
  apply (abs_sub _ _).trans ((add_le_add ((abs_add_le _ _).trans
    (add_le_add (hsamp ha0 ha b hq) hhigh)) hlow).trans _)
  have hlen' := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.sub_le (M+1) a) :
    ((M+1-a:ℕ):ℝ) ≤ (M+1:ℕ)) hD
  linarith only [hlen']

private theorem indicator_tail_integral (F : ℝ → ℝ) {N M : ℕ} (h : N ≤ M) (l : ℝ) :
    (∫ x in (N:ℝ)..M, if l ≤ x then F x else 0) = ∫ x in realTailStart N M l..M, F x := by
  have hNM : (N:ℝ) ≤ M := Nat.cast_le.mpr h
  have hcut : Set.Ioc (N:ℝ) M ∩ Set.Ioi l = Set.Ioc (realTailStart N M l) M := by
    ext x
    simp only [realTailStart,Set.mem_inter_iff,Set.mem_Ioc,Set.mem_Ioi,min_lt_iff,max_lt_iff]
    constructor
    · rintro ⟨⟨hN,hM⟩,hl⟩
      exact ⟨Or.inr ⟨hN,hl⟩,hM⟩
    · rintro ⟨hm | ⟨hN,hl⟩,hM⟩
      · exact (hm.not_ge hM).elim
      · exact ⟨⟨hN,hM⟩,hl⟩
  calc _ = ∫ x in (N:ℝ)..M, (Set.Ioi l).indicator F x := by
            apply intervalIntegral.integral_congr_ae
            filter_upwards [volume.ae_ne l] with x hx _
            simp only [Set.indicator_apply,Set.mem_Ioi,le_iff_lt_or_eq,Ne.symm hx,or_false]
       _ = _ := by
            rw [intervalIntegral.integral_of_le hNM,setIntegral_indicator measurableSet_Ioi,hcut,
              intervalIntegral.integral_of_le (min_le_left (M:ℝ) (max N l))]

/-- Sampling on a two-ended shell of positive powers costs O(M) per product.
Rounding is uniform even when either product cut crosses the terminal conductor. -/
theorem power_shell_sampling_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {N M : ℕ}, 0 < N → N ≤ M → ∀ (b : ℕ) {q α β c : ℝ},
      0 < q → 0 < α → 0 < β → 0 < c →
      |(∑ n ∈ Ioc N M with (n:ℝ)^α < q ∧ q ≤ c*(n:ℝ)^β,
          (n:ℝ)*quotientMeshProfile b (q/(n:ℝ)^2)) -
        ∫ x in (N:ℝ)..M, if x^α < q ∧ q ≤ c*x^β then x*quotientMeshProfile b (q/x^2) else 0| ≤
          K*(M+1:ℕ) := by
  obtain ⟨K,hK,h⟩ := real_tail_sampling_error
  obtain ⟨_,_,hb⟩ := real_conductor_mesh_sampling
  refine ⟨K+K,add_nonneg hK hK,fun {N M} hN hNM b q α β c hq hα hβ hc => ?_⟩
  let l := (q/c)^β⁻¹
  let u := q^α⁻¹
  let F := fun x : ℝ => x*quotientMeshProfile b (q/x^2)
  let G := fun (r x : ℝ) => if r ≤ x then F x else 0
  have hm (x : ℝ) (hx : 0 ≤ x) : (x^α < q ∧ q ≤ c*x^β) ↔ (l ≤ x ∧ x < u) := by
    dsimp only [l,u]
    rw [Real.rpow_inv_le_iff_of_pos (div_nonneg hq.le hc.le) hx hβ,
      Real.lt_rpow_inv_iff_of_pos hx hq.le hα,div_le_iff₀ hc,mul_comm (x^β) c,and_comm]
  have hNM' : (N:ℝ) ≤ M := Nat.cast_le.mpr hNM
  have hpos : (0:ℝ) < N := Nat.cast_pos.mpr hN
  let v := max l u
  have fpoint (x : ℝ) (hx : 0 ≤ x) :
      (if x^α < q ∧ q ≤ c*x^β then F x else 0) = G l x - G v x := by
    simp only [hm x hx,G,v,max_le_iff]
    by_cases hl : l ≤ x <;> by_cases hu : u ≤ x <;> simp [hl,hu,lt_iff_not_ge]
  have hint_base : IntervalIntegrable F volume (N:ℝ) M := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hNM'] at hx
    obtain ⟨_,_,hd⟩ := (hb b hq (hpos.trans_le hx.1)).2
    exact hd.continuousAt.continuousWithinAt
  have hint (r : ℝ) : IntervalIntegrable (G r) volume (N:ℝ) M := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hNM'] at hint_base ⊢
    exact hint_base.indicator measurableSet_Ici
  have hen : (∫ x in (N:ℝ)..M, if x^α < q ∧ q ≤ c*x^β then F x else 0) =
      (∫ x in realTailStart N M l..M, F x) - ∫ x in realTailStart N M v..M, F x := by
    rw [←indicator_tail_integral F hNM l,←indicator_tail_integral F hNM v,
      ←intervalIntegral.integral_sub (hint l) (hint v)]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hNM'] at hx
    exact fpoint x (hpos.trans_le hx.1).le
  have hsum : (∑ n ∈ Ioc N M with (n:ℝ)^α < q ∧ q ≤ c*(n:ℝ)^β, F n) =
      (∑ n ∈ Ioc N M with l ≤ (n:ℝ), F n) - ∑ n ∈ Ioc N M with v ≤ (n:ℝ), F n := by
    simp only [sum_filter,←sum_sub_distrib]
    exact sum_congr rfl fun n _ => fpoint n (Nat.cast_nonneg n)
  change |(∑ n ∈ Ioc N M with (n:ℝ)^α < q ∧ q ≤ c*(n:ℝ)^β, F n) -
    ∫ x in (N:ℝ)..M, if x^α < q ∧ q ≤ c*x^β then F x else 0| ≤ _
  rw [hsum,hen,sub_sub_sub_comm]
  exact (abs_sub _ _).trans ((add_le_add (h hN hNM b hq l) (h hN hNM b hq v)).trans_eq (by ring))

private theorem integral_on_padded_interval (F : ℝ → ℝ) {a l u z : ℝ}
    (hal : a ≤ l) (hlu : l ≤ u) (huz : u ≤ z) :
    (∫ x in a..z, if l < x ∧ x ≤ u then F x else 0) = ∫ x in l..u, F x := by
  change (∫ x in a..z, (Set.Ioc l u).indicator F x) = _
  rw [intervalIntegral.integral_of_le (hal.trans (hlu.trans huz)),setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_right.mpr (Set.Ioc_subset_Ioc hal huz),←intervalIntegral.integral_of_le hlu]

private theorem centered_product_total_variation (H : ℕ) :
    (∑ q ∈ Ioc 0 H, |vonMangoldt q-1|) ≤ 8*(H:ℝ) := by
  have he : Ioc 0 H = Icc 1 H := by ext q; simp only [mem_Icc,mem_Ioc]; omega
  rw [he]
  calc _ ≤ ∑ q ∈ Icc 1 H, (vonMangoldt q+1) := sum_le_sum fun q _ => by
              simpa only [abs_of_nonneg vonMangoldt_nonneg,abs_one] using abs_sub (vonMangoldt q) 1
       _ ≤ 7*(H:ℝ)+H := by
              rw [sum_add_distrib,sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,mul_one]
              exact add_le_add (_root_.RHTower.sum_vonMangoldt_Icc_le_seven H) (le_refl (H:ℝ))
       _ = _ := by ring

/-- The discrete sum on a power shell differs from its common rescaled
integral by O((M+1)H). All product scales through H share the same endpoints
T and Z, provided those endpoints cover the conductor interval. -/
theorem power_shell_rescaled_quadrature :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N M H : ℕ}, 0 < N → N ≤ M → ∀ (b : ℕ) {α β c T Z : ℝ},
      0 < α → 0 < β → 0 < c → 0 < T → T ≤ Z → T*Real.sqrt H ≤ N → (M:ℝ) ≤ Z →
      |(∑ q ∈ Ioc 0 H, (vonMangoldt q-1) *
          ∑ n ∈ Ioc N M with (n:ℝ)^α < q ∧ (q:ℝ) ≤ c*(n:ℝ)^β,
            (n:ℝ)*quotientMeshProfile b (q/(n:ℝ)^2)) -
        ∫ t in T..Z, (t*quotientMeshProfile b (1/t^2)) *
          ∑ q ∈ rescaledShellProducts H N M t α β c with 0 < q, (vonMangoldt q-1)*q| ≤
          C*(M+1:ℕ)*H := by
  obtain ⟨K,hK,h⟩ := power_shell_sampling_error
  refine ⟨8*K,by positivity,fun {N M H} hN hNM b α β c T Z hα hβ hc hT hTZ hTN hMZ => ?_⟩
  let F (q : ℕ) (x : ℝ) := x*quotientMeshProfile b (q/x^2)
  let A (q : ℕ) (x : ℝ) := x^α < q ∧ (q:ℝ) ≤ c*x^β
  let a := fun q => vonMangoldt q-1
  let S (q : ℕ) := ∑ n ∈ Ioc N M with A q n, F q n
  let I (q : ℕ) := ∫ x in (N:ℝ)..M, if A q x then F q x else 0
  have pad (q : ℕ) (hq : q ∈ Ioc 0 H) :
      (∫ x in T*Real.sqrt q..Z*Real.sqrt q,
        if (N:ℝ)<x ∧ x ≤ M ∧ A q x then a q * F q x else 0) = a q * I q := by
    have hq1 := (mem_Ioc.mp hq).1
    have hl := (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (Nat.cast_le.mpr (mem_Ioc.mp hq).2)) hT.le).trans hTN
    have hs : 1 ≤ Real.sqrt q := by simpa only [Real.sqrt_one] using
      Real.sqrt_le_sqrt (Nat.one_le_cast.mpr hq1 : (1:ℝ) ≤ q)
    have hu := hMZ.trans (le_mul_of_one_le_right (hT.trans_le hTZ).le hs)
    rw [show (fun x : ℝ => if (N:ℝ)<x ∧ x ≤ M ∧ A q x then a q*F q x else 0) =
        fun x => if (N:ℝ)<x ∧ x ≤ M then a q*(if A q x then F q x else 0) else 0 from
      funext fun x => by by_cases hl : (N:ℝ)<x <;> by_cases hu : x≤M <;> by_cases hm : A q x <;> simp [hl,hu,hm],
      integral_on_padded_interval _ hl (Nat.cast_le.mpr hNM) hu,intervalIntegral.integral_const_mul]
  rw [←rescaled_shell_integral_exchange b 0 H (N:ℝ) M c α β hT hTZ,
    sum_congr rfl pad,←sum_sub_distrib]
  change |∑ q ∈ Ioc 0 H, (a q*S q-a q*I q)| ≤ _
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ q ∈ Ioc 0 H, |a q|*(K*(M+1:ℕ)) := by
              apply sum_le_sum
              intro q hq
              rw [←mul_sub,abs_mul]
              exact mul_le_mul_of_nonneg_left
                (h hN hNM b (Nat.cast_pos.mpr (mem_Ioc.mp hq).1) hα hβ hc) (abs_nonneg _)
       _ ≤ 8*(H:ℝ)*(K*(M+1:ℕ)) := by
              rw [←sum_mul]
              exact mul_le_mul_of_nonneg_right (centered_product_total_variation H) (by positivity)
       _ = _ := by ring

/-- Uniform bound through H on the discrete shell, including all rounding
and both partial-conductor endpoints. The upper rescaled limit incurs no loss. -/
theorem discrete_rescaled_shell_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N M H : ℕ}, 0 < N → N ≤ M → 1 ≤ H →
      ∀ (b : ℕ) {α β c T Z : ℝ}, 0 < α → α ≤ 2 → 0 < β → β ≤ 2 → 0 < c →
      0 < T → T ≤ Z → T*Real.sqrt H ≤ N → (M:ℝ) ≤ Z →
      7/T^2 < Real.exp (-8) → 4*Real.exp 8 < b/Z^2 →
      |∑ q ∈ Ioc 0 H, (vonMangoldt q-1) *
          ∑ n ∈ Ioc N M with (n:ℝ)^α < q ∧ (q:ℝ) ≤ c*(n:ℝ)^β,
            (n:ℝ)*quotientMeshProfile b (q/(n:ℝ)^2)| ≤
          C*(((M+1:ℕ):ℝ)*H+(H:ℝ)^(1+(8/9:ℝ))/T^12) := by
  obtain ⟨A,hA,ha⟩ := power_shell_rescaled_quadrature
  obtain ⟨B,hB,hb⟩ := rescaled_shell_integral_bound
  refine ⟨A+B,add_nonneg hA hB,fun {N M H} hN hNM hH b α β c T Z hα hα2 hβ hβ2 hc hT hTZ hTN hMZ hs hl => ?_⟩
  let I := ∫ t in T..Z, (t*quotientMeshProfile b (1/t^2)) *
            ∑ q ∈ rescaledShellProducts H N M t α β c with 0 < q, (vonMangoldt q-1)*q
  have h := ha hN hNM b hα hβ hc hT hTZ hTN hMZ
  have j := hb H b hH 0 (Nat.zero_le H) N M c hα2 hβ2 hT hTZ hs hl
  let S := ∑ q ∈ Ioc 0 H, (vonMangoldt q-1) *
          ∑ n ∈ Ioc N M with (n:ℝ)^α < q ∧ (q:ℝ) ≤ c*(n:ℝ)^β,
            (n:ℝ)*quotientMeshProfile b (q/(n:ℝ)^2)
  change |S-I| ≤ _ at h
  change |I| ≤ _ at j
  change |S| ≤ _
  have hs' : |S| ≤ |S-I| + |I| := by simpa only [sub_add_cancel] using abs_add_le (S-I) I
  apply hs'.trans ((add_le_add h j).trans _)
  have hr : 0 ≤ (H:ℝ)^(1+(8/9:ℝ))/T^12 := by positivity
  have hQ : 0 ≤ ((M+1:ℕ):ℝ)*H := by positivity
  push_cast
  push_cast at hQ
  linarith only [mul_nonneg hA hr,mul_nonneg hB hQ]

#print axioms discrete_rescaled_shell_bound
#print axioms power_shell_rescaled_quadrature
#print axioms power_shell_sampling_error
#print axioms real_tail_sampling_error
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
