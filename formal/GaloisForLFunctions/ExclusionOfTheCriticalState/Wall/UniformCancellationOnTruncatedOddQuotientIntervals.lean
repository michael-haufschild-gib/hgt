import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.OddQuotientsInTheFractionalPrimeTest
import GaloisForLFunctions.HTGeometry.DiscreteEnergyBootstrap
import GaloisForLFunctions.RHTower.PrimeWindowSupply

/-!
# Uniform cancellation over denominator intervals at one numerator

The variation of the odd-quotient digit beyond m costs at most H/m.
Discrete partial summation therefore pays for the tail with the largest
Chebyshev error up to H. Removing the first m denominators costs O(m).
The prime number theorem yields o(H), uniformly in both interval ends.
-/

open Finset Filter
noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

private def bit (H n : ℕ) : ℝ := if H/n%2=1 then 1 else 0
private def err (n : ℕ) : ℝ := Chebyshev.theta n-n

private theorem bit_abs (H n : ℕ) : |bit H n| ≤ 1 := by unfold bit; split <;> norm_num

private theorem bit_change (H k : ℕ) (hk : 0<k) :
    |bit H (k+1)-bit H k| ≤ (H/k:ℕ)-(↑(H/(k+1)):ℝ) := by
  have hm : H/(k+1) ≤ H/k := Nat.div_le_div_left (Nat.le_succ k) hk
  by_cases he : H/(k+1)=H/k
  · simp [bit,he]
  · have hlt := lt_of_le_of_ne hm he
    have step : (↑(H/(k+1)):ℝ)+1 ≤ (H/k:ℕ) := by exact_mod_cast Nat.succ_le_of_lt hlt
    simp only [bit]
    split_ifs <;> norm_num <;> first | linarith only [step] | exact hm

private theorem coeff_eq_step (n : ℕ) : ordinaryPrimeExcessCoeff (n+1)=err (n+1)-err n := by
  have hs : Ioc n (n+1) = {n+1} := by ext i; simp only [mem_Ioc,mem_singleton]; omega
  have h := _root_.RHTower.theta_window_eq (Nat.le_succ n)
  rw [hs,sum_filter,sum_singleton] at h
  unfold ordinaryPrimeExcessCoeff err
  rw [←h,Nat.cast_succ]
  ring

private theorem interval_abel {u v : ℕ} (huv : u≤v) (H : ℕ) :
    oddQuotientPrimeExcess (Ioc u v) H =
      bit H v*err v-bit H u*err u-∑ k ∈ Ico u v, (bit H (k+1)-bit H k)*err k := by
  rw [←HTGeometry.abel_sum_Ico (bit H) err huv]
  induction v,huv using Nat.le_induction with
  | base => simp [oddQuotientPrimeExcess]
  | succ v hv ih =>
    have row := sum_Ioc_consecutive (fun n => if H/n%2=1 then ordinaryPrimeExcessCoeff n else 0) hv (Nat.le_succ v)
    have hs : Ioc v (v+1)={v+1} := by ext i; simp only [mem_Ioc,mem_singleton]; omega
    rw [hs,sum_singleton] at row
    change oddQuotientPrimeExcess (Ioc u v) H+_=oddQuotientPrimeExcess (Ioc u (v+1)) H at row
    rw [←row,ih,sum_Ico_succ_top hv,coeff_eq_step]
    split_ifs with he <;> simp [bit,he]

/-- Uniform deterministic denominator-tail bound. Endpoints contribute
at most twice the maximum Chebyshev error. Interior changes cost at most
the drop of the integer quotient. -/
theorem odd_quotient_tail_variation_bound (H u v : ℕ) (hu : 0<u) (huv : u≤v)
    (E : ℝ) (hE : ∀ k ∈ Icc u v, |Chebyshev.theta k-(k:ℝ)| ≤ E) :
    |oddQuotientPrimeExcess (Ioc u v) H| ≤
      E*(2+(↑(H/u):ℝ)-(↑(H/v):ℝ)) := by
  let q (n : ℕ) : ℝ := (↑(H/n):ℝ)
  have qdiff k (hk : k ∈ Ico u v) : |bit H (k+1)-bit H k| ≤ q k-q (k+1) :=
    bit_change H k (hu.trans_le (mem_Ico.mp hk).1)
  have qt : (∑ k ∈ Ico u v, (q k-q (k+1))) = q u-q v := by
    have h := HTGeometry.telescope_Ico (fun n => -q n) huv
    simpa only [neg_sub_neg] using h
  have sumBound : |∑ k ∈ Ico u v, (bit H (k+1)-bit H k)*err k| ≤ (q u-q v)*E := by
    apply (abs_sum_le_sum_abs _ _).trans
    rw [←qt,sum_mul]
    apply sum_le_sum
    intro k hk
    rw [abs_mul]
    exact mul_le_mul (qdiff k hk) (hE k (mem_Icc.mpr ⟨(mem_Ico.mp hk).1,(mem_Ico.mp hk).2.le⟩))
      (abs_nonneg _) ((abs_nonneg _).trans (qdiff k hk))
  have e k (hk : k ∈ Icc u v) : |bit H k*err k| ≤ E := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (bit_abs H k) (abs_nonneg _)).trans
      ((one_mul _).le.trans (hE k hk))
  have ends := abs_sub (bit H v*err v) (bit H u*err u)
  rw [interval_abel huv]
  apply (abs_sub _ _).trans
  change _ ≤ E*(2+q u-q v)
  linarith only [ends,e u (mem_Icc.mpr ⟨le_rfl,huv⟩),e v (mem_Icc.mpr ⟨huv,le_rfl⟩),sumBound]

private theorem max_prefix_error_eventually {δ : ℝ} (hd : 0<δ) :
    ∀ᶠ H : ℕ in atTop, ∀ n ≤ H, |err n| ≤ δ*H := by
  obtain ⟨N,hN⟩ := _root_.RHTower.chebyshevTheta_remainder_eventually_le hd
  let D := ∑ n ∈ range N, |err n|
  filter_upwards [eventually_ge_atTop ⌈D/δ⌉₊] with H hH
  intro n hn
  by_cases hi : N ≤ n
  · exact (hN n hi).trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hn) hd.le)
  · have he : D/δ ≤ (H:ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hH)
    have small : |err n| ≤ D := single_le_sum (fun j _ => abs_nonneg (err j)) (mem_range.mpr (lt_of_not_ge hi))
    exact small.trans (by simpa only [mul_comm (H:ℝ)] using (div_le_iff₀ hd).mp he)

/-- Chebyshev cancellation for every denominator interval simultaneously.
The digit and the interval may both change with the numerator. -/
private theorem capped_intervals {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ H : ℕ in atTop, ∀ x y : ℕ, y ≤ H →
      |oddQuotientPrimeExcess (Ioc x y) H| ≤ ε*H := by
  obtain ⟨Q,hQ⟩ := exists_nat_gt (16/ε)
  have hQ' : 0 < (Q:ℝ) := (div_pos (by norm_num) hε).trans hQ
  have hQn : 0<Q := Nat.cast_pos.mp hQ'
  let δ := ε/(2*(2+(Q:ℝ)))
  have hd : 0<δ := by dsimp only [δ]; positivity
  have dcost : δ*(2+(Q:ℝ))=ε/2 := by dsimp only [δ]; field_simp [show (2+(Q:ℝ))≠0 by positivity] <;> ring
  filter_upwards [max_prefix_error_eventually hd,eventually_ge_atTop Q] with H hp hH
  intro x y hy
  let M := H/Q+1
  have hM : 0<M := Nat.zero_lt_succ _
  have hden : H/M ≤ Q := by
    have h := Nat.lt_mul_div_succ H hQn
    exact (Nat.div_lt_iff_lt_mul hM).mpr (by simpa only [M,mul_comm] using h) |>.le
  have pay : 4*(M:ℝ) ≤ ε*H/2 := by
    have quot : (↑(H/Q):ℝ)*(Q:ℝ) ≤ H := by exact_mod_cast Nat.div_mul_le_self H Q
    have eq := (div_lt_iff₀ hε).mp hQ
    have qle : (Q:ℝ) ≤ H := Nat.cast_le.mpr hH
    have hm : (M:ℝ)*(Q:ℝ) ≤ 2*H := by dsimp only [M]; push_cast; linarith only [quot,qle]
    have grow := mul_le_mul_of_nonneg_left (le_of_lt eq) (Nat.cast_nonneg (α:=ℝ) H)
    have bound : (4*(M:ℝ))*Q ≤ (ε*H/2)*Q := by linarith only [grow,hm]
    exact le_of_mul_le_mul_right bound hQ'
  have cheap {v : ℕ} (hv : v ≤ M) :
      |oddQuotientPrimeExcess (Ioc x v) H| ≤ 4*(M:ℝ) := by
    refine (oddQuotientPrimeExcess_le _ M H (fun n hn => mem_Ioc.mpr
      ⟨(Nat.zero_le _).trans_lt (mem_Ioc.mp hn).1,(mem_Ioc.mp hn).2.trans hv⟩)).trans ?_
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  by_cases hem : y ≤ x
  · simp only [Ioc_eq_empty_of_le hem,oddQuotientPrimeExcess,sum_empty,abs_zero]
    positivity
  by_cases hym : y ≤ M
  · exact ((cheap hym).trans pay).trans (by have := mul_nonneg hε.le (Nat.cast_nonneg (α:=ℝ) H); linarith)
  let u := max M x
  have huy : u ≤ y := max_le (le_of_not_ge hym) (le_of_not_ge hem)
  have tail := odd_quotient_tail_variation_bound H u y (hM.trans_le (le_max_left _ _)) huy (δ*H)
    (fun n hn => hp n ((mem_Icc.mp hn).2.trans hy))
  have smallq : H/u ≤ Q := (Nat.div_le_div_left (le_max_left _ _) hM).trans hden
  have paid : |oddQuotientPrimeExcess (Ioc u y) H| ≤ ε*H/2 := by
    have upper : 2+(↑(H/u):ℝ)-(↑(H/y):ℝ) ≤ 2+(Q:ℝ) := by
      linarith only [show (↑(H/u):ℝ) ≤ Q from Nat.cast_le.mpr smallq,Nat.cast_nonneg (α:=ℝ) (H/y)]
    have h := tail.trans (mul_le_mul_of_nonneg_left upper (mul_nonneg hd.le (Nat.cast_nonneg _)))
    calc _ ≤ _ := h
         _ = (δ*(2+(Q:ℝ)))*H := by ring
         _ = _ := by rw [dcost]; ring
  have head : |oddQuotientPrimeExcess (Ioc x u) H| ≤ ε*H/2 := by
    rcases le_total M x with hx|hx
    · simp only [u,max_eq_right hx,Ioc_self,oddQuotientPrimeExcess,sum_empty,abs_zero]
      positivity
    · rw [show u=M from max_eq_left hx]
      exact (cheap le_rfl).trans pay
  have cut : oddQuotientPrimeExcess (Ioc x u) H+oddQuotientPrimeExcess (Ioc u y) H =
      oddQuotientPrimeExcess (Ioc x y) H := sum_Ioc_consecutive _ (le_max_right _ _) huy
  rw [←cut]
  exact (abs_add_le ..).trans (by linarith only [head,paid])

/-- No denominator above the numerator contributes an odd quotient. -/
theorem odd_quotient_interval_clip (H x y : ℕ) :
    oddQuotientPrimeExcess (Ioc x (min y H)) H = oddQuotientPrimeExcess (Ioc x y) H := by
  apply sum_subset (fun n hn => mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1,(mem_Ioc.mp hn).2.trans (min_le_left ..)⟩)
  intro n hn miss
  have large : H<n := lt_of_not_ge (fun hs => miss (mem_Ioc.mpr
    ⟨(mem_Ioc.mp hn).1,le_min (mem_Ioc.mp hn).2 hs⟩))
  simp [Nat.div_eq_of_lt large]

/-- The largest absolute discrepancy of an odd-quotient denominator
interval is o(H). Endpoints beyond H are allowed. -/
theorem eventually_all_odd_quotient_intervals {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ H : ℕ in atTop, ∀ x y : ℕ, |oddQuotientPrimeExcess (Ioc x y) H| ≤ ε*H := by
  filter_upwards [capped_intervals hε] with H h
  intro x y
  rw [←odd_quotient_interval_clip H x y]
  exact h _ _ (min_le_right ..)

end GaloisForLFunctions.ExclusionOfTheCriticalState
