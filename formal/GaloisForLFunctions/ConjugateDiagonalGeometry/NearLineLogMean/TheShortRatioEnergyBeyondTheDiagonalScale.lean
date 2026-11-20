import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PrimitiveSpectrumOfTheMoebiusGram
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PhaseRetrievalFromSuccessiveLogWindows

/-!
# Diagonal approximation beyond the resolution scale

In the p = 2 log-window energy a new endpoint n interacts with at most
nδ earlier coefficients. When δ ≤ 1/2 these lie above n/2. For coefficients
bounded by the inverse square root this costs at most 4δ² per endpoint.
Thus the normalized energy differs from the full diagonal by O(N/T),
uniformly through and beyond the scale where neighboring windows overlap.
-/

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
open Finset Complex Filter MeasureTheory
open scoped ComplexConjugate
open _root_.RHTower
open GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
noncomputable section

private def neighbors (N : ℕ) (δ : ℝ) :=
  (Icc 1 N).filter (fun m => gap N m < δ)

private theorem neighbor_gap {m N : ℕ} {δ : ℝ} (hm : m ∈ neighbors N δ) :
    ((N+1 : ℕ) : ℝ)-(m : ℝ) < ((N+1 : ℕ) : ℝ)*δ := by
  obtain ⟨h,hs⟩ := mem_filter.mp hm
  have hn : (0 : ℝ) < (N+1 : ℕ) := Nat.cast_pos.mpr (Nat.succ_pos N)
  have hp : (0 : ℝ) < m := Nat.cast_pos.mpr (mem_Icc.mp h).1
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hn hp)
  rw [inv_div,Real.log_div hn.ne' hp.ne'] at hlog
  have hlow : (((N+1 : ℕ) : ℝ)-m)/((N+1 : ℕ) : ℝ) ≤ gap N m := by
    simpa only [gap,sub_div,div_self hn.ne'] using hlog
  exact ((div_lt_iff₀ hn).mp (hlow.trans_lt hs)).trans_eq (mul_comm _ _)

private theorem neighbor_count {N : ℕ} {δ : ℝ} (hd : 0 ≤ δ) :
    ((neighbors N δ).card : ℝ) ≤ ((N+1 : ℕ) : ℝ)*δ := by
  let n := N+1
  let q := ⌊((n : ℝ)*δ)⌋₊
  have hinj : Set.InjOn (fun m : ℕ => n-m) (neighbors N δ : Set ℕ) := by
    intro a ha b hb h
    have ha' := (mem_Icc.mp (mem_filter.mp ha).1).2
    have hb' := (mem_Icc.mp (mem_filter.mp hb).1).2
    dsimp only [n] at h
    omega
  have hs : (neighbors N δ).image (fun m => n-m) ⊆ Icc 1 q := by
    intro j hj
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hj
    have hmN := (mem_Icc.mp (mem_filter.mp hm).1).2
    have hmn : m ≤ n := hmN.trans (Nat.le_succ N)
    refine mem_Icc.mpr ⟨by dsimp only [n]; omega,?_⟩
    apply (Nat.le_floor_iff (mul_nonneg (Nat.cast_nonneg _) hd)).mpr
    rw [Nat.cast_sub hmn]
    exact (neighbor_gap hm).le
  have hcard := card_le_card hs
  rw [card_image_of_injOn hinj] at hcard
  have hq : (neighbors N δ).card ≤ q := by simpa [Nat.card_Icc] using hcard
  exact (Nat.cast_le.mpr hq).trans (Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) hd))

private theorem gram_neighbor_bound (a : ℕ → ℂ) (h : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ 1/Real.sqrt n)
    {N m : ℕ} {δ : ℝ} (hδ : δ ≤ 1/2) (hm : m ∈ neighbors N δ) :
    |gram (a (N+1)) (a m)| ≤ 2/((N+1 : ℕ) : ℝ) := by
  let n := N+1
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.succ_pos N)
  have hp := (mem_Icc.mp (mem_filter.mp hm).1).1
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hp
  have hlog : (n : ℝ)-m < (n : ℝ)*δ := neighbor_gap hm
  have hthin := mul_le_mul_of_nonneg_left hδ hn.le
  have hcomp : Real.sqrt n ≤ 2*Real.sqrt m := by
    calc
      _ ≤ Real.sqrt (4*(m : ℝ)) := Real.sqrt_le_sqrt (by linarith only [hlog,hthin,hm'])
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num
  calc
    _ ≤ ‖a n*conj (a m)‖ := Complex.abs_re_le_norm _
    _ = ‖a n‖*‖a m‖ := by rw [norm_mul,Complex.norm_conj]
    _ ≤ (1/Real.sqrt n)*(1/Real.sqrt m) :=
      mul_le_mul (h n (Nat.succ_pos _)) (h m hp) (norm_nonneg _) (by positivity)
    _ ≤ 2 / (n : ℝ) := by
      rw [div_mul_div_comm,one_mul,div_le_div_iff₀ (mul_pos (Real.sqrt_pos.mpr hn)
        (Real.sqrt_pos.mpr hm')) hn,one_mul]
      calc (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hn.le).symm
           _ ≤ Real.sqrt n * (2 * Real.sqrt m) :=
             mul_le_mul_of_nonneg_left hcomp (Real.sqrt_nonneg n)
           _ = 2 * (Real.sqrt n * Real.sqrt m) := by ring

/-- The off-diagonal error of a single added coefficient is quadratic in
bandwidth, regardless of how long the section already is. -/
theorem row_diagonal_error (a : ℕ → ℂ) (h : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ 1/Real.sqrt n)
    (N : ℕ) {δ : ℝ} (hd : 0 ≤ δ) (ht : δ ≤ 1/2) :
    |row a N δ - ‖a (N+1)‖^2*δ| ≤ 4*δ^2 := by
  let n := N+1
  let f (m : ℕ) := gram (a n) (a m)*max (δ-gap N m) 0
  have hn : (0 : ℝ)<n := Nat.cast_pos.mpr (Nat.succ_pos N)
  have he : ∑ m ∈ neighbors N δ, f m = ∑ m ∈ Icc 1 N, f m := by
    apply sum_subset (filter_subset _ _)
    intro m hm hnot
    have hg : δ ≤ gap N m := le_of_not_gt (fun hg => hnot (mem_filter.mpr ⟨hm,hg⟩))
    simp only [f,max_eq_right (sub_nonpos.mpr hg),mul_zero]
  have hf {m : ℕ} (hm : m ∈ neighbors N δ) : |f m| ≤ (2/(n : ℝ))*δ := by
    obtain ⟨hM,hcut⟩ := mem_filter.mp hm
    have hleft := (mem_Icc.mp hM).1
    have hright := (mem_Icc.mp hM).2.trans (Nat.le_succ N)
    have hg : 0 ≤ gap N m := sub_nonneg.mpr
      (Real.log_le_log (Nat.cast_pos.mpr hleft) (Nat.cast_le.mpr hright))
    dsimp only [f]
    rw [abs_mul,max_eq_left (sub_nonneg.mpr hcut.le),abs_of_nonneg (sub_nonneg.mpr hcut.le)]
    exact mul_le_mul (gram_neighbor_bound a h ht hm) (sub_le_self _ hg) (sub_nonneg.mpr hcut.le) (by positivity)
  have hh : |∑ m ∈ neighbors N δ, f m| ≤ 2*δ^2 := by
    calc
      _ ≤ ∑ m ∈ neighbors N δ, |f m| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _m ∈ neighbors N δ, (2/(n : ℝ))*δ := sum_le_sum fun _ hm => hf hm
      _ = ((neighbors N δ).card : ℝ)*((2/(n : ℝ))*δ) := by simp
      _ ≤ ((n : ℝ)*δ)*((2/(n : ℝ))*δ) := mul_le_mul_of_nonneg_right (neighbor_count hd) (by positivity)
      _ = _ := by field_simp [hn.ne']
  rw [row_spectrum,max_eq_left hd,add_sub_cancel_left]
  change |2*(∑ m ∈ Icc 1 N, f m)| ≤ _
  rw [←he,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ)≤2)]
  linarith only [hh]

/-- Global error against the squarefree harmonic diagonal, uniform in
length and valid even when the logarithmic windows overlap. -/
theorem normalized_energy_diagonal_error (N : ℕ) {T : ℝ} (hT : 2 ≤ T) :
    |T*bandEnergy N T⁻¹ - ∑ n ∈ Icc 1 N, mobiusRealCoefficient n^2/n| ≤ 4*(N : ℝ)/T := by
  let a (n : ℕ) : ℂ := coeff n
  have ha (n : ℕ) (hn : 1 ≤ n) : ‖a n‖ ≤ 1/Real.sqrt n := by
    have hμ : |mobiusRealCoefficient n| ≤ 1 := by
      unfold mobiusRealCoefficient
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    simpa only [a,Complex.norm_real,Real.norm_eq_abs,coeff,abs_div,abs_of_nonneg (Real.sqrt_nonneg n)] using
      (div_le_div_of_nonneg_right hμ (Real.sqrt_nonneg n))
  have ht : 0 < T := by linarith
  have hd : T⁻¹ ≤ 1/2 := by simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ)<2) hT
  have hs (L : ℕ) : |bandEnergy L T⁻¹-T⁻¹*(∑ n ∈ Icc 1 L, mobiusRealCoefficient n^2/n)| ≤
      4*(L : ℝ)*(T⁻¹)^2 := by
    induction L with
    | zero => simp [bandEnergy,_root_.RHTower.Sieve.logWindowSum]
    | succ L ih =>
      have hb := row_diagonal_error a ha L (inv_nonneg.mpr ht.le) hd
      have he : ‖a (L+1)‖^2 = mobiusRealCoefficient (L+1)^2/((L+1 : ℕ) : ℝ) := by
        simp only [a,Complex.norm_real,Real.norm_eq_abs, sq_abs,coeff,div_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
      change |(bandEnergy (L+1) T⁻¹-bandEnergy L T⁻¹)-‖a (L+1)‖^2*T⁻¹| ≤ _ at hb
      rw [sum_Icc_succ_top (by omega : 1 ≤ L+1)]
      rw [he] at hb
      calc
        _ = |(bandEnergy L T⁻¹-T⁻¹*∑ n ∈ Icc 1 L, mobiusRealCoefficient n^2/n) +
            ((bandEnergy (L+1) T⁻¹-bandEnergy L T⁻¹)-mobiusRealCoefficient (L+1)^2/((L+1 : ℕ) : ℝ)*T⁻¹)| :=
          congrArg abs (by ring)
        _ ≤ _ := (abs_add_le _ _).trans ((add_le_add ih hb).trans_eq (by push_cast; ring))
  have he : T*bandEnergy N T⁻¹-(∑ n ∈ Icc 1 N, mobiusRealCoefficient n^2/n) =
      T*(bandEnergy N T⁻¹-T⁻¹*∑ n ∈ Icc 1 N, mobiusRealCoefficient n^2/n) := by
    rw [mul_sub,←mul_assoc,mul_inv_cancel₀ ht.ne',one_mul]
  rw [he,abs_mul,abs_of_pos ht]
  exact (mul_le_mul_of_nonneg_left (hs N) ht.le).trans_eq (by field_simp [ht.ne'])

end
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
