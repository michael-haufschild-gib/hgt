import GaloisForLFunctions.RHTower.HarmonicHalfErrorBounds
import GaloisForLFunctions.RHTower.EulerDeletionQuotientHarmonicBound
import GaloisForLFunctions.RHTower.Sieve.DivisorSumMeanSquareSmooth

/-!
# The endpoint term of a truncated divisor floor

Reversing a divisor floor gives one interval for each quotient. Harmonic
summation contributes half the lower endpoint, uniformly in its fractional
position. An interval-count discrepancy costs only the number of quotients.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Euler's half-endpoint term survives moving the cutoff anywhere between
two consecutive integers. The residual decays as the reciprocal cutoff. -/
theorem harmonic_endpoint {t : ℝ} {n : ℕ} (ht : 0 < t)
    (hn : (n : ℝ) ≤ t) (hn' : t ≤ (n : ℝ)+1) :
    |t*(harmonic n : ℝ)-n - (t*(Real.log t+Real.eulerMascheroniConstant-1)+1/2)| ≤ 4/t := by
  have hg₀ : 0 ≤ Real.eulerMascheroniConstant := by linarith only [Real.one_half_lt_eulerMascheroniConstant]
  have hg₁ : Real.eulerMascheroniConstant ≤ 1 := by linarith only [Real.eulerMascheroniConstant_lt_two_thirds]
  rcases Nat.eq_zero_or_pos n with h | hn₀
  · subst n
    simp only [Nat.cast_zero,zero_add] at hn'
    simp only [harmonic_zero,Rat.cast_zero,mul_zero,Nat.cast_zero,sub_zero,zero_sub,abs_neg]
    have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
    rw [Real.log_inv] at hl
    have h₁ := mul_le_mul_of_nonneg_left hl ht.le
    rw [mul_sub,mul_inv_cancel₀ ht.ne',mul_one] at h₁
    have h₂ := mul_nonpos_of_nonneg_of_nonpos ht.le (Real.log_nonpos ht.le hn')
    have hγ := mul_le_of_le_one_right ht.le hg₁
    have hc : (4:ℝ) ≤ 4/t := (le_div_iff₀ ht).mpr (by linarith only [hn'])
    apply le_trans _ hc
    rw [abs_le]
    constructor <;> linarith only [h₁,h₂,hγ,mul_nonneg ht.le hg₀,ht,hn']
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn₀
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn₀
    let r := t-(n : ℝ)
    have hr : 0 ≤ r := sub_nonneg.mpr hn
    have hr1 : r ≤ 1 := by dsimp [r]; linarith only [hn']
    have ht' : t = n+r := by dsimp [r]; ring
    have hab := RHTower.harmonic_mascheroni_half_bounds hn₀
    let e := (harmonic n : ℝ)-Real.log n-Real.eulerMascheroniConstant
    have herr : |t*e-1/2| ≤ 1/(2*(n : ℝ)) := by
      have he₀ : 0 ≤ e := (by positivity : (0 : ℝ) ≤ 1/(2*((n : ℝ)+1))).trans hab.1
      have hlo := mul_le_mul hn hab.1 (by positivity) ht.le
      have hhi := mul_le_mul hn' hab.2 he₀ (by positivity)
      change (n : ℝ)*(1/(2*((n : ℝ)+1))) ≤ t*e at hlo
      change t*e ≤ ((n : ℝ)+1)*(1/(2*(n : ℝ))) at hhi
      have hd : 1/(2*((n : ℝ)+1)) ≤ 1/(2*(n : ℝ)) := by gcongr; linarith only [hn0]
      have hl : (n : ℝ)*(1/(2*((n : ℝ)+1))) = 1/2-1/(2*((n : ℝ)+1)) := by field_simp; ring
      have hu : ((n : ℝ)+1)*(1/(2*(n : ℝ))) = 1/2+1/(2*(n : ℝ)) := by field_simp
      rw [hl] at hlo
      rw [hu] at hhi
      exact abs_le.mpr ⟨by linarith only [hlo,hd],by linarith only [hhi]⟩
    have hlog₁ := Real.log_le_sub_one_of_pos (div_pos ht hn0)
    have hlog₂ := Real.log_le_sub_one_of_pos (div_pos hn0 ht)
    rw [Real.log_div ht.ne' hn0.ne'] at hlog₁
    rw [Real.log_div hn0.ne' ht.ne'] at hlog₂
    have hlow := mul_le_mul_of_nonneg_left hlog₂ ht.le
    have hlow' : t*(n/t-1) = -r := by dsimp [r]; field_simp; ring
    rw [hlow'] at hlow
    have hu := mul_le_mul_of_nonneg_left hlog₁ ht.le
    have heq : t*(t/n-1) = r+r^2/n := by rw [ht']; field_simp; ring
    rw [heq] at hu
    have hr₂ : r^2/(n : ℝ) ≤ 1/n := div_le_div_of_nonneg_right
      (by nlinarith only [mul_nonneg hr (sub_nonneg.mpr hr1),hr1]) hn0.le
    have he' : |t*(Real.log t-Real.log n)-r| ≤ 1/n := by
      rw [abs_le]
      constructor <;> linarith only [hlow,hu,hr₂,show (0 : ℝ) ≤ 1/n by positivity]
    have hid : t*(harmonic n : ℝ)-n-(t*(Real.log t+Real.eulerMascheroniConstant-1)+1/2) =
        (t*e-1/2)-(t*(Real.log t-Real.log n)-r) := by dsimp [r,e]; ring
    rw [hid]
    apply (abs_sub _ _).trans ((add_le_add herr he').trans ?_)
    apply (le_div_iff₀ ht).mpr
    have hs : 1/(2*(n : ℝ))+1/n = 3/(2*n) := by ring
    rw [hs,div_mul_eq_mul_div,div_le_iff₀ (by positivity : (0 : ℝ) < 2*n)]
    linarith only [hn',hn1]

/-- Main term of one floor on the interval of long factors starting at Z. -/
def floorDensity (X Z k : ℕ) : ℝ :=
  ((X : ℝ)/k)*(Real.log ((X : ℝ)/(k*Z))+Real.eulerMascheroniConstant-1)+(Z : ℝ)/2

/-- Counting floors against a density-one sequence with bounded interval discrepancy.
The endpoint error has size kZ²/X and the counting error has size X/(kZ). -/
theorem truncated_floor_density {X Y k : ℕ} (hX : 1 ≤ X) (hk : 1 ≤ k)
    (a : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (ha : ∀ L U : ℕ, L ≤ U → |(∑ m ∈ Ioc L U, a m)-((U : ℝ)-L)| ≤ B) :
    let Z := Y+1
    |(∑ m ∈ Ioc Y X, a m*((X/m/k : ℕ) : ℝ))-floorDensity X Z k| ≤
      (B+2)*((X : ℝ)/(k*Z))+4*k*(Z : ℝ)^2/X := by
  intro Z
  let n := X/k/Z
  let t := (X : ℝ)/(k*Z)
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hZ : 0 < Z := Nat.succ_pos _
  have hz : (0 : ℝ) < Z := by exact_mod_cast hZ
  have ht : 0 < t := div_pos hx (mul_pos hk0 hz)
  have hn : n = X/(k*Z) := Nat.div_div_eq_div_mul ..
  have hn₁ : (n : ℝ) ≤ t := by
    rw [hn]; simpa only [Nat.cast_mul] using (Nat.cast_div_le (α := ℝ) (m := X) (n := k*Z))
  have hn₂ : t ≤ (n : ℝ)+1 := by
    apply (div_le_iff₀ (mul_pos hk0 hz)).mpr
    have hh := Nat.lt_mul_div_succ X (show 0 < k*Z by positivity)
    rw [← hn,mul_comm (k*Z)] at hh
    exact_mod_cast hh.le
  have hid : (∑ m ∈ Ioc Y X, a m*((X/m/k : ℕ) : ℝ)) =
      ∑ j ∈ Icc 1 n, ∑ m ∈ Ioc Y (X/k/j), a m := by
    have hswap (m : ℕ) : X/m/k=X/k/m := by simp only [Nat.div_div_eq_div_mul,mul_comm m k]
    simp_rw [hswap]
    rw [← RHTower.DeletionQuotientTail.truncated_floor_hyperbola a Y (X/k)]
    apply (sum_subset (f := fun m => a m*((X/k/m : ℕ) : ℝ)) ?_ ?_).symm
    · intro m hm; exact mem_Ioc.mpr ⟨(mem_Ioc.mp hm).1,(mem_Ioc.mp hm).2.trans (Nat.div_le_self ..)⟩
    · intro m hm hnot
      have hlt : X/k < m := by
        by_contra! hh
        exact hnot (mem_Ioc.mpr ⟨(mem_Ioc.mp hm).1,hh⟩)
      rw [Nat.div_eq_of_lt hlt,Nat.cast_zero,mul_zero]
  have each (j : ℕ) (hj : j ∈ Icc 1 n) :
      |(∑ m ∈ Ioc Y (X/k/j), a m)-((X : ℝ)/(k*j)-Z)| ≤ B+2 := by
    obtain ⟨hj1,hjn⟩ := mem_Icc.mp hj
    have hle : Z ≤ X/k/j := (Nat.le_div_iff_mul_le hj1).mpr (by
      simpa only [mul_comm Z j] using (Nat.le_div_iff_mul_le hZ).mp hjn)
    have hA := abs_le.mp (ha Y (X/k/j) (by dsimp [Z] at hle; omega))
    have hf := RHTower.Sieve.abs_natDiv_sub_div_le (N := X) (show 0 < k*j from Nat.mul_pos hk hj1)
    rw [Nat.div_div_eq_div_mul] at hA ⊢
    push_cast at hf
    have hh := abs_le.mp hf
    dsimp [Z]
    push_cast
    rw [abs_le]
    constructor <;> linarith only [hA.1,hA.2,hh.1,hh.2]
  have hsum : ∑ j ∈ Icc 1 n, ((X : ℝ)/(k*j)-Z) = (Z : ℝ)*(t*(harmonic n : ℝ)-n) := by
    have hh : (harmonic n : ℝ) = ∑ j ∈ Icc 1 n, 1/(j : ℝ) := by
      rw [harmonic_eq_sum_Icc]; push_cast; simp only [one_div]
    rw [hh,sum_sub_distrib,mul_sub,← mul_assoc,mul_sum]
    simp only [sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,mul_comm (n : ℝ) (Z : ℝ)]
    congr 1
    apply sum_congr rfl
    intro j _
    dsimp [t]; field_simp
  have herr : |(∑ m ∈ Ioc Y X, a m*((X/m/k : ℕ) : ℝ)) -
      (Z : ℝ)*(t*(harmonic n : ℝ)-n)| ≤ (B+2)*t := by
    rw [hid,←hsum,←sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans ((sum_le_sum each).trans ?_)
    simp only [sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
    exact (mul_le_mul_of_nonneg_right hn₁ (by positivity : 0 ≤ B+2)).trans_eq (mul_comm ..)
  have hend := mul_le_mul_of_nonneg_left (harmonic_endpoint ht hn₁ hn₂) hz.le
  have hmain : (Z : ℝ)*(t*(Real.log t+Real.eulerMascheroniConstant-1)+1/2) = floorDensity X Z k := by
    unfold floorDensity; change _ = (X/k : ℝ)*(Real.log t+Real.eulerMascheroniConstant-1)+Z/2
    have htz : (Z : ℝ)*t = (X : ℝ)/k := by dsimp [t]; field_simp
    rw [mul_add,←mul_assoc,htz]; ring
  have htail : (Z : ℝ)*(4/t) = 4*k*(Z : ℝ)^2/X := by dsimp [t]; field_simp
  have hend' : |(Z : ℝ)*(t*(harmonic n : ℝ)-n)-floorDensity X Z k| ≤ 4*k*(Z : ℝ)^2/X := by
    rw [← hmain,← mul_sub,abs_mul,abs_of_nonneg hz.le,← htail]
    exact hend
  exact (abs_sub_le _ _ _).trans (add_le_add herr hend')

#print axioms truncated_floor_density

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
