import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.SmallDiskZeros
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.WeightedDetector

/-! A nearby zero forces a large normalized derivative of the logarithmic derivative. -/

open Complex Finset WindowedLandauTheory.ZeroFreeDirichlet

noncomputable section

namespace QH.PrimeProgressions

private theorem detector_absorb (K j : ℕ) (hj : K + 1 ≤ j) (hj₂ : 2 ≤ j)
    {b : ℝ} (hb : 0 < b) (X P Y : ℂ)
    (hY : (8 * b) ^ j ≤ ‖Y‖ + (K : ℝ) * b ^ j)
    (hP : ‖P‖ ≤ b ^ j) (hE : ‖X - P + Y‖ ≤ (K : ℝ) * b ^ j) :
    (4 * b) ^ j ≤ ‖X‖ := by
  have hK : (K : ℝ) ≤ (2 : ℝ) ^ j := by
    exact_mod_cast (show K ≤ 2 ^ j from (show K ≤ j by omega).trans j.lt_two_pow_self.le)
  have ht : (K : ℝ) * b ^ j ≤ (2 * b) ^ j := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hK (by positivity)
  have hp : b ^ j ≤ (2 * b) ^ j :=
    pow_le_pow_left₀ hb.le (by linarith only [hb]) j
  have hY' : ‖Y‖ ≤ ‖X - P + Y‖ + ‖P‖ + ‖X‖ := by
    calc
      ‖Y‖ = ‖(X - P + Y) + P - X‖ := by congr 1; abel
      _ ≤ ‖(X - P + Y) + P‖ + ‖X‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add (norm_add_le _ _) le_rfl
  have hpow : (4 : ℝ) ≤ (2 : ℝ) ^ j := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hj₂
  have hsum : 3 * (2 * b) ^ j ≤ (4 * b) ^ j := by
    rw [show 4 * b = 2 * (2 * b) by ring, mul_pow (2 : ℝ) (2 * b) j]
    exact mul_le_mul_of_nonneg_right ((by norm_num : (3 : ℝ) ≤ 4).trans hpow) (by positivity)
  have hlarge : 2 * (4 * b) ^ j ≤ (8 * b) ^ j := by
    rw [show 8 * b = 2 * (4 * b) by ring, mul_pow (2 : ℝ) (4 * b) j]
    exact mul_le_mul_of_nonneg_right ((by norm_num : (2 : ℝ) ≤ 4).trans hpow) (by positivity)
  linarith only [hY, hY', hP, hE, ht, hp, hsum, hlarge]

theorem exists_large_log_derivative :
    ∃ A C₀ r₀ : ℝ, 1 ≤ A ∧ 0 < C₀ ∧ 0 < r₀ ∧
      ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (t r L : ℝ) (K : ℕ) (ρ : ℂ),
        (χ ≠ 1 ∨ 2 ≤ |t|) → Real.log ((M : ℝ) * (|t| + 2)) ≤ L →
        0 < r → 1 ≤ r * L → r ≤ r₀ → C₀ * (r * L) ≤ K →
        IsLZero χ ρ → ‖ρ - (1 + t * I)‖ ≤ r →
        ∃ k : ℕ, K ≤ k ∧ k ≤ 2 * K ∧
          (1 / (A * r)) ^ (k + 1) ≤
            ‖(-1 : ℂ) ^ k / (k.factorial : ℂ) *
              iteratedDeriv k (negLD χ) (((1 + r : ℝ) : ℂ) + t * I)‖ := by
  classical
  obtain ⟨C, hC, hlocal⟩ := deuring_heilbronn_local
  obtain ⟨D, hD, hright⟩ := l_log_deriv_right
  let A : ℝ := 6400 * Real.exp 1
  have hA : 1 ≤ A := by
    dsimp only [A]
    linarith only [Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)]
  have hA₀ : 0 < A := zero_lt_one.trans_le hA
  let b : ℝ := 1 / (8 * A)
  have hb : 0 < b := by dsimp only [b]; positivity
  have hb' : b ≤ 1 / 2 := by
    dsimp only [b]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith only [hA])
  have hb₁ : b ≤ 1 := by linarith only [hb']
  let U := 2 + D + C
  let r₀ := b ^ 2 / 25
  refine ⟨2 * A, U / b ^ 2, r₀, by linarith only [hA], by dsimp only [U]; positivity,
    by dsimp only [r₀]; positivity, ?_⟩
  intro M _ χ t r L K ρ hχ hL hr hrL hr₀ hK hρ hρnear
  let ℓ := Real.log ((M : ℝ) * (|t| + 2))
  let s : ℂ := ((1 + r : ℝ) : ℂ) + t * I
  let w (z : ℂ) := (r : ℂ) / z
  have hrs : 25 * r ≤ b ^ 2 := by dsimp only [r₀] at hr₀; linarith only [hr₀]
  have hbb : b ^ 2 ≤ b := by nlinarith only [mul_le_mul_of_nonneg_left hb₁ hb.le]
  have hrr : r ≤ 1 / 25 := by linarith only [hrs, hbb, hb₁]
  have hsr : s.re = 1 + r := by simp [s]
  have hs₁ : 1 < s.re := by rw [hsr]; linarith only [hr]
  have hs : ‖s - ((26 / 25 : ℂ) + t * I)‖ ≤ 1 / 25 := by
    have he : s - ((26 / 25 : ℂ) + t * I) = ((r - 1 / 25 : ℝ) : ℂ) := by
      dsimp only [s]
      push_cast
      ring
    rw [he, norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hrr)]
    linarith only [hr]
  obtain ⟨Z, m, hZ, hm, -, hZright, -, hE⟩ := hlocal M χ t
  have hρZ : ρ ∈ Z := by
    refine (hZ ρ).mpr ⟨?_, hρ⟩
    have he : ρ - ((26 / 25 : ℂ) + t * I) = (ρ - (1 + t * I)) - (1 / 25 : ℂ) := by ring
    rw [he]
    have h := norm_sub_le (ρ - (1 + t * I)) (1 / 25)
    have hn : ‖(1 / 25 : ℂ)‖ = 1 / 25 := by norm_num [norm_div]
    rw [hn] at h
    linarith only [h, hρnear, hrr]
  have hnear : 1 / 2 ≤ ‖w (s - ρ)‖ := by
    have hn₀ : 0 < ‖s - ρ‖ := by
      have h := re_le_norm (s - ρ)
      rw [sub_re, hsr] at h
      linarith only [h, hr, hZright ρ hρZ]
    have hn : ‖s - ρ‖ ≤ 2 * r := by
      have he : s - ρ = (r : ℂ) - (ρ - (1 + t * I)) := by dsimp only [s]; push_cast; ring
      rw [he]
      have h := norm_sub_le ((r : ℝ) : ℂ) (ρ - (1 + t * I))
      rw [norm_real, Real.norm_of_nonneg hr.le] at h
      linarith only [h, hρnear]
    dsimp only [w]
    rw [norm_div, norm_real, Real.norm_of_nonneg hr.le, le_div_iff₀ hn₀]
    linarith only [hn]
  have hsum := local_reciprocal_square_mass χ t r (C * ℓ) D hr Z m hZright
    (by
      have h := hright M χ s hs₁
      rw [hsr, add_sub_cancel_left] at h
      exact h)
    (by simpa only [zero_add, pow_zero, pow_one, Nat.factorial_zero, Nat.cast_one, div_one,
      one_mul, mul_one, iteratedDeriv_zero] using hE 0 s hs₁ hs)
  have hscale : U * (r * L) ≤ (K : ℝ) * b ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hK (sq_nonneg b)
    have he : U / b ^ 2 * (r * L) * b ^ 2 = U * (r * L) := by field_simp [hb.ne']
    rwa [he] at h
  have hmass : (∑ ρ ∈ Z, (m ρ : ℝ) * ‖w (s - ρ)‖ ^ 2) ≤ (K : ℝ) * b ^ 2 := by
    calc
      _ = r ^ 2 * ∑ ρ ∈ Z, (m ρ : ℝ) / ‖s - ρ‖ ^ 2 := by
        rw [mul_sum]
        refine sum_congr rfl fun ρ _ => ?_
        dsimp only [w]
        rw [norm_div, norm_real, Real.norm_of_nonneg hr.le, div_pow]
        ring
      _ ≤ r ^ 2 * ((2 / r + D + C * ℓ) / r) := mul_le_mul_of_nonneg_left hsum (sq_nonneg r)
      _ = 2 + D * r + C * (r * ℓ) := by field_simp [hr.ne']
      _ ≤ U * (r * L) := by
        dsimp only [U]
        linarith only [mul_le_mul_of_nonneg_left (show r ≤ r * L by linarith only [hrr, hrL]) hD,
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL hr.le) hC.le, hrL]
      _ ≤ _ := hscale
  obtain ⟨j, hj, hj', hdet⟩ := weighted_detector_power_sum Z m s w K b hb hb' hmass
    ⟨ρ, hρZ, hm ρ hρZ, hnear⟩
  have hj₂ : 2 ≤ j := by omega
  let k := j - 1
  have hkj : k + 1 = j := by omega
  let G := (-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD χ) s
  let P : ℂ := if χ = 1 then 1 / (s - 1) ^ j else 0
  let Y := ∑ ρ ∈ Z, (m ρ : ℂ) * w (s - ρ) ^ j
  have hY : (8 * b) ^ j ≤ ‖Y‖ + (K : ℝ) * b ^ j := by
    have he : 8 * b = 1 / A := by dsimp only [b]; field_simp
    rw [he]
    exact hdet
  have hP : ‖(r : ℂ) ^ j * P‖ ≤ b ^ j := by
    dsimp only [P]
    split_ifs with hprincipal
    · have ht := hχ.resolve_left (not_not_intro hprincipal)
      have hn := (abs_im_le_norm (s - 1))
      have ht' : |t| ≤ ‖s - 1‖ := by simpa [s] using hn
      rw [norm_mul, norm_pow, norm_real, Real.norm_of_nonneg hr.le, norm_div, norm_one, norm_pow,
        mul_one_div, ← div_pow]
      refine pow_le_pow_left₀ (by positivity) ((div_le_iff₀ (by linarith only [ht, ht'])).mpr ?_) j
      linarith only [hrs, hbb, hb, mul_le_mul_of_nonneg_left ht' hb.le,
        mul_le_mul_of_nonneg_left ht hb.le]
    · rw [mul_zero, norm_zero]
      positivity
  have hCL : C * (r * ℓ) ≤ K := by
    have hCb : C ≤ U / b ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hb)).mpr
      dsimp only [U]
      linarith only [mul_le_mul_of_nonneg_left (hbb.trans hb₁) hC.le, hD]
    calc
      C * (r * ℓ) ≤ C * (r * L) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL hr.le) hC.le
      _ ≤ U / b ^ 2 * (r * L) := mul_le_mul_of_nonneg_right hCb (zero_le_one.trans hrL)
      _ ≤ _ := hK
  have hE' : ‖(r : ℂ) ^ j * G - (r : ℂ) ^ j * P + Y‖ ≤ (K : ℝ) * b ^ j := by
    have he : (r : ℂ) ^ j * (G - P + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ j) =
        (r : ℂ) ^ j * G - (r : ℂ) ^ j * P + Y := by
      rw [mul_add, mul_sub, mul_sum]
      congr 1
      refine sum_congr rfl fun ρ _ => ?_
      dsimp only [w]
      rw [div_pow]
      ring
    rw [← he, norm_mul, norm_pow, norm_real, Real.norm_of_nonneg hr.le]
    calc
      _ ≤ r ^ j * (C * ℓ * 25 ^ k) := mul_le_mul_of_nonneg_left
        (by simpa only [G, P, ← hkj] using hE k s hs₁ hs) (by positivity)
      _ = C * (r * ℓ) * (25 * r) ^ k := by rw [← hkj, pow_succ, mul_pow]; ring
      _ ≤ (K : ℝ) * b ^ j := by
        apply mul_le_mul hCL _ (by positivity) (Nat.cast_nonneg _)
        calc
          _ ≤ (b ^ 2) ^ k := pow_le_pow_left₀ (by positivity) hrs k
          _ = b ^ (2 * k) := (pow_mul b 2 k).symm
          _ ≤ _ := pow_le_pow_of_le_one hb.le hb₁ (by omega)
  have hbound := detector_absorb K j hj hj₂ hb ((r : ℂ) ^ j * G) ((r : ℂ) ^ j * P) Y hY hP hE'
  rw [norm_mul, norm_pow, norm_real, Real.norm_of_nonneg hr.le, ← div_le_iff₀' (pow_pos hr j),
    ← div_pow] at hbound
  have hbA : 4 * b / r = 1 / (2 * A * r) := by
    dsimp only [b]
    field_simp [hr.ne', hA₀.ne']
    <;> ring
  rw [hbA] at hbound
  refine ⟨k, by omega, by omega, ?_⟩
  simpa only [hkj] using hbound

end QH.PrimeProgressions
