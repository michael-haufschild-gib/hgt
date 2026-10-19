import GaloisForLFunctions.BiScaleUncertainty.SieveHighestModeSharpWitness
import GaloisForLFunctions.BiScaleUncertainty.SieveHighestDyadicCoordinate

/-! The cube-root exponent cannot be improved in any neighborhood of the pure parity source. -/

set_option autoImplicit false

namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.TopAnchor.Sharp
open GaloisForLFunctions.BezoutValuationIncidence

/-- No exponent above one third works uniformly even near the pure parity profile,
while both highest admitted dyadic coordinates remain exactly one. -/
theorem no_improved_exponent_near_parity (α : ℝ) (hα : 1/3 < α)
    (R : ℝ) (hR : 0 < R) :
    ¬∃ C : ℝ, ∀ (c e : ℕ → ℝ) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
      1 ≤ |selbergMultiplesCoord 3 c (topOrder 3)| →
      1 ≤ |selbergMultiplesCoord 3 e (topOrder 3)| →
      (∀ n, |sieveSeq 3 c n-sieveSeq 3 (weights 0) n| ≤ R) →
      (∀ n, |sieveSeq 3 e n-sieveSeq 3 (weights 0) n| ≤ R) →
      (∀ h : Fin 5 → ℕ, |translatedMoment 3 c h-translatedMoment 3 e h| ≤ ε) →
      (∀ h : Fin 6 → ℕ, |translatedMoment 3 c h-translatedMoment 3 e h| ≤ ε) →
      ∃ h : ℕ, ∀ n : ℕ, |sieveSeq 3 e n-sieveSeq 3 c (n+h)| ≤ C*ε^α := by
  rintro ⟨C, hC⟩
  have htop : topOrder 3 = 2 := by decide
  have hg : 0 < 3*α-1 := by linarith
  let K : ℝ := C*(224 : ℝ)^α
  let M : ℝ := min (R/2) (1/8)
  have hM : 0 < M := by dsimp [M]; positivity
  let x : ℝ := (|K|+1)/(3*α-1)+M⁻¹
  let t : ℝ := Real.exp (-x)
  have hx : 0 < x := by dsimp [x]; positivity
  have ht : 0 < t := Real.exp_pos _
  have htM : t ≤ M := by
    have hMx : M⁻¹ ≤ x := by
      have hb : 0 ≤ (|K|+1)/(3*α-1) := by positivity
      dsimp [x]
      linarith
    have hMe : M⁻¹ ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    have hmul := mul_le_mul_of_nonneg_left hMe hM.le
    rw [mul_inv_cancel₀ hM.ne'] at hmul
    change Real.exp (-x) ≤ M
    rw [Real.exp_neg, ← one_div]
    exact (div_le_iff₀ (Real.exp_pos x)).mpr hmul
  have ht8 : t ≤ 1/8 := htM.trans (min_le_right _ _)
  have ht1 : t ≤ 1 := by linarith
  have htR : 2*t ≤ R := by
    have hm := htM.trans (min_le_left _ _)
    linarith
  have he0 : 0 ≤ 224*t^3 := by positivity
  have he1 : 224*t^3 ≤ 1 := by
    have hp := pow_le_pow_left₀ ht.le ht8 3
    norm_num at hp
    linarith
  have hnear (n : ℕ) := (near_parity t n).trans (by simpa [abs_of_pos ht] using htR)
  have hnearNeg (n : ℕ) :=
    (near_parity (-t) n).trans (by simpa [abs_neg, abs_of_pos ht] using htR)
  obtain ⟨h, hh⟩ := hC (weights t) (weights (-t)) (224*t^3) he0 he1
    (by rw [htop, coordinate_two]; norm_num) (by rw [htop, coordinate_two]; norm_num)
    hnear hnearNeg
    (fun v => by rw [abs_sub_comm]; exact fifth_error ht.le ht1 v)
    (fun v => by rw [sixth_equal, sub_self, abs_zero]; exact he0)
  obtain ⟨n, hn⟩ := translation_separation t h
  have hb := hn.trans (hh n)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 224) (pow_nonneg ht.le 3),
    ← Real.rpow_natCast_mul ht.le 3 α] at hb
  norm_num only [Nat.cast_ofNat] at hb
  have hp : 0 < t^(3*α) := by positivity
  have hratio : t^(1-3*α) ≤ K := by
    rw [Real.rpow_sub ht, Real.rpow_one]
    apply (div_le_iff₀ hp).mpr
    dsimp [K]
    nlinarith only [hb, ht]
  have he : t^(1-3*α) = Real.exp (|K|+1+M⁻¹*(3*α-1)) := by
    rw [Real.rpow_def_of_pos ht]
    change Real.exp (Real.log (Real.exp (-x))*(1-3*α)) = _
    rw [Real.log_exp]
    congr 1
    dsimp [x]
    field_simp [hg.ne', hM.ne']
    ring
  rw [he] at hratio
  have hnonneg : 0 ≤ M⁻¹*(3*α-1) := mul_nonneg (inv_nonneg.mpr hM.le) hg.le
  linarith [Real.add_one_le_exp (|K|+1+M⁻¹*(3*α-1)), le_abs_self K]

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.TopAnchor.Sharp
