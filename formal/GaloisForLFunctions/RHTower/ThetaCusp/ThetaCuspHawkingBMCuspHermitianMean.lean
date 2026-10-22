import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspSourceMean

/-! Exact Hermitian means of the original paired Fourier series. -/
open Complex MeasureTheory Set Filter Topology
namespace RHTower.D4BMCuspProjection
noncomputable section

/-- Complex conjugation reverses the original integer character. -/
theorem character_conj (k : ℤ) (x : ℝ) :
    (starRingEnd ℂ) (character k x) = character (-k) x := by
  simp only [character, ← Complex.exp_conj, map_mul, map_ofNat, Complex.conj_ofReal,
    Complex.conj_I, map_intCast, Int.cast_neg]
  congr 1
  ring

/-- The unchanged pair of opposite characters is real. -/
theorem wave_conj (N : ℕ) (x : ℝ) : (starRingEnd ℂ) (wave N x) = wave N x := by
  simp only [wave,map_add,character_conj,neg_neg]
  ring

/-- Conjugation acts on the coefficients of the original paired series. -/
theorem series_conj (a : ℕ → ℂ) (x : ℝ) :
    (starRingEnd ℂ) (series a x) = series (fun N => (starRingEnd ℂ) (a N)) x := by
  simp only [series,Complex.conj_tsum,map_mul,wave_conj]

private theorem term_bound (a : ℕ → ℂ) (N : ℕ) (x : ℝ) :
    ‖a N*wave N x‖ ≤ 2*‖a N‖ := by
  rw [norm_mul,mul_comm (2:ℝ)]
  exact mul_le_mul_of_nonneg_left (wave_norm_le N x) (norm_nonneg _)

/-- The bilinear mean retains the diagonal product of both actual coefficient sequences. -/
theorem mean_series_mul (a b : ℕ → ℂ)
    (ha : Summable (fun N => ‖a N‖)) (hb : Summable (fun N => ‖b N‖)) :
    mean (fun x => series a x*series b x) = 2*∑' N, a N*b N := by
  let B : ℕ × ℕ → ℝ := fun p => (2*‖a p.1‖)*(2*‖b p.2‖)
  have hB : Summable B := (ha.mul_left 2).mul_of_nonneg (hb.mul_left 2)
    (fun _ => by positivity) (fun _ => by positivity)
  have ht (p : ℕ × ℕ) (x : ℝ) :
      ‖(a p.1*wave p.1 x)*(b p.2*wave p.2 x)‖ ≤ B p := by
    rw [norm_mul]
    exact mul_le_mul (term_bound a _ _) (term_bound b _ _) (norm_nonneg _) (by positivity)
  have hp (x : ℝ) : series a x*series b x =
      ∑' p : ℕ × ℕ, (a p.1*wave p.1 x)*(b p.2*wave p.2 x) := by
    have hna : Summable (fun N => ‖a N*wave N x‖) :=
      (ha.mul_left 2).of_nonneg_of_le (fun _ => norm_nonneg _) (fun N => term_bound a N x)
    have hnb : Summable (fun N => ‖b N*wave N x‖) :=
      (hb.mul_left 2).of_nonneg_of_le (fun _ => norm_nonneg _) (fun N => term_bound b N x)
    exact tsum_mul_tsum_of_summable_norm hna hnb
  simp_rw [hp]
  rw [mean_tsum (fun p x => (a p.1*wave p.1 x)*(b p.2*wave p.2 x)) B hB (fun p => (continuous_const.mul (wave_continuous p.1)).mul
    (continuous_const.mul (wave_continuous p.2))) ht]
  have hm (p : ℕ × ℕ) : mean (fun x => (a p.1*wave p.1 x)*(b p.2*wave p.2 x)) =
      if p.1=p.2 then 2*(a p.1*b p.1) else 0 := by
    have he : (fun x => (a p.1*wave p.1 x)*(b p.2*wave p.2 x)) =
      fun x => (a p.1*b p.2)*(wave p.1 x*wave p.2 x) := by funext x; ring
    rw [he]
    change (∫ x in Ioc (-1/2:ℝ) (1/2), _*_) = _
    rw [integral_const_mul]
    change (a p.1*b p.2)*mean (fun x => wave p.1 x*wave p.2 x) = _
    rw [mean_wave_mul]
    split_ifs with h
    · rw [h]; ring
    · ring
  simp_rw [hm]
  have hd : Summable (fun p : ℕ × ℕ => if p.1=p.2 then 2*(a p.1*b p.1) else 0) := by
    apply Summable.of_norm_bounded hB
    intro p
    split_ifs with h
    · rw [norm_mul,norm_mul,Complex.norm_ofNat]
      dsimp [B]
      rw [h]
      nlinarith [mul_nonneg (norm_nonneg (a p.2)) (norm_nonneg (b p.2))]
    · simp only [norm_zero]
      dsimp [B]
      positivity
  rw [hd.tsum_prod]
  have hi (N : ℕ) : (∑' M : ℕ, if N=M then 2*(a N*b N) else 0) = 2*(a N*b N) := by
    rw [tsum_eq_single N]
    · simp
    · intro M hM; simp [Ne.symm hM]
  simp_rw [hi]
  rw [tsum_mul_left]

/-- The actual squared norm mean is twice the complete squared coefficient norm mass. -/
theorem mean_series_norm_sq (a : ℕ → ℂ) (ha : Summable (fun N => ‖a N‖)) :
    (∫ x in Ioc (-1/2:ℝ) (1/2), ‖series a x‖^(2 : ℕ)) = 2*∑' N, ‖a N‖^(2 : ℕ) := by
  have hb : Summable (fun N => ‖(starRingEnd ℂ) (a N)‖) := by simpa only [norm_conj] using ha
  have h := mean_series_mul (fun N => (starRingEnd ℂ) (a N)) a hb ha
  simp_rw [← series_conj,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq] at h
  change (∫ x in Ioc (-1/2:ℝ) (1/2), ((‖series a x‖^(2 : ℕ):ℝ):ℂ)) = _ at h
  have hi : (∫ x in Ioc (-1/2:ℝ) (1/2), ((‖series a x‖^(2 : ℕ):ℝ):ℂ)) =
      ((∫ x in Ioc (-1/2:ℝ) (1/2), ‖series a x‖^(2 : ℕ) : ℝ):ℂ) := integral_ofReal
  rw [hi,← Complex.ofReal_tsum] at h
  exact_mod_cast h

end
end RHTower.D4BMCuspProjection
