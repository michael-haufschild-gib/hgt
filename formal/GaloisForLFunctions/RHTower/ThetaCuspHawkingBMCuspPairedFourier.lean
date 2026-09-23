import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspMeanCharacter

/-!
# Exact opposite-frequency selection for the complex square of an infinite paired Fourier series.

This leaf proves the displayed source or cusp identity. Causal continuation,
left-QNM evaluation and Hawking-clock extinction remain separate obligations.
-/

open Complex MeasureTheory Set Filter Topology
namespace RHTower.D4BMCuspProjection
noncomputable section

private theorem mean_add (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) :
    mean (fun x => f x+g x) = mean f+mean g :=
  integral_add hf.integrableOn_Ioc hg.integrableOn_Ioc

private theorem mean_const_mul (c : ℂ) (f : ℝ → ℂ) :
    mean (fun x => c*f x) = c*mean f := integral_const_mul c f

/-- The paired positive and negative original cusp frequencies. -/
def wave (N : ℕ) (x : ℝ) : ℂ := character (N+1) x+character (-(N+1)) x

theorem wave_continuous (N : ℕ) : Continuous (wave N) :=
  (character_continuous _).add (character_continuous _)

theorem wave_norm_le (N : ℕ) (x : ℝ) : ‖wave N x‖ ≤ 2 := by
  exact (norm_add_le _ _).trans (by rw [character_norm,character_norm]; norm_num)

theorem mean_wave (N : ℕ) : mean (wave N) = 0 := by
  change mean (fun x => character (N+1) x+character (-(N+1)) x)=0
  rw [mean_add (character (N+1)) (character (-(N+1))) (character_continuous _) (character_continuous _),
    mean_character,mean_character]
  split_ifs <;> norm_num <;> omega

theorem mean_wave_mul (N M : ℕ) :
    mean (fun x => wave N x*wave M x) = if N=M then 2 else 0 := by
  have he : (fun x => wave N x*wave M x) = fun x =>
      (character ((N+1)+(M+1)) x+character ((N+1)+(-(M+1))) x)+
      (character ((-(N+1))+(M+1)) x+character ((-(N+1))+(-(M+1))) x) := by
    funext x
    simp only [wave,add_mul,mul_add,character_mul]
    ring
  rw [he,mean_add
    (fun x => character ((N+1)+(M+1)) x+character ((N+1)+(-(M+1))) x)
    (fun x => character ((-(N+1))+(M+1)) x+character ((-(N+1))+(-(M+1))) x)
    ((character_continuous _).add (character_continuous _))
    ((character_continuous _).add (character_continuous _)),
    mean_add (character ((N+1)+(M+1))) (character ((N+1)+(-(M+1))))
      (character_continuous _) (character_continuous _),
    mean_add (character ((-(N+1))+(M+1))) (character ((-(N+1))+(-(M+1))))
      (character_continuous _) (character_continuous _)]
  simp only [mean_character]
  split_ifs <;> norm_num <;> omega

/-- The entire paired Fourier series, retaining its complex amplitudes. -/
def series (a : ℕ → ℂ) (x : ℝ) : ℂ := ∑' N, a N*wave N x

private theorem series_term_norm (a : ℕ → ℂ) (N : ℕ) (x : ℝ) :
    ‖a N*wave N x‖ ≤ 2*‖a N‖ := by
  rw [norm_mul,mul_comm (2:ℝ)]
  exact mul_le_mul_of_nonneg_left (wave_norm_le N x) (norm_nonneg _)

theorem series_continuous (a : ℕ → ℂ) (ha : Summable (fun N => ‖a N‖)) :
    Continuous (series a) :=
  continuous_tsum (fun _ => continuous_const.mul (wave_continuous _))
    (ha.mul_left 2) (series_term_norm a)

theorem mean_series (a : ℕ → ℂ) (ha : Summable (fun N => ‖a N‖)) : mean (series a) = 0 := by
  change mean (fun x => ∑' N, a N*wave N x) = 0
  rw [mean_tsum (fun N x => a N*wave N x) _ (ha.mul_left 2)
    (fun _ => continuous_const.mul (wave_continuous _)) (series_term_norm a)]
  simp only [mean_const_mul,mean_wave,mul_zero,tsum_zero]

/-- Opposite-frequency selection for an absolutely convergent complex squared series.
The coefficient is a square, not a conjugate square. -/
theorem mean_series_sq (a : ℕ → ℂ) (ha : Summable (fun N => ‖a N‖)) :
    mean (fun x => series a x^(2 : ℕ)) = 2*∑' N, a N^(2 : ℕ) := by
  let B : ℕ × ℕ → ℝ := fun p => (2*‖a p.1‖)*(2*‖a p.2‖)
  have hB : Summable B := (ha.mul_left 2).mul_of_nonneg (ha.mul_left 2)
    (fun _ => by positivity) (fun _ => by positivity)
  have hterm (p : ℕ × ℕ) (x : ℝ) :
      ‖(a p.1*wave p.1 x)*(a p.2*wave p.2 x)‖ ≤ B p := by
    rw [norm_mul]
    exact mul_le_mul (series_term_norm a _ _) (series_term_norm a _ _)
      (norm_nonneg _) (by positivity)
  have hprod (x : ℝ) : series a x^(2 : ℕ) =
      ∑' p : ℕ × ℕ, (a p.1*wave p.1 x)*(a p.2*wave p.2 x) := by
    have hn : Summable (fun N => ‖a N*wave N x‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun N => series_term_norm a N x)
        (ha.mul_left 2)
    simpa only [series,pow_two] using tsum_mul_tsum_of_summable_norm hn hn
  simp_rw [hprod]
  rw [mean_tsum (fun p x => (a p.1*wave p.1 x)*(a p.2*wave p.2 x)) B hB (fun p => (continuous_const.mul (wave_continuous p.1)).mul
    (continuous_const.mul (wave_continuous p.2))) hterm]
  have hm (p : ℕ × ℕ) : mean (fun x => (a p.1*wave p.1 x)*(a p.2*wave p.2 x)) =
      if p.1=p.2 then 2*a p.1^(2 : ℕ) else 0 := by
    have he : (fun x => (a p.1*wave p.1 x)*(a p.2*wave p.2 x)) =
      (fun x => (a p.1*a p.2)*(wave p.1 x*wave p.2 x)) := by funext x; ring
    rw [he,mean_const_mul,mean_wave_mul]
    split_ifs with h
    · rw [h]; ring
    · ring
  simp_rw [hm]
  have hd : Summable (fun p : ℕ × ℕ => if p.1=p.2 then 2*a p.1^(2 : ℕ) else 0) := by
    apply Summable.of_norm_bounded hB
    intro p
    split_ifs with h
    · rw [norm_mul,norm_pow,Complex.norm_ofNat]
      dsimp [B]
      rw [h]
      nlinarith [sq_nonneg ‖a p.2‖]
    · simp only [norm_zero]
      dsimp [B]
      positivity
  rw [hd.tsum_prod]
  have hi (N : ℕ) : (∑' M : ℕ, if N=M then 2*a N^(2 : ℕ) else 0) = 2*a N^(2 : ℕ) := by
    rw [tsum_eq_single N]
    · simp
    · intro M hM
      simp [Ne.symm hM]
  simp_rw [hi]
  rw [tsum_mul_left]

end
end RHTower.D4BMCuspProjection
