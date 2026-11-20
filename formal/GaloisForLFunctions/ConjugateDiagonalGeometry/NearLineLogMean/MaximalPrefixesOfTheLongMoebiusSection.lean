import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.LongMoebiusSecondMomentRigidity
import GaloisForLFunctions.RHTower.BourgainPartialSummation

/-!
# Simultaneous cutoffs and decreasing weights in the long Möbius mean

At each height the largest prefix norm is the exact supremum over all
decreasing weights in [0,1]. Their level sets are prefixes; Abel summation
bounds their superposition, and an indicator of one prefix attains equality.
Taking this maximum inside the integral preserves the optimal coefficient
of the length exponent in the cofinal second-moment criterion.
-/

noncomputable section
open Finset Complex Filter Topology MeasureTheory
open GaloisForLFunctions.MultiscaleMollifiedZetaField
open GaloisForLFunctions.SquareRootThreshold
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

/-- Largest critical-line Möbius prefix visible at the given height. -/
def moebiusPrefixMaximum (N : ℕ) (t : ℝ) : ℝ :=
  (range (N+1)).sup' ⟨0,by simp⟩ fun j => ‖moebiusPoly j (linePoint t)‖

theorem moebius_prefix_norm_le_maximum {j N : ℕ} (hj : j ≤ N) (t : ℝ) :
    ‖moebiusPoly j (linePoint t)‖ ≤ moebiusPrefixMaximum N t :=
  le_sup' (fun k => ‖moebiusPoly k (linePoint t)‖) (mem_range.mpr (Nat.lt_succ_of_le hj))

theorem continuous_moebiusPrefixMaximum (N : ℕ) : Continuous (moebiusPrefixMaximum N) :=
  Continuous.finset_sup'_apply _ fun j _ =>
    ((differentiable_moebiusPoly j).continuous.comp continuous_linePoint).norm

private def criticalTerm (t : ℝ) (n : ℕ) : ℂ :=
  _root_.RHTower.mobCoeff n*((n:ℝ):ℂ)^(-linePoint t)

private theorem prefix_eq (N : ℕ) (t : ℝ) :
    (∑ n ∈ Ioc 0 N, criticalTerm t n) = moebiusPoly N (linePoint t) := by
  have h : Ioc 0 N = Icc 1 N := by ext n; simp only [mem_Icc,mem_Ioc]; omega
  rw [h]; rfl

/-- Attenuating each term by a decreasing weight between zero and one,
even with a different choice at every height, has exact extremal value
equal to the largest prefix norm. -/
theorem moebius_prefix_maximum_iff_taper_bound (N : ℕ) (t B : ℝ) :
    moebiusPrefixMaximum N t ≤ B ↔
    ∀ w : ℕ → ℝ, (∀ n, 0 ≤ w n) → Antitone w → w 1 ≤ 1 →
      ‖∑ n ∈ Ioc 0 N, (w n:ℂ)*_root_.RHTower.mobCoeff n*((n:ℝ):ℂ)^(-linePoint t)‖ ≤ B := by
  constructor
  · intro h w hw hm h1
    have hB := (norm_nonneg _).trans ((moebius_prefix_norm_le_maximum (j:=N) le_rfl t).trans h)
    by_cases hN : 0 < N
    · have H := _root_.RHTower.norm_sum_Ioc_weight_mul_le (criticalTerm t) w hN hw
        (fun n _ => hm (Nat.le_succ n)) (B:=B) (fun n hn => by
          rw [prefix_eq]; exact (moebius_prefix_norm_le_maximum (mem_Ioc.mp hn).2 t).trans h)
      simpa only [criticalTerm,mul_assoc] using H.trans (mul_le_of_le_one_right hB h1)
    · have hzero : N=0 := by omega
      simpa [hzero] using hB
  · intro h
    apply sup'_le
    intro j hj
    have hjN := Nat.le_of_lt_succ (mem_range.mp hj)
    let w (n : ℕ) : ℝ := if n ≤ j then 1 else 0
    have hw (n : ℕ) : 0 ≤ w n := by dsimp [w]; split <;> norm_num
    have hm : Antitone w := by
      intro a b hab
      by_cases hb : b ≤ j
      · simp only [w,if_pos hb,if_pos (hab.trans hb),le_refl]
      · simpa only [w,if_neg hb] using hw a
    have H := h w hw hm (by dsimp [w]; split <;> norm_num)
    have he : (Ioc 0 N).filter (fun n => n ≤ j) = Ioc 0 j := by
      ext n; simp only [mem_filter,mem_Ioc]; omega
    have hwSum : (∑ n ∈ Ioc 0 j, criticalTerm t n) =
        ∑ n ∈ Ioc 0 N, (w n:ℂ)*_root_.RHTower.mobCoeff n*((n:ℝ):ℂ)^(-linePoint t) := by
      rw [←he,sum_filter]
      apply sum_congr rfl
      intro n _
      by_cases hn : n ≤ j <;> simp [w,hn,criticalTerm]
    rwa [←prefix_eq,hwSum]

private theorem maximum_at_cutoff {θ ε T : ℝ} (hε : 0 < ε) (hT : 1 ≤ T)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ (j : ℕ) (t : ℝ), 1 ≤ j → ‖moebiusPoly j (linePoint t)‖ ≤
      2*(j:ℝ)^(zetaZeroWidth+ε)*(K*(1+|t|))) {t : ℝ} (ht : t ∈ Set.Icc 1 T) :
    moebiusPrefixMaximum ⌊T^θ⌋₊ t ≤ 4*K*T*T^(θ*(zetaZeroWidth+ε)) := by
  have hT0 := zero_lt_one.trans_le hT
  apply sup'_le
  intro j hj
  have hjN := Nat.le_of_lt_succ (mem_range.mp hj)
  rcases Nat.eq_zero_or_pos j with rfl|hjpos
  · simp only [moebiusPoly,_root_.RHTower.edPoly,show Icc 1 0 = ∅ from by decide,sum_empty,norm_zero]
    positivity
  have hjT : (j:ℝ) ≤ T^θ := (Nat.cast_le.mpr hjN).trans (Nat.floor_le (by positivity))
  have hx := Real.rpow_le_rpow (Nat.cast_nonneg _) hjT (add_nonneg zetaZeroWidth_nonneg hε.le)
  rw [←Real.rpow_mul hT0.le] at hx
  have hu : 1+|t| ≤ 2*T := by rw [abs_of_nonneg (zero_le_one.trans ht.1)]; linarith only [ht.2,hT]
  refine (hbound j t hjpos).trans ?_
  calc 2*(j:ℝ)^(zetaZeroWidth+ε)*(K*(1+|t|))
      ≤ 2*T^(θ*(zetaZeroWidth+ε))*(K*(2*T)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hx zero_le_two)
          (mul_le_mul_of_nonneg_left hu hK) (by positivity) (by positivity)
    _ = _ := by ring

/-- Uniform in every cutoff up to T^θ inside the mean, with arbitrarily
small fixed slack above the intercept three. -/
theorem maximal_moebius_moment_upper {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
    (∫ t in (1:ℝ)..T, (moebiusPrefixMaximum ⌊T^θ⌋₊ t)^2) ≤ C*T^(3+η+2*zetaZeroWidth*θ) := by
  let ε := η/(2*θ)
  have hε : 0 < ε := div_pos hη (by positivity)
  obtain ⟨K,hK,hbound⟩ := exists_norm_moebiusPoly_line_le hε
  refine ⟨16*K^2,by positivity,fun T hT => ?_⟩
  have hT0 := zero_lt_one.trans_le hT
  let r := θ*(zetaZeroWidth+ε)
  let U := 4*K*T*T^r
  have hpt (t : ℝ) (ht : t ∈ Set.Icc 1 T) : (moebiusPrefixMaximum ⌊T^θ⌋₊ t)^2 ≤ U^2 :=
    pow_le_pow_left₀ ((norm_nonneg _).trans (moebius_prefix_norm_le_maximum le_rfl t))
      (maximum_at_cutoff (θ:=θ) hε hT hK hbound ht) 2
  have hi := intervalIntegral.integral_mono_on (μ:=volume) hT
    (((continuous_moebiusPrefixMaximum _).pow 2).intervalIntegrable 1 T)
    intervalIntegrable_const hpt
  rw [intervalIntegral.integral_const,smul_eq_mul] at hi
  apply hi.trans
  calc (T-1)*U^2 ≤ T*U^2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    _ = 16*K^2*(T^(3:ℝ)*(T^r)^2) := by simp only [U,Real.rpow_ofNat]; ring
    _ = _ := by
      rw [←Real.rpow_natCast (T^r) 2,←Real.rpow_mul hT0.le,←Real.rpow_add hT0]
      congr 2
      dsimp [r,ε]
      field_simp [hθ.ne']
      ring

/-- The infimal length slope remains twice the zeta-zero width even when
the maximizing cutoff is allowed to change at every height. -/
theorem zetaZeroWidth_iff_cofinal_maximal_moebius_slope {β : ℝ} (hβ : 0 ≤ β) :
    zetaZeroWidth ≤ β ↔ ∃ K : ℝ, 0 ≤ K ∧ ∀ θ₀ : ℝ, 0 < θ₀ →
      ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ᶠ T : ℝ in atTop,
      (∫ t in (1:ℝ)..T, (moebiusPrefixMaximum ⌊T^θ⌋₊ t)^2) ≤ C*T^(K+2*β*θ) := by
  constructor
  · intro h
    refine ⟨4,by norm_num,fun θ hθ => ⟨θ,le_rfl,?_⟩⟩
    obtain ⟨C,hC,H⟩ := maximal_moebius_moment_upper hθ (zero_lt_one : (0:ℝ)<1)
    refine ⟨C,hC,(eventually_ge_atTop (1:ℝ)).frequently.mono fun T hT => (H T hT).trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ hC
    exact Real.rpow_le_rpow_of_exponent_le hT (by nlinarith only [mul_le_mul_of_nonneg_right h hθ.le])
  · rintro ⟨K,hK,H⟩
    apply zetaZeroWidth_le_of_cofinal_pure_moebius_slope hβ hK
    intro θ₀ hθ₀
    obtain ⟨θ,hθ,C,hC,h⟩ := H θ₀ hθ₀
    refine ⟨θ,hθ,C,hC,(h.and_eventually (eventually_ge_atTop (1:ℝ))).mono fun T ⟨hb,hT⟩ => ?_⟩
    simp_rw [edPoly_moebiusMollifierCoeff_eq_moebiusPoly]
    refine (intervalIntegral.integral_mono_on hT ?_ ?_ (fun t _ =>
      pow_le_pow_left₀ (norm_nonneg _) (moebius_prefix_norm_le_maximum le_rfl t) 2)).trans hb
    · exact ((((differentiable_moebiusPoly _).continuous.comp continuous_linePoint).norm).pow 2).intervalIntegrable _ _
    · exact ((continuous_moebiusPrefixMaximum _).pow 2).intervalIntegrable _ _

#print axioms moebius_prefix_maximum_iff_taper_bound
#print axioms maximal_moebius_moment_upper
#print axioms zetaZeroWidth_iff_cofinal_maximal_moebius_slope

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
