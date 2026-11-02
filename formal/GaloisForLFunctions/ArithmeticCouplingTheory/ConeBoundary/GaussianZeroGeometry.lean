import GaloisForLFunctions.RHTower.ZetaZeroCountUpperBound

/-!
# Geometry of actual zeros for Gaussian clock filters

Local finiteness isolates each fixed zero from every other zero. The actual
zero-count bound gives at most `C n^5` distinct zeros below height `n^4`.
These two bounds control the number and normalization of finite clock factors.
-/

open Complex Finset
open Zeta23
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary

/-- Local finiteness gives each fixed actual zero a positive distance from every other zero. -/
lemma exists_zeta_fixed_target_radius (ρ₀ : zetaZeroConfig.carrier) :
    ∃ r : ℝ, 0 < r ∧ ∀ ρ : zetaZeroConfig.carrier,
      ρ ≠ ρ₀ → r ≤ ‖(ρ:ℂ)-(ρ₀:ℂ)‖ := by
  classical
  let S := (zetaZeroConfig.finite_window ((ρ₀:ℂ).im-2) ((ρ₀:ℂ).im+2)).toFinset.erase (ρ₀:ℂ)
  have hpos : ∀ z ∈ S, 0 < ‖z-(ρ₀:ℂ)‖ := by
    intro z hz
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (mem_erase.mp hz).1)
  have hfinite : ∃ r : ℝ, 0 < r ∧ ∀ z ∈ S, r ≤ ‖z-(ρ₀:ℂ)‖ := by
    rcases S.eq_empty_or_nonempty with he | hn
    · exact ⟨1,zero_lt_one,by intro z hz; simp [he] at hz⟩
    · exact ⟨S.inf' hn (fun z => ‖z-(ρ₀:ℂ)‖),
        (lt_inf'_iff hn).mpr hpos,fun z hz => inf'_le _ hz⟩
  obtain ⟨r,hr,hlower⟩ := hfinite
  refine ⟨min r 1,lt_min hr zero_lt_one,?_⟩
  intro ρ hne
  by_cases hdist : ‖(ρ:ℂ)-(ρ₀:ℂ)‖ < 1
  · have him := (Complex.abs_im_le_norm ((ρ:ℂ)-(ρ₀:ℂ))).trans_lt hdist
    rw [Complex.sub_im,abs_lt] at him
    have hmem : (ρ:ℂ) ∈ S := mem_erase.mpr ⟨by exact fun he => hne (Subtype.ext he),
      (Set.Finite.mem_toFinset _).mpr ⟨ρ.property,by linarith only [him.1],by linarith only [him.2]⟩⟩
    exact (min_le_left r 1).trans (hlower _ hmem)
  · exact (min_le_right r 1).trans (le_of_not_gt hdist)

/-- The actual distinct zero count below `n^4` grows at most as `n^5`.
This coarse integral-power bound suffices for Gaussian clock interpolation. -/
theorem exists_zeta_fourth_cutoff_count :
    ∃ C R : ℝ, 0 < C ∧ 1 ≤ R ∧ ∀ n : ℕ, R ≤ (n:ℝ) →
      ((RHTower.lowZeros ((n:ℝ)^4)).ncard:ℝ) ≤ C*(n:ℝ)^5 := by
  obtain ⟨B,R,hB,hR,hupper⟩ := RHTower.zeroCount_upper
  obtain ⟨c₀,hcard⟩ := RHTower.ncard_lowZeros_le
  refine ⟨9+32*B+(c₀:ℝ),R,by positivity,by linarith only [hR],?_⟩
  intro n hn
  have hn1 : 1 ≤ (n:ℝ) := by linarith only [hn,hR]
  have hn0 : 0 < (n:ℝ) := zero_lt_one.trans_le hn1
  have hnp : (n:ℝ) ≤ (n:ℝ)^4 := by
    calc
      (n:ℝ) = (n:ℝ)*1 := (mul_one _).symm
      _ ≤ (n:ℝ)*(n:ℝ)^3 := mul_le_mul_of_nonneg_left (one_le_pow₀ hn1) hn0.le
      _ = _ := by ring
  have hT0 : 0 < (n:ℝ)^4 := pow_pos hn0 4
  have hlog : 0 ≤ Real.log ((n:ℝ)^4) := Real.log_nonneg (one_le_pow₀ hn1)
  have hlogn : Real.log (n:ℝ) ≤ (n:ℝ) := (Real.log_le_sub_one_of_pos hn0).trans (by linarith)
  have hlogT : Real.log ((n:ℝ)^4) ≤ 4*(n:ℝ) := by
    rw [Real.log_pow]
    exact mul_le_mul_of_nonneg_left hlogn (by norm_num)
  have hmain : RHTower.zeroCountMain ((n:ℝ)^4) ≤ (n:ℝ)^4*Real.log ((n:ℝ)^4) := by
    have hpi : 1 ≤ 2*Real.pi := by linarith only [Real.pi_gt_three]
    have hdiv : (n:ℝ)^4/(2*Real.pi) ≤ (n:ℝ)^4 := div_le_self hT0.le hpi
    have hlogdiv : Real.log ((n:ℝ)^4/(2*Real.pi))-1 ≤ Real.log ((n:ℝ)^4) := by
      have hh := Real.log_le_log (div_pos hT0 (by positivity)) hdiv
      linarith only [hh]
    exact (mul_le_mul_of_nonneg_left hlogdiv (div_nonneg hT0.le (by positivity))).trans
      (mul_le_mul_of_nonneg_right hdiv hlog)
  have hn2 : (n:ℝ)^2 ≤ (n:ℝ)^5 := by
    calc
      (n:ℝ)^2 = (n:ℝ)^2*1 := (mul_one _).symm
      _ ≤ (n:ℝ)^2*(n:ℝ)^3 := mul_le_mul_of_nonneg_left (one_le_pow₀ hn1) (sq_nonneg _)
      _ = _ := by ring
  have hlog2 : Real.log ((n:ℝ)^4)^2 ≤ 16*(n:ℝ)^5 := by
    have hh := pow_le_pow_left₀ hlog hlogT 2
    have hp := mul_le_mul_of_nonneg_left hn2 (show (0:ℝ) ≤ 16 by norm_num)
    nlinarith only [hh,hp]
  have hN := hupper ((n:ℝ)^4) (hn.trans hnp)
  have hfirst := mul_le_mul_of_nonneg_left hlogT (pow_nonneg hn0.le 4)
  have hsecond := mul_le_mul_of_nonneg_left hlog2 hB
  have hcount := hcard ((n:ℝ)^4) hT0.le
  have hcountR : ((RHTower.lowZeros ((n:ℝ)^4)).ncard:ℝ) ≤
      2*(zetaZeroConfig.N 0 ((n:ℝ)^4):ℝ)+(c₀:ℝ) := by exact_mod_cast hcount
  have hc := mul_le_mul_of_nonneg_left (one_le_pow₀ hn1 (n := 5)) (Nat.cast_nonneg c₀ : (0:ℝ) ≤ c₀)
  nlinarith only [hcountR,hN,hmain,hfirst,hsecond,hc,pow_pos hn0 5]

#print axioms exists_zeta_fixed_target_radius
#print axioms exists_zeta_fourth_cutoff_count
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary
