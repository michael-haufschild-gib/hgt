import GaloisForLFunctions.RHTower.LiClockPairedEtaCompletionMoments
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
/-!
# Entire clock of the actual Gamma and dyadic completion

The literal completed source contour equals the complete residual Gamma and
dyadic hyperbolic kernel at every complex clock. Square-summable reciprocal
frequencies justify the full source-by-order interchange and local uniform
convergence. Every selected completion coefficient is real and positive.
The first remaining Gamma atom dominates the entire dyadic lattice, giving
the exact two-rate lower bound and its positive surviving hyperbolic margin.
-/



open Complex Filter Topology
noncomputable section
namespace GaloisForLFunctions

/-- Odd hyperbolic Taylor term with the reciprocal-frequency atom kept explicit. -/
def liClockCompletionHyperbolicTaylorTerm {α : Type*} (β : α → ℂ)
    (t : ℂ) (q : α) (j : ℕ) : ℂ :=
  β q ^ (2 * j + 2) * t ^ (2 * j + 1) / ((2 * j + 1).factorial : ℂ)

/-- Every atom retains the exact odd factorial expansion. -/
theorem hasSum_liClockCompletionHyperbolicTaylorTerm {α : Type*}
    (β : α → ℂ) (t : ℂ) (q : α) :
    HasSum (liClockCompletionHyperbolicTaylorTerm β t q)
      (β q * Complex.sinh (t * β q)) := by
  have hterm (j : ℕ) : liClockCompletionHyperbolicTaylorTerm β t q j =
      β q * ((t * β q) ^ (2 * j + 1) / ((2 * j + 1).factorial : ℂ)) := by
    unfold liClockCompletionHyperbolicTaylorTerm
    rw [show 2 * j + 2 = (2 * j + 1) + 1 by omega, pow_succ, mul_pow]
    ring
  change HasSum (fun j : ℕ => liClockCompletionHyperbolicTaylorTerm β t q j) _
  simp_rw [hterm]
  exact (Complex.hasSum_sinh (t * β q)).mul_left (β q)

/-- A compact-clock envelope separates the square-summable source from Taylor order. -/
theorem norm_liClockCompletionHyperbolicTaylorTerm_le {α : Type*}
    (β : α → ℂ) (t : ℂ) (q : α) (j : ℕ) {T : ℝ}
    (hb : ‖β q‖ ≤ 1) (ht : ‖t‖ ≤ T) :
    ‖liClockCompletionHyperbolicTaylorTerm β t q j‖ ≤
      ‖β q‖ ^ 2 * (T ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) := by
  have hp : ‖β q‖ ^ (2 * j) ≤ 1 := pow_le_one₀ (norm_nonneg _) hb
  have hT : 0 ≤ T := (norm_nonneg t).trans ht
  unfold liClockCompletionHyperbolicTaylorTerm
  simp only [norm_div, norm_mul, norm_pow, Complex.norm_natCast]
  rw [pow_add]
  calc
    (‖β q‖ ^ (2 * j) * ‖β q‖ ^ 2) * ‖t‖ ^ (2 * j + 1) /
        ((2 * j + 1).factorial : ℝ) ≤
      (1 * ‖β q‖ ^ 2) * T ^ (2 * j + 1) /
        ((2 * j + 1).factorial : ℝ) := by gcongr
    _ = _ := by ring

/-- Uniform norm envelope for a single atom on any closed clock disk. -/
theorem norm_liClockCompletionHyperbolicAtom_le {α : Type*}
    (β : α → ℂ) (t : ℂ) (q : α) {T : ℝ}
    (hb : ‖β q‖ ≤ 1) (ht : ‖t‖ ≤ T) :
    ‖β q * Complex.sinh (t * β q)‖ ≤ ‖β q‖ ^ 2 * Real.sinh T := by
  have hT : 0 ≤ T := (norm_nonneg t).trans ht
  have hm := (Real.hasSum_sinh T).summable.mul_left (‖β q‖ ^ 2)
  have hn : Summable (fun j => ‖liClockCompletionHyperbolicTaylorTerm β t q j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => norm_liClockCompletionHyperbolicTaylorTerm_le β t q j hb ht) hm
  calc
    ‖β q * Complex.sinh (t * β q)‖ =
        ‖∑' j : ℕ, liClockCompletionHyperbolicTaylorTerm β t q j‖ := by
      rw [(hasSum_liClockCompletionHyperbolicTaylorTerm β t q).tsum_eq]
    _ ≤ ∑' j : ℕ, ‖liClockCompletionHyperbolicTaylorTerm β t q j‖ :=
      norm_tsum_le_tsum_norm hn
    _ ≤ ∑' j : ℕ, ‖β q‖ ^ 2 * (T ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) :=
      hn.tsum_le_tsum (fun j => norm_liClockCompletionHyperbolicTaylorTerm_le β t q j hb ht) hm
    _ = _ := by rw [tsum_mul_left, (Real.hasSum_sinh T).tsum_eq]

/-- Absolute convergence holds on the entire source-by-order product. -/
theorem summable_norm_liClockCompletionHyperbolicTaylorTerm {α : Type*}
    (β : α → ℂ) (hs : Summable (fun q => ‖β q‖ ^ 2))
    (hb : ∀ q, ‖β q‖ ≤ 1) (t : ℂ) :
    Summable (fun p : α × ℕ => ‖liClockCompletionHyperbolicTaylorTerm β t p.1 p.2‖) := by
  have hj := (Real.hasSum_sinh ‖t‖).summable
  have hmajor := hs.mul_of_nonneg hj (fun q => by positivity)
    (fun j => by positivity)
  apply Summable.of_nonneg_of_le (fun p => norm_nonneg _) _ hmajor
  intro p
  exact norm_liClockCompletionHyperbolicTaylorTerm_le β t p.1 p.2 (hb p.1) le_rfl

/-- The full hyperbolic atom sum is absolutely convergent. -/
theorem summable_norm_liClockCompletionHyperbolicAtom {α : Type*}
    (β : α → ℂ) (hs : Summable (fun q => ‖β q‖ ^ 2))
    (hb : ∀ q, ‖β q‖ ≤ 1) (t : ℂ) :
    Summable (fun q => ‖β q * Complex.sinh (t * β q)‖) := by
  have hd := summable_norm_liClockCompletionHyperbolicTaylorTerm β hs hb t
  apply Summable.of_nonneg_of_le (fun q => norm_nonneg _) _ hd.prod
  intro q
  rw [← (hasSum_liClockCompletionHyperbolicTaylorTerm β t q).tsum_eq]
  exact norm_tsum_le_tsum_norm (hd.prod_factor q)

/-- Uniform complete-source norm envelope on every closed clock disk. -/
theorem norm_liClockCompletionHyperbolic_tsum_le {α : Type*}
    (β : α → ℂ) (hs : Summable (fun q => ‖β q‖ ^ 2))
    (hb : ∀ q, ‖β q‖ ≤ 1) (t : ℂ) {T : ℝ} (ht : ‖t‖ ≤ T) :
    ‖∑' q : α, β q * Complex.sinh (t * β q)‖ ≤
      (∑' q : α, ‖β q‖ ^ 2) * Real.sinh T := by
  have hn := summable_norm_liClockCompletionHyperbolicAtom β hs hb t
  calc
    _ ≤ ∑' q : α, ‖β q * Complex.sinh (t * β q)‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' q : α, ‖β q‖ ^ 2 * Real.sinh T :=
      hn.tsum_le_tsum (fun q => norm_liClockCompletionHyperbolicAtom_le β t q (hb q) ht)
        (hs.mul_right (Real.sinh T))
    _ = _ := tsum_mul_right

/-- Exact coefficient/atom interchange, preserving every index of the source. -/
theorem liClockCompletionHyperbolic_tsum_eq {α : Type*}
    (β : α → ℂ) (hs : Summable (fun q => ‖β q‖ ^ 2))
    (hb : ∀ q, ‖β q‖ ≤ 1) (t : ℂ) :
    (∑' j : ℕ, (∑' q : α, β q ^ (2 * j + 2)) * t ^ (2 * j + 1) /
      ((2 * j + 1).factorial : ℂ)) =
      ∑' q : α, β q * Complex.sinh (t * β q) := by
  have hcomm : (∑' j : ℕ, ∑' q : α, liClockCompletionHyperbolicTaylorTerm β t q j) =
      ∑' q : α, ∑' j : ℕ, liClockCompletionHyperbolicTaylorTerm β t q j :=
    Summable.tsum_comm (f := fun q j => liClockCompletionHyperbolicTaylorTerm β t q j)
      (summable_norm_liClockCompletionHyperbolicTaylorTerm β hs hb t).of_norm
  calc
    _ = ∑' j : ℕ, ∑' q : α, liClockCompletionHyperbolicTaylorTerm β t q j := by
      congr 1
      funext j
      simp only [liClockCompletionHyperbolicTaylorTerm, tsum_div_const, tsum_mul_right]
    _ = _ := by
      rw [hcomm]
      exact tsum_congr (fun q => (hasSum_liClockCompletionHyperbolicTaylorTerm β t q).tsum_eq)

end GaloisForLFunctions



open Complex Filter Topology
noncomputable section
namespace GaloisForLFunctions

private theorem completion_hasSum_primary (t : ℝ) :
    HasSum (fun j : ℕ => (4 / 25 : ℝ) ^ (j + 1) * t ^ (2 * j + 1) /
      ((2 * j + 1).factorial : ℝ)) ((2 / 5) * Real.sinh ((2 / 5) * t)) := by
  convert! (Real.hasSum_sinh ((2 / 5) * t)).mul_left (2 / 5) using 1
  funext j
  rw [show (4 / 25 : ℝ) = (2 / 5) ^ 2 by norm_num, ← pow_mul,
    show 2 * (j + 1) = (2 * j + 1) + 1 by omega, pow_succ, mul_pow]
  ring_nf

private theorem completion_hasSum_subtracted (t : ℝ) :
    HasSum (fun j : ℕ => 3 * (1 / 64 : ℝ) ^ (j + 1) * t ^ (2 * j + 1) /
      ((2 * j + 1).factorial : ℝ)) ((3 / 8) * Real.sinh (t / 8)) := by
  convert! (Real.hasSum_sinh ((1 / 8) * t)).mul_left (3 / 8) using 1
  · funext j
    rw [show (1 / 64 : ℝ) = (1 / 8) ^ 2 by norm_num, ← pow_mul,
      show 2 * (j + 1) = (2 * j + 1) + 1 by omega, pow_succ, mul_pow]
    ring_nf
  · congr 1
    ring_nf

private theorem completion_hasSum_lower (t : ℝ) :
    HasSum (fun j : ℕ => ((4 / 25 : ℝ) ^ (j + 1) - 3 * (1 / 64 : ℝ) ^ (j + 1)) *
      t ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ))
      ((2 / 5) * Real.sinh ((2 / 5) * t) - (3 / 8) * Real.sinh (t / 8)) := by
  convert! (completion_hasSum_primary t).sub (completion_hasSum_subtracted t) using 1
  funext j
  ring_nf

/-- Coefficient lower bounds give the exact two-rate hyperbolic comparison. -/
theorem liClockCompletion_sinh_lower_le_tsum (c : ℕ → ℝ)
    (hj : ∀ j, (4 / 25 : ℝ) ^ (j + 1) - 3 * (1 / 64 : ℝ) ^ (j + 1) ≤ c j)
    {t : ℝ} (ht : 0 ≤ t)
    (hs : Summable (fun j : ℕ => c j * t ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ))) :
    (2 / 5) * Real.sinh ((2 / 5) * t) - (3 / 8) * Real.sinh (t / 8) ≤
      ∑' j : ℕ, c j * t ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ) := by
  rw [← (completion_hasSum_lower t).tsum_eq]
  apply (completion_hasSum_lower t).summable.tsum_le_tsum _ hs
  intro j
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hj j) (pow_nonneg ht _)) (by positivity)

/-- The two-rate lower clock has an exact strictly positive surviving margin. -/
theorem liClockCompletion_sinh_margin {t : ℝ} (ht : 0 ≤ t) :
    (181 / 640 : ℝ) * Real.sinh ((2 / 5) * t) ≤
      (2 / 5) * Real.sinh ((2 / 5) * t) - (3 / 8) * Real.sinh (t / 8) := by
  have hratio : Real.sinh (t / 8) ≤ (5 / 16 : ℝ) * Real.sinh ((2 / 5) * t) := by
    have hs := (Real.hasSum_sinh ((2 / 5) * t)).summable.mul_left (5 / 16)
    calc
      Real.sinh (t / 8) = ∑' j : ℕ, (t / 8) ^ (2 * j + 1) /
          ((2 * j + 1).factorial : ℝ) := (Real.hasSum_sinh (t / 8)).tsum_eq.symm
      _ ≤ ∑' j : ℕ, (5 / 16 : ℝ) * (((2 / 5) * t) ^ (2 * j + 1) /
          ((2 * j + 1).factorial : ℝ)) := by
        apply (Real.hasSum_sinh (t / 8)).summable.tsum_le_tsum _ hs
        intro j
        have hp : (5 / 16 : ℝ) ^ (2 * j) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        have hodd : (5 / 16 : ℝ) ^ (2 * j + 1) ≤ 5 / 16 := by
          rw [pow_succ]
          nlinarith
        rw [show t / 8 = (5 / 16 : ℝ) * ((2 / 5) * t) by ring_nf, mul_pow]
        have htp : 0 ≤ ((2 / 5 : ℝ) * t) ^ (2 * j + 1) := by positivity
        have hbound := mul_le_mul_of_nonneg_right hodd htp
        simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hbound
          (show 0 ≤ ((2 * j + 1).factorial : ℝ) by positivity)
      _ = _ := by rw [tsum_mul_left, (Real.hasSum_sinh ((2 / 5) * t)).tsum_eq]
  nlinarith

/-- The completed clock is strictly positive at every positive real clock. -/
theorem liClockCompletion_tsum_pos (c : ℕ → ℝ)
    (hj : ∀ j, (4 / 25 : ℝ) ^ (j + 1) - 3 * (1 / 64 : ℝ) ^ (j + 1) ≤ c j)
    {t : ℝ} (ht : 0 < t)
    (hs : Summable (fun j : ℕ => c j * t ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ))) :
    0 < ∑' j : ℕ, c j * t ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ) := by
  have hpos : 0 < (181 / 640 : ℝ) * Real.sinh ((2 / 5) * t) :=
    mul_pos (by norm_num) (Real.sinh_pos_iff.mpr (by positivity))
  exact hpos.trans_le ((liClockCompletion_sinh_margin ht.le).trans
    (liClockCompletion_sinh_lower_le_tsum c hj ht.le hs))

end GaloisForLFunctions

open GaloisForLFunctions Complex Set Filter Topology RiemannGaussian
open scoped ComplexConjugate
namespace RHTower
noncomputable section

def liClockPairedEtaCompletionClockTerm (t : ℂ) (j : ℕ) : ℂ :=
  liClockPairedEtaCompletionMoment j*t^(2*j+1)/((2*j+1).factorial:ℂ)

private theorem completion_raw_term_eq (t : ℂ) (j : ℕ) :
    liClockCentralTraceSineContourTerm liClockPairedEtaCompletionSourceTrace t j =
      -liClockPairedEtaCompletionClockTerm t j := by
  unfold liClockCentralTraceSineContourTerm liClockPairedEtaCompletionClockTerm
  rw [iteratedDeriv_liClockPairedEtaCompletionSourceTrace_odd]
  have hfac : ((2*j+1).factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*j+1)
  have hsign : (-1:ℂ)^j*(-1:ℂ)^(j+1) = -1 := by
    rw [pow_succ,← mul_assoc,← mul_pow]
    norm_num
  have hs : (-1:ℂ)^j*((-1:ℂ)^(j+1)*((2*j+1).factorial:ℂ)*liClockPairedEtaCompletionMoment j) =
      -((2*j+1).factorial:ℂ)*liClockPairedEtaCompletionMoment j := by
    calc
      _ = ((-1:ℂ)^j*(-1:ℂ)^(j+1))*((2*j+1).factorial:ℂ)*liClockPairedEtaCompletionMoment j := by ring
      _ = _ := by rw [hsign]; ring
  rw [hs]
  field_simp [hfac]

theorem summable_norm_liClockPairedEtaCompletionClockTerm (t : ℂ) :
    Summable (fun j : ℕ => ‖liClockPairedEtaCompletionClockTerm t j‖) := by
  have h := summable_norm_liClockCentralTraceSineContourTerm
    (r := 1/4) (by norm_num) (diffContOnCl_liClockPairedEtaCompletionSourceTrace (by norm_num)) t
  simpa only [completion_raw_term_eq,norm_neg] using h

theorem liClockPairedEtaCompletionClockResponse_eq_tsum {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) (t : ℂ) :
    liClockPairedEtaCompletionClockResponse r t = ∑' j : ℕ,liClockPairedEtaCompletionClockTerm t j := by
  unfold liClockPairedEtaCompletionClockResponse
  rw [liClockCentralTraceSineContour_eq_neg_tsum hr
    (diffContOnCl_liClockPairedEtaCompletionSourceTrace hrhalf)]
  simp_rw [completion_raw_term_eq]
  rw [tsum_neg,neg_neg]

def liClockPairedEtaCompletionKernel (t : ℂ) : ℂ :=
  (∑' n : ℕ, (liClockPairedEtaGammaReciprocal n:ℂ)*
    Complex.sinh (t*(liClockPairedEtaGammaReciprocal n:ℂ)))+
  ∑' k : ℤ,liClockPairedEtaDyadicReciprocal k*Complex.sinh (t*liClockPairedEtaDyadicReciprocal k)

theorem liClockPairedEtaCompletionKernel_eq_tsum_sinh_div (t : ℂ) :
    liClockPairedEtaCompletionKernel t =
      (∑' n : ℕ,Complex.sinh (t/(2*(n:ℂ)+5/2))/(2*(n:ℂ)+5/2))+
      ∑' k : ℤ,if k=0 then 0 else
        Complex.sinh (t/(1/2+2*(Real.pi:ℂ)*I*(k:ℂ)/(Real.log 2:ℂ)))/
          (1/2+2*(Real.pi:ℂ)*I*(k:ℂ)/(Real.log 2:ℂ)) := by
  unfold liClockPairedEtaCompletionKernel
  congr 1
  · apply tsum_congr
    intro n
    unfold liClockPairedEtaGammaReciprocal
    push_cast
    simp only [div_eq_mul_inv]
    ring
  · apply tsum_congr
    intro k
    by_cases hk : k=0
    · subst k; simp [liClockPairedEtaDyadicReciprocal]
    · simp only [liClockPairedEtaDyadicReciprocal,if_neg hk,div_eq_mul_inv]
      ring

theorem liClockPairedEtaDyadicReciprocal_conj (k : ℤ) :
    liClockPairedEtaDyadicReciprocal (-k) = conj (liClockPairedEtaDyadicReciprocal k) := by
  by_cases hk : k=0
  · subst k; simp [liClockPairedEtaDyadicReciprocal]
  · have hn : -k≠0 := neg_ne_zero.mpr hk
    rw [liClockPairedEtaDyadicReciprocal,if_neg hn,liClockPairedEtaDyadicReciprocal,if_neg hk,map_inv₀]
    congr 1
    simp only [map_add,map_div₀,map_mul,map_one,map_ofNat,Complex.conj_ofReal,Complex.conj_I,Int.cast_neg,
      map_intCast]
    ring

theorem liClockPairedEtaCompletionMoment_im_eq_zero (j : ℕ) :
    (liClockPairedEtaCompletionMoment j).im = 0 := by
  have hd : conj (∑' k : ℤ,liClockPairedEtaDyadicReciprocal k^(2*j+2)) =
      ∑' k : ℤ,liClockPairedEtaDyadicReciprocal k^(2*j+2) := by
    rw [Complex.conj_tsum]
    simp_rw [map_pow,← liClockPairedEtaDyadicReciprocal_conj]
    simpa only [Equiv.neg_apply] using
      (Equiv.neg ℤ).tsum_eq (fun k : ℤ => liClockPairedEtaDyadicReciprocal k^(2*j+2))
  apply Complex.conj_eq_iff_im.mp
  unfold liClockPairedEtaCompletionMoment
  rw [map_add,Complex.conj_ofReal,hd]

theorem liClockPairedEtaCompletionMoment_re_ge_margin (j : ℕ) :
    (181/1600:ℝ)*(4/25:ℝ)^j ≤ (liClockPairedEtaCompletionMoment j).re := by
  have hp : (1/64:ℝ)^j ≤ (4/25:ℝ)^j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
  have hh := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤3/64)
  have hl := liClockPairedEtaCompletionMoment_re_lower j
  rw [pow_succ,pow_succ] at hl
  nlinarith

theorem liClockPairedEtaCompletionMoment_re_pos (j : ℕ) :
    0 < (liClockPairedEtaCompletionMoment j).re := by
  exact (mul_pos (by norm_num : (0:ℝ)<181/1600) (pow_pos (by norm_num) j)).trans_le
    (liClockPairedEtaCompletionMoment_re_ge_margin j)

private theorem gamma_complex_square_summable :
    Summable (fun n : ℕ => ‖(liClockPairedEtaGammaReciprocal n:ℂ)‖^2) := by
  simpa only [Complex.norm_real,Real.norm_eq_abs,sq_abs] using summable_liClockPairedEtaGammaReciprocal_square

private theorem gamma_complex_norm_le_one (n : ℕ) :
    ‖(liClockPairedEtaGammaReciprocal n:ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (liClockPairedEtaGammaReciprocal_nonneg n)]
  exact (liClockPairedEtaGammaReciprocal_le_two_fifths n).trans (by norm_num)

private theorem dyadic_norm_le_one (k : ℤ) : ‖liClockPairedEtaDyadicReciprocal k‖ ≤ 1 := by
  nlinarith [liClockPairedEtaDyadicReciprocal_norm_sq_le_one_sixtyfourth k,norm_nonneg (liClockPairedEtaDyadicReciprocal k)]

theorem summable_norm_liClockPairedEtaCompletionKernel_gamma (t : ℂ) :
    Summable (fun n : ℕ => ‖(liClockPairedEtaGammaReciprocal n:ℂ)*
      Complex.sinh (t*(liClockPairedEtaGammaReciprocal n:ℂ))‖) :=
  summable_norm_liClockCompletionHyperbolicAtom (fun n => (liClockPairedEtaGammaReciprocal n:ℂ))
    gamma_complex_square_summable gamma_complex_norm_le_one t

theorem summable_norm_liClockPairedEtaCompletionKernel_dyadic (t : ℂ) :
    Summable (fun k : ℤ => ‖liClockPairedEtaDyadicReciprocal k*
      Complex.sinh (t*liClockPairedEtaDyadicReciprocal k)‖) :=
  summable_norm_liClockCompletionHyperbolicAtom liClockPairedEtaDyadicReciprocal
    summable_liClockPairedEtaDyadicReciprocal_norm_sq dyadic_norm_le_one t

private theorem hyperbolic_summableLocallyUniformlyOn {α : Type*} (β : α → ℂ)
    (hs : Summable (fun q => ‖β q‖^2)) (hb : ∀q,‖β q‖≤1) :
    SummableLocallyUniformlyOn (fun q t => β q*Complex.sinh (t*β q)) (univ : Set ℂ) := by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_univ
  intro K _ hK
  obtain ⟨T,hT⟩ := hK.bddAbove_image continuous_norm.continuousOn
  let M : ℝ := max T 0
  refine ⟨fun q => ‖β q‖^2*Real.sinh M,hs.mul_right (Real.sinh M),?_⟩
  intro q t ht
  exact norm_liClockCompletionHyperbolicAtom_le β t q (hb q)
    ((hT ⟨t,ht,rfl⟩).trans (le_max_left _ _))

theorem summableLocallyUniformlyOn_liClockPairedEtaCompletionKernel_gamma :
    SummableLocallyUniformlyOn (fun n t => (liClockPairedEtaGammaReciprocal n:ℂ)*
      Complex.sinh (t*(liClockPairedEtaGammaReciprocal n:ℂ))) (univ : Set ℂ) :=
  hyperbolic_summableLocallyUniformlyOn (fun n => (liClockPairedEtaGammaReciprocal n:ℂ))
    gamma_complex_square_summable gamma_complex_norm_le_one

theorem summableLocallyUniformlyOn_liClockPairedEtaCompletionKernel_dyadic :
    SummableLocallyUniformlyOn (fun k t => liClockPairedEtaDyadicReciprocal k*
      Complex.sinh (t*liClockPairedEtaDyadicReciprocal k)) (univ : Set ℂ) :=
  hyperbolic_summableLocallyUniformlyOn liClockPairedEtaDyadicReciprocal
    summable_liClockPairedEtaDyadicReciprocal_norm_sq dyadic_norm_le_one

private theorem gamma_complex_moment (j : ℕ) :
    (∑' n : ℕ,(liClockPairedEtaGammaReciprocal n:ℂ)^(2*j+2)) =
      (((∑' n : ℕ,liClockPairedEtaGammaReciprocal n^(2*j+2)):ℝ):ℂ) := by
  rw [Complex.ofReal_tsum]
  simp only [Complex.ofReal_pow]

private theorem summable_hyperbolic_coefficient {α : Type*} (β : α → ℂ)
    (hs : Summable (fun q => ‖β q‖^2)) (hb : ∀q,‖β q‖≤1) (t : ℂ) :
    Summable (fun j : ℕ => (∑' q : α,β q^(2*j+2))*t^(2*j+1)/((2*j+1).factorial:ℂ)) := by
  have hh := ((summable_norm_liClockCompletionHyperbolicTaylorTerm β hs hb t).of_norm.comp_injective
    Prod.swap_injective).prod
  apply hh.congr
  intro j
  simp only [Function.comp_apply,Prod.swap_prod_mk,liClockCompletionHyperbolicTaylorTerm,
    tsum_div_const,tsum_mul_right]

theorem liClockPairedEtaCompletionClockResponse_eq_kernel {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) (t : ℂ) :
    liClockPairedEtaCompletionClockResponse r t = liClockPairedEtaCompletionKernel t := by
  have hg := summable_hyperbolic_coefficient (fun n => (liClockPairedEtaGammaReciprocal n:ℂ))
    gamma_complex_square_summable gamma_complex_norm_le_one t
  have hd := summable_hyperbolic_coefficient liClockPairedEtaDyadicReciprocal
    summable_liClockPairedEtaDyadicReciprocal_norm_sq dyadic_norm_le_one t
  rw [liClockPairedEtaCompletionClockResponse_eq_tsum hr hrhalf]
  have ht : liClockPairedEtaCompletionClockTerm t = fun j =>
      (∑' n : ℕ,(liClockPairedEtaGammaReciprocal n:ℂ)^(2*j+2))*t^(2*j+1)/((2*j+1).factorial:ℂ)+
      (∑' k : ℤ,liClockPairedEtaDyadicReciprocal k^(2*j+2))*t^(2*j+1)/((2*j+1).factorial:ℂ) := by
    funext j
    unfold liClockPairedEtaCompletionClockTerm liClockPairedEtaCompletionMoment
    rw [gamma_complex_moment]
    ring
  rw [ht,Summable.tsum_add hg hd,
    liClockCompletionHyperbolic_tsum_eq (fun n => (liClockPairedEtaGammaReciprocal n:ℂ))
      gamma_complex_square_summable gamma_complex_norm_le_one t,
    liClockCompletionHyperbolic_tsum_eq liClockPairedEtaDyadicReciprocal
      summable_liClockPairedEtaDyadicReciprocal_norm_sq dyadic_norm_le_one t]
  rfl

private theorem completion_term_re (t : ℝ) (j : ℕ) :
    (liClockPairedEtaCompletionClockTerm (t:ℂ) j).re =
      (liClockPairedEtaCompletionMoment j).re*t^(2*j+1)/((2*j+1).factorial:ℝ) := by
  unfold liClockPairedEtaCompletionClockTerm
  rw [← Complex.ofReal_pow,← Complex.ofReal_natCast,Complex.div_ofReal_re]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

theorem liClockPairedEtaCompletionClockResponse_re_ge_two_sinh {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) {t : ℝ} (ht : 0 ≤ t) :
    (2/5:ℝ)*Real.sinh ((2/5)*t)-(3/8)*Real.sinh (t/8) ≤
      (liClockPairedEtaCompletionClockResponse r (t:ℂ)).re := by
  have hs := ((summable_norm_liClockPairedEtaCompletionClockTerm (t:ℂ)).of_norm.map
    Complex.reCLM Complex.reCLM.continuous).congr (completion_term_re t)
  rw [liClockPairedEtaCompletionClockResponse_eq_tsum hr hrhalf,
    Complex.re_tsum (summable_norm_liClockPairedEtaCompletionClockTerm (t:ℂ)).of_norm]
  simp_rw [completion_term_re]
  exact liClockCompletion_sinh_lower_le_tsum (fun j => (liClockPairedEtaCompletionMoment j).re)
    liClockPairedEtaCompletionMoment_re_lower ht hs

theorem liClockPairedEtaCompletionClockResponse_re_ge_sinh {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) {t : ℝ} (ht : 0 ≤ t) :
    (181/640:ℝ)*Real.sinh ((2/5)*t) ≤ (liClockPairedEtaCompletionClockResponse r (t:ℂ)).re :=
  (liClockCompletion_sinh_margin ht).trans (liClockPairedEtaCompletionClockResponse_re_ge_two_sinh hr hrhalf ht)

theorem liClockPairedEtaCompletionClockResponse_re_pos {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) {t : ℝ} (ht : 0 < t) :
    0 < (liClockPairedEtaCompletionClockResponse r (t:ℂ)).re := by
  exact (mul_pos (by norm_num : (0:ℝ)<181/640)
    (Real.sinh_pos_iff.mpr (by positivity))).trans_le
      (liClockPairedEtaCompletionClockResponse_re_ge_sinh hr hrhalf ht.le)

theorem liClockPairedEtaCompletionSourceTrace_reflection (z : ℂ) :
    liClockPairedEtaCompletionSourceTrace (-conj z) = -conj (liClockPairedEtaCompletionSourceTrace z) := by
  have hfun : (conj ∘ pairedEtaXiCompletionFactor ∘ conj) = pairedEtaXiCompletionFactor := by
    funext w
    simp [Function.comp_apply,pairedEtaXiCompletionFactor_conj]
  have hd := deriv_conj_conj (f := pairedEtaXiCompletionFactor)
  rw [hfun] at hd
  have hderiv (s : ℂ) : deriv pairedEtaXiCompletionFactor (conj s) = conj (deriv pairedEtaXiCompletionFactor s) := by
    have h := congrFun hd (conj s)
    simpa only [Function.comp_apply,Complex.conj_conj] using h
  have hQ (s : ℂ) : logDeriv pairedEtaXiCompletionFactor (conj s) = conj (logDeriv pairedEtaXiCompletionFactor s) := by
    rw [logDeriv_apply,logDeriv_apply,hderiv,pairedEtaXiCompletionFactor_conj,map_div₀]
  have hc : (1/2+(-conj z)*I:ℂ) = conj (1/2+z*I) := by
    simp only [map_add,map_div₀,map_one,map_ofNat,map_mul,Complex.conj_I]
    ring
  unfold liClockPairedEtaCompletionSourceTrace
  rw [hc,hQ]
  simp only [map_mul,Complex.conj_I]
  ring

theorem liClockPairedEtaCompletionClockResponse_im_ofReal_eq_zero {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) (t : ℝ) :
    (liClockPairedEtaCompletionClockResponse r (t:ℂ)).im = 0 :=
  liClockCentralTraceSineContour_im_ofReal_eq_zero hr
    (diffContOnCl_liClockPairedEtaCompletionSourceTrace hrhalf)
      liClockPairedEtaCompletionSourceTrace_reflection t

end
end RHTower
