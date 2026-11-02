import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineHeightCorrection

/-!
# Discrete spline Jacobians and correction parameters

Dual primitives split each real node-motion Jacobian into ordinary and conjugate
Fourier pairings. Integral bounds and grid quadrature give explicit row errors,
uniform in translation. Explicit spacing, radius, node count, and height choices
make these errors small enough for exact finite spline correction.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

/-- The normalized average on a translated equally spaced grid. -/
def splineGridAverage (f : ℝ → ℂ) (a h : ℝ) (n : ℕ) : ℂ :=
  (∑ j : Fin n, f (a+j.val*h))/(n : ℂ)

/-- Normalize a grid quadrature estimate and an integral-center estimate together. -/
lemma norm_splineGridAverage_sub_center_le {f : ℝ → ℂ} {a h A K : ℝ} {n : ℕ} {z : ℂ}
    (hn : 0 < n) (hh : 0 < h)
    (hcell : ‖(∑ k ∈ range n, h • f (a+k*h))-∫ x in a..(a+n*h), f x‖ ≤ n*K*h^2/2)
    (hmean : ‖(∫ x in a..(a+n*h), f x)-(((n : ℝ)*h : ℝ) : ℂ)*z‖ ≤ A) :
    ‖splineGridAverage f a h n-z‖ ≤ A/((n : ℝ)*h)+K*h/2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hsum : (∑ k ∈ range n, h • f (a+k*h))=
      (h : ℂ)*∑ j : Fin n, f (a+j.val*h) := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [Complex.real_smul]
    rw [mul_sum]
  have he : splineGridAverage f a h n-z=
      (((∑ k ∈ range n, h • f (a+k*h))-(∫ x in a..(a+n*h), f x))+
        ((∫ x in a..(a+n*h), f x)-(((n : ℝ)*h : ℝ) : ℂ)*z))/((n : ℂ)*(h : ℂ)) := by
    rw [splineGridAverage, hsum]
    push_cast
    field_simp [hnC,hhC]
    simp only [mul_comm h]
    ring
  rw [he, norm_div, norm_mul, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hh]
  calc
    _ ≤ ((n : ℝ)*K*h^2/2+A)/((n : ℝ)*h) :=
      div_le_div_of_nonneg_right ((norm_add_le _ _).trans (add_le_add hcell hmean))
        (mul_pos hnR hh).le
    _ = _ := by field_simp [hnR.ne',hh.ne']; ring

lemma norm_grid_spline_pair_self_sub_one_le {δ s h : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    (hh : 0 < h) {n : ℕ} (hn : 0 < n) (a : ℝ) :
    ‖splineGridAverage (fun x => shiftedSplineSlope δ s x*splineDual δ s x) a h n-1‖ ≤
      2*splinePairBoundaryBound δ s/((n : ℝ)*h)+splinePairLipschitzBound δ s s*h/2 := by
  have hm := norm_integral_spline_pair_self_sub_length_le hδ hs a (a+n*h)
  rw [show a+(n : ℝ)*h-a=(n : ℝ)*h by ring] at hm
  have hm' : ‖(∫ x in a..(a+n*h), shiftedSplineSlope δ s x*splineDual δ s x)-
      (((n : ℝ)*h : ℝ) : ℂ)*(1 : ℂ)‖ ≤ 2*splinePairBoundaryBound δ s := by
    simpa only [mul_one] using hm
  exact norm_splineGridAverage_sub_center_le (f := fun x => shiftedSplineSlope δ s x*splineDual δ s x)
    (z := 1) hn hh (norm_spline_pair_grid_error_le hδ hs s a hh.le n) hm'

lemma norm_grid_spline_pair_le_of_ne {δ s t h : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    (hts : t ≠ s) (hh : 0 < h) {n : ℕ} (hn : 0 < n) (a : ℝ) :
    ‖splineGridAverage (fun x => shiftedSplineSlope δ t x*splineDual δ s x) a h n‖ ≤
      (2*splinePairBoundaryBound δ s+2/|t-s|)/((n : ℝ)*h)+splinePairLipschitzBound δ t s*h/2 := by
  have hm := norm_integral_spline_pair_le_of_ne hδ hs hts a (a+n*h)
  have hm' : ‖(∫ x in a..(a+n*h), shiftedSplineSlope δ t x*splineDual δ s x)-
      (((n : ℝ)*h : ℝ) : ℂ)*(0 : ℂ)‖ ≤ 2*splinePairBoundaryBound δ s+2/|t-s| := by
    simpa only [mul_zero, sub_zero] using hm
  simpa only [sub_zero] using norm_splineGridAverage_sub_center_le
    (f := fun x => shiftedSplineSlope δ t x*splineDual δ s x) (z := 0) hn hh
    (norm_spline_pair_grid_error_le hδ hs t a hh.le n) hm'

lemma norm_grid_spline_conj_pair_le {δ s t h : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    (ht : 0 < t) (hh : 0 < h) {n : ℕ} (hn : 0 < n) (a : ℝ) :
    ‖splineGridAverage (fun x => shiftedSplineSlope δ t x*(starRingEnd ℂ) (splineDual δ s x)) a h n‖ ≤
      (2*splinePairBoundaryBound δ s+
        2*((1+splineRatio δ)^8/(t+s)*(1/(1-splineRatio δ)^8)))/((n : ℝ)*h)+
      splinePairLipschitzBound δ t s*h/2 := by
  have hm := norm_integral_spline_conj_pair_le hδ hs ht a (a+n*h)
  have hm' : ‖(∫ x in a..(a+n*h), shiftedSplineSlope δ t x*(starRingEnd ℂ) (splineDual δ s x))-
      (((n : ℝ)*h : ℝ) : ℂ)*(0 : ℂ)‖ ≤ 2*splinePairBoundaryBound δ s+
      2*((1+splineRatio δ)^8/(t+s)*(1/(1-splineRatio δ)^8)) := by
    simpa only [mul_zero, sub_zero] using hm
  simpa only [sub_zero] using norm_splineGridAverage_sub_center_le
    (f := fun x => shiftedSplineSlope δ t x*(starRingEnd ℂ) (splineDual δ s x)) (z := 0) hn hh
    (norm_spline_conj_pair_grid_error_le hδ hs t a hh.le n) hm'

#print axioms norm_grid_spline_pair_self_sub_one_le
#print axioms norm_grid_spline_pair_le_of_ne
#print axioms norm_grid_spline_conj_pair_le
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
variable {ι : Type*} [Fintype ι]

lemma splineGridAverage_add (f g : ℝ → ℂ) (a h : ℝ) (n : ℕ) :
    splineGridAverage (fun x => f x+g x) a h n=
      splineGridAverage f a h n+splineGridAverage g a h n := by
  simp only [splineGridAverage, sum_add_distrib, add_div]

lemma splineGridAverage_mul_const (f : ℝ → ℂ) (c : ℂ) (a h : ℝ) (n : ℕ) :
    splineGridAverage (fun x => f x*c) a h n=splineGridAverage f a h n*c := by
  simp only [splineGridAverage, ← sum_mul]
  ring

lemma splineGridAverage_sum (f : ι → ℝ → ℂ) (a h : ℝ) (n : ℕ) :
    splineGridAverage (fun x => ∑ i, f i x) a h n=∑ i, splineGridAverage (f i) a h n := by
  unfold splineGridAverage
  rw [sum_comm, sum_div]

lemma norm_splineGridAverage_le {f : ℝ → ℂ} {a h C : ℝ} {n : ℕ} (hn : 0 < n)
    (hf : ∀ j : Fin n, ‖f (a+j.val*h)‖ ≤ C) :
    ‖splineGridAverage f a h n‖ ≤ C := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [splineGridAverage, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hnR).2
  calc
    _ ≤ ∑ j : Fin n, ‖f (a+j.val*h)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, C := sum_le_sum fun j _ => hf j
    _ = _ := by simp [mul_comm]

/-- The real node displacement has ordinary and conjugate complex matrix entries. -/
lemma splineGridAverage_slope_correction (δ : ℝ) (t : ι → ℝ) (y : ι → ℂ)
    (i : ι) (a h : ℝ) (n : ℕ) :
    splineGridAverage (fun x => shiftedSplineSlope δ (t i) x*
        (splineHeightCorrection δ t y x : ℂ)) a h n=
      ∑ j, (splineGridAverage (fun x => shiftedSplineSlope δ (t i) x*splineDual δ (t j) x) a h n*y j+
        splineGridAverage (fun x => shiftedSplineSlope δ (t i) x*
          (starRingEnd ℂ) (splineDual δ (t j) x)) a h n*(starRingEnd ℂ) (y j)) := by
  simp_rw [splineHeightCorrection_complex, mul_sum, mul_add, ← mul_assoc]
  rw [splineGridAverage_sum]
  apply sum_congr rfl
  intro j _
  rw [splineGridAverage_add, splineGridAverage_mul_const, splineGridAverage_mul_const]

lemma norm_splineGridAverage_slope_correction_sub_le [DecidableEq ι] {δ a h : ℝ} {t : ι → ℝ}
    {n : ℕ} {A B : ι → ι → ℝ}
    (hA : ∀ i j, ‖splineGridAverage (fun x => shiftedSplineSlope δ (t i) x*splineDual δ (t j) x) a h n-
      (if i=j then 1 else 0)‖ ≤ A i j)
    (hB : ∀ i j, ‖splineGridAverage (fun x => shiftedSplineSlope δ (t i) x*
      (starRingEnd ℂ) (splineDual δ (t j) x)) a h n‖ ≤ B i j)
    (y : ι → ℂ) (i : ι) :
    ‖splineGridAverage (fun x => shiftedSplineSlope δ (t i) x*
        (splineHeightCorrection δ t y x : ℂ)) a h n-y i‖ ≤
      (∑ j, (A i j+B i j))*‖y‖ := by
  classical
  rw [splineGridAverage_slope_correction]
  have he : (∑ j, (splineGridAverage (fun x => shiftedSplineSlope δ (t i) x*splineDual δ (t j) x) a h n*y j+
        splineGridAverage (fun x => shiftedSplineSlope δ (t i) x*
          (starRingEnd ℂ) (splineDual δ (t j) x)) a h n*(starRingEnd ℂ) (y j)))-y i=
      ∑ j, ((splineGridAverage (fun x => shiftedSplineSlope δ (t i) x*splineDual δ (t j) x) a h n-
        (if i=j then 1 else 0))*y j+
        splineGridAverage (fun x => shiftedSplineSlope δ (t i) x*
          (starRingEnd ℂ) (splineDual δ (t j) x)) a h n*(starRingEnd ℂ) (y j)) := by
    simp only [sub_mul, sub_add, sum_sub_distrib, sum_add_distrib]
    simp
    ring
  rw [he]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ j, (A i j+B i j)*‖y‖ := by
      apply sum_le_sum
      intro j _
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_conj, add_mul]
      exact add_le_add
        (mul_le_mul (hA i j) (norm_le_pi_norm y j) (norm_nonneg _)
          ((norm_nonneg _).trans (hA i j)))
        (mul_le_mul (hB i j) (norm_le_pi_norm y j) (norm_nonneg _)
          ((norm_nonneg _).trans (hB i j)))
    _ = _ := (sum_mul _ _ _).symm

#print axioms norm_splineGridAverage_slope_correction_sub_le
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
variable {ι : Type*} [Fintype ι]

/-- Continuous pairing error in one real Jacobian entry. -/
def splineJacobianEntryBound (δ t s : ℝ) : ℝ :=
  4*splinePairBoundaryBound δ s+2/|t-s|+
    2*((1+splineRatio δ)^8/(t+s)*(1/(1-splineRatio δ)^8))

/-- A row-wise discrete Jacobian estimate, uniform in the grid's translation. -/
theorem norm_spline_discrete_jacobian_defect_le {δ h : ℝ} (hδ : 0 < δ)
    {t : ι → ℝ} (ht : ∀ i, 0 < t i) (hinj : Function.Injective t)
    (hh : 0 < h) {n : ℕ} (hn : 0 < n) (a : ℝ) (y : ι → ℂ) (i : ι) :
    ‖splineGridAverage (fun x => shiftedSplineSlope δ (t i) x*
        (splineHeightCorrection δ t y x : ℂ)) a h n-y i‖ ≤
      ((∑ j, splineJacobianEntryBound δ (t i) (t j))/((n : ℝ)*h)+
        (∑ j, splinePairLipschitzBound δ (t i) (t j))*h)*‖y‖ := by
  classical
  let A : ι → ι → ℝ := fun i j =>
    (2*splinePairBoundaryBound δ (t j)+2/|t i-t j|)/((n : ℝ)*h)+
      splinePairLipschitzBound δ (t i) (t j)*h/2
  let B : ι → ι → ℝ := fun i j =>
    (2*splinePairBoundaryBound δ (t j)+
      2*((1+splineRatio δ)^8/(t i+t j)*(1/(1-splineRatio δ)^8)))/((n : ℝ)*h)+
      splinePairLipschitzBound δ (t i) (t j)*h/2
  have hA (i j : ι) :
      ‖splineGridAverage (fun x => shiftedSplineSlope δ (t i) x*splineDual δ (t j) x) a h n-
        (if i=j then 1 else 0)‖ ≤ A i j := by
    by_cases hij : i=j
    · subst j
      simpa only [A, sub_self, abs_zero, div_zero, add_zero, ite_true] using
        norm_grid_spline_pair_self_sub_one_le hδ (ht i) hh hn a
    · simpa only [A, if_neg hij, sub_zero] using
        norm_grid_spline_pair_le_of_ne hδ (ht j) (fun he => hij (hinj he)) hh hn a
  have hB (i j : ι) :
      ‖splineGridAverage (fun x => shiftedSplineSlope δ (t i) x*
        (starRingEnd ℂ) (splineDual δ (t j) x)) a h n‖ ≤ B i j :=
    norm_grid_spline_conj_pair_le hδ (ht j) (ht i) hh hn a
  refine (norm_splineGridAverage_slope_correction_sub_le hA hB y i).trans_eq ?_
  congr 1
  rw [sum_div, sum_mul, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  dsimp only [A, B, splineJacobianEntryBound]
  ring

#print axioms norm_spline_discrete_jacobian_defect_le
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

/-- Explicit scalar choices balance grid, nonlinear, and inverse-height errors. -/
lemma exists_spline_correction_parameters {δ L η A J P Q G B : ℝ}
    (hδ : 0 < δ) (hL : 0 ≤ L) (hη : 0 < η)
    (hA : 0 ≤ A) (hJ : 0 ≤ J) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hG : 0 ≤ G) (hB : 0 ≤ B) :
    ∃ Λ ρ H₀ : ℝ, ∃ n : ℕ, 0 < Λ ∧ L+8 ≤ Λ ∧ 0 < ρ ∧ 0 < H₀ ∧ 0 < n ∧
      P*ρ ≤ (Real.pi/(2*Λ))/4 ∧
      J*(Real.pi/(2*Λ)) ≤ 1/8 ∧
      A/((n : ℝ)*(Real.pi/(2*Λ))) ≤ 1/8 ∧
      Q*P^2*ρ ≤ 1/8 ∧ 2*Λ*B/(η*n) ≤ ρ/8 ∧
      Λ=1+(L+8)+4*Real.pi*J ∧
      ρ=min ((Real.pi/(2*Λ))/(4*(P+1))) (1/(8*(Q*P^2+1))) ∧
      H₀=1+64*((((n : ℝ)+1)*(Real.pi/(2*Λ))+δ)*G+B)*P+
        64*(((n : ℝ)+1)*(Real.pi/(2*Λ))+δ)*B/ρ ∧
      (n : ℝ) ≤ 2+8*A/(Real.pi/(2*Λ))+16*Λ*B/(η*ρ) ∧
      ∀ H : ℝ, H₀ ≤ H →
        8*((((n : ℝ)+1)*(Real.pi/(2*Λ))+δ)*G+B)*P/H ≤ 1/8 ∧
        8*(((n : ℝ)+1)*(Real.pi/(2*Λ))+δ)*B/H ≤ ρ/8 := by
  let Λ := 1+(L+8)+4*Real.pi*J
  have hΛ : 0 < Λ := by dsimp only [Λ]; positivity
  have hΛL : L+8 ≤ Λ := by
    dsimp only [Λ]
    have hp := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) Real.pi_pos.le) hJ
    linarith only [hp]
  let h := Real.pi/(2*Λ)
  have hh : 0 < h := by dsimp only [h]; positivity
  have hJh : J*h ≤ 1/8 := by
    dsimp only [h]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 2*Λ)).2
    dsimp only [Λ]
    nlinarith only [hL]
  let ρ := min (h/(4*(P+1))) (1/(8*(Q*P^2+1)))
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hdisp : P*ρ ≤ h/4 := by
    have h1 := (le_div_iff₀ (by positivity : 0 < 4*(P+1))).mp (min_le_left (h/(4*(P+1))) (1/(8*(Q*P^2+1))))
    change ρ*(4*(P+1)) ≤ h at h1
    nlinarith only [h1,hρ]
  have hquad : Q*P^2*ρ ≤ 1/8 := by
    have h1 := (le_div_iff₀ (by positivity : 0 < 8*(Q*P^2+1))).mp (min_le_right (h/(4*(P+1))) (1/(8*(Q*P^2+1))))
    change ρ*(8*(Q*P^2+1)) ≤ 1 at h1
    nlinarith only [h1,hρ]
  let n := ⌊1+8*A/h+16*Λ*B/(η*ρ)⌋₊+1
  have hn : 1+8*A/h+16*Λ*B/(η*ρ) < (n : ℝ) := by
    simpa only [n, Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one (1+8*A/h+16*Λ*B/(η*ρ))
  have hnUpper : (n : ℝ) ≤ 2+8*A/h+16*Λ*B/(η*ρ) := by
    have hf := Nat.floor_le (show 0 ≤ 1+8*A/h+16*Λ*B/(η*ρ) by positivity)
    dsimp only [n]
    push_cast
    linarith only [hf]
  have hx : 0 ≤ 8*A/h := by positivity
  have hy : 0 ≤ 16*Λ*B/(η*ρ) := by positivity
  have hnR : (0 : ℝ) < n := by linarith only [hn,hx,hy]
  have hnN : 0 < n := by exact_mod_cast hnR
  have hAn : A/((n : ℝ)*h) ≤ 1/8 := by
    apply (div_le_iff₀ (mul_pos hnR hh)).2
    have hb : 8*A/h ≤ n := by linarith only [hn,hy]
    have hc := (div_le_iff₀ hh).mp hb
    linarith only [hc]
  have hBn : 2*Λ*B/(η*n) ≤ ρ/8 := by
    apply (div_le_iff₀ (mul_pos hη hnR)).2
    have hb : 16*Λ*B/(η*ρ) ≤ n := by linarith only [hn,hx]
    have hc := (div_le_iff₀ (mul_pos hη hρ)).mp hb
    nlinarith only [hc]
  let C := ((n : ℝ)+1)*h
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let H₀ := 1+64*((C+δ)*G+B)*P+64*(C+δ)*B/ρ
  have hH₀ : 0 < H₀ := by dsimp only [H₀]; positivity
  refine ⟨Λ,ρ,H₀,n,hΛ,hΛL,hρ,hH₀,hnN,hdisp,hJh,hAn,hquad,hBn,rfl,rfl,rfl,hnUpper,?_⟩
  intro H hH
  have hHp := hH₀.trans_le hH
  have he0 : 0 ≤ 64*((C+δ)*G+B)*P := by positivity
  have hb0 : 0 ≤ 64*(C+δ)*B/ρ := by positivity
  constructor
  · apply (div_le_iff₀ hHp).2
    change 1+64*((C+δ)*G+B)*P+64*(C+δ)*B/ρ ≤ H at hH
    change 8*((C+δ)*G+B)*P ≤ (1/8)*H
    nlinarith only [hH,hb0]
  · apply (div_le_iff₀ hHp).2
    have hb : 64*(C+δ)*B/ρ ≤ H := by
      change 1+64*((C+δ)*G+B)*P+64*(C+δ)*B/ρ ≤ H at hH
      linarith only [hH,he0]
    have hc := (div_le_iff₀ hρ).mp hb
    change 8*(C+δ)*B ≤ ρ/8*H
    nlinarith only [hc]

#print axioms exists_spline_correction_parameters
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
