import GaloisForLFunctions.RHTower.Sieve.LogWindowKernel
import GaloisForLFunctions.HTGeometry.LogFrequencySeparation
import GaloisForLFunctions.RHTower.WardDefectFreedomVacuous
import GaloisForLFunctions.HTGeometry.ExpNatIrrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Phase retrieval from successive logarithmic windows

In the weighted Gram expansion of Gabet, Ferreira Da Costa and Lee
(arXiv:2611.18900, §4), Fourier support separates pairs of columns.
Successive arithmetic cutoffs remove every pair except those involving
the latest coefficient. These logarithmic differences are separated at
inverse-linear resolution, even when two earlier pairs have the same ratio.
-/

noncomputable section
open Finset Complex MeasureTheory RHTower RHTower.Sieve
open scoped ComplexConjugate
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval

/-- Short-interval energy of the coefficient prefix. -/
def energy (a : ℕ → ℂ) (N : ℕ) (d : ℝ) :=
  ∫ t : ℝ, ‖logWindowSum a (Icc 1 N) d t‖^2

/-- Additional energy contributed by the next coefficient, including interference. -/
def row (a : ℕ → ℂ) (N : ℕ) (d : ℝ) := energy a (N+1) d - energy a N d

/-- Real Gram pairing of two complex coefficients. -/
def gram (z w : ℂ) := (z*conj w).re

private theorem gram_comm (z w : ℂ) : gram z w=gram w z := by
  simp only [gram,Complex.mul_re,Complex.conj_re,Complex.conj_im]; ring

private theorem gram_self (z : ℂ) : gram z z=‖z‖^2 := by
  rw [gram,Complex.mul_conj,Complex.ofReal_re,Complex.normSq_eq_norm_sq]

/-- Frequency of a cofactor relative to the newly admitted endpoint. -/
def gap (N m : ℕ) := Real.log (N+1:ℕ)-Real.log m

private theorem gap_lower {m N : ℕ} (hm : m ∈ Icc 1 N) :
    ((N+1:ℕ):ℝ)⁻¹ ≤ gap N m := by
  have ht : 0 < N+1 := Nat.succ_pos _
  have hm' := mem_Icc.mp hm
  have h := _root_.HTGeometry.inv_le_abs_log_sub_log_of_le ht hm'.1
    (by omega : N+1 ≠ m) le_rfl (hm'.2.trans (Nat.le_succ N))
  have hg := Real.log_le_log (Nat.cast_pos.mpr hm'.1) (Nat.cast_le.mpr (hm'.2.trans (Nat.le_succ N)))
  simpa only [abs_of_nonneg (sub_nonneg.mpr hg),gap] using h

/-- Exact spectrum of the difference between two nested measurements. -/
theorem row_spectrum (a : ℕ → ℂ) (N : ℕ) (d : ℝ) :
    row a N d = ‖a (N+1)‖^2 * max d 0 +
      2*∑ m ∈ Icc 1 N, gram (a (N+1)) (a m)*max (d-gap N m) 0 := by
  classical
  let K (i j : ℕ) := gram (a i) (a j)*max (d-|Real.log i-Real.log j|) 0
  have hi : Icc 1 (N+1) = insert (N+1) (Icc 1 N) := by
    ext i; simp only [mem_Icc,mem_insert]; omega
  have hn : N+1 ∉ Icc 1 N := by simp
  have hk : ∀ i j, K i j = K j i := fun i j => by
    unfold K
    rw [gram_comm (a i),abs_sub_comm (Real.log i)]
  have hcol : (∑ m ∈ Icc 1 N, K m (N+1)) = ∑ m ∈ Icc 1 N, K (N+1) m :=
    sum_congr rfl fun m _ => hk _ _
  have hfirst : (∑ m ∈ Icc 1 N, K (N+1) m) =
      ∑ m ∈ Icc 1 N, gram (a (N+1)) (a m)*max (d-gap N m) 0 := by
    apply sum_congr rfl
    intro m hm
    have hg : 0 ≤ gap N m := (by positivity : 0 ≤ ((N+1:ℕ):ℝ)⁻¹).trans (gap_lower hm)
    change _ * max (d-|gap N m|) 0 = _
    rw [abs_of_nonneg hg]
  rw [row,energy,energy,integral_normSq_logWindowSum,integral_normSq_logWindowSum]
  change (∑ i ∈ Icc 1 (N+1), ∑ j ∈ Icc 1 (N+1), K i j) -
    (∑ i ∈ Icc 1 N, ∑ j ∈ Icc 1 N, K i j) = _
  have hd : K (N+1) (N+1)=‖a (N+1)‖^2*max d 0 := by simp only [K,gram_self,sub_self,abs_zero,sub_zero]
  simp only [hi,sum_insert hn,sum_add_distrib,hd,hcol,hfirst]
  ring

/-- The first bandwidth bin reads exactly the squared modulus of the
new coefficient, independently of all previous phases. -/
theorem row_diagonal (a : ℕ → ℂ) (N : ℕ) {h : ℝ} (hh : 0 ≤ h) (hcut : h ≤ ((N+1:ℕ):ℝ)⁻¹) :
    row a N h = ‖a (N+1)‖^2*h := by
  rw [row_spectrum,max_eq_left hh,sum_eq_zero (fun m hm => by
    rw [max_eq_right (sub_nonpos.mpr (hcut.trans (gap_lower hm))),mul_zero]),mul_zero,add_zero]

/-- Symmetric second difference of a bandwidth measurement. -/
def second (f : ℝ → ℝ) (x h : ℝ) := f (x+h)-2*f x+f (x-h)

private theorem shifted_ramp (x g : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    second (fun d => max (d-g) 0) x h = max (h-|x-g|) 0 := by
  have he := ramp_secondDifference h (x+h-g) hh
  simpa only [second,tent,show x+h-g-h=x-g by ring,
    show x+h-g-2*h=x-h-g by ring,max_comm (0:ℝ)] using he

private theorem second_row (a : ℕ → ℂ) (N : ℕ) (x : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    second (row a N) x h = ‖a (N+1)‖^2*max (h-|x|) 0 +
      2*∑ m ∈ Icc 1 N, gram (a (N+1)) (a m)*max (h-|x-gap N m|) 0 := by
  have hd := shifted_ramp x 0 hh
  simp only [second,sub_zero] at hd
  have he (m : ℕ) := shifted_ramp x (gap N m) hh
  simp only [second] at he
  rw [← hd]
  simp_rw [← he]
  simp only [second,row_spectrum,mul_add,mul_sub,sum_add_distrib,sum_sub_distrib,
    show ∀ a b : ℝ, a*(2*b)=2*(a*b) by intros; ring,← mul_sum]
  ring

/-- Two cutoffs and three bandwidths recover any prescribed real Gram
entry. Inverse-linear bandwidth resolution suffices for the entire row. -/
theorem read_gram (a : ℕ → ℂ) {N m : ℕ} (hm : m ∈ Icc 1 N) {h : ℝ}
    (hh : 0 < h) (hcut : h ≤ ((N+1:ℕ):ℝ)⁻¹) :
    second (row a N) (gap N m) h/(2*h)=gram (a (N+1)) (a m) := by
  have hz := hcut.trans (gap_lower hm)
  have hsep (j : ℕ) (hj : j ∈ Icc 1 N) (hne : j ≠ m) :
      h ≤ |gap N m-gap N j| := by
    rw [show gap N m-gap N j=Real.log j-Real.log m by dsimp [gap]; ring]
    exact hcut.trans (_root_.HTGeometry.inv_le_abs_log_sub_log_of_le (mem_Icc.mp hj).1
      (mem_Icc.mp hm).1 hne ((mem_Icc.mp hj).2.trans (Nat.le_succ _)) ((mem_Icc.mp hm).2.trans (Nat.le_succ _)))
  rw [second_row a N _ hh.le,abs_of_pos (hh.trans_le hz),max_eq_right (sub_nonpos.mpr hz),mul_zero,zero_add,
    sum_eq_single m (fun j hj hne => by rw [max_eq_right (sub_nonpos.mpr (hsep j hj hne)),mul_zero])
      (fun hn => (hn hm).elim),sub_self,abs_zero,sub_zero,max_eq_left hh.le,
    div_eq_iff (mul_ne_zero two_ne_zero hh.ne')]
  ring

/-- Equality of all measured energy curves is equivalent to equality of
the real Gram matrices of all positive-index coefficients. -/
theorem equal_energies_iff_grams (a b : ℕ → ℂ) :
    (∀ N d, energy a N d=energy b N d) ↔
      ∀ i j : ℕ, 0 < i → 0 < j → gram (a i) (a j)=gram (b i) (b j) := by
  constructor
  · intro he
    have hr (N : ℕ) : row a N=row b N := funext fun d => by simp only [row,he]
    have triangle (i j : ℕ) (hi : 0 < i) (hj : 0 < j) (hji : j ≤ i) :
        gram (a i) (a j)=gram (b i) (b j) := by
      obtain ⟨N,rfl⟩ : ∃ N, i=N+1 := ⟨i-1,by omega⟩
      let h := ((N+1:ℕ):ℝ)⁻¹
      have hh : 0 < h := by dsimp [h]; positivity
      rcases eq_or_lt_of_le hji with rfl | hlt
      · have hs := congrFun (hr N) h
        rw [row_diagonal _ _ hh.le le_rfl,row_diagonal _ _ hh.le le_rfl] at hs
        simpa only [gram_self] using mul_right_cancel₀ hh.ne' hs
      · have hm : j ∈ Icc 1 N := mem_Icc.mpr ⟨hj,by omega⟩
        rw [← read_gram a hm hh le_rfl,← read_gram b hm hh le_rfl,hr]
    intro i j hi hj
    rcases le_total j i with h | h
    · exact triangle i j hi hj h
    · rw [gram_comm (a i),gram_comm (b i)]
      exact triangle j i hj hi h
  · intro hg N d
    simp only [energy,integral_normSq_logWindowSum]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    exact congrArg (fun v : ℝ => v*_) (hg i j (mem_Icc.mp hi).1 (mem_Icc.mp hj).1)

private theorem real_sign_rigidity (x y : ℕ → ℝ)
    (h : ∀ i j : ℕ, 0 < i → 0 < j → x i*x j=y i*y j) :
    (∀ i, 0 < i → x i=y i) ∨ (∀ i, 0 < i → x i= -y i) := by
  by_cases hn : ∃ k, 0 < k ∧ x k ≠ 0
  · obtain ⟨k,hk,hk0⟩ := hn
    have hsq := h k k hk hk
    have hp : (x k-y k)*(x k+y k)=0 := by linarith only [hsq]
    rcases mul_eq_zero.mp hp with he | he
    · have he' := sub_eq_zero.mp he
      refine Or.inl fun i hi => mul_left_cancel₀ hk0 ?_
      simpa only [← he'] using h k i hk hi
    · have he' : y k= -x k := by linarith only [he]
      refine Or.inr fun i hi => mul_left_cancel₀ hk0 ?_
      simpa only [he',neg_mul,mul_neg] using h k i hk hi
  · refine Or.inl fun i hi => ?_
    have hz : x i=0 := not_ne_iff.mp fun he => hn ⟨i,hi,he⟩
    have hs := h i i hi hi
    rw [hz,zero_mul] at hs
    rcases mul_eq_zero.mp hs.symm with he | he <;> rw [he,hz]

/-- For real coefficients a single common sign is the entire ambiguity.
Zeros among the coefficients require no special support assumptions. -/
theorem real_phase_retrieval (a b : ℕ → ℝ) :
    (∀ N d, energy (fun i => (a i:ℂ)) N d=energy (fun i => (b i:ℂ)) N d) ↔
      (∀ i, 0 < i → a i=b i) ∨ (∀ i, 0 < i → a i= -b i) := by
  rw [equal_energies_iff_grams]
  simp only [gram,Complex.conj_ofReal,← Complex.ofReal_mul,Complex.ofReal_re]
  constructor
  · exact real_sign_rigidity a b
  · rintro (h|h) i j hi hj
    · rw [h i hi,h j hj]
    · rw [h i hi,h j hj,neg_mul_neg]

private theorem gram_twist (z w c : ℂ) : gram (z*c) (w*c)=gram z w * ‖c‖^2 := by
  simp only [gram,Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
    ← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  ring

private theorem gram_conj (z w : ℂ) : gram (conj z) (conj w)=gram z w := by
  simp only [gram,Complex.mul_re,Complex.conj_re,Complex.conj_im,neg_neg]; ring

/-- Complex coefficients are determined up to a common rotation and a
possible common conjugation. An anchor fixes the real coordinates;
the real Gram matrix leaves only one common sign for the imaginary coordinates. -/
theorem complex_phase_retrieval (a b : ℕ → ℂ) :
    (∀ N d, energy a N d=energy b N d) ↔
    ∃ u : ℂ, ‖u‖=1 ∧ ((∀ i, 0 < i → b i=a i*u) ∨ (∀ i, 0 < i → b i=conj (a i)*u)) := by
  rw [equal_energies_iff_grams]
  constructor
  · intro hg
    have hn (i : ℕ) (hi : 0 < i) : ‖a i‖=‖b i‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      simpa only [gram_self] using hg i i hi hi
    by_cases hnon : ∃ k, 0 < k ∧ a k ≠ 0
    · obtain ⟨k,hk,ha⟩ := hnon
      have hb : b k ≠ 0 := norm_ne_zero_iff.mp ((hn k hk).symm.trans_ne (norm_ne_zero_iff.mpr ha))
      have hc : conj (b k) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hb
      let A := fun i => a i*conj (a k)
      let B := fun i => b i*conj (b k)
      have hre (i : ℕ) (hi : 0 < i) : (B i).re=(A i).re := (hg i k hi hk).symm
      have him (i j : ℕ) (hi : 0 < i) (hj : 0 < j) : (B i).im*(B j).im=(A i).im*(A j).im := by
        have he : gram (B i) (B j)=gram (A i) (A j) := by
          dsimp only [B,A]
          rw [gram_twist,gram_twist,hg i j hi hj,Complex.norm_conj,Complex.norm_conj,hn k hk]
        simp only [gram,Complex.mul_re,Complex.conj_re,Complex.conj_im,hre i hi,hre j hj] at he
        linarith only [he]
      rcases real_sign_rigidity (fun i => (B i).im) (fun i => (A i).im) him with hs | hs
      · refine ⟨conj (a k)/conj (b k),?_,Or.inl fun i hi => ?_⟩
        · rw [norm_div,Complex.norm_conj,Complex.norm_conj,hn k hk,div_self (norm_ne_zero_iff.mpr hb)]
        · have he := Complex.ext (hre i hi) (hs i hi)
          change b i*conj (b k)=a i*conj (a k) at he
          rw [← mul_div_assoc,eq_div_iff hc]
          exact he
      · refine ⟨a k/conj (b k),?_,Or.inr fun i hi => ?_⟩
        · rw [norm_div,Complex.norm_conj,hn k hk,div_self (norm_ne_zero_iff.mpr hb)]
        · have he : B i=conj (A i) := Complex.ext (by simpa only [Complex.conj_re] using hre i hi)
            (by simpa only [Complex.conj_im] using hs i hi)
          change b i*conj (b k)=conj (a i*conj (a k)) at he
          rw [map_mul,conj_conj] at he
          rw [← mul_div_assoc,eq_div_iff hc]
          exact he
    · refine ⟨1,norm_one,Or.inl fun i hi => ?_⟩
      have hz := not_ne_iff.mp (fun he => hnon ⟨i,hi,he⟩)
      have hb := hn i hi
      rw [hz,norm_zero] at hb
      rw [norm_eq_zero.mp hb.symm,hz,zero_mul]
  · rintro ⟨u,hu,h|h⟩ i j hi hj
    · rw [h i hi,h j hj,gram_twist,hu,one_pow,mul_one]
    · rw [h i hi,h j hj,gram_twist,gram_conj,hu,one_pow,mul_one]

/-- Translation by t in the time variable of the exponential polynomial. -/
def translated (a : ℕ → ℂ) (t : ℝ) (n : ℕ) :=
  a n * cexp (((t*Real.log n : ℝ):ℂ)*I)

/-- A time shift rotates each complex correlation through its own log gap. -/
theorem translated_gram (a : ℕ → ℂ) (t : ℝ) (i j : ℕ) :
    gram (translated a t i) (translated a t j) =
      gram (a i) (a j)*Real.cos (t*(Real.log i-Real.log j)) -
      (a i*conj (a j)).im*Real.sin (t*(Real.log i-Real.log j)) := by
  have he : translated a t i * conj (translated a t j) =
      (a i*conj (a j)) * cexp (((t*(Real.log i-Real.log j) : ℝ):ℂ)*I) := by
    simp only [translated,map_mul,← Complex.exp_conj,Complex.conj_ofReal,Complex.conj_I,mul_neg]
    rw [show (((t*(Real.log i-Real.log j):ℝ):ℂ)*I) =
      ((t*Real.log i:ℝ):ℂ)*I + -(((t*Real.log j:ℝ):ℂ)*I) by push_cast; ring, Complex.exp_add]
    ring
  simp only [gram,he,Complex.mul_re,Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im]

/-- The shift π separates every positive integer pair: otherwise the
exponential of a nonzero integer would be their rational ratio. -/
theorem pi_shift_separates {i j : ℕ} (hi : 0 < i) (hj : 0 < j) (hij : i ≠ j) :
    Real.sin (Real.pi*(Real.log i-Real.log j)) ≠ 0 := by
  intro he
  obtain ⟨k,hk⟩ := Real.sin_eq_zero_iff.mp he
  have hlog : Real.log i-Real.log j = (k:ℝ) := by
    apply mul_right_cancel₀ Real.pi_ne_zero
    linear_combination -hk
  have hex : Real.exp k = (i:ℝ)/j := by
    rw [← hlog,Real.exp_sub,Real.exp_log (Nat.cast_pos.mpr hi),Real.exp_log (Nat.cast_pos.mpr hj)]
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Int.cast_zero,Real.exp_zero,eq_div_iff (Nat.cast_ne_zero.mpr hj.ne'),one_mul] at hex
    exact hij (by exact_mod_cast hex.symm)
  exact (GaloisForLFunctions.RHTower.exp_int_irrational hk0).ne_rational i j (by
    simpa only [Int.cast_natCast] using hex)

/-- Two translated energy curves recover the *imaginary* part of a
correlation at the same bandwidth resolution as the real part. -/
theorem read_imaginary_correlation (a : ℕ → ℂ) {N m : ℕ} (hm : m ∈ Icc 1 N) {h : ℝ}
    (hh : 0 < h) (hcut : h ≤ ((N+1:ℕ):ℝ)⁻¹) :
    let g := gap N m
    (second (row a N) g h/(2*h)*Real.cos (Real.pi*g) -
     second (row (translated a Real.pi) N) g h/(2*h))/Real.sin (Real.pi*g) =
      (a (N+1)*conj (a m)).im := by
  intro g
  have hm' := mem_Icc.mp hm
  have hs := pi_shift_separates (Nat.succ_pos N) hm'.1 (by omega : N+1 ≠ m)
  rw [read_gram a hm hh hcut,read_gram _ hm hh hcut,translated_gram]
  dsimp only [g,gap]
  rw [div_eq_iff hs]
  ring

/-- A single prescribed translation together with the original measurement
determines the whole sequence up to a constant unit phase. -/
theorem two_translates_recover_phase (a b : ℕ → ℂ) :
    ((∀ N d, energy a N d = energy b N d) ∧
      (∀ N d, energy (translated a Real.pi) N d = energy (translated b Real.pi) N d)) ↔
    ∃ u : ℂ, ‖u‖=1 ∧ ∀ i : ℕ, 0 < i → b i=a i*u := by
  simp only [equal_energies_iff_grams]
  constructor
  · rintro ⟨hg,hs⟩
    have hprod (i j : ℕ) (hi : 0 < i) (hj : 0 < j) : a i*conj (a j)=b i*conj (b j) := by
      refine Complex.ext (hg i j hi hj) ?_
      by_cases he : i=j
      · subst j; simp only [Complex.mul_conj,Complex.ofReal_im]
      have h := hs i j hi hj
      rw [translated_gram,translated_gram,hg i j hi hj] at h
      exact mul_right_cancel₀ (pi_shift_separates hi hj he) (by linarith only [h])
    have hn (i : ℕ) (hi : 0 < i) : ‖a i‖=‖b i‖ :=
      (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by simpa only [gram_self] using hg i i hi hi)
    by_cases hx : ∃ k : ℕ, 0 < k ∧ a k ≠ 0
    · obtain ⟨k,hk,ha⟩ := hx
      have hb : b k ≠ 0 := norm_ne_zero_iff.mp ((hn k hk).symm.trans_ne (norm_ne_zero_iff.mpr ha))
      have hc : conj (b k) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hb
      refine ⟨conj (a k)/conj (b k),?_,fun i hi => ?_⟩
      · rw [norm_div,Complex.norm_conj,Complex.norm_conj,hn k hk,div_self (norm_ne_zero_iff.mpr hb)]
      · rw [← mul_div_assoc,eq_div_iff hc]
        exact (hprod i k hi hk).symm
    · refine ⟨1,norm_one,fun i hi => ?_⟩
      have hz : a i=0 := not_ne_iff.mp fun he => hx ⟨i,hi,he⟩
      have hn' := hn i hi
      rw [hz,norm_zero] at hn'
      rw [hz,zero_mul,norm_eq_zero.mp hn'.symm]
  · rintro ⟨u,hu,h⟩
    have ht (i : ℕ) (hi : 0 < i) :
        translated b Real.pi i = translated a Real.pi i*u := by
      simp only [translated,h i hi]; ring
    constructor <;> intro i j hi hj
    · rw [h i hi,h j hj,gram_twist,hu,one_pow,mul_one]
    · rw [ht i hi,ht j hj,gram_twist,hu,one_pow,mul_one]

/-- At every fixed time shift the sine denominator for adjacent
frequencies is at most |t|/n. Exact identifiability therefore does
not supply a condition number uniform in the polynomial length. -/
theorem adjacent_translation_bound (t : ℝ) {n : ℕ} (hn : 0 < n) :
    |Real.sin (t*gap n n)| ≤ |t|/(n:ℝ) := by
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hnn : 0 ≤ gap n n := (by positivity : 0 ≤ ((n+1:ℕ):ℝ)⁻¹).trans (gap_lower (mem_Icc.mpr ⟨hn,le_rfl⟩))
  have hg : gap n n ≤ 1/(n:ℝ) := by
    rw [gap,← Real.log_div (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) hn'.ne']
    have he := Real.log_le_sub_one_of_pos (div_pos (Nat.cast_pos.mpr (Nat.succ_pos n)) hn')
    refine he.trans_eq ?_
    push_cast
    field_simp [hn'.ne']
    ring
  calc _ ≤ |t*gap n n| := Real.abs_sin_le_abs
       _ = |t| * gap n n := by rw [abs_mul,abs_of_nonneg hnn]
       _ ≤ |t| * (1/n) := mul_le_mul_of_nonneg_left hg (abs_nonneg t)
       _ = _ := by ring

#print axioms pi_shift_separates
#print axioms read_imaginary_correlation
#print axioms two_translates_recover_phase
#print axioms adjacent_translation_bound

#print axioms real_phase_retrieval
#print axioms complex_phase_retrieval
#print axioms row_spectrum
#print axioms row_diagonal
#print axioms read_gram
#print axioms equal_energies_iff_grams
end GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
