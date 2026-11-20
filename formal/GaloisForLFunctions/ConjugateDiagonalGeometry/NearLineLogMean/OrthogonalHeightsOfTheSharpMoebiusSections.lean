import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheMicroscopicCovarianceOfSharpMoebiusSections

/-!
# Orthogonal microscopic heights of actual Möbius sections

The sinc Gram matrix of the log frequencies occurs in averages of the
sharp critical-line Möbius polynomial. Logarithmic normalization lowers
the amount of time averaging required to L much larger than X/log X.
On a harmonic lattice the finite part of the unnormalized Gram matrix
is a common rank-one term.
-/
noncomputable section
open Finset Complex MeasureTheory Filter
open scoped ComplexConjugate Topology
open _root_.RHTower.Sieve (squarefreeDensity)
open GaloisForLFunctions.MultiscaleMollifiedZetaField
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private theorem density_pos : 0 < squarefreeDensity := by
  rw [_root_.RHTower.Sieve.squarefreeDensity_eq]; positivity

/-- Time Gram entry for two independently translated copies of the same
sharp critical-line polynomial, with logarithmic height coordinates. -/
def microscopicGram (X A L u v : ℝ) : ℂ :=
  (∫ t in A..(A+L),moebiusPoly ⌊X⌋₊ (linePoint (t+u/Real.log X))*
    conj (moebiusPoly ⌊X⌋₊ (linePoint (t+v/Real.log X))))/(L:ℂ)

private theorem gram_as_shift (X A L u v : ℝ) :
    microscopicGram X A L u v=sharpMoebiusCovariance X (A+v/Real.log X) L ((u-v)/Real.log X) := by
  let f := fun t => moebiusPoly ⌊X⌋₊ (linePoint (t+(u-v)/Real.log X))*conj (moebiusPoly ⌊X⌋₊ (linePoint t))
  have h := intervalIntegral.integral_comp_add_right (f:=f) (a:=A) (b:=A+L) (v/Real.log X)
  dsimp only [f] at h
  simp only [show ∀ t : ℝ,t+v/Real.log X+(u-v)/Real.log X=t+u/Real.log X from fun t => by ring] at h
  rw [show A+L+v/Real.log X=A+v/Real.log X+L by ring] at h
  exact congrArg (fun z : ℂ => z/(L:ℂ)) h

/-- Uniform error for every pair of microscopic height translates. -/
theorem microscopic_gram_error {X L : ℝ} (hX : 1<X) (hL : 0<L) (A u v : ℝ) :
    ‖microscopicGram X A L u v-(squarefreeDensity:ℂ)*(Real.log X:ℂ)*unitLogWindow (u-v)-
      (squarefreeHarmonicConstant:ℂ)‖ ≤ 104*X/L+12*X^(-(1/2:ℝ))+24*|u-v|/Real.log X := by
  have ht := sharp_covariance_microscopic_estimate hX hL (A+v/Real.log X) ((u-v)/Real.log X)
  rw [div_mul_cancel₀ _ (Real.log_pos hX).ne',abs_div,abs_of_pos (Real.log_pos hX),←mul_div_assoc] at ht
  rwa [gram_as_shift]

/-- Intervals need only dominate X/log X for the normalized Gram matrix
to converge at every fixed pair of heights u,v. -/
theorem microscopic_gram_sinc_limit (A L : ℝ → ℝ) (hL : ∀ᶠ X in atTop,0<L X)
    (hsize : Tendsto (fun X : ℝ => X/(L X*Real.log X)) atTop (𝓝 0)) (u v : ℝ) :
    Tendsto (fun X : ℝ => microscopicGram X (A X) (L X) u v/(Real.log X:ℂ))
      atTop (𝓝 ((squarefreeDensity:ℂ)*unitLogWindow (u-v))) := by
  let c := squarefreeHarmonicConstant
  let E := fun X : ℝ => microscopicGram X (A X) (L X) u v-
    (squarefreeDensity:ℂ)*(Real.log X:ℂ)*unitLogWindow (u-v)-(c:ℂ)
  have hlog := tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hcut := tendsto_rpow_neg_atTop (by norm_num : 0<(1/2:ℝ))
  have he0 : Tendsto (fun X : ℝ => E X/(Real.log X:ℂ)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have ht := (hsize.const_mul 104).add (((hcut.const_mul 12).mul hlog).add ((hlog.pow 2).const_mul (24*|u-v|)))
    simp only [mul_zero,zero_mul,add_zero,zero_pow (by decide : 2≠0)] at ht
    refine squeeze_zero' (.of_forall fun _ => norm_nonneg _) ?_ ht
    filter_upwards [eventually_gt_atTop (1:ℝ),hL] with X hX hl
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.log_pos hX)]
    have he := div_le_div_of_nonneg_right (microscopic_gram_error hX hl (A X) u v) (Real.log_pos hX).le
    exact he.trans_eq (by dsimp only [Function.comp_apply];ring)
  have hc : Tendsto (fun X : ℝ => (c:ℂ)/(Real.log X:ℂ)) atTop (𝓝 0) := by
    simpa only [Complex.ofReal_zero,div_eq_mul_inv,Complex.ofReal_inv,mul_zero,Function.comp_apply] using
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hlog).const_mul (c:ℂ)
  have ht := (he0.add hc).add_const ((squarefreeDensity:ℂ)*unitLogWindow (u-v))
  rw [zero_add,zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
  dsimp only [E]
  field_simp [Complex.ofReal_ne_zero.mpr (Real.log_pos hX).ne']
  ring

private theorem unit_window_at_zero : unitLogWindow 0=1 := by simp [unitLogWindow]

/-- The only nonzero height gaps orthogonal in the limiting Gram matrix
are nonzero integral multiples of a full turn. -/
theorem unitLogWindow_eq_zero_iff (v : ℝ) :
    unitLogWindow v=0 ↔ ∃ k : ℤ,k≠0 ∧ v=(k:ℝ)*(2*Real.pi) := by
  refine ⟨fun hv => ?_,fun ⟨k,hk,h⟩ => h ▸ unitLogWindow_nonzero_harmonic hk⟩
  have hn : v≠0 := by rintro rfl;rw [unit_window_at_zero] at hv;exact one_ne_zero hv
  have hc := mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hn)) I_ne_zero
  rw [unitLogWindow,integral_exp_mul_complex hc] at hv
  simp only [Complex.ofReal_one,Complex.ofReal_zero,mul_one,mul_zero,Complex.exp_zero,
    div_eq_zero_iff,hc,or_false,sub_eq_zero] at hv
  obtain ⟨k,hk⟩ := Complex.exp_eq_one_iff.mp hv
  have him := congrArg Complex.im hk
  simp only [Complex.mul_im,Complex.ofReal_im,Complex.neg_re,Complex.ofReal_re,Complex.neg_im,
    Complex.I_im,Complex.I_re,Complex.intCast_im,Complex.intCast_re,Complex.re_ofNat,Complex.im_ofNat,Complex.mul_re,sub_zero,
    mul_one,zero_mul,mul_zero,add_zero,zero_add,neg_zero] at him
  refine ⟨-k,?_,?_⟩
  · intro hzero
    have he : k=0 := neg_eq_zero.mp hzero
    rw [he,Int.cast_zero,zero_mul] at him
    exact hn (neg_eq_zero.mp him)
  · rw [Int.cast_neg]
    linarith only [him]

/-- Limiting time orthogonality of two microscopic copies is equivalent
to the arithmetic lattice condition on their height gap. -/
theorem microscopic_orthogonal_iff (A L : ℝ → ℝ) (hL : ∀ᶠ X in atTop,0<L X)
    (hsize : Tendsto (fun X : ℝ => X/(L X*Real.log X)) atTop (𝓝 0)) (u v : ℝ) :
    Tendsto (fun X : ℝ => microscopicGram X (A X) (L X) u v/(Real.log X:ℂ)) atTop (𝓝 0) ↔
      ∃ k : ℤ,k≠0 ∧ u-v=(k:ℝ)*(2*Real.pi) := by
  have h := microscopic_gram_sinc_limit A L hL hsize u v
  rw [←unitLogWindow_eq_zero_iff]
  constructor
  · intro hz
    exact (mul_eq_zero.mp (tendsto_nhds_unique h hz)).resolve_left (Complex.ofReal_ne_zero.mpr density_pos.ne')
  · intro hz
    simpa only [hz,mul_zero] using h

private theorem lattice_window (i j : ℤ) :
    unitLogWindow ((i:ℝ)*(2*Real.pi)-(j:ℝ)*(2*Real.pi))=if i=j then 1 else 0 := by
  by_cases h : i=j
  · simp [h,unit_window_at_zero]
  · rw [if_neg h,←sub_mul,←Int.cast_sub]
    exact unitLogWindow_nonzero_harmonic (sub_ne_zero.mpr h)

/-- After subtracting the logarithmic diagonal, *every* pair of harmonic
height translations has the same Laurent constant in its time Gram entry. -/
theorem harmonic_gram_finite_part (A L : ℝ → ℝ) (hL : ∀ᶠ X in atTop,0<L X)
    (hshort : Tendsto (fun X : ℝ => X/L X) atTop (𝓝 0)) (i j : ℤ) :
    Tendsto (fun X : ℝ => microscopicGram X (A X) (L X) ((i:ℝ)*(2*Real.pi)) ((j:ℝ)*(2*Real.pi))-
      (if i=j then (squarefreeDensity:ℂ)*(Real.log X:ℂ) else 0)) atTop (𝓝 (squarefreeHarmonicConstant:ℂ)) := by
  let u := (i:ℝ)*(2*Real.pi)
  let v := (j:ℝ)*(2*Real.pi)
  have hh : Tendsto (fun X : ℝ => (u-v)/Real.log X) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul (u-v)
  have ht := sharp_covariance_regular_part (fun X => A X+v/Real.log X) L _ hL hshort hh
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
  rw [gram_as_shift,div_mul_cancel₀ _ (Real.log_pos hX).ne']
  dsimp only [u,v]
  rw [lattice_window]
  split <;> simp

/-- On any finite lattice of translated heights the second term is a
rank-one form, including for general complex cross weights. In particular
balanced linear combinations remove the constant exactly in the limit. -/
theorem weighted_harmonic_gram_finite_part (S : Finset ℤ) (a b : ℤ → ℂ)
    (A L : ℝ → ℝ) (hL : ∀ᶠ X in atTop,0<L X) (hshort : Tendsto (fun X : ℝ => X/L X) atTop (𝓝 0)) :
    Tendsto (fun X : ℝ => (∑ i∈S,∑ j∈S,a i*conj (b j)*
        microscopicGram X (A X) (L X) ((i:ℝ)*(2*Real.pi)) ((j:ℝ)*(2*Real.pi)))-
      (squarefreeDensity:ℂ)*(Real.log X:ℂ)*∑ i∈S,a i*conj (b i)) atTop
      (𝓝 ((squarefreeHarmonicConstant:ℂ)*(∑ i∈S,a i)*conj (∑ j∈S,b j))) := by
  classical
  let G := fun X i j => microscopicGram X (A X) (L X) ((i:ℝ)*(2*Real.pi)) ((j:ℝ)*(2*Real.pi))
  let d := fun X : ℝ => (squarefreeDensity:ℂ)*(Real.log X:ℂ)
  have ht (i j : ℤ) : Tendsto (fun X => a i*conj (b j)*(G X i j-if i=j then d X else 0))
      atTop (𝓝 (a i*conj (b j)*(squarefreeHarmonicConstant:ℂ))) :=
    (harmonic_gram_finite_part A L hL hshort i j).const_mul _
  have hs := tendsto_finsetSum S (fun i _ => tendsto_finsetSum S (fun j _ => ht i j))
  have hsum : (∑ i∈S,∑ j∈S,a i*conj (b j)*(squarefreeHarmonicConstant:ℂ))=
      (squarefreeHarmonicConstant:ℂ)*(∑ i∈S,a i)*conj (∑ j∈S,b j) := by
    rw [map_sum,mul_assoc,Finset.sum_mul_sum,Finset.mul_sum]
    exact sum_congr rfl fun i _ => by rw [Finset.mul_sum];exact sum_congr rfl fun j _ => by ring
  rw [hsum] at hs
  apply hs.congr'
  apply Filter.Eventually.of_forall
  intro X
  simp only [mul_sub,sum_sub_distrib,mul_ite,mul_zero,Finset.sum_ite_eq]
  rw [Finset.mul_sum]
  congr 1
  apply sum_congr rfl
  intro i hi
  simp only [if_pos hi,G,d]
  ring

/-- Finite Gram error for any number of integer harmonics. The rank-one
Laurent term is explicit and the remaining operator error depends on the
diameter of the frequency set and the ℓ¹ masses of the two input rows. -/
theorem harmonic_gram_error_on_a_band (S : Finset ℤ) (a b : ℤ → ℂ) {R X L : ℝ}
    (hR : ∀ i∈S,∀ j∈S,|(i:ℝ)-(j:ℝ)|≤R) (hX : 1<X) (hL : 0<L) (A : ℝ) :
    ‖(∑ i∈S,∑ j∈S,a i*conj (b j)*microscopicGram X A L ((i:ℝ)*(2*Real.pi)) ((j:ℝ)*(2*Real.pi)))-
      (squarefreeDensity:ℂ)*(Real.log X:ℂ)*(∑ i∈S,a i*conj (b i))-
      (squarefreeHarmonicConstant:ℂ)*(∑ i∈S,a i)*conj (∑ j∈S,b j)‖ ≤
        (104*X/L+12*X^(-(1/2:ℝ))+48*Real.pi*R/Real.log X)*(∑ i∈S,‖a i‖)*(∑ j∈S,‖b j‖) := by
  classical
  let G := fun i j : ℤ => microscopicGram X A L ((i:ℝ)*(2*Real.pi)) ((j:ℝ)*(2*Real.pi))
  let d : ℂ := (squarefreeDensity:ℂ)*(Real.log X:ℂ)
  let c : ℂ := squarefreeHarmonicConstant
  let E := 104*X/L+12*X^(-(1/2:ℝ))+48*Real.pi*R/Real.log X
  let K := fun i j : ℤ => G i j-(if i=j then d else 0)-c
  have hbnd (i : ℤ) (hi : i∈S) (j : ℤ) (hj : j∈S) : ‖K i j‖≤E := by
    have h := microscopic_gram_error hX hL A ((i:ℝ)*(2*Real.pi)) ((j:ℝ)*(2*Real.pi))
    rw [lattice_window,←sub_mul,abs_mul,abs_of_pos (mul_pos (by norm_num : (0:ℝ) < 2) Real.pi_pos)] at h
    have hg := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hR i hi j hj) (mul_pos (by norm_num : (0:ℝ) < 2) Real.pi_pos).le) (by norm_num : (0:ℝ)≤24))
      (Real.log_pos hX).le
    have h' := h.trans (add_le_add_right hg _)
    dsimp only [K,G,c,d,E]
    have hE : 104*X/L+12*X^(-(1/2:ℝ))+24*(R*(2*Real.pi))/Real.log X =
        104*X/L+12*X^(-(1/2:ℝ))+48*Real.pi*R/Real.log X := by ring
    rw [hE] at h'
    split_ifs at h' ⊢
    · simpa only [mul_one] using h'
    · simpa only [mul_zero,sub_zero] using h'
  have hdiag (i : ℤ) (hi : i∈S) : (∑ j∈S,a i*conj (b j)*(if i=j then d else 0))=d*(a i*conj (b i)) := by
    rw [sum_eq_single_of_mem i hi]
    · rw [if_pos rfl];ring
    · intro j _ hj;rw [if_neg hj.symm,mul_zero]
  have hconst (i : ℤ) : (∑ j∈S,a i*conj (b j)*c)=(c*a i)*conj (∑ j∈S,b j) := by
    rw [map_sum,mul_sum];exact sum_congr rfl fun j _ => by ring
  have hsum : (∑ i∈S,∑ j∈S,a i*conj (b j)*K i j)=
      (∑ i∈S,∑ j∈S,a i*conj (b j)*G i j)-d*(∑ i∈S,a i*conj (b i))-c*(∑ i∈S,a i)*conj (∑ j∈S,b j) := by
    simp only [K,mul_sub,sum_sub_distrib,hconst,←sum_mul]
    rw [sum_congr rfl hdiag,←mul_sum,←mul_sum]
  change ‖(∑ i∈S,∑ j∈S,a i*conj (b j)*G i j)-d*_ - c*_*_‖≤ E*_*_
  rw [←hsum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i∈S,∑ j∈S,‖a i‖*‖b j‖*E := by
      refine sum_le_sum fun i hi => (norm_sum_le _ _).trans (sum_le_sum fun j hj => ?_)
      simp only [norm_mul,Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left (hbnd i hi j hj) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      rw [mul_assoc E,Finset.sum_mul]
      rw [mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [mul_sum,mul_sum]
      exact sum_congr rfl fun j _ => by ring

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
