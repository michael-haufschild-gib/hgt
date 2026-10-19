import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalCorrelationLimit
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPatternHarmonicMass

/-! Critical harmonic correlations of finite factorial patterns under translation.
The fixed offset phases survive exactly on the dilation resonance `k = r * l`;
their finite quadratic sum is the physical pattern mass. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

private theorem tr_integrable {f : ℝ → ℝ} {B : ℝ}
    (hf : Continuous f) (hB : ∀ x, |f x| ≤ B) :
    IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ) * f x) (Ioi 1) :=
  (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)).mul_bdd
    hf.aestronglyMeasurable (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hB x))

private def trCos (a : ℝ) : ℝ :=
  ∫ x in Ioi (1 : ℝ), x ^ (-2 : ℝ) * Real.cos (2 * Real.pi * a * x)

private theorem tr_cos_integrable (a : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ) * Real.cos (2 * Real.pi * a * x)) (Ioi 1) :=
  tr_integrable (by fun_prop) (fun x => Real.abs_cos_le_one _)

private def trKernel (a b x : ℝ) : ℝ :=
  x ^ (-2 : ℝ) * Real.cos (2 * Real.pi * a * x) * Real.cos (2 * Real.pi * b * x)

private def trProduct (a b : ℝ) : ℝ := ∫ x in Ioi (1 : ℝ), trKernel a b x

private theorem tr_product_tendsto {a b u v : ℝ} {s t : ℕ → ℝ}
    (ha : 0 < a) (hb : 0 < b) (hs : Tendsto s atTop (𝓝 u)) (ht : Tendsto t atTop (𝓝 v)) :
    Tendsto (fun n => trProduct (a * ((n+1 : ℕ) : ℝ) + s n)
      (b * ((n+1 : ℕ) : ℝ) + t n)) atTop
      (𝓝 (if a=b then trCos (u-v)/2 else 0)) :=
  factorialCriticalCosineProduct_tendsto ha hb hs ht

private theorem tr_kernel_integrable (a b : ℝ) : IntegrableOn (trKernel a b) (Ioi 1) :=
  (tr_cos_integrable a).mul_bdd (by fun_prop)
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (2 * Real.pi * b * x)))

private def trLayer (n j k : ℕ) (x : ℝ) : ℝ :=
  Real.cos (2 * Real.pi * ((k : ℝ) * factorialShiftedFreq (n+j+1)) * x) -
    Real.cos (2 * Real.pi * ((k : ℝ) * ((n+j+1 : ℕ) : ℝ)) * x)

private def trCorr (n i j k l r : ℕ) : ℝ :=
  ∫ x in Ioi (1 : ℝ), x ^ (-2 : ℝ) * trLayer n i k x * trLayer n j l ((r : ℝ) * x)

private theorem tr_corr_eq (n i j k l r : ℕ) :
    trCorr n i j k l r =
      trProduct ((k : ℝ) * factorialShiftedFreq (n+i+1)) (((r : ℝ) * l) * factorialShiftedFreq (n+j+1)) -
      trProduct ((k : ℝ) * factorialShiftedFreq (n+i+1)) (((r : ℝ) * l) * ((n+j+1 : ℕ) : ℝ)) -
      trProduct ((k : ℝ) * ((n+i+1 : ℕ) : ℝ)) (((r : ℝ) * l) * factorialShiftedFreq (n+j+1)) +
      trProduct ((k : ℝ) * ((n+i+1 : ℕ) : ℝ)) (((r : ℝ) * l) * ((n+j+1 : ℕ) : ℝ)) := by
  let a : ℝ := (k : ℝ) * factorialShiftedFreq (n+i+1)
  let a₀ : ℝ := (k : ℝ) * ((n+i+1 : ℕ) : ℝ)
  let b : ℝ := ((r : ℝ) * l) * factorialShiftedFreq (n+j+1)
  let b₀ : ℝ := ((r : ℝ) * l) * ((n+j+1 : ℕ) : ℝ)
  have heq (x : ℝ) : x ^ (-2 : ℝ) * trLayer n i k x * trLayer n j l ((r : ℝ) * x) =
      ((trKernel a b x - trKernel a b₀ x) - trKernel a₀ b x) + trKernel a₀ b₀ x := by
    have he (u : ℝ) : 2 * Real.pi * ((l : ℝ) * u) * ((r : ℝ) * x) =
        2 * Real.pi * (((r : ℝ) * l) * u) * x := by ring
    dsimp only [trLayer, trKernel, a, a₀, b, b₀]
    rw [he, he]
    ring
  unfold trCorr
  simp_rw [heq]
  have hadd := integral_add (((tr_kernel_integrable a b).sub (tr_kernel_integrable a b₀)).sub
    (tr_kernel_integrable a₀ b)) (tr_kernel_integrable a₀ b₀)
  have hsub := integral_sub ((tr_kernel_integrable a b).sub (tr_kernel_integrable a b₀))
    (tr_kernel_integrable a₀ b)
  simp only [Pi.sub_apply] at hadd hsub
  rw [hadd, hsub, integral_sub (tr_kernel_integrable a b) (tr_kernel_integrable a b₀)]
  rfl

private def trDefect (k i j : ℕ) : ℝ :=
  ∫ x in Ioi (1 : ℝ), x ^ (-2 : ℝ) *
    Real.cos (2 * Real.pi * k * ((i : ℝ) - j) * x) * (1 - Real.cos (2 * Real.pi * k * x / 12))

private theorem tr_resonance (a u v : ℝ) :
    trCos (a*(u+1/12)-a*(v+1/12))/2 - trCos (a*(u+1/12)-a*v)/2 -
      trCos (a*u-a*(v+1/12))/2 + trCos (a*u-a*v)/2 =
    ∫ x in Ioi (1 : ℝ), x ^ (-2 : ℝ) * Real.cos (2 * Real.pi * a * (u-v) * x) *
      (1 - Real.cos (2 * Real.pi * a * x / 12)) := by
  have h₁ := (tr_cos_integrable (a*(u+1/12)-a*(v+1/12))).div_const 2
  have h₂ := (tr_cos_integrable (a*(u+1/12)-a*v)).div_const 2
  have h₃ := (tr_cos_integrable (a*u-a*(v+1/12))).div_const 2
  have h₄ := (tr_cos_integrable (a*u-a*v)).div_const 2
  unfold trCos
  simp_rw [← integral_div]
  have hsub := integral_sub (h₁.sub h₂) h₃
  have hadd := integral_add ((h₁.sub h₂).sub h₃) h₄
  simp only [Pi.sub_apply] at hsub hadd
  rw [← integral_sub h₁ h₂, ← hsub, ← hadd]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [show 2 * Real.pi * (a*(u+1/12)-a*(v+1/12)) * x =
        2 * Real.pi * a * (u-v) * x by ring,
    show 2 * Real.pi * (a*(u+1/12)-a*v) * x =
        2 * Real.pi * a * (u-v) * x + 2 * Real.pi * a * x / 12 by ring,
    show 2 * Real.pi * (a*u-a*(v+1/12)) * x =
        2 * Real.pi * a * (u-v) * x - 2 * Real.pi * a * x / 12 by ring,
    show 2 * Real.pi * (a*u-a*v) * x = 2 * Real.pi * a * (u-v) * x by ring,
    Real.cos_add, Real.cos_sub]
  ring

private theorem tr_corr_tendsto (i j : ℕ) {k l r : ℕ}
    (hk : 0 < k) (hl : 0 < l) (hr : 0 < r) :
    Tendsto (fun n => trCorr n i j k l r) atTop
      (𝓝 (if k = r*l then trDefect k i j else 0)) := by
  let a : ℝ := k
  let b : ℝ := (r : ℝ) * l
  have ha : 0 < a := by dsimp only [a]; exact_mod_cast hk
  have hb : 0 < b := mul_pos (by exact_mod_cast hr) (by exact_mod_cast hl)
  have hs := (factorialShiftedFreq_translated_sub_tendsto i).const_mul a
  have ht := (factorialShiftedFreq_translated_sub_tendsto j).const_mul b
  have hss := tr_product_tendsto ha hb hs ht
  have hsi := tr_product_tendsto ha hb hs
    (tendsto_const_nhds (x := b * j))
  have his := tr_product_tendsto ha hb
    (tendsto_const_nhds (x := a * i)) ht
  have hii := tr_product_tendsto ha hb
    (tendsto_const_nhds (x := a * i)) (tendsto_const_nhds (x := b * j))
  have h := ((hss.sub hsi).sub his).add hii
  have hval :
      (if a=b then trCos (a*(i+1/12)-b*(j+1/12))/2 else 0) -
      (if a=b then trCos (a*(i+1/12)-b*j)/2 else 0) -
      (if a=b then trCos (a*i-b*(j+1/12))/2 else 0) +
      (if a=b then trCos (a*i-b*j)/2 else 0) =
      if a=b then trDefect k i j else 0 := by
    by_cases hab : a=b
    · simp only [← hab, ite_true]
      exact tr_resonance a i j
    · simp only [if_neg hab]
      ring
  change Tendsto _ atTop (𝓝 (_ - _ - _ + _)) at h
  rw [hval] at h
  have heq (n : ℕ) :
      trCorr n i j k l r =
      trProduct (a * ((n+1 : ℕ) : ℝ) + a * (factorialShiftedFreq (n+i+1) - ((n+1 : ℕ) : ℝ)))
        (b * ((n+1 : ℕ) : ℝ) + b * (factorialShiftedFreq (n+j+1) - ((n+1 : ℕ) : ℝ))) -
      trProduct (a * ((n+1 : ℕ) : ℝ) + a * (factorialShiftedFreq (n+i+1) - ((n+1 : ℕ) : ℝ)))
        (b * ((n+1 : ℕ) : ℝ) + b*j) -
      trProduct (a * ((n+1 : ℕ) : ℝ) + a*i)
        (b * ((n+1 : ℕ) : ℝ) + b * (factorialShiftedFreq (n+j+1) - ((n+1 : ℕ) : ℝ))) +
      trProduct (a * ((n+1 : ℕ) : ℝ) + a*i) (b * ((n+1 : ℕ) : ℝ) + b*j) := by
    have hf (c x : ℝ) : c * ((n+1 : ℕ) : ℝ) + c * (x - ((n+1 : ℕ) : ℝ)) = c*x := by ring
    have hi (c : ℝ) (q : ℕ) : c * ((n+1 : ℕ) : ℝ) + c*q = c * ((n+q+1 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [tr_corr_eq]
    simp only [hf, hi, a, b]
  have hres := h.congr (fun n => (heq n).symm)
  simpa only [a, b, ← Nat.cast_mul, Nat.cast_inj] using hres

private theorem tr_defect_integrable (k i j : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ) *
      Real.cos (2 * Real.pi * k * ((i : ℝ) - j) * x) *
        (1 - Real.cos (2 * Real.pi * k * x / 12))) (Ioi 1) := by
  have hbound (x : ℝ) : |Real.cos (2 * Real.pi * k * ((i : ℝ) - j) * x) *
      (1 - Real.cos (2 * Real.pi * k * x / 12))| ≤ 2 := by
    rw [abs_mul]
    have hs : |1 - Real.cos (2 * Real.pi * k * x / 12)| ≤ 2 := by
      rw [abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
      linarith [Real.neg_one_le_cos (2 * Real.pi * k * x / 12)]
    exact (mul_le_mul (Real.abs_cos_le_one _) hs (abs_nonneg _) zero_le_one).trans_eq (one_mul 2)
  simpa only [mul_assoc] using tr_integrable (by fun_prop) hbound

private theorem tr_defect_sum_eq_mass (S : Finset ℕ) (b : ℕ → ℝ) (k : ℕ) :
    (∑ i ∈ S, ∑ j ∈ S, b i * b j * trDefect k i j) =
      factorialCriticalPatternHarmonicMass S b k := by
  classical
  let F (i j : ℕ) (x : ℝ) := b i * b j * (x ^ (-2 : ℝ) *
    Real.cos (2 * Real.pi * k * ((i : ℝ) - j) * x) * (1 - Real.cos (2 * Real.pi * k * x / 12)))
  have hF (i j : ℕ) : IntegrableOn (F i j) (Ioi 1) :=
    (tr_defect_integrable k i j).const_mul _
  have hFi (i : ℕ) : IntegrableOn (fun x => ∑ j ∈ S, F i j x) (Ioi 1) :=
    integrable_finsetSum S (fun j hj => hF i j)
  have hsum : (∫ x in Ioi (1 : ℝ), ∑ i ∈ S, ∑ j ∈ S, F i j x) =
      ∑ i ∈ S, ∑ j ∈ S, ∫ x in Ioi (1 : ℝ), F i j x := by
    rw [integral_finsetSum S (fun i hi => hFi i)]
    apply Finset.sum_congr rfl
    intro i hi
    exact integral_finsetSum S (fun j hj => hF i j)
  have hmass : (∫ x in Ioi (1 : ℝ), ∑ i ∈ S, ∑ j ∈ S, F i j x) =
      factorialCriticalPatternHarmonicMass S b k := by
    unfold factorialCriticalPatternHarmonicMass
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [factorialCriticalPatternDensity_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [F]
    rw [show 2 * Real.pi * ((i : ℝ) - j) * ((k : ℝ) * x) =
      2 * Real.pi * k * ((i : ℝ) - j) * x by ring]
    ring
  calc
    (∑ i ∈ S, ∑ j ∈ S, b i * b j * trDefect k i j) =
        ∑ i ∈ S, ∑ j ∈ S, ∫ x in Ioi (1 : ℝ), F i j x := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only [F, trDefect]
      rw [integral_const_mul]
    _ = (∫ x in Ioi (1 : ℝ), ∑ i ∈ S, ∑ j ∈ S, F i j x) := hsum.symm
    _ = factorialCriticalPatternHarmonicMass S b k := hmass

private theorem tr_pattern_corr_tendsto (S : Finset ℕ) (b : ℕ → ℝ) {k l r : ℕ}
    (hk : 0 < k) (hl : 0 < l) (hr : 0 < r) :
    Tendsto (fun n => ∑ i ∈ S, ∑ j ∈ S, b i * b j * trCorr n i j k l r) atTop
      (𝓝 (if k = r*l then factorialCriticalPatternHarmonicMass S b k else 0)) := by
  have h := tendsto_finsetSum S (fun i hi => tendsto_finsetSum S (fun j hj =>
    (tr_corr_tendsto i j hk hl hr).const_mul (b i * b j)))
  have hv : (∑ i ∈ S, ∑ j ∈ S, b i * b j * (if k = r*l then trDefect k i j else 0)) =
      if k = r*l then factorialCriticalPatternHarmonicMass S b k else 0 := by
    by_cases hres : k = r*l
    · simp only [if_pos hres]
      exact tr_defect_sum_eq_mass S b k
    · simp only [if_neg hres, mul_zero, Finset.sum_const_zero]
  rwa [hv] at h

private theorem tr_layer_image (S : Finset ℕ) (b : ℕ → ℝ) (n k : ℕ) (x : ℝ) :
    (factorialHarmonicLayer (S.image (fun j => n+j)) (fun q => (b (q-n) : ℂ)) k x).re =
      ∑ j ∈ S, b j * trLayer n j k x := by
  classical
  unfold factorialHarmonicLayer
  rw [Finset.sum_image]
  · simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Nat.add_sub_cancel_left, trLayer, mul_assoc]
  · intro i hi j hj hij
    exact Nat.add_left_cancel hij

private theorem tr_layer_bound (n j k : ℕ) (x : ℝ) : |trLayer n j k x| ≤ 2 := by
  unfold trLayer
  have h₁ := Real.abs_cos_le_one (2 * Real.pi * ((k : ℝ) * factorialShiftedFreq (n+j+1)) * x)
  have h₂ := Real.abs_cos_le_one (2 * Real.pi * ((k : ℝ) * ((n+j+1 : ℕ) : ℝ)) * x)
  exact (abs_sub _ _).trans (by linarith)

private theorem tr_pair_integrable (n i j k l r : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ) * trLayer n i k x * trLayer n j l ((r : ℝ) * x))
      (Ioi 1) := by
  have hbound (x : ℝ) : |trLayer n i k x * trLayer n j l ((r : ℝ) * x)| ≤ 4 := by
    rw [abs_mul]
    exact (mul_le_mul (tr_layer_bound n i k x) (tr_layer_bound n j l ((r : ℝ) * x))
      (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hc : Continuous (fun x : ℝ => trLayer n i k x * trLayer n j l ((r : ℝ) * x)) := by
    unfold trLayer
    fun_prop
  simpa only [mul_assoc] using tr_integrable hc hbound

private def trSumCorr (S : Finset ℕ) (b : ℕ → ℝ) (n k l r : ℕ) : ℝ :=
  ∫ x in Ioi (1 : ℝ), x ^ (-2 : ℝ) * (∑ i ∈ S, b i * trLayer n i k x) *
    (∑ j ∈ S, b j * trLayer n j l ((r : ℝ) * x))

private theorem tr_sum_corr_eq (S : Finset ℕ) (b : ℕ → ℝ) (n k l r : ℕ) :
    trSumCorr S b n k l r = ∑ i ∈ S, ∑ j ∈ S, b i * b j * trCorr n i j k l r := by
  classical
  let F (i j : ℕ) (x : ℝ) := b i * b j * (x ^ (-2 : ℝ) * trLayer n i k x *
    trLayer n j l ((r : ℝ) * x))
  have hF (i j : ℕ) : IntegrableOn (F i j) (Ioi 1) := (tr_pair_integrable n i j k l r).const_mul _
  have heq (x : ℝ) : x ^ (-2 : ℝ) * (∑ i ∈ S, b i * trLayer n i k x) *
      (∑ j ∈ S, b j * trLayer n j l ((r : ℝ) * x)) = ∑ i ∈ S, ∑ j ∈ S, F i j x := by
    rw [mul_assoc, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [F]
    ring
  unfold trSumCorr
  simp_rw [heq]
  rw [integral_finsetSum S (fun i hi => integrable_finsetSum S (fun j hj => hF i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum S (fun j hj => hF i j)]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only [F, trCorr]
  rw [integral_const_mul]

/-- The actual translated harmonic layers retain precisely their resonant pattern mass. -/
theorem factorialCriticalTranslatedHarmonicCorrelation_tendsto
    (S : Finset ℕ) (b : ℕ → ℝ) (k l r : ℕ) (hr : 0 < r) :
    Tendsto (fun n => ∫ x in Ioi (1 : ℝ), x ^ (-2 : ℝ) *
      (factorialHarmonicLayer (S.image (fun j => n+j)) (fun q => (b (q-n) : ℂ)) k x).re *
      (factorialHarmonicLayer (S.image (fun j => n+j)) (fun q => (b (q-n) : ℂ)) l ((r : ℝ) * x)).re)
      atTop (𝓝 (if k = r*l then factorialCriticalPatternHarmonicMass S b k else 0)) := by
  by_cases hk : k = 0
  · subst k
    simp [factorialHarmonicLayer, factorialCriticalPatternHarmonicMass]
  by_cases hl : l = 0
  · subst l
    simp [factorialHarmonicLayer, hk]
  have h := tr_pattern_corr_tendsto S b (Nat.pos_of_ne_zero hk) (Nat.pos_of_ne_zero hl) hr
  apply h.congr
  intro n
  symm
  simp only [tr_layer_image]
  exact tr_sum_corr_eq S b n k l r

end GaloisForLFunctions.ArithmeticPositivityTheory
