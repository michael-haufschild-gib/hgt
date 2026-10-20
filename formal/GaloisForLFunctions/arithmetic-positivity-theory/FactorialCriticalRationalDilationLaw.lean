import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalTranslatedCorrelationLimit
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeAdmission

/-!
# Rational dilation law of critical factorial sources

The critical correlation of a translated factorial pattern at an arbitrary real dilation `ρ`
expands into harmonic pairs `(k, l)`. The cosine-product limit keeps a pair only when the rates
agree, `k = ρ l`, and then the collar's slow phase survives as the pattern mass `J_k(b)`. Hence
the limit exists at every real dilation, vanishes at every irrational `ρ`, and at a reduced
rational `p/q` equals `(4/π⁴) Σ_t w_{pt} w_{qt} J_{pt}(b)`. In shift coordinates the limiting
autocorrelation of every translated critical source is supported on `log ℚ_{>0}`; the prime
channel samples only its integer atoms `log r`.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

private theorem dl_integrable {f : ℝ → ℝ} {B : ℝ}
    (hf : Continuous f) (hB : ∀ x, |f x| ≤ B) :
    IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ) * f x) (Ioi 1) :=
  (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)).mul_bdd
    hf.aestronglyMeasurable (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hB x))

private def dlCos (a : ℝ) : ℝ :=
  ∫ x in Ioi (1 : ℝ), x ^ (-2 : ℝ) * Real.cos (2 * Real.pi * a * x)

private theorem dl_cos_integrable (a : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ) * Real.cos (2 * Real.pi * a * x)) (Ioi 1) :=
  dl_integrable (by fun_prop) (fun x => Real.abs_cos_le_one _)

private def dlKernel (a b x : ℝ) : ℝ :=
  x ^ (-2 : ℝ) * Real.cos (2 * Real.pi * a * x) * Real.cos (2 * Real.pi * b * x)

private def dlProduct (a b : ℝ) : ℝ := ∫ x in Ioi (1 : ℝ), dlKernel a b x

private theorem dl_product_tendsto {a b u v : ℝ} {s t : ℕ → ℝ}
    (ha : 0 < a) (hb : 0 < b) (hs : Tendsto s atTop (𝓝 u)) (ht : Tendsto t atTop (𝓝 v)) :
    Tendsto (fun n => dlProduct (a * ((n+1 : ℕ) : ℝ) + s n)
      (b * ((n+1 : ℕ) : ℝ) + t n)) atTop
      (𝓝 (if a=b then dlCos (u-v)/2 else 0)) :=
  factorialCriticalCosineProduct_tendsto ha hb hs ht

private theorem dl_kernel_integrable (a b : ℝ) : IntegrableOn (dlKernel a b) (Ioi 1) :=
  (dl_cos_integrable a).mul_bdd (by fun_prop)
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (2 * Real.pi * b * x)))

/-- One translated harmonic layer of a single factorial source. -/
private def dlLayer (n j k : ℕ) (x : ℝ) : ℝ :=
  Real.cos (2 * Real.pi * ((k : ℝ) * factorialShiftedFreq (n+j+1)) * x) -
    Real.cos (2 * Real.pi * ((k : ℝ) * ((n+j+1 : ℕ) : ℝ)) * x)

private def dlCorr (n i j k l : ℕ) (ρ : ℝ) : ℝ :=
  ∫ x in Ioi (1 : ℝ), x ^ (-2 : ℝ) * dlLayer n i k x * dlLayer n j l (ρ * x)

private theorem dl_corr_eq (n i j k l : ℕ) (ρ : ℝ) :
    dlCorr n i j k l ρ =
      dlProduct ((k : ℝ) * factorialShiftedFreq (n+i+1)) ((ρ * l) * factorialShiftedFreq (n+j+1)) -
      dlProduct ((k : ℝ) * factorialShiftedFreq (n+i+1)) ((ρ * l) * ((n+j+1 : ℕ) : ℝ)) -
      dlProduct ((k : ℝ) * ((n+i+1 : ℕ) : ℝ)) ((ρ * l) * factorialShiftedFreq (n+j+1)) +
      dlProduct ((k : ℝ) * ((n+i+1 : ℕ) : ℝ)) ((ρ * l) * ((n+j+1 : ℕ) : ℝ)) := by
  let a : ℝ := (k : ℝ) * factorialShiftedFreq (n+i+1)
  let a₀ : ℝ := (k : ℝ) * ((n+i+1 : ℕ) : ℝ)
  let b : ℝ := (ρ * l) * factorialShiftedFreq (n+j+1)
  let b₀ : ℝ := (ρ * l) * ((n+j+1 : ℕ) : ℝ)
  have heq (x : ℝ) : x ^ (-2 : ℝ) * dlLayer n i k x * dlLayer n j l (ρ * x) =
      ((dlKernel a b x - dlKernel a b₀ x) - dlKernel a₀ b x) + dlKernel a₀ b₀ x := by
    have he (u : ℝ) : 2 * Real.pi * ((l : ℝ) * u) * (ρ * x) =
        2 * Real.pi * ((ρ * l) * u) * x := by ring
    dsimp only [dlLayer, dlKernel, a, a₀, b, b₀]
    rw [he, he]
    ring
  unfold dlCorr
  simp_rw [heq]
  have hadd := integral_add (((dl_kernel_integrable a b).sub (dl_kernel_integrable a b₀)).sub
    (dl_kernel_integrable a₀ b)) (dl_kernel_integrable a₀ b₀)
  have hsub := integral_sub ((dl_kernel_integrable a b).sub (dl_kernel_integrable a b₀))
    (dl_kernel_integrable a₀ b)
  simp only [Pi.sub_apply] at hadd hsub
  rw [hadd, hsub, integral_sub (dl_kernel_integrable a b) (dl_kernel_integrable a b₀)]
  rfl

private def dlDefect (k i j : ℕ) : ℝ :=
  ∫ x in Ioi (1 : ℝ), x ^ (-2 : ℝ) *
    Real.cos (2 * Real.pi * k * ((i : ℝ) - j) * x) * (1 - Real.cos (2 * Real.pi * k * x / 12))

private theorem dl_resonance (a u v : ℝ) :
    dlCos (a*(u+1/12)-a*(v+1/12))/2 - dlCos (a*(u+1/12)-a*v)/2 -
      dlCos (a*u-a*(v+1/12))/2 + dlCos (a*u-a*v)/2 =
    ∫ x in Ioi (1 : ℝ), x ^ (-2 : ℝ) * Real.cos (2 * Real.pi * a * (u-v) * x) *
      (1 - Real.cos (2 * Real.pi * a * x / 12)) := by
  have h₁ := (dl_cos_integrable (a*(u+1/12)-a*(v+1/12))).div_const 2
  have h₂ := (dl_cos_integrable (a*(u+1/12)-a*v)).div_const 2
  have h₃ := (dl_cos_integrable (a*u-a*(v+1/12))).div_const 2
  have h₄ := (dl_cos_integrable (a*u-a*v)).div_const 2
  unfold dlCos
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

/-- Harmonic correlations at a real dilation keep their slow phase exactly on `k = ρ l`. -/
private theorem dl_corr_tendsto (i j : ℕ) {k l : ℕ} {ρ : ℝ}
    (hk : 0 < k) (hl : 0 < l) (hρ : 0 < ρ) :
    Tendsto (fun n => dlCorr n i j k l ρ) atTop
      (𝓝 (if (k : ℝ) = ρ * l then dlDefect k i j else 0)) := by
  let a : ℝ := k
  let b : ℝ := ρ * l
  have ha : 0 < a := by dsimp only [a]; exact_mod_cast hk
  have hb : 0 < b := mul_pos hρ (by exact_mod_cast hl)
  have hs := (factorialShiftedFreq_translated_sub_tendsto i).const_mul a
  have ht := (factorialShiftedFreq_translated_sub_tendsto j).const_mul b
  have hss := dl_product_tendsto ha hb hs ht
  have hsi := dl_product_tendsto ha hb hs (tendsto_const_nhds (x := b * j))
  have his := dl_product_tendsto ha hb (tendsto_const_nhds (x := a * i)) ht
  have hii := dl_product_tendsto ha hb (tendsto_const_nhds (x := a * i))
    (tendsto_const_nhds (x := b * j))
  have h := ((hss.sub hsi).sub his).add hii
  have hval :
      (if a=b then dlCos (a*(i+1/12)-b*(j+1/12))/2 else 0) -
      (if a=b then dlCos (a*(i+1/12)-b*j)/2 else 0) -
      (if a=b then dlCos (a*i-b*(j+1/12))/2 else 0) +
      (if a=b then dlCos (a*i-b*j)/2 else 0) =
      if a=b then dlDefect k i j else 0 := by
    by_cases hab : a=b
    · simp only [← hab, ite_true]
      exact dl_resonance a i j
    · simp only [if_neg hab]
      ring
  change Tendsto _ atTop (𝓝 (_ - _ - _ + _)) at h
  rw [hval] at h
  have heq (n : ℕ) :
      dlCorr n i j k l ρ =
      dlProduct (a * ((n+1 : ℕ) : ℝ) + a * (factorialShiftedFreq (n+i+1) - ((n+1 : ℕ) : ℝ)))
        (b * ((n+1 : ℕ) : ℝ) + b * (factorialShiftedFreq (n+j+1) - ((n+1 : ℕ) : ℝ))) -
      dlProduct (a * ((n+1 : ℕ) : ℝ) + a * (factorialShiftedFreq (n+i+1) - ((n+1 : ℕ) : ℝ)))
        (b * ((n+1 : ℕ) : ℝ) + b*j) -
      dlProduct (a * ((n+1 : ℕ) : ℝ) + a*i)
        (b * ((n+1 : ℕ) : ℝ) + b * (factorialShiftedFreq (n+j+1) - ((n+1 : ℕ) : ℝ))) +
      dlProduct (a * ((n+1 : ℕ) : ℝ) + a*i) (b * ((n+1 : ℕ) : ℝ) + b*j) := by
    have hf (c x : ℝ) : c * ((n+1 : ℕ) : ℝ) + c * (x - ((n+1 : ℕ) : ℝ)) = c*x := by ring
    have hi (c : ℝ) (q : ℕ) : c * ((n+1 : ℕ) : ℝ) + c*q = c * ((n+q+1 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [dl_corr_eq]
    simp only [hf, hi, a, b]
  exact h.congr (fun n => (heq n).symm)

private theorem dl_defect_integrable (k i j : ℕ) :
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
  simpa only [mul_assoc] using dl_integrable (by fun_prop) hbound

private theorem dl_defect_sum_eq_mass (S : Finset ℕ) (b : ℕ → ℝ) (k : ℕ) :
    (∑ i ∈ S, ∑ j ∈ S, b i * b j * dlDefect k i j) =
      factorialCriticalPatternHarmonicMass S b k := by
  classical
  let F (i j : ℕ) (x : ℝ) := b i * b j * (x ^ (-2 : ℝ) *
    Real.cos (2 * Real.pi * k * ((i : ℝ) - j) * x) * (1 - Real.cos (2 * Real.pi * k * x / 12)))
  have hF (i j : ℕ) : IntegrableOn (F i j) (Ioi 1) := (dl_defect_integrable k i j).const_mul _
  have hFi (i : ℕ) : IntegrableOn (fun x => ∑ j ∈ S, F i j x) (Ioi 1) :=
    integrable_finsetSum S (fun j _ => hF i j)
  have hsum : (∫ x in Ioi (1 : ℝ), ∑ i ∈ S, ∑ j ∈ S, F i j x) =
      ∑ i ∈ S, ∑ j ∈ S, ∫ x in Ioi (1 : ℝ), F i j x := by
    rw [integral_finsetSum S (fun i _ => hFi i)]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum S (fun j _ => hF i j)
  have hmass : (∫ x in Ioi (1 : ℝ), ∑ i ∈ S, ∑ j ∈ S, F i j x) =
      factorialCriticalPatternHarmonicMass S b k := by
    unfold factorialCriticalPatternHarmonicMass
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [factorialCriticalPatternDensity_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    dsimp only [F]
    rw [show 2 * Real.pi * ((i : ℝ) - j) * ((k : ℝ) * x) =
      2 * Real.pi * k * ((i : ℝ) - j) * x by ring]
    ring
  have h1 : (∑ i ∈ S, ∑ j ∈ S, b i * b j * dlDefect k i j) =
      ∑ i ∈ S, ∑ j ∈ S, ∫ x in Ioi (1 : ℝ), F i j x := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    dsimp only [F, dlDefect]
    rw [integral_const_mul]
  rw [h1, ← hsum, hmass]

private theorem dl_layer_image (S : Finset ℕ) (b : ℕ → ℝ) (n k : ℕ) (x : ℝ) :
    (factorialHarmonicLayer (S.image (fun j => n+j)) (fun q => (b (q-n) : ℂ)) k x).re =
      ∑ j ∈ S, b j * dlLayer n j k x := by
  classical
  unfold factorialHarmonicLayer
  rw [Finset.sum_image]
  · simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Nat.add_sub_cancel_left, dlLayer, mul_assoc]
  · intro i _ j _ hij
    exact Nat.add_left_cancel hij

private theorem dl_layer_bound (n j k : ℕ) (x : ℝ) : |dlLayer n j k x| ≤ 2 := by
  unfold dlLayer
  have h₁ := Real.abs_cos_le_one (2 * Real.pi * ((k : ℝ) * factorialShiftedFreq (n+j+1)) * x)
  have h₂ := Real.abs_cos_le_one (2 * Real.pi * ((k : ℝ) * ((n+j+1 : ℕ) : ℝ)) * x)
  exact (abs_sub _ _).trans (by linarith)

private theorem dl_pair_integrable (n i j k l : ℕ) (ρ : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ) * dlLayer n i k x * dlLayer n j l (ρ * x)) (Ioi 1) := by
  have hbound (x : ℝ) : |dlLayer n i k x * dlLayer n j l (ρ * x)| ≤ 4 := by
    rw [abs_mul]
    exact (mul_le_mul (dl_layer_bound n i k x) (dl_layer_bound n j l (ρ * x))
      (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hc : Continuous (fun x : ℝ => dlLayer n i k x * dlLayer n j l (ρ * x)) := by
    unfold dlLayer; fun_prop
  simpa only [mul_assoc] using dl_integrable hc hbound

/-- Translated harmonic layers at a real dilation keep the pattern mass on `k = ρ l`. -/
theorem factorialCriticalTranslatedHarmonicDilation_tendsto
    (S : Finset ℕ) (b : ℕ → ℝ) (k l : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun n => ∫ x in Ioi (1 : ℝ), x ^ (-2 : ℝ) *
      (factorialHarmonicLayer (S.image (fun j => n+j)) (fun q => (b (q-n) : ℂ)) k x).re *
      (factorialHarmonicLayer (S.image (fun j => n+j)) (fun q => (b (q-n) : ℂ)) l (ρ * x)).re)
      atTop (𝓝 (if (k : ℝ) = ρ * l then factorialCriticalPatternHarmonicMass S b k else 0)) := by
  classical
  have h0 : factorialCriticalPatternHarmonicMass S b 0 = 0 := by
    simp [factorialCriticalPatternHarmonicMass]
  by_cases hk : k = 0
  · subst k
    rw [show (if ((0 : ℕ) : ℝ) = ρ * l then factorialCriticalPatternHarmonicMass S b 0 else 0) = 0 by
      split_ifs <;> simp [h0]]
    simp [factorialHarmonicLayer]
  by_cases hl : l = 0
  · subst l
    have hne : (k : ℝ) ≠ ρ * ((0 : ℕ) : ℝ) := by
      simp only [Nat.cast_zero, mul_zero]; exact_mod_cast hk
    rw [if_neg hne]
    simp [factorialHarmonicLayer]
  have hpat := tendsto_finsetSum S (fun i _ => tendsto_finsetSum S (fun j _ =>
    (dl_corr_tendsto i j (Nat.pos_of_ne_zero hk) (Nat.pos_of_ne_zero hl) hρ).const_mul (b i * b j)))
  have hv : (∑ i ∈ S, ∑ j ∈ S, b i * b j * (if (k : ℝ) = ρ * l then dlDefect k i j else 0)) =
      if (k : ℝ) = ρ * l then factorialCriticalPatternHarmonicMass S b k else 0 := by
    by_cases hres : (k : ℝ) = ρ * l
    · simp only [if_pos hres]; exact dl_defect_sum_eq_mass S b k
    · simp only [if_neg hres, mul_zero, Finset.sum_const_zero]
  rw [hv] at hpat
  refine hpat.congr fun n => ?_
  simp only [dl_layer_image]
  let F (i j : ℕ) (x : ℝ) := b i * b j * (x ^ (-2 : ℝ) * dlLayer n i k x * dlLayer n j l (ρ * x))
  have hF (i j : ℕ) : IntegrableOn (F i j) (Ioi 1) := (dl_pair_integrable n i j k l ρ).const_mul _
  have heq (x : ℝ) : x ^ (-2 : ℝ) * (∑ i ∈ S, b i * dlLayer n i k x) *
      (∑ j ∈ S, b j * dlLayer n j l (ρ * x)) = ∑ i ∈ S, ∑ j ∈ S, F i j x := by
    rw [mul_assoc, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    dsimp only [F]; ring
  simp_rw [heq]
  rw [integral_finsetSum S (fun i _ => integrable_finsetSum S (fun j _ => hF i j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum S (fun j _ => hF i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  dsimp only [F, dlCorr]
  rw [integral_const_mul]

private def dlPatLayer (S : Finset ℕ) (b : ℕ → ℝ) (n k : ℕ) (v : ℝ) : ℝ :=
  (factorialHarmonicLayer (S.image (fun j => n+j)) (fun q => (b (q-n) : ℂ)) k v).re

private def dlPhase (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) (v : ℝ) : ℝ :=
  (factorialPhaseCombination (S.image (fun j => n+j)) (fun q => (b (q-n) : ℂ)) v).re

private theorem dl_norm_sum (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) :
    (∑ q ∈ S.image (fun j => n+j), ‖(b (q-n) : ℂ)‖) = ∑ j ∈ S, |b j| := by
  classical
  rw [Finset.sum_image]
  · simp only [Nat.add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
  · intro i _ j _ hij
    exact Nat.add_left_cancel hij

private theorem dl_pat_layer_bound (S : Finset ℕ) (b : ℕ → ℝ) (n k : ℕ) (v : ℝ) :
    |dlPatLayer S b n k v| ≤ 2 * ∑ j ∈ S, |b j| := by
  have h := (Complex.abs_re_le_norm _).trans
    (norm_factorialHarmonicLayer_le (S.image (fun j => n+j)) (fun q => (b (q-n) : ℂ)) k v)
  rwa [dl_norm_sum] at h

private theorem dl_pat_layer_continuous (S : Finset ℕ) (b : ℕ → ℝ) (n k : ℕ) :
    Continuous (dlPatLayer S b n k) :=
  Complex.continuous_re.comp (continuous_factorialHarmonicLayer _ _ _)

private theorem dl_pat_layer_hasSum (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) (v : ℝ) :
    HasSum (fun k => dyadicHarmonicWeight k * dlPatLayer S b n k v)
      (-(Real.pi ^ 2 / 2) * dlPhase S b n v) := by
  have h := Complex.hasSum_re (factorialPhaseCombination_hasSum
    (S.image (fun j => n+j)) (fun q => (b (q-n) : ℂ)) v)
  simpa only [dlPatLayer, dlPhase, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, zero_mul,
    sub_zero] using h

private theorem dl_pair_summable (S : Finset ℕ) (b : ℕ → ℝ) :
    Summable (fun p : ℕ × ℕ => (|dyadicHarmonicWeight p.1| * |dyadicHarmonicWeight p.2|) *
      (4 * (∑ j ∈ S, |b j|) ^ 2)) :=
  (summable_abs_dyadicHarmonicWeight.mul_of_nonneg summable_abs_dyadicHarmonicWeight
    (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)).mul_right _

private theorem dl_pair_bound (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) (ρ : ℝ) (p : ℕ × ℕ) (v : ℝ) :
    |(dyadicHarmonicWeight p.1 * dlPatLayer S b n p.1 v) *
      (dyadicHarmonicWeight p.2 * dlPatLayer S b n p.2 (ρ * v))| ≤
      (|dyadicHarmonicWeight p.1| * |dyadicHarmonicWeight p.2|) * (4 * (∑ j ∈ S, |b j|) ^ 2) := by
  have h := mul_le_mul (dl_pat_layer_bound S b n p.1 v) (dl_pat_layer_bound S b n p.2 (ρ * v))
    (abs_nonneg _) (by positivity)
  calc _ = (|dyadicHarmonicWeight p.1| * |dyadicHarmonicWeight p.2|) *
      (|dlPatLayer S b n p.1 v| * |dlPatLayer S b n p.2 (ρ * v)|) := by simp only [abs_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (h.trans_eq (by ring)) (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- The critical physical correlation of a translated pattern at an arbitrary real dilation `ρ`. -/
def factorialCriticalTranslatedDilationCorrelation (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) (ρ : ℝ) : ℝ :=
  ∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) *
    (factorialPhaseCombination (S.image (fun j => n+j)) (fun q => (b (q-n) : ℂ)) v).re *
    (factorialPhaseCombination (S.image (fun j => n+j)) (fun q => (b (q-n) : ℂ)) (ρ * v)).re

/-- The resonance sum at a real dilation: only pairs `k = ρ l` survive. -/
def factorialCriticalDilationLimit (S : Finset ℕ) (b : ℕ → ℝ) (ρ : ℝ) : ℝ :=
  (4 / Real.pi ^ 4) * ∑' p : ℕ × ℕ, if (p.1 : ℝ) = ρ * p.2 then
    dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2 *
      factorialCriticalPatternHarmonicMass S b p.1 else 0

private theorem dl_correlation_hasSum (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) (ρ : ℝ) :
    HasSum (fun p : ℕ × ℕ => dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2 *
      ∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) * dlPatLayer S b n p.1 v * dlPatLayer S b n p.2 (ρ * v))
      ((Real.pi ^ 4 / 4) * factorialCriticalTranslatedDilationCorrelation S b n ρ) := by
  let F (p : ℕ × ℕ) (v : ℝ) := v ^ (-2 : ℝ) *
    ((dyadicHarmonicWeight p.1 * dlPatLayer S b n p.1 v) *
      (dyadicHarmonicWeight p.2 * dlPatLayer S b n p.2 (ρ * v)))
  let B (p : ℕ × ℕ) := (|dyadicHarmonicWeight p.1| * |dyadicHarmonicWeight p.2|) *
    (4 * (∑ j ∈ S, |b j|) ^ 2)
  let f (v : ℝ) := v ^ (-2 : ℝ) *
    ((-(Real.pi ^ 2 / 2) * dlPhase S b n v) * (-(Real.pi ^ 2 / 2) * dlPhase S b n (ρ * v)))
  have hw : IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hs (v : ℝ) : Summable (fun p : ℕ × ℕ =>
      (dyadicHarmonicWeight p.1 * dlPatLayer S b n p.1 v) *
        (dyadicHarmonicWeight p.2 * dlPatLayer S b n p.2 (ρ * v))) :=
    (dl_pair_summable S b).of_norm_bounded (fun p => by rw [Real.norm_eq_abs]; exact dl_pair_bound S b n ρ p v)
  have h := hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi (1 : ℝ))) (F := F) (f := f)
    (fun p v => B p * v ^ (-2 : ℝ))
    (fun p => hw.aestronglyMeasurable.mul
      (((dl_pat_layer_continuous S b n p.1).const_mul _).mul
        (((dl_pat_layer_continuous S b n p.2).comp
          (continuous_const.mul continuous_id)).const_mul _)).aestronglyMeasurable)
    (by
      intro p
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hw0 : 0 ≤ v ^ (-2 : ℝ) := Real.rpow_nonneg (le_trans zero_le_one (le_of_lt hv)) _
      dsimp only [F, B]
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hw0, Real.norm_eq_abs]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (dl_pair_bound S b n ρ p v) hw0)
    (Eventually.of_forall fun v => (dl_pair_summable S b).mul_right (v ^ (-2 : ℝ)))
    (by
      have hi := hw.const_mul (∑' p, B p)
      simpa only [tsum_mul_right] using hi)
    (Eventually.of_forall fun v =>
      ((dl_pat_layer_hasSum S b n v).mul (dl_pat_layer_hasSum S b n (ρ * v)) (hs v)).mul_left (v ^ (-2 : ℝ)))
  have hfun : HasSum (fun p : ℕ × ℕ => dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2 *
      ∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) * dlPatLayer S b n p.1 v * dlPatLayer S b n p.2 (ρ * v))
      (∫ v in Ioi (1 : ℝ), f v) := by
    refine h.congr_fun (fun p => ?_)
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with v
    dsimp only [F]
    ring
  have hval : (∫ v in Ioi (1 : ℝ), f v) =
      (Real.pi ^ 4 / 4) * factorialCriticalTranslatedDilationCorrelation S b n ρ := by
    unfold factorialCriticalTranslatedDilationCorrelation
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with v
    dsimp only [f, dlPhase]
    ring
  rwa [hval] at hfun

/-- **Real dilation law.** At every real dilation `ρ > 0` the complete critical correlation of
a translated pattern converges to the resonance sum over pairs `k = ρ l`. -/
theorem factorialCriticalTranslatedDilationCorrelation_tendsto (S : Finset ℕ) (b : ℕ → ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun n => factorialCriticalTranslatedDilationCorrelation S b n ρ) atTop
      (𝓝 (factorialCriticalDilationLimit S b ρ)) := by
  let g (p : ℕ × ℕ) := if (p.1 : ℝ) = ρ * p.2 then dyadicHarmonicWeight p.1 *
    dyadicHarmonicWeight p.2 * factorialCriticalPatternHarmonicMass S b p.1 else 0
  have hpair (p : ℕ × ℕ) : Tendsto (fun n => dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2 *
      ∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) * dlPatLayer S b n p.1 v * dlPatLayer S b n p.2 (ρ * v))
      atTop (𝓝 (g p)) := by
    have h := (factorialCriticalTranslatedHarmonicDilation_tendsto S b p.1 p.2 hρ).const_mul
      (dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2)
    simpa only [dlPatLayer, mul_ite, mul_zero, g] using h
  have hbound (n : ℕ) (p : ℕ × ℕ) : ‖dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2 *
      ∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) * dlPatLayer S b n p.1 v * dlPatLayer S b n p.2 (ρ * v)‖ ≤
      (|dyadicHarmonicWeight p.1| * |dyadicHarmonicWeight p.2|) * (4 * (∑ j ∈ S, |b j|) ^ 2) := by
    have hc1 := dl_pat_layer_continuous S b n p.1
    have hc2 := dl_pat_layer_continuous S b n p.2
    have hint := dl_integrable (B := 4 * (∑ j ∈ S, |b j|) ^ 2)
      (f := fun v => dlPatLayer S b n p.1 v * dlPatLayer S b n p.2 (ρ * v)) (by fun_prop)
      (fun v => by
        rw [abs_mul]
        exact (mul_le_mul (dl_pat_layer_bound S b n p.1 v) (dl_pat_layer_bound S b n p.2 (ρ * v))
          (abs_nonneg _) (by positivity)).trans_eq (by ring))
    have hmass : (∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ)) = 1 := by
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one]; norm_num
    have hI : |∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) * dlPatLayer S b n p.1 v * dlPatLayer S b n p.2 (ρ * v)| ≤
        4 * (∑ j ∈ S, |b j|) ^ 2 := by
      calc _ ≤ ∫ v in Ioi (1 : ℝ), 4 * (∑ j ∈ S, |b j|) ^ 2 * v ^ (-2 : ℝ) := by
            rw [← Real.norm_eq_abs]
            have hn : IntegrableOn (fun v => ‖v ^ (-2 : ℝ) * dlPatLayer S b n p.1 v *
                dlPatLayer S b n p.2 (ρ * v)‖) (Ioi 1) := by
              have := hint.norm
              simp only [mul_assoc] at this ⊢
              exact this
            refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on hn
              ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one).const_mul _)
              measurableSet_Ioi fun v hv => ?_)
            have hw0 : 0 ≤ v ^ (-2 : ℝ) := Real.rpow_nonneg (le_trans zero_le_one (le_of_lt hv)) _
            rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg hw0, abs_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right ((mul_le_mul (dl_pat_layer_bound S b n p.1 v)
              (dl_pat_layer_bound S b n p.2 (ρ * v)) (abs_nonneg _) (by positivity)).trans_eq (by ring)) hw0
        _ = _ := by rw [integral_const_mul, hmass, mul_one]
    simp only [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hI (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have h := tendsto_tsum_of_dominated_convergence (dl_pair_summable S b) hpair
    (Eventually.of_forall fun n p => hbound n p)
  have hscaled := h.const_mul (4 / Real.pi ^ 4)
  refine hscaled.congr fun n => ?_
  rw [(dl_correlation_hasSum S b n ρ).tsum_eq]
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **Non-resonant decorrelation.** At an irrational dilation no harmonic pair resonates and the
limiting critical correlation vanishes. -/
theorem factorialCriticalDilationLimit_eq_zero_of_irrational (S : Finset ℕ) (b : ℕ → ℝ) {ρ : ℝ}
    (hρ : Irrational ρ) : factorialCriticalDilationLimit S b ρ = 0 := by
  unfold factorialCriticalDilationLimit
  have hz : ∀ p : ℕ × ℕ, (if (p.1 : ℝ) = ρ * p.2 then dyadicHarmonicWeight p.1 *
      dyadicHarmonicWeight p.2 * factorialCriticalPatternHarmonicMass S b p.1 else 0) = 0 := by
    intro p
    split_ifs with h
    · rcases Nat.eq_zero_or_pos p.2 with h2 | h2
      · have : (p.1 : ℝ) = 0 := by rw [h, h2]; simp
        have hp1 : p.1 = 0 := by exact_mod_cast this
        simp [hp1, dyadicHarmonicWeight]
      · exfalso
        have h2R : (p.2 : ℝ) ≠ 0 := by exact_mod_cast h2.ne'
        apply hρ
        refine ⟨(p.1 : ℚ) / p.2, ?_⟩
        push_cast
        field_simp
        linarith
    · rfl
  simp only [hz, tsum_zero, mul_zero]

/-- **Rational resonance law.** At a reduced rational dilation `p/q` the limiting critical
correlation is the resonance series `(4/π⁴) Σ_t w_{pt} w_{qt} J_{pt}(b)`. -/
theorem factorialCriticalDilationLimit_rat (S : Finset ℕ) (b : ℕ → ℝ) {p q : ℕ} (hp : 0 < p)
    (hq : 0 < q) (hpq : Nat.Coprime p q) :
    factorialCriticalDilationLimit S b ((p : ℝ) / q) = (4 / Real.pi ^ 4) * ∑' t : ℕ,
      dyadicHarmonicWeight (p * t) * dyadicHarmonicWeight (q * t) *
        factorialCriticalPatternHarmonicMass S b (p * t) := by
  unfold factorialCriticalDilationLimit
  congr 1
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hres (k l : ℕ) : (k : ℝ) = (p : ℝ) / q * l ↔ k * q = p * l := by
    rw [div_mul_eq_mul_div, eq_div_iff hqR]; exact_mod_cast Iff.rfl
  have hinj : Function.Injective fun t : ℕ => (p * t, q * t) := by
    intro a c h
    simp only [Prod.mk.injEq] at h
    exact Nat.eq_of_mul_eq_mul_left hp h.1
  set F : ℕ × ℕ → ℝ := fun x => if (x.1 : ℝ) = (p : ℝ) / q * x.2 then dyadicHarmonicWeight x.1 *
    dyadicHarmonicWeight x.2 * factorialCriticalPatternHarmonicMass S b x.1 else 0
  have hsupp : Function.support F ⊆ Set.range fun t : ℕ => (p * t, q * t) := by
    intro x hx
    simp only [Function.mem_support, F, ne_eq] at hx
    split_ifs at hx with h
    · rw [hres] at h
      have hdvd : q ∣ x.2 := by
        have : q ∣ p * x.2 := ⟨x.1, by rw [← h]; ring⟩
        exact hpq.symm.dvd_of_dvd_mul_left this
      obtain ⟨t, ht⟩ := hdvd
      refine ⟨t, ?_⟩
      have h1 : x.1 = p * t := by
        rw [ht] at h
        have : x.1 * q = p * t * q := by rw [h]; ring
        exact Nat.eq_of_mul_eq_mul_right hq this
      ext <;> simp [h1, ht]
    · exact absurd rfl hx
  rw [← hinj.tsum_eq hsupp]
  refine tsum_congr fun t => ?_
  simp only [F]
  rw [if_pos ((hres _ _).mpr (by ring))]

/-- **Critical autocorrelation spectrum.** At every shift `x > 0` the autocorrelation of the
translated critical source converges to `e^{-x/2}` times the dilation limit at `e^x`. -/
theorem criticalFactorialSource_translated_autocorrelation_tendsto (S : Finset ℕ) (b : ℕ → ℝ)
    {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => ∫ y : ℝ, criticalFactorialSource (S.image (fun j => n+j)) (fun q => b (q-n)) y *
      criticalFactorialSource (S.image (fun j => n+j)) (fun q => b (q-n)) (y - x)) atTop
      (𝓝 (Real.exp (-(x / 2)) * factorialCriticalDilationLimit S b (Real.exp x))) := by
  have hr : 1 ≤ Real.exp x := Real.one_le_exp hx
  have hsq : (Real.sqrt (Real.exp x))⁻¹ = Real.exp (-(x / 2)) := by
    rw [show Real.exp x = Real.exp (x / 2) ^ 2 by rw [← Real.exp_nat_mul]; ring_nf,
      Real.sqrt_sq (Real.exp_pos _).le, Real.exp_neg]
  have h := (factorialCriticalTranslatedDilationCorrelation_tendsto S b (Real.exp_pos x)).const_mul
    (Real.exp (-(x / 2)))
  refine h.congr fun n => ?_
  have hc := criticalFactorialSource_correlation_eq (S.image (fun j => n+j)) (fun q => b (q-n)) hr
  rw [Real.log_exp, hsq] at hc
  rw [hc]
  rfl

/-- At every shift `x > 0` with `e^x` irrational the limiting critical autocorrelation vanishes. -/
theorem criticalFactorialSource_translated_autocorrelation_tendsto_zero (S : Finset ℕ) (b : ℕ → ℝ)
    {x : ℝ} (hx : 0 ≤ x) (hirr : Irrational (Real.exp x)) :
    Tendsto (fun n => ∫ y : ℝ, criticalFactorialSource (S.image (fun j => n+j)) (fun q => b (q-n)) y *
      criticalFactorialSource (S.image (fun j => n+j)) (fun q => b (q-n)) (y - x)) atTop (𝓝 0) := by
  have h := criticalFactorialSource_translated_autocorrelation_tendsto S b hx
  rwa [factorialCriticalDilationLimit_eq_zero_of_irrational S b hirr, mul_zero] at h

end GaloisForLFunctions.ArithmeticPositivityTheory
