import GaloisForLFunctions.RHTower.ChiRamanujanGlobalResidueControl

/-!
# Polynomial complex neighborhoods of the actual BAG sources

The full Euler corrections are bounded on their normal-convergence tubes.
The actual pole-removed cubic and axis sources have polynomial bounds on
complex balls of polynomially shrinking radius, uniformly through damping one.
-/

noncomputable section
open Set Filter Metric
open scoped BigOperators Topology
namespace RHTower.BAGTrace

private theorem norm_hasProd_le_exp {ι : Type*} {f : ι → ℂ} {a : ℂ} {b : ι → ℝ}
    (hf : HasProd f a) (hb : Summable b) (hb0 : ∀ i, 0 ≤ b i)
    (hbound : ∀ i, ‖f i-1‖ ≤ b i) : ‖a‖ ≤ Real.exp (∑' i, b i) := by
  apply le_of_tendsto hf.norm
  apply Filter.Eventually.of_forall
  intro P
  calc
    (∏ i ∈ P, ‖f i‖) ≤ ∏ i ∈ P, (1+b i) := Finset.prod_le_prod (fun _ _ => norm_nonneg _) (by
      intro i hi
      have h := norm_add_le (f i-1) (1 : ℂ)
      simp only [sub_add_cancel,norm_one] at h
      linarith [hbound i])
    _ ≤ Real.exp (∑ i ∈ P, b i) := Real.prod_one_add_le_exp_sum P hb0
    _ ≤ Real.exp (∑' i, b i) := Real.exp_le_exp.mpr (hb.sum_le_tsum P (fun i _ => hb0 i))

/-- The actual normal Euler correction is bounded over the entire complex tube. -/
theorem exists_cubicEulerCorrection_bound :
    ∃ H > 0, ∀ σ α β : ℂ, (σ,α,β) ∈ cubicTube → ‖cubicEulerCorrection σ α β‖ ≤ H := by
  let b : Nat.Primes → ℝ := fun p => cubicMajorant*(p : ℝ)^(-(3/2) : ℝ)
  have hpow : Summable (fun p : Nat.Primes => (p : ℝ)^(-(3/2) : ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-(3/2) : ℝ) < -1)).subtype Nat.Prime
  have hb : Summable b := hpow.mul_left cubicMajorant
  have hb0 : ∀ p, 0 ≤ b p := by intro p; dsimp [b,cubicMajorant]; positivity
  refine ⟨Real.exp (∑' p, b p),Real.exp_pos _,?_⟩
  intro σ α β h
  exact norm_hasProd_le_exp (f := fun p => cubicPrimeFactor p σ α β) (a := cubicEulerCorrection σ α β) (b := b)
    (hasProdLocallyUniformlyOn_cubicPrimeFactor.hasProd (x := (σ,α,β)) h) hb hb0
    (fun p => norm_cubicPrimeFactor_sub_one_le p (σ := σ) (α := α) (β := β) h.1.le h.2.1.le h.2.2.le)

/-- The actual axis Euler correction is likewise uniformly bounded on its tube. -/
theorem exists_axisEulerCorrection_bound :
    ∃ H > 0, ∀ σ α : ℂ, (σ,α) ∈ axisTube → ‖axisEulerCorrection σ α‖ ≤ H := by
  let b : Nat.Primes → ℝ := fun p => axisMajorant*(p : ℝ)^(-(13/8) : ℝ)
  have hpow : Summable (fun p : Nat.Primes => (p : ℝ)^(-(13/8) : ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-(13/8) : ℝ) < -1)).subtype Nat.Prime
  have hb : Summable b := hpow.mul_left axisMajorant
  have hb0 : ∀ p, 0 ≤ b p := by intro p; dsimp [b,axisMajorant]; positivity
  refine ⟨Real.exp (∑' p, b p),Real.exp_pos _,?_⟩
  intro σ α h
  exact norm_hasProd_le_exp (f := fun p => axisPrimeFactor p σ α) (a := axisEulerCorrection σ α) (b := b)
    (hasProdLocallyUniformlyOn_axisPrimeFactor.hasProd (x := (σ,α)) h) hb hb0
    (fun p => norm_axisPrimeFactor_sub_one_le p (σ := σ) (α := α) h.1.le h.2.le)

private theorem residue_control_on_common_disk {c M : ℝ} (hc : 0 < c) (hM : 0 < M)
    (hdisks : ∀ σ ∈ Icc (1 : ℝ) 2, ∀ t : ℝ,
      ∀ z ∈ closedBall ((σ : ℂ)+(t : ℂ)*Complex.I) (c/(1+|t|)^9),
        zetaResidueFactor z ≠ 0 ∧ ‖zetaResidueFactor z‖ ≤ M*(1+|t|)^9 ∧
        ‖(zetaResidueFactor z)⁻¹‖ ≤ M*(1+|t|)^9)
    {σ t T : ℝ} (hσ : σ ∈ Icc (1 : ℝ) 2) (hT : 1+|t| ≤ T)
    {z : ℂ} (hz : ‖z-((σ : ℂ)+(t : ℂ)*Complex.I)‖ ≤ c/T^9) :
    zetaResidueFactor z ≠ 0 ∧ ‖zetaResidueFactor z‖ ≤ M*T^9 ∧
      ‖(zetaResidueFactor z)⁻¹‖ ≤ M*T^9 := by
  have hp : (1+|t|)^9 ≤ T^9 := pow_le_pow_left₀ (by positivity) hT 9
  have hr : c/T^9 ≤ c/(1+|t|)^9 := div_le_div₀ hc.le (le_refl _) (by positivity) hp
  have h := hdisks σ hσ t z (by simpa only [mem_closedBall,dist_eq_norm] using hz.trans hr)
  have hm := mul_le_mul_of_nonneg_left hp hM.le
  exact ⟨h.1,h.2.1.trans hm,h.2.2.trans hm⟩

private theorem residuePair_control_on_common_disk {c M : ℝ} (hc : 0 < c) (hM : 0 < M)
    (hdisks : ∀ σ ∈ Icc (1 : ℝ) 2, ∀ t : ℝ,
      ∀ z ∈ closedBall ((σ : ℂ)+(t : ℂ)*Complex.I) (c/(1+|t|)^9),
        zetaResidueFactor z ≠ 0 ∧ ‖zetaResidueFactor z‖ ≤ M*(1+|t|)^9 ∧
        ‖(zetaResidueFactor z)⁻¹‖ ≤ M*(1+|t|)^9)
    {σ t T r : ℝ} (hσ : σ ∈ Icc (1 : ℝ) 2) (hT : 1+|t| ≤ T)
    (hr : 3*r ≤ c/T^9) {s a : ℂ}
    (hs : ‖s-(σ : ℂ)‖ ≤ r) (ha : ‖a-(t : ℂ)*Complex.I‖ ≤ 2*r) :
    residuePair s a ≠ 0 ∧ ‖residuePair s a‖ ≤ (M*T^9)^2 ∧
      ‖(residuePair s a)⁻¹‖ ≤ (M*T^9)^2 := by
  have hp : ‖(s+a)-((σ : ℂ)+(t : ℂ)*Complex.I)‖ ≤ c/T^9 := by
    calc
      _ = ‖(s-(σ : ℂ))+(a-(t : ℂ)*Complex.I)‖ := by congr 1; ring
      _ ≤ ‖s-(σ : ℂ)‖+‖a-(t : ℂ)*Complex.I‖ := norm_add_le _ _
      _ ≤ c/T^9 := (by linarith : ‖s-(σ : ℂ)‖+‖a-(t : ℂ)*Complex.I‖ ≤ 3*r).trans hr
  have hm : ‖(s-a)-((σ : ℂ)+((-t : ℝ) : ℂ)*Complex.I)‖ ≤ c/T^9 := by
    calc
      _ = ‖(s-(σ : ℂ))-(a-(t : ℂ)*Complex.I)‖ := by push_cast; congr 1; ring
      _ ≤ ‖s-(σ : ℂ)‖+‖a-(t : ℂ)*Complex.I‖ := norm_sub_le _ _
      _ ≤ c/T^9 := (by linarith : ‖s-(σ : ℂ)‖+‖a-(t : ℂ)*Complex.I‖ ≤ 3*r).trans hr
  have hP := residue_control_on_common_disk hc hM hdisks hσ hT hp
  have hN := residue_control_on_common_disk hc hM hdisks hσ (by simpa using hT) hm
  refine ⟨mul_ne_zero hP.1 hN.1,?_,?_⟩
  · simpa only [residuePair,norm_mul,pow_two] using
      mul_le_mul hP.2.1 hN.2.1 (norm_nonneg _) (le_trans (norm_nonneg _) hP.2.1)
  · simpa only [residuePair,mul_inv,norm_mul,pow_two] using
      mul_le_mul hP.2.2 hN.2.2 (norm_nonneg _) (le_trans (norm_nonneg _) hP.2.2)

/-- Actual cubic source: polynomial-size bounds on complex balls with polynomial radius,
uniform in the closed damping strip. The balls lie inside the actual analytic domain. -/
theorem exists_regularCubicSource_polynomial_balls :
    ∃ d ∈ Ioc (0 : ℝ) 1, ∃ C > 0, ∀ σ ∈ Icc (1 : ℝ) 2, ∀ u v : ℝ,
      ∀ w ∈ closedBall (![σ,(u : ℂ)*Complex.I,(v : ℂ)*Complex.I] : Fin 3 → ℂ)
        (d/(1+|u|+|v|)^9),
        w ∈ cubicRegularDomain ∧
        ‖regularCubicSource (w 0) (w 1) (w 2)‖ ≤ C*(1+|u|+|v|)^54 := by
  obtain ⟨c,hc,M,hM,hdisks⟩ := exists_residue_global_polynomial_disks
  obtain ⟨H,hH,hHbound⟩ := exists_cubicEulerCorrection_bound
  let d := min (c/3) (1/32)
  let C := H*M^6
  have hd : 0 < d := lt_min (div_pos hc.1 (by norm_num)) (by norm_num)
  have hd32 : d ≤ 1/32 := min_le_right _ _
  have hdc : 3*d ≤ c := by have := min_le_left (c/3) (1/32); dsimp [d]; linarith
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨d,⟨hd,by linarith⟩,C,hC,?_⟩
  intro σ hσ u v w hw
  let T := 1+|u|+|v|
  let r := d/T^9
  have hT1 : 1 ≤ T := by dsimp [T]; linarith [abs_nonneg u,abs_nonneg v]
  have hT : 0 < T := zero_lt_one.trans_le hT1
  have hr : 0 ≤ r := (div_pos hd (pow_pos hT 9)).le
  have hr32 : r ≤ 1/32 := (div_le_self hd.le (one_le_pow₀ hT1)).trans hd32
  have hrC : 3*r ≤ c/T^9 := by
    dsimp [r]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hdc (pow_nonneg hT.le 9)
  have hw' : ‖w-(![σ,(u : ℂ)*Complex.I,(v : ℂ)*Complex.I] : Fin 3 → ℂ)‖ ≤ r := by
    simpa only [mem_closedBall,dist_eq_norm] using hw
  have hw0 : ‖w 0-(σ : ℂ)‖ ≤ r := by
    simpa using (norm_le_pi_norm (w-![(σ : ℂ),(u : ℂ)*Complex.I,(v : ℂ)*Complex.I]) 0).trans hw'
  have hw1 : ‖w 1-(u : ℂ)*Complex.I‖ ≤ r := by
    simpa using (norm_le_pi_norm (w-![(σ : ℂ),(u : ℂ)*Complex.I,(v : ℂ)*Complex.I]) 1).trans hw'
  have hw2 : ‖w 2-(v : ℂ)*Complex.I‖ ≤ r := by
    simpa using (norm_le_pi_norm (w-![(σ : ℂ),(u : ℂ)*Complex.I,(v : ℂ)*Complex.I]) 2).trans hw'
  have hw12 : ‖(w 1-w 2)-((u-v : ℝ) : ℂ)*Complex.I‖ ≤ 2*r := by
    calc
      _ = ‖(w 1-(u : ℂ)*Complex.I)-(w 2-(v : ℂ)*Complex.I)‖ := by push_cast; congr 1; ring
      _ ≤ ‖w 1-(u : ℂ)*Complex.I‖+‖w 2-(v : ℂ)*Complex.I‖ := norm_sub_le _ _
      _ ≤ 2*r := by linarith
  have hU := residuePair_control_on_common_disk hc.1 hM hdisks hσ
    (show 1+|u| ≤ T by dsimp [T]; linarith [abs_nonneg v]) hrC hw0 (hw1.trans (by linarith))
  have hV := residuePair_control_on_common_disk hc.1 hM hdisks hσ
    (show 1+|v| ≤ T by dsimp [T]; linarith [abs_nonneg u]) hrC hw0 (hw2.trans (by linarith))
  have hUV := residuePair_control_on_common_disk hc.1 hM hdisks hσ
    (show 1+|u-v| ≤ T by
      have hh := norm_sub_le u v
      simp only [Real.norm_eq_abs] at hh
      dsimp [T]; linarith) hrC hw0 hw12
  have h0re : |(w 0).re-σ| ≤ r := by
    simpa using (Complex.abs_re_le_norm (w 0-(σ : ℂ))).trans hw0
  have h1re : |(w 1).re| ≤ r := by
    simpa using (Complex.abs_re_le_norm (w 1-(u : ℂ)*Complex.I)).trans hw1
  have h2re : |(w 2).re| ≤ r := by
    simpa using (Complex.abs_re_le_norm (w 2-(v : ℂ)*Complex.I)).trans hw2
  have htube : (w 0,w 1,w 2) ∈ cubicTube :=
    ⟨by linarith [(abs_le.mp h0re).1,hσ.1],by linarith,by linarith⟩
  refine ⟨⟨htube,hUV.1⟩,?_⟩
  have hh := hHbound (w 0) (w 1) (w 2) htube
  change ‖residuePair (w 0) (w 1)*residuePair (w 0) (w 2)*
    cubicEulerCorrection (w 0) (w 1) (w 2)/residuePair (w 0) (w 1-w 2)‖ ≤ _
  rw [div_eq_mul_inv,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ ((M*T^9)^2*(M*T^9)^2)*H*(M*T^9)^2 :=
      mul_le_mul (mul_le_mul (mul_le_mul hU.2.1 hV.2.1 (norm_nonneg _) (by positivity))
        hh (norm_nonneg _) (by positivity)) hUV.2.2 (norm_nonneg _) (by positivity)
    _ = C*T^54 := by
      have hid (X Y Z : ℝ) : (X*Y^9)^2*(X*Y^9)^2*Z*(X*Y^9)^2 = Z*X^6*Y^54 := by ring
      exact hid M T H

/-- Actual axis source on uniform polynomial-radius complex balls. -/
theorem exists_regularAxisSource_polynomial_balls :
    ∃ d ∈ Ioc (0 : ℝ) 1, ∃ C > 0, ∀ σ ∈ Icc (1 : ℝ) 2, ∀ u : ℝ,
      ∀ w ∈ closedBall (![σ,(u : ℂ)*Complex.I] : Fin 2 → ℂ) (d/(1+|u|)^9),
        w ∈ axisCoordinateTube ∧ ‖regularAxisSource (w 0) (w 1)‖ ≤ C*(1+|u|)^18 := by
  obtain ⟨c,hc,M,hM,hdisks⟩ := exists_residue_global_polynomial_disks
  obtain ⟨H,hH,hHbound⟩ := exists_axisEulerCorrection_bound
  let d := min (c/3) (1/32)
  let C := H*M^2
  have hd : 0 < d := lt_min (div_pos hc.1 (by norm_num)) (by norm_num)
  have hd32 : d ≤ 1/32 := min_le_right _ _
  have hdc : 3*d ≤ c := by have := min_le_left (c/3) (1/32); dsimp [d]; linarith
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨d,⟨hd,by linarith⟩,C,hC,?_⟩
  intro σ hσ u w hw
  let T := 1+|u|
  let r := d/T^9
  have hT1 : 1 ≤ T := by dsimp [T]; linarith [abs_nonneg u]
  have hT : 0 < T := zero_lt_one.trans_le hT1
  have hr : 0 ≤ r := (div_pos hd (pow_pos hT 9)).le
  have hr32 : r ≤ 1/32 := (div_le_self hd.le (one_le_pow₀ hT1)).trans hd32
  have hrC : 3*r ≤ c/T^9 := by
    dsimp [r]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hdc (pow_nonneg hT.le 9)
  have hw' : ‖w-(![σ,(u : ℂ)*Complex.I] : Fin 2 → ℂ)‖ ≤ r := by
    simpa only [mem_closedBall,dist_eq_norm] using hw
  have hw0 : ‖w 0-(σ : ℂ)‖ ≤ r := by
    simpa using (norm_le_pi_norm (w-![(σ : ℂ),(u : ℂ)*Complex.I]) 0).trans hw'
  have hw1 : ‖w 1-(u : ℂ)*Complex.I‖ ≤ r := by
    simpa using (norm_le_pi_norm (w-![(σ : ℂ),(u : ℂ)*Complex.I]) 1).trans hw'
  have hU := residuePair_control_on_common_disk hc.1 hM hdisks hσ
    (show 1+|u| ≤ T from le_refl _) hrC hw0 (hw1.trans (by linarith))
  have h0re : |(w 0).re-σ| ≤ r := by
    simpa using (Complex.abs_re_le_norm (w 0-(σ : ℂ))).trans hw0
  have h1re : |(w 1).re| ≤ r := by
    simpa using (Complex.abs_re_le_norm (w 1-(u : ℂ)*Complex.I)).trans hw1
  have htube : (w 0,w 1) ∈ axisTube :=
    ⟨by linarith [(abs_le.mp h0re).1,hσ.1],by linarith⟩
  refine ⟨htube,?_⟩
  have hh := hHbound (w 0) (w 1) htube
  change ‖residuePair (w 0) (w 1)*axisEulerCorrection (w 0) (w 1)‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ (M*T^9)^2*H := mul_le_mul hU.2.1 hh (norm_nonneg _) (by positivity)
    _ = C*T^18 := by
      have hid (X Y Z : ℝ) : (X*Y^9)^2*Z = Z*X^2*Y^18 := by ring
      exact hid M T H

end RHTower.BAGTrace
