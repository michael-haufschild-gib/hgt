/-
# The strip residue's continuum bridge: the slope `Φ'(2)` and the ahead-shell Riemann limit

Two continuum facts about the residue `Φ(c) = 1 − (π/c)cot(π/c)` of the inverted-response strip.

* **Slope** (`deriv_stripResidue_two`): `Φ'(2) = −π²/8`. The exact derivative at the threshold
  `c = 2`, built from the derivative of `cot` (`= −1/sin²`) by the chain and product rules.

* **Ahead/behind shells and their balance** (`tendsto_aheadShell`, `tendsto_behindShell`,
  `tendsto_shellDiff`): the discrete `n`-th ahead and behind shell sums on the harmonic carrier, with
  the exact pole distances `ahead_k = c/(2i) + c·Σ_{l=i+1}^{i+k} 1/l` and
  `behind_k = c/(2i) + c·Σ_{l=i−k}^{i−1} 1/l`, divided by `i`, converge to `1/(nc − 1)` and
  `1/(nc + 1)`; their difference converges to `2/((cn)² − 1)`, exactly the `n`-th term of the residue
  series `Φ(c) = Σ_{n≥1} 2/((cn)² − 1)`. So `(A−B)/i → Φ(c)` holds shell by shell. The harmonic
  distances are pinned to the continuum log by `harmonic_sub_log_le` (forward) and `backward_harmonic`
  (backward); the shell profiles `(1+x)^{−nc}` and `(1−x)^{nc}` Riemann sums converge by
  `tendsto_riemann_sum_antitone_Ioi` / `tendsto_riemann_sum_antitone`, with the improper integral
  `1/(nc−1)` evaluated through the reusable `Ioi`-translation lemmas (`setIntegral_Ioi_add_right`,
  `integrableOn_Ioi_add_right_iff`) and `∫_0^1(1−x)^{nc} = 1/(nc+1)` by `integral_one_sub_rpow`.
-/
import GaloisForLFunctions.RHTower.LegStripThreshold
open MeasureTheory Real Set Filter Topology
noncomputable section
namespace RHTower

/-- Derivative of `cot` where `sin ≠ 0`: `(cot)' = −1/sin²`. -/
theorem hasDerivAt_rcot {u : ℝ} (hsin : Real.sin u ≠ 0) :
    HasDerivAt Real.cot (-1/(Real.sin u)^2) u := by
  have hd := (Real.hasDerivAt_cos u).div (Real.hasDerivAt_sin u) hsin
  have heq : ((-Real.sin u) * Real.sin u - Real.cos u * Real.cos u) / (Real.sin u)^2
      = -1/(Real.sin u)^2 := by
    rw [show (-Real.sin u) * Real.sin u - Real.cos u * Real.cos u
          = -((Real.sin u)^2 + (Real.cos u)^2) by ring, Real.sin_sq_add_cos_sq]
  rw [heq] at hd
  have hcot : Real.cot = fun x => Real.cos x / Real.sin x := funext Real.cot_eq_cos_div_sin
  rw [hcot]; exact hd

/-- **The continuum slope at the threshold: `Φ'(2) = −π²/8`.** -/
theorem hasDerivAt_stripResidue_two : HasDerivAt stripResidue (-(π^2/8)) 2 := by
  have h2 : (2:ℝ) ≠ 0 := by norm_num
  have hsin : Real.sin (π/2) ≠ 0 := by rw [Real.sin_pi_div_two]; norm_num
  have ha : HasDerivAt (fun c => π / c) ((0 * 2 - π * 1)/2^2) 2 :=
    (hasDerivAt_const 2 π).div (hasDerivAt_id 2) h2
  have hphi : HasDerivAt (fun u => u * Real.cot u)
      (1 * Real.cot (π/2) + (π/2) * (-1/(Real.sin (π/2))^2)) (π/2) :=
    (hasDerivAt_id (π/2)).mul (hasDerivAt_rcot hsin)
  have hcomp : HasDerivAt (fun c => (π/c) * Real.cot (π/c))
      ((1 * Real.cot (π/2) + (π/2) * (-1/(Real.sin (π/2))^2)) * ((0 * 2 - π * 1)/2^2)) 2 :=
    HasDerivAt.comp 2 hphi ha
  have hsr : HasDerivAt stripResidue
      (0 - (1 * Real.cot (π/2) + (π/2) * (-1/(Real.sin (π/2))^2)) * ((0 * 2 - π * 1)/2^2)) 2 := by
    have hf := (hasDerivAt_const (2:ℝ) (1:ℝ)).sub hcomp
    have hsreq : stripResidue = fun c => 1 - (π/c) * Real.cot (π/c) := by
      funext c; rw [stripResidue]
    rw [hsreq]; exact hf
  convert hsr using 1
  rw [Real.cot_eq_cos_div_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring

/-- `deriv` form of the threshold slope. -/
theorem deriv_stripResidue_two : deriv stripResidue 2 = -(π^2/8) :=
  hasDerivAt_stripResidue_two.deriv


theorem setIntegral_Ioi_add_right (f : ℝ → ℝ) (a b : ℝ) :
    ∫ x in Ioi a, f (x + b) = ∫ t in Ioi (a + b), f t := by
  have hmp := measurePreserving_add_right (volume : Measure ℝ) b
  have h := hmp.setIntegral_preimage_emb (measurableEmbedding_addRight b) f (Ioi (a + b))
  rw [show (fun x => x + b) ⁻¹' Ioi (a + b) = Ioi a by ext x; simp] at h
  exact h

theorem integrableOn_Ioi_add_right_iff (f : ℝ → ℝ) (a b : ℝ) :
    IntegrableOn (fun x => f (x + b)) (Ioi a) ↔ IntegrableOn f (Ioi (a + b)) := by
  have hmp := measurePreserving_add_right (volume : Measure ℝ) b
  rw [show Ioi a = (fun x => x + b) ⁻¹' Ioi (a + b) by ext x; simp]
  exact hmp.integrableOn_comp_preimage (measurableEmbedding_addRight b)

theorem integral_one_add_rpow {r : ℝ} (hr : 1 < r) :
    ∫ x in Ioi (0:ℝ), (1 + x) ^ (-r) = 1/(r-1) := by
  have h : ∫ x in Ioi (0:ℝ), (1 + x) ^ (-r) = ∫ x in Ioi (0:ℝ), (x + 1) ^ (-r) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _; show (1 + x) ^ (-r) = (x + 1) ^ (-r); rw [add_comm]
  have hshift : ∫ x in Ioi (0:ℝ), (x + 1) ^ (-r) = ∫ t in Ioi (1:ℝ), t ^ (-r) := by
    simpa using setIntegral_Ioi_add_right (fun t => t ^ (-r)) 0 1
  rw [h, hshift, integral_Ioi_rpow_of_lt (show (-r) < -1 by linarith) (by norm_num : (0:ℝ) < 1),
    Real.one_rpow]
  have hne1 : (-r + 1) ≠ 0 := by linarith
  have hne2 : (r - 1) ≠ 0 := by linarith
  field_simp
  ring

theorem integrableOn_one_add_rpow {r : ℝ} (hr : 1 < r) :
    IntegrableOn (fun x : ℝ => (1 + x) ^ (-r)) (Ioi 0) := by
  have h : (fun x : ℝ => (1 + x) ^ (-r)) = (fun x : ℝ => (x + 1) ^ (-r)) := by
    funext x; rw [add_comm]
  rw [h, integrableOn_Ioi_add_right_iff (fun t => t ^ (-r)) 0 1, zero_add]
  exact integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num : (0:ℝ) < 1)

/-- Summability of the shell profile samples `(1 + k/i)^{-r}` (`i ≥ 1`, `r > 1`). -/
theorem summable_one_add_div_rpow {i : ℕ} (hi : 1 ≤ i) {r : ℝ} (hr : 1 < r) :
    Summable (fun k : ℕ => (1 + (k:ℝ)/i)^(-r)) := by
  have hi0 : (0:ℝ) < i := by exact_mod_cast hi
  have hi1 : (1:ℝ) ≤ i := by exact_mod_cast hi
  have hps : Summable (fun k : ℕ => ((k:ℝ)+1)^(-r)) := by
    have hbase := (Real.summable_nat_rpow (p := -r)).mpr (by linarith)
    refine (hbase.comp_injective (add_left_injective 1)).congr (fun k => ?_)
    simp only [Function.comp_apply]; push_cast; rw [add_comm]
  have hmaj : Summable (fun k:ℕ => (i:ℝ)^r * ((k:ℝ)+1)^(-r)) := hps.mul_left _
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hmaj
  have hb : (0:ℝ) < (1+(k:ℝ))/i := by positivity
  have hb2 : (1+(k:ℝ))/i ≤ 1 + (k:ℝ)/i := by
    rw [add_div]; gcongr; exact (div_le_one hi0).mpr hi1
  calc (1 + (k:ℝ)/i)^(-r) ≤ ((1+(k:ℝ))/i)^(-r) :=
        Real.rpow_le_rpow_of_nonpos hb hb2 (by linarith)
    _ = (i:ℝ)^r * ((k:ℝ)+1)^(-r) := by
        rw [Real.div_rpow (by positivity) (by positivity),
          Real.rpow_neg (by positivity : (0:ℝ) ≤ (i:ℝ)), div_eq_mul_inv, inv_inv, mul_comm,
          add_comm (1:ℝ) (k:ℝ)]

/-- **The ahead shell converges to the continuum shell value.** For `c > 1`, `n ≥ 1`, the discrete
`n`-th ahead shell sum on the harmonic carrier — with exact pole distances
`ahead_k = c/(2i) + c·Σ_{l=i+1}^{i+k} 1/l` — divided by `i`, converges to `1/(nc − 1)`. The harmonic
distances are pinned to the continuum log by `harmonic_sub_log_le` (a correction `e^{±nc/2i} → 1`),
and the shell profile `(1+x)^{−nc}` Riemann sum converges by `tendsto_riemann_sum_antitone_Ioi`, its
integral being `1/(nc−1)`. -/
theorem tendsto_aheadShell {c : ℝ} (hc : 1 < c) (n : ℕ+) :
    Tendsto (fun i : ℕ => (1/(i:ℝ)) * ∑' k : ℕ,
      Real.exp (-(n:ℝ) * (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1))))
      atTop (𝓝 (1/((n:ℝ)*c - 1))) := by
  set r : ℝ := (n:ℝ)*c with hr_def
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast n.pos
  have hc0 : 0 < c := by linarith
  have hr1 : 1 < r := by rw [hr_def]; nlinarith [hn1, hc]
  have hr0 : 0 < r := by linarith
  set f : ℝ → ℝ := fun x => (1+x)^(-r) with hf_def
  have hf_anti : AntitoneOn f (Set.Ici 0) := by
    intro a ha b hb hab
    simp only [Set.mem_Ici] at ha hb
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have hf_nn : ∀ x ∈ Set.Ici (0:ℝ), 0 ≤ f x := by
    intro x hx; simp only [Set.mem_Ici] at hx; simp only [hf_def]; positivity
  have hf_int : IntegrableOn f (Set.Ioi 0) := integrableOn_one_add_rpow hr1
  have hR : Tendsto (fun i:ℕ => (1/(i:ℝ)) * ∑' k:ℕ, f ((k:ℝ)/i)) atTop (𝓝 (1/(r-1))) := by
    rw [← integral_one_add_rpow hr1]
    exact tendsto_riemann_sum_antitone_Ioi hf_anti hf_nn hf_int
  have hsumf : ∀ i:ℕ, 1 ≤ i → Summable (fun k:ℕ => f ((k:ℝ)/i)) :=
    fun i hi => by simpa only [hf_def] using summable_one_add_div_rpow hi hr1
  have hfnn : ∀ (i:ℕ), 1 ≤ i → ∀ k:ℕ, 0 ≤ f ((k:ℝ)/i) := by
    intro i hi k
    have hi0 : (0:ℝ) < i := by exact_mod_cast hi
    exact hf_nn _ (by simp only [Set.mem_Ici]; positivity)
  have hEeq : ∀ i:ℕ, 1 ≤ i → ∀ k:ℕ,
      Real.exp (-(n:ℝ) * (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1)))
        = Real.exp (-r/(2*(i:ℝ))) *
          (f ((k:ℝ)/i) * Real.exp (r * (Real.log (((i:ℝ)+k)/i)
            - ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1)))) := by
    intro i hi k
    have hi0 : (0:ℝ) < i := by exact_mod_cast hi
    have hpos : (0:ℝ) < 1 + (k:ℝ)/i := by positivity
    have hbase_eq : (1:ℝ) + (k:ℝ)/i = ((i:ℝ)+k)/i := by
      rw [add_div, div_self (ne_of_gt hi0)]
    have hfk : f ((k:ℝ)/i) = Real.exp (-r * Real.log (((i:ℝ)+k)/i)) := by
      simp only [hf_def]
      rw [Real.rpow_def_of_pos hpos, hbase_eq]
      congr 1; ring
    rw [hfk, ← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hr_def]; ring
  -- termwise squeeze: e^{-r/2i}·f ≤ summand ≤ e^{r/2i}·f
  have hbounds : ∀ (i:ℕ), 1 ≤ i → ∀ k:ℕ,
      Real.exp (-r/(2*(i:ℝ))) * f ((k:ℝ)/i)
        ≤ Real.exp (-(n:ℝ) * (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1)))
      ∧ Real.exp (-(n:ℝ) * (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1)))
        ≤ Real.exp (r/(2*(i:ℝ))) * f ((k:ℝ)/i) := by
    intro i hi k
    have hi0 : (0:ℝ) < i := by exact_mod_cast hi
    have hharm := harmonic_sub_log_le i hi k
    have hfk := hfnn i hi k
    rw [hEeq i hi k]
    set A := Real.exp (r * (Real.log (((i:ℝ)+k)/i)
      - ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1))) with hA
    have hAlb : (1:ℝ) ≤ A := Real.one_le_exp_iff.mpr (mul_nonneg hr0.le hharm.1)
    have hAub : A ≤ Real.exp (r/(i:ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_left hharm.2 hr0.le
      rwa [mul_one_div] at hm
    refine ⟨?_, ?_⟩
    · exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hfk hAlb) (Real.exp_pos _).le
    · calc Real.exp (-r/(2*(i:ℝ))) * (f ((k:ℝ)/i) * A)
          ≤ Real.exp (-r/(2*(i:ℝ))) * (f ((k:ℝ)/i) * Real.exp (r/(i:ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAub hfk) (Real.exp_pos _).le
        _ = Real.exp (r/(2*(i:ℝ))) * f ((k:ℝ)/i) := by
            rw [show Real.exp (-r/(2*(i:ℝ))) * (f ((k:ℝ)/i) * Real.exp (r/(i:ℝ)))
                = f ((k:ℝ)/i) * (Real.exp (-r/(2*(i:ℝ))) * Real.exp (r/(i:ℝ))) by ring,
              ← Real.exp_add, show -r/(2*(i:ℝ)) + r/(i:ℝ) = r/(2*(i:ℝ)) by ring, mul_comm]
  have hsumE : ∀ (i:ℕ), 1 ≤ i → Summable (fun k:ℕ => Real.exp (-(n:ℝ) *
      (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1)))) := fun i hi =>
    Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) (fun k => (hbounds i hi k).2)
      ((hsumf i hi).mul_left (Real.exp (r/(2*(i:ℝ)))))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun i:ℕ => Real.exp (-r/(2*(i:ℝ))) * ((1/(i:ℝ)) * ∑' k:ℕ, f ((k:ℝ)/i)))
    (h := fun i:ℕ => Real.exp (r/(2*(i:ℝ))) * ((1/(i:ℝ)) * ∑' k:ℕ, f ((k:ℝ)/i)))
    ?_ ?_ ?_ ?_
  · have hz : Tendsto (fun i:ℕ => Real.exp (-r/(2*(i:ℝ)))) atTop (𝓝 1) := by
      have h0 : Tendsto (fun i:ℕ => -r/(2*(i:ℝ))) atTop (𝓝 0) := by
        refine (tendsto_const_div_atTop_nhds_zero_nat (-r/2)).congr (fun i => ?_); ring
      simpa using! (Real.continuous_exp.tendsto 0).comp h0
    simpa using hz.mul hR
  · have hz : Tendsto (fun i:ℕ => Real.exp (r/(2*(i:ℝ)))) atTop (𝓝 1) := by
      have h0 : Tendsto (fun i:ℕ => r/(2*(i:ℝ))) atTop (𝓝 0) := by
        refine (tendsto_const_div_atTop_nhds_zero_nat (r/2)).congr (fun i => ?_); ring
      simpa using! (Real.continuous_exp.tendsto 0).comp h0
    simpa using hz.mul hR
  · filter_upwards [eventually_ge_atTop 1] with i hi
    have hlow : Real.exp (-r/(2*(i:ℝ))) * ∑' k:ℕ, f ((k:ℝ)/i)
        ≤ ∑' k:ℕ, Real.exp (-(n:ℝ) *
          (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1))) := by
      rw [← tsum_mul_left]
      exact Summable.tsum_mono ((hsumf i hi).mul_left _) (hsumE i hi) (fun k => (hbounds i hi k).1)
    calc Real.exp (-r/(2*(i:ℝ))) * ((1/(i:ℝ)) * ∑' k : ℕ, f ((k:ℝ)/i))
        = (1/(i:ℝ)) * (Real.exp (-r/(2*(i:ℝ))) * ∑' k : ℕ, f ((k:ℝ)/i)) := by ring
      _ ≤ (1/(i:ℝ)) * ∑' k : ℕ, Real.exp (-(n:ℝ) *
            (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1))) :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
  · filter_upwards [eventually_ge_atTop 1] with i hi
    have hupp : ∑' k:ℕ, Real.exp (-(n:ℝ) *
          (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1)))
        ≤ Real.exp (r/(2*(i:ℝ))) * ∑' k:ℕ, f ((k:ℝ)/i) := by
      rw [← tsum_mul_left]
      exact Summable.tsum_mono (hsumE i hi) ((hsumf i hi).mul_left _) (fun k => (hbounds i hi k).2)
    calc (1/(i:ℝ)) * ∑' k : ℕ, Real.exp (-(n:ℝ) *
            (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1)))
        ≤ (1/(i:ℝ)) * (Real.exp (r/(2*(i:ℝ))) * ∑' k : ℕ, f ((k:ℝ)/i)) :=
          mul_le_mul_of_nonneg_left hupp (by positivity)
      _ = Real.exp (r/(2*(i:ℝ))) * ((1/(i:ℝ)) * ∑' k : ℕ, f ((k:ℝ)/i)) := by ring

/-- Backward harmonic sandwich: for `1 ≤ i`, `k < i`, the backward tail
`B_k = Σ_{l=i-k}^{i-1} 1/l = Σ_{j<k} 1/(i-1-j)` satisfies
`log(i/(i-k)) ≤ B_k ≤ log(i/(i-k)) + 1/(i-k) - 1/i`. -/
theorem backward_harmonic (i : ℕ) (hi : 1 ≤ i) :
    ∀ k : ℕ, k < i →
      Real.log ((i:ℝ)/((i:ℝ)-k)) ≤ ∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j)
      ∧ (∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j)) - Real.log ((i:ℝ)/((i:ℝ)-k))
          ≤ 1/((i:ℝ)-k) - 1/(i:ℝ) := by
  have hi0 : (0:ℝ) < i := by exact_mod_cast hi
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk1
    have hk : k < i := by omega
    obtain ⟨ihl, ihu⟩ := ih hk
    have hik : (0:ℝ) < (i:ℝ) - k := by
      have : (k:ℝ) < i := by exact_mod_cast hk
      linarith
    have hik1 : (0:ℝ) < (i:ℝ) - k - 1 := by
      have : ((k:ℝ)+1) < i := by exact_mod_cast hk1
      linarith
    have hstep := log_step_bounds hik1
    rw [show (i:ℝ) - k - 1 + 1 = (i:ℝ) - k by ring] at hstep
    rw [Finset.sum_range_succ]
    push_cast
    rw [show (i:ℝ) - ((k:ℝ) + 1) = (i:ℝ) - k - 1 by ring,
      show (1:ℝ)/((i:ℝ) - 1 - (k:ℝ)) = 1/((i:ℝ) - k - 1) by congr 1; ring]
    have hlogsplit : Real.log ((i:ℝ)/((i:ℝ) - k - 1))
        = Real.log ((i:ℝ)/((i:ℝ) - k)) + Real.log (((i:ℝ) - k)/((i:ℝ) - k - 1)) := by
      rw [Real.log_div (ne_of_gt hi0) (ne_of_gt hik1), Real.log_div (ne_of_gt hi0) (ne_of_gt hik),
        Real.log_div (ne_of_gt hik) (ne_of_gt hik1)]
      ring
    rw [hlogsplit]
    exact ⟨by linarith [ihl, hstep.2], by linarith [ihu, hstep.1]⟩

/-- `∫_0^1 (1-x)^r = 1/(r+1)` for `r > -1`. -/
theorem integral_one_sub_rpow {r : ℝ} (hr : -1 < r) :
    ∫ x in (0:ℝ)..1, (1 - x) ^ r = 1/(r+1) := by
  rw [intervalIntegral.integral_comp_sub_left (fun y => y ^ r) 1]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl hr), Real.one_rpow, Real.zero_rpow (by linarith : r + 1 ≠ 0)]
  norm_num

/-- **The behind shell converges to the continuum shell value.** For `c > 1`, `n ≥ 1`, the discrete
`n`-th behind shell sum on the harmonic carrier — with exact pole distances
`behind_k = c/(2i) + c·Σ_{l=i-k}^{i-1} 1/l` — divided by `i`, converges to `1/(nc + 1)`. The backward
harmonic tail is pinned to the log by `backward_harmonic`; the profile `(1-x)^{nc}` Riemann sum
converges by `tendsto_riemann_sum_antitone`; the near-endpoint non-uniformity of the correction is
absorbed by the total deviation bound `≤ nc/i → 0` (via `1 - e^{-x} ≤ x`). -/
theorem tendsto_behindShell {c : ℝ} (hc : 1 < c) (n : ℕ+) :
    Tendsto (fun i : ℕ => (1/(i:ℝ)) * ∑ k ∈ Finset.range i,
      Real.exp (-(n:ℝ) * (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j))))
      atTop (𝓝 (1/((n:ℝ)*c + 1))) := by
  set r : ℝ := (n:ℝ)*c with hr_def
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast n.pos
  have hc0 : 0 < c := by linarith
  have hr1 : 1 < r := by rw [hr_def]; nlinarith [hn1, hc]
  have hr0 : 0 < r := by linarith
  set g : ℝ → ℝ := fun x => (1 - x) ^ r with hg_def
  have hg_anti : AntitoneOn g (Set.Icc 0 1) := by
    intro a ha b hb hab
    simp only [Set.mem_Icc] at ha hb; simp only [hg_def]
    exact Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
  have hP : Tendsto (fun i:ℕ => Real.exp (-r/(2*(i:ℝ))) *
      ((1/(i:ℝ)) * ∑ k ∈ Finset.range i, g ((k:ℝ)/i))) atTop (𝓝 (1/(r+1))) := by
    have hgint : Tendsto (fun i:ℕ => (1/(i:ℝ)) * ∑ k ∈ Finset.range i, g ((k:ℝ)/i)) atTop
        (𝓝 (1/(r+1))) := by
      have h := tendsto_riemann_sum_antitone hg_anti
      rwa [show (∫ x in (0:ℝ)..1, g x) = 1/(r+1) by
        simpa only [hg_def] using integral_one_sub_rpow (by linarith : (-1:ℝ) < r)] at h
    have hz : Tendsto (fun i:ℕ => Real.exp (-r/(2*(i:ℝ)))) atTop (𝓝 1) := by
      have h0 : Tendsto (fun i:ℕ => -r/(2*(i:ℝ))) atTop (𝓝 0) := by
        refine (tendsto_const_div_atTop_nhds_zero_nat (-r/2)).congr (fun i => ?_); ring
      simpa using! (Real.continuous_exp.tendsto 0).comp h0
    simpa using hz.mul hgint
  have hEeqB : ∀ i:ℕ, 1 ≤ i → ∀ k, k < i →
      Real.exp (-(n:ℝ) * (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j)))
        = Real.exp (-r/(2*(i:ℝ))) * (g ((k:ℝ)/i) *
          Real.exp (-r * ((∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j)) - Real.log ((i:ℝ)/((i:ℝ)-k))))) := by
    intro i hi k hk
    have hi0 : (0:ℝ) < i := by exact_mod_cast hi
    have hkr : (k:ℝ) < (i:ℝ) := by exact_mod_cast hk
    have hik : (0:ℝ) < (i:ℝ) - k := by linarith
    have hprof : g ((k:ℝ)/i) = Real.exp (-r * Real.log ((i:ℝ)/((i:ℝ)-k))) := by
      simp only [hg_def]
      rw [show (1:ℝ) - (k:ℝ)/i = ((i:ℝ)-k)/i by field_simp, Real.rpow_def_of_pos (by positivity),
        Real.log_div (by positivity) (ne_of_gt hi0), Real.log_div (ne_of_gt hi0) (ne_of_gt hik)]
      ring_nf
    rw [hprof, ← Real.exp_add, ← Real.exp_add]; congr 1; rw [hr_def]; ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun i:ℕ => Real.exp (-r/(2*(i:ℝ))) *
      ((1/(i:ℝ)) * ∑ k ∈ Finset.range i, g ((k:ℝ)/i)) - r/(i:ℝ))
    (h := fun i:ℕ => Real.exp (-r/(2*(i:ℝ))) *
      ((1/(i:ℝ)) * ∑ k ∈ Finset.range i, g ((k:ℝ)/i)))
    (by simpa using hP.sub (tendsto_const_div_atTop_nhds_zero_nat r)) hP ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with i hi
    have hi0 : (0:ℝ) < i := by exact_mod_cast hi
    have hterm : ∀ k ∈ Finset.range i,
        Real.exp (-r/(2*(i:ℝ))) * g ((k:ℝ)/i) - (r/(i:ℝ)) * (1 - (k:ℝ)/i) ^ (r - 1)
          ≤ Real.exp (-(n:ℝ) * (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j))) := by
      intro k hkm
      rw [Finset.mem_range] at hkm
      have hkr : (k:ℝ) < (i:ℝ) := by exact_mod_cast hkm
      have hik : (0:ℝ) < (i:ℝ) - k := by linarith
      have hpos1 : (0:ℝ) < 1 - (k:ℝ)/i := by rw [sub_pos, div_lt_one hi0]; exact hkr
      have hgk : g ((k:ℝ)/i) = (1 - (k:ℝ)/i) ^ r := rfl
      have hgnn : (0:ℝ) ≤ g ((k:ℝ)/i) := by rw [hgk]; positivity
      have hbh := backward_harmonic i hi k hkm
      have herr0 : (0:ℝ) ≤ (∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j)) - Real.log ((i:ℝ)/((i:ℝ)-k)) := by
        linarith [hbh.1]
      have herrub : (∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j)) - Real.log ((i:ℝ)/((i:ℝ)-k))
          ≤ 1/((i:ℝ)-k) := by linarith [hbh.2, (by positivity : (0:ℝ) ≤ 1/(i:ℝ))]
      rw [hEeqB i hi k hkm]
      set err : ℝ := (∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j)) - Real.log ((i:ℝ)/((i:ℝ)-k)) with herr
      have hak_nn : (0:ℝ) ≤ Real.exp (-r/(2*(i:ℝ))) * g ((k:ℝ)/i) := by positivity
      have hexp1 : Real.exp (-r/(2*(i:ℝ))) ≤ 1 := by
        rw [Real.exp_le_one_iff, neg_div]; exact neg_nonpos.mpr (by positivity)
      have hak_le : Real.exp (-r/(2*(i:ℝ))) * g ((k:ℝ)/i) ≤ g ((k:ℝ)/i) := by
        nlinarith [hexp1, hgnn]
      have h1E : (1:ℝ) - Real.exp (-r * err) ≤ r * err := by
        have := Real.add_one_le_exp (-r * err); linarith
      have hbid : g ((k:ℝ)/i) * (r * (1/((i:ℝ)-k))) = (r/(i:ℝ)) * (1 - (k:ℝ)/i) ^ (r-1) := by
        rw [hgk, show (i:ℝ) - k = (i:ℝ) * (1 - (k:ℝ)/i) by field_simp,
          show r = (r-1)+1 by ring, Real.rpow_add hpos1, Real.rpow_one]
        field_simp
        ring_nf
      have hdev : Real.exp (-r/(2*(i:ℝ))) * g ((k:ℝ)/i)
          - Real.exp (-r/(2*(i:ℝ))) * (g ((k:ℝ)/i) * Real.exp (-r * err))
          ≤ (r/(i:ℝ)) * (1 - (k:ℝ)/i) ^ (r-1) := by
        calc Real.exp (-r/(2*(i:ℝ))) * g ((k:ℝ)/i)
              - Real.exp (-r/(2*(i:ℝ))) * (g ((k:ℝ)/i) * Real.exp (-r * err))
            = (Real.exp (-r/(2*(i:ℝ))) * g ((k:ℝ)/i)) * (1 - Real.exp (-r * err)) := by ring
          _ ≤ (Real.exp (-r/(2*(i:ℝ))) * g ((k:ℝ)/i)) * (r * err) :=
              mul_le_mul_of_nonneg_left h1E hak_nn
          _ ≤ g ((k:ℝ)/i) * (r * err) := by
              apply mul_le_mul_of_nonneg_right hak_le; positivity
          _ ≤ g ((k:ℝ)/i) * (r * (1/((i:ℝ)-k))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left herrub hr0.le) hgnn
          _ = (r/(i:ℝ)) * (1 - (k:ℝ)/i) ^ (r-1) := hbid
      linarith [hdev]
    have hdevsum : (∑ k ∈ Finset.range i, (r/(i:ℝ)) * (1 - (k:ℝ)/i) ^ (r-1)) ≤ r := by
      have hb : ∀ k ∈ Finset.range i, (r/(i:ℝ)) * (1 - (k:ℝ)/i) ^ (r-1) ≤ (r/(i:ℝ)) * 1 := by
        intro k hkm
        rw [Finset.mem_range] at hkm
        have hkr : (k:ℝ) < (i:ℝ) := by exact_mod_cast hkm
        have h1 : (0:ℝ) ≤ 1 - (k:ℝ)/i := by rw [sub_nonneg, div_le_one hi0]; linarith
        have h2 : 1 - (k:ℝ)/i ≤ 1 := by nlinarith [(show (0:ℝ) ≤ (k:ℝ)/i by positivity)]
        gcongr
        exact Real.rpow_le_one h1 h2 (by linarith)
      calc (∑ k ∈ Finset.range i, (r/(i:ℝ)) * (1 - (k:ℝ)/i) ^ (r-1))
          ≤ ∑ _k ∈ Finset.range i, (r/(i:ℝ)) * 1 := Finset.sum_le_sum hb
        _ = (i:ℝ) * ((r/(i:ℝ)) * 1) := by rw [Finset.sum_const, Finset.card_range]; ring
        _ = r := by field_simp
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_sub_distrib] at hsum
    have hstep : Real.exp (-r/(2*(i:ℝ))) * ((1/(i:ℝ)) * ∑ k ∈ Finset.range i, g ((k:ℝ)/i)) - r/(i:ℝ)
        = (1/(i:ℝ)) * ((∑ k ∈ Finset.range i, Real.exp (-r/(2*(i:ℝ))) * g ((k:ℝ)/i)) - r) := by
      rw [← Finset.mul_sum]; ring
    rw [hstep]
    have hle : (∑ k ∈ Finset.range i, Real.exp (-r/(2*(i:ℝ))) * g ((k:ℝ)/i)) - r
        ≤ ∑ k ∈ Finset.range i, Real.exp (-(n:ℝ) *
          (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j))) := by linarith [hsum, hdevsum]
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  · filter_upwards [eventually_ge_atTop 1] with i hi
    have hi0 : (0:ℝ) < i := by exact_mod_cast hi
    have hterm : ∀ k ∈ Finset.range i,
        Real.exp (-(n:ℝ) * (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j)))
          ≤ Real.exp (-r/(2*(i:ℝ))) * g ((k:ℝ)/i) := by
      intro k hkm
      rw [Finset.mem_range] at hkm
      have hkr : (k:ℝ) < (i:ℝ) := by exact_mod_cast hkm
      have hik : (0:ℝ) < (i:ℝ) - k := by linarith
      have hpos1 : (0:ℝ) < 1 - (k:ℝ)/i := by rw [sub_pos, div_lt_one hi0]; exact hkr
      have hgnn : (0:ℝ) ≤ g ((k:ℝ)/i) := by simp only [hg_def]; positivity
      have hbh := backward_harmonic i hi k hkm
      have herr0 : (0:ℝ) ≤ (∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j)) - Real.log ((i:ℝ)/((i:ℝ)-k)) := by
        linarith [hbh.1]
      rw [hEeqB i hi k hkm]
      have hE1 : Real.exp (-r * ((∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j)) - Real.log ((i:ℝ)/((i:ℝ)-k)))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [herr0, hr0.le])
      calc Real.exp (-r/(2*(i:ℝ))) * (g ((k:ℝ)/i) *
            Real.exp (-r * ((∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j)) - Real.log ((i:ℝ)/((i:ℝ)-k)))))
          ≤ Real.exp (-r/(2*(i:ℝ))) * (g ((k:ℝ)/i) * 1) := by
            gcongr
        _ = Real.exp (-r/(2*(i:ℝ))) * g ((k:ℝ)/i) := by ring
    have hsum := Finset.sum_le_sum hterm
    calc (1/(i:ℝ)) * ∑ k ∈ Finset.range i, Real.exp (-(n:ℝ) *
            (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j)))
        ≤ (1/(i:ℝ)) * ∑ k ∈ Finset.range i, Real.exp (-r/(2*(i:ℝ))) * g ((k:ℝ)/i) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = Real.exp (-r/(2*(i:ℝ))) * ((1/(i:ℝ)) * ∑ k ∈ Finset.range i, g ((k:ℝ)/i)) := by
          rw [← Finset.mul_sum]; ring


/-- **Per-shell balance converges to the residue-series term.** For `c > 1`, `n ≥ 1`, the `n`-th
shell of the physical field's ahead-minus-behind balance on the harmonic carrier, divided by `i`,
converges to `2/((cn)² − 1)` — exactly the `n`-th term of `Φ(c) = Σ_{n≥1} 2/((cn)² − 1)`
(`stripResidue_eq_tsum`). Thus `(A−B)/i → Φ(c)` holds shell by shell: each shell of the discrete
field balance lands on its continuum residue term. -/
theorem tendsto_shellDiff {c : ℝ} (hc : 1 < c) (n : ℕ+) :
    Tendsto (fun i : ℕ =>
      (1/(i:ℝ)) * ∑' k : ℕ,
        Real.exp (-(n:ℝ) * (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1)))
      - (1/(i:ℝ)) * ∑ k ∈ Finset.range i,
        Real.exp (-(n:ℝ) * (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j))))
      atTop (𝓝 (2/(((n:ℝ)*c)^2 - 1))) := by
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast n.pos
  have hc0 : 0 < c := by linarith
  have hnc : 1 < (n:ℝ)*c := by nlinarith [hn1, hc]
  have heq : (1:ℝ)/((n:ℝ)*c - 1) - 1/((n:ℝ)*c + 1) = 2/(((n:ℝ)*c)^2 - 1) := by
    have h1 : (n:ℝ)*c - 1 ≠ 0 := ne_of_gt (by linarith)
    have h2 : (n:ℝ)*c + 1 ≠ 0 := ne_of_gt (by linarith)
    rw [div_sub_div _ _ h1 h2,
      show (1:ℝ)*((n:ℝ)*c+1) - ((n:ℝ)*c-1)*1 = 2 by ring,
      show ((n:ℝ)*c-1)*((n:ℝ)*c+1) = ((n:ℝ)*c)^2-1 by ring]
  have h := (tendsto_aheadShell hc n).sub (tendsto_behindShell hc n)
  rw [heq] at h
  exact h

end RHTower
end
