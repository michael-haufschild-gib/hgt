import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSelfEnergyOfAnAtomIsExactlyLogarithmic
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheEnergyOfAHorizonBlock
import GaloisForLFunctions.ArithmeticIncidencePositivity.TranslatePairingCalculus

/-!
# The local Gamma Gram is the autocorrelation matrix

On shrinking intervals, the coefficient of the logarithmic Gamma energy is
the physical square mass. For neighboring integer atoms, their rescaled
logarithmic centers approach an arithmetic progression, retaining the
profile's autocorrelation Gram.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory Filter Topology Set Finset

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis _root_.RHTower
open ArithmeticIncidencePositivity RenormalizedArithmeticPotentialTheory.CompletedShell

/-- Uniformly Lipschitz shrinking sources retain exactly their rescaled square mass
as the leading logarithmic Gamma energy. -/
theorem tendsto_scaled_archForm_of_shrinking_support
    {ι : Type*} {l : Filter ι} {r : ι → ℝ} (hr : Tendsto r l atTop)
    {f : ι → ℝ → ℝ} {W K C M : ℝ} (hW : 0 < W) (hK : 0 ≤ K)
    (hsmooth : ∀ᶠ n in l, ContDiff ℝ 2 (f n))
    (hsupp : ∀ᶠ n in l, ∀ u, u ∉ Set.Icc 0 (W / r n) → f n u = 0)
    (hlip : ∀ᶠ n in l, ∀ u v, |f n u - f n v| ≤ K * r n * |u - v|)
    (hL1 : ∀ᶠ n in l, r n * (∫ u, |f n u|) ≤ C)
    (hmass : Tendsto (fun n => r n * ∫ u, f n u ^ 2) l (𝓝 M)) :
    Tendsto (fun n => r n / Real.log (r n) * archForm (f n)) l (𝓝 M) := by
  let a := 2 * gammaHardyPhaseRate 0 - Real.log W
  let b := a + selfEnergyConstant
  let d := Real.exp (1 / 2) * K * W
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hlog := Real.tendsto_log_atTop.comp hr
  have ha : Tendsto (fun n => a / Real.log (r n)) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hb : Tendsto (fun n => b / Real.log (r n)) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hpay : Tendsto (fun n => d * C / Real.log (r n)) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hlo : Tendsto (fun n => (1 + a / Real.log (r n)) *
      (r n * ∫ u, f n u ^ 2)) l (𝓝 M) := by
    simpa only [add_zero, one_mul] using
      ((tendsto_const_nhds (x := (1 : ℝ))).add ha).mul hmass
  have hup : Tendsto (fun n => (1 + b / Real.log (r n)) *
      (r n * ∫ u, f n u ^ 2) + d * C / Real.log (r n)) l (𝓝 M) := by
    simpa only [add_zero, one_mul] using
      (((tendsto_const_nhds (x := (1 : ℝ))).add hb).mul hmass).add hpay
  have hbounds : ∀ᶠ n in l,
      (1 + a / Real.log (r n)) * (r n * ∫ u, f n u ^ 2) ≤
          r n / Real.log (r n) * archForm (f n) ∧
      r n / Real.log (r n) * archForm (f n) ≤
        (1 + b / Real.log (r n)) * (r n * ∫ u, f n u ^ 2) +
          d * C / Real.log (r n) := by
    filter_upwards [hsmooth, hsupp, hlip, hL1,
      hr.eventually_gt_atTop 1, hr.eventually_ge_atTop W] with n hf hs hL hI hr1 hrW
    have hr0 : 0 < r n := zero_lt_one.trans hr1
    have hl0 : 0 < Real.log (r n) := Real.log_pos hr1
    have hw0 : 0 < W / r n := div_pos hW hr0
    have hw1 : W / r n ≤ 1 := (div_le_one hr0).mpr hrW
    have hc : HasCompactSupport (f n) := HasCompactSupport.intro isCompact_Icc hs
    have he : Real.log (1 / (W / r n)) = Real.log (r n) - Real.log W := by
      rw [show 1 / (W / r n) = r n / W by field_simp,
        Real.log_div hr0.ne' hW.ne']
    have hlow := archForm_atom_ge hf hc hs hw0 hw1
    have hupp := archForm_atom_le hf hc hs hw0 hw1 (mul_nonneg hK hr0.le) hL
    rw [he] at hlow hupp
    constructor
    · calc
        _ = (r n / Real.log (r n)) *
            ((2 * gammaHardyPhaseRate 0 + (Real.log (r n) - Real.log W)) *
              ∫ u, f n u ^ 2) := by
          dsimp only [a]
          field_simp
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hlow (div_nonneg hr0.le hl0.le)
    · have hpaid := mul_le_mul_of_nonneg_left hI (div_nonneg hd hl0.le)
      calc
        _ ≤ (r n / Real.log (r n)) *
            (((2 * gammaHardyPhaseRate 0 + (Real.log (r n) - Real.log W) +
                selfEnergyConstant) * ∫ u, f n u ^ 2) +
              Real.exp (1 / 2) * (K * r n) * (W / r n) * ∫ u, |f n u|) :=
          mul_le_mul_of_nonneg_left hupp (div_nonneg hr0.le hl0.le)
        _ = (1 + b / Real.log (r n)) * (r n * ∫ u, f n u ^ 2) +
            (d / Real.log (r n)) * (r n * ∫ u, |f n u|) := by
          dsimp only [b, a, d]
          field_simp
          ring
        _ ≤ (1 + b / Real.log (r n)) * (r n * ∫ u, f n u ^ 2) +
            (d / Real.log (r n)) * C := add_le_add le_rfl hpaid
        _ = _ := by ring
  exact hlo.squeeze' hup (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

/-- A finite combination of translated copies of a profile at width `c`. -/
def localProfileComb (φ : ℝ → ℝ) (c : ℝ) (m : ℕ) (x a : ℕ → ℝ) (u : ℝ) : ℝ :=
  ∑ i ∈ range m, x i * φ ((u - a i) / c)

private theorem profileDilate_nice {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hs : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c) :
    ContCompact (fun u => φ (u / c)) := by
  refine ⟨hφ.comp (continuous_id.div_const c),
    HasCompactSupport.intro isCompact_Icc (K := Set.Icc 0 c) ?_⟩
  intro u hu
  apply hs
  intro hmem
  exact hu ⟨by simpa only [zero_mul] using (le_div_iff₀ hc).mp hmem.1,
    (div_le_one hc).mp hmem.2⟩

theorem localProfileComb_nice {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hs : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c)
    (m : ℕ) (x a : ℕ → ℝ) : ContCompact (localProfileComb φ c m x a) := by
  have heq : localProfileComb φ c m x a =
      translateComb (fun u => φ (u / c)) m x (fun i => -a i) := by
    funext u
    simp only [localProfileComb, translateComb, sub_eq_add_neg]
  rw [heq]
  exact (profileDilate_nice hφ hs hc).comb m x (fun i => -a i)

theorem contDiff_localProfileComb {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (c : ℝ) (m : ℕ) (x a : ℕ → ℝ) : ContDiff ℝ 2 (localProfileComb φ c m x a) :=
  ContDiff.sum fun _ _ => contDiff_const.mul
    (hφ.comp ((contDiff_id.sub contDiff_const).div_const c))

/-- The Gram of a finite translate combination is exactly its physical square mass. -/
theorem integral_sq_localProfileComb {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hs : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c)
    (m : ℕ) (x a : ℕ → ℝ) :
    (∫ u, localProfileComb φ c m x a u ^ 2) =
      c * ∑ i ∈ range m, ∑ j ∈ range m,
        x i * x j * shellAutocorr φ ((a i - a j) / c) := by
  have h := testPairing_comb (profileDilate_nice hφ hs hc)
    m m x (fun i => -a i) x (fun i => -a i)
  have heq : localProfileComb φ c m x a =
      translateComb (fun u => φ (u / c)) m x (fun i => -a i) := by
    funext u
    simp only [localProfileComb, translateComb, sub_eq_add_neg]
  rw [show (∫ u, localProfileComb φ c m x a u ^ 2) =
      testPairing (localProfileComb φ c m x a) (localProfileComb φ c m x a) by
        simp only [testPairing, pow_two], heq, h, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  have hcorr := bumpCorr_atomDilate_eq' (φ := φ) hc (-a j - -a i)
  change _ = c * (x i * x j * shellAutocorr φ ((a i - a j) / c))
  change bumpCorr (atomDilate φ c) (-a j - -a i) = _ at hcorr
  change x i * x j * bumpCorr (atomDilate φ c) (-a j - -a i) = _
  rw [hcorr, show -a j - -a i = a i - a j by ring]
  ring

private theorem integral_localProfileComb {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hs : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c)
    (m : ℕ) (x a : ℕ → ℝ) :
    (∫ u, localProfileComb φ c m x a u) = c * (∑ i ∈ range m, x i) * ∫ u, φ u := by
  have hi (i : ℕ) : Integrable (fun u => x i * φ ((u - a i) / c)) := by
    have hnice := ((profileDilate_nice hφ hs hc).translate (-a i)).const_mul_nice (x i)
    simpa only [sub_eq_add_neg] using hnice.1.integrable_of_hasCompactSupport hnice.2
  change (∫ u, ∑ i ∈ range m, x i * φ ((u - a i) / c)) = _
  rw [integral_finsetSum _ (fun i _ => hi i)]
  have hterm (i : ℕ) : (∫ u, x i * φ ((u - a i) / c)) = x i * (c * ∫ u, φ u) := by
    rw [integral_const_mul, integral_sub_right_eq_self (fun u => φ (u / c)),
      Measure.integral_comp_div, abs_of_pos hc, smul_eq_mul]
  simp_rw [hterm]
  rw [← sum_mul]
  ring

theorem integral_abs_localProfileComb_le {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hs : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c)
    (m : ℕ) (x a : ℕ → ℝ) :
    (∫ u, |localProfileComb φ c m x a u|) ≤
      c * (∑ i ∈ range m, |x i|) * ∫ u, |φ u| := by
  have habss : ∀ u, u ∉ Set.Icc 0 1 → |φ u| = 0 := fun u hu => by rw [hs u hu, abs_zero]
  have hf := localProfileComb_nice hφ hs hc m x a
  have hg := localProfileComb_nice hφ.abs habss hc m (fun i => |x i|) a
  have hi : Integrable (localProfileComb φ c m x a) :=
    hf.1.integrable_of_hasCompactSupport hf.2
  calc
    _ ≤ ∫ u, localProfileComb (fun v => |φ v|) c m (fun i => |x i|) a u := by
      apply integral_mono hi.abs (hg.1.integrable_of_hasCompactSupport hg.2)
      intro u
      simpa only [localProfileComb, abs_mul] using
        abs_sum_le_sum_abs (fun i => x i * φ ((u - a i) / c)) (range m)
    _ = _ := integral_localProfileComb hφ.abs habss hc m (fun i => |x i|) a

theorem localProfileComb_eq_zero {φ : ℝ → ℝ}
    (hs : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c A : ℝ} (hc : 0 < c)
    (m : ℕ) (x a : ℕ → ℝ) (ha : ∀ i ∈ range m, a i ∈ Set.Icc 0 A)
    {u : ℝ} (hu : u ∉ Set.Icc 0 (A + c)) : localProfileComb φ c m x a u = 0 := by
  apply sum_eq_zero
  intro i hi
  rw [hs _ (fun hm => hu ?_), mul_zero]
  have h0 : 0 ≤ u - a i := by simpa only [zero_mul] using (le_div_iff₀ hc).mp hm.1
  have h1 : u - a i ≤ c := (div_le_one hc).mp hm.2
  exact ⟨by linarith only [h0, (ha i hi).1], by linarith only [h1, (ha i hi).2]⟩

theorem localProfileComb_lipschitz {φ : ℝ → ℝ} {K c : ℝ}
    (hφ : ∀ u v, |φ u - φ v| ≤ K * |u - v|) (hc : 0 < c)
    (m : ℕ) (x a : ℕ → ℝ) (u v : ℝ) :
    |localProfileComb φ c m x a u - localProfileComb φ c m x a v| ≤
      ((∑ i ∈ range m, |x i|) * K / c) * |u - v| := by
  rw [localProfileComb, localProfileComb, ← sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ range m, |x i * φ ((u - a i) / c) - x i * φ ((v - a i) / c)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range m, |x i| * (K * (|u - v| / c)) := by
      apply sum_le_sum
      intro i _
      rw [← mul_sub, abs_mul]
      have hb := mul_le_mul_of_nonneg_left (hφ ((u - a i) / c) ((v - a i) / c))
        (abs_nonneg (x i))
      simpa only [← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hc] using hb
    _ = _ := by rw [← sum_mul]; ring

/-- Convergent rescaled centers give the corresponding autocorrelation Gram in
the leading Gamma energy. All support and norm bounds follow from the profile. -/
theorem tendsto_scaled_archForm_localProfileComb
    {ι : Type*} {l : Filter ι} {r : ι → ℝ} (hr : Tendsto r l atTop)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hs : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A) (m : ℕ) (x : ℕ → ℝ)
    (a : ι → ℕ → ℝ) (b : ℕ → ℝ)
    (ha : ∀ i ∈ range m, Tendsto (fun n => a n i) l (𝓝 (b i)))
    (hb : ∀ᶠ n in l, ∀ i ∈ range m, a n i ∈ Set.Icc 0 A) :
    Tendsto (fun n => r n / Real.log (r n) *
      archForm (fun u => localProfileComb φ c m x (a n) (r n * u))) l
      (𝓝 (c * ∑ i ∈ range m, ∑ j ∈ range m,
        x i * x j * shellAutocorr φ ((b i - b j) / c))) := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc hs
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφc hφ (by norm_num)
  have hLip (u v : ℝ) : |φ u - φ v| ≤ (K : ℝ) * |u - v| := by
    simpa only [Real.dist_eq] using hK.dist_le_mul u v
  let S : ℝ := ∑ i ∈ range m, |x i|
  let L : ℝ := S * K / c
  have hS : 0 ≤ S := sum_nonneg fun _ _ => abs_nonneg _
  have hL : 0 ≤ L := div_nonneg (mul_nonneg hS K.coe_nonneg) hc.le
  have hmass : Tendsto (fun n => r n *
      ∫ u, localProfileComb φ c m x (a n) (r n * u) ^ 2) l
      (𝓝 (c * ∑ i ∈ range m, ∑ j ∈ range m,
        x i * x j * shellAutocorr φ ((b i - b j) / c))) := by
    have hlim : Tendsto (fun n => c * ∑ i ∈ range m, ∑ j ∈ range m,
        x i * x j * shellAutocorr φ ((a n i - a n j) / c)) l
        (𝓝 (c * ∑ i ∈ range m, ∑ j ∈ range m,
          x i * x j * shellAutocorr φ ((b i - b j) / c))) := by
      apply tendsto_const_nhds.mul
      apply tendsto_finsetSum
      intro i hi
      apply tendsto_finsetSum
      intro j hj
      exact tendsto_const_nhds.mul ((continuous_shellAutocorr hφ hs).tendsto _ |>.comp
        (((ha i hi).sub (ha j hj)).div_const c))
    apply hlim.congr'
    filter_upwards [hr.eventually_gt_atTop 0] with n hrn
    rw [Measure.integral_comp_mul_left (fun v => localProfileComb φ c m x (a n) v ^ 2),
      abs_of_pos (inv_pos.mpr hrn), smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hrn.ne', one_mul, integral_sq_localProfileComb hφ.continuous hs hc]
  apply tendsto_scaled_archForm_of_shrinking_support hr (W := A + c) (K := L)
    (C := c * S * ∫ u, |φ u|) (add_pos_of_nonneg_of_pos hA hc) hL _ _ _ _ hmass
  · exact Eventually.of_forall fun n =>
      (contDiff_localProfileComb hφ c m x (a n)).comp (contDiff_const.mul contDiff_id)
  · filter_upwards [hb, hr.eventually_gt_atTop 0] with n hbn hrn
    intro u hu
    apply localProfileComb_eq_zero hs hc m x (a n) hbn
    intro hm
    apply hu
    exact ⟨nonneg_of_mul_nonneg_left (by simpa only [mul_comm] using hm.1) hrn,
      (le_div_iff₀ hrn).mpr (by simpa only [mul_comm] using hm.2)⟩
  · filter_upwards [hr.eventually_gt_atTop 0] with n hrn
    intro u v
    have h := localProfileComb_lipschitz hLip hc m x (a n) (r n * u) (r n * v)
    rw [← mul_sub, abs_mul, abs_of_pos hrn] at h
    simpa only [L, S, mul_assoc] using h
  · filter_upwards [hr.eventually_gt_atTop 0] with n hrn
    rw [Measure.integral_comp_mul_left (fun v => |localProfileComb φ c m x (a n) v|),
      abs_of_pos (inv_pos.mpr hrn), smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hrn.ne', one_mul]
    exact integral_abs_localProfileComb_le hφ.continuous hs hc m x (a n)

/-- The rescaled logarithmic coordinate of an integer at fixed distance tends
to that distance. -/
theorem tendsto_nat_mul_log_one_add_div (j : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) * Real.log (1 + j / N)) atTop (𝓝 j) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply squeeze_zero_norm' (a := fun N : ℕ => 2 * j ^ 2 / N)
  · filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop (0 : ℝ),
      tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * |j|)] with N hN hNj
    have ht : |j / (N : ℝ)| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos hN, div_le_iff₀ hN]
      linarith only [hNj]
    have hb := mul_le_mul_of_nonneg_left (abs_log_one_add_sub_le ht) hN.le
    have he : (N : ℝ) * Real.log (1 + j / N) - j =
        N * (Real.log (1 + j / N) - j / N) := by field_simp
    rw [Real.norm_eq_abs, he, abs_mul, abs_of_pos hN]
    calc
      _ ≤ (N : ℝ) * (2 * (j / N) ^ 2) := hb
      _ = _ := by field_simp
  · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

/-- Centers of the atoms `N,...,N+m-1`, measured at the literal horizon `N+m`. -/
def localIntegerCenter (m N j : ℕ) : ℝ :=
  ((N : ℝ) + m) * Real.log (1 + (j : ℝ) / N)

theorem tendsto_localIntegerCenter (m j : ℕ) :
    Tendsto (fun N => localIntegerCenter m N j) atTop (𝓝 (j : ℝ)) := by
  have hratio : Tendsto (fun N : ℕ => 1 + (m : ℝ) / N) atTop (𝓝 1) := by
    simpa only [add_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).add
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  have h := hratio.mul (tendsto_nat_mul_log_one_add_div (j : ℝ))
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop (0 : ℝ)] with N hN
  dsimp only [localIntegerCenter]
  field_simp

theorem localIntegerCenter_mem {m N j : ℕ} (hN : 0 < N) (hm : m ≤ N) (hj : j < m) :
    localIntegerCenter m N j ∈ Set.Icc 0 (2 * (m : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmr : (m : ℝ) ≤ N := by exact_mod_cast hm
  have hjr : (j : ℝ) ≤ m := by exact_mod_cast hj.le
  have harg : 0 < 1 + (j : ℝ) / N := by positivity
  have hlo : 0 ≤ Real.log (1 + (j : ℝ) / N) :=
    Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  have hup : Real.log (1 + (j : ℝ) / N) ≤ (j : ℝ) / N := by
    simpa only [add_sub_cancel_left] using Real.log_le_sub_one_of_pos harg
  constructor
  · exact mul_nonneg (by positivity) hlo
  · calc
      localIntegerCenter m N j ≤ ((N : ℝ) + m) * ((j : ℝ) / N) :=
        mul_le_mul_of_nonneg_left hup (by positivity)
      _ ≤ (2 * (N : ℝ)) * ((j : ℝ) / N) :=
        mul_le_mul_of_nonneg_right (by linarith only [hmr]) (by positivity)
      _ = 2 * (j : ℝ) := by field_simp
      _ ≤ 2 * (m : ℝ) := mul_le_mul_of_nonneg_left hjr (by norm_num)

/-- A neighboring integer block, translated to start at the origin, with atom
width `c/(N+m)`. -/
def localIntegerBlock (φ : ℝ → ℝ) (c : ℝ) (m : ℕ) (x : ℕ → ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  localProfileComb φ c m x (localIntegerCenter m N) (((N : ℝ) + m) * u)

/-- The leading Gamma Gram of a fixed neighboring integer block is exactly
the Toeplitz autocorrelation Gram of its profile. -/
theorem tendsto_localIntegerBlock_archForm {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hs : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c)
    (m : ℕ) (x : ℕ → ℝ) :
    Tendsto (fun N : ℕ => ((N : ℝ) + m) / Real.log ((N : ℝ) + m) *
      archForm (localIntegerBlock φ c m x N)) atTop
      (𝓝 (c * ∑ i ∈ range m, ∑ j ∈ range m,
        x i * x j * shellAutocorr φ (((i : ℝ) - j) / c))) := by
  have hr : Tendsto (fun N : ℕ => (N : ℝ) + m) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  apply tendsto_scaled_archForm_localProfileComb hr hφ hs hc
    (A := 2 * (m : ℝ)) (by positivity) m x (localIntegerCenter m) (fun j => (j : ℝ))
  · intro i _
    exact tendsto_localIntegerCenter m i
  · filter_upwards [eventually_ge_atTop (max m 1)] with N hN
    intro j hj
    exact localIntegerCenter_mem (by omega) (by omega) (mem_range.mp hj)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_localIntegerBlock_archForm
