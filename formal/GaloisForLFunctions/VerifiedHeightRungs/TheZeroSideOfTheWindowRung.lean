import GaloisForLFunctions.VerifiedHeightRungs.JensenEntries
import GaloisForLFunctions.VerifiedHeightRungs.SeparatedNodesControlTheTransform
import GaloisForLFunctions.VerifiedHeightRungs.TheNormalizedSmoothingKeepsThePoles

/-!
# The zero side of the window rung

Below a verified height the smoothed Weil form has nonnegative summands, at least half of `|h_f(γ)|²` on chosen zeros;
above it the summands form a tail (`re_W_smoothed_ge_of_verified`). `window_numeric` is the final balance.
-/

open Complex MeasureTheory Real Set Filter Topology Finset
open scoped ComplexConjugate

namespace GaloisForLFunctions.VerifiedHeightRungs

open _root_.RHTower Zeta23 GaloisForLFunctions.SquareRootThreshold

noncomputable section

/-- On-line zeros from a verified height, in the carrier of `ζ`. -/
theorem re_eq_half_of_mem_carrier {T : ℝ} (hRH : RHVerifiedThrough T) {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier)
    (hT : |ρ.im| ≤ T) : ρ.re = 1 / 2 := by
  have hxi : xi ρ = 0 := (xi_eq_zero_iff hρ.2.1 (by
    intro he
    have hh := hρ.2.2
    rw [he] at hh
    norm_num at hh)).mpr hρ.1
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
  have h := im_xiSpectralPoint_eq_zero hRH q (by rw [re_xiSpectralPoint, hq]; exact hT)
  rw [im_xiSpectralPoint, hq] at h
  linarith only [h]

/-- **The zero side.** Above the verified height the summands are a tail; below they are nonnegative and at least half of
`|h_f(γ)|²` on a chosen finite set of zeros. -/
theorem re_W_smoothed_ge_of_verified {a b T : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hb1 : b ≤ 1) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Set.Icc (-a) a) (hT : 0 ≤ T) (hRH : RHVerifiedThrough T)
    (S : Finset zetaZeroConfig.carrier)
    (hS : ∀ ρ ∈ S, |(ρ : ℂ).im| ≤ T ∧ 2 * (b * (ρ : ℂ).im) ^ 2 ≤ 1) :
    1 / 2 * ∑ ρ ∈ S, ‖paperFT f ((ρ : ℂ).im : ℝ)‖ ^ 2 -
        Real.exp a * (∫ u, ‖f u‖) ^ 2 * (Real.exp 1 * 400 ^ 2 / b ^ 6) * (24 * 240 * Real.log 3 / (1 + T)) ≤
      (zetaZeroConfig.W f (smoothedTest b f)).re := by
  classical
  have hfc : HasCompactSupport f := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hfs' : ∀ u, f u ≠ 0 → |u| ≤ a := fun u hu => abs_le.mpr (hfs (subset_tsupport f hu))
  obtain ⟨K, hK⟩ : ∃ K, K = Real.exp a * (∫ u, ‖f u‖) ^ 2 * (Real.exp 1 * 400 ^ 2 / b ^ 6) := ⟨_, rfl⟩
  rw [← hK]
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  let u : zetaZeroConfig.carrier → ℝ := fun ρ =>
    if ρ ∈ S then 1 / 2 * ‖paperFT f ((ρ : ℂ).im : ℝ)‖ ^ 2 else 0
  have hterm (ρ : zetaZeroConfig.carrier) : u ρ - K * highTailErr zetaZeroConfig T ρ ≤
      (zetaZeroConfig.Wsummand f (smoothedTest b f) ρ).re := by
    by_cases hρT : |(ρ : ℂ).im| ≤ T
    · have hre := re_eq_half_of_mem_carrier hRH ρ.2 hρT
      have hgam : gammaOf (ρ : ℂ) = (((ρ : ℂ).im : ℝ) : ℂ) := by
        apply Complex.ext
        · simp [WeilEF.gammaOf_re]
        · simp [WeilEF.gammaOf_im, hre]
      obtain ⟨r, hr, hr0, hr1⟩ := kernelQ_real hb hb1 (ρ : ℂ).im
      rw [highTailErr, if_pos hρT, mul_zero, sub_zero, Wsummand_smoothedTest zetaZeroConfig hb.le hf.continuous hfc,
        hgam, Complex.conj_ofReal, hr]
      have hval : ((zetaZeroConfig.mult ρ : ℕ) : ℂ) * (paperFT f ((ρ : ℂ).im : ℝ) *
          conj (paperFT f ((ρ : ℂ).im : ℝ)) * (r : ℂ) ^ 2) =
          (((zetaZeroConfig.mult ρ : ℕ) * ‖paperFT f ((ρ : ℂ).im : ℝ)‖ ^ 2 * r ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj']
        push_cast
        ring
      rw [hval, Complex.ofReal_re]
      have hm1 : (1 : ℝ) ≤ zetaZeroConfig.mult ρ := by
        exact_mod_cast zetaZeroConfig.one_le_mult ρ ρ.2
      have hN := sq_nonneg ‖paperFT f ((ρ : ℂ).im : ℝ)‖
      by_cases hρS : ρ ∈ S
      · have hu : u ρ = 1 / 2 * ‖paperFT f ((ρ : ℂ).im : ℝ)‖ ^ 2 := if_pos hρS
        rw [hu]
        have h2 := (hS ρ hρS).2
        have hr2 : 1 / 2 ≤ r ^ 2 := by linarith only [hr1, h2]
        calc
          1 / 2 * ‖paperFT f ((ρ : ℂ).im : ℝ)‖ ^ 2 ≤ 1 * ‖paperFT f ((ρ : ℂ).im : ℝ)‖ ^ 2 * r ^ 2 := by
            nlinarith only [mul_le_mul_of_nonneg_left hr2 hN]
          _ ≤ _ := by
            refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg r)
            exact mul_le_mul_of_nonneg_right hm1 hN
      · have hu : u ρ = 0 := if_neg hρS
        rw [hu]
        positivity
    · have hρS : ρ ∉ S := fun h => hρT (hS ρ h).1
      have hu : u ρ = 0 := if_neg hρS
      rw [hu, zero_sub, highTailErr, if_neg hρT]
      have h := re_Wsummand_smoothedTest_ge_high zetaZeroConfig ha hb hb1 hf.continuous hfs' ρ.2
      refine le_trans (le_of_eq ?_) h
      rw [hK]
      have hD : (0 : ℝ) < 1 + |(ρ : ℂ).im| := by positivity
      field_simp
  obtain ⟨hs4, t4⟩ := highTailErr_summable_le zetaZeroConfig (A₀ := 240) (by norm_num) zeta_unit_count_le_240 hT
  have hA : HasCompactSupport (smoothedTest b f) := hasCompactSupport_smoothedTest hb.le hfc
  have hAs : tsupport (smoothedTest b f) ⊆ Set.Icc (-(a + 2)) (a + 2) :=
    (tsupport_smoothedTest_subset hb.le hfs).trans
      (Set.Icc_subset_Icc (by linarith only [hb1]) (by linarith only [hb1]))
  have hfA : tsupport f ⊆ Set.Icc (-(a + 2)) (a + 2) :=
    hfs.trans (Set.Icc_subset_Icc (by linarith only) (by linarith only))
  have hW := (W_eq_pole_add_integral_bilinear hf (smoothedTest_contDiff hb.le hf hfc) hfA hAs).1
  have hre := (Complex.hasSum_re hW.hasSum).summable
  have hsumu : Summable u := summable_of_finite_support (S.finite_toSet.subset fun ρ hρ => by
    by_contra hc
    exact hρ (if_neg hc))
  have hle := Summable.tsum_le_tsum hterm (hsumu.sub (hs4.mul_left K)) hre
  rw [hsumu.tsum_sub (hs4.mul_left K), tsum_mul_left] at hle
  have hut : ∑' ρ, u ρ = 1 / 2 * ∑ ρ ∈ S, ‖paperFT f ((ρ : ℂ).im : ℝ)‖ ^ 2 := by
    rw [tsum_eq_sum (s := S) (fun ρ hρ => if_neg hρ), Finset.mul_sum]
    exact Finset.sum_congr rfl fun ρ hρ => if_pos hρ
  rw [hut] at hle
  rw [ZeroConfig.W, Complex.re_tsum hW]
  have ht := mul_le_mul_of_nonneg_left t4 hK0
  linarith only [hle, ht]

/-- **The nodes.** One verified zero in each cell of length `σ` above `(n+1)σ`. -/
theorem exists_window_nodes {T σ : ℝ} {n : ℕ} (hRH : RHVerifiedThrough T) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hn1 : gapHeight (σ / 2) ≤ ((n : ℝ) + 1) * σ)
    (hT1 : 3 * ((n : ℝ) + 1) * σ + Real.exp (gapScale (σ / 2)) + 1 ≤ T) :
    ∃ node : ℕ → zetaZeroConfig.carrier,
      (∀ j ∈ Finset.range (n + 1), ((n : ℝ) + 1 + 2 * j) * σ ≤ ((node j : ℂ)).im ∧
        ((node j : ℂ)).im ≤ ((n : ℝ) + 1 + 2 * j + 1) * σ) ∧
      Set.InjOn node (Finset.range (n + 1) : Finset ℕ) := by
  have hE1 := Real.exp_pos (gapScale (σ / 2))
  have hnode : ∀ j : ℕ, j ∈ Finset.range (n + 1) → ∃ ρ : zetaZeroConfig.carrier,
      ((n : ℝ) + 1 + 2 * j) * σ ≤ (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ ((n : ℝ) + 1 + 2 * j + 1) * σ := by
    intro j hj
    have hjn : (j : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    obtain ⟨c, hc⟩ : ∃ c, c = ((n : ℝ) + 1 + 2 * j) * σ + σ / 2 := ⟨_, rfl⟩
    have hc0 : 0 ≤ c := by rw [hc]; positivity
    have hcup : c ≤ 3 * ((n : ℝ) + 1) * σ := by
      rw [hc]
      nlinarith only [hσ, hjn]
    have hclow : ((n : ℝ) + 1) * σ ≤ c := by
      rw [hc]
      nlinarith only [hσ, hj0]
    have hgap : gapHeight (σ / 2) ≤ |c| := by
      rw [abs_of_nonneg hc0]
      exact hn1.trans hclow
    have hon : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im - c| ≤ Real.exp (gapScale (σ / 2)) → ρ.re = 1 / 2 := by
      intro ρ hρ hρc
      refine re_eq_half_of_mem_carrier hRH hρ ?_
      have h1 : |ρ.im| ≤ |ρ.im - c| + |c| := by
        have := abs_sub_abs_le_abs_sub ρ.im c
        linarith only [this]
      rw [abs_of_nonneg hc0] at h1
      linarith only [h1, hρc, hcup, hT1]
    obtain ⟨ρ, hρ, hρc⟩ := exists_zero_near_of_onLine (σ := σ / 2) (by positivity) (by linarith only [hσ1, hσ]) hgap hon
    obtain ⟨h1, h2⟩ := abs_lt.1 hρc
    refine ⟨⟨ρ, hρ⟩, ?_, ?_⟩
    · change _ ≤ ρ.im
      rw [hc] at h1
      linarith only [h1]
    · change ρ.im ≤ _
      rw [hc] at h2
      nlinarith only [h2]
  have hne : Nonempty zetaZeroConfig.carrier := by
    obtain ⟨ρ, -⟩ := hnode 0 (Finset.mem_range.2 (Nat.succ_pos n))
    exact ⟨ρ⟩
  have hnode' : ∀ j : ℕ, ∃ ρ : zetaZeroConfig.carrier, j ∈ Finset.range (n + 1) →
      ((n : ℝ) + 1 + 2 * j) * σ ≤ (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ ((n : ℝ) + 1 + 2 * j + 1) * σ := by
    intro j
    by_cases hj : j ∈ Finset.range (n + 1)
    · obtain ⟨ρ, hρ⟩ := hnode j hj
      exact ⟨ρ, fun _ => hρ⟩
    · exact ⟨hne.some, fun h => absurd h hj⟩
  choose node hnodeP using hnode'
  refine ⟨node, hnodeP, ?_⟩
  intro i hi j hj hij
  by_contra hne
  have hvij : ((node i : ℂ)).im = ((node j : ℂ)).im := by rw [hij]
  have h1 := hnodeP i hi
  have h2 := hnodeP j hj
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h3 : (i : ℝ) + 1 ≤ j := by exact_mod_cast hlt
    nlinarith only [h1.2, h2.1, hvij, h3, hσ]
  · have h3 : (j : ℝ) + 1 ≤ i := by exact_mod_cast hgt
    nlinarith only [h1.1, h2.2, hvij, h3, hσ]

/-- The final balance, in real variables. -/
theorem window_numeric {κi ϖ b D₀ T₁ K Sn F Tail Wg Wf M R D a q : ℝ} (hκ1 : 1 / 2 ≤ κi) (hκ2 : κi ≤ 1)
    (hϖ : b ^ 2 / 2560 ≤ ϖ) (hzero : 1 / 2 * Sn - Tail ≤ Wg)
    (hself : κi * Wg + ϖ * (2 * π * F) - D * M * (2 * T₁) ≤ Wf) (hD0 : 0 ≤ D) (hD : D ≤ b ^ 2 * D₀) (hD₀ : 0 ≤ D₀)
    (hM : M = K * Sn + R) (hR0 : 0 ≤ R) (hR : R ≤ 4 * a * F * q) (h1 : 8 * T₁ * D₀ * K * b ^ 2 ≤ 1)
    (h2 : 8 * a * T₁ * D₀ * q ≤ π / 2560) (hTail0 : 0 ≤ Tail) (hTail : Tail ≤ π * b ^ 2 / 2560 * F) (hSn : 0 ≤ Sn)
    (hF : 0 ≤ F) (hT₁ : 0 ≤ T₁) (hK : 0 ≤ K) : 0 ≤ Wf := by
  have hπ := Real.pi_pos
  have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  -- The cost of the low band.
  have hcost : D * M * (2 * T₁) ≤ 1 / 4 * Sn + π * b ^ 2 / 2560 * F := by
    have h3 : D * M * (2 * T₁) ≤ b ^ 2 * D₀ * M * (2 * T₁) := by
      have := mul_le_mul_of_nonneg_right hD hM0
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have h4 : M ≤ K * Sn + 4 * a * F * q := by rw [hM]; linarith only [hR]
    have h5 : b ^ 2 * D₀ * M * (2 * T₁) ≤ b ^ 2 * D₀ * (K * Sn + 4 * a * F * q) * (2 * T₁) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left h4 (by positivity)
    have e : b ^ 2 * D₀ * (K * Sn + 4 * a * F * q) * (2 * T₁) =
        (8 * T₁ * D₀ * K * b ^ 2) * (Sn / 4) + (8 * a * T₁ * D₀ * q) * (b ^ 2 * F) := by ring
    have h6 : (8 * T₁ * D₀ * K * b ^ 2) * (Sn / 4) ≤ 1 * (Sn / 4) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h7 : (8 * a * T₁ * D₀ * q) * (b ^ 2 * F) ≤ π / 2560 * (b ^ 2 * F) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    rw [e] at h5
    linarith only [h3, h5, h6, h7]
  -- The node terms of the zero side.
  have hzeroκ : 1 / 4 * Sn - Tail ≤ κi * Wg := by
    have h3 := mul_le_mul_of_nonneg_left hzero (by linarith only [hκ1] : 0 ≤ κi)
    have h4 : κi * Tail ≤ 1 * Tail := mul_le_mul_of_nonneg_right hκ2 hTail0
    have h5 : 1 / 2 * (1 / 2 * Sn) ≤ κi * (1 / 2 * Sn) :=
      mul_le_mul_of_nonneg_right hκ1 (by positivity)
    nlinarith only [h3, h4, h5]
  have hmass : π * b ^ 2 / 1280 * F ≤ ϖ * (2 * π * F) := by
    have := mul_le_mul_of_nonneg_right hϖ (by positivity : 0 ≤ 2 * π * F)
    refine le_trans (le_of_eq ?_) this
    ring
  have e2 : π * b ^ 2 / 1280 * F = 2 * (π * b ^ 2 / 2560 * F) := by ring
  linarith only [hself, hcost, hzeroκ, hmass, hTail, e2]

end

end GaloisForLFunctions.VerifiedHeightRungs

#print axioms GaloisForLFunctions.VerifiedHeightRungs.re_W_smoothed_ge_of_verified
#print axioms GaloisForLFunctions.VerifiedHeightRungs.window_numeric
