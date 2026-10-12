import GaloisForLFunctions.RHTower.XiCosineShiftDefectTransportAllHeights
import GaloisForLFunctions.RHTower.ZetaZeroDensityInghamHuxley
import GaloisForLFunctions.RHTower.XiReflectionSelfIntersectionCharge
import GaloisForLFunctions.RHTower.WeilLagFunctionCriterion

/-!
# The cosine family is real-rooted up to a power-saving exceptional set

For `h > 0` let `A^h = cos(hD)Ξ = (Ξ(z+ih) + Ξ(z−ih))/2` (`cosProducer h`).

**Theorem** (`exists_windowDefectCount_le_ingham_huxley`).  For `0 < h ≤ ½` and `0 < ε ≤ 1` the
non-real zeros of `A^h` with real part in `[T, 2T]`, counted with multiplicity, number at most
`D (1 + log T)^B T^{(A(½+h) + ε)(½ − h)}` for large `T`, where `A` is the Ingham–Huxley exponent.

**Corollary** (`exists_windowDefectCount_le_rpow_lt_one`).  For every `0 < h ≤ ½` there is
`θ < 1` with at most `T^θ` such non-real zeros for large `T`.  Since `A^h` has `≍ T log T` zeros
with real part in `[T, 2T]`, all but a power-saving proportion of them are real.

**Proof.**  The sharp defect transport (`eventually_windowDefectCount_le_transport`) bounds the
non-real zeros by twice the number of zeros of `ξ` with `β ≥ ½ + h` and `T/2 ≤ γ ≤ 3T`, plus `2`.
The orders of these zeros are counted by their multiplicity copies
(`sum_order_le_ncard_of_subset`), which lie in three dyadic boxes `[T/2, T]`, `[T, 2T]`,
`[2T, 4T]`; each is bounded by the Ingham–Huxley estimate.  The exponent satisfies
`A(σ)(1 − σ) < 1` for `σ > ½` (`inghamHuxleyExponent_mul_lt_one`).

The power saving improves without limit as `h` grows and degenerates as `h → 0`, where the
threshold of the cosine family sits: `A^h` is real-rooted for all `h > 0` iff RH holds.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-- **Zero orders are counted by multiplicity copies.**  For a finite set `F` of zeros of `ξ` and a
finite set `S` of copies containing every copy above `F`, `Σ_{w ∈ F} ord_w ξ ≤ #S`. -/
theorem sum_order_le_ncard_of_subset {F : Finset ℂ} (hF : ∀ w ∈ F, xi w = 0)
    {S : Set XiZeroCopy} (hS : S.Finite) (hsub : ∀ q : XiZeroCopy, (q.1 : ℂ) ∈ F → q ∈ S) :
    ∑ w ∈ F, (analyticOrderAt xi w).toNat ≤ S.ncard := by
  classical
  set C := hS.toFinset.filter (fun q : XiZeroCopy => (q.1 : ℂ) ∈ F) with hC
  have hcard : C.card = ∑ w ∈ F, (C.filter (fun q => (q.1 : ℂ) = w)).card :=
    Finset.card_eq_sum_card_fiberwise fun q hq => (Finset.mem_filter.mp hq).2
  have hle : ∀ w ∈ F,
      (analyticOrderAt xi w).toNat ≤ (C.filter (fun q => (q.1 : ℂ) = w)).card := by
    intro w hw
    obtain ⟨q₀, hq₀⟩ := exists_xiZeroCopy_of_xi_eq_zero (hF w hw)
    have e : (analyticOrderAt xi w).toNat = (xiZeroCopyFiber q₀.1).card := by
      rw [card_xiZeroCopyFiber_eq_order_toNat, hq₀]
    rw [e]
    refine Finset.card_le_card fun q hq => ?_
    rw [mem_xiZeroCopyFiber] at hq
    have hqw : (q.1 : ℂ) = w := by rw [hq, hq₀]
    have hqF : (q.1 : ℂ) ∈ F := by rw [hqw]; exact hw
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hS.mem_toFinset.mpr (hsub q hqF), hqF⟩, hqw⟩
  calc ∑ w ∈ F, (analyticOrderAt xi w).toNat
      ≤ ∑ w ∈ F, (C.filter (fun q => (q.1 : ℂ) = w)).card := Finset.sum_le_sum hle
    _ = C.card := hcard.symm
    _ ≤ hS.toFinset.card := Finset.card_filter_le _ _
    _ = S.ncard := (Set.ncard_eq_toFinset_card S hS).symm

/-- The Ingham–Huxley exponent lies in `[2, 12/5]`. -/
theorem inghamHuxleyExponent_mem {σ : ℝ} (hσ : 1 / 2 < σ) :
    2 ≤ inghamHuxleyExponent σ ∧ inghamHuxleyExponent σ ≤ 12 / 5 := by
  unfold inghamHuxleyExponent
  split_ifs with h1 h2
  · have h0 : 0 < 2 - σ := by linarith
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ h0]; linarith
    · rw [div_le_iff₀ h0]; linarith
  · have h0 : 0 < 3 * σ - 1 := by linarith
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ h0]; linarith
    · rw [div_le_iff₀ h0]; linarith [not_le.mp h1]
  · norm_num

/-- **The Ingham–Huxley exponent saves a power**: `A(σ)(1 − σ) < 1` for `σ > ½`. -/
theorem inghamHuxleyExponent_mul_lt_one {σ : ℝ} (hσ : 1 / 2 < σ) :
    inghamHuxleyExponent σ * (1 - σ) < 1 := by
  unfold inghamHuxleyExponent
  split_ifs with h1 h2
  · have h0 : 0 < 2 - σ := by linarith
    rw [div_mul_eq_mul_div, div_lt_one h0]; linarith
  · have h0 : 0 < 3 * σ - 1 := by linarith
    rw [div_mul_eq_mul_div, div_lt_one h0]; linarith [not_le.mp h1]
  · linarith [not_le.mp h1]

/-- **Defects of the cosine family obey the Ingham–Huxley density bound.** -/
theorem exists_windowDefectCount_le_ingham_huxley {h ε : ℝ} (hh : 0 < h) (hh1 : h ≤ 1 / 2)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ B : ℕ, ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (windowDefectCount T (2 * T) h : ℝ) ≤
        D * (1 + Real.log T) ^ B * T ^ ((inghamHuxleyExponent (1 / 2 + h) + ε) * (1 / 2 - h)) := by
  classical
  set σ : ℝ := 1 / 2 + h with hσ
  set E : ℝ := (inghamHuxleyExponent σ + ε) * (1 / 2 - h) with hE
  have hσ1 : 1 / 2 < σ := by rw [hσ]; linarith
  have hσ2 : σ ≤ 1 := by rw [hσ]; linarith
  obtain ⟨hA2, hA12⟩ := inghamHuxleyExponent_mem hσ1
  have hE0 : 0 ≤ E := by rw [hE]; apply mul_nonneg <;> linarith
  have hE2 : E ≤ 2 := by
    rw [hE]
    nlinarith
  obtain ⟨D, hD, B, T₁, hT₁, hIH⟩ := exists_zeroHeightBox_ncard_le_ingham_huxley hσ1 hσ2 hε hε1
  have h1σ : (inghamHuxleyExponent σ + ε) * (1 - σ) = E := by rw [hE, hσ]; ring
  rw [h1σ] at hIH
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp (eventually_windowDefectCount_le_transport hh)
  set K : ℝ := 2 * (D * (2 + 4 * 2 ^ B)) + 2 with hK
  refine ⟨K, by rw [hK]; positivity, B, max T₂ (max (2 * T₁) 2), fun T hT => ?_⟩
  have hT₂T : T₂ ≤ T := (le_max_left _ _).trans hT
  have hT₁T : 2 * T₁ ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hT2 : 2 ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  have hT0 : 0 < T := by linarith
  -- the three dyadic boxes
  set S : Set XiZeroCopy := zeroHeightBox σ (T / 2) ∪ zeroHeightBox σ T ∪ zeroHeightBox σ (2 * T)
    with hSdef
  have hSfin : S.Finite :=
    ((zeroHeightBox_finite _ _).union (zeroHeightBox_finite _ _)).union (zeroHeightBox_finite _ _)
  set F := (boxFinsetLe (3 * T)).filter (fun w => 1 / 2 + h ≤ w.re ∧ T / 2 ≤ w.im) with hFdef
  have hF : ∀ w ∈ F, xi w = 0 := fun w hw =>
    (mem_boxFinsetLe.mp (Finset.mem_filter.mp hw).1).2.2.2.2
  have hsub : ∀ q : XiZeroCopy, (q.1 : ℂ) ∈ F → q ∈ S := by
    intro q hq
    obtain ⟨hbox, hre, him⟩ := Finset.mem_filter.mp hq
    have hb := mem_boxFinsetLe.mp hbox
    have him3 : (q.1 : ℂ).im ≤ 3 * T := hb.2.2.2.1
    rw [hSdef]
    by_cases h1 : (q.1 : ℂ).im ≤ T
    · exact Or.inl (Or.inl ⟨hre, him, by linarith⟩)
    · by_cases h2 : (q.1 : ℂ).im ≤ 2 * T
      · exact Or.inl (Or.inr ⟨hre, by linarith, h2⟩)
      · exact Or.inr ⟨hre, by linarith, by linarith⟩
  have hsum := sum_order_le_ncard_of_subset hF hSfin hsub
  have hncard : (S.ncard : ℝ) ≤ (zeroHeightBox σ (T / 2)).ncard + (zeroHeightBox σ T).ncard
      + (zeroHeightBox σ (2 * T)).ncard := by
    have h1 := Set.ncard_union_le (zeroHeightBox σ (T / 2) ∪ zeroHeightBox σ T)
      (zeroHeightBox σ (2 * T))
    have h2 := Set.ncard_union_le (zeroHeightBox σ (T / 2)) (zeroHeightBox σ T)
    exact_mod_cast (h1.trans (Nat.add_le_add_right h2 _))
  -- the Ingham–Huxley bounds at the three heights
  set P : ℝ := (1 + Real.log T) ^ B * T ^ E with hP
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hP1 : 1 ≤ P := by
    rw [hP]
    have : 1 ≤ (1 + Real.log T) ^ B := one_le_pow₀ (by linarith)
    have : 1 ≤ T ^ E := Real.one_le_rpow (by linarith) hE0
    nlinarith
  have hb1 : ((zeroHeightBox σ (T / 2)).ncard : ℝ) ≤ D * P := by
    have := hIH (T / 2) (by linarith)
    refine this.trans ?_
    rw [hP, ← mul_assoc]
    have hl : (1 + Real.log (T / 2)) ^ B ≤ (1 + Real.log T) ^ B := by
      have : Real.log (T / 2) ≤ Real.log T := Real.log_le_log (by linarith) (by linarith)
      have h0 : 0 ≤ 1 + Real.log (T / 2) := by
        have := Real.log_nonneg (show (1 : ℝ) ≤ T / 2 by linarith); linarith
      exact pow_le_pow_left₀ h0 (by linarith) B
    have hr : (T / 2) ^ E ≤ T ^ E := Real.rpow_le_rpow (by linarith) (by linarith) hE0
    have := mul_le_mul hl hr (by positivity) (by positivity)
    nlinarith
  have hb2 : ((zeroHeightBox σ T).ncard : ℝ) ≤ D * P := by
    have := hIH T (by linarith)
    rw [hP, ← mul_assoc]; exact this
  have hb3 : ((zeroHeightBox σ (2 * T)).ncard : ℝ) ≤ D * (4 * 2 ^ B) * P := by
    have := hIH (2 * T) (by linarith)
    refine this.trans ?_
    have hl : (1 + Real.log (2 * T)) ^ B ≤ 2 ^ B * (1 + Real.log T) ^ B := by
      rw [← mul_pow]
      have hlog2 : Real.log (2 * T) = Real.log 2 + Real.log T :=
        Real.log_mul (by norm_num) (by linarith)
      have hl2 : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9; linarith
      have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      exact pow_le_pow_left₀ (by rw [hlog2]; linarith) (by rw [hlog2]; linarith) B
    have hr : (2 * T) ^ E ≤ 4 * T ^ E := by
      rw [Real.mul_rpow (by norm_num) (by linarith)]
      have : (2 : ℝ) ^ E ≤ 4 := by
        calc (2 : ℝ) ^ E ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hE2
          _ = 4 := by norm_num
      have := Real.rpow_nonneg (show (0 : ℝ) ≤ T by linarith) E
      nlinarith
    have hmul := mul_le_mul hl hr (by positivity) (by positivity)
    have hD' : D * ((1 + Real.log (2 * T)) ^ B * (2 * T) ^ E) ≤
        D * ((2 ^ B * (1 + Real.log T) ^ B) * (4 * T ^ E)) :=
      mul_le_mul_of_nonneg_left hmul hD
    calc D * (1 + Real.log (2 * T)) ^ B * (2 * T) ^ E
        = D * ((1 + Real.log (2 * T)) ^ B * (2 * T) ^ E) := by ring
      _ ≤ D * ((2 ^ B * (1 + Real.log T) ^ B) * (4 * T ^ E)) := hD'
      _ = D * (4 * 2 ^ B) * P := by rw [hP]; ring
  -- assembly
  have htr := hT₂ T hT₂T
  have hcast : (windowDefectCount T (2 * T) h : ℝ) ≤ 2 * (S.ncard : ℝ) + 2 := by
    have h1 : windowDefectCount T (2 * T) h ≤ 2 * S.ncard + 2 := by
      refine htr.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 ?_) 2)
      rw [hFdef] at hsum
      exact hsum
    exact_mod_cast h1
  calc (windowDefectCount T (2 * T) h : ℝ) ≤ 2 * (S.ncard : ℝ) + 2 := hcast
    _ ≤ 2 * (D * P + D * P + D * (4 * 2 ^ B) * P) + 2 := by linarith
    _ = 2 * (D * (2 + 4 * 2 ^ B)) * P + 2 := by ring
    _ ≤ 2 * (D * (2 + 4 * 2 ^ B)) * P + 2 * P := by linarith
    _ = K * (1 + Real.log T) ^ B * T ^ E := by rw [hK, hP]; ring

/-- **The cosine family is real-rooted up to a power-saving exceptional set.**  For every
`0 < h ≤ ½` there are `θ < 1` and `T₀` such that `cos(hD)Ξ` has at most `T^θ` non-real zeros,
counted with multiplicity, with real part in `[T, 2T]`, for every `T ≥ T₀`. -/
theorem exists_windowDefectCount_le_rpow_lt_one {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1 / 2) :
    ∃ θ : ℝ, θ < 1 ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → (windowDefectCount T (2 * T) h : ℝ) ≤ T ^ θ := by
  set σ : ℝ := 1 / 2 + h with hσ
  have hσ1 : 1 / 2 < σ := by rw [hσ]; linarith
  have hσ2 : σ ≤ 1 := by rw [hσ]; linarith
  set g : ℝ := 1 - inghamHuxleyExponent σ * (1 - σ) with hg
  have hg0 : 0 < g := by rw [hg]; linarith [inghamHuxleyExponent_mul_lt_one hσ1]
  set ε : ℝ := min 1 g with hε
  have hε0 : 0 < ε := lt_min one_pos hg0
  have hε1 : ε ≤ 1 := min_le_left _ _
  obtain ⟨D, hD, B, T₁, hT₁⟩ := exists_windowDefectCount_le_ingham_huxley hh hh1 hε0 hε1
  set E : ℝ := (inghamHuxleyExponent σ + ε) * (1 / 2 - h) with hE
  have h1σ : 1 / 2 - h = 1 - σ := by rw [hσ]; ring
  -- `E ≤ 1 − g/2`
  have hEg : E ≤ 1 - g / 2 := by
    have hεg : ε ≤ g := min_le_right _ _
    have h12 : 1 - σ ≤ 1 / 2 := by linarith
    have h0 : 0 ≤ 1 - σ := by linarith
    rw [hE, h1σ]
    have : ε * (1 - σ) ≤ g / 2 := by nlinarith
    nlinarith
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow B (c := g / 4) (by positivity) D)
  refine ⟨1 - g / 4, by linarith, max (max T₁ T₂) 1, fun T hT => ?_⟩
  have hT1 : 1 ≤ T := (le_max_right _ _).trans hT
  have hTT₁ : T₁ ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans hT)
  have hTT₂ : T₂ ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans hT)
  have hpoly := hT₂ T hTT₂
  calc (windowDefectCount T (2 * T) h : ℝ) ≤ D * (1 + Real.log T) ^ B * T ^ E := hT₁ T hTT₁
    _ ≤ T ^ (g / 4) * T ^ (1 - g / 2) :=
        mul_le_mul hpoly (Real.rpow_le_rpow_of_exponent_le hT1 hEg) (by positivity)
          (by positivity)
    _ = T ^ (1 - g / 4) := by
        rw [← Real.rpow_add (by linarith)]; ring_nf

end

end RHTower
