import GaloisForLFunctions.RHTower.ZetaNotchBohrLift

/-!
# The main term of a smooth twist

For a finite set `P` of primes and an exponent vector `b : P → ℤ`, write `h = h(b)`, `k = k(b)` for
the reduced numerator and denominator and `N = hk`. Combining the diagonal split
(`exists_norm_twistedMoment_sub_diag_le`), the diagonal law (`exists_norm_diagMain_sub_le`) and the
near-resonant mass (`tsum_nearRes_le`) (`exists_norm_twistedMoment_vec_sub_le`):

`‖∫ ω|ζ|² e^{−iλ(b)t} − N^{−1/2} ∫ ω(t) log t dt‖ ≤ N^{−1/2}·2L(C + 2 log N)
    + C (24 δ k L^{3/2} + L²/(Lδ)^K + L² e^{−L²/32})`,

with `N^{−1/2} = Π_p p^{−|b_p|/2}`. Summed against the Bohr coefficients of the notch weight
(`norm_weightedMoment_sub_main_le`), the Euler factors at `P` cancel the lifted main terms of all
smooth twists `n ≠ n₀`, and the twist at `n₀` keeps `ε Π_p (1 − 1/p) ∫ ω log t`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

namespace RHTower.ZetaNotch

open RHTower.SmoothNumbers

variable {P : Finset ℕ}

/-- The remainder envelope of a single twist. -/
def twistEnvelope (C L δ : ℝ) (K : ℕ) (b : P → ℤ) : ℝ :=
  (∏ p : P, primeHalf p ^ (b p).natAbs) * (2 * L * (C + 2 * Real.log ((vecNum b : ℝ) * vecDen b)))
    + C * (24 * δ * vecDen b * L * Real.sqrt L + L ^ 2 / (L * δ) ^ K +
      L ^ 2 * Real.exp (-(L ^ 2) / 32))

theorem primeHalf_nonneg (p : ℕ) : 0 ≤ primeHalf p := inv_nonneg.mpr (Real.sqrt_nonneg _)

/-- The remainder envelope of a coprime twist `h/k`. -/
def hkEnvelope (C L δ : ℝ) (K : ℕ) (h k : ℕ) : ℝ :=
  (Real.sqrt ((h : ℝ) * k))⁻¹ * (2 * L * (C + 2 * Real.log ((h : ℝ) * k)))
    + C * (24 * δ * k * L * Real.sqrt L + L ^ 2 / (L * δ) ^ K +
      L ^ 2 * Real.exp (-(L ^ 2) / 32))

/-- **Main term of a coprime twist**:
`‖∫ ω|ζ|² (k/h)^{it} − (hk)^{−1/2} ∫ ω log t‖ ≤ hkEnvelope`. -/
theorem exists_norm_twistedMoment_hk_sub_le (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L δ : ℝ}, 16 ≤ L → 0 < δ → δ ≤ 1 / 4 → ∀ {h k : ℕ}, 0 < h → 0 < k →
      Nat.Coprime h k →
      ‖twistedMoment L (Real.log h - Real.log k) -
          (((Real.sqrt ((h : ℝ) * k))⁻¹ : ℝ) : ℂ) * logWindow L‖ ≤
        hkEnvelope C L δ K h k := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_twistedMoment_sub_diag_le K
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_diagMain_sub_le
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun {L δ} hL hδ hδ4 {h k} hh0 hk0 hcop => ?_⟩
  have hL0 : 0 < L := by linarith
  set N : ℝ := (h : ℝ) * k with hN
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh0
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
    nlinarith
  set w : ℝ := (Real.sqrt N)⁻¹ with hw
  have hw0 : 0 ≤ w := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hwN : ((Real.sqrt N : ℂ))⁻¹ = (w : ℂ) := by rw [hw, Complex.ofReal_inv]
  have hE1 := h₁ hL hδ hh0 hk0 hcop
  rw [show ((h : ℝ) * (k : ℝ)) = N from rfl, hwN] at hE1
  have hD := h₂ hL hN1
  have hwhat := norm_windowHat_le hL0 0
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hnear : nearMass L h k δ ≤ 24 * δ * k * Real.sqrt L :=
    tsum_nearRes_le hh0 hk0 hδ hδ4 hL0
  set ξ : ℝ := Real.log h - Real.log k with hξ
  have hsplit : twistedMoment L ξ - (w : ℂ) * logWindow L =
      (twistedMoment L ξ - (w : ℂ) * diagMain L N) +
        (w : ℂ) * (diagMain L N - (logWindow L - windowHat L 0 * (Real.log N : ℂ))) -
        (w : ℂ) * (windowHat L 0 * (Real.log N : ℂ)) := by ring
  rw [hsplit]
  have hA : ‖(w : ℂ) * (diagMain L N - (logWindow L - windowHat L 0 * (Real.log N : ℂ)))‖ ≤
      w * (2 * L * (max C₁ C₂ + Real.log N)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
    refine mul_le_mul_of_nonneg_left (hD.trans ?_) hw0
    gcongr
    exact le_max_right _ _
  have hB : ‖(w : ℂ) * (windowHat L 0 * (Real.log N : ℂ))‖ ≤ w * (2 * L * Real.log N) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogN]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hwhat hlogN) hw0
  have hC : ‖twistedMoment L ξ - (w : ℂ) * diagMain L N‖ ≤
      max C₁ C₂ * (24 * δ * k * L * Real.sqrt L + L ^ 2 / (L * δ) ^ K +
        L ^ 2 * Real.exp (-(L ^ 2) / 32)) := by
    refine hE1.trans ?_
    have hq : 0 ≤ L ^ 2 / (L * δ) ^ K + L ^ 2 * Real.exp (-(L ^ 2) / 32) := by positivity
    calc C₁ * (L * nearMass L h k δ + L ^ 2 / (L * δ) ^ K + L ^ 2 * Real.exp (-(L ^ 2) / 32))
        ≤ C₁ * (L * (24 * δ * k * Real.sqrt L) + L ^ 2 / (L * δ) ^ K +
            L ^ 2 * Real.exp (-(L ^ 2) / 32)) := by gcongr
      _ ≤ max C₁ C₂ * (24 * δ * k * L * Real.sqrt L + L ^ 2 / (L * δ) ^ K +
            L ^ 2 * Real.exp (-(L ^ 2) / 32)) := by
          rw [show L * (24 * δ * k * Real.sqrt L) = 24 * δ * k * L * Real.sqrt L by ring]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  set X := twistedMoment L ξ - (w : ℂ) * diagMain L N with hX
  set Y := (w : ℂ) * (diagMain L N - (logWindow L - windowHat L 0 * (Real.log N : ℂ))) with hY
  set Z := (w : ℂ) * (windowHat L 0 * (Real.log N : ℂ)) with hZ
  have htri : ‖X + Y - Z‖ ≤ ‖X‖ + ‖Y‖ + ‖Z‖ := by
    have h1 := norm_sub_le (X + Y) Z
    have h2 := norm_add_le X Y
    linarith
  refine htri.trans ?_
  unfold hkEnvelope
  rw [← hN, ← hw]
  nlinarith [hA, hB, hC]

/-- **Main term of a smooth twist.** -/
theorem exists_norm_twistedMoment_vec_sub_le (hP : ∀ p ∈ P, p.Prime) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L δ : ℝ}, 16 ≤ L → 0 < δ → δ ≤ 1 / 4 → ∀ b : P → ℤ,
      ‖twistedMoment L (vecFreq b) -
          ((∏ p : P, primeHalf p ^ (b p).natAbs : ℝ) : ℂ) * logWindow L‖ ≤
        twistEnvelope C L δ K b := by
  obtain ⟨C, hC, hmain⟩ := exists_norm_twistedMoment_hk_sub_le K
  refine ⟨C, hC, fun {L δ} hL hδ hδ4 b => ?_⟩
  have h := hmain hL hδ hδ4 (vecNum_pos hP b) (vecDen_pos hP b) (coprime_vecNum_vecDen hP b)
  unfold hkEnvelope at h
  unfold twistEnvelope
  rw [← vecFreq_eq hP b, inv_sqrt_vecNum_mul_vecDen b] at h
  exact h

/-! ## Bohr summation over the modes -/

theorem mem_bohrModes_neg_one : (-1 : ℤ) ∈ bohrModes := by decide
theorem mem_bohrModes_zero : (0 : ℤ) ∈ bohrModes := by decide
theorem mem_bohrModes_one : (1 : ℤ) ∈ bohrModes := by decide

/-- The lifted main terms cancel except at `n = n₀`:
`Σ_{j,c} e_j(−ε) E(c) Π_p s_p^{|b_p|} = ε Π_p (1 − s_p²) [n = n₀]`. -/
theorem sum_modeCoeff_mul_weight {n n₀ : ℕ} (hn : IsSmoothOver P n) (hn₀ : IsSmoothOver P n₀)
    (ε : ℝ) :
    ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
        modeCoeff ε j c * ∏ p : P, primeHalf p ^ ((vecOf P n - (j • vecOf P n₀ + c)) p).natAbs =
      if n = n₀ then ε * ∏ p : P, (1 - primeHalf p ^ 2) else 0 := by
  classical
  have hj : ∀ j : ℤ, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
      modeCoeff ε j c * ∏ p : P, primeHalf p ^ ((vecOf P n - (j • vecOf P n₀ + c)) p).natAbs =
      bohrCoeff (-ε) j * (if vecOf P n - j • vecOf P n₀ = 0 then
        ∏ p : P, (1 - primeHalf p ^ 2) else 0) := by
    intro j
    simp_rw [modeCoeff, mul_assoc, ← Finset.mul_sum]
    congr 1
    rw [← sum_bohrVec_mul_prod_pow (fun p : P => primeHalf p) (vecOf P n - j • vecOf P n₀)]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun p _ => ?_
    congr 2
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hj j), sum_bohrModes]
  have hm1 : ¬ (vecOf P n - (-1 : ℤ) • vecOf P n₀ = 0) := by
    rw [vecOf_sub_smul_eq_zero_iff hn hn₀ mem_bohrModes_neg_one]
    rintro ⟨h, _⟩
    exact absurd h (by decide)
  have h0 : ¬ (vecOf P n - (0 : ℤ) • vecOf P n₀ = 0) := by
    rw [vecOf_sub_smul_eq_zero_iff hn hn₀ mem_bohrModes_zero]
    rintro ⟨h, _⟩
    exact absurd h (by decide)
  have h1 : (vecOf P n - (1 : ℤ) • vecOf P n₀ = 0) ↔ n = n₀ := by
    rw [vecOf_sub_smul_eq_zero_iff hn hn₀ mem_bohrModes_one]
    simp
  have b1 : bohrCoeff (-ε) 1 = ε := by
    rw [bohrCoeff, if_neg (by decide), neg_neg]
  rw [if_neg hm1, if_neg h0, b1]
  by_cases hnn : n = n₀
  · rw [if_pos (h1.mpr hnn), if_pos hnn]
    ring
  · rw [if_neg (fun h => hnn (h1.mp h)), if_neg hnn]
    ring

/-- **The weighted moment at a smooth twist**: main term plus the envelopes of the modes. -/
theorem exists_norm_weightedMoment_sub_main_le (hP : ∀ p ∈ P, p.Prime) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L δ : ℝ}, 16 ≤ L → 0 < δ → δ ≤ 1 / 4 → ∀ (ε : ℝ) {n n₀ : ℕ},
      IsSmoothOver P n → IsSmoothOver P n₀ →
      ‖weightedMoment L (notchWeight P ε n₀) (Real.log n) -
          ((if n = n₀ then ε * ∏ p : P, (1 - primeHalf p ^ 2) else 0 : ℝ) : ℂ) * logWindow L‖ ≤
        ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
          |modeCoeff ε j c| * twistEnvelope C L δ K (vecOf P n - (j • vecOf P n₀ + c)) := by
  classical
  obtain ⟨C, hC, hmain⟩ := exists_norm_twistedMoment_vec_sub_le hP K
  refine ⟨C, hC, fun {L δ} hL hδ hδ4 ε {n n₀} hn hn₀ => ?_⟩
  have hL0 : 0 < L := by linarith
  set b : ℤ → (P → ℤ) → (P → ℤ) := fun j c => vecOf P n - (j • vecOf P n₀ + c) with hb
  set w : (P → ℤ) → ℝ := fun a => ∏ p : P, primeHalf p ^ (a p).natAbs with hw
  have hfreq : ∀ j c, Real.log n - modeFreq n₀ j c = vecFreq (b j c) := by
    intro j c
    rw [hb, vecFreq_sub, vecFreq_vecOf hn.2, modeFreq_eq hn₀.2]
  rw [weightedMoment_notchWeight_eq hL0]
  simp_rw [hfreq]
  have hsum := sum_modeCoeff_mul_weight hn hn₀ ε
  have hmainC : ((if n = n₀ then ε * ∏ p : P, (1 - primeHalf p ^ 2) else 0 : ℝ) : ℂ) *
      logWindow L = ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
        (modeCoeff ε j c : ℂ) * ((w (b j c) : ℂ) * logWindow L) := by
    rw [← hsum]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [hw, hb]
    push_cast
    ring
  rw [hmainC, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hmain hL hδ hδ4 (b j c)) (abs_nonneg _)

end RHTower.ZetaNotch
