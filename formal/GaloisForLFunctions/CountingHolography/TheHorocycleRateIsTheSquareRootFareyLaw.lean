import GaloisForLFunctions.CountingHolography.TheFareyReadingOfTheHorocycle
import GaloisForLFunctions.BlackHoleRingdown.TheHorocycleRateIsTheZeroFreeRegion

/-!
# The horocycle rate is the square-root Farey law

For a smooth source `φ` supported above depth `1`, the mean of its pseudo-Eisenstein series along the
closed horocycle of height `y ≤ 1` is the **Farey count**
(`horocycleMean_eq_fareyCount`)

  `𝔉_φ(y) = 2 Σ_{c ≥ 1} φ(c) K_φ(y, c)`,

a totient-weighted count of cusp images. Rescaling the kernel (`fareyKernel_eq_weight`) shows that it
depends on `c` only through `c/C` with `C = y^{-1/2}`, the largest denominator the horocycle can see:

  `𝔉_φ(y) = (2/C²) Σ_c φ(c) w_φ(c/C)`,  `w_φ(r) = ∫ φ(1/(r²(1 + u²))) du`

(`fareyCount_eq_order`). So the horocycle at height `y` reads the smoothed count of the Farey points of
order `C`, normalized by its area `C²`.

**The three rates as counts.**

* Unconditionally the count reaches its limit at relative rate `C^{-1+2ε}`, i.e. `y^{1/2-ε}`
  (`fareyCount_rate`).
* Rate `y^α` for every source forces every zero into `Re ρ ≤ 2 - 2α` (`re_le_of_fareyCount_rate`):
  thermalization faster than `y^{1/2}` by any power is a zero-free strip.
* **RH holds iff every smoothed Farey count of order `C` has square-root error**
  (`riemannHypothesis_iff_squareRootFareyLaw`):

    `Σ_c φ(c) w_φ(c/C) = m_φ C² + O(C^{1/2+ε})`.

  This is Zagier's rate `y^{3/4-ε}` read as a count: `3/4 = (2 - 1/2)/2` is the area exponent of the
  count minus its square-root fluctuation, per unit of `log C = -½ log y`. Equivalently
  `3/4 = 1/2 + 1/4`: the horocycle exponent `1 - Re ρ/2` of a zero is `1/2` plus its ringdown damping
  rate `(1 - Re ρ)/2`, so the two RH rates read the same poles `ρ/2`.
-/

open MeasureTheory Set Finset Filter Topology
open scoped ContDiff

noncomputable section

namespace GaloisForLFunctions.CountingHolography

open BlackHoleRingdown

/-! ### The Farey count of a source -/

/-- **The Farey count** of a source at height `y`: the totient-weighted sum of the Farey kernels. -/
def fareyCount (ψ : ℝ → ℂ) (y : ℝ) : ℂ := 2 * ∑' c : ℕ, (c.totient : ℂ) * fareyKernel ψ y c

/-- **The Farey weight** of a source: the profile along the horoball of a cusp image of relative
denominator `r = c/C`. -/
def fareyWeight (ψ : ℝ → ℂ) (r : ℝ) : ℂ := ∫ u : ℝ, ψ (1 / (r ^ 2 * (1 + u ^ 2)))

/-- **The kernel depends on `c² y` only.** -/
theorem fareyKernel_eq_weight (ψ : ℝ → ℂ) {y : ℝ} (hy : 0 < y) (c : ℕ) :
    fareyKernel ψ y c = (y : ℂ) * fareyWeight ψ (c * Real.sqrt y) := by
  have h := Measure.integral_comp_mul_left (fun v => ψ (y / ((c : ℝ) ^ 2 * (v ^ 2 + y ^ 2)))) y
  have hs : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
  have e : (fun u : ℝ => ψ (y / ((c : ℝ) ^ 2 * ((y * u) ^ 2 + y ^ 2)))) =
      fun u => ψ (1 / (((c : ℝ) * Real.sqrt y) ^ 2 * (1 + u ^ 2))) := by
    funext u
    congr 1
    rw [show ((c : ℝ) * Real.sqrt y) ^ 2 = (c : ℝ) ^ 2 * y by rw [mul_pow, hs]]
    rcases eq_or_ne (c : ℝ) 0 with hc | hc
    · simp [hc]
    · field_simp
      ring
  simp only [e] at h
  rw [fareyKernel, fareyWeight, h, abs_inv, abs_of_pos hy, Complex.real_smul, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast hy.ne'), one_mul]

/-- **The Farey count of order `C`.** At height `y = C⁻²` the Farey count is the totient-weighted sum of
the weights at `c/C`, normalized by the area `C²`. -/
theorem fareyCount_eq_order (ψ : ℝ → ℂ) {C : ℝ} (hC : 0 < C) :
    fareyCount ψ (C ^ 2)⁻¹ = 2 / (C : ℂ) ^ 2 * ∑' c : ℕ, (c.totient : ℂ) * fareyWeight ψ (c / C) := by
  have hy : 0 < (C ^ 2)⁻¹ := by positivity
  have hsq : Real.sqrt (C ^ 2)⁻¹ = C⁻¹ := by
    rw [Real.sqrt_inv, Real.sqrt_sq hC.le]
  unfold fareyCount
  simp_rw [fareyKernel_eq_weight ψ hy, hsq, ← div_eq_mul_inv]
  rw [show (fun c : ℕ => (c.totient : ℂ) * ((((C ^ 2)⁻¹ : ℝ) : ℂ) * fareyWeight ψ (c / C))) =
      fun c : ℕ => ((((C ^ 2)⁻¹ : ℝ) : ℂ)) * ((c.totient : ℂ) * fareyWeight ψ (c / C)) by
    funext c; ring, tsum_mul_left]
  push_cast
  ring

/-! ### Sources above depth one -/

/-- **The horocycle mean of a source above depth one is its Farey count.** -/
theorem horocycleMean_eq_fareyCount {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioi 1) {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    horocycleMean (pseudoEisenstein fun t => (φ t : ℂ)) y = fareyCount (fun t => (φ t : ℂ)) y := by
  obtain ⟨a, b, ha, hab, hφa, hφb⟩ := exists_band_of_tsupport hc hs
  have ha0 : 0 < a := by linarith
  set ψ : ℝ → ℂ := fun t => (φ t : ℂ)
  have hψc : Continuous ψ := Complex.continuous_ofReal.comp hφ.continuous
  have hψs : HasCompactSupport ψ := hc.comp_left Complex.ofReal_zero
  obtain ⟨M, hM⟩ := hψc.bounded_above_of_compact_support hψs
  have hψa : ∀ t, t < a → ψ t = 0 := fun t ht => by simp [ψ, hφa t ht]
  obtain ⟨C, hC⟩ := exists_nat_gt (1 / (a * y))
  have hay : 0 < a * y := mul_pos ha0 hy
  have hC1 : 1 < ((C : ℝ) + 1) ^ 2 * a * y := by
    have h1 : 1 < (C : ℝ) * (a * y) := by rwa [div_lt_iff₀ hay] at hC
    have h2 : (C : ℝ) ≤ ((C : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith
  rw [horocycleMean_eq_fareySum hψc.measurable hM ha0 hψa hy hC1, hψa y (by linarith), mul_zero,
    zero_add, fareyCount]
  congr 1
  symm
  refine tsum_eq_sum fun c hcn => ?_
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · simp
  · have hCc : C + 1 ≤ c := by
      by_contra h
      exact hcn (Finset.mem_Icc.mpr ⟨hc0, by omega⟩)
    have hCc' : (C : ℝ) + 1 ≤ c := by exact_mod_cast hCc
    have hsq : ((C : ℝ) + 1) ^ 2 ≤ (c : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hCc' 2
    have hbig : 1 < (c : ℝ) ^ 2 * a * y := by
      calc 1 < ((C : ℝ) + 1) ^ 2 * a * y := hC1
        _ ≤ (c : ℝ) ^ 2 * a * y := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right hsq hay.le
    rw [fareyKernel_eq_zero hψa hy hbig, mul_zero]

/-! ### The three rates -/

/-- **The unconditional rate**: the Farey count of order `C` reaches its limit at relative rate
`y^{1/2-ε}`. -/
theorem fareyCount_rate {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioi 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖fareyCount (fun t => (φ t : ℂ)) y - 6 / Real.pi * mellin (fun t => (φ t : ℂ)) (-1)‖ ≤
        C * y ^ (1 / 2 - ε) := by
  obtain ⟨C, hC0, hC⟩ := horocycle_rate hφ hc hs hε hε1
  exact ⟨C, hC0, fun y hy hy1 => by rw [← horocycleMean_eq_fareyCount hφ hc hs hy hy1]; exact hC y hy hy1⟩

/-- Rate statements for the horocycle and for the Farey count are the same statements. -/
theorem horocycle_rate_iff_fareyCount_rate (α : ℝ) :
    (∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioi 1 →
      ∃ c : ℂ, ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖horocycleMean (pseudoEisenstein fun t => (φ t : ℂ)) y - c‖ ≤ C * y ^ α) ↔
    (∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioi 1 →
      ∃ c : ℂ, ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖fareyCount (fun t => (φ t : ℂ)) y - c‖ ≤ C * y ^ α) := by
  refine forall_congr' fun φ => imp_congr_right fun hφ => imp_congr_right fun hc =>
    imp_congr_right fun hs => ?_
  refine exists_congr fun c => exists_congr fun C => forall_congr' fun y => imp_congr_right fun hy =>
    imp_congr_right fun hy1 => ?_
  rw [horocycleMean_eq_fareyCount hφ hc hs hy hy1]

/-- **Fast thermalization is a zero-free strip.** If every Farey count reaches its limit at rate `y^α`,
every zero of `ζ` with `Re ρ > 0` has `Re ρ ≤ 2 - 2α`. -/
theorem re_le_of_fareyCount_rate {α : ℝ}
    (h : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioi 1 →
      ∃ c : ℂ, ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖fareyCount (fun t => (φ t : ℂ)) y - c‖ ≤ C * y ^ α)
    {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hρ0 : 0 < ρ.re) : ρ.re ≤ 2 - 2 * α :=
  re_le_of_horocycle_rate ((horocycle_rate_iff_fareyCount_rate α).mpr h) hρ hρ0

/-- **Zagier's theorem as a count.** RH holds iff every Farey count reaches its limit at rate
`y^{3/4-ε}` for every `ε > 0`. -/
theorem riemannHypothesis_iff_fareyCount_rate :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioi 1 → ∃ c : ℂ, ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖fareyCount (fun t => (φ t : ℂ)) y - c‖ ≤ C * y ^ (3 / 4 - ε) := by
  rw [riemannHypothesis_iff_horocycle_rate]
  exact forall_congr' fun ε => imp_congr_right fun _ => horocycle_rate_iff_fareyCount_rate _

/-- The rate of a Farey count at height `y = C⁻²` is the error of the count of order `C`. -/
theorem fareyCount_rate_iff_order {ψ : ℝ → ℂ} {c : ℂ} {K α : ℝ} :
    (∀ y : ℝ, 0 < y → y ≤ 1 → ‖fareyCount ψ y - c‖ ≤ K * y ^ α) ↔
      ∀ C : ℝ, 1 ≤ C → ‖∑' n : ℕ, (n.totient : ℂ) * fareyWeight ψ (n / C) - c / 2 * (C : ℂ) ^ 2‖ ≤
        K / 2 * C ^ (2 - 2 * α) := by
  constructor
  · intro h C hC
    have hC0 : 0 < C := by linarith
    have hy : 0 < (C ^ 2)⁻¹ := by positivity
    have hy1 : (C ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
    have h1 := h _ hy hy1
    rw [fareyCount_eq_order ψ hC0] at h1
    have hCc : (C : ℂ) ≠ 0 := by exact_mod_cast hC0.ne'
    have e : ∑' n : ℕ, (n.totient : ℂ) * fareyWeight ψ (n / C) - c / 2 * (C : ℂ) ^ 2 =
        ((C : ℂ) ^ 2 / 2) * (2 / (C : ℂ) ^ 2 * ∑' n : ℕ, (n.totient : ℂ) * fareyWeight ψ (n / C) - c) := by
      field_simp
    rw [e, norm_mul]
    have hn : ‖(C : ℂ) ^ 2 / 2‖ = C ^ 2 / 2 := by
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hC0.le]
      norm_num
    rw [hn]
    have hpow : ((C ^ 2)⁻¹ : ℝ) ^ α = C ^ (-(2 * α)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg_one, ← Real.rpow_mul hC0.le, ← Real.rpow_mul hC0.le]
      norm_num
    rw [hpow] at h1
    have hC2 : C ^ (2 - 2 * α) = C ^ 2 * C ^ (-(2 * α)) := by
      rw [sub_eq_add_neg, Real.rpow_add hC0, Real.rpow_two]
    rw [hC2]
    have h2 : 0 ≤ C ^ 2 / 2 := by positivity
    calc C ^ 2 / 2 * ‖2 / (C : ℂ) ^ 2 * ∑' n : ℕ, (n.totient : ℂ) * fareyWeight ψ (n / C) - c‖
        ≤ C ^ 2 / 2 * (K * C ^ (-(2 * α))) := mul_le_mul_of_nonneg_left h1 h2
      _ = K / 2 * (C ^ 2 * C ^ (-(2 * α))) := by ring
  · intro h y hy hy1
    set C := Real.sqrt y⁻¹ with hCdef
    have hC0 : 0 < C := Real.sqrt_pos.mpr (inv_pos.mpr hy)
    have hC1 : 1 ≤ C := by
      rw [hCdef, ← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (one_le_inv₀ hy |>.mpr hy1)
    have hyC : y = (C ^ 2)⁻¹ := by
      rw [hCdef, Real.sq_sqrt (inv_nonneg.mpr hy.le), inv_inv]
    have h1 := h C hC1
    rw [hyC, fareyCount_eq_order ψ hC0]
    have hCc : (C : ℂ) ≠ 0 := by exact_mod_cast hC0.ne'
    have e : 2 / (C : ℂ) ^ 2 * ∑' n : ℕ, (n.totient : ℂ) * fareyWeight ψ (n / C) - c =
        (2 / (C : ℂ) ^ 2) * (∑' n : ℕ, (n.totient : ℂ) * fareyWeight ψ (n / C) - c / 2 * (C : ℂ) ^ 2) := by
      field_simp
    rw [e, norm_mul]
    have hn : ‖2 / (C : ℂ) ^ 2‖ = 2 / C ^ 2 := by
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hC0.le]
      norm_num
    rw [hn]
    have hpow : ((C ^ 2)⁻¹ : ℝ) ^ α = C ^ (-(2 * α)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg_one, ← Real.rpow_mul hC0.le, ← Real.rpow_mul hC0.le]
      norm_num
    rw [hpow]
    have hC2 : C ^ (2 - 2 * α) = C ^ 2 * C ^ (-(2 * α)) := by
      rw [sub_eq_add_neg, Real.rpow_add hC0, Real.rpow_two]
    rw [hC2] at h1
    have h2 : 0 ≤ 2 / C ^ 2 := by positivity
    calc 2 / C ^ 2 * ‖∑' n : ℕ, (n.totient : ℂ) * fareyWeight ψ (n / C) - c / 2 * (C : ℂ) ^ 2‖
        ≤ 2 / C ^ 2 * (K / 2 * (C ^ 2 * C ^ (-(2 * α)))) := mul_le_mul_of_nonneg_left h1 h2
      _ = K * C ^ (-(2 * α)) := by field_simp

/-- **RH is the square-root Farey law.** RH holds iff for every smooth source above depth one and every
`ε > 0`, the totient-weighted count of the Farey points of order `C` with weight `w_φ(c/C)` is
`m C² + O(C^{1/2 + ε})`. -/
theorem riemannHypothesis_iff_squareRootFareyLaw :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioi 1 → ∃ m : ℂ, ∃ K : ℝ, ∀ C : ℝ, 1 ≤ C →
        ‖∑' n : ℕ, (n.totient : ℂ) * fareyWeight (fun t => (φ t : ℂ)) (n / C) - m * (C : ℂ) ^ 2‖ ≤
          K * C ^ (1 / 2 + 2 * ε) := by
  rw [riemannHypothesis_iff_fareyCount_rate]
  refine forall_congr' fun ε => imp_congr_right fun _ => forall_congr' fun φ =>
    imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right fun _ => ?_
  have e : (2 : ℝ) - 2 * (3 / 4 - ε) = 1 / 2 + 2 * ε := by ring
  constructor
  · rintro ⟨c, K, h⟩
    refine ⟨c / 2, K / 2, fun C hC => ?_⟩
    have := (fareyCount_rate_iff_order.mp h) C hC
    rwa [e] at this
  · rintro ⟨m, K, h⟩
    refine ⟨2 * m, 2 * K, fareyCount_rate_iff_order.mpr fun C hC => ?_⟩
    rw [e, show 2 * m / 2 = m by ring, show 2 * K / 2 = K by ring]
    exact h C hC

end GaloisForLFunctions.CountingHolography

end
