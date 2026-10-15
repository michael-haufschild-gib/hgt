import GaloisForLFunctions.RHTower.BlindArchimedeanNodeTwoCertificate
import GaloisForLFunctions.RHTower.WeilConeXiDivisibleBlindTest
import GaloisForLFunctions.RHTower.WeilPositivityMajorantRigidity
import GaloisForLFunctions.RHTower.ArchimedeanGenusZeroSum

/-!
# The one-prime certificate on the decay class, and the pole of `Ξ`-divisible blind tests

The node-two certificate `Re P(k) + (γ(0) + 2)‖f‖² − √2 ℓ₂(f) ≤ weilArchRe k` of
`BlindArchimedeanNodeTwoCertificate` holds for compactly supported tests.  Truncating a test `F` of
the exponential decay class (`ExpDecayTest`) and passing to the limit gives
(`pole_add_anomaly_sub_node_two_le_archPoleEnergy`)

`2 Re(F̂(i/2) conj F̂(−i/2)) + (γ(0) + 2) ∫F² − 2 (F ⋆ F̃)(log 2) ≤ archPoleEnergy F`,

and for `F` blind at `2` the last term vanishes (`pole_add_anomaly_le_archPoleEnergy_of_blind_two`).

**Consequence for the null face** (`pole_le_of_xiDivisibleBlindTest`,
`re_g_mul_conj_g_le_of_xiDivisibleBlindTest`).  A `Ξ`-divisible prime-blind test has pole and
archimedean energy `0` (`archPoleEnergy_eq_zero_of_xiDivisibleBlindTest`), so its pole term is at
most `(−γ(0) − 2) ∫F² ≈ 3.37 ∫F²`.  With `F̂ = Ξ g` and `Ξ(±i/2) = ½` this bounds the multiplier
at the pole: `Re(g(i/2) conj g(−i/2)) ≤ 2(−γ(0) − 2) ∫F²`.  The pole-to-mass ratio of every (N1)
witness is bounded by a constant coming from the single prime `2`.
-/

open Complex MeasureTheory Filter Topology Finsupp Zeta23
open scoped ComplexConjugate
open RHTower.WeilSpectral

namespace RHTower.WeilOneSided

noncomputable section

/-- The pole term of the autocorrelation of a continuous compactly supported test. -/
theorem weilPoleTerm_re_eq_two_re {f : ℝ → ℂ} (hfc : Continuous f) (hfs : HasCompactSupport f) :
    (weilPoleTerm (EF.weilTest f f)).re =
      2 * (paperFT f (I / 2) * conj (paperFT f (-I / 2))).re := by
  have hp : weilPoleTerm (EF.weilTest f f) =
      ((2 * (paperFT f (I / 2) * conj (paperFT f (-I / 2))).re : ℝ) : ℂ) := by
    unfold weilPoleTerm
    rw [EF.paperFT_weilTest hfc hfc hfs hfs, EF.paperFT_weilTest hfc hfc hfs hfs]
    have h1 : conj (I / 2) = -I / 2 := by rw [map_div₀, Complex.conj_I, map_ofNat]
    have h2 : conj (-I / 2) = I / 2 := by
      rw [map_div₀, map_neg, Complex.conj_I, map_ofNat, neg_neg]
    rw [h1, h2]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  rw [hp, Complex.ofReal_re]

/-- The mass of a real test is its autocorrelation at `0`. -/
theorem integral_norm_sq_ofReal_eq_crossCorr_zero (F : ℝ → ℝ) :
    ∫ x, ‖((F x : ℝ) : ℂ)‖ ^ 2 = crossCorr F F 0 := by
  unfold crossCorr
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [sub_zero, Complex.norm_real, Real.norm_eq_abs, sq_abs, sq]

/-- The normalized node value of a real test at `2` in terms of its autocorrelation. -/
theorem logValue_ofReal_two (F : ℝ → ℝ) :
    logValue (fun u => ((F u : ℝ) : ℂ)) 2 = 2 * crossCorr F F (Real.log 2) / Real.sqrt 2 := by
  unfold logValue
  rw [weilTest_ofReal_eq, weilTest_ofReal_eq]
  have e1 : (∫ t, F t * F (t - Real.log 2)) = crossCorr F F (Real.log 2) := rfl
  have e2 : (∫ t, F t * F (t - -Real.log 2)) = crossCorr F F (-Real.log 2) := rfl
  simp only [Nat.cast_ofNat, Complex.add_re, Complex.ofReal_re]
  rw [e1, e2, crossCorr_self_neg]
  ring

/-- **The node-two certificate for a truncated decay-class test.** -/
theorem pole_add_anomaly_sub_node_two_le_archPoleEnergy_truncTest {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (L : ℝ) :
    2 * (paperFT (fun u => (truncTest F L u : ℂ)) (I / 2) *
        conj (paperFT (fun u => (truncTest F L u : ℂ)) (-I / 2))).re +
      (EF.gammaBracket 0 + 2) * crossCorr (truncTest F L) (truncTest F L) 0 -
      2 * crossCorr (truncTest F L) (truncTest F L) (Real.log 2) ≤
      archPoleEnergy (truncTest F L) := by
  set f : WeilTestFn := ⟨fun u => (truncTest F L u : ℂ), contDiff_ofReal_truncTest hF L,
    (hasCompactSupport_truncTest F L).comp_left Complex.ofReal_zero⟩ with hf
  have h := node_two_certificate_le_weilArchRe f
  have hfc : Continuous f.1 := f.2.1.continuous
  rw [weilPoleTerm_re_eq_two_re hfc f.2.2] at h
  have hmass : (∫ x, ‖f.1 x‖ ^ 2) = crossCorr (truncTest F L) (truncTest F L) 0 :=
    integral_norm_sq_ofReal_eq_crossCorr_zero (truncTest F L)
  have hℓ : logValue f.1 2 = 2 * crossCorr (truncTest F L) (truncTest F L) (Real.log 2) / Real.sqrt 2 :=
    logValue_ofReal_two (truncTest F L)
  rw [hmass, hℓ, weilArchRe_weilTest_truncTest_eq hF L] at h
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
  have e : Real.sqrt 2 * (2 * crossCorr (truncTest F L) (truncTest F L) (Real.log 2) / Real.sqrt 2) =
      2 * crossCorr (truncTest F L) (truncTest F L) (Real.log 2) := by
    field_simp
  rw [e] at h
  exact h

/-- **The node-two certificate on the decay class.**  For a test `F` of the exponential decay class,
`2 Re(F̂(i/2) conj F̂(−i/2)) + (γ(0) + 2) ∫F² − 2 (F ⋆ F̃)(log 2) ≤ archPoleEnergy F`. -/
theorem pole_add_anomaly_sub_node_two_le_archPoleEnergy {F : ℝ → ℝ} (hF : ExpDecayTest F) :
    2 * (paperFT (fun u => (F u : ℂ)) (I / 2) * conj (paperFT (fun u => (F u : ℂ)) (-I / 2))).re +
      (EF.gammaBracket 0 + 2) * crossCorr F F 0 - 2 * crossCorr F F (Real.log 2) ≤
      archPoleEnergy F := by
  have hp : |((I / 2 : ℂ)).im| ≤ 1 / 2 := by simp
  have hm : |((-I / 2 : ℂ)).im| ≤ 1 / 2 := by simp [abs_div]
  have h1 := tendsto_paperFT_truncTest hF hp
  have h2 := tendsto_paperFT_truncTest hF hm
  have h2c : Tendsto (fun L : ℝ => conj (paperFT (fun u => (truncTest F L u : ℂ)) (-I / 2))) atTop
      (𝓝 (conj (paperFT (fun u => (F u : ℂ)) (-I / 2)))) :=
    (Complex.continuous_conj.tendsto _).comp h2
  have hprod := h1.mul h2c
  have hre : Tendsto (fun L : ℝ => (paperFT (fun u => (truncTest F L u : ℂ)) (I / 2) *
      conj (paperFT (fun u => (truncTest F L u : ℂ)) (-I / 2))).re) atTop
      (𝓝 ((paperFT (fun u => (F u : ℂ)) (I / 2) * conj (paperFT (fun u => (F u : ℂ)) (-I / 2))).re)) :=
    (Complex.continuous_re.tendsto _).comp hprod
  have hmass := tendsto_crossCorr_truncTest hF 0
  have hℓ := tendsto_crossCorr_truncTest hF (Real.log 2)
  have hE := tendsto_archPoleEnergy_truncTest hF
  have hLHS := ((hre.const_mul 2).add (hmass.const_mul (EF.gammaBracket 0 + 2))).sub (hℓ.const_mul 2)
  exact le_of_tendsto_of_tendsto' hLHS hE fun L =>
    pole_add_anomaly_sub_node_two_le_archPoleEnergy_truncTest hF.1 L

/-- **Blind at `2`, in the decay class**: `2 Re(F̂(i/2) conj F̂(−i/2)) + (γ(0) + 2) ∫F² ≤ archPoleEnergy F`. -/
theorem pole_add_anomaly_le_archPoleEnergy_of_blind_two {F : ℝ → ℝ} (hF : ExpDecayTest F)
    (h2 : crossCorr F F (Real.log 2) = 0) :
    2 * (paperFT (fun u => (F u : ℂ)) (I / 2) * conj (paperFT (fun u => (F u : ℂ)) (-I / 2))).re +
      (EF.gammaBracket 0 + 2) * crossCorr F F 0 ≤ archPoleEnergy F := by
  have := pole_add_anomaly_sub_node_two_le_archPoleEnergy hF
  rwa [h2, mul_zero, sub_zero] at this

/-- **The pole of a `Ξ`-divisible blind test is at most `(−γ(0) − 2)` times its mass.** -/
theorem pole_le_of_xiDivisibleBlindTest {F : ℝ → ℝ} (hF : XiDivisibleBlindTest F) :
    2 * (paperFT (fun u => (F u : ℂ)) (I / 2) * conj (paperFT (fun u => (F u : ℂ)) (-I / 2))).re ≤
      (-EF.gammaBracket 0 - 2) * crossCorr F F 0 := by
  have h := pole_add_anomaly_le_archPoleEnergy_of_blind_two hF.1 (hF.2.1 2 le_rfl)
  rw [archPoleEnergy_eq_zero_of_xiDivisibleBlindTest hF] at h
  linarith

/-- **The multiplier of a `Ξ`-divisible blind test at the pole.**  If `F̂ = Ξ g` on the strip, then
`Re(g(i/2) conj g(−i/2)) ≤ 2(−γ(0) − 2) ∫F²`. -/
theorem re_g_mul_conj_g_le_of_xiDivisibleBlindTest {F : ℝ → ℝ} (hF : XiDivisibleBlindTest F)
    {g : ℂ → ℂ} (hg : ∀ z : ℂ, |z.im| ≤ 1 / 2 → paperFT (fun u => (F u : ℂ)) z = RHTower.XiC z * g z) :
    (g (I / 2) * conj (g (-I / 2))).re ≤ 2 * (-EF.gammaBracket 0 - 2) * crossCorr F F 0 := by
  have h := pole_le_of_xiDivisibleBlindTest hF
  have hp : |((I / 2 : ℂ)).im| ≤ 1 / 2 := by simp
  have hm : |((-I / 2 : ℂ)).im| ≤ 1 / 2 := by simp [abs_div]
  rw [hg _ hp, hg _ hm, RHTower.XiC_I_half, RHTower.XiC_neg_I_half] at h
  have e : ((1 / 2 : ℂ) * g (I / 2) * conj ((1 / 2 : ℂ) * g (-I / 2))).re =
      (g (I / 2) * conj (g (-I / 2))).re / 4 := by
    rw [map_mul, show conj (1 / 2 : ℂ) = 1 / 2 by
      rw [map_div₀, map_one, map_ofNat]]
    rw [show (1 / 2 : ℂ) * g (I / 2) * (1 / 2 * conj (g (-I / 2))) =
      (1 / 4 : ℂ) * (g (I / 2) * conj (g (-I / 2))) by ring]
    rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    ring
  rw [e] at h
  linarith

end

end RHTower.WeilOneSided
