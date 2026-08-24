import GaloisForLFunctions.RHTower.ThetaCuspHawkingBackreactionCubicCompletionEndpoint
/-!
# Schwarzschild recoil completion of theta-Hawking cubic response

This endpoint tests a backreaction law coming from black-hole entropy rather than generic KMS,
CCR, group, inverse, or Krein structure.

For Schwarzschild entropy `S_BH(M) = 4*pi*M^2`, the Parikh--Wilczek microcanonical weight of two
emissions with total energy `E+F`, normalized against its two diagonal weights, is exactly

`exp(-4*pi*(E-F)^2)`.

Mass cancels. Repeated recoil steps multiply these factors, giving a genuine Gaussian dephasing
semigroup `exp(-4*pi*depth*(E-F)^2)`. Dressing the source-faithful selectively stimulated theta
kernel by this factor preserves every diagonal, increases every two-shell determinant, and kills
every off-diagonal coherence at large recoil depth. Hence every ordered theta three-shell packet
enters the strict passive chamber after finitely many integer recoil steps.

**[PAPER-PROVED] [LEAN-PROVED] [HAWKING-SPECIFIC]** The entropy identity, semigroup law,
two-shell improvement, diagonal limit, finite-depth strict passivity, and off-critical
raw-negative-to-passive transition are unconditional.

**[FALSIFIED RH PRODUCER]** Passivity imposed only after unrestricted full backreaction cannot prove
RH. A hypothetical off-critical orbit first opens the negative raw stimulated chamber, but the
Schwarzschild recoil channel repairs it at finite depth. The RH-bearing producer must therefore
control the zero-recoil/early-time response, bound physical recoil depth below the chamber-crossing
depth, or derive a different coefficient-faithful backreaction invariant that recoil cannot erase.

**[SPECULATIVE PHYSICAL WELD]** Parikh--Wilczek supplies the entropy-difference emission weight,
not the identification of its normalized two-emission ratio with the theta shell covariance.
That identification, and the calibration of `depth` to actual evaporation history, remain open.
See Parikh--Wilczek, arXiv:hep-th/9907001. Black-hole-induced decoherence provides independent
physical motivation; see Danielson--Satishchandran--Wald, arXiv:2205.06279.
-/

open Set Filter Topology Real

namespace RHTower

noncomputable section

def schwarzschildBekensteinHawkingEntropy (M : ℝ) : ℝ :=
  4 * Real.pi * M ^ 2

def schwarzschildNormalizedTwoEmissionRecoilCoherence
    (M E F : ℝ) : ℝ :=
  Real.exp
    (schwarzschildBekensteinHawkingEntropy (M - E - F) -
      (schwarzschildBekensteinHawkingEntropy (M - 2 * E) +
        schwarzschildBekensteinHawkingEntropy (M - 2 * F)) / 2)

theorem schwarzschildNormalizedTwoEmissionRecoilCoherence_eq
    (M E F : ℝ) :
    schwarzschildNormalizedTwoEmissionRecoilCoherence M E F =
      Real.exp (-4 * Real.pi * (E - F) ^ 2) := by
  unfold schwarzschildNormalizedTwoEmissionRecoilCoherence
    schwarzschildBekensteinHawkingEntropy
  congr 1
  ring

def schwarzschildCumulativeRecoilCoherence
    (depth E F : ℝ) : ℝ :=
  Real.exp (-4 * Real.pi * depth * (E - F) ^ 2)

theorem schwarzschildCumulativeRecoilCoherence_one_eq_normalized
    (M E F : ℝ) :
    schwarzschildCumulativeRecoilCoherence 1 E F =
      schwarzschildNormalizedTwoEmissionRecoilCoherence M E F := by
  rw [schwarzschildNormalizedTwoEmissionRecoilCoherence_eq,
    schwarzschildCumulativeRecoilCoherence]
  congr 1
  ring

@[simp] theorem schwarzschildCumulativeRecoilCoherence_zero
    (E F : ℝ) :
    schwarzschildCumulativeRecoilCoherence 0 E F = 1 := by
  simp [schwarzschildCumulativeRecoilCoherence]

@[simp] theorem schwarzschildCumulativeRecoilCoherence_diag
    (depth E : ℝ) :
    schwarzschildCumulativeRecoilCoherence depth E E = 1 := by
  simp [schwarzschildCumulativeRecoilCoherence]

theorem schwarzschildCumulativeRecoilCoherence_add
    (s t E F : ℝ) :
    schwarzschildCumulativeRecoilCoherence (s + t) E F =
      schwarzschildCumulativeRecoilCoherence s E F *
        schwarzschildCumulativeRecoilCoherence t E F := by
  rw [schwarzschildCumulativeRecoilCoherence,
    schwarzschildCumulativeRecoilCoherence,
    schwarzschildCumulativeRecoilCoherence]
  rw [show -4 * Real.pi * (s + t) * (E - F) ^ 2 =
      -4 * Real.pi * s * (E - F) ^ 2 +
        -4 * Real.pi * t * (E - F) ^ 2 by ring,
    Real.exp_add]

theorem tendsto_schwarzschildCumulativeRecoilCoherence_atTop_zero
    {E F : ℝ} (hEF : E ≠ F) :
    Tendsto (fun depth : ℝ =>
      schwarzschildCumulativeRecoilCoherence depth E F) atTop (𝓝 0) := by
  have hsq : 0 < (E - F) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hEF)
  have hc : 0 < 4 * Real.pi * (E - F) ^ 2 := by positivity
  have hscale : Tendsto
      (fun depth : ℝ => (4 * Real.pi * (E - F) ^ 2) * depth)
      atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc tendsto_id
  have hlimit := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  convert hlimit using 1
  funext depth
  rw [schwarzschildCumulativeRecoilCoherence]
  congr 1
  ring

def schwarzschildRecoilDressedKernel
    (K : ℝ → ℝ → ℝ) (depth x y : ℝ) : ℝ :=
  schwarzschildCumulativeRecoilCoherence depth x y * K x y

@[simp] theorem schwarzschildRecoilDressedKernel_zero
    (K : ℝ → ℝ → ℝ) (x y : ℝ) :
    schwarzschildRecoilDressedKernel K 0 x y = K x y := by
  simp [schwarzschildRecoilDressedKernel]

@[simp] theorem schwarzschildRecoilDressedKernel_diag
    (K : ℝ → ℝ → ℝ) (depth x : ℝ) :
    schwarzschildRecoilDressedKernel K depth x x = K x x := by
  simp [schwarzschildRecoilDressedKernel]

theorem schwarzschildCumulativeRecoilCoherence_le_one
    {depth : ℝ} (hdepth : 0 ≤ depth) (E F : ℝ) :
    schwarzschildCumulativeRecoilCoherence depth E F ≤ 1 := by
  rw [schwarzschildCumulativeRecoilCoherence, Real.exp_le_one_iff]
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hsq : 0 ≤ (E - F) ^ 2 := sq_nonneg _
  have hmul : 0 ≤ 4 * Real.pi * depth * (E - F) ^ 2 := by positivity
  linarith

theorem schwarzschildRecoilDressedKernel_twoPointDet_ge
    (K : ℝ → ℝ → ℝ) {depth : ℝ} (hdepth : 0 ≤ depth) (x y : ℝ) :
    K x x * K y y - K x y ^ 2 ≤
      schwarzschildRecoilDressedKernel K depth x x *
          schwarzschildRecoilDressedKernel K depth y y -
        schwarzschildRecoilDressedKernel K depth x y ^ 2 := by
  let c := schwarzschildCumulativeRecoilCoherence depth x y
  have hc0 : 0 ≤ c := Real.exp_nonneg _
  have hc1 : c ≤ 1 :=
    schwarzschildCumulativeRecoilCoherence_le_one hdepth x y
  have hcSq : c ^ 2 ≤ 1 := by nlinarith [sq_nonneg c]
  have hmul := mul_le_mul_of_nonneg_right hcSq (sq_nonneg (K x y))
  simp only [schwarzschildRecoilDressedKernel_diag]
  change K x x * K y y - K x y ^ 2 ≤
    K x x * K y y - (c * K x y) ^ 2
  nlinarith

theorem tendsto_schwarzschildRecoilDressedKernel_offdiag_atTop_zero
    (K : ℝ → ℝ → ℝ) {x y : ℝ} (hxy : x ≠ y) :
    Tendsto (fun depth : ℝ =>
      schwarzschildRecoilDressedKernel K depth x y) atTop (𝓝 0) := by
  simpa [schwarzschildRecoilDressedKernel] using
    (tendsto_schwarzschildCumulativeRecoilCoherence_atTop_zero hxy).mul_const (K x y)

theorem tendsto_symmetricThreePointDet_schwarzschildRecoilDressedKernel
    (K : ℝ → ℝ → ℝ) {x y z : ℝ}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Tendsto
      (fun depth : ℝ => symmetricThreePointDet
        (schwarzschildRecoilDressedKernel K depth) x y z)
      atTop (𝓝 (K x x * K y y * K z z)) := by
  have hxx : Tendsto (fun _depth : ℝ => K x x) atTop (𝓝 (K x x)) :=
    tendsto_const_nhds
  have hyy : Tendsto (fun _depth : ℝ => K y y) atTop (𝓝 (K y y)) :=
    tendsto_const_nhds
  have hzz : Tendsto (fun _depth : ℝ => K z z) atTop (𝓝 (K z z)) :=
    tendsto_const_nhds
  have hxy' := tendsto_schwarzschildRecoilDressedKernel_offdiag_atTop_zero K hxy
  have hxz' := tendsto_schwarzschildRecoilDressedKernel_offdiag_atTop_zero K hxz
  have hyz' := tendsto_schwarzschildRecoilDressedKernel_offdiag_atTop_zero K hyz
  have htwo : Tendsto (fun _depth : ℝ => (2 : ℝ)) atTop (𝓝 2) :=
    tendsto_const_nhds
  have hdiag := (hxx.mul hyy).mul hzz
  have hcross := ((htwo.mul hxy').mul hxz').mul hyz'
  have hnegYZ := (hxx.mul hyz').mul hyz'
  have hnegXZ := (hyy.mul hxz').mul hxz'
  have hnegXY := (hzz.mul hxy').mul hxy'
  unfold symmetricThreePointDet
  simp only [schwarzschildRecoilDressedKernel_diag]
  have htotal :=
    (((hdiag.add hcross).sub hnegYZ).sub hnegXZ).sub hnegXY
  convert htotal using 1
  · funext depth
    ring
  · norm_num

theorem exists_eventually_schwarzschildRecoilDressedKernel_threePointDet_pos
    (K : ℝ → ℝ → ℝ) {x y z : ℝ}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxx : 0 < K x x) (hyy : 0 < K y y) (hzz : 0 < K z z) :
    ∃ R : ℝ, ∀ depth : ℝ, R ≤ depth →
      0 < symmetricThreePointDet
        (schwarzschildRecoilDressedKernel K depth) x y z := by
  have hprod : 0 < K x x * K y y * K z z := by positivity
  have hlimit :=
    tendsto_symmetricThreePointDet_schwarzschildRecoilDressedKernel
      K hxy hxz hyz
  have hevent : ∀ᶠ depth : ℝ in atTop,
      (K x x * K y y * K z z) / 2 <
        symmetricThreePointDet
          (schwarzschildRecoilDressedKernel K depth) x y z :=
    (tendsto_order.mp hlimit).1 _ (by linarith)
  obtain ⟨R, hR⟩ := eventually_atTop.mp hevent
  refine ⟨R, fun depth hdepth => ?_⟩
  have := hR depth hdepth
  linarith

def thetaCuspHawkingSchwarzschildRecoilKernel
    (q : XiZeroCopy) (rapidity depth x y : ℝ) : ℝ :=
  schwarzschildRecoilDressedKernel
    (thetaCuspHawkingSelectiveModularGainKernel q rapidity) depth x y

@[simp] theorem thetaCuspHawkingSchwarzschildRecoilKernel_zero
    (q : XiZeroCopy) (rapidity x y : ℝ) :
    thetaCuspHawkingSchwarzschildRecoilKernel q rapidity 0 x y =
      thetaCuspHawkingSelectiveModularGainKernel q rapidity x y := by
  simp [thetaCuspHawkingSchwarzschildRecoilKernel]

theorem exists_eventually_thetaCuspHawkingSchwarzschildRecoil_threePointDet_pos
    (q : XiZeroCopy) (rapidity : ℝ) {x y z : ℝ}
    (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    ∃ R : ℝ, ∀ depth : ℝ, R ≤ depth →
      0 < symmetricThreePointDet
        (thetaCuspHawkingSchwarzschildRecoilKernel q rapidity depth) x y z := by
  apply exists_eventually_schwarzschildRecoilDressedKernel_threePointDet_pos
  · exact ne_of_lt hxy
  · exact ne_of_lt (hxy.trans hyz)
  · exact ne_of_lt hyz
  · exact xiSquaredEulerReweightedFullKernel_diag_pos q
      (thetaCuspHawkingModularGain_one_le rapidity) hx
  · exact xiSquaredEulerReweightedFullKernel_diag_pos q
      (thetaCuspHawkingModularGain_one_le rapidity) (hx.trans hxy)
  · exact xiSquaredEulerReweightedFullKernel_diag_pos q
      (thetaCuspHawkingModularGain_one_le rapidity) (hx.trans (hxy.trans hyz))

def ThetaCuspHawkingSchwarzschildRecoilThreeShellStrictlyPassive
    (q : XiZeroCopy) (rapidity depth x y z : ℝ) : Prop :=
  let K := thetaCuspHawkingSchwarzschildRecoilKernel q rapidity depth
  0 < K x x ∧ 0 < K y y ∧ 0 < K z z ∧
    0 < K x x * K y y - K x y ^ 2 ∧
    0 < K x x * K z z - K x z ^ 2 ∧
    0 < K y y * K z z - K y z ^ 2 ∧
    0 < symmetricThreePointDet K x y z

theorem exists_nat_thetaCuspHawkingSchwarzschildRecoil_threeShellStrictlyPassive
    (q : XiZeroCopy) (rapidity : ℝ) {x y z : ℝ}
    (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    ∃ n : ℕ,
      ThetaCuspHawkingSchwarzschildRecoilThreeShellStrictlyPassive
        q rapidity n x y z := by
  let K := thetaCuspHawkingSelectiveModularGainKernel q rapidity
  have hxx : 0 < K x x :=
    xiSquaredEulerReweightedFullKernel_diag_pos q
      (thetaCuspHawkingModularGain_one_le rapidity) hx
  have hyy : 0 < K y y :=
    xiSquaredEulerReweightedFullKernel_diag_pos q
      (thetaCuspHawkingModularGain_one_le rapidity) (hx.trans hxy)
  have hzz : 0 < K z z :=
    xiSquaredEulerReweightedFullKernel_diag_pos q
      (thetaCuspHawkingModularGain_one_le rapidity) (hx.trans (hxy.trans hyz))
  have hxyRaw :=
    thetaCuspHawkingSelectiveModularGainKernel_twoPoint_det_pos
      q rapidity hx hxy
  have hxzRaw :=
    thetaCuspHawkingSelectiveModularGainKernel_twoPoint_det_pos
      q rapidity hx (hxy.trans hyz)
  have hyzRaw :=
    thetaCuspHawkingSelectiveModularGainKernel_twoPoint_det_pos
      q rapidity (hx.trans hxy) hyz
  obtain ⟨R, hR⟩ :=
    exists_eventually_thetaCuspHawkingSchwarzschildRecoil_threePointDet_pos
      q rapidity hx hxy hyz
  obtain ⟨n, hn⟩ := exists_nat_ge R
  refine ⟨n, ?_⟩
  have hdepth : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hxyDressed :=
    schwarzschildRecoilDressedKernel_twoPointDet_ge K hdepth x y
  have hxzDressed :=
    schwarzschildRecoilDressedKernel_twoPointDet_ge K hdepth x z
  have hyzDressed :=
    schwarzschildRecoilDressedKernel_twoPointDet_ge K hdepth y z
  dsimp [ThetaCuspHawkingSchwarzschildRecoilThreeShellStrictlyPassive]
  change
    0 < schwarzschildRecoilDressedKernel K n x x ∧
      0 < schwarzschildRecoilDressedKernel K n y y ∧
      0 < schwarzschildRecoilDressedKernel K n z z ∧
      0 < schwarzschildRecoilDressedKernel K n x x *
          schwarzschildRecoilDressedKernel K n y y -
        schwarzschildRecoilDressedKernel K n x y ^ 2 ∧
      0 < schwarzschildRecoilDressedKernel K n x x *
          schwarzschildRecoilDressedKernel K n z z -
        schwarzschildRecoilDressedKernel K n x z ^ 2 ∧
      0 < schwarzschildRecoilDressedKernel K n y y *
          schwarzschildRecoilDressedKernel K n z z -
        schwarzschildRecoilDressedKernel K n y z ^ 2 ∧
      0 < symmetricThreePointDet
        (schwarzschildRecoilDressedKernel K n) x y z
  exact ⟨by simpa using hxx, by simpa using hyy, by simpa using hzz,
    lt_of_lt_of_le hxyRaw hxyDressed,
    lt_of_lt_of_le hxzRaw hxzDressed,
    lt_of_lt_of_le hyzRaw hyzDressed,
    hR n hn⟩

theorem exists_nat_thetaCuspHawkingSchwarzschildRecoil_exits_negativeCubic
    (q : XiZeroCopy) (rapidity : ℝ) {x y z : ℝ}
    (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (hnegative : symmetricThreePointDet
      (thetaCuspHawkingSelectiveModularGainKernel q rapidity) x y z < 0) :
    ∃ n : ℕ,
      symmetricThreePointDet
          (thetaCuspHawkingSchwarzschildRecoilKernel q rapidity 0) x y z < 0 ∧
        0 < symmetricThreePointDet
          (thetaCuspHawkingSchwarzschildRecoilKernel q rapidity (n : ℝ)) x y z := by
  obtain ⟨R, hR⟩ :=
    exists_eventually_thetaCuspHawkingSchwarzschildRecoil_threePointDet_pos
      q rapidity hx hxy hyz
  obtain ⟨n, hn⟩ := exists_nat_ge R
  refine ⟨n, ?_, hR n hn⟩
  rw [show thetaCuspHawkingSchwarzschildRecoilKernel q rapidity 0 =
      thetaCuspHawkingSelectiveModularGainKernel q rapidity by
    funext u v
    exact thetaCuspHawkingSchwarzschildRecoilKernel_zero q rapidity u v]
  exact hnegative

/-- Every physical ordered theta shell becomes strictly passive after finitely many cumulative
Schwarzschild recoil steps. -/
def ThetaCuspHawkingSchwarzschildRecoilEventuallyStrictlyPassive : Prop :=
  ∀ (q : XiZeroCopy) (rapidity x y z : ℝ),
    0 < x → x < y → y < z →
      ∃ n : ℕ,
        ThetaCuspHawkingSchwarzschildRecoilThreeShellStrictlyPassive
          q rapidity n x y z

theorem thetaCuspHawkingSchwarzschildRecoilEventuallyStrictlyPassive :
    ThetaCuspHawkingSchwarzschildRecoilEventuallyStrictlyPassive := by
  intro q rapidity x y z hx hxy hyz
  exact
    exists_nat_thetaCuspHawkingSchwarzschildRecoil_threeShellStrictlyPassive
      q rapidity hx hxy hyz

/-- An off-critical orbit opens a negative raw stimulated chamber, but the exact cumulative
Schwarzschild recoil channel still reaches the strict passive chamber at finite integer depth. -/
theorem exists_thetaCuspHawking_offCritical_rawNegative_recoilStrictlyPassive
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    ∃ (rapidity : ℝ) (n : ℕ),
      symmetricThreePointDet
          (thetaCuspHawkingSelectiveModularGainKernel q rapidity) x y z < 0 ∧
        ThetaCuspHawkingSchwarzschildRecoilThreeShellStrictlyPassive
          q rapidity n x y z := by
  obtain ⟨R, hR⟩ :=
    exists_eventually_negative_thetaCuspHawkingSelectiveModularGainKernel_threePointDet
      q hoff hx hxy hyz
  have hnegative := hR R le_rfl
  obtain ⟨n, hn⟩ :=
    exists_nat_thetaCuspHawkingSchwarzschildRecoil_threeShellStrictlyPassive
      q R hx hxy hyz
  exact ⟨R, n, hnegative, hn⟩

end

end RHTower
