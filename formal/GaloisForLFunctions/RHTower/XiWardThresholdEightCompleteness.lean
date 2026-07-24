import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardEulerEdgeCompleteness

/-!
# Threshold-eight corner completeness of the Xi Ward column

Replace the four-unit corner budget of the continued Ward column by an arbitrary budget `c`.
The corner defect at budget `c` on a finite right-half-plane packet is `c` times the Hardy
Cauchy Gram minus the rank-one response term.  Under RH every continued response vanishes, so
the defect is positive semidefinite for every `c ≥ 0`.  Conversely, a strict-right centered Xi
zero `lam = a + I b` with `0 < a < 1/2` carries paired Cauchy self-energy
`E(lam) = 4 (1/a + a/(a² + b²)) > 8`, and the continued responses sampled at the two pair nodes
`lam, conj lam` satisfy the energy floor `E(lam) ≤ 2 (Re r(lam) + Re r(conj lam))`.  Testing
the corner defect of the packet `(lam, conj lam)` against the direction `(2, 2)` then forces
`c ≥ E(lam) > 8`.  Hence for every fixed budget `0 ≤ c < 8` the corner lift law at budget `c`
is exactly RH: the four-unit budget of the continued Ward column can be relaxed to any budget
strictly below eight without losing completeness.
-/

open Complex
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- Corner defect of the continued Ward column at budget `c` on a finite packet: `c` times the
Hardy Cauchy Gram minus the rank-one continued-response term. -/
def continuedXiWardCornerDefect (c : ℝ) {n : ℕ} (node : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    (c : ℂ) * rightHalfPlaneHardyCauchyGram node i j -
      continuedXiAntiCausalWardResponse (node i) *
        star (continuedXiAntiCausalWardResponse (node j))

/-- Corner lift law at budget `c`: the corner defect is positive semidefinite on every finite
right-half-plane packet. -/
def ContinuedXiWardCornerLiftLaw (c : ℝ) : Prop :=
  ∀ {n : ℕ} (node : Fin n → ℂ), (∀ i, 0 < (node i).re) →
    (continuedXiWardCornerDefect c node).PosSemidef

/-- Paired Cauchy self-energy of one strict-right Schwarz pair centered at `lam`. -/
def xiWardPairEnergy (lam : ℂ) : ℝ :=
  4 * (1 / lam.re + lam.re / (lam.re ^ 2 + lam.im ^ 2))

/-- Any point of the open strip `0 < Re lam < 1/2` has paired Cauchy self-energy strictly
larger than eight. -/
theorem eight_lt_xiWardPairEnergy {lam : ℂ}
    (ha : 0 < lam.re) (hhalf : lam.re < 1 / 2) :
    8 < xiWardPairEnergy lam := by
  have hN : 0 < lam.re ^ 2 + lam.im ^ 2 := by
    nlinarith [pow_pos ha 2, sq_nonneg lam.im]
  have h1 : 2 < 1 / lam.re := by
    rw [lt_div_iff₀ ha]
    linarith
  have h2 : 0 < lam.re / (lam.re ^ 2 + lam.im ^ 2) := div_pos ha hN
  rw [xiWardPairEnergy]
  linarith

/-- The paired Cauchy self-energy of every strict-right centered Xi zero exceeds eight. -/
theorem eight_lt_xiWardPairEnergy_xiRightCenteredZero (q : XiRightZeroCopy) :
    8 < xiWardPairEnergy (xiRightCenteredZero q) :=
  eight_lt_xiWardPairEnergy (xiRightCenteredZero_re_pos q)
    ((abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)).2)

/-- Real part of the reflected-node Cauchy kernel `(lam + conj lam)⁻¹`. -/
theorem re_inv_self_add_conj (lam : ℂ) :
    ((lam + (starRingEnd ℂ) lam)⁻¹).re = (2 * lam.re)⁻¹ := by
  rw [Complex.add_conj, ← Complex.ofReal_inv, Complex.ofReal_re]

/-- Real part of the reflected-node Cauchy kernel `(conj lam + lam)⁻¹`. -/
theorem re_inv_conj_add_self (lam : ℂ) :
    (((starRingEnd ℂ) lam + lam)⁻¹).re = (2 * lam.re)⁻¹ := by
  rw [add_comm, re_inv_self_add_conj]

/-- Real part of the doubled-node Cauchy kernel `(lam + lam)⁻¹`. -/
theorem re_inv_self_add_self (lam : ℂ) :
    ((lam + lam)⁻¹).re =
      2 * lam.re / (2 * lam.re * (2 * lam.re) + 2 * lam.im * (2 * lam.im)) := by
  have h2 : lam + lam = 2 * lam := by ring
  have hre : (2 * lam).re = 2 * lam.re := by norm_num [Complex.mul_re]
  have him : (2 * lam).im = 2 * lam.im := by norm_num [Complex.mul_im]
  rw [h2, Complex.inv_re, Complex.normSq_apply, hre, him]

/-- Real part of the doubled conjugate-node Cauchy kernel `(conj lam + conj lam)⁻¹`. -/
theorem re_inv_conj_add_conj (lam : ℂ) :
    (((starRingEnd ℂ) lam + (starRingEnd ℂ) lam)⁻¹).re =
      2 * lam.re / (2 * lam.re * (2 * lam.re) + 2 * lam.im * (2 * lam.im)) := by
  have h2 : (starRingEnd ℂ) lam + (starRingEnd ℂ) lam =
      2 * (starRingEnd ℂ) lam := by ring
  have hre : (2 * (starRingEnd ℂ) lam).re = 2 * lam.re := by
    norm_num [Complex.mul_re]
  have him : (2 * (starRingEnd ℂ) lam).im = -(2 * lam.im) := by
    norm_num [Complex.mul_im]
  rw [h2, Complex.inv_re, Complex.normSq_apply, hre, him]
  ring_nf

/-- Self-spend identity: the raw Schwarz-pair kernel of the pair centered at `lam`, sampled at
its own two nodes, spends exactly half the paired Cauchy self-energy in real part. -/
theorem re_two_mul_inv_pair_self_add_conj {lam : ℂ} (ha : 0 < lam.re) :
    (2 * ((lam + lam)⁻¹ + (lam + (starRingEnd ℂ) lam)⁻¹)).re +
      (2 * (((starRingEnd ℂ) lam + lam)⁻¹ +
        ((starRingEnd ℂ) lam + (starRingEnd ℂ) lam)⁻¹)).re =
      xiWardPairEnergy lam / 2 := by
  have hane : lam.re ≠ 0 := ne_of_gt ha
  have hD : 0 < 2 * lam.re * (2 * lam.re) + 2 * lam.im * (2 * lam.im) := by
    nlinarith [mul_pos ha ha, mul_self_nonneg lam.im]
  have hN : 0 < lam.re ^ 2 + lam.im ^ 2 := by
    nlinarith [pow_pos ha 2, sq_nonneg lam.im]
  have h2re : ∀ z : ℂ, ((2 : ℂ) * z).re = 2 * z.re := fun z => by
    norm_num [Complex.mul_re]
  rw [h2re, h2re, Complex.add_re, Complex.add_re, re_inv_self_add_self,
    re_inv_self_add_conj, re_inv_conj_add_self, re_inv_conj_add_conj,
    xiWardPairEnergy]
  field_simp
  ring

/-- Self-spend identity for one strict-right Xi Schwarz pair: its own raw pair response sampled
at the two pair nodes has total real part exactly half the paired Cauchy self-energy. -/
theorem re_xiAntiCausalWardSchwarzPairResponse_self_add_conj
    (q : XiRightUpperZeroCopy) :
    (xiAntiCausalWardSchwarzPairResponse q (xiRightCenteredZero q.1)).re +
      (xiAntiCausalWardSchwarzPairResponse q
        ((starRingEnd ℂ) (xiRightCenteredZero q.1))).re =
      xiWardPairEnergy (xiRightCenteredZero q.1) / 2 := by
  rw [xiAntiCausalWardSchwarzPairResponse, xiAntiCausalWardSchwarzPairResponse,
    xiRightCenteredZero_conj q.1]
  exact re_two_mul_inv_pair_self_add_conj (xiRightCenteredZero_re_pos q.1)

/-- Cross-nonnegativity: every raw Schwarz-pair response contributes nonnegative total real
part at any conjugate pair of right-half-plane nodes. -/
theorem re_xiAntiCausalWardSchwarzPairResponse_conjPair_nonneg
    (p : XiRightUpperZeroCopy) {lam : ℂ} (ha : 0 < lam.re) :
    0 ≤ (xiAntiCausalWardSchwarzPairResponse p lam).re +
      (xiAntiCausalWardSchwarzPairResponse p ((starRingEnd ℂ) lam)).re := by
  have h1 := re_xiAntiCausalWardSchwarzPairResponse_pos p ha
  have h2 := re_xiAntiCausalWardSchwarzPairResponse_pos p
    (w := (starRingEnd ℂ) lam) (by simpa using ha)
  linarith

/-- Energy floor: the continued Ward response sampled at the two nodes of a strict-right Xi
Schwarz pair spends at least half the paired Cauchy self-energy per unit of the two-node
average, i.e. `E(lam) ≤ 2 (Re r(lam) + Re r(conj lam))`. -/
theorem xiWardPairEnergy_le_two_mul_re_continuedResponses
    (q : XiRightUpperZeroCopy) :
    xiWardPairEnergy (xiRightCenteredZero q.1) ≤
      2 * ((continuedXiAntiCausalWardResponse (xiRightCenteredZero q.1)).re +
        (continuedXiAntiCausalWardResponse
          ((starRingEnd ℂ) (xiRightCenteredZero q.1))).re) := by
  have ha : 0 < (xiRightCenteredZero q.1).re := xiRightCenteredZero_re_pos q.1
  have ha' : 0 < ((starRingEnd ℂ) (xiRightCenteredZero q.1)).re := by simpa using ha
  have hsum1 := summable_xiAntiCausalWardSchwarzPairResponse ha
  have hsum2 := summable_xiAntiCausalWardSchwarzPairResponse ha'
  have hreal1 : Summable (fun p : XiRightUpperZeroCopy =>
      (xiAntiCausalWardSchwarzPairResponse p (xiRightCenteredZero q.1)).re) := by
    simpa only [Complex.reCLM_apply] using hsum1.mapL Complex.reCLM
  have hreal2 : Summable (fun p : XiRightUpperZeroCopy =>
      (xiAntiCausalWardSchwarzPairResponse p
        ((starRingEnd ℂ) (xiRightCenteredZero q.1))).re) := by
    simpa only [Complex.reCLM_apply] using hsum2.mapL Complex.reCLM
  have hpair := (hreal1.add hreal2).sum_le_tsum
    ({q} : Finset XiRightUpperZeroCopy)
    (fun p _ => re_xiAntiCausalWardSchwarzPairResponse_conjPair_nonneg p ha)
  simp only [Finset.sum_singleton] at hpair
  rw [re_xiAntiCausalWardSchwarzPairResponse_self_add_conj q,
    hreal1.tsum_add hreal2] at hpair
  rw [continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs ha,
    continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs ha',
    Complex.re_tsum hsum1, Complex.re_tsum hsum2]
  linarith

/-- Budget violation core: if `lam` lies in the open strip `0 < Re lam < 1/2`, the energy
floor holds for a response pair `(r1, r2)`, and the `(2,2)`-direction quadratic form of the
budget-`c` corner defect on the packet `(lam, conj lam)` is nonnegative, then `c ≥ E(lam) > 8`;
so any budget `c < 8` is contradictory. -/
theorem xiWardCornerBudget_violation_core {c : ℝ} {lam r1 r2 : ℂ}
    (ha : 0 < lam.re) (hhalf : lam.re < 1 / 2) (hc : c < 8)
    (hfloor : xiWardPairEnergy lam ≤ 2 * (r1.re + r2.re))
    (hQ : (0 : ℝ) ≤ ((4 : ℂ) * ((c : ℂ) *
        ((lam + (starRingEnd ℂ) lam)⁻¹ + (lam + lam)⁻¹ +
          ((starRingEnd ℂ) lam + (starRingEnd ℂ) lam)⁻¹ +
          ((starRingEnd ℂ) lam + lam)⁻¹) -
        (r1 + r2) * ((starRingEnd ℂ) r1 + (starRingEnd ℂ) r2))).re) :
    False := by
  have hane : lam.re ≠ 0 := ne_of_gt ha
  have hD : 0 < 2 * lam.re * (2 * lam.re) + 2 * lam.im * (2 * lam.im) := by
    nlinarith [mul_pos ha ha, mul_self_nonneg lam.im]
  have hN : 0 < lam.re ^ 2 + lam.im ^ 2 := by
    nlinarith [pow_pos ha 2, sq_nonneg lam.im]
  have h4re : ∀ z : ℂ, ((4 : ℂ) * z).re = 4 * z.re := fun z => by
    norm_num [Complex.mul_re]
  rw [h4re, Complex.sub_re, Complex.re_ofReal_mul, Complex.add_re, Complex.add_re,
    Complex.add_re, re_inv_self_add_conj, re_inv_self_add_self,
    re_inv_conj_add_conj, re_inv_conj_add_self, ← map_add, Complex.mul_conj,
    Complex.ofReal_re] at hQ
  have hgsum : (2 * lam.re)⁻¹ +
      2 * lam.re / (2 * lam.re * (2 * lam.re) + 2 * lam.im * (2 * lam.im)) +
      2 * lam.re / (2 * lam.re * (2 * lam.re) + 2 * lam.im * (2 * lam.im)) +
      (2 * lam.re)⁻¹ = xiWardPairEnergy lam / 4 := by
    rw [xiWardPairEnergy]
    field_simp
    ring
  rw [hgsum] at hQ
  have hE := eight_lt_xiWardPairEnergy ha hhalf
  have hsq : (r1 + r2).re * (r1 + r2).re ≤ Complex.normSq (r1 + r2) :=
    Complex.re_sq_le_normSq (r1 + r2)
  rw [Complex.add_re] at hsq
  nlinarith [mul_self_le_mul_self
      (by linarith : (0 : ℝ) ≤ xiWardPairEnergy lam / 2)
      (by linarith : xiWardPairEnergy lam / 2 ≤ r1.re + r2.re),
    mul_lt_mul_of_pos_right hc (by linarith : (0 : ℝ) < xiWardPairEnergy lam),
    mul_lt_mul_of_pos_right hE (by linarith : (0 : ℝ) < xiWardPairEnergy lam)]

/-- A strict-right Xi Schwarz pair defeats every corner budget `c < 8`: the corner defect on
the two-node packet `(lam, conj lam)` fails positive semidefiniteness in the `(2,2)`
direction. -/
theorem continuedXiWardCornerDefect_conjPair_not_posSemidef
    (q : XiRightUpperZeroCopy) {c : ℝ} (hc : c < 8) :
    ¬ (continuedXiWardCornerDefect c
        ![xiRightCenteredZero q.1,
          (starRingEnd ℂ) (xiRightCenteredZero q.1)]).PosSemidef := by
  intro h
  have hquad := h.dotProduct_mulVec_nonneg ![2, 2]
  rw [Complex.le_def] at hquad
  have hQ0 := hquad.1
  rw [Complex.zero_re] at hQ0
  have hexpand : star (![2, 2] : Fin 2 → ℂ) ⬝ᵥ
      (continuedXiWardCornerDefect c
        ![xiRightCenteredZero q.1,
          (starRingEnd ℂ) (xiRightCenteredZero q.1)]).mulVec ![2, 2] =
      (4 : ℂ) * ((c : ℂ) *
        ((xiRightCenteredZero q.1 +
            (starRingEnd ℂ) (xiRightCenteredZero q.1))⁻¹ +
          (xiRightCenteredZero q.1 + xiRightCenteredZero q.1)⁻¹ +
          ((starRingEnd ℂ) (xiRightCenteredZero q.1) +
            (starRingEnd ℂ) (xiRightCenteredZero q.1))⁻¹ +
          ((starRingEnd ℂ) (xiRightCenteredZero q.1) + xiRightCenteredZero q.1)⁻¹) -
        (continuedXiAntiCausalWardResponse (xiRightCenteredZero q.1) +
            continuedXiAntiCausalWardResponse
              ((starRingEnd ℂ) (xiRightCenteredZero q.1))) *
          ((starRingEnd ℂ)
              (continuedXiAntiCausalWardResponse (xiRightCenteredZero q.1)) +
            (starRingEnd ℂ)
              (continuedXiAntiCausalWardResponse
                ((starRingEnd ℂ) (xiRightCenteredZero q.1))))) := by
    simp only [continuedXiWardCornerDefect, rightHalfPlaneHardyCauchyGram, dotProduct,
      Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.star_apply, RCLike.star_def, Complex.conj_conj, map_ofNat, one_div]
    ring
  rw [hexpand] at hQ0
  exact xiWardCornerBudget_violation_core (xiRightCenteredZero_re_pos q.1)
    ((abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q.1)).2) hc
    (xiWardPairEnergy_le_two_mul_re_continuedResponses q) hQ0

/-- Under RH the continued response vanishes and the corner defect at any nonnegative budget is
a nonnegative multiple of the Hardy Cauchy Gram, hence positive semidefinite. -/
theorem continuedXiWardCornerLiftLaw_of_riemannHypothesis
    {c : ℝ} (hc : 0 ≤ c) (hRH : RiemannHypothesis) :
    ContinuedXiWardCornerLiftLaw c := by
  intro n node hnode
  have hr (i : Fin n) : continuedXiAntiCausalWardResponse (node i) = 0 :=
    continuedXiAntiCausalWardResponse_eq_zero_of_riemannHypothesis hRH (hnode i)
  have hdef : continuedXiWardCornerDefect c node =
      (c : ℂ) • rightHalfPlaneHardyCauchyGram node := by
    ext i j
    simp [continuedXiWardCornerDefect, hr]
  rw [hdef]
  exact (rightHalfPlaneHardyCauchyGram_posSemidef hnode).smul (by exact_mod_cast hc)

/-- Any corner budget strictly below eight is complete: the corner lift law at budget `c < 8`
forces RH. -/
theorem riemannHypothesis_of_continuedXiWardCornerLiftLaw
    {c : ℝ} (hc : c < 8) (hlaw : ContinuedXiWardCornerLiftLaw c) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_for_boundaryLift hRH
  have hnode : ∀ i : Fin 2, 0 <
      ((![xiRightCenteredZero q.1,
        (starRingEnd ℂ) (xiRightCenteredZero q.1)] : Fin 2 → ℂ) i).re := by
    intro i
    fin_cases i
    · simpa using xiRightCenteredZero_re_pos q.1
    · simpa using xiRightCenteredZero_re_pos q.1
  exact continuedXiWardCornerDefect_conjPair_not_posSemidef q hc
    (hlaw _ hnode)

/-- **Threshold-eight corner completeness law.**  For every fixed budget `0 ≤ c < 8`, RH is
equivalent to positive semidefiniteness of the budget-`c` corner defect of the continued Ward
column on all finite right-half-plane packets.  The classical four-unit budget is the case
`c = 4`; completeness persists up to (but not including) the paired Cauchy self-energy
threshold eight. -/
theorem riemannHypothesis_iff_continuedXiWardCornerLiftLaw
    {c : ℝ} (hc0 : 0 ≤ c) (hc8 : c < 8) :
    RiemannHypothesis ↔ ContinuedXiWardCornerLiftLaw c :=
  ⟨continuedXiWardCornerLiftLaw_of_riemannHypothesis hc0,
    riemannHypothesis_of_continuedXiWardCornerLiftLaw hc8⟩

end

end RHTower
