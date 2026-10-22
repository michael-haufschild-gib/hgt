import GaloisForLFunctions.SquareRootThreshold.DifferenceLagFamilyPositiveThroughTheFirstPrime
import GaloisForLFunctions.SquareRootThreshold.LagRateBoundsTheDeBruijnNewmanHeatTime
import GaloisForLFunctions.ArithmeticIncidencePositivity.GlobalIncidenceAllocationCondition
import GaloisForLFunctions.SquareRootThreshold.TheShiftedGroundStateInequalitiesReadTheOddWindow

/-!
# The incidence ledger graded by the zero width

`ArithmeticIncidencePositivity` writes the odd zero form exactly as a ledger at every aperture
(`fullZeroForm_eq_incidenceLedger`): costs and pole against pool, crossing potential, gains and
the signed remainder, and RH is the resulting allocation condition at every aperture
(`forall_odd_fullZeroForm_nonneg_iff_globalIncidenceAllocation`).  That condition is a **sign**, so
in the shared units it measures nothing: a partial result on it certifies no aperture, no lag and
no exponent.

Here the ledger is graded.  The difference tests of the lag family are odd and supported in
`[−(v/2+w), v/2+w]`, the lag functional of such a test is the zero form
(`zeta_W_eq_literatureRHS`, `literatureRHS_twoBump_eq_lagPrimeWindowRHS`), and the zero width is
exactly the exponential rate at which the lag family may go negative
(`zetaZeroWidth_le_iff_lag_primeWindow_ge_neg_exp`).  Composing:

* `zetaZeroWidth_le_of_graded_odd_fullZeroForm_floor` — an odd-sector floor
  `Ẑ(F) ≥ −C e^{2σ r} ∫F²` at every aperture `r` gives the zero-free strip `|Re ρ − ½| ≤ σ`;
* `zetaZeroWidth_le_of_gradedIncidenceAllocation` — the same written on the ledger: the allocation
  may **fail**, by `C e^{2σ r} ∫F²` at aperture `r`, and still certify the strip `½ + σ`;
* `riemannHypothesis_of_gradedIncidenceAllocation_zero` — at rate `0` the allocation may fail by an
  absolute constant times the mass at *every* aperture and still give RH.

So the ledger acquires a value in the width unit: an estimate of the allocation deficit at rate
`2σ` is the explicit exponent `Θ ≤ ½ + σ`, and the sign is needed only in the limit.  The exact
positivity of the allocation condition is the endpoint `σ = 0`, `C = 0` of a one-parameter family,
exactly as the partial damping continuation of
`ArithmeticContinuationAndCriticalEnergy` grades the receiver.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open _root_.Zeta23 _root_.RHTower GaloisForLFunctions.ArithmeticCriticalityTheory
  GaloisForLFunctions.ArithmeticIncidencePositivity GaloisForLFunctions.ArithmeticPositivityTheory

/-! ### A graded odd-sector floor is a zero-free strip -/

/-- **A graded odd-sector floor is a zero-free strip.** If every odd `C²` test with compact support
inside `[−r, r]` satisfies `Ẑ(F) ≥ −C e^{2σ r} ∫F²`, then every zero of `ζ` lies in
`|Re ρ − ½| ≤ σ`.  The floor is evaluated on the difference tests of the lag family, whose lag
functional is the zero form and whose aperture is `v/2 + w`, so the aperture rate `2σ` becomes the
lag rate `σ`, which is exactly the zero width. -/
theorem zetaZeroWidth_le_of_graded_odd_fullZeroForm_floor {σ C : ℝ} (hσ : 0 ≤ σ)
    (hfloor : ∀ r : ℝ, 0 < r → ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      -(C * Real.exp (2 * σ * r) * ∫ x, F x ^ 2) ≤ fullZeroForm F) :
    zetaZeroWidth ≤ σ := by
  obtain ⟨E, hE, hlaw⟩ := zetaZeroWidth_le_iff_lag_primeWindow_ge_neg_exp
  obtain ⟨w, ⟨hw, hwlt⟩, hwE⟩ :=
    exists_mem_Ioo_notMem_of_countable (half_pos (Real.log_pos one_lt_two)) hE
  have hw2 : 2 * w < Real.log 2 := by linarith
  refine (hlaw w hw hw2 hwE σ hσ).mpr ?_
  refine ⟨2 * C * Real.exp (2 * σ * w) * ∫ t, ‖modScaledBump w 0 t‖ ^ 2, 2 * w + 1,
    by positivity, fun v hv => ?_⟩
  have hvw : 2 * w < v := by linarith
  have hv0 : 0 ≤ v := by linarith
  have hr : 0 < v / 2 + w := by linarith
  -- the difference test and its regularity
  set f : ℝ → ℂ := twoBump (modScaledBump w 0) v (-1) with hfdef
  have hf : ContDiff ℝ 2 f := contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1]
  have hfc : HasCompactSupport f :=
    hasCompactSupport_twoBump
      (hasCompactSupport_of_support_subset_abs (modScaledBump_support hw 0)) v (-1)
  have hfs : tsupport f ⊆ Icc (-(v / 2 + w)) (v / 2 + w) :=
    tsupport_twoBump_modScaledBump_subset hw hv0
  have hodd : ∀ x, f (-x) = -f x := twoBump_modScaledBump_zero_neg w v
  have hzero : ∀ x, v / 2 + w < |x| → f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have hmem' := hfs hmem
      rw [mem_Icc] at hmem'
      exact absurd (abs_le.mpr hmem') (not_le.mpr hx)
  -- the real and imaginary parts carry the floor
  have hRe : ContDiff ℝ 2 (fun u => (f u).re) := Complex.reCLM.contDiff.comp hf
  have hIm : ContDiff ℝ 2 (fun u => (f u).im) := Complex.imCLM.contDiff.comp hf
  have hRec : HasCompactSupport (fun u => (f u).re) :=
    hfc.comp_left (g := fun z : ℂ => z.re) (by simp)
  have hImc : HasCompactSupport (fun u => (f u).im) :=
    hfc.comp_left (g := fun z : ℂ => z.im) (by simp)
  have h1 := hfloor (v / 2 + w) hr _ hRe hRec (fun x => by simp [hodd x])
    (fun x hx => by simp [hzero x hx])
  have h2 := hfloor (v / 2 + w) hr _ hIm hImc (fun x => by simp [hodd x])
    (fun x hx => by simp [hzero x hx])
  -- the two masses add to the complex mass
  have hint (g : ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g) :
      Integrable (fun x => g x ^ 2) volume := by
    have hs : HasCompactSupport (fun x => g x ^ 2) :=
      HasCompactSupport.of_support_subset_isCompact hgc.isCompact fun x hx =>
        subset_tsupport g (by simpa using hx)
    exact (hg.pow 2).integrable_of_hasCompactSupport hs
  have hsplit : ∫ x, ‖f x‖ ^ 2 = (∫ x, (f x).re ^ 2) + ∫ x, (f x).im ^ 2 := by
    rw [← integral_add (hint _ hRe.continuous hRec) (hint _ hIm.continuous hImc)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  -- assemble into the Weil form and pass to the lag functional
  have hW : -(C * Real.exp (2 * σ * (v / 2 + w)) * ∫ x, ‖f x‖ ^ 2)
      ≤ (zetaZeroConfig.W f f).re := by
    rw [zeta_W_re_eq_fullZeroForm_re_add_im hf hfc, hsplit]
    nlinarith [h1, h2]
  rw [integral_norm_sq_twoBump_modScaledBump_eq hw hvw,
    zeta_W_eq_literatureRHS (f := f) hf hfc,
    literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2 hv0] at hW
  -- the aperture rate `2σ` is the lag rate `σ`
  have hexp : Real.exp (2 * σ * (v / 2 + w)) = Real.exp (σ * v) * Real.exp (2 * σ * w) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hexp] at hW
  have hmass : 0 ≤ ∫ t, ‖modScaledBump w 0 t‖ ^ 2 :=
    integral_nonneg fun t => by positivity
  calc -(2 * C * Real.exp (2 * σ * w) * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) * Real.exp (σ * v))
      = -(C * (Real.exp (σ * v) * Real.exp (2 * σ * w)) *
          (2 * ∫ t, ‖modScaledBump w 0 t‖ ^ 2)) := by ring
    _ ≤ _ := hW

/-- **The pure jump form in the width unit.** On odd tests the zero form is the full zero form
(`fullZeroForm_eq_zeroForm_of_odd`), and in every smeared gauge the zero form is the signed jump
energy plus the variance (`zeroForm_phiDoob_mul_eq_signedJump_add_varianceEnergy`).  So a graded
floor for the conductance form of mechanism 1, at rate `2σ` in the aperture, is the strip
`Θ ≤ ½ + σ`: the prime-side inequality has slack after all, and the slack costs exactly an
exponent. -/
theorem zetaZeroWidth_le_of_graded_odd_zeroForm_floor {σ C : ℝ} (hσ : 0 ≤ σ)
    (hfloor : ∀ r : ℝ, 0 < r → ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      -(C * Real.exp (2 * σ * r) * ∫ x, F x ^ 2) ≤ zeroForm F) :
    zetaZeroWidth ≤ σ := by
  refine zetaZeroWidth_le_of_graded_odd_fullZeroForm_floor (C := C) hσ ?_
  intro r hr F hF hFc hodd hsupp
  rw [fullZeroForm_eq_zeroForm_of_odd hodd]
  exact hfloor r hr F hF hFc hodd hsupp

/-- **Weil positivity up to a constant is Weil positivity.** If the Weil functional of `ζ` is
bounded below by `−C ∫F²` on *all* odd compactly supported `C²` tests, with one constant for every
aperture, then the Riemann Hypothesis holds.  So the exact sign in Weil's criterion is not what has
to be proved: a uniform additive defect is already enough, and the criterion is stable.  (It is the
uniformity in the aperture that carries the statement: `fullZeroForm_ge_of_odd_support_le_*` give
such bounds on bounded apertures and say nothing about the width.) -/
theorem riemannHypothesis_of_odd_fullZeroForm_bddBelow {C : ℝ}
    (hfloor : ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, F (-x) = -F x) →
      -(C * ∫ x, F x ^ 2) ≤ fullZeroForm F) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_zetaZeroWidth_eq_zero]
  refine le_antisymm ?_ zetaZeroWidth_nonneg
  refine zetaZeroWidth_le_of_graded_odd_fullZeroForm_floor (C := C) le_rfl ?_
  intro r hr F hF hFc hodd _
  simpa using hfloor F hF hFc hodd

/-- **A subexponential defect in the aperture is Weil positivity.** If for *every* rate `σ > 0`
some constant bounds the odd Weil functional below by `−C_σ e^{2σ r} ∫F²` at aperture `r`, then RH
holds.  Every polynomial or logarithmic defect in the aperture is of this form, so the sign in
Weil's criterion may be replaced by any estimate that loses less than an exponential in the
aperture: a positivity problem becomes an estimation problem. -/
theorem riemannHypothesis_of_subexponential_odd_floor
    (hfloor : ∀ σ : ℝ, 0 < σ → ∃ C : ℝ, ∀ r : ℝ, 0 < r → ∀ F : ℝ → ℝ, ContDiff ℝ 2 F →
      HasCompactSupport F → (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      -(C * Real.exp (2 * σ * r) * ∫ x, F x ^ 2) ≤ fullZeroForm F) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_zetaZeroWidth_eq_zero]
  refine le_antisymm ?_ zetaZeroWidth_nonneg
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨C, hC⟩ := hfloor ε hε
  simpa using zetaZeroWidth_le_of_graded_odd_fullZeroForm_floor (C := C) hε.le hC

/-- **A sub-trivial floor is a fixed zero-free strip.** The trivial floor at aperture `r` is
`−C r e^{r}`, the `ℓ¹` norm `Σ_{n ≤ e^{2r}} Λ(n) n^{−1/2} ≍ 2e^{r}` of the prime side
(`RHTower.aperturePrimeSum_le_four_mul_mul_exp`): rate exactly `1`, giving the trivial width `½`.
Any **power saving** in that rate, at every aperture, is a fixed zero-free strip
`Θ ≤ 1 − (1 − θ)/2`, uniformly in the height — which no zero-free region of de la Vallée Poussin
or Vinogradov–Korobov type provides. -/
theorem zetaZeroWidth_le_half_mul_of_subTrivial_odd_floor {θ C : ℝ} (hθ : 0 ≤ θ)
    (hfloor : ∀ r : ℝ, 0 < r → ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      -(C * Real.exp (θ * r) * ∫ x, F x ^ 2) ≤ fullZeroForm F) :
    zetaZeroWidth ≤ θ / 2 := by
  refine zetaZeroWidth_le_of_graded_odd_fullZeroForm_floor (C := C) (by linarith) ?_
  intro r hr F hF hFc hodd hsupp
  have hrate : 2 * (θ / 2) * r = θ * r := by ring
  rw [hrate]
  exact hfloor r hr F hF hFc hodd hsupp

/-! ### The ledger, graded -/

/-- **The graded global incidence allocation condition at rate `2σ`.** The costs and the pole may
exceed the pool, the crossing potential, the gains and the remainder, by at most
`C e^{2σ r} ∫F²` at aperture `r`.  At `σ = 0`, `C = 0` this is
`ArithmeticIncidencePositivity.GlobalIncidenceAllocation`. -/
def GradedIncidenceAllocation (σ C : ℝ) : Prop :=
  ∀ (r R : ℝ) (F : ℝ → ℝ), 0 < r → r < R → ContDiff ℝ 2 F → HasCompactSupport F →
    (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
    (∑ n ∈ relevantShifts r, oddStripCost F r n) + poleCharge F ≤
      surplusPool (aperturePlateau r R) F + crossingPotentialTerm (aperturePlateau r R) F +
        (∑ n ∈ relevantShifts r, evenStripGain F r n) +
        gaugeRemainder (aperturePlateau r R) F +
        C * Real.exp (2 * σ * r) * ∫ x, F x ^ 2

/-- **The incidence ledger in the width unit.** A graded allocation at rate `2σ` gives the
zero-free strip `|Re ρ − ½| ≤ σ`: an estimate of the allocation deficit is an explicit exponent,
and the sign of the ledger is needed only at the endpoint. -/
theorem zetaZeroWidth_le_of_gradedIncidenceAllocation {σ C : ℝ} (hσ : 0 ≤ σ)
    (h : GradedIncidenceAllocation σ C) : zetaZeroWidth ≤ σ := by
  refine zetaZeroWidth_le_of_graded_odd_fullZeroForm_floor (C := C) hσ ?_
  intro r hr F hF hFc hodd hsupp
  rw [fullZeroForm_eq_incidenceLedger hF hFc hodd hr hsupp (lt_add_one r)]
  have hal := h r (r + 1) F hr (lt_add_one r) hF hFc hodd hsupp
  linarith

/-- **At rate zero the allocation may fail by a constant and still give RH.** -/
theorem riemannHypothesis_of_gradedIncidenceAllocation_zero {C : ℝ}
    (h : GradedIncidenceAllocation 0 C) : RiemannHypothesis := by
  rw [riemannHypothesis_iff_zetaZeroWidth_eq_zero]
  exact le_antisymm (zetaZeroWidth_le_of_gradedIncidenceAllocation le_rfl h)
    zetaZeroWidth_nonneg

end GaloisForLFunctions.SquareRootThreshold

end
