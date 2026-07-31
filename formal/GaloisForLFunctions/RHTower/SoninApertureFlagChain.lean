import GaloisForLFunctions.RHTower.SoninApertureExtendedTraceFlagLaw

/-!
# Refining an aperture flag loses exactly the sum of the layer couplings

The three-point flag law says that splitting one aperture step into two loses the coupling energy
between the two lost layers.  Iterating it along a chain inside a single crossing chamber shows
that splitting one step into `m` loses exactly the sum of the `m-1` successive couplings: the loss
accumulates, term by term, with no cancellation and no cross terms.

The scalar bookkeeping is done on the residual traces alone, so no principal-relative presentation
is needed; the logarithmic weights cancel as a coboundary along the chain in any case.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- Ordinary trace of the Schatten-1 shell residual of one aperture step. -/
def soninApertureResidualTrace (u v r : ℝ) (hr : 1 < r) : ℂ :=
  opTrace (evenSoninApertureRestrictionDefect u v r hr -
    evenTwoPolarizationShell (r * u) (r * v))

/-- The three-point flag law, read on the residual traces. -/
theorem soninApertureResidualTrace_split
    {a b c r : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hr : 1 < r) (hcr : c < r * a) :
    soninApertureResidualTrace a c r hr =
      soninApertureResidualTrace a b r hr + soninApertureResidualTrace b c r hr +
        opTrace (evenSoninApertureRestrictionCurvature a b c r hr) :=
  opTrace_soninApertureShellResidual_flag ha hab hbc hr hcr

/-- **Chain flag law.**  Along a strictly increasing chain inside one crossing chamber, the
residual trace of the total step is the sum of the residual traces of the individual steps plus the
curvature traces of the successive refinements. -/
theorem soninApertureResidualTrace_chain {r : ℝ} (hr : 1 < r) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hstep : ∀ i, x i < x (i + 1)) :
    ∀ m : ℕ, 1 ≤ m → x m < r * x 0 →
      soninApertureResidualTrace (x 0) (x m) r hr =
        (∑ i ∈ Finset.range m, soninApertureResidualTrace (x i) (x (i + 1)) r hr) +
          ∑ j ∈ Finset.Ico 1 m,
            opTrace (evenSoninApertureRestrictionCurvature (x 0) (x j) (x (j + 1)) r hr) := by
  have hmono : StrictMono x := strictMono_nat_of_lt_succ hstep
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
      intro _
      simp
  | succ m hm ih =>
      intro hcham
      have hmid : x m < r * x 0 := (hstep m).trans hcham
      have h0m : x 0 < x m := hmono (by omega)
      have hsplit := soninApertureResidualTrace_split (a := x 0) (b := x m)
        (c := x (m + 1)) hx0 h0m (hstep m) hr hcham
      rw [hsplit, ih hmid, Finset.sum_range_succ,
        Finset.sum_Ico_succ_top hm]
      ring

/-- **Quantitative refinement loss.**  The real residual trace of the total step is the sum of the
step values minus the total coupling energy of the refinement. -/
theorem re_soninApertureResidualTrace_chain {r : ℝ} (hr : 1 < r) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hstep : ∀ i, x i < x (i + 1)) (m : ℕ) (hm : 1 ≤ m)
    (hcham : x m < r * x 0) :
    (soninApertureResidualTrace (x 0) (x m) r hr).re =
      (∑ i ∈ Finset.range m, (soninApertureResidualTrace (x i) (x (i + 1)) r hr).re) -
        ∑ j ∈ Finset.Ico 1 m,
          hsNormSq (evenSoninApertureSuccessiveLayerTransition
            (x 0) (x j) (x (j + 1)) r hr) := by
  have hmono : StrictMono x := strictMono_nat_of_lt_succ hstep
  have hchain := soninApertureResidualTrace_chain hr x hx0 hstep m hm hcham
  have hcurv : ∀ j ∈ Finset.Ico 1 m,
      (opTrace (evenSoninApertureRestrictionCurvature (x 0) (x j) (x (j + 1)) r hr)).re =
        -hsNormSq (evenSoninApertureSuccessiveLayerTransition
          (x 0) (x j) (x (j + 1)) r hr) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have h0j : x 0 < x j := hmono (by omega)
    have hjm : x (j + 1) ≤ x m := hmono.le_iff_le.mpr (by omega)
    exact re_opTrace_evenSoninApertureRestrictionCurvature_eq_neg_hsNormSq
      hx0 h0j (hstep j) hr (lt_of_le_of_lt hjm hcham)
  rw [hchain]
  simp only [Complex.add_re, Complex.re_sum]
  rw [Finset.sum_congr rfl hcurv, Finset.sum_neg_distrib]
  ring

/-- **Chain subadditivity.**  Refining an aperture step into a chain can only decrease the real
residual trace, and the total decrease is the accumulated coupling energy of the refinement. -/
theorem re_soninApertureResidualTrace_chain_le {r : ℝ} (hr : 1 < r) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hstep : ∀ i, x i < x (i + 1)) (m : ℕ) (hm : 1 ≤ m)
    (hcham : x m < r * x 0) :
    (soninApertureResidualTrace (x 0) (x m) r hr).re ≤
      ∑ i ∈ Finset.range m, (soninApertureResidualTrace (x i) (x (i + 1)) r hr).re := by
  rw [re_soninApertureResidualTrace_chain hr x hx0 hstep m hm hcham]
  have hnn : (0 : ℝ) ≤ ∑ j ∈ Finset.Ico 1 m,
      hsNormSq (evenSoninApertureSuccessiveLayerTransition
        (x 0) (x j) (x (j + 1)) r hr) :=
    Finset.sum_nonneg fun j _ => hsNormSq_nonneg _
  linarith

end RHTower
