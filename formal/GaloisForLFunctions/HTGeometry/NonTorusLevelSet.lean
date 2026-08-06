import GaloisForLFunctions.HTGeometry.GeneralScaleStabilizer
import GaloisForLFunctions.HTGeometry.TorusDerivationConstants

/-!
# The all-jet level set at a non-torus point

A point of the polyannulus whose phase jets all agree with those of the base
point annihilates every active character.

Shrinking the polyannulus so that scaling by the point still lands inside the
original one, the translated observable and the observable itself are
holomorphic on the same smaller polyannulus and have the same Taylor series at
the origin of time.  They therefore agree on the connected time strip, hence
along the whole real orbit, hence on the smaller polyannulus and in particular
on the torus — where the scaling law reads off the annihilation.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-! ### A polyannulus adapted to a scaling -/

/-- Radii small enough that scaling by `w` still lands in the original
polyannulus. -/
def shrinkRadii (ρ : d → ℝ) (w : d → ℂ) : d → ℝ :=
  fun j => (ρ j - |Real.log ‖w j‖|) / 2

omit [Fintype d] [DecidableEq d] in
theorem norm_pos_of_mem_polyannulus {ρ : d → ℝ} {w : d → ℂ}
    (hw : w ∈ polyannulus ρ) (j : d) : 0 < ‖w j‖ :=
  lt_trans (Real.exp_pos _) (hw j).1

omit [Fintype d] [DecidableEq d] in
theorem abs_log_norm_lt {ρ : d → ℝ} {w : d → ℂ} (hw : w ∈ polyannulus ρ)
    (j : d) : |Real.log ‖w j‖| < ρ j := by
  have hpos : 0 < ‖w j‖ := norm_pos_of_mem_polyannulus hw j
  have hupper : Real.log ‖w j‖ < ρ j := by
    have := Real.log_lt_log hpos (hw j).2
    rwa [Real.log_exp] at this
  have hlower : -ρ j < Real.log ‖w j‖ := by
    have := Real.log_lt_log (Real.exp_pos (-(ρ j))) (hw j).1
    rwa [Real.log_exp] at this
  exact abs_lt.2 ⟨hlower, hupper⟩

omit [Fintype d] [DecidableEq d] in
theorem shrinkRadii_pos {ρ : d → ℝ} {w : d → ℂ} (hw : w ∈ polyannulus ρ)
    (j : d) : 0 < shrinkRadii ρ w j := by
  have := abs_log_norm_lt hw j
  rw [shrinkRadii]
  linarith

omit [Fintype d] [DecidableEq d] in
theorem shrinkRadii_le {ρ : d → ℝ} {w : d → ℂ} (hρ : ∀ j, 0 < ρ j) (j : d) :
    shrinkRadii ρ w j ≤ ρ j := by
  have h1 : 0 ≤ |Real.log ‖w j‖| := abs_nonneg _
  have h2 := hρ j
  rw [shrinkRadii]
  linarith

omit [Fintype d] [DecidableEq d] in
theorem polyannulus_shrinkRadii_subset {ρ : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    (w : d → ℂ) : polyannulus (shrinkRadii ρ w) ⊆ polyannulus ρ := by
  intro z hz j
  have hle := shrinkRadii_le (w := w) hρ j
  refine ⟨lt_of_le_of_lt (Real.exp_le_exp.2 (by linarith)) (hz j).1,
    lt_of_lt_of_le (hz j).2 (Real.exp_le_exp.2 hle)⟩

omit [Fintype d] [DecidableEq d] in
theorem torusScale_mem_polyannulus_of_shrink {ρ : d → ℝ} {w : d → ℂ}
    (hw : w ∈ polyannulus ρ) :
    ∀ z ∈ polyannulus (shrinkRadii ρ w), torusScale w z ∈ polyannulus ρ := by
  intro z hz j
  have hpos : 0 < ‖w j‖ := norm_pos_of_mem_polyannulus hw j
  have habs := abs_log_norm_lt hw j
  set L : ℝ := Real.log ‖w j‖ with hL
  have hwexp : ‖w j‖ = Real.exp L := (Real.exp_log hpos).symm
  have hnorm : ‖torusScale w z j‖ = ‖w j‖ * ‖z j‖ := by
    rw [torusScale, norm_mul]
  have hupper : ‖w j‖ * ‖z j‖ < Real.exp (ρ j) := by
    have h1 : ‖z j‖ < Real.exp (shrinkRadii ρ w j) := (hz j).2
    have h2 : ‖w j‖ * ‖z j‖ < Real.exp L * Real.exp (shrinkRadii ρ w j) := by
      rw [hwexp]
      exact mul_lt_mul_of_pos_left h1 (Real.exp_pos L)
    refine lt_of_lt_of_le h2 ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hle : L ≤ |L| := le_abs_self L
    rw [shrinkRadii]
    linarith
  have hlower : Real.exp (-(ρ j)) < ‖w j‖ * ‖z j‖ := by
    have h1 : Real.exp (-(shrinkRadii ρ w j)) < ‖z j‖ := (hz j).1
    have h2 : Real.exp L * Real.exp (-(shrinkRadii ρ w j)) < ‖w j‖ * ‖z j‖ := by
      rw [hwexp]
      exact mul_lt_mul_of_pos_left h1 (Real.exp_pos L)
    refine lt_of_le_of_lt ?_ h2
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hle : -|L| ≤ L := neg_abs_le L
    rw [shrinkRadii]
    linarith
  rw [mem_logAnnulus_iff, hnorm]
  exact ⟨hlower, hupper⟩

/-! ### The level-set statement -/

/-- **A point with the same phase jets as the base point annihilates every
active character.** -/
theorem charPow_eq_one_of_phaseJet_eq {ρ omega : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hindep : RationallyIndependentFrequency omega)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {w : d → ℂ}
    (hw : w ∈ polyannulus ρ)
    (hjets : ∀ k, phaseJet omega F k w
      = phaseJet omega F k (fun _ : d => (1 : ℂ))) :
    ∀ m ∈ activeSupport F, charPow w m = 1 := by
  classical
  set σ : d → ℝ := shrinkRadii ρ w with hσdef
  have hσpos : ∀ j, 0 < σ j := fun j => shrinkRadii_pos hw j
  have hsub : polyannulus σ ⊆ polyannulus ρ := polyannulus_shrinkRadii_subset hρ w
  have hmaps : ∀ z ∈ polyannulus σ, torusScale w z ∈ polyannulus ρ :=
    torusScale_mem_polyannulus_of_shrink hw
  have hFσ : AnalyticOnNhd ℂ F (polyannulus σ) := fun z hz => hF z (hsub hz)
  have hG : AnalyticOnNhd ℂ (fun z => F (torusScale w z)) (polyannulus σ) :=
    analyticOnNhd_comp_torusScale_of_mapsTo hmaps hF
  have h1σ : (fun _ : d => (1 : ℂ)) ∈ polyannulus σ := one_mem_polyannulus hσpos
  have hjets0 : ∀ k,
      iteratedDeriv k (phaseFunction omega (fun z => F (torusScale w z))) 0
        = iteratedDeriv k (phaseFunction omega F) 0 := by
    intro k
    rw [iteratedDeriv_phaseFunction hG k 0 (zero_mem_phaseStrip hσpos),
      iteratedDeriv_phaseFunction hFσ k 0 (zero_mem_phaseStrip hσpos),
      phaseFunction, phaseFunction, phasePoint_zero]
    have hcomp := phaseJet_comp_torusScale_of_mapsTo omega hmaps hF k _ h1σ
    rw [torusScale_one] at hcomp
    exact hcomp.trans (hjets k)
  have hstrip := eqOn_of_iteratedDeriv_eq (isPreconnected_phaseStrip σ omega)
    (analyticOnNhd_phaseFunction (omega := omega) hG)
    (analyticOnNhd_phaseFunction (omega := omega) hFσ)
    (zero_mem_phaseStrip hσpos) hjets0
  have horbit : ∀ t : ℝ,
      F (torusScale w (torusOrbitPoint omega t)) - F (torusOrbitPoint omega t) = 0 := by
    intro t
    have hval := hstrip (ofReal_mem_phaseStrip hσpos t)
    rw [phaseFunction, phaseFunction, phasePoint_ofReal] at hval
    rw [hval, sub_self]
  have hall := eqOn_zero_polyannulus_of_eqOn_zero_orbit hσpos hindep
    (hG.sub hFσ) horbit
  have htorus : ∀ z ∈ unitTorus d, F (torusScale w z) = F z := by
    intro z hz
    have hzσ : z ∈ polyannulus σ := unitTorus_subset_polyannulus hσpos hz
    have hzz : F (torusScale w z) - F z = 0 := hall z hzσ
    linear_combination hzz
  exact charPow_eq_one_of_eqOn_unitTorus hρ hF hw htorus

end

end GaloisForLFunctions.HTGeometry
