import GaloisForLFunctions.ArithmeticPositiveDuality.AnnihilatorPhaseGeometry
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# The exact dual formula for positive annihilator mass

Continuous real linear phase bounds give all lower bounds on the infimal mass
of exact normalized positive two-prime annihilators. Finite-dimensional
separation identifies the relaxed closed convex constraint. The negative
homothety supplied by one annihilator converts every strict radial contraction
into an actual finite phase combination, so the relaxation loses no mass.
-/

noncomputable section
set_option autoImplicit false
open Set Topology
open scoped NNReal

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

variable {ι : Type*} [Fintype ι]

/-- Every real linear functional bounded above by one on the continuous phase
line takes value at most the budget on the simultaneous antipodal vector. -/
def PhaseMassDualBound (γ : ι → ℝ) (H : ℝ) : Prop :=
  ∀ f : (ι → ℂ) →L[ℝ] ℝ,
    (∀ t : ℝ, f (annihilatorPhaseLine γ t) ≤ 1) →
      f (fun _ : ι => (-1 : ℂ)) ≤ H

private theorem antipodal_smul (H : ℝ) :
    (fun _ : ι => -((1 / H : ℝ) : ℂ)) =
      (1 / H : ℝ) • (fun _ : ι => (-1 : ℂ)) := by
  funext i
  simp only [Pi.smul_apply, Complex.real_smul, mul_neg, mul_one]

variable [Nonempty ι]

/-- A single coordinate phase already certifies the universal unit mass floor. -/
theorem one_le_of_phaseMassDualBound (γ : ι → ℝ) {H : ℝ}
    (hdual : PhaseMassDualBound γ H) : 1 ≤ H := by
  let i : ι := Classical.choice ‹Nonempty ι›
  let f : (ι → ℂ) →L[ℝ] ℝ := -(Complex.reCLM.comp (ContinuousLinearMap.proj i))
  have hb (t : ℝ) : f (annihilatorPhaseLine γ t) ≤ 1 := by
    change -(annihilatorPhaseLine γ t i).re ≤ 1
    simpa only [Complex.neg_re, norm_neg, norm_annihilatorPhaseLine] using
      Complex.re_le_norm (-(annihilatorPhaseLine γ t i))
  have h := hdual f hb
  simpa [f] using h

/-- A zero ordinate makes the normalized phase certificates unbounded. -/
theorem ordinates_ne_zero_of_phaseMassDualBound (γ : ι → ℝ) {H : ℝ}
    (hdual : PhaseMassDualBound γ H) : ∀ i, γ i ≠ 0 := by
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one (one_le_of_phaseMassDualBound γ hdual)
  intro i hi
  let f : (ι → ℂ) →L[ℝ] ℝ :=
    (-(H + 1)) • (Complex.reCLM.comp (ContinuousLinearMap.proj i))
  have hb (t : ℝ) : f (annihilatorPhaseLine γ t) ≤ 1 := by
    change -(H + 1) * (annihilatorPhaseLine γ t i).re ≤ 1
    simp only [annihilatorPhaseLine, hi, Complex.ofReal_zero, mul_zero, zero_mul,
      Complex.exp_zero, Complex.one_re, mul_one]
    linarith only [hH]
  have h := hdual f hb
  have hv : f (fun _ : ι => (-1 : ℂ)) = H + 1 := by simp [f]
  rw [hv] at h
  linarith only [h]

/-- Every actual annihilator obeys every normalized continuous phase bound. -/
theorem phaseMassDualBound_of_annihilator {P : MvPolynomial (Fin 2) ℝ≥0}
    (hc : MvPolynomial.constantCoeff P = 1) (β : ℝ) (γ : ι → ℝ)
    (he : ∀ i, dirichletEval (harmonicPacketPoint β (γ i) 1) P = 0) :
    PhaseMassDualBound γ (dirichletTailMass P β) := by
  intro f hf
  have hH : 0 < dirichletTailMass P β :=
    dirichletTailMass_pos_of_zero hc (he (Classical.choice ‹Nonempty ι›)) β
  have hx := phase_point_mem_convexHull_of_annihilator hc β γ he hH rfl
  have hD : monomialPhaseSet γ ⊆ f ⁻¹' Set.Iic 1 := by
    rintro _ ⟨d, _, rfl⟩
    exact hf (monomialLog d)
  have hb : convexHull ℝ (monomialPhaseSet γ) ⊆ f ⁻¹' Set.Iic 1 :=
    convexHull_min hD ((convex_Iic (1 : ℝ)).linear_preimage f.toLinearMap)
  have h := hb hx
  change f (fun _ : ι => -((1 / dirichletTailMass P β : ℝ) : ℂ)) ≤ 1 at h
  rw [antipodal_smul, map_smul, smul_eq_mul, one_div, mul_comm, ← div_eq_mul_inv] at h
  have hh := (div_le_iff₀ hH).mp h
  simpa only [one_mul] using hh

private theorem phase_closedConvexHull_mem_of_dual (γ : ι → ℝ) {H : ℝ}
    (hdual : PhaseMassDualBound γ H) :
    (fun _ : ι => -((1 / H : ℝ) : ℂ)) ∈ closure (convexHull ℝ (monomialPhaseSet γ)) := by
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one (one_le_of_phaseMassDualBound γ hdual)
  have hγ := ordinates_ne_zero_of_phaseMassDualBound γ hdual
  by_contra hx
  obtain ⟨f, u, hfu, hux⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (monomialPhaseSet γ)).closure isClosed_closure hx
  have hu : 0 < u := by
    simpa only [map_zero] using hfu 0 (subset_closure (zero_mem_phaseConvexHull γ hγ))
  let g : (ι → ℂ) →L[ℝ] ℝ := u⁻¹ • f
  have hgline (t : ℝ) : g (annihilatorPhaseLine γ t) ≤ 1 := by
    have ht := closure_mono (subset_convexHull ℝ (monomialPhaseSet γ))
      (phaseLine_mem_phaseHull γ t)
    have hft := hfu _ ht
    change u⁻¹ * f (annihilatorPhaseLine γ t) ≤ 1
    rw [mul_comm, ← div_eq_mul_inv]
    exact ((div_lt_one hu).mpr hft).le
  have hgx : g (fun _ : ι => -((1 / H : ℝ) : ℂ)) ≤ 1 := by
    rw [antipodal_smul, map_smul, smul_eq_mul, one_div, mul_comm, ← div_eq_mul_inv]
    exact (div_le_iff₀ hH).mpr (by simpa only [one_mul] using hdual g hgline)
  have hgx' : 1 < g (fun _ : ι => -((1 / H : ℝ) : ℂ)) := by
    change 1 < u⁻¹ * f (fun _ : ι => -((1 / H : ℝ) : ℂ))
    rw [mul_comm, ← div_eq_mul_inv]
    exact (lt_div_iff₀ hu).mpr (by simpa only [one_mul] using hux)
  exact (not_lt_of_ge hgx) hgx'

/-- Above any budget certified by all normalized phase bounds, every larger
mass is attained by an exact positive two-prime annihilator. -/
theorem exists_exact_mass_above_phaseDualBound (β : ℝ) (γ : ι → ℝ)
    {H M : ℝ} (hdual : PhaseMassDualBound γ H) (hHM : H < M) :
    ∃ P : MvPolynomial (Fin 2) ℝ≥0, MvPolynomial.constantCoeff P = 1 ∧
      (∀ i, dirichletEval (harmonicPacketPoint β (γ i) 1) P = 0) ∧
      dirichletTailMass P β = M := by
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one (one_le_of_phaseMassDualBound γ hdual)
  have hM : 0 < M := lt_trans hH hHM
  have hγ := ordinates_ne_zero_of_phaseMassDualBound γ hdual
  have hz := phase_closedConvexHull_mem_of_dual γ hdual
  have hr := phaseHull_radial_exactness γ hγ hz (div_pos hH hM).le ((div_lt_one hM).mpr hHM)
  have hscalar : (H / M) * (1 / H) = 1 / M := by
    field_simp [hH.ne', hM.ne']
  have heq : (H / M) • (fun _ : ι => -((1 / H : ℝ) : ℂ)) =
      (fun _ : ι => -((1 / M : ℝ) : ℂ)) := by
    funext i
    change ((H / M : ℝ) : ℂ) * (-((1 / H : ℝ) : ℂ)) = -((1 / M : ℝ) : ℂ)
    rw [mul_neg, ← Complex.ofReal_mul, hscalar]
  rw [heq] at hr
  exact exists_annihilator_of_phaseConvexHull β γ hM hr

/-- Complete dual formula for the infimal mass of exact positive annihilators.
The budget is arbitrary, and a zero ordinate automatically makes both sides false. -/
theorem near_mass_annihilation_iff_phaseDualBound (β : ℝ) (γ : ι → ℝ) (H : ℝ) :
    (∀ ε : ℝ, 0 < ε → ∃ P : MvPolynomial (Fin 2) ℝ≥0,
      MvPolynomial.constantCoeff P = 1 ∧
      (∀ i, dirichletEval (harmonicPacketPoint β (γ i) 1) P = 0) ∧
      dirichletTailMass P β < H + ε) ↔ PhaseMassDualBound γ H := by
  constructor
  · intro hnear f hf
    by_contra! hgt
    obtain ⟨P, hc, he, hm⟩ := hnear ((f (fun _ : ι => (-1 : ℂ)) - H) / 2)
      (by linarith only [hgt])
    have hb := phaseMassDualBound_of_annihilator hc β γ he f hf
    linarith only [hm, hb, hgt]
  · intro hdual ε hε
    obtain ⟨P, hc, he, hm⟩ := exists_exact_mass_above_phaseDualBound β γ hdual
      (show H < H + ε / 2 by linarith only [hε])
    refine ⟨P, hc, he, ?_⟩
    rw [hm]
    linarith only [hε]

#print axioms exists_exact_mass_above_phaseDualBound
#print axioms near_mass_annihilation_iff_phaseDualBound

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator
