import GaloisForLFunctions.HTGeometry.ZetaGammaFieldHypertranscendence
import GaloisForLFunctions.HTGeometry.GammaFieldPrimeFrequencyExclusion
import GaloisForLFunctions.HTGeometry.DirichletBohrSpectrum

/-!
# Zeta is differentially transcendental over the Gamma field

The prime logarithms are Bohr frequencies of `ζ` on every vertical line to the right of `1`: the
Dirichlet coefficient of the line restriction at `−log n` is `e^{−σ log n} ≠ 0`.  Their `ℚ`-span is
therefore contained in the frequency module of `ζ`, and that span has infinite rational rank.

The finite phase law bounds the rational rank of the frequency module of any solution of a relation
with coefficients in `ℂ(s)⟨Γ⟩`, so `ζ` satisfies no such relation — with the coefficients arbitrary
nonzero elements of the differential field, not merely elements presented by explicit Gamma-jet data.
-/

open Filter Set Topology Function

open scoped Differential

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance zetaFieldDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance zetaFieldIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance zetaFieldDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance zetaFieldComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance zetaFieldRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

/-- Zeta is analytic on every upper half-plane: its only singularity is real. -/
theorem analyticOnNhd_zeta_upperTail : AnalyticOnNhd ℂ riemannZeta (upperTail 0) := by
  refine DifferentiableOn.analyticOnNhd ?_ (isOpen_upperTail 0)
  intro z hz
  have him : (0 : ℝ) < z.im := hz
  have hne : z ≠ 1 := by
    intro h
    rw [h] at him
    simp at him
  exact (differentiableAt_riemannZeta hne).differentiableWithinAt

/-- Zeta as an upper-end analytic germ. -/
def zetaUpperAnalytic : upperEndAnalyticSubring :=
  ⟨(Germ.coeRingHom upperEndFilter riemannZeta),
    ⟨riemannZeta, 0, analyticOnNhd_zeta_upperTail, rfl⟩⟩

@[simp] theorem zetaUpperAnalytic_coe :
    upperEndAnalyticSubring.subtype zetaUpperAnalytic
      = Germ.coeRingHom upperEndFilter riemannZeta := rfl

/-- Zeta is holomorphic on every vertical strip inside the half-plane of absolute convergence. -/
theorem differentiableOn_zeta_verticalStrip {σ R : ℝ} (_hσ : 1 < σ) (hRσ : R ≤ σ - 1) :
    DifferentiableOn ℂ riemannZeta (verticalStrip σ R) := by
  intro z hz
  have habs : |z.re - σ| < R := hz
  have h1 : σ - R < z.re := by
    have := (abs_lt.mp habs).1
    linarith
  have hne : z ≠ 1 := by
    intro h
    rw [h] at h1
    simp at h1
    linarith
  exact (differentiableAt_riemannZeta hne).differentiableWithinAt

/-- Zeta is almost periodic on every vertical strip inside the half-plane of absolute
convergence. -/
theorem isStripAlmostPeriodic_zeta {σ R : ℝ} (hRσ : R ≤ σ - 1) :
    IsStripAlmostPeriodic riemannZeta σ R :=
  isStripAlmostPeriodic_dirichlet (fun _ : ℕ => (1 : ℂ))
    (fun i : ℕ => Real.log ((i : ℝ) + 1)) riemannZeta (zeta_dirichlet_conv hRσ)

/-- **Every Dirichlet frequency of zeta is a Bohr frequency of its line restriction.** -/
theorem neg_log_mem_bohrSpectrum_zeta {σ : ℝ} (hσ : 1 < σ) (m : ℕ) :
    -(Real.log ((m : ℝ) + 1))
      ∈ bohrSpectrum fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) := by
  classical
  have hR : (0 : ℝ) < (σ - 1) / 2 := by linarith
  have hRσ : (σ - 1) / 2 ≤ σ - 1 := by linarith
  have hline : _root_.HTGeometry.IsBohrAlmostPeriodic
      fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) :=
    isBohrAlmostPeriodic_line hR (isStripAlmostPeriodic_zeta hRσ)
  have hcont : Continuous fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) :=
    continuous_zeta_line hσ
  have hm : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, m < n₀ ∧ ∀ t : ℝ,
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
        - ∑ k ∈ Finset.range n₀,
          (1 : ℂ) * Complex.exp (-((Real.log ((k : ℝ) + 1) : ℝ) : ℂ)
            * ((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ ε := by
    intro ε hε
    obtain ⟨M, hM⟩ := zeta_uniform_approx hσ hε
    refine ⟨max M (m + 1), lt_of_lt_of_le (Nat.lt_succ_self m) (le_max_right _ _), fun t => ?_⟩
    exact hM _ (le_max_left _ _) _ (by simp)
  have hcoeff := bohrCoefficient_dirichlet_line (fun _ : ℕ => (1 : ℂ))
    (fun i : ℕ => Real.log ((i : ℝ) + 1)) riemannZeta zetaFrequency_injective hcont hline m hm
  show bohrCoefficient (fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I))
    (-(Real.log ((m : ℝ) + 1))) ≠ 0
  rw [hcoeff, one_mul]
  have hpos : (0 : ℝ) < Real.exp (-(Real.log ((m : ℝ) + 1)) * σ) := Real.exp_pos _
  exact_mod_cast ne_of_gt hpos

/-- **The prime-log span sits inside the frequency module of zeta.** -/
theorem primeLogFullSpan_le_bohrFrequencyModule_zeta {σ : ℝ} (hσ : 1 < σ) :
    primeLogFullSpan
      ≤ bohrFrequencyModule fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) := by
  rw [primeLogFullSpan, bohrFrequencyModule]
  refine Submodule.span_le.mpr ?_
  rintro y ⟨p, rfl⟩
  have hp1 : 1 ≤ (p : ℕ) := (p.2).one_lt.le
  have hcast : (((p : ℕ) - 1 : ℕ) : ℝ) + 1 = ((p : ℕ) : ℝ) := by
    rw [Nat.cast_sub hp1]
    push_cast
    ring
  have hmem := neg_log_mem_bohrSpectrum_zeta hσ ((p : ℕ) - 1)
  have hval : Real.log ((p : ℕ) : ℝ) = -(-(Real.log ((((p : ℕ) - 1 : ℕ) : ℝ) + 1))) := by
    rw [hcast]
    ring
  show Real.log ((p : ℕ) : ℝ) ∈ Submodule.span ℚ _
  rw [hval]
  exact Submodule.neg_mem _ (Submodule.subset_span hmem)

/-- **Zeta is differentially transcendental over the Gamma field.**  On any vertical line to the
right of `1`, zeta satisfies no nontrivial differential relation whose coefficients are nonzero
elements of the differential field generated by `Γ` over `ℂ(s)`. -/
theorem zeta_no_gammaField_field_relation {σ : ℝ} (hσ : 1 < σ) {n N : ℕ} (hN : 0 < N)
    (e : Fin N → Fin (n + 1) → ℕ) (he : Function.Injective e)
    (x : Fin N → upperEndMeroField)
    (hxmem : ∀ α, x α ∈ differentialAdjoin (RatFunc ℂ)
      ({gammaUpperMero} : Set upperEndMeroField))
    (hx0 : ∀ α, x α ≠ 0) :
    ∑ α : Fin N, x α * ∏ i : Fin (n + 1),
        (differentialJet (i : ℕ)
          (algebraMap upperEndAnalyticSubring upperEndMeroField zetaUpperAnalytic)) ^ (e α i)
      ≠ 0 := by
  have hR : (0 : ℝ) < (σ - 1) / 2 := by linarith
  have hRσ : (σ - 1) / 2 ≤ σ - 1 := by linarith
  exact no_gammaField_relation_of_primeLogFullSpan_le (by linarith) hR
    (differentiableOn_zeta_verticalStrip hσ hRσ) (isStripAlmostPeriodic_zeta hRσ)
    (primeLogFullSpan_le_bohrFrequencyModule_zeta hσ) hN e he zetaUpperAnalytic rfl x hxmem hx0

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The negated prime logarithms are rationally independent. -/
theorem linearIndependent_rat_neg_log_primes {K : ℕ} (ps : Fin (K + 1) → Nat.Primes)
    (hps : Function.Injective ps) :
    LinearIndependent ℚ (fun i : Fin (K + 1) => -(Real.log (((ps i : ℕ)) : ℝ))) := by
  have hQ : LinearIndependent ℚ (fun i : Fin (K + 1) => Real.log (((ps i : ℕ)) : ℝ)) :=
    linearIndependent_log_primes.comp ps hps
  have hfun : ((fun _ : Fin (K + 1) => (-1 : ℚˣ)) •
        (fun i : Fin (K + 1) => Real.log (((ps i : ℕ)) : ℝ)))
      = fun i : Fin (K + 1) => -(Real.log (((ps i : ℕ)) : ℝ)) := by
    funext i
    simp [Units.smul_def]
  have h := hQ.units_smul (fun _ : Fin (K + 1) => (-1 : ℚˣ))
  rw [hfun] at h
  exact h

/-- **The Bohr–Fourier expansion of zeta carries arbitrarily many rationally independent
frequencies.**  This is the hypothesis of the spectral exclusion criterion, verified for zeta. -/
theorem zeta_independent_spectrum {σ : ℝ} (hσ : 1 < σ) (K : ℕ) :
    ∃ ν : Fin (K + 1) → ℝ, LinearIndependent ℚ ν ∧
      ∀ i, ν i ∈ bohrSpectrum fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) := by
  classical
  set ps : Fin (K + 1) → Nat.Primes :=
    fun i => ⟨Nat.nth Nat.Prime (i : ℕ), Nat.prime_nth_prime (i : ℕ)⟩ with hps_def
  have hps : Function.Injective ps := by
    intro i j hij
    have h : Nat.nth Nat.Prime (i : ℕ) = Nat.nth Nat.Prime (j : ℕ) := congrArg Subtype.val hij
    exact Fin.ext (nthPrime_injective h)
  refine ⟨fun i => -(Real.log (((ps i : ℕ)) : ℝ)), linearIndependent_rat_neg_log_primes ps hps,
    fun i => ?_⟩
  have hp1 : 1 ≤ (ps i : ℕ) := ((ps i).2).one_lt.le
  have hcast : ((((ps i : ℕ) - 1 : ℕ) : ℝ)) + 1 = (((ps i : ℕ)) : ℝ) := by
    rw [Nat.cast_sub hp1]
    push_cast
    ring
  have hmem := neg_log_mem_bohrSpectrum_zeta hσ ((ps i : ℕ) - 1)
  rwa [hcast] at hmem

end

end GaloisForLFunctions.HTGeometry
