import GaloisForLFunctions.HTGeometry.PaperPrimeTransportXi
import GaloisForLFunctions.Bottcher.MeromorphicField
import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Original analytic Xi ideal and conormal under prime transport

Work in the native ring of analytic functions on the classified half-plane,
modulo equality there. The actual multiplier and its analytic inverse form
a unit of this ring. Consequently the original principal Xi ideal is
unchanged, as are all its powers and its full conormal module I/I².
The argument does not replace analytic functions with arbitrary functions
and does not restrict the source to simple zeros.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology
open scoped NNReal

noncomputable section

private def ofAnalytic {U : Set ℂ} (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) :
    Bottcher.analyticSubring U :=
  ⟨Germ.coeRingHom (𝓟 U) f, f, hf, rfl⟩

private def unitOfAnalytic {U : Set ℂ} (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U)
    (hn : ∀ z ∈ U, f z ≠ 0) : (Bottcher.analyticSubring U)ˣ where
  val := ofAnalytic f hf
  inv := ofAnalytic (fun z => (f z)⁻¹) (fun z hz => (hf z hz).inv (hn z hz))
  val_inv := by
    apply Subtype.ext
    change (f : Germ (𝓟 U) ℂ) * ((fun z => (f z)⁻¹) : Germ (𝓟 U) ℂ) = 1
    rw [← Germ.coe_mul, ← Germ.coe_one, Germ.coe_eq]
    exact eventually_principal.mpr (fun z hz => mul_inv_cancel₀ (hn z hz))
  inv_val := by
    apply Subtype.ext
    change ((fun z => (f z)⁻¹) : Germ (𝓟 U) ℂ) * (f : Germ (𝓟 U) ℂ) = 1
    rw [← Germ.coe_mul, ← Germ.coe_one, Germ.coe_eq]
    exact eventually_principal.mpr (fun z hz => inv_mul_cancel₀ (hn z hz))

/-- The genuine native analytic ring on the open right half-plane. -/
abbrev paperPrimeTransportAnalyticRing (σ : ℝ≥0) :=
  Bottcher.analyticSubring {s : ℂ | (σ : ℝ) < s.re}

/-- Original completed Xi as an element of the analytic source ring. -/
def paperPrimeOriginalXiGerm (σ : ℝ≥0) : paperPrimeTransportAnalyticRing σ :=
  ofAnalytic RHTower.xi (RHTower.xi_analyticOnNhd _)

/-- Literal transported completed source in that same analytic ring. -/
def paperPrimeTransportXiGerm (p : Nat.Primes) (σ : ℝ≥0)
    (t : paperPrimeTransportParameters p σ) : paperPrimeTransportAnalyticRing σ :=
  ofAnalytic (paperPrimeTransportXi p t)
    (fun z hz => paperPrimeTransportXi_analyticAt p σ t ⟨z, hz⟩)

/-- Both the actual multiplier and its inverse are analytic; this is a ring unit. -/
def paperPrimeTransportAnalyticUnit (p : Nat.Primes) (σ : ℝ≥0)
    (t : paperPrimeTransportParameters p σ) : (paperPrimeTransportAnalyticRing σ)ˣ :=
  unitOfAnalytic (paperPrimeTransportFactor p t)
    (fun z hz => paperPrimeTransportFactor_analyticAt p σ t ⟨z, hz⟩)
    (fun z hz => paperPrimeTransportFactor_ne_zero p σ t ⟨z, hz⟩)

/-- The ring unit multiplies the original analytic Xi element to the literal transported one. -/
theorem paperPrimeTransportXiGerm_eq_unit_mul (p : Nat.Primes) (σ : ℝ≥0)
    (t : paperPrimeTransportParameters p σ) :
    paperPrimeTransportXiGerm p σ t =
      (paperPrimeTransportAnalyticUnit p σ t : paperPrimeTransportAnalyticRing σ) *
        paperPrimeOriginalXiGerm σ :=
  Subtype.ext rfl

/-- The original principal analytic Xi ideal, including every multiplicity. -/
def paperPrimeOriginalXiIdeal (σ : ℝ≥0) : Ideal (paperPrimeTransportAnalyticRing σ) :=
  Ideal.span {paperPrimeOriginalXiGerm σ}

/-- Principal ideal of the literal transported completed source. -/
def paperPrimeTransportXiIdeal (p : Nat.Primes) (σ : ℝ≥0)
    (t : paperPrimeTransportParameters p σ) : Ideal (paperPrimeTransportAnalyticRing σ) :=
  Ideal.span {paperPrimeTransportXiGerm p σ t}

/-- Prime transport preserves the original analytic ideal exactly. -/
theorem paperPrimeTransportXiIdeal_eq (p : Nat.Primes) (σ : ℝ≥0)
    (t : paperPrimeTransportParameters p σ) :
    paperPrimeTransportXiIdeal p σ t = paperPrimeOriginalXiIdeal σ := by
  unfold paperPrimeTransportXiIdeal paperPrimeOriginalXiIdeal
  rw [paperPrimeTransportXiGerm_eq_unit_mul]
  exact Ideal.span_singleton_mul_left_unit (paperPrimeTransportAnalyticUnit p σ t).isUnit _

/-- Every infinitesimal thickening of the original source is retained. -/
theorem paperPrimeTransportXiIdeal_pow_eq (p : Nat.Primes) (σ : ℝ≥0)
    (t : paperPrimeTransportParameters p σ) (n : ℕ) :
    paperPrimeTransportXiIdeal p σ t ^ n = paperPrimeOriginalXiIdeal σ ^ n := by
  rw [paperPrimeTransportXiIdeal_eq]

/-- Canonical equivalence of the full analytic conormal modules I/I². -/
def paperPrimeTransportConormalEquiv (p : Nat.Primes) (σ : ℝ≥0)
    (t : paperPrimeTransportParameters p σ) :
    (paperPrimeTransportXiIdeal p σ t).Cotangent ≃ₗ[paperPrimeTransportAnalyticRing σ]
      (paperPrimeOriginalXiIdeal σ).Cotangent :=
  Ideal.Cotangent.equivOfEq _ _ (paperPrimeTransportXiIdeal_eq p σ t)

/-- The conormal map is induced by the identity on the original analytic ambient ring. -/
theorem paperPrimeTransportConormalEquiv_class (p : Nat.Primes) (σ : ℝ≥0)
    (t : paperPrimeTransportParameters p σ) (x : paperPrimeTransportXiIdeal p σ t) :
    paperPrimeTransportConormalEquiv p σ t
        ((paperPrimeTransportXiIdeal p σ t).toCotangent x) =
      (paperPrimeOriginalXiIdeal σ).toCotangent
        (LinearEquiv.ofEq _ _ (paperPrimeTransportXiIdeal_eq p σ t) x) :=
  Ideal.Cotangent.equivOfEq_toCotangent _ _ _ _

/-- At the arithmetic nonunit time, the full conormal survives on Re(s)>0. -/
def paperPrimeTimeOneConormalEquiv (p : Nat.Primes) :
    (paperPrimeTransportXiIdeal p 0 ⟨1, Or.inl rfl⟩).Cotangent
      ≃ₗ[paperPrimeTransportAnalyticRing 0] (paperPrimeOriginalXiIdeal 0).Cotangent :=
  paperPrimeTransportConormalEquiv p 0 ⟨1, Or.inl rfl⟩

end

end GaloisForLFunctions.HTGeometry
