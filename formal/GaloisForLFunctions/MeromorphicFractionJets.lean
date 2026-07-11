import GaloisForLFunctions.EllipticGammaExternalDefectNonElliptic
import GaloisForLFunctions.DifferenceDifferential

/-!
# Explicit differential jets of global meromorphic fractions

The `n`th differential jet of an analytic fraction is represented recursively by entire
numerator and denominator germs.  The same recursion on representative functions is entire, its
denominator remains nonzero, and its quotient agrees with the ordinary `n`th iterated derivative
at every regular point.  This identifies differential-field jets with punctured-local analytic
jets without assigning values at poles.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance meromorphicFractionJetsDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance meromorphicFractionJetsIntAlgebraAnalytic :
    Algebra ℤ (analyticSubring Set.univ) := Ring.toIntAlgebra _

local instance meromorphicFractionJetsIntAlgebraMero :
    Algebra ℤ (meroField Set.univ) := Ring.toIntAlgebra _

local instance meromorphicFractionJetsDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

/-- An entire function as an element of the global analytic subring. -/
def univAnalytic (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ) :
    analyticSubring Set.univ :=
  ⟨Germ.coeRingHom (𝓟 Set.univ) f, ⟨f, hf, rfl⟩⟩

/-- Recursive entire numerator/denominator pair for differential jets of `a / b`. -/
def analyticFractionJetPair
    (a b : analyticSubring Set.univ) :
    ℕ → analyticSubring Set.univ × analyticSubring Set.univ
  | 0 => (a, b)
  | n + 1 =>
      let p := analyticFractionJetPair a b n
      (analyticSubringDeriv isOpen_univ p.1 * p.2 -
        p.1 * analyticSubringDeriv isOpen_univ p.2, p.2 * p.2)

/-- Function-level quotient-rule recursion parallel to `analyticFractionJetPair`. -/
def functionFractionJetPair (f g : ℂ → ℂ) : ℕ → (ℂ → ℂ) × (ℂ → ℂ)
  | 0 => (f, g)
  | n + 1 =>
      let p := functionFractionJetPair f g n
      (fun z => deriv p.1 z * p.2 z - p.1 z * deriv p.2 z,
        fun z => p.2 z * p.2 z)

/-- Both functions in the recursive quotient-jet pair are entire. -/
theorem functionFractionJetPair_analytic
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ) (n : ℕ) :
    AnalyticOnNhd ℂ (functionFractionJetPair f g n).1 Set.univ ∧
      AnalyticOnNhd ℂ (functionFractionJetPair f g n).2 Set.univ := by
  induction n with
  | zero => exact ⟨hf, hg⟩
  | succ n ih =>
      simp only [functionFractionJetPair]
      exact ⟨(ih.1.deriv.mul ih.2).sub (ih.1.mul ih.2.deriv), ih.2.mul ih.2⟩

/-- The function recursion represents the analytic-subring recursion exactly. -/
theorem analyticFractionJetPair_rep
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ) (n : ℕ) :
    Germ.coeRingHom (𝓟 Set.univ) (functionFractionJetPair f g n).1 =
        ((analyticFractionJetPair (univAnalytic f hf) (univAnalytic g hg) n).1 :
          Germ (𝓟 Set.univ) ℂ) ∧
      Germ.coeRingHom (𝓟 Set.univ) (functionFractionJetPair f g n).2 =
        ((analyticFractionJetPair (univAnalytic f hf) (univAnalytic g hg) n).2 :
          Germ (𝓟 Set.univ) ℂ) := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
      simp only [functionFractionJetPair, analyticFractionJetPair]
      constructor
      · change Germ.ofFun (l := 𝓟 Set.univ)
            (fun z => deriv (functionFractionJetPair f g n).1 z *
                (functionFractionJetPair f g n).2 z -
              (functionFractionJetPair f g n).1 z *
                deriv (functionFractionJetPair f g n).2 z) =
          analyticGermDeriv isOpen_univ
                (analyticFractionJetPair (univAnalytic f hf)
                  (univAnalytic g hg) n).1.1 *
              (analyticFractionJetPair (univAnalytic f hf)
                (univAnalytic g hg) n).2.1 -
            (analyticFractionJetPair (univAnalytic f hf)
                (univAnalytic g hg) n).1.1 *
              analyticGermDeriv isOpen_univ
                (analyticFractionJetPair (univAnalytic f hf)
                  (univAnalytic g hg) n).2.1
        rw [← ih.1, ← ih.2]
        rfl
      · change Germ.ofFun (l := 𝓟 Set.univ)
            (fun z => (functionFractionJetPair f g n).2 z *
              (functionFractionJetPair f g n).2 z) =
          (analyticFractionJetPair (univAnalytic f hf)
              (univAnalytic g hg) n).2.1 *
            (analyticFractionJetPair (univAnalytic f hf)
              (univAnalytic g hg) n).2.1
        rw [← ih.2]
        rfl

/-- A nonzero initial denominator remains nonzero through every quotient-rule jet. -/
theorem analyticFractionJetPair_denominator_ne_zero
    {a b : analyticSubring Set.univ} (hb : b ≠ 0) (n : ℕ) :
    (analyticFractionJetPair a b n).2 ≠ 0 := by
  induction n with
  | zero => exact hb
  | succ n ih =>
      simp only [analyticFractionJetPair]
      exact mul_ne_zero ih ih

/-- Pointwise regularity of the initial denominator propagates through every function jet pair. -/
theorem functionFractionJetPair_denominator_ne_zero
    {f g : ℂ → ℂ} {z : ℂ} (hg : g z ≠ 0) (n : ℕ) :
    (functionFractionJetPair f g n).2 z ≠ 0 := by
  induction n with
  | zero => exact hg
  | succ n ih =>
      simp only [functionFractionJetPair]
      exact mul_ne_zero ih ih

/-- The differential-field `n`th jet of an analytic fraction is the recursive analytic fraction. -/
theorem differentialJet_analyticFraction_eq
    (a b : analyticSubring Set.univ) (hb : b ≠ 0) (n : ℕ) :
    differentialJet n
        (algebraMap (analyticSubring Set.univ) (meroField Set.univ) a /
          algebraMap (analyticSubring Set.univ) (meroField Set.univ) b) =
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (analyticFractionJetPair a b n).1 /
        algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (analyticFractionJetPair a b n).2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [differentialJet_succ, ih]
      simp only [analyticFractionJetPair]
      rw [Derivation.leibniz_div]
      simp only [smul_eq_mul, map_sub, map_mul]
      rw [meroFieldDifferential_algebraMap, meroFieldDifferential_algebraMap]
      have hd : algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (analyticFractionJetPair a b n).2 ≠ 0 :=
        fun hz => analyticFractionJetPair_denominator_ne_zero hb n
          ((IsFractionRing.injective (analyticSubring Set.univ) (meroField Set.univ))
            (by simpa using hz))
      field_simp [hd]
      all_goals first | exact isPreconnected_univ | exact Set.univ_nonempty

/-- At every regular point, the recursive quotient is the ordinary iterated derivative. -/
theorem functionFractionJetPair_div_eq_iteratedDeriv
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ) (n : ℕ) {z : ℂ} (hgz : g z ≠ 0) :
    (functionFractionJetPair f g n).1 z /
        (functionFractionJetPair f g n).2 z =
      iteratedDeriv n (fun w => f w / g w) z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
      let p := functionFractionJetPair f g n
      have hpa := (functionFractionJetPair_analytic hf hg n).1
      have hpb := (functionFractionJetPair_analytic hf hg n).2
      have hpbz : p.2 z ≠ 0 := functionFractionJetPair_denominator_ne_zero hgz n
      have hgne : ∀ᶠ w in 𝓝 z, g w ≠ 0 :=
        (hg z (Set.mem_univ z)).continuousAt.eventually_ne hgz
      have heq : (fun w => p.1 w / p.2 w) =ᶠ[𝓝 z]
          iteratedDeriv n (fun w => f w / g w) := by
        filter_upwards [hgne] with w hgw
        exact ih hgw
      have hderiv := heq.deriv_eq
      rw [← iteratedDeriv_succ] at hderiv
      dsimp [p] at hderiv
      simp only [functionFractionJetPair]
      rw [← hderiv]
      have hdiv := deriv_div (hpa z (Set.mem_univ z)).differentiableAt
        (hpb z (Set.mem_univ z)).differentiableAt hpbz
      convert hdiv.symm using 1 <;> ring

end

end GaloisForLFunctions
