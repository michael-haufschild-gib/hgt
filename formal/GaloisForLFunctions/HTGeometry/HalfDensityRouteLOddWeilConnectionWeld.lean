import GaloisForLFunctions.HTGeometry.RouteLOddCurrentSuzukiApertureMassReconstructionLaw
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Types.Basic

/-!
# Half-density Route-L odd-Weil connection weld

This module formalizes every proven statement on the corresponding Stage-2 card:

* exact half-density conjugacy of expansion/contraction Route-L operators with the reflected
  von-Mangoldt convolution;
* the actual locally finite reflected atomic distribution, weak entire parameter dependence,
  and exact critical normal derivative;
* the coefficient identities `-Λ(n) log(n) / √n` and `-(log p)^2 / √p`;
* the algebraic connection transgression;
* the log-coordinate arrow equivalence and vanishing algebraic cofiber.

All infinite atomic sums are `finsum`s whose finite support is proved from compact test-function
support. No truncation or convergence premise is introduced.
-/

open scoped BigOperators
open Distributions
open CategoryTheory
open CategoryTheory.Limits

namespace GaloisForLFunctions.HTGeometry

noncomputable section

abbrev PositiveReal_halfDensityRouteLOddWeilConnectionWeld := {x : ℝ // 0 < x}

noncomputable def halfDensityLogEquiv :
    (PositiveReal_halfDensityRouteLOddWeilConnectionWeld → ℂ) ≃ₗ[ℂ] (ℝ → ℂ) where
  toFun f t := Complex.exp ((t : ℂ) / 2) * f ⟨Real.exp t, Real.exp_pos t⟩
  invFun g x := Complex.exp (-(Real.log (x : ℝ) : ℂ) / 2) * g (Real.log (x : ℝ))
  left_inv f := by
    funext x
    change Complex.exp (-(Real.log (x : ℝ) : ℂ) / 2) *
      (Complex.exp ((Real.log (x : ℝ) : ℂ) / 2) *
        f ⟨Real.exp (Real.log (x : ℝ)), Real.exp_pos _⟩) = f x
    rw [← mul_assoc, ← Complex.exp_add]
    have hx : (⟨Real.exp (Real.log (x : ℝ)), Real.exp_pos _⟩ : PositiveReal_halfDensityRouteLOddWeilConnectionWeld) = x :=
      Subtype.ext (Real.exp_log x.prop)
    rw [hx]
    rw [show -(Real.log (x : ℝ) : ℂ) / 2 + (Real.log (x : ℝ) : ℂ) / 2 = 0 by ring,
      Complex.exp_zero, one_mul]
  right_inv g := by
    funext t
    change Complex.exp ((t : ℂ) / 2) *
      (Complex.exp (-(Real.log (Real.exp t) : ℂ) / 2) *
        g (Real.log (Real.exp t))) = g t
    rw [Real.log_exp, ← mul_assoc, ← Complex.exp_add]
    rw [show (t : ℂ) / 2 + -(t : ℂ) / 2 = 0 by ring, Complex.exp_zero, one_mul]
  map_add' f g := by
    funext t
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext t
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

def complexMellinWeight (b : ℂ) (n : ℕ) : ℂ :=
  Complex.exp (-(Real.log (n : ℝ) : ℂ) * b)

def positiveDilation (n : ApertureAtom) (f : PositiveReal_halfDensityRouteLOddWeilConnectionWeld → ℂ) (x : PositiveReal_halfDensityRouteLOddWeilConnectionWeld) : ℂ :=
  f ⟨(n : ℝ) * x, mul_pos (by exact_mod_cast (show 0 < (n : ℕ) by omega)) x.prop⟩

def positiveContraction (n : ApertureAtom) (f : PositiveReal_halfDensityRouteLOddWeilConnectionWeld → ℂ) (x : PositiveReal_halfDensityRouteLOddWeilConnectionWeld) : ℂ :=
  f ⟨(x : ℝ) / n, div_pos x.prop (by exact_mod_cast (show 0 < (n : ℕ) by omega))⟩

theorem halfDensityLogEquiv_positiveDilation
    (n : {n : ℕ // 2 ≤ n}) (g : ℝ → ℂ) (t : ℝ) :
    halfDensityLogEquiv (positiveDilation n (halfDensityLogEquiv.symm g)) t =
      complexMellinWeight (1 / 2) n * g (t + Real.log (n : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < (n : ℕ) by omega)
  change Complex.exp ((t : ℂ) / 2) *
      (Complex.exp (-(Real.log ((n : ℝ) * Real.exp t) : ℂ) / 2) *
        g (Real.log ((n : ℝ) * Real.exp t))) = _
  rw [Real.log_mul hnpos.ne' (Real.exp_pos t).ne', Real.log_exp,
    ← mul_assoc, ← Complex.exp_add]
  rw [add_comm (Real.log (n : ℝ)) t]
  rw [complexMellinWeight]
  congr 1
  push_cast
  ring_nf

theorem halfDensityLogEquiv_positiveContraction
    (n : {n : ℕ // 2 ≤ n}) (g : ℝ → ℂ) (t : ℝ) :
    halfDensityLogEquiv (positiveContraction n (halfDensityLogEquiv.symm g)) t =
      complexMellinWeight (-1 / 2) n * g (t - Real.log (n : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < (n : ℕ) by omega)
  change Complex.exp ((t : ℂ) / 2) *
      (Complex.exp (-(Real.log (Real.exp t / (n : ℝ)) : ℂ) / 2) *
        g (Real.log (Real.exp t / (n : ℝ)))) = _
  rw [Real.log_div (Real.exp_pos t).ne' hnpos.ne', Real.log_exp,
    ← mul_assoc, ← Complex.exp_add]
  rw [complexMellinWeight]
  congr 1
  push_cast
  ring_nf

theorem complexMellinWeight_add (b c : ℂ) (n : ℕ) :
    complexMellinWeight (b + c) n =
      complexMellinWeight b n * complexMellinWeight c n := by
  rw [complexMellinWeight, complexMellinWeight, complexMellinWeight, ← Complex.exp_add]
  congr 1
  ring

def routeLPositiveExpansionOperator
    (a : ℂ) (f : PositiveReal_halfDensityRouteLOddWeilConnectionWeld → ℂ) (x : PositiveReal_halfDensityRouteLOddWeilConnectionWeld) : ℂ :=
  ∑ᶠ n : ℕ, if hn : 2 ≤ n then
    (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight a n *
      positiveDilation ⟨n, hn⟩ f x else 0

def routeLPositiveContractionOperator
    (a : ℂ) (f : PositiveReal_halfDensityRouteLOddWeilConnectionWeld → ℂ) (x : PositiveReal_halfDensityRouteLOddWeilConnectionWeld) : ℂ :=
  ∑ᶠ n : ℕ, if hn : 2 ≤ n then
    (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight (a + 1) n *
      positiveContraction ⟨n, hn⟩ f x else 0

def routeLPositiveComparisonOperator
    (a : ℂ) (f : PositiveReal_halfDensityRouteLOddWeilConnectionWeld → ℂ) : PositiveReal_halfDensityRouteLOddWeilConnectionWeld → ℂ :=
  routeLPositiveContractionOperator a f - routeLPositiveExpansionOperator a f

def routeLLogExpansionOperator (a : ℂ) (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑ᶠ n : ℕ, if 2 ≤ n then
    (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight (a + 1 / 2) n *
      g (t + Real.log (n : ℝ)) else 0

def routeLLogContractionOperator (a : ℂ) (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑ᶠ n : ℕ, if 2 ≤ n then
    (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight (a + 1 / 2) n *
      g (t - Real.log (n : ℝ)) else 0

def routeLLogComparisonOperator (a : ℂ) (g : ℝ → ℂ) : ℝ → ℂ :=
  routeLLogContractionOperator a g - routeLLogExpansionOperator a g

theorem halfDensityLogEquiv_routeLPositiveExpansionOperator
    (a : ℂ) (g : ℝ → ℂ) :
    halfDensityLogEquiv
        (routeLPositiveExpansionOperator a (halfDensityLogEquiv.symm g)) =
      routeLLogExpansionOperator a g := by
  funext t
  rw [halfDensityLogEquiv]
  change Complex.exp ((t : ℂ) / 2) *
      (∑ᶠ n : ℕ, if hn : 2 ≤ n then
        (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight a n *
          positiveDilation ⟨n, hn⟩ (halfDensityLogEquiv.symm g)
            ⟨Real.exp t, Real.exp_pos t⟩ else 0) = _
  rw [mul_finsum]
  apply finsum_congr
  intro n
  by_cases hn : 2 ≤ n
  · simp only [dif_pos hn, if_pos hn]
    have hd := halfDensityLogEquiv_positiveDilation ⟨n, hn⟩ g t
    change Complex.exp ((t : ℂ) / 2) *
      positiveDilation ⟨n, hn⟩ (halfDensityLogEquiv.symm g)
        ⟨Real.exp t, Real.exp_pos t⟩ = _ at hd
    rw [show complexMellinWeight (a + 1 / 2) n =
      complexMellinWeight a n * complexMellinWeight (1 / 2) n from
        complexMellinWeight_add a (1 / 2) n]
    calc
      Complex.exp ((t : ℂ) / 2) *
          ((ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight a n *
            positiveDilation ⟨n, hn⟩ (halfDensityLogEquiv.symm g)
              ⟨Real.exp t, Real.exp_pos t⟩) =
          (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight a n *
            (Complex.exp ((t : ℂ) / 2) *
              positiveDilation ⟨n, hn⟩ (halfDensityLogEquiv.symm g)
                ⟨Real.exp t, Real.exp_pos t⟩) := by ring
      _ = _ := by rw [hd]; ring
  · simp only [dif_neg hn, if_neg hn, mul_zero]

theorem halfDensityLogEquiv_routeLPositiveContractionOperator
    (a : ℂ) (g : ℝ → ℂ) :
    halfDensityLogEquiv
        (routeLPositiveContractionOperator a (halfDensityLogEquiv.symm g)) =
      routeLLogContractionOperator a g := by
  funext t
  rw [halfDensityLogEquiv]
  change Complex.exp ((t : ℂ) / 2) *
      (∑ᶠ n : ℕ, if hn : 2 ≤ n then
        (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight (a + 1) n *
          positiveContraction ⟨n, hn⟩ (halfDensityLogEquiv.symm g)
            ⟨Real.exp t, Real.exp_pos t⟩ else 0) = _
  rw [mul_finsum]
  apply finsum_congr
  intro n
  by_cases hn : 2 ≤ n
  · simp only [dif_pos hn, if_pos hn]
    have hc := halfDensityLogEquiv_positiveContraction ⟨n, hn⟩ g t
    change Complex.exp ((t : ℂ) / 2) *
      positiveContraction ⟨n, hn⟩ (halfDensityLogEquiv.symm g)
        ⟨Real.exp t, Real.exp_pos t⟩ = _ at hc
    rw [show complexMellinWeight (a + 1 / 2) n =
      complexMellinWeight (a + 1) n * complexMellinWeight (-1 / 2) n by
        rw [← complexMellinWeight_add]
        congr 1
        ring]
    calc
      Complex.exp ((t : ℂ) / 2) *
          ((ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight (a + 1) n *
            positiveContraction ⟨n, hn⟩ (halfDensityLogEquiv.symm g)
              ⟨Real.exp t, Real.exp_pos t⟩) =
          (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight (a + 1) n *
            (Complex.exp ((t : ℂ) / 2) *
              positiveContraction ⟨n, hn⟩ (halfDensityLogEquiv.symm g)
                ⟨Real.exp t, Real.exp_pos t⟩) := by ring
      _ = _ := by rw [hc]; ring
  · simp only [dif_neg hn, if_neg hn, mul_zero]

theorem halfDensity_routeL_comparison_weld (a : ℂ) (g : ℝ → ℂ) :
    halfDensityLogEquiv
        (routeLPositiveComparisonOperator a (halfDensityLogEquiv.symm g)) =
      routeLLogComparisonOperator a g := by
  rw [routeLPositiveComparisonOperator, routeLLogComparisonOperator, map_sub,
    halfDensityLogEquiv_routeLPositiveContractionOperator,
    halfDensityLogEquiv_routeLPositiveExpansionOperator]

def reflectedAtomicConvolution (b : ℂ) (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑ᶠ n : ℕ, if 2 ≤ n then
    (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight b n *
      (g (t - Real.log (n : ℝ)) - g (t + Real.log (n : ℝ))) else 0

theorem routeLLogTranslatedTerms_support_finite
    (a : ℂ) (g : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℂ)) (t : ℝ) :
    (Function.support fun n : ℕ => if 2 ≤ n then
      (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight (a + 1 / 2) n *
        g (t - Real.log (n : ℝ)) else 0).Finite ∧
    (Function.support fun n : ℕ => if 2 ≤ n then
      (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight (a + 1 / 2) n *
        g (t + Real.log (n : ℝ)) else 0).Finite := by
  obtain ⟨lo, hlo⟩ := g.hasCompactSupport.bddBelow
  obtain ⟨hi, hhi⟩ := g.hasCompactSupport.bddAbove
  constructor
  · refine (positiveAtomicLocations_interval_finite (t - hi) (t - lo)).subset ?_
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    by_cases hn2 : 2 ≤ n
    · have hg : g (t - Real.log (n : ℝ)) ≠ 0 := by
        intro hz
        exact hn (by simp only [if_pos hn2, hz, mul_zero])
      have hmem : t - Real.log (n : ℝ) ∈ tsupport (g : ℝ → ℂ) := subset_closure hg
      simp only [Set.mem_setOf_eq, Set.mem_Icc]
      constructor <;> linarith [hlo hmem, hhi hmem]
    · exact (hn (by simp only [if_neg hn2])).elim
  · refine (positiveAtomicLocations_interval_finite (lo - t) (hi - t)).subset ?_
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    by_cases hn2 : 2 ≤ n
    · have hg : g (t + Real.log (n : ℝ)) ≠ 0 := by
        intro hz
        exact hn (by simp only [if_pos hn2, hz, mul_zero])
      have hmem : t + Real.log (n : ℝ) ∈ tsupport (g : ℝ → ℂ) := subset_closure hg
      simp only [Set.mem_setOf_eq, Set.mem_Icc]
      constructor <;> linarith [hlo hmem, hhi hmem]
    · exact (hn (by simp only [if_neg hn2])).elim

theorem routeLLogComparisonOperator_eq_reflectedAtomicConvolution
    (a : ℂ) (g : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℂ)) :
    routeLLogComparisonOperator a g = reflectedAtomicConvolution (a + 1 / 2) g := by
  funext t
  unfold routeLLogComparisonOperator routeLLogContractionOperator
    routeLLogExpansionOperator reflectedAtomicConvolution
  simp only [Pi.sub_apply]
  rw [← finsum_sub_distrib
    (routeLLogTranslatedTerms_support_finite a g t).1
    (routeLLogTranslatedTerms_support_finite a g t).2]
  apply finsum_congr
  intro n
  by_cases hn : 2 ≤ n
  · simp only [if_pos hn]
    ring
  · simp only [if_neg hn, sub_zero]

theorem halfDensity_routeL_oddWeil_weld
    (a : ℂ) (g : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℂ)) :
    halfDensityLogEquiv
        (routeLPositiveComparisonOperator a (halfDensityLogEquiv.symm g)) =
      reflectedAtomicConvolution (a + 1 / 2) g := by
  rw [halfDensity_routeL_comparison_weld,
    routeLLogComparisonOperator_eq_reflectedAtomicConvolution]

/-! ## The actual reflected atomic distribution -/

abbrev ComplexTestDistribution :=
  𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℂ)

theorem reflectedAtomicIndices_finite (K : TopologicalSpace.Compacts ℝ) :
    Set.Finite {n : ℕ | 2 ≤ n ∧
      (Real.log (n : ℝ) ∈ (K : Set ℝ) ∨ -Real.log (n : ℝ) ∈ (K : Set ℝ))} := by
  obtain ⟨lo, hlo⟩ := K.isCompact.bddBelow
  obtain ⟨hi, hhi⟩ := K.isCompact.bddAbove
  refine (positiveAtomicLocations_interval_finite (min lo (-hi)) (max hi (-lo))).subset ?_
  intro n hn
  rcases hn with ⟨hn2, hnK | hnK⟩
  · simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · exact (min_le_left _ _).trans (hlo hnK)
    · exact (hhi hnK).trans (le_max_left _ _)
  · simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · have hlog : -hi ≤ Real.log (n : ℝ) := by linarith [hhi hnK]
      exact (min_le_right _ _).trans hlog
    · have hlog : Real.log (n : ℝ) ≤ -lo := by linarith [hlo hnK]
      exact hlog.trans (le_max_right _ _)

noncomputable def reflectedAtomicIndices (K : TopologicalSpace.Compacts ℝ) : Finset ℕ :=
  (reflectedAtomicIndices_finite K).toFinset

@[simp] theorem mem_reflectedAtomicIndices
    (K : TopologicalSpace.Compacts ℝ) (n : ℕ) :
    n ∈ reflectedAtomicIndices K ↔
      2 ≤ n ∧
        (Real.log (n : ℝ) ∈ (K : Set ℝ) ∨ -Real.log (n : ℝ) ∈ (K : Set ℝ)) := by
  rw [reflectedAtomicIndices, Set.Finite.mem_toFinset]
  rfl

noncomputable def routeLReflectedAtomicDistribution (b : ℂ) :
    ComplexTestDistribution :=
  TestFunction.limitCLM ℝ
    (fun g => ∑ᶠ n : ℕ, if 2 ≤ n then
      (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight b n *
        (g (Real.log (n : ℝ)) - g (-Real.log (n : ℝ))) else 0)
    (fun K _ =>
      { toFun := fun g => ∑ n ∈ reflectedAtomicIndices K,
          (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight b n *
            (g (Real.log (n : ℝ)) - g (-Real.log (n : ℝ)))
        map_add' := by
          intro f g
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro n hn
          change (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight b n *
              (((f (Real.log (n : ℝ)) + g (Real.log (n : ℝ)) : ℝ) : ℂ) -
                ((f (-Real.log (n : ℝ)) + g (-Real.log (n : ℝ)) : ℝ) : ℂ)) =
            (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight b n *
                ((f (Real.log (n : ℝ)) : ℂ) - (f (-Real.log (n : ℝ)) : ℂ)) +
              (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight b n *
                ((g (Real.log (n : ℝ)) : ℂ) - (g (-Real.log (n : ℝ)) : ℂ))
          push_cast
          ring
        map_smul' := by
          intro r g
          simp only [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          change (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight b n *
              (((r * g (Real.log (n : ℝ)) : ℝ) : ℂ) -
                ((r * g (-Real.log (n : ℝ)) : ℝ) : ℂ)) =
            (r : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight b n *
              ((g (Real.log (n : ℝ)) : ℂ) - (g (-Real.log (n : ℝ)) : ℂ)))
          push_cast
          ring
        cont := by fun_prop })
    (by
      intro K Ksub g
      change (∑ᶠ n : ℕ, if 2 ≤ n then
          (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight b n *
            (g (Real.log (n : ℝ)) - g (-Real.log (n : ℝ))) else 0) =
        ∑ n ∈ reflectedAtomicIndices K,
          (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight b n *
            (g (Real.log (n : ℝ)) - g (-Real.log (n : ℝ)))
      calc
        (∑ᶠ n : ℕ, if 2 ≤ n then
            (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight b n *
              (g (Real.log (n : ℝ)) - g (-Real.log (n : ℝ))) else 0) =
            ∑ n ∈ reflectedAtomicIndices K, if 2 ≤ n then
              (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight b n *
                (g (Real.log (n : ℝ)) - g (-Real.log (n : ℝ))) else 0 := by
          apply finsum_eq_finsetSum_of_support_subset
          intro n hn
          change n ∈ reflectedAtomicIndices K
          rw [mem_reflectedAtomicIndices]
          simp only [Function.mem_support, ne_eq] at hn
          by_cases hn2 : 2 ≤ n
          · refine ⟨hn2, ?_⟩
            by_contra hnot
            push Not at hnot
            have hplus : g (Real.log (n : ℝ)) = 0 := g.zero_on_compl hnot.1
            have hminus : g (-Real.log (n : ℝ)) = 0 := g.zero_on_compl hnot.2
            exact hn (by simp [hplus, hminus])
          · exact (hn (by simp only [if_neg hn2])).elim
        _ = _ := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [if_pos (mem_reflectedAtomicIndices K n |>.mp hn).1])

@[simp] theorem routeLReflectedAtomicDistribution_apply
    (b : ℂ) (g : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) :
    routeLReflectedAtomicDistribution b g =
      ∑ᶠ n : ℕ, if 2 ≤ n then
        (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight b n *
          (g (Real.log (n : ℝ)) - g (-Real.log (n : ℝ))) else 0 := rfl

theorem hasDerivAt_complexMellinWeight (b : ℂ) (n : ℕ) :
    HasDerivAt (fun z : ℂ => complexMellinWeight z n)
      (-(Real.log (n : ℝ) : ℂ) * complexMellinWeight b n) b := by
  have h : HasDerivAt
      (fun z : ℂ => -(Real.log (n : ℝ) : ℂ) * z)
      (-(Real.log (n : ℝ) : ℂ)) b := by
    simpa using (hasDerivAt_id b).const_mul (-(Real.log (n : ℝ) : ℂ))
  simpa [complexMellinWeight, mul_comm] using h.cexp

theorem hasDerivAt_complexMellinWeight_shift_critical (n : ℕ) :
    HasDerivAt (fun a : ℂ => complexMellinWeight (a + 1 / 2) n)
      (-(Real.log (n : ℝ) : ℂ) * complexMellinWeight (1 / 2) n) 0 := by
  have hshift : HasDerivAt (fun a : ℂ => a + 1 / 2) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).add_const (1 / 2)
  have hbase : HasDerivAt (fun z : ℂ => complexMellinWeight z n)
      (-(Real.log (n : ℝ) : ℂ) * complexMellinWeight (1 / 2) n)
      ((fun a : ℂ => a + 1 / 2) 0) := by
    simpa using hasDerivAt_complexMellinWeight (1 / 2) n
  change HasDerivAt
    ((fun z : ℂ => complexMellinWeight z n) ∘ (fun a : ℂ => a + 1 / 2))
    (-(Real.log (n : ℝ) : ℂ) * complexMellinWeight (1 / 2) n) 0
  exact (hbase.comp 0 hshift).congr_deriv (mul_one _)

theorem analyticAt_complexMellinWeight (b : ℂ) (n : ℕ) :
    AnalyticAt ℂ (fun z : ℂ => complexMellinWeight z n) b := by
  unfold complexMellinWeight
  fun_prop

noncomputable def reflectedAtomicTestCarrier
    (g : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) : TopologicalSpace.Compacts ℝ :=
  ⟨tsupport g, g.hasCompactSupport⟩

theorem routeLReflectedAtomicDistribution_apply_eq_finset
    (b : ℂ) (g : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) :
    routeLReflectedAtomicDistribution b g =
      ∑ n ∈ reflectedAtomicIndices (reflectedAtomicTestCarrier g),
        (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight b n *
          (g (Real.log (n : ℝ)) - g (-Real.log (n : ℝ))) := by
  rw [routeLReflectedAtomicDistribution_apply]
  calc
    (∑ᶠ n : ℕ, if 2 ≤ n then
        (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight b n *
          (g (Real.log (n : ℝ)) - g (-Real.log (n : ℝ))) else 0) =
      ∑ n ∈ reflectedAtomicIndices (reflectedAtomicTestCarrier g), if 2 ≤ n then
        (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight b n *
          (g (Real.log (n : ℝ)) - g (-Real.log (n : ℝ))) else 0 := by
      apply finsum_eq_finsetSum_of_support_subset
      intro n hn
      change n ∈ reflectedAtomicIndices (reflectedAtomicTestCarrier g)
      rw [mem_reflectedAtomicIndices]
      simp only [Function.mem_support, ne_eq] at hn
      by_cases hn2 : 2 ≤ n
      · refine ⟨hn2, ?_⟩
        by_contra hnot
        push Not at hnot
        have hplus : g (Real.log (n : ℝ)) = 0 := by
          by_contra hg
          exact hnot.1 (subset_closure hg)
        have hminus : g (-Real.log (n : ℝ)) = 0 := by
          by_contra hg
          exact hnot.2 (subset_closure hg)
        exact hn (by simp [hplus, hminus])
      · exact (hn (by simp only [if_neg hn2])).elim
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [if_pos (mem_reflectedAtomicIndices _ n |>.mp hn).1]

/-- Every scalar evaluation of the reflected Route-L distribution is entire in its parameter. -/
theorem routeLReflectedAtomicDistribution_weaklyEntire
    (g : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) (b : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => routeLReflectedAtomicDistribution z g) b := by
  let S := reflectedAtomicIndices (reflectedAtomicTestCarrier g)
  have hfun : (fun z : ℂ => routeLReflectedAtomicDistribution z g) =
      fun z : ℂ => ∑ n ∈ S,
        (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight z n *
          (g (Real.log (n : ℝ)) - g (-Real.log (n : ℝ))) := by
    funext z
    exact routeLReflectedAtomicDistribution_apply_eq_finset z g
  rw [hfun]
  apply Finset.analyticAt_fun_sum
  intro n hn
  exact (analyticAt_const.mul (analyticAt_complexMellinWeight b n)).mul analyticAt_const

def routeLReflectedNormalDerivativeFunctional
    (g : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) : ℂ :=
  ∑ᶠ n : ℕ, if 2 ≤ n then
    (ArithmeticFunction.vonMangoldt n : ℂ) *
      (-(Real.log (n : ℝ) : ℂ) * complexMellinWeight (1 / 2) n) *
      (g (Real.log (n : ℝ)) - g (-Real.log (n : ℝ))) else 0

theorem routeLReflectedNormalDerivativeFunctional_eq_finset
    (g : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) :
    routeLReflectedNormalDerivativeFunctional g =
      ∑ n ∈ reflectedAtomicIndices (reflectedAtomicTestCarrier g),
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          (-(Real.log (n : ℝ) : ℂ) * complexMellinWeight (1 / 2) n) *
          (g (Real.log (n : ℝ)) - g (-Real.log (n : ℝ))) := by
  unfold routeLReflectedNormalDerivativeFunctional
  calc
    (∑ᶠ n : ℕ, if 2 ≤ n then
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          (-(Real.log (n : ℝ) : ℂ) * complexMellinWeight (1 / 2) n) *
          (g (Real.log (n : ℝ)) - g (-Real.log (n : ℝ))) else 0) =
      ∑ n ∈ reflectedAtomicIndices (reflectedAtomicTestCarrier g), if 2 ≤ n then
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          (-(Real.log (n : ℝ) : ℂ) * complexMellinWeight (1 / 2) n) *
          (g (Real.log (n : ℝ)) - g (-Real.log (n : ℝ))) else 0 := by
      apply finsum_eq_finsetSum_of_support_subset
      intro n hn
      change n ∈ reflectedAtomicIndices (reflectedAtomicTestCarrier g)
      rw [mem_reflectedAtomicIndices]
      simp only [Function.mem_support, ne_eq] at hn
      by_cases hn2 : 2 ≤ n
      · refine ⟨hn2, ?_⟩
        by_contra hnot
        push Not at hnot
        have hplus : g (Real.log (n : ℝ)) = 0 := by
          by_contra hg
          exact hnot.1 (subset_closure hg)
        have hminus : g (-Real.log (n : ℝ)) = 0 := by
          by_contra hg
          exact hnot.2 (subset_closure hg)
        exact hn (by simp [hplus, hminus])
      · exact (hn (by simp only [if_neg hn2])).elim
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [if_pos (mem_reflectedAtomicIndices _ n |>.mp hn).1]

/-- Exact normal derivative at the critical half-density parameter. -/
theorem hasDerivAt_routeLReflectedAtomicDistribution_critical
    (g : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)) :
    HasDerivAt
      (fun a : ℂ => routeLReflectedAtomicDistribution (a + 1 / 2) g)
      (routeLReflectedNormalDerivativeFunctional g) 0 := by
  let S := reflectedAtomicIndices (reflectedAtomicTestCarrier g)
  have hfun : (fun a : ℂ => routeLReflectedAtomicDistribution (a + 1 / 2) g) =
      fun a : ℂ => ∑ n ∈ S,
        (ArithmeticFunction.vonMangoldt n : ℂ) * complexMellinWeight (a + 1 / 2) n *
          (g (Real.log (n : ℝ)) - g (-Real.log (n : ℝ))) := by
    funext a
    exact routeLReflectedAtomicDistribution_apply_eq_finset (a + 1 / 2) g
  rw [hfun, routeLReflectedNormalDerivativeFunctional_eq_finset]
  refine (HasDerivAt.fun_sum (u := S) (x := (0 : ℂ)) (fun n hn =>
    ((hasDerivAt_const (x := (0 : ℂ))
        (ArithmeticFunction.vonMangoldt n : ℂ)).mul
      (hasDerivAt_complexMellinWeight_shift_critical n)).mul_const
          (g (Real.log (n : ℝ)) - g (-Real.log (n : ℝ))))).congr_deriv ?_
  apply Finset.sum_congr rfl
  intro n hn
  simp only [zero_mul, zero_add]

theorem complexMellinWeight_ofReal_eq_arithmeticMellinWeight
    (a : ℝ) {n : ℕ} (hn : n ≠ 0) :
    complexMellinWeight (a : ℂ) n = (arithmeticMellinWeight a n : ℂ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [complexMellinWeight, arithmeticMellinWeight, if_neg hn,
    Real.rpow_def_of_pos hnpos, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

def routeLReflectedNormalCoefficient (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) *
    (-(Real.log (n : ℝ) : ℂ) * complexMellinWeight (1 / 2) n)

theorem routeLReflectedNormalCoefficient_eq_primeWeilTangent
    {n : ℕ} (hn : n ≠ 0) :
    routeLReflectedNormalCoefficient n =
      (atomicPositionMul primeWeilKernel).pos n := by
  have hw : complexMellinWeight (1 / 2 : ℂ) n =
      (arithmeticMellinWeight (1 / 2 : ℝ) n : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
    exact complexMellinWeight_ofReal_eq_arithmeticMellinWeight (1 / 2 : ℝ) hn
  rw [routeLReflectedNormalCoefficient, hw, primeWeilTangent_positiveCoefficient]
  ring

/-- Paper normalization `-Λ(n) log(n) / sqrt(n)` for every positive arithmetic index. -/
theorem routeLReflectedNormalCoefficient_eq_log_div_sqrt
    {n : ℕ} (hn : n ≠ 0) :
    routeLReflectedNormalCoefficient n =
      -Complex.ofReal
        (ArithmeticFunction.vonMangoldt n * Real.log (n : ℝ) / Real.sqrt n) := by
  rw [routeLReflectedNormalCoefficient_eq_primeWeilTangent hn,
    primeWeilTangent_positiveCoefficient_eq_log_div_sqrt hn]

/-- At a prime the normal coefficient is exactly `-(log p)^2 / sqrt p`. -/
theorem routeLReflectedNormalCoefficient_prime
    {p : ℕ} (hp : p.Prime) :
    routeLReflectedNormalCoefficient p =
      -Complex.ofReal ((Real.log (p : ℝ)) ^ 2 / Real.sqrt p) := by
  rw [routeLReflectedNormalCoefficient_eq_log_div_sqrt hp.ne_zero,
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  congr 2
  ring

/-! ## Algebraic connection transgression -/

/-- Universal block identity underlying `∇⁻ b_Γ - b_Γ ∇ᵈᵢᵃᵍ = κ π₋`. -/
theorem routeLConnectionTransgression_block
    {X : Type*} (Aminus Aplus Fminus Fplus : X → ℂ) :
    (Aminus * Fminus - Aplus * Fplus) - Aminus * (Fminus - Fplus) =
      (Aminus - Aplus) * Fplus := by
  funext x
  simp only [Pi.mul_apply, Pi.sub_apply]
  ring

/-- The paper's Route-L connection formula on the arithmetic coefficient algebra. -/
theorem halfDensityRouteL_connection_transgression (a : ℝ) :
    ((routeLContractionConnection a * routeLContractionMobiusSection a) -
        (routeLExpansionConnection a * routeLMobiusSection a)) -
      routeLContractionConnection a * routeLSourceTransgression a =
    routeLComparisonDefect a * routeLMobiusSection a :=
  routeLSourceTransgression_covariant a

/-! ## Arrow equivalence and its zero cofiber -/

structure FunctionArrowEquiv {A B C D : Type*} (f : A → B) (g : C → D) where
  domainEquiv : A ≃ C
  codomainEquiv : B ≃ D
  intertwines : ∀ x, codomainEquiv (f x) = g (domainEquiv x)

abbrev ComplexRouteLTestFunction :=
  𝓓((⊤ : TopologicalSpace.Opens ℝ), ℂ)

/-- Exact equivalence between the positive-coordinate Route-L arrow and reflected convolution. -/
noncomputable def halfDensityRouteLArrowEquiv (a : ℂ) :
    FunctionArrowEquiv
      (fun g : ComplexRouteLTestFunction =>
        routeLPositiveComparisonOperator a (halfDensityLogEquiv.symm g))
      (fun g : ComplexRouteLTestFunction =>
        reflectedAtomicConvolution (a + 1 / 2) g) where
  domainEquiv := Equiv.refl _
  codomainEquiv := halfDensityLogEquiv.toEquiv
  intertwines g := halfDensity_routeL_oddWeil_weld a g

noncomputable def halfDensityRouteLPositiveArrow (a : ℂ) : Arrow Type :=
  Arrow.mk (TypeCat.ofHom (show ComplexRouteLTestFunction → (PositiveReal_halfDensityRouteLOddWeilConnectionWeld → ℂ) from
    fun g => routeLPositiveComparisonOperator a (halfDensityLogEquiv.symm g)))

noncomputable def halfDensityRouteLConvolutionArrow (a : ℂ) : Arrow Type :=
  Arrow.mk (TypeCat.ofHom (show ComplexRouteLTestFunction → (ℝ → ℂ) from
    fun g => reflectedAtomicConvolution (a + 1 / 2) g))

/-- The literal arrow-category isomorphism of the half-density commutative square. -/
noncomputable def halfDensityRouteLArrowIso (a : ℂ) :
    halfDensityRouteLPositiveArrow a ≅ halfDensityRouteLConvolutionArrow a :=
  Arrow.isoMk
    (Equiv.toIso (Equiv.refl _))
    (Equiv.toIso halfDensityLogEquiv.toEquiv)
    (by
      ext g
      exact (halfDensity_routeL_oddWeil_weld a g).symm)

/-- Every realization functor preserves the Route-L arrow equivalence. -/
theorem halfDensityRouteLArrowIso_preserved
    {C : Type*} [Category C]
    (F : Arrow Type ⥤ C) (a : ℂ) :
    IsIso (F.map (halfDensityRouteLArrowIso a).hom) := by
  infer_instance

/-- In every preadditive realization admitting the cofiber, that cofiber is a zero object.
Stable realizations are a special case. -/
theorem halfDensityRouteLArrowIso_cofiber_isZero
    {C : Type*} [Category C] [Preadditive C]
    (F : Arrow Type ⥤ C) (a : ℂ)
    [HasCokernel (F.map (halfDensityRouteLArrowIso a).hom)] :
    IsZero (cokernel (F.map (halfDensityRouteLArrowIso a).hom)) :=
  isZero_cokernel_of_epi _

abbrev HalfDensityLogCofiber :=
  (ℝ → ℂ) ⧸ LinearMap.range halfDensityLogEquiv.toLinearMap

/-- The algebraic cofiber of the log-coordinate equivalence is zero. -/
theorem halfDensityLogCofiber_subsingleton : Subsingleton HalfDensityLogCofiber := by
  rw [Submodule.Quotient.subsingleton_iff]
  exact LinearMap.range_eq_top.mpr halfDensityLogEquiv.surjective

theorem halfDensityLogCofiber_eq_zero (q : HalfDensityLogCofiber) : q = 0 :=
  @Subsingleton.elim _ halfDensityLogCofiber_subsingleton q 0

end

end GaloisForLFunctions.HTGeometry
