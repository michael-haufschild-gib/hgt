import GaloisForLFunctions.RHTower.EulerSourceJetJacobian
import GaloisForLFunctions.RHTower.CompletedFluxPrimeArchDecomposition
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Exact completed Euler-source image in infinite flux-jet space

This module packages the full residue-filled local jet together with one connected meromorphic
continuation reaching `re s > 1`.  After subtracting the fixed archimedean channel, admissibility
means exact representation by a Dirichlet series absolutely convergent on every closed half-plane
strictly right of `1`.

The coefficient stream is not auxiliary data in the final predicate: `canonicalDirichletCoeff`
chooses the representation, and `dirichletRepresentsAboveOne_unique` proves that choice unique.
For every `N >= 2`, `tendsto_dirichlet_recursive_extraction` proves the literal recursive
far-right extraction formula.  The all-order quadratic prime-ray equations then cut out exactly
one prime-indexed degree-one Euler parameter field.  The von Mangoldt stream is exactly the unit
parameter sublocus.
-/

open Complex Set Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Open Euler half-plane. -/
def rightHalfPlaneOne : Set ℂ := {s | 1 < s.re}

theorem isOpen_rightHalfPlaneOne : IsOpen rightHalfPlaneOne := by
  exact isOpen_lt continuous_const Complex.continuous_re

/-- Coefficients absolutely summable at every real exponent strictly larger than one.  The
coefficients at zero and one vanish because the prime logarithmic flux starts at `n = 2`. -/
structure AboveOneDirichletCoeff (c : ℕ → ℂ) : Prop where
  zero : c 0 = 0
  one : c 1 = 0
  summable : ∀ σ : ℝ, 1 < σ → LSeriesSummable c σ

/-- Exact Dirichlet representation on the whole Euler half-plane. -/
structure DirichletRepresentsAboveOne (f : ℂ → ℂ) (c : ℕ → ℂ) : Prop
    extends AboveOneDirichletCoeff c where
  eqOn : ∀ s ∈ rightHalfPlaneOne, f s = LSeries c s

/-- Existence of an absolutely convergent Dirichlet representation on `re s > 1`. -/
def DirichletAdmissibleAboveOne (f : ℂ → ℂ) : Prop :=
  ∃ c : ℕ → ℂ, DirichletRepresentsAboveOne f c

/-- Canonical coefficient stream of an admissible far-right function.  Its apparent choice is
removed by `dirichletRepresentsAboveOne_unique`. -/
noncomputable def canonicalDirichletCoeff (f : ℂ → ℂ) : ℕ → ℂ := by
  classical
  exact if h : DirichletAdmissibleAboveOne f then Classical.choose h else 0

theorem aboveOneDirichletCoeff_abscissa_le_one {c : ℕ → ℂ}
    (hc : AboveOneDirichletCoeff c) :
    LSeries.abscissaOfAbsConv c ≤ (1 : ℝ) := by
  exact LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable hc.summable

theorem aboveOneDirichletCoeff_abscissa_lt_top {c : ℕ → ℂ}
    (hc : AboveOneDirichletCoeff c) :
    LSeries.abscissaOfAbsConv c < ⊤ :=
  (aboveOneDirichletCoeff_abscissa_le_one hc).trans_lt (EReal.coe_lt_top 1)

/-- Dirichlet coefficients are determined by a function on the far-right real ray. -/
theorem dirichletRepresentsAboveOne_unique {f : ℂ → ℂ} {c d : ℕ → ℂ}
    (hc : DirichletRepresentsAboveOne f c)
    (hd : DirichletRepresentsAboveOne f d) : c = d := by
  funext n
  cases n with
  | zero => exact hc.zero.trans hd.zero.symm
  | succ n =>
      apply LSeries.eq_of_LSeries_eventually_eq
        (aboveOneDirichletCoeff_abscissa_lt_top hc.toAboveOneDirichletCoeff)
        (aboveOneDirichletCoeff_abscissa_lt_top hd.toAboveOneDirichletCoeff)
        _ (Nat.succ_ne_zero n)
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      rw [← hc.eqOn (x : ℂ) (by simpa [rightHalfPlaneOne] using hx),
        ← hd.eqOn (x : ℂ) (by simpa [rightHalfPlaneOne] using hx)]

theorem canonicalDirichletCoeff_represents {f : ℂ → ℂ}
    (hf : DirichletAdmissibleAboveOne f) :
    DirichletRepresentsAboveOne f (canonicalDirichletCoeff f) := by
  rw [canonicalDirichletCoeff, dif_pos hf]
  exact Classical.choose_spec hf

theorem canonicalDirichletCoeff_eq {f : ℂ → ℂ} {c : ℕ → ℂ}
    (hc : DirichletRepresentsAboveOne f c) :
    canonicalDirichletCoeff f = c := by
  exact dirichletRepresentsAboveOne_unique
    (canonicalDirichletCoeff_represents ⟨c, hc⟩) hc

/-- Absolute convergence on every farther-right line makes the represented function analytic on
the whole open Euler half-plane.  This is the normal-convergence consequence used by the card. -/
theorem dirichletRepresentsAboveOne_analyticOnNhd {f : ℂ → ℂ} {c : ℕ → ℂ}
    (hc : DirichletRepresentsAboveOne f c) :
    AnalyticOnNhd ℂ f rightHalfPlaneOne := by
  have hL : AnalyticOnNhd ℂ (LSeries c) rightHalfPlaneOne :=
    (LSeries_analyticOnNhd c).mono (by
      intro s hs
      exact (aboveOneDirichletCoeff_abscissa_le_one hc.toAboveOneDirichletCoeff).trans_lt
        (by exact_mod_cast hs))
  exact hL.congr isOpen_rightHalfPlaneOne fun s hs ↦ (hc.eqOn s hs).symm

/-- Coefficient stream after deleting every index below `N`. -/
def dirichletTail (c : ℕ → ℂ) (N n : ℕ) : ℂ :=
  if N ≤ n then c n else 0

/-- Finite coefficient prefix on `2 <= n < N`. -/
def dirichletPrefixCoeff (c : ℕ → ℂ) (N n : ℕ) : ℂ :=
  if 2 ≤ n ∧ n < N then c n else 0

/-- Literal finite Dirichlet prefix in the recursive extraction formula. -/
def dirichletPrefix (c : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Ico 2 N, c n / (n : ℂ) ^ s

theorem dirichletPrefixCoeff_add_tail {c : ℕ → ℂ}
    (hc : AboveOneDirichletCoeff c) (N : ℕ) :
    dirichletPrefixCoeff c N + dirichletTail c N = c := by
  funext n
  by_cases hnN : n < N
  · by_cases hn2 : 2 ≤ n
    · simp [dirichletPrefixCoeff, dirichletTail, hnN, hn2,
        Nat.not_le_of_lt hnN]
    · have hn : n = 0 ∨ n = 1 := by omega
      rcases hn with rfl | rfl
      · simp [dirichletPrefixCoeff, dirichletTail, hc.zero]
      · simp [dirichletPrefixCoeff, dirichletTail, hc.one]
  · have hNn : N ≤ n := Nat.le_of_not_gt hnN
    simp [dirichletPrefixCoeff, dirichletTail, hnN, hNn]

theorem LSeries_dirichletPrefixCoeff (c : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    LSeries (dirichletPrefixCoeff c N) s = dirichletPrefix c N s := by
  rw [LSeries, tsum_eq_sum (s := Finset.Ico 2 N)]
  · apply Finset.sum_congr rfl
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Ico.mp hn).1
    have hnN : n < N := (Finset.mem_Ico.mp hn).2
    rw [LSeries.term_of_ne_zero (by omega)]
    simp [dirichletPrefixCoeff, hn2, hnN]
  · intro n hn
    have hn' : ¬ (2 ≤ n ∧ n < N) := by
      simpa [Finset.mem_Ico] using hn
    by_cases hn0 : n = 0
    · subst n
      simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn0]
      simp [dirichletPrefixCoeff, hn']

theorem dirichletPrefixCoeff_summable (c : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    LSeriesSummable (dirichletPrefixCoeff c N) s := by
  rw [LSeriesSummable]
  apply summable_of_hasFiniteSupport
  exact (Finset.finite_toSet (Finset.Ico 2 N)).subset (by
    intro n hn
    simp only [Function.mem_support] at hn
    by_contra hmem
    apply hn
    have hn' : ¬ (2 ≤ n ∧ n < N) := by
      simpa [Finset.mem_Ico] using hmem
    by_cases hn0 : n = 0
    · subst n
      simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn0]
      simp [dirichletPrefixCoeff, hn'])

theorem dirichletTail_eventuallyEq (c : ℕ → ℂ) (N : ℕ) :
    dirichletTail c N =ᶠ[atTop] c := by
  filter_upwards [eventually_ge_atTop N] with n hn
  simp [dirichletTail, hn]

theorem dirichletTail_summable {c : ℕ → ℂ}
    (hc : AboveOneDirichletCoeff c) (N : ℕ) {s : ℂ}
    (hs : s ∈ rightHalfPlaneOne) : LSeriesSummable (dirichletTail c N) s := by
  apply (LSeriesSummable_congr' s (dirichletTail_eventuallyEq c N)).mpr
  exact (hc.summable s.re hs).of_re_le_re (by simp)

theorem LSeries_eq_prefix_add_tail {c : ℕ → ℂ}
    (hc : AboveOneDirichletCoeff c) (N : ℕ) {s : ℂ}
    (hs : s ∈ rightHalfPlaneOne) :
    LSeries c s = dirichletPrefix c N s + LSeries (dirichletTail c N) s := by
  have h := LSeries_add (dirichletPrefixCoeff_summable c N s)
    (dirichletTail_summable hc N hs)
  rw [dirichletPrefixCoeff_add_tail hc N, LSeries_dirichletPrefixCoeff] at h
  exact h

/-- Subtracting the recovered finite prefix leaves exactly the coefficient tail. -/
theorem dirichletRepresentsAboveOne_sub_prefix_eq_tail
    {f : ℂ → ℂ} {c : ℕ → ℂ}
    (hc : DirichletRepresentsAboveOne f c) (N : ℕ) {s : ℂ}
    (hs : s ∈ rightHalfPlaneOne) :
    f s - dirichletPrefix c N s = LSeries (dirichletTail c N) s := by
  rw [hc.eqOn s hs, LSeries_eq_prefix_add_tail hc.toAboveOneDirichletCoeff N hs]
  abel

theorem dirichletTail_abscissa_lt_top {c : ℕ → ℂ}
    (hc : AboveOneDirichletCoeff c) (N : ℕ) :
    LSeries.abscissaOfAbsConv (dirichletTail c N) < ⊤ := by
  rw [LSeries.abscissaOfAbsConv_congr' (dirichletTail_eventuallyEq c N)]
  exact aboveOneDirichletCoeff_abscissa_lt_top hc

/-- After deleting indices below `N`, rescaling by `N^x` recovers coefficient `c N`. -/
theorem tendsto_dirichletTail_extraction {c : ℕ → ℂ}
    (hc : AboveOneDirichletCoeff c) {N : ℕ} (hN : 2 ≤ N) :
    Tendsto (fun x : ℝ ↦ (N : ℂ) ^ (x : ℂ) *
      LSeries (dirichletTail c N) x) atTop (nhds (c N)) := by
  have hzero : ∀ m ≤ N - 1, dirichletTail c N m = 0 := by
    intro m hm
    rw [dirichletTail, if_neg]
    omega
  have ht := LSeries.tendsto_cpow_mul_atTop hzero
    (dirichletTail_abscissa_lt_top hc N)
  have hbase : ((N - 1 : ℕ) : ℂ) + 1 = (N : ℂ) := by
    exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ N)
  rw [hbase] at ht
  simpa [dirichletTail, Nat.sub_add_cancel (by omega : 1 ≤ N)] using ht

/-- Exact recursive extraction formula `(3)` from the card, simultaneously for every admissible
function, coefficient stream, and `N >= 2`. -/
theorem tendsto_dirichlet_recursive_extraction
    {f : ℂ → ℂ} {c : ℕ → ℂ}
    (hc : DirichletRepresentsAboveOne f c) {N : ℕ} (hN : 2 ≤ N) :
    Tendsto (fun x : ℝ ↦ (N : ℂ) ^ (x : ℂ) *
      (f x - dirichletPrefix c N x)) atTop (nhds (c N)) := by
  apply (tendsto_dirichletTail_extraction hc.toAboveOneDirichletCoeff hN).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [dirichletRepresentsAboveOne_sub_prefix_eq_tail hc N
    (by simpa [rightHalfPlaneOne] using hx)]

/-- Full continuation-and-jet datum.  `filledGerm` retains the pole residue at zero and agrees on
the punctured germ with `x * flux (rho + x)`; hence `jet 0` is not silently forced to zero. -/
structure CompletedSourceJetDatum (rho : ℂ) where
  domain : Set ℂ
  domain_open : IsOpen domain
  domain_connected : IsConnected domain
  rho_mem : rho ∈ domain
  rightHalfPlane_mem : rightHalfPlaneOne ⊆ domain
  flux : ℂ → ℂ
  flux_meromorphic : MeromorphicOn flux domain
  filledGerm : ℂ → ℂ
  filledGerm_analytic : AnalyticAt ℂ filledGerm 0
  filledGerm_eq : filledGerm =ᶠ[nhdsWithin 0 {0}ᶜ]
    fun x ↦ x * flux (rho + x)
  jet : ℕ → ℂ
  jet_eq : ∀ n, jet n = iteratedDeriv n filledGerm 0 / n.factorial

/-- Prime candidate obtained by subtracting `B_arch = -logDeriv archFactor`. -/
def CompletedSourceJetDatum.primePart {rho : ℂ}
    (d : CompletedSourceJetDatum rho) (s : ℂ) : ℂ :=
  d.flux s + logDeriv archFactor s

/-- Adding the fixed archimedean channel back recovers the supplied completed continuation. -/
theorem CompletedSourceJetDatum.primePart_add_archimedean {rho : ℂ}
    (d : CompletedSourceJetDatum rho) (s : ℂ) :
    d.primePart s - logDeriv archFactor s = d.flux s := by
  simp [CompletedSourceJetDatum.primePart]

/-- Pure jet-space compatibility: admissibility and all quadratic Euler-ray equations are imposed
on the canonical coefficient stream of the analytically continued jet. -/
def CompletedSourceEulerCompatible {rho : ℂ}
    (d : CompletedSourceJetDatum rho) : Prop :=
  DirichletAdmissibleAboveOne d.primePart ∧
    DegreeOneEulerQuadraticCompatible (canonicalDirichletCoeff d.primePart)

/-- A prime parameter field represents the far-right prime part of the same completed
continuation, whose filled local Taylor jet is already part of `d`. -/
def DegreeOneEulerSourceRepresents {rho : ℂ}
    (d : CompletedSourceJetDatum rho) (a : Nat.Primes → ℂ) : Prop :=
  DirichletRepresentsAboveOne d.primePart (degreeOneEulerPrimeFluxCoeff a)

/-- **Exact completed source infinite-jet image classification.**  Euler compatibility of the
canonically extracted stream is equivalent to existence of exactly one prime-indexed degree-one
Euler source giving the far-right continuation and therefore the same residue-filled local jet. -/
theorem completedSourceEulerCompatible_iff_existsUnique_primeParameter
    {rho : ℂ} (d : CompletedSourceJetDatum rho) :
    CompletedSourceEulerCompatible d ↔
      ∃! a : Nat.Primes → ℂ, DegreeOneEulerSourceRepresents d a := by
  constructor
  · rintro ⟨hadm, hquad⟩
    have hc := canonicalDirichletCoeff_represents hadm
    obtain ⟨a, ha, hauniq⟩ :=
      (degreeOneEulerQuadraticCompatible_iff_existsUnique_primeParameter _).mp hquad
    refine ⟨a, ?_, ?_⟩
    · change DirichletRepresentsAboveOne d.primePart
        (degreeOneEulerPrimeFluxCoeff a)
      rw [ha]
      exact hc
    · intro b hb
      apply hauniq b
      exact dirichletRepresentsAboveOne_unique hb hc
  · rintro ⟨a, ha, _⟩
    refine ⟨⟨degreeOneEulerPrimeFluxCoeff a, ha⟩, ?_⟩
    rw [canonicalDirichletCoeff_eq ha]
    exact degreeOneEulerQuadraticCompatible_iff_existsUnique_primeParameter _ |>.mpr
      ⟨a, rfl, fun b hb ↦ degreeOneEulerPrimeFluxCoeff_injective hb⟩

/-- Fixed zeta/von-Mangoldt sublocus inside the classified source image. -/
def CompletedSourceZetaSublocus {rho : ℂ}
    (d : CompletedSourceJetDatum rho) : Prop :=
  DirichletRepresentsAboveOne d.primePart
    (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ))

theorem degreeOneEulerPrimeFluxCoeff_one_eq_vonMangoldt :
    degreeOneEulerPrimeFluxCoeff (fun _ ↦ 1) =
      fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ) := by
  rw [degreeOneEulerPrimeFluxCoeff]
  calc
    degreeOneEulerFluxCoeff
        (fun n ↦ if hn : n.Prime then (1 : ℂ) else 0) =
        degreeOneEulerFluxCoeff (fun _ ↦ 1) := by
      apply degreeOneEulerFluxCoeff_eq_of_eq_on_primes
      intro p hp
      simp [hp]
    _ = fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ) := by
      funext n
      exact degreeOneEulerFluxCoeff_one_eq_vonMangoldt n

/-- Zeta is exactly the unit point `a_p = 1` of the prime parameter space. -/
theorem completedSourceZetaSublocus_iff_unitPrimeParameter
    {rho : ℂ} (d : CompletedSourceJetDatum rho) :
    CompletedSourceZetaSublocus d ↔
      DegreeOneEulerSourceRepresents d (fun _ ↦ 1) := by
  rw [CompletedSourceZetaSublocus, DegreeOneEulerSourceRepresents]
  rw [degreeOneEulerPrimeFluxCoeff_one_eq_vonMangoldt]

/-- Equivalent choice-free description of the zeta sublocus via the canonical stream. -/
theorem completedSourceZetaSublocus_canonicalCoeff
    {rho : ℂ} (d : CompletedSourceJetDatum rho) :
    CompletedSourceZetaSublocus d ↔
      DirichletAdmissibleAboveOne d.primePart ∧
      canonicalDirichletCoeff d.primePart =
        fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ) := by
  constructor
  · intro h
    exact ⟨⟨_, h⟩, canonicalDirichletCoeff_eq h⟩
  · rintro ⟨hadm, heq⟩
    change DirichletRepresentsAboveOne d.primePart
      (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ))
    simpa [heq] using canonicalDirichletCoeff_represents hadm

end RHTower
