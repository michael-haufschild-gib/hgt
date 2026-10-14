import GaloisForLFunctions.RHTower.WeilFullConeOneSidedCriterion

/-!
# Compactness of the Weil cone and the Krein–Milman reduction of RH

Index the weights of full-cone Weil positivity by `n ≥ 2` (`LogIndex`) and put

`weilCone = {μ : LogIndex → ℝ | WeilPositiveFull (extendLog μ)}`.

* `abs_le_coordBound_of_mem_weilCone`: every coordinate is bounded on the cone. The pair tests
  `h ± h(· − log j)` built from narrow bumps have `ℓ`-vector `±w_j e_j` with `w_j > 0`
  (`logVector_pairTestFn`), so Weil positivity gives `±w_j μ j ≤ A_±(j)`.
* `isClosed_weilCone`, `convex_weilCone`: each test imposes one closed half-space, depending on
  finitely many coordinates.
* `isCompact_weilCone`: by Tychonoff the cone is compact in the product topology.
* `riemannHypothesis_of_extremePoints_weilCone`: if the cone is nonempty and every extreme point is
  `Λ`, the Riemann hypothesis holds. By Krein–Milman a nonempty compact convex set has an extreme
  point; that point is `Λ`, so `Λ` is full-cone Weil-positive.
* `riemannHypothesis_of_primeBlindPositive_of_extremePoints`: the same with nonemptiness supplied by
  prime-blind positivity (`exists_weilPositiveFull_iff_primeBlindPositive`).
-/

open Set Finsupp
open Zeta23

noncomputable section

namespace RHTower.WeilOneSided

/-- Extend weights on `n ≥ 2` by zero to all of `ℕ`. -/
def extendLog (μ : LogIndex → ℝ) (n : ℕ) : ℝ := if h : 2 ≤ n then μ ⟨n, h⟩ else 0

theorem extendLog_coe (μ : LogIndex → ℝ) (j : LogIndex) : extendLog μ j = μ j := by
  simp [extendLog, j.2]

/-- The full Weil cone, indexed by `n ≥ 2`. -/
def weilCone : Set (LogIndex → ℝ) := {μ | WeilPositiveFull (extendLog μ)}

/-- The Weil functional of `extendLog μ` on a test, as archimedean part minus a linear form. -/
theorem re_weilFullFunctional_extendLog (μ : LogIndex → ℝ) (f : WeilTestFn) :
    (weilFullFunctional (extendLog μ) (EF.weilTest f.1 f.1)).re =
      weilArchRe (EF.weilTest f.1 f.1) - linearCombination ℝ μ (logVector f) := by
  have h : (fun j : LogIndex => extendLog μ j) = μ := funext fun j => extendLog_coe μ j
  rw [re_weilFullFunctional_eq, h]

theorem mem_weilCone_iff (μ : LogIndex → ℝ) :
    μ ∈ weilCone ↔ ∀ f : WeilTestFn,
      linearCombination ℝ μ (logVector f) ≤ weilArchRe (EF.weilTest f.1 f.1) := by
  constructor
  · intro h f
    have := h f.1 f.2.1 f.2.2
    rw [re_weilFullFunctional_extendLog μ f] at this
    linarith
  · intro h f hf hfc
    rw [re_weilFullFunctional_extendLog μ ⟨f, hf, hfc⟩]
    linarith [h ⟨f, hf, hfc⟩]

/-- The linear form of a test is a finite sum of coordinates, hence continuous. -/
theorem continuous_linearCombination_logVector (f : WeilTestFn) :
    Continuous fun μ : LogIndex → ℝ => linearCombination ℝ μ (logVector f) := by
  have h : (fun μ : LogIndex → ℝ => linearCombination ℝ μ (logVector f)) =
      fun μ => ∑ j ∈ (logVector f).support, logVector f j * μ j := by
    funext μ
    rw [linearCombination_apply, Finsupp.sum]
    rfl
  rw [h]
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)

theorem isClosed_weilCone : IsClosed weilCone := by
  have h : weilCone = ⋂ f : WeilTestFn,
      {μ | linearCombination ℝ μ (logVector f) ≤ weilArchRe (EF.weilTest f.1 f.1)} := by
    ext μ
    rw [mem_iInter, mem_weilCone_iff]
    rfl
  rw [h]
  exact isClosed_iInter fun f =>
    isClosed_le (continuous_linearCombination_logVector f) continuous_const

theorem linearCombination_add_smul (μ ν : LogIndex → ℝ) (a b : ℝ) (l : LogIndex →₀ ℝ) :
    linearCombination ℝ (a • μ + b • ν) l =
      a * linearCombination ℝ μ l + b * linearCombination ℝ ν l := by
  simp only [linearCombination_apply, Finsupp.sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem convex_weilCone : Convex ℝ weilCone := by
  intro μ hμ ν hν a b ha hb hab
  rw [mem_weilCone_iff] at hμ hν ⊢
  intro f
  rw [linearCombination_add_smul]
  have h1 := mul_le_mul_of_nonneg_left (hμ f) ha
  have h2 := mul_le_mul_of_nonneg_left (hν f) hb
  have : weilArchRe (EF.weilTest f.1 f.1) =
      a * weilArchRe (EF.weilTest f.1 f.1) + b * weilArchRe (EF.weilTest f.1 f.1) := by
    rw [← add_mul, hab, one_mul]
  linarith

/-- The positive weight of the pair test at `j`. -/
def pairWeight (j : LogIndex) : ℝ := 2 * (∫ t, (narrowBump j t) ^ 2) / Real.sqrt j

theorem linearCombination_logVector_pairTestFn (μ : LogIndex → ℝ) (j : LogIndex) (σ : ℝ) :
    linearCombination ℝ μ (logVector (pairTestFn j σ)) = σ * pairWeight j * μ j := by
  rw [logVector_pairTestFn, linearCombination_single, smul_eq_mul, pairWeight]
  ring

/-- The coordinate bound: the larger archimedean energy of the two pair tests over the weight. -/
def coordBound (j : LogIndex) : ℝ :=
  max (weilArchRe (EF.weilTest (pairTestFn j 1).1 (pairTestFn j 1).1))
      (weilArchRe (EF.weilTest (pairTestFn j (-1)).1 (pairTestFn j (-1)).1)) / pairWeight j

/-- **Every coordinate is bounded on the Weil cone.** -/
theorem abs_le_coordBound_of_mem_weilCone {μ : LogIndex → ℝ} (hμ : μ ∈ weilCone)
    (j : LogIndex) : |μ j| ≤ coordBound j := by
  rw [mem_weilCone_iff] at hμ
  have hw := pairTest_weight_pos j
  change 0 < pairWeight j at hw
  have hp := hμ (pairTestFn j 1)
  have hm := hμ (pairTestFn j (-1))
  rw [linearCombination_logVector_pairTestFn] at hp hm
  set Ap := weilArchRe (EF.weilTest (pairTestFn j 1).1 (pairTestFn j 1).1)
  set Am := weilArchRe (EF.weilTest (pairTestFn j (-1)).1 (pairTestFn j (-1)).1)
  rw [coordBound, le_div_iff₀ hw]
  have h1 : pairWeight j * μ j ≤ max Ap Am := le_trans (by linarith) (le_max_left _ _)
  have h2 : -(pairWeight j * μ j) ≤ max Ap Am := le_trans (by linarith) (le_max_right _ _)
  calc |μ j| * pairWeight j = |pairWeight j * μ j| := by
        rw [abs_mul, abs_of_pos hw, mul_comm]
    _ ≤ max Ap Am := abs_le.mpr ⟨by linarith, h1⟩

/-- **The Weil cone is compact** in the product topology. -/
theorem isCompact_weilCone : IsCompact weilCone := by
  have hbox : IsCompact (univ.pi fun j : LogIndex => Icc (-coordBound j) (coordBound j)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  refine hbox.of_isClosed_subset isClosed_weilCone fun μ hμ => ?_
  rw [mem_univ_pi]
  intro j
  exact abs_le.mp (abs_le_coordBound_of_mem_weilCone hμ j)

/-- Weil positivity only sees the weights at `n ≥ 2`. -/
theorem weilPositiveFull_congr {lam lam' : ℕ → ℝ} (h : ∀ n, 2 ≤ n → lam n = lam' n)
    (hW : WeilPositiveFull lam) : WeilPositiveFull lam' := by
  intro f hf hfc
  rw [← weilFullFunctional_congr h]
  exact hW f hf hfc

theorem mem_weilCone_of_weilPositiveFull {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    (fun j : LogIndex => lam j) ∈ weilCone :=
  weilPositiveFull_congr (fun n hn => by simp [extendLog, hn]) hW

/-- **Krein–Milman reduction.** If the Weil cone is nonempty and every extreme point of it is the
von Mangoldt function, the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_extremePoints_weilCone (hne : weilCone.Nonempty)
    (hext : ∀ μ ∈ extremePoints ℝ weilCone, ∀ j : LogIndex,
      μ j = (ArithmeticFunction.vonMangoldt j : ℝ)) :
    RiemannHypothesis := by
  obtain ⟨μ, hμ⟩ := isCompact_weilCone.extremePoints_nonempty hne
  have hmem : μ ∈ weilCone := extremePoints_subset hμ
  refine riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr
    (weilPositiveFull_congr (fun n hn => ?_) hmem)
  simp only [extendLog, dif_pos hn]
  exact hext μ hμ ⟨n, hn⟩

/-- **Prime-blind positivity plus extreme-point rigidity gives RH.** -/
theorem riemannHypothesis_of_primeBlindPositive_of_extremePoints (hP : PrimeBlindPositive)
    (hext : ∀ μ ∈ extremePoints ℝ weilCone, ∀ j : LogIndex,
      μ j = (ArithmeticFunction.vonMangoldt j : ℝ)) :
    RiemannHypothesis := by
  obtain ⟨lam, hW⟩ := exists_weilPositiveFull_iff_primeBlindPositive.mpr hP
  exact riemannHypothesis_of_extremePoints_weilCone ⟨_, mem_weilCone_of_weilPositiveFull hW⟩ hext

/-- Under RH the cone contains `Λ`. -/
theorem vonMangoldt_mem_weilCone_of_riemannHypothesis (hRH : RiemannHypothesis) :
    (fun j : LogIndex => (ArithmeticFunction.vonMangoldt j : ℝ)) ∈ weilCone :=
  mem_weilCone_of_weilPositiveFull (riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH)

end RHTower.WeilOneSided

end
