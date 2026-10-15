import GaloisForLFunctions.RHTower.EvenSectorFullPositivity
import GaloisForLFunctions.RHTower.PrimeBlindNodeCriticality

/-!
# Even prime-blind positivity is node-critical

For a set `S` of integers let `PrimeBlindPositiveEvenOn S` say that the pole and archimedean part
`A(k) = weilArchRe k` of the Weil functional is nonnegative on every nonnegative combination of
autocorrelations of EVEN `C²` compactly supported tests whose values vanish at `±log n` for every
`n ∈ S`, `n ≥ 2`.

**Theorem** (`primeBlindPositiveEvenOn_iff`).  For every `S ⊆ ℕ`,
`PrimeBlindPositiveEvenOn S ↔ RH ∧ (every prime power lies in S)`.

**Unique repair** (`repairedBlindPositiveEven_iff`).  Restoring the nodes off `S` with weights `w`
keeps the Weil functional nonnegative on the `S`-blind even cone exactly when RH holds and `w = Λ`
at every restored node.  In particular (`riemannHypothesis_iff_singlePrimeWeilPositiveEven`) RH
holds iff the archimedean place together with the Euler factor at one prime `p` is nonnegative on
the even combinations that are blind at every node that is not a power of `p`.

Proof.  Two-sided feasibility on the coordinates in `S` (`exists_of_nonneg_on_null_cone`), with the
even tests `evenPlus j`, `evenMinus j` reaching each node with either sign, produces a weight that
is Weil-positive on even tests and has the prescribed values off `S`.  Even Weil positivity forces
that weight to be `Λ` and RH (`weilPositiveEvenAt_one_iff`).
-/

open Finsupp Zeta23
open scoped Classical

noncomputable section

namespace RHTower.EvenSector

open WeilOneSided WeilSpectral

/-- **Even prime-blind positivity on the nodes `S`.** -/
def PrimeBlindPositiveEvenOn (S : Set ℕ) : Prop :=
  ∀ c : EvenWeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → n ∈ S → (c.sum fun f t => t * logValue f.1.1 n) = 0) →
    0 ≤ c.sum fun f t => t * weilArchRe (EF.weilTest f.1.1 f.1.1)

theorem logVectorOn_of_single (S : Set ℕ) {f : WeilTestFn} {j : LogIndex} {a : ℝ}
    (hf : logVector f = Finsupp.single j a) (hj : (j : ℕ) ∈ S) :
    logVectorOn S f = Finsupp.single ⟨j, hj⟩ a := by
  ext b
  rw [logVectorOn, Finsupp.subtypeDomain_apply, hf, Finsupp.single_apply, Finsupp.single_apply]
  by_cases h : j = b.1
  · rw [if_pos h, if_pos (Subtype.ext h)]
  · rw [if_neg h, if_neg fun h' => h (congrArg Subtype.val h')]

theorem linearCombination_logVectorOn_even_apply (S : Set ℕ) (c : EvenWeilTestFn →₀ ℝ)
    (a : {j : LogIndex // (j : ℕ) ∈ S}) :
    linearCombination ℝ (fun f : EvenWeilTestFn => logVectorOn S f.1) c a =
      c.sum fun f t => t * logValue f.1.1 a.1 := by
  rw [linearCombination_apply, Finsupp.sum_apply]
  simp [logVectorOn, logVector_apply]

theorem re_weilFullFunctional_weilTest_eq (lam : ℕ → ℝ) (f : WeilTestFn) :
    (weilFullFunctional lam (EF.weilTest f.1 f.1)).re =
      weilArchRe (EF.weilTest f.1 f.1) -
        linearCombination ℝ (fun j : LogIndex => lam j) (logVector f) := by
  rw [← weilPoleWeightFunctional_one, re_weilPoleWeightFunctional_eq]
  simp [poleWeightArchRe]

/-- The combined log vector of an even combination, evaluated at a node. -/
theorem sum_smul_logVector_apply (c : EvenWeilTestFn →₀ ℝ) (j : LogIndex) :
    (c.sum fun f t => t • logVector f.1) j = c.sum fun f t => t * logValue f.1.1 j := by
  rw [Finsupp.sum_apply]
  refine Finsupp.sum_congr fun f _ => ?_
  rw [Finsupp.smul_apply, logVector_apply, smul_eq_mul]

/-- Pairing a weight with an even combination, through the combined log vector. -/
theorem sum_mul_linearCombination_logVector (c : EvenWeilTestFn →₀ ℝ) (lam : LogIndex → ℝ) :
    (c.sum fun f t => t * linearCombination ℝ lam (logVector f.1)) =
      linearCombination ℝ lam (c.sum fun f t => t • logVector f.1) := by
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun f _ => ?_
  rw [map_smul, smul_eq_mul]

theorem linearCombination_eq_of_agree {v : LogIndex →₀ ℝ} {a b : LogIndex → ℝ}
    (h : ∀ j, v j = 0 ∨ a j = b j) : linearCombination ℝ a v = linearCombination ℝ b v := by
  rw [linearCombination_apply, linearCombination_apply]
  refine Finsupp.sum_congr fun j _ => ?_
  rcases h j with h | h
  · rw [h, zero_smul, zero_smul]
  · rw [h]

/-- An even-positive weight that agrees with `w` off `S` makes the `S`-blind even cone
nonnegative for the Weil functional with weights `w` off `S`. -/
theorem sum_nonneg_of_weilPositiveEvenAt {S : Set ℕ} {lam w : ℕ → ℝ}
    (h : WeilPositiveEvenAt 1 lam) (hS : ∀ n, 2 ≤ n → n ∉ S → lam n = w n)
    {c : EvenWeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f)
    (hnull : ∀ n : ℕ, 2 ≤ n → n ∈ S → (c.sum fun f t => t * logValue f.1.1 n) = 0) :
    0 ≤ c.sum fun f t => t * (weilFullFunctional (offNodes S w) (EF.weilTest f.1.1 f.1.1)).re := by
  have h1 : 0 ≤ c.sum fun f t => t * (weilFullFunctional lam (EF.weilTest f.1.1 f.1.1)).re :=
    Finsupp.sum_nonneg fun f _ => mul_nonneg (hc f) (by
      have := h f.1.1 f.1.2.1 f.1.2.2 f.2
      rwa [weilPoleWeightFunctional_one] at this)
  have e : ∀ (u : ℕ → ℝ), (c.sum fun f t => t * (weilFullFunctional u (EF.weilTest f.1.1 f.1.1)).re)
      = (c.sum fun f t => t * weilArchRe (EF.weilTest f.1.1 f.1.1)) -
        linearCombination ℝ (fun j : LogIndex => u j) (c.sum fun f t => t • logVector f.1) := by
    intro u
    rw [← sum_mul_linearCombination_logVector, ← Finsupp.sum_sub]
    refine Finsupp.sum_congr fun f _ => ?_
    rw [re_weilFullFunctional_weilTest_eq]
    ring
  rw [e] at h1 ⊢
  rwa [linearCombination_eq_of_agree (b := fun j : LogIndex => lam j) fun j => by
    by_cases hj : (j : ℕ) ∈ S
    · left; rw [sum_smul_logVector_apply, hnull j j.2 hj]
    · right; simp only [offNodes, hj, if_false]; exact (hS j j.2 hj).symm]

/-- **Even prime-blind positivity on `S`, or any repair of it, produces an even-positive weight.**
If the Weil functional with weights `w` off `S` is nonnegative on the `S`-blind even cone, some
weight is Weil-positive on every even test and equals `w` off `S`. -/
theorem exists_weilPositiveEvenAt_of_repaired {S : Set ℕ} {w : ℕ → ℝ}
    (h : ∀ c : EvenWeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
      (∀ n : ℕ, 2 ≤ n → n ∈ S → (c.sum fun f t => t * logValue f.1.1 n) = 0) →
      0 ≤ c.sum fun f t => t * (weilFullFunctional (offNodes S w) (EF.weilTest f.1.1 f.1.1)).re) :
    ∃ lam : ℕ → ℝ, WeilPositiveEvenAt 1 lam ∧ ∀ n, 2 ≤ n → n ∉ S → lam n = w n := by
  have hsqrt : ∀ j : LogIndex, 0 < Real.sqrt (j : ℕ) := fun j =>
    Real.sqrt_pos.mpr (by exact_mod_cast (lt_of_lt_of_le two_pos j.2))
  obtain ⟨lam', hlam'⟩ := GaloisForLFunctions.HTGeometry.exists_of_nonneg_on_null_cone
    (fun f : EvenWeilTestFn => logVectorOn S f.1)
    (fun f : EvenWeilTestFn => (weilFullFunctional (offNodes S w) (EF.weilTest f.1.1 f.1.1)).re)
    (fun a => ⟨evenMinus a.1, _, div_pos (mul_pos two_pos (integral_oddProfile_sq_pos a.1))
      (hsqrt a.1), logVectorOn_of_single S (logVector_evenMinus a.1) a.2⟩)
    (fun a => ⟨evenPlus a.1, _, div_pos (mul_pos two_pos (integral_evenProfile_sq_pos a.1))
      (hsqrt a.1), logVectorOn_of_single S (logVector_evenPlus a.1) a.2⟩)
    (fun c hc hnull => by
      rw [linearCombination_apply]
      simp only [smul_eq_mul]
      refine h c hc fun n hn hnS => ?_
      rw [← linearCombination_logVectorOn_even_apply S c ⟨⟨n, hn⟩, hnS⟩, hnull]
      rfl)
  set lamL : LogIndex → ℝ :=
    fun j => (if hj : (j : ℕ) ∈ S then lam' ⟨j, hj⟩ else 0) + offNodes S w j with hlamL
  refine ⟨fun n => if hn : 2 ≤ n then lamL ⟨n, hn⟩ else 0, fun f hf hfc hev => ?_,
    fun n hn hnS => ?_⟩
  · rw [weilPoleWeightFunctional_one]
    have e : (fun j : LogIndex => (fun n => if hn : 2 ≤ n then lamL ⟨n, hn⟩ else 0) (j : ℕ)) =
        lamL := funext fun j => by simp [j.2]
    rw [re_weilFullFunctional_weilTest_eq (f := ⟨f, hf, hfc⟩), e, hlamL,
      linearCombination_coeff_add, linearCombination_extendOn]
    have h1 := hlam' ⟨⟨f, hf, hfc⟩, hev⟩
    rw [re_weilFullFunctional_weilTest_eq] at h1
    linarith
  · simp [hlamL, offNodes, hn, hnS]

/-- **Node criticality on the even cone.** -/
theorem primeBlindPositiveEvenOn_iff {S : Set ℕ} :
    PrimeBlindPositiveEvenOn S ↔
      RiemannHypothesis ∧ ∀ n, 2 ≤ n → ArithmeticFunction.vonMangoldt n ≠ 0 → n ∈ S := by
  have hoff : ∀ f : WeilTestFn, (weilFullFunctional (offNodes S 0) (EF.weilTest f.1 f.1)).re =
      weilArchRe (EF.weilTest f.1 f.1) := fun f => by
    rw [re_weilFullFunctional_weilTest_eq]
    have : (fun j : LogIndex => offNodes S 0 (j : ℕ)) = 0 := funext fun j => by
      simp [offNodes]
    rw [this, linearCombination_apply]
    simp
  constructor
  · intro h
    obtain ⟨lam, hW, hS⟩ := exists_weilPositiveEvenAt_of_repaired (S := S) (w := 0)
      fun c hc hnull => by simp only [hoff]; exact h c hc hnull
    obtain ⟨hRH, hΛ⟩ := weilPositiveEvenAt_one_iff.mp hW
    refine ⟨hRH, fun n hn hΛn => ?_⟩
    by_contra hnS
    exact hΛn (by rw [← hΛ n hn, hS n hn hnS]; rfl)
  · rintro ⟨hRH, hS⟩ c hc hnull
    have h := sum_nonneg_of_weilPositiveEvenAt (S := S) (w := 0)
      (weilPositiveEvenAt_one_iff.mpr ⟨hRH, fun _ _ => rfl⟩) (fun n hn hnS => by
        by_contra hne
        exact hnS (hS n hn hne)) hc hnull
    simpa only [hoff] using h

/-- Blindness at the prime powers alone, on even tests, already characterizes RH. -/
theorem riemannHypothesis_iff_primeBlindPositiveEvenOn_primePowers :
    RiemannHypothesis ↔ PrimeBlindPositiveEvenOn {n | IsPrimePow n} := by
  rw [primeBlindPositiveEvenOn_iff]
  exact ⟨fun h => ⟨h, fun n _ hn => ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hn⟩,
    fun h => h.1⟩

/-- **Deleting one prime-power node breaks even prime-blind positivity**, unconditionally. -/
theorem not_primeBlindPositiveEvenOn_of_primePower_not_mem {S : Set ℕ} {m : ℕ}
    (hm : IsPrimePow m) (hmS : m ∉ S) : ¬ PrimeBlindPositiveEvenOn S := fun h =>
  hmS ((primeBlindPositiveEvenOn_iff.mp h).2 m hm.two_le
    (ArithmeticFunction.vonMangoldt_ne_zero_iff.mpr hm))

/-! ## Repairing deleted nodes on the even cone -/

/-- **Repaired even prime-blind positivity.** -/
def RepairedBlindPositiveEven (S : Set ℕ) (w : ℕ → ℝ) : Prop :=
  ∀ c : EvenWeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → n ∈ S → (c.sum fun f t => t * logValue f.1.1 n) = 0) →
    0 ≤ c.sum fun f t => t * (weilFullFunctional (offNodes S w) (EF.weilTest f.1.1 f.1.1)).re

/-- **Unique repair on the even cone.** -/
theorem repairedBlindPositiveEven_iff {S : Set ℕ} {w : ℕ → ℝ} :
    RepairedBlindPositiveEven S w ↔
      RiemannHypothesis ∧ ∀ n, 2 ≤ n → n ∉ S → w n = ArithmeticFunction.vonMangoldt n := by
  constructor
  · intro h
    obtain ⟨lam, hW, hS⟩ := exists_weilPositiveEvenAt_of_repaired h
    obtain ⟨hRH, hΛ⟩ := weilPositiveEvenAt_one_iff.mp hW
    exact ⟨hRH, fun n hn hnS => by rw [← hS n hn hnS, hΛ n hn]⟩
  · rintro ⟨hRH, hw⟩ c hc hnull
    exact sum_nonneg_of_weilPositiveEvenAt
      (weilPositiveEvenAt_one_iff.mpr ⟨hRH, fun _ _ => rfl⟩)
      (fun n hn hnS => (hw n hn hnS).symm) hc hnull

/-- **An interpolating family of even RH criteria.** -/
theorem riemannHypothesis_iff_repairedBlindPositiveEven_vonMangoldt (S : Set ℕ) :
    RiemannHypothesis ↔
      RepairedBlindPositiveEven S fun n => (ArithmeticFunction.vonMangoldt n : ℝ) :=
  ⟨fun h => repairedBlindPositiveEven_iff.mpr ⟨h, fun _ _ _ => rfl⟩,
    fun h => (repairedBlindPositiveEven_iff.mp h).1⟩

/-- **The single-prime Weil criterion on even tests.**  RH holds iff the archimedean part together
with the Euler factor at one prime `p` is nonnegative on the even combinations that are blind at
every node `n ≥ 2` that is not a power of `p`. -/
theorem riemannHypothesis_iff_singlePrimeWeilPositiveEven (p : ℕ) :
    RiemannHypothesis ↔
      RepairedBlindPositiveEven {n | ∀ k : ℕ, n ≠ p ^ (k + 1)}
        fun n => (ArithmeticFunction.vonMangoldt n : ℝ) :=
  riemannHypothesis_iff_repairedBlindPositiveEven_vonMangoldt _

end RHTower.EvenSector

end
