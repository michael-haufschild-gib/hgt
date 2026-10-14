import GaloisForLFunctions.RHTower.WeilConeUniquenessUnconditional

/-!
# Prime-blind positivity is node-critical

For a set `S` of integers let `PrimeBlindPositiveOn S` say that the pole and archimedean part
`A(k) = weilArchRe k` of the Weil functional is nonnegative on every nonnegative combination
`Σ c_f k_f` of autocorrelations `k_f = f ⋆ f̃` of `C²` compactly supported tests whose symmetric
values vanish at `±log n` for every `n ∈ S`, `n ≥ 2` (`PrimeBlindPositive` is the case `S = ℕ`).

**Theorem** (`primeBlindPositiveOn_iff`).  For every `S ⊆ ℕ`,

`PrimeBlindPositiveOn S ↔ RH ∧ (every prime power lies in S)`.

So the blindness conditions at the integers that are not prime powers can be dropped, while dropping
the condition at a single prime power `p^k` makes the statement false, unconditionally
(`not_primeBlindPositiveOn_of_primePower_not_mem`).  Equivalently
(`exists_negative_arch_of_primePower_node_deleted`): for every prime power `m` there is a
nonnegative combination of autocorrelations vanishing at `±log n` for every `n ≥ 2`, `n ≠ m`, whose
pole and archimedean part is negative.

Proof.
* `PrimeBlindPositiveOn S` holds iff some full-cone Weil-positive weight vanishes at every `n ∉ S`
  (`exists_weilPositiveFull_of_primeBlindPositiveOn`).  This is the two-sided feasibility theorem
  `HTGeometry.exists_of_nonneg_on_null_cone` for the log vectors restricted to `S`.  The pair tests
  `h ± h(· − log j)` reach every coordinate with both signs.
* Every full-cone Weil-positive weight is `Λ` on `n ≥ 2` (`eq_vonMangoldt_of_weilPositiveFull`, the
  twisted arc minimum principle).
* Hence `PrimeBlindPositiveOn S` holds iff `Λ` is Weil-positive (RH) and `Λ(n) = 0` for `n ∉ S`.

**Positive survivor: unique repair** (`repairedBlindPositive_iff`).  Restoring the deleted nodes
`n ∉ S` with weights `w` (the Weil functional with `w` off `S`, on the `S`-blind cone) keeps
positivity exactly when RH holds and `w(n) = Λ(n)` at every deleted node.  The archimedean place
determines the von Mangoldt weight of every node it is asked to repair.

**Interpolating criteria** (`riemannHypothesis_iff_repairedBlindPositive_vonMangoldt`).  For every node
set `S`, RH holds iff the Weil functional with weights `Λ` off `S` is nonnegative on the `S`-blind
cone.  This runs from Weil's criterion (`S = ∅`) to prime-blind positivity (`S = ℕ`) and contains the
single-prime criterion `riemannHypothesis_iff_singlePrimeWeilPositive`: the archimedean place plus the
Euler factor at one prime `p`, on the combinations blind at every node that is not a power of `p`.
-/

open Finsupp Zeta23
open scoped Classical

namespace RHTower.WeilOneSided

noncomputable section

/-- **Prime-blind positivity on the nodes `S`.** -/
def PrimeBlindPositiveOn (S : Set ℕ) : Prop :=
  ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → n ∈ S → (c.sum fun f t => t * logValue f.1 n) = 0) →
    0 ≤ c.sum fun f t => t * weilArchRe (EF.weilTest f.1 f.1)

/-- The log vector restricted to the nodes in `S`. -/
def logVectorOn (S : Set ℕ) (f : WeilTestFn) : {j : LogIndex // (j : ℕ) ∈ S} →₀ ℝ :=
  (logVector f).subtypeDomain fun j : LogIndex => (j : ℕ) ∈ S

theorem linearCombination_logVectorOn_apply (S : Set ℕ) (c : WeilTestFn →₀ ℝ)
    (a : {j : LogIndex // (j : ℕ) ∈ S}) :
    linearCombination ℝ (logVectorOn S) c a = c.sum fun f t => t * logValue f.1 a.1 := by
  rw [linearCombination_apply, Finsupp.sum_apply]
  simp [logVectorOn, logVector_apply]

theorem logVectorOn_pairTestFn (S : Set ℕ) (j : LogIndex) (hj : (j : ℕ) ∈ S) (σ : ℝ) :
    logVectorOn S (pairTestFn j σ) =
      Finsupp.single ⟨j, hj⟩ (2 * σ * (∫ t, (narrowBump j t) ^ 2) / Real.sqrt j) := by
  ext a
  rw [logVectorOn, Finsupp.subtypeDomain_apply, logVector_pairTestFn, Finsupp.single_apply,
    Finsupp.single_apply]
  by_cases h : j = a.1
  · rw [if_pos h, if_pos (Subtype.ext h)]
  · rw [if_neg h, if_neg fun h' => h (congrArg Subtype.val h')]

/-- A full-cone Weil-positive weight vanishing off `S` gives prime-blind positivity on `S`. -/
theorem primeBlindPositiveOn_of_weilPositiveFull {S : Set ℕ} {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (hS : ∀ n, 2 ≤ n → n ∉ S → lam n = 0) :
    PrimeBlindPositiveOn S := by
  intro c hc hnull
  have h1 := sum_nonneg_of_weilPositiveFull hW c hc
  rw [sum_re_weilFullFunctional] at h1
  have h0 : linearCombination ℝ (fun j : LogIndex => lam j) (linearCombination ℝ logVector c) =
      0 := by
    rw [linearCombination_apply, Finsupp.sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : (j : ℕ) ∈ S
    · rw [linearCombination_logVector_apply, hnull j j.2 hj, zero_smul]
    · rw [hS j j.2 hj, smul_zero]
  rw [h0, sub_zero] at h1
  rw [sum_weilArchRe_eq]
  exact h1

/-- Extending a weight on the nodes of `S` by `0` does not change its pairing with log vectors. -/
theorem linearCombination_extendOn (S : Set ℕ) (lam' : {j : LogIndex // (j : ℕ) ∈ S} → ℝ)
    (f : WeilTestFn) :
    linearCombination ℝ (fun j : LogIndex => if hj : (j : ℕ) ∈ S then lam' ⟨j, hj⟩ else 0)
        (logVector f) = linearCombination ℝ lam' (logVectorOn S f) := by
  classical
  rw [linearCombination_apply, linearCombination_apply, Finsupp.sum, Finsupp.sum, logVectorOn,
    Finsupp.support_subtypeDomain]
  have hmap := Finset.sum_subtype_map_embedding (s := (logVector f).support.subtype
      fun j : LogIndex => (j : ℕ) ∈ S)
    (f := fun a => (logVector f).subtypeDomain (fun j : LogIndex => (j : ℕ) ∈ S) a • lam' a)
    (g := fun j => logVector f j • if hj : (j : ℕ) ∈ S then lam' ⟨j, hj⟩ else 0) fun a _ => by
      simp [a.2]
  rw [← hmap, Finset.subtype_map]
  rw [Finset.sum_filter_of_ne]
  intro j _ hne
  by_contra hjS
  exact hne (by simp [hjS])

/-- **Prime-blind positivity on `S` produces a Weil-positive weight vanishing off `S`.** -/
theorem exists_weilPositiveFull_of_primeBlindPositiveOn {S : Set ℕ} (h : PrimeBlindPositiveOn S) :
    ∃ lam : ℕ → ℝ, WeilPositiveFull lam ∧ ∀ n, 2 ≤ n → n ∉ S → lam n = 0 := by
  classical
  obtain ⟨lam', hlam'⟩ := GaloisForLFunctions.HTGeometry.exists_of_nonneg_on_null_cone
    (logVectorOn S) (fun f : WeilTestFn => weilArchRe (EF.weilTest f.1 f.1))
    (fun a => ⟨pairTestFn a.1 (-1), _, pairTest_weight_pos a.1, by
      rw [logVectorOn_pairTestFn S a.1 a.2]; congr 1; ring⟩)
    (fun a => ⟨pairTestFn a.1 1, _, pairTest_weight_pos a.1, by
      rw [logVectorOn_pairTestFn S a.1 a.2]; congr 1; ring⟩)
    (fun c hc hnull => by
      rw [← sum_weilArchRe_eq]
      refine h c hc fun n hn hnS => ?_
      rw [← linearCombination_logVectorOn_apply S c ⟨⟨n, hn⟩, hnS⟩, hnull]
      rfl)
  set lam : LogIndex → ℝ := fun j => if hj : (j : ℕ) ∈ S then lam' ⟨j, hj⟩ else 0 with hlam
  have key : ∀ f : WeilTestFn,
      linearCombination ℝ lam (logVector f) = linearCombination ℝ lam' (logVectorOn S f) :=
    fun f => linearCombination_extendOn S lam' f
  refine ⟨_, weilPositiveFull_of_le_arch (lam := lam) fun f => (key f).symm ▸ hlam' f,
    fun n hn hnS => ?_⟩
  simp [hlam, hn, hnS]

/-- **Node criticality of prime-blind positivity.**  Prime-blind positivity on `S` holds exactly
when RH holds and `S` contains every prime power. -/
theorem primeBlindPositiveOn_iff {S : Set ℕ} :
    PrimeBlindPositiveOn S ↔
      RiemannHypothesis ∧ ∀ n, 2 ≤ n → ArithmeticFunction.vonMangoldt n ≠ 0 → n ∈ S := by
  constructor
  · intro h
    obtain ⟨lam, hW, hS⟩ := exists_weilPositiveFull_of_primeBlindPositiveOn h
    have hΛ := RHTower.WeilSpectral.eq_vonMangoldt_of_weilPositiveFull hW
    refine ⟨riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr fun f hf hc => ?_,
      fun n hn hΛn => ?_⟩
    · have := hW f hf hc
      rwa [weilFullFunctional_congr hΛ] at this
    · by_contra hnS
      exact hΛn (by rw [← hΛ n hn, hS n hn hnS])
  · rintro ⟨hRH, hS⟩
    refine primeBlindPositiveOn_of_weilPositiveFull
      (riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH) fun n hn hnS => ?_
    by_contra h
    exact hnS (hS n hn h)

/-- Blindness at the prime powers alone already characterizes RH. -/
theorem riemannHypothesis_iff_primeBlindPositiveOn_primePowers :
    RiemannHypothesis ↔ PrimeBlindPositiveOn {n | IsPrimePow n} := by
  rw [primeBlindPositiveOn_iff]
  refine ⟨fun h => ⟨h, fun n _ hn => ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hn⟩,
    fun h => h.1⟩

/-- **Deleting one prime-power node breaks prime-blind positivity**, unconditionally. -/
theorem not_primeBlindPositiveOn_of_primePower_not_mem {S : Set ℕ} {m : ℕ} (hm : IsPrimePow m)
    (hmS : m ∉ S) : ¬ PrimeBlindPositiveOn S := fun h =>
  hmS ((primeBlindPositiveOn_iff.mp h).2 m hm.two_le
    (ArithmeticFunction.vonMangoldt_ne_zero_iff.mpr hm))

/-- **The archimedean part is negative on a cone missing one prime-power node.**  For every prime
power `m` some nonnegative combination of autocorrelations, vanishing at `±log n` for every `n ≥ 2`
with `n ≠ m`, has negative pole and archimedean part. -/
theorem exists_negative_arch_of_primePower_node_deleted {m : ℕ} (hm : IsPrimePow m) :
    ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧
      (∀ n : ℕ, 2 ≤ n → n ≠ m → (c.sum fun f t => t * logValue f.1 n) = 0) ∧
      (c.sum fun f t => t * weilArchRe (EF.weilTest f.1 f.1)) < 0 := by
  have h := not_primeBlindPositiveOn_of_primePower_not_mem (S := {n | n ≠ m}) hm (by simp)
  simp only [PrimeBlindPositiveOn, not_forall, not_le, exists_prop] at h
  obtain ⟨c, hc, hnull, hneg⟩ := h
  exact ⟨c, hc, fun n hn hnm => hnull n hn hnm, hneg⟩

/-! ### Repairing deleted nodes -/

/-- The weight `w` at the nodes outside `S`, and `0` at the nodes in `S`. -/
def offNodes (S : Set ℕ) (w : ℕ → ℝ) (n : ℕ) : ℝ := if n ∈ S then 0 else w n

/-- **Repaired prime-blind positivity.**  The Weil functional with the weights `w` at the nodes
outside `S` is nonnegative on every nonnegative combination that is blind at the nodes in `S`. -/
def RepairedBlindPositive (S : Set ℕ) (w : ℕ → ℝ) : Prop :=
  ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → n ∈ S → (c.sum fun f t => t * logValue f.1 n) = 0) →
    0 ≤ c.sum fun f t => t * (weilFullFunctional (offNodes S w) (EF.weilTest f.1 f.1)).re

theorem linearCombination_coeff_add (a b : LogIndex → ℝ) (v : LogIndex →₀ ℝ) :
    linearCombination ℝ (fun j => a j + b j) v =
      linearCombination ℝ a v + linearCombination ℝ b v := by
  simp only [linearCombination_apply, smul_add, Finsupp.sum_add]

/-- **Unique repair of deleted nodes.**  Restoring the nodes outside `S` with weights `w` keeps the
Weil functional nonnegative on the `S`-blind cone exactly when RH holds and `w = Λ` at every
deleted node `n ≥ 2`. -/
theorem repairedBlindPositive_iff {S : Set ℕ} {w : ℕ → ℝ} :
    RepairedBlindPositive S w ↔
      RiemannHypothesis ∧ ∀ n, 2 ≤ n → n ∉ S → w n = ArithmeticFunction.vonMangoldt n := by
  classical
  constructor
  · intro h
    obtain ⟨lam', hlam'⟩ := GaloisForLFunctions.HTGeometry.exists_of_nonneg_on_null_cone
      (logVectorOn S)
      (fun f : WeilTestFn => (weilFullFunctional (offNodes S w) (EF.weilTest f.1 f.1)).re)
      (fun a => ⟨pairTestFn a.1 (-1), _, pairTest_weight_pos a.1, by
        rw [logVectorOn_pairTestFn S a.1 a.2]; congr 1; ring⟩)
      (fun a => ⟨pairTestFn a.1 1, _, pairTest_weight_pos a.1, by
        rw [logVectorOn_pairTestFn S a.1 a.2]; congr 1; ring⟩)
      (fun c hc hnull => by
        rw [linearCombination_apply]
        simp only [smul_eq_mul]
        refine h c hc fun n hn hnS => ?_
        rw [← linearCombination_logVectorOn_apply S c ⟨⟨n, hn⟩, hnS⟩, hnull]
        rfl)
    set lam : LogIndex → ℝ :=
      fun j => (if hj : (j : ℕ) ∈ S then lam' ⟨j, hj⟩ else 0) + offNodes S w j with hlam
    have hle : ∀ f : WeilTestFn,
        linearCombination ℝ lam (logVector f) ≤ weilArchRe (EF.weilTest f.1 f.1) := by
      intro f
      have h1 := hlam' f
      rw [re_weilFullFunctional_eq] at h1
      rw [hlam, linearCombination_coeff_add, linearCombination_extendOn]
      linarith
    have hW := weilPositiveFull_of_le_arch hle
    have hΛ := RHTower.WeilSpectral.eq_vonMangoldt_of_weilPositiveFull hW
    refine ⟨riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr fun f hf hc => ?_,
      fun n hn hnS => ?_⟩
    · have := hW f hf hc
      rwa [weilFullFunctional_congr hΛ] at this
    · have := hΛ n hn
      simpa [hlam, offNodes, hn, hnS] using this
  · rintro ⟨hRH, hw⟩ c hc hnull
    have h1 := sum_nonneg_of_weilPositiveFull
      (riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH) c hc
    rw [sum_re_weilFullFunctional] at h1 ⊢
    have hv : ∀ j : LogIndex, (j : ℕ) ∈ S → linearCombination ℝ logVector c j = 0 := fun j hj => by
      rw [linearCombination_logVector_apply, hnull j j.2 hj]
    have e : linearCombination ℝ (fun j : LogIndex => offNodes S w j)
        (linearCombination ℝ logVector c) =
        linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
          (linearCombination ℝ logVector c) := by
      generalize linearCombination ℝ logVector c = v at hv ⊢
      rw [linearCombination_apply, linearCombination_apply]
      refine Finsupp.sum_congr fun j _ => ?_
      by_cases hj : (j : ℕ) ∈ S
      · rw [hv j hj, zero_smul, zero_smul]
      · simp only [offNodes, hj, if_false, hw j j.2 hj]
    rw [e]
    exact h1

/-- **An interpolating family of RH criteria.**  For every node set `S`, RH holds iff the Weil
functional with the von Mangoldt weights at the nodes off `S` is nonnegative on the `S`-blind cone.
`S = ∅` is Weil's criterion; `S = ℕ` is prime-blind positivity. -/
theorem riemannHypothesis_iff_repairedBlindPositive_vonMangoldt (S : Set ℕ) :
    RiemannHypothesis ↔
      RepairedBlindPositive S fun n => (ArithmeticFunction.vonMangoldt n : ℝ) :=
  ⟨fun h => repairedBlindPositive_iff.mpr ⟨h, fun _ _ _ => rfl⟩,
    fun h => (repairedBlindPositive_iff.mp h).1⟩

/-- **The single-prime Weil criterion.**  RH holds iff the archimedean part together with the Euler
factor at one prime `p` (the weights `Λ(p^k)` at the powers of `p`) is nonnegative on the
combinations that are blind at every node `n ≥ 2` that is not a power of `p`. -/
theorem riemannHypothesis_iff_singlePrimeWeilPositive (p : ℕ) :
    RiemannHypothesis ↔
      RepairedBlindPositive {n | ∀ k : ℕ, n ≠ p ^ (k + 1)}
        fun n => (ArithmeticFunction.vonMangoldt n : ℝ) :=
  riemannHypothesis_iff_repairedBlindPositive_vonMangoldt _

end

end RHTower.WeilOneSided
