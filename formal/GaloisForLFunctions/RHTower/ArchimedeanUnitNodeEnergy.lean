import GaloisForLFunctions.RHTower.PrimeBlindNodeCriticality

/-!
# The von Mangoldt function as an archimedean unit-node energy

For a nonnegative finitely supported combination `c` of Weil tests write
`A(c) = Σ c_f A(k_f)` for the pole and archimedean part of the Weil functional on the
autocorrelations `k_f = f ⋆ f̃`, and `L_n(c) = Σ c_f ℓ_n(f)` for the normalized symmetric value at
`±log n`.  For an integer `m ≥ 2` let `E_m` be the set of the energies `A(c)` of the combinations
that are blind at every node `n ≥ 2`, `n ≠ m`, and carry unit mass `L_m(c) = 1` at `m`
(`unitNodeEnergies`).

**Theorem.**
* `isGLB_unitNodeEnergies`: under RH, `inf E_m = Λ(m)` for every `m ≥ 2`.
* `not_bddBelow_unitNodeEnergies`: if RH fails, `E_m` is unbounded below for every `m ≥ 2`.
* `riemannHypothesis_iff_bddBelow_unitNodeEnergies`: RH holds iff `E_m` is bounded below, for any
  single `m ≥ 2`.

So the archimedean place alone, through the positions `log n`, determines the primes: under RH the
least archimedean energy that puts unit mass at the single node `log m` is `Λ(m)`.  It is `log p`
at `m = p^k` and `0` at every other `m`.

Proof.
* Lower bound.  Under RH, `W_Λ(c) = A(c) − Σ Λ(n) L_n(c) ≥ 0`, and on `E_m` the sum is `Λ(m)`.
* Sharpness.  Suppose every energy in `E_m` is at least `b > Λ(m)`.  Then the Weil functional with
  weight `b` at `m` and `0` at the other nodes is nonnegative on the cone blind off `m`.  If
  `L_m(c) > 0`, rescale `c` into `E_m`.  If `L_m(c) ≤ 0`, compare with `W_Λ(c) ≥ 0`.  This
  contradicts the unique repair theorem (`repairedBlindPositive_iff`), which forces `b = Λ(m)`.
* Unboundedness.  If RH fails, prime-blind positivity fails
  (`riemannHypothesis_iff_primeBlindPositive_unconditional`).  A fully blind `c₀` with `A(c₀) < 0`,
  added with a large coefficient to a normalized pair test at `m`, drives the energy to `−∞`.
-/

open Finsupp Zeta23

namespace RHTower.WeilOneSided

noncomputable section

/-- The pole and archimedean energy `A(c) = Σ c_f A(k_f)` of a combination of tests. -/
def nodeArchEnergy (c : WeilTestFn →₀ ℝ) : ℝ :=
  linearCombination ℝ (fun f : WeilTestFn => weilArchRe (EF.weilTest f.1 f.1)) c

/-- The node values `n ↦ L_n(c)` of a combination of tests. -/
def nodeVector (c : WeilTestFn →₀ ℝ) : LogIndex →₀ ℝ := linearCombination ℝ logVector c

/-- **Unit-node energies.**  The energies of the nonnegative combinations that vanish at every node
other than `m` and carry unit mass at `m`. -/
def unitNodeEnergies (m : LogIndex) : Set ℝ :=
  {E | ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ (∀ j : LogIndex, j ≠ m → nodeVector c j = 0) ∧
    nodeVector c m = 1 ∧ nodeArchEnergy c = E}

theorem nodeVector_eq_single {c : WeilTestFn →₀ ℝ} {m : LogIndex}
    (h : ∀ j : LogIndex, j ≠ m → nodeVector c j = 0) :
    nodeVector c = Finsupp.single m (nodeVector c m) := by
  ext j
  by_cases hj : j = m
  · subst hj; simp
  · rw [h j hj, Finsupp.single_apply, if_neg (Ne.symm hj)]

/-- The real part of the Weil functional of a combination blind off `m`. -/
theorem sum_re_weilFullFunctional_of_blind_off (U : ℕ → ℝ) {c : WeilTestFn →₀ ℝ} {m : LogIndex}
    (h : ∀ j : LogIndex, j ≠ m → nodeVector c j = 0) :
    (c.sum fun f t => t * (weilFullFunctional U (EF.weilTest f.1 f.1)).re) =
      nodeArchEnergy c - nodeVector c m * U m := by
  rw [sum_re_weilFullFunctional]
  change nodeArchEnergy c - linearCombination ℝ (fun j : LogIndex => U j) (nodeVector c) = _
  rw [nodeVector_eq_single h, linearCombination_single, smul_eq_mul, Finsupp.single_eq_same]

/-- Under RH, `A(c) ≥ Λ(m) L_m(c)` on the nonnegative combinations blind off `m`. -/
theorem vonMangoldt_mul_le_nodeArchEnergy (hRH : RiemannHypothesis) {c : WeilTestFn →₀ ℝ}
    (hc : ∀ f, 0 ≤ c f) {m : LogIndex} (h : ∀ j : LogIndex, j ≠ m → nodeVector c j = 0) :
    nodeVector c m * ArithmeticFunction.vonMangoldt (m : ℕ) ≤ nodeArchEnergy c := by
  have h1 := sum_nonneg_of_weilPositiveFull
    (riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH) c hc
  rw [sum_re_weilFullFunctional_of_blind_off _ h] at h1
  linarith

/-- **Under RH, the least unit-node energy at `m` is `Λ(m)`.** -/
theorem isGLB_unitNodeEnergies (hRH : RiemannHypothesis) (m : LogIndex) :
    IsGLB (unitNodeEnergies m) (ArithmeticFunction.vonMangoldt (m : ℕ)) := by
  refine ⟨?_, fun b hb => ?_⟩
  · rintro E ⟨c, hc, hblind, hm, rfl⟩
    have := vonMangoldt_mul_le_nodeArchEnergy hRH hc hblind
    rwa [hm, one_mul] at this
  · by_contra hlt
    rw [not_le] at hlt
    have hrep : RepairedBlindPositive {n | n ≠ (m : ℕ)} fun _ => b := by
      intro c hc hnull
      have hblind : ∀ j : LogIndex, j ≠ m → nodeVector c j = 0 := fun j hj => by
        rw [nodeVector, linearCombination_logVector_apply]
        exact hnull j j.2 fun h => hj (Subtype.ext h)
      rw [sum_re_weilFullFunctional_of_blind_off _ hblind]
      have hoff : offNodes {n | n ≠ (m : ℕ)} (fun _ => b) (m : ℕ) = b := by
        simp [offNodes]
      rw [hoff]
      set x := nodeVector c m with hx
      rcases lt_or_ge 0 x with hpos | hnonpos
      · have hmem : nodeArchEnergy (x⁻¹ • c) ∈ unitNodeEnergies m := by
          refine ⟨x⁻¹ • c, fun f => ?_, fun j hj => ?_, ?_, rfl⟩
          · simp only [Finsupp.smul_apply, smul_eq_mul]
            exact mul_nonneg (inv_nonneg.mpr hpos.le) (hc f)
          · simp only [nodeVector, map_smul, Finsupp.smul_apply, smul_eq_mul]
            rw [← nodeVector, hblind j hj, mul_zero]
          · simp only [nodeVector, map_smul, Finsupp.smul_apply, smul_eq_mul]
            rw [← nodeVector, ← hx, inv_mul_cancel₀ hpos.ne']
        have hb' := hb hmem
        simp only [nodeArchEnergy, map_smul, smul_eq_mul] at hb'
        rw [← nodeArchEnergy] at hb'
        have : b * x ≤ nodeArchEnergy c := by
          have := mul_le_mul_of_nonneg_left hb' hpos.le
          rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, mul_comm] at this
        linarith
      · have h1 := vonMangoldt_mul_le_nodeArchEnergy hRH hc hblind
        rw [← hx] at h1
        nlinarith
    have := (repairedBlindPositive_iff.mp hrep).2 m m.2 (by simp)
    exact absurd this (ne_of_gt hlt)

/-- A test with unit mass at the single node `m`. -/
def unitNodeTest (m : LogIndex) : WeilTestFn →₀ ℝ :=
  (2 * (∫ t, (narrowBump m t) ^ 2) / Real.sqrt m)⁻¹ • Finsupp.single (pairTestFn m 1) 1

theorem nodeVector_unitNodeTest (m : LogIndex) :
    nodeVector (unitNodeTest m) = Finsupp.single m 1 := by
  have ha := pairTest_weight_pos m
  rw [unitNodeTest, nodeVector, map_smul, linearCombination_single, one_smul,
    logVector_pairTestFn, Finsupp.smul_single, smul_eq_mul]
  congr 1
  rw [mul_one]
  exact inv_mul_cancel₀ ha.ne'

theorem unitNodeTest_nonneg (m : LogIndex) (f : WeilTestFn) : 0 ≤ unitNodeTest m f := by
  classical
  have ha := pairTest_weight_pos m
  rw [unitNodeTest, Finsupp.smul_apply, smul_eq_mul]
  refine mul_nonneg (inv_nonneg.mpr ha.le) ?_
  rw [Finsupp.single_apply]
  split_ifs <;> norm_num

/-- **If RH fails, the unit-node energies are unbounded below.** -/
theorem not_bddBelow_unitNodeEnergies (hRH : ¬ RiemannHypothesis) (m : LogIndex) :
    ¬ BddBelow (unitNodeEnergies m) := by
  have hP : ¬ PrimeBlindPositive := fun h =>
    hRH (riemannHypothesis_iff_primeBlindPositive_unconditional.mpr h)
  simp only [PrimeBlindPositive, not_forall, not_le, exists_prop] at hP
  obtain ⟨c₀, hc₀, hnull, hneg⟩ := hP
  rw [sum_weilArchRe_eq, ← nodeArchEnergy] at hneg
  have hv₀ : ∀ j : LogIndex, nodeVector c₀ j = 0 := fun j => by
    rw [nodeVector, linearCombination_logVector_apply]
    exact hnull j j.2
  rintro ⟨L, hL⟩
  set t : ℝ := (|nodeArchEnergy (unitNodeTest m)| + |L| + 1) / (-nodeArchEnergy c₀) with ht
  have ht0 : 0 ≤ t := div_nonneg (by positivity) (by linarith)
  have hmem : nodeArchEnergy (unitNodeTest m + t • c₀) ∈ unitNodeEnergies m := by
    refine ⟨unitNodeTest m + t • c₀, fun f => ?_, fun j hj => ?_, ?_, rfl⟩
    · simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
      exact add_nonneg (unitNodeTest_nonneg m f) (mul_nonneg ht0 (hc₀ f))
    · simp only [nodeVector, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
        smul_eq_mul]
      rw [← nodeVector, ← nodeVector, nodeVector_unitNodeTest, hv₀ j, mul_zero, add_zero,
        Finsupp.single_apply, if_neg (Ne.symm hj)]
    · simp only [nodeVector, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
        smul_eq_mul]
      rw [← nodeVector, ← nodeVector, nodeVector_unitNodeTest, hv₀ m, mul_zero, add_zero,
        Finsupp.single_eq_same]
  have h1 := hL hmem
  simp only [nodeArchEnergy, map_add, map_smul, smul_eq_mul] at h1
  rw [← nodeArchEnergy, ← nodeArchEnergy] at h1
  have h2 : t * nodeArchEnergy c₀ = -(|nodeArchEnergy (unitNodeTest m)| + |L| + 1) := by
    rw [ht, div_mul_eq_mul_div, div_eq_iff (by linarith : -nodeArchEnergy c₀ ≠ 0)]
    ring
  have h3 := le_abs_self (nodeArchEnergy (unitNodeTest m))
  have h4 := neg_abs_le L
  linarith

/-- **RH is the boundedness of a single unit-node energy.** -/
theorem riemannHypothesis_iff_bddBelow_unitNodeEnergies (m : LogIndex) :
    RiemannHypothesis ↔ BddBelow (unitNodeEnergies m) :=
  ⟨fun h => (isGLB_unitNodeEnergies h m).bddBelow, fun h => by
    by_contra hRH
    exact not_bddBelow_unitNodeEnergies hRH m h⟩

end

end RHTower.WeilOneSided
