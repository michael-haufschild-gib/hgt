import GaloisForLFunctions.RHTower.GammaSewnSynchronizedRecoveryQuadraticCurvature
import GaloisForLFunctions.RHTower.GammaSewnXiWardJuliaGramTangentUniversalityLaw

/-!
# Forced cross-prime curvature in synchronized Gamma recovery

The synchronized recovery curvature is not a direct sum of its one-prime
curvatures.  Its exact positive remainder is forced by the global squared
prime-log phase.  This gives a source-side obstruction to any formation
construction which assembles prime cells additively before it supplies a
signed mixed companion.

It makes no divisor, zero, or RH assertion.
-/

open scoped BigOperators
open Filter Topology

namespace RHTower

noncomputable section

/-- Curvature not accounted for by the sum of all singleton prime cells. -/
def gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly
    (P : Finset Nat.Primes) : ℝ :=
  gammaSewnSynchronizedRecoveryQuadraticCost P -
    ∑ p ∈ P, gammaSewnSynchronizedRecoveryQuadraticCost {p}

/-- Adding a new prime creates exactly its pairwise logarithmic interaction
with the existing synchronized support. -/
theorem gammaSewnSynchronizedRecoveryQuadraticCost_insert
    {p : Nat.Primes} {P : Finset Nat.Primes} (hp : p ∉ P) :
    gammaSewnSynchronizedRecoveryQuadraticCost (insert p P) =
      gammaSewnSynchronizedRecoveryQuadraticCost P +
        gammaSewnSynchronizedRecoveryQuadraticCost {p} +
          (1 / 12 : ℝ) * Real.log (p : ℝ) *
            ∑ q ∈ P, Real.log (q : ℝ) := by
  simp only [gammaSewnSynchronizedRecoveryQuadraticCost, Finset.sum_insert hp,
    Finset.sum_singleton]
  ring

/-- The cross anomaly has the same exact insertion recurrence. -/
theorem gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly_insert
    {p : Nat.Primes} {P : Finset Nat.Primes} (hp : p ∉ P) :
    gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly (insert p P) =
      gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly P +
        (1 / 12 : ℝ) * Real.log (p : ℝ) *
          ∑ q ∈ P, Real.log (q : ℝ) := by
  rw [gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly,
    gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly,
    gammaSewnSynchronizedRecoveryQuadraticCost_insert hp,
    Finset.sum_insert hp]
  ring

/-- The mixed curvature is never negative. -/
theorem gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly_nonneg
    (P : Finset Nat.Primes) :
    0 ≤ gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly P := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      simp [gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly,
        gammaSewnSynchronizedRecoveryQuadraticCost]
  | @insert p P hp ih =>
      rw [gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly_insert hp]
      have hlogp : 0 ≤ Real.log (p : ℝ) := by
        exact Real.log_nonneg (by exact_mod_cast p.property.one_le)
      have hsum : 0 ≤ ∑ q ∈ P, Real.log (q : ℝ) := by
        exact Finset.sum_nonneg fun q _ =>
          Real.log_nonneg (by exact_mod_cast q.property.one_le)
      positivity

/-- Any two distinct prime cells force strictly positive mixed curvature. -/
theorem gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly_pos_of_two_mem
    {P : Finset Nat.Primes} {p q : Nat.Primes}
    (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    0 < gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly P := by
  have hqerase : q ∈ P.erase p := Finset.mem_erase.mpr ⟨hpq.symm, hq⟩
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hsum : 0 < ∑ r ∈ P.erase p, Real.log (r : ℝ) := by
    apply Finset.sum_pos
    · intro r hr
      exact Real.log_pos (by exact_mod_cast r.property.one_lt)
    · exact ⟨q, hqerase⟩
  have hrewrite : insert p (P.erase p) = P := Finset.insert_erase hp
  have hpnoterase : p ∉ P.erase p := by simp
  rw [← hrewrite,
    gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly_insert hpnoterase]
  have hnonneg := gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly_nonneg (P.erase p)
  have hcross : 0 < (1 / 12 : ℝ) * Real.log (p : ℝ) *
      ∑ r ∈ P.erase p, Real.log (r : ℝ) := by positivity
  linarith

/-- Consequently, singleton-additive formation cannot reproduce a support
containing two distinct primes. -/
theorem gammaSewnSynchronizedRecoveryQuadraticCost_ne_sum_singletons_of_two_mem
    {P : Finset Nat.Primes} {p q : Nat.Primes}
    (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    gammaSewnSynchronizedRecoveryQuadraticCost P ≠
      ∑ r ∈ P, gammaSewnSynchronizedRecoveryQuadraticCost {r} := by
  intro hadditive
  have hpos :=
    gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly_pos_of_two_mem hp hq hpq
  apply (ne_of_gt hpos)
  unfold gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly
  rw [hadditive]
  ring

/-- The density-independent source factor which remains after removing every
primewise recovery multiplier from synchronized recovery. -/
def gammaSewnSynchronizedRecoveryCrossFactor
    (x : ℝ) (P : Finset Nat.Primes) : ℝ :=
  (∏ p ∈ P, exponentialChordFactor (x * Real.log (p : ℝ))) /
    exponentialChordFactor (x * ∑ p ∈ P, Real.log (p : ℝ))

/-- On a singleton, synchronized recovery is the literal one-prime
Gamma-sewn valuation multiplier. -/
theorem gammaSewnSynchronizedRecoveryRatio_singleton_eq_multiplier
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    gammaSewnSynchronizedRecoveryRatio nu x {p} =
      gammaSewnMobiusValuationContractionMultiplier x p := by
  rw [gammaSewnSynchronizedRecoveryRatio_eq_chordQuotient nu hnu hx (by simp)]
  have hpos : 0 < exponentialChordFactor (x * Real.log (p : ℝ)) :=
    exponentialChordFactor_pos (mul_nonneg hx.le (Real.log_nonneg
      (by exact_mod_cast p.property.one_le)))
  simp only [Finset.prod_singleton, Finset.sum_singleton]
  field_simp [hpos.ne']

/-- Exact finite source factorization: synchronization is the product of all
one-prime recoveries times one canonical mixed chord factor. -/
theorem gammaSewnSynchronizedRecoveryRatio_eq_prod_singleton_mul_crossFactor
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    {x : ℝ} (hx : 0 < x) {P : Finset Nat.Primes} (hP : P.Nonempty) :
    gammaSewnSynchronizedRecoveryRatio nu x P =
      (∏ p ∈ P, gammaSewnSynchronizedRecoveryRatio nu x {p}) *
        gammaSewnSynchronizedRecoveryCrossFactor x P := by
  rw [gammaSewnSynchronizedRecoveryRatio_eq_chordQuotient nu hnu hx hP]
  simp_rw [gammaSewnSynchronizedRecoveryRatio_singleton_eq_multiplier nu hnu hx]
  unfold gammaSewnSynchronizedRecoveryCrossFactor
  rw [Finset.prod_mul_distrib]
  ring

private theorem tendsto_finset_prod_one_local
    {α : Type*} [DecidableEq α] (P : Finset α)
    (f : α → ℝ → ℝ)
    (hf : ∀ p ∈ P, Tendsto (f p) (𝓝 (0 : ℝ)) (𝓝 1)) :
    Tendsto (fun x ↦ ∏ p ∈ P, f p x) (𝓝 (0 : ℝ)) (𝓝 1) := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
      rw [show (fun x ↦ ∏ q ∈ insert p P, f q x) =
          fun x ↦ f p x * ∏ q ∈ P, f q x by
        funext x
        rw [Finset.prod_insert hp]]
      convert (hf p (Finset.mem_insert_self p P)).mul
        (ih (fun q hq ↦ hf q (Finset.mem_insert_of_mem hq))) using 1
      simp

private theorem tendsto_finset_prod_pureSecondJet
    {α : Type*} [DecidableEq α]
    (P : Finset α) (f : α → ℝ → ℝ) (b : α → ℝ)
    (hf0 : ∀ p ∈ P, Tendsto (f p) (𝓝 (0 : ℝ)) (𝓝 1))
    (hf2 : ∀ p ∈ P,
      Tendsto (fun x : ℝ => (f p x - 1) / x ^ (2 : ℕ))
        (𝓝[>] (0 : ℝ)) (𝓝 (b p))) :
    Tendsto
      (fun x : ℝ => ((∏ p ∈ P, f p x) - 1) / x ^ (2 : ℕ))
      (𝓝[>] (0 : ℝ)) (𝓝 (∑ p ∈ P, b p)) := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
      have hp0 := hf0 p (Finset.mem_insert_self p P)
      have hp2 := hf2 p (Finset.mem_insert_self p P)
      have hP0 :
          Tendsto (fun x : ℝ => ∏ q ∈ P, f q x)
            (𝓝[>] (0 : ℝ)) (𝓝 1) :=
        (tendsto_finset_prod_one_local P f
          (fun q hq ↦ hf0 q (Finset.mem_insert_of_mem hq))).mono_left
          nhdsWithin_le_nhds
      have hP2 := ih
        (fun q hq ↦ hf0 q (Finset.mem_insert_of_mem hq))
        (fun q hq ↦ hf2 q (Finset.mem_insert_of_mem hq))
      have hmain := hp0.mono_left nhdsWithin_le_nhds |>.mul hP2 |>.add hp2
      rw [Finset.sum_insert hp]
      have hmain' :
          Tendsto
            (fun x : ℝ =>
              f p x * (((∏ q ∈ P, f q x) - 1) / x ^ (2 : ℕ)) +
                (f p x - 1) / x ^ (2 : ℕ))
            (𝓝[>] (0 : ℝ)) (𝓝 (b p + ∑ q ∈ P, b q)) := by
        convert hmain using 1
        all_goals ring_nf
      apply hmain'.congr'
      filter_upwards [self_mem_nhdsWithin] with x hx
      change 0 < x at hx
      rw [Finset.prod_insert hp]
      field_simp [hx.ne']
      ring

/-- The product of literal primewise recovery multipliers has only the sum
of their quadratic jets. -/
theorem tendsto_gammaSewnSynchronizedRecoveryPrimewiseFactor_quadraticJet_zero
    (P : Finset Nat.Primes) :
    Tendsto
      (fun x : ℝ =>
        ((∏ p ∈ P, gammaSewnMobiusValuationContractionMultiplier x p) - 1) / x ^ (2 : ℕ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ p ∈ P, -(3 / 8 : ℝ) * Real.log (p : ℝ) ^ (2 : ℕ))) := by
  apply tendsto_finset_prod_pureSecondJet P
    (fun p x ↦ gammaSewnMobiusValuationContractionMultiplier x p)
    (fun p ↦ -(3 / 8 : ℝ) * Real.log (p : ℝ) ^ (2 : ℕ))
  · intro p hp
    simpa [gammaSewnMobiusValuationContractionMultiplier_zero] using
      (continuousAt_gammaSewnMobiusValuationContractionMultiplier_zero p).tendsto
  · intro p hp
    exact tendsto_gammaSewnMobiusValuationContraction_quadraticJet_zero p

/-- The canonical synchronized mixed factor has precisely the negative of
the forced cross-prime curvature as its quadratic boundary jet. -/
theorem tendsto_gammaSewnSynchronizedRecoveryCrossFactor_quadraticJet_zero
    (P : Finset Nat.Primes) :
    Tendsto
      (fun x : ℝ =>
        (gammaSewnSynchronizedRecoveryCrossFactor x P - 1) / x ^ (2 : ℕ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (-gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly P)) := by
  classical
  by_cases hP0 : P = ∅
  · subst P
    simp [gammaSewnSynchronizedRecoveryCrossFactor,
      gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly,
      gammaSewnSynchronizedRecoveryQuadraticCost, exponentialChordFactor]
  have hP : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hP0
  let M : ℝ → ℝ := fun x ↦
    ∏ p ∈ P, gammaSewnMobiusValuationContractionMultiplier x p
  have hM0 : Tendsto M (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    (tendsto_finset_prod_one_local P
      (fun p x ↦ gammaSewnMobiusValuationContractionMultiplier x p)
      (fun p hp ↦ by
        simpa [gammaSewnMobiusValuationContractionMultiplier_zero] using
          (continuousAt_gammaSewnMobiusValuationContractionMultiplier_zero p).tendsto)).mono_left
      nhdsWithin_le_nhds
  have hM2 :=
    tendsto_gammaSewnSynchronizedRecoveryPrimewiseFactor_quadraticJet_zero P
  have hR := tendsto_gammaSewnSynchronizedRecoveryRatio_quadraticJet_zero
    (fun _ : Nat.Primes ↦ (1 : ℝ)) (by intro p; norm_num) P
  have hdiff := hR.sub hM2
  have hquot := hdiff.div hM0 one_ne_zero
  change Tendsto
      (fun x : ℝ =>
        ((gammaSewnSynchronizedRecoveryRatio (fun _ : Nat.Primes ↦ (1 : ℝ)) x P - 1) / x ^ (2 : ℕ) -
          ((∏ p ∈ P, gammaSewnMobiusValuationContractionMultiplier x p) - 1) / x ^ (2 : ℕ)) / M x)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((-gammaSewnSynchronizedRecoveryQuadraticCost P -
        ∑ p ∈ P, -(3 / 8 : ℝ) * Real.log (p : ℝ) ^ (2 : ℕ)) / 1)) at hquot
  have hcost :
      (∑ p ∈ P, -(3 / 8 : ℝ) * Real.log (p : ℝ) ^ (2 : ℕ)) =
        -∑ p ∈ P, gammaSewnSynchronizedRecoveryQuadraticCost {p} := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    simp [gammaSewnSynchronizedRecoveryQuadraticCost]
    ring
  rw [hcost] at hquot
  have htarget :
      -gammaSewnSynchronizedRecoveryQuadraticCost P -
          (-∑ p ∈ P, gammaSewnSynchronizedRecoveryQuadraticCost {p}) =
        -gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly P := by
    unfold gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly
    ring
  rw [htarget] at hquot
  have hquot' :
      Tendsto
        (fun x : ℝ =>
          ((gammaSewnSynchronizedRecoveryRatio (fun _ : Nat.Primes ↦ (1 : ℝ)) x P - 1) / x ^ (2 : ℕ) -
            (M x - 1) / x ^ (2 : ℕ)) / M x)
        (𝓝[>] (0 : ℝ))
        (𝓝 (-gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly P)) := by
    simpa only [M, div_one] using hquot
  apply hquot'.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  have hfactor := gammaSewnSynchronizedRecoveryRatio_eq_prod_singleton_mul_crossFactor
    (fun _ : Nat.Primes ↦ (1 : ℝ)) (by intro p; norm_num) hx hP
  simp_rw [gammaSewnSynchronizedRecoveryRatio_singleton_eq_multiplier
    (fun _ : Nat.Primes ↦ (1 : ℝ)) (by intro p; norm_num) hx] at hfactor
  have hMpos : 0 < M x := by
    dsimp only [M]
    exact Finset.prod_pos fun p hp => gammaSewnMobiusValuationContractionMultiplier_pos x p
  change
    (((gammaSewnSynchronizedRecoveryRatio (fun _ : Nat.Primes ↦ (1 : ℝ)) x P - 1) / x ^ (2 : ℕ) -
      (M x - 1) / x ^ (2 : ℕ)) / M x) =
      (gammaSewnSynchronizedRecoveryCrossFactor x P - 1) / x ^ (2 : ℕ)
  rw [hfactor]
  field_simp [hx.ne', hMpos.ne']
  ring

/-- Exact signed source factorization.  Möbius-oriented synchronized recovery is
the product of the literal one-prime amplitudes times the positive square root
of its canonical mixed chord factor.  Thus the cross-prime carrier survives at
amplitude level; it is not an artifact of squared norms. -/
theorem gammaSewnSynchronizedSignedRecoveryAmplitude_eq_prod_singleton_mul_sqrt_crossFactor
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    {x : ℝ} (hx : 0 < x) {P : Finset Nat.Primes} (hP : P.Nonempty) :
    gammaSewnSynchronizedSignedRecoveryAmplitude nu x P =
      (∏ p ∈ P, gammaSewnSynchronizedSignedRecoveryAmplitude nu x {p}) *
        (Real.sqrt (gammaSewnSynchronizedRecoveryCrossFactor x P) : ℂ) := by
  have hfactor :=
    gammaSewnSynchronizedRecoveryRatio_eq_prod_singleton_mul_crossFactor
      nu hnu hx hP
  have hsqrt :
      Real.sqrt (gammaSewnSynchronizedRecoveryRatio nu x P) =
        (∏ p ∈ P, Real.sqrt (gammaSewnSynchronizedRecoveryRatio nu x {p})) *
          Real.sqrt (gammaSewnSynchronizedRecoveryCrossFactor x P) := by
    rw [hfactor, Real.sqrt_mul (Finset.prod_nonneg fun p hp =>
      (gammaSewnSynchronizedRecoveryRatio_pos_le_one nu hnu hx {p}).1.le)]
    rw [Real.sqrt_prod P fun p hp =>
      (gammaSewnSynchronizedRecoveryRatio_pos_le_one nu hnu hx {p}).1.le]
  have hreal :
      (-1 : ℝ) ^ P.card *
          Real.sqrt (gammaSewnSynchronizedRecoveryRatio nu x P) =
        (∏ p ∈ P, (-1 : ℝ) ^ ({p} : Finset Nat.Primes).card *
          Real.sqrt (gammaSewnSynchronizedRecoveryRatio nu x {p})) *
          Real.sqrt (gammaSewnSynchronizedRecoveryCrossFactor x P) := by
    rw [hsqrt, Finset.prod_mul_distrib]
    simp only [Finset.card_singleton, pow_one]
    rw [Finset.prod_const]
    ring
  simpa [gammaSewnSynchronizedSignedRecoveryAmplitude,
    Complex.ofReal_mul] using congrArg Complex.ofReal hreal

/-- The mixed amplitude factor has exactly half the quadratic cross curvature.
This is the first non-primewise signed jet: it is absent from the linear
Julia tangent but cannot be removed at quadratic order. -/
theorem tendsto_sqrt_gammaSewnSynchronizedRecoveryCrossFactor_sub_one_div_sq_zero
    (P : Finset Nat.Primes) :
    Tendsto
      (fun x : ℝ =>
        (Real.sqrt (gammaSewnSynchronizedRecoveryCrossFactor x P) - 1) / x ^ (2 : ℕ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (-gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly P / 2)) := by
  have hqjet :=
    tendsto_gammaSewnSynchronizedRecoveryCrossFactor_quadraticJet_zero P
  have hid : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hqminus :
      Tendsto
        (fun x : ℝ => gammaSewnSynchronizedRecoveryCrossFactor x P - 1)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hprod := hqjet.mul (hid.pow 2)
    have hprod' :
        Tendsto
          (fun x : ℝ =>
            ((gammaSewnSynchronizedRecoveryCrossFactor x P - 1) / x ^ (2 : ℕ)) * x ^ (2 : ℕ))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using hprod
    apply hprod'.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    field_simp [hx.ne']
  have hqzero :
      Tendsto (fun x : ℝ => gammaSewnSynchronizedRecoveryCrossFactor x P)
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hsum :
        Tendsto
          (fun x : ℝ => gammaSewnSynchronizedRecoveryCrossFactor x P - 1 + 1)
          (𝓝[>] (0 : ℝ)) (𝓝 (0 + 1)) :=
      hqminus.add tendsto_const_nhds
    simpa only [sub_add_cancel, zero_add] using hsum
  have hsqrt :
      Tendsto (fun x : ℝ => Real.sqrt (gammaSewnSynchronizedRecoveryCrossFactor x P))
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [Function.comp_def, Real.sqrt_one] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hqzero
  have hden :
      Tendsto
        (fun x : ℝ => Real.sqrt (gammaSewnSynchronizedRecoveryCrossFactor x P) + 1)
        (𝓝[>] (0 : ℝ)) (𝓝 2) := by
    convert hsqrt.add tendsto_const_nhds using 1
    norm_num
  have hquot :
      Tendsto
        (fun x : ℝ =>
          ((gammaSewnSynchronizedRecoveryCrossFactor x P - 1) / x ^ (2 : ℕ)) /
            (Real.sqrt (gammaSewnSynchronizedRecoveryCrossFactor x P) + 1))
        (𝓝[>] (0 : ℝ))
        (𝓝 (-gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly P / 2)) := by
    exact hqjet.div hden (by norm_num : (2 : ℝ) ≠ 0)
  apply hquot.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  have hqpos : 0 < gammaSewnSynchronizedRecoveryCrossFactor x P := by
    unfold gammaSewnSynchronizedRecoveryCrossFactor
    apply div_pos
    · apply Finset.prod_pos
      intro p hp
      apply exponentialChordFactor_pos
      exact mul_nonneg hx.le (Real.log_nonneg (by exact_mod_cast p.property.one_le))
    · apply exponentialChordFactor_pos
      apply mul_nonneg hx.le
      exact Finset.sum_nonneg fun p hp =>
        Real.log_nonneg (by exact_mod_cast p.property.one_le)
  have hsqrtSq :
      Real.sqrt (gammaSewnSynchronizedRecoveryCrossFactor x P) ^ (2 : ℕ) =
        gammaSewnSynchronizedRecoveryCrossFactor x P :=
    Real.sq_sqrt hqpos.le
  field_simp [hx.ne', (by positivity :
    Real.sqrt (gammaSewnSynchronizedRecoveryCrossFactor x P) + 1 ≠ 0)]
  nlinarith

/-- The relative signed recovery amplitude has a nonzero quadratic carrier
exactly when the support has forced mixed curvature.  This turns the finite
source formation law into an explicit complex-valued cross term, prior to any
norm-square or scalarization. -/
theorem tendsto_gammaSewnSynchronizedSignedRecoveryAmplitude_sub_prod_singleton_div_sq_zero
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (P : Finset Nat.Primes) (hP : P.Nonempty) :
    Tendsto
      (fun x : ℝ =>
        (gammaSewnSynchronizedSignedRecoveryAmplitude nu x P -
            ∏ p ∈ P, gammaSewnSynchronizedSignedRecoveryAmplitude nu x {p}) /
          (x : ℂ) ^ (2 : ℕ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.ofReal ((-1 : ℝ) ^ P.card) *
        Complex.ofReal (-gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly P / 2))) := by
  classical
  have hampProd :
      Tendsto
        (fun x : ℝ =>
          ∏ p ∈ P, gammaSewnSynchronizedSignedRecoveryAmplitude nu x {p})
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.ofReal ((-1 : ℝ) ^ P.card))) := by
    clear hP
    induction P using Finset.induction_on with
    | empty => simp
    | @insert p P hp ih =>
        rw [show
          (fun x : ℝ => ∏ q ∈ insert p P,
            gammaSewnSynchronizedSignedRecoveryAmplitude nu x {q}) =
            fun x => gammaSewnSynchronizedSignedRecoveryAmplitude nu x {p} *
              ∏ q ∈ P, gammaSewnSynchronizedSignedRecoveryAmplitude nu x {q} by
            funext x
            rw [Finset.prod_insert hp],
          Finset.card_insert_of_notMem hp]
        simpa [pow_succ, mul_assoc] using
          (tendsto_gammaSewnSynchronizedSignedRecoveryAmplitude_zero nu hnu {p}).mul ih
  have hcross :=
    (tendsto_sqrt_gammaSewnSynchronizedRecoveryCrossFactor_sub_one_div_sq_zero P).ofReal
  have hmain :
      Tendsto
        (fun x : ℝ =>
          (∏ p ∈ P, gammaSewnSynchronizedSignedRecoveryAmplitude nu x {p}) *
            ((Real.sqrt (gammaSewnSynchronizedRecoveryCrossFactor x P) - 1 : ℝ) : ℂ) /
              (x : ℂ) ^ (2 : ℕ))
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.ofReal ((-1 : ℝ) ^ P.card) *
          Complex.ofReal (-gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly P / 2))) := by
    have hmain' :
        Tendsto
          (fun x : ℝ =>
            (∏ p ∈ P, gammaSewnSynchronizedSignedRecoveryAmplitude nu x {p}) *
              (((Real.sqrt (gammaSewnSynchronizedRecoveryCrossFactor x P) - 1) / x ^ (2 : ℕ) : ℝ) : ℂ))
          (𝓝[>] (0 : ℝ))
          (𝓝 (Complex.ofReal ((-1 : ℝ) ^ P.card) *
            Complex.ofReal (-gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly P / 2))) := by
      simpa only [Complex.ofReal_sub, Complex.ofReal_div, map_pow,
        Complex.ofReal_one] using hampProd.mul hcross
    apply hmain'.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have hx2 : (x : ℂ) ^ (2 : ℕ) ≠ 0 := pow_ne_zero _ hx0
    field_simp [hx0, hx2]
    push_cast
    have hinv : (x : ℂ) ^ (2 : ℕ) * (x : ℂ)⁻¹ ^ (2 : ℕ) = 1 := by
      rw [inv_pow]
      exact mul_inv_cancel₀ hx2
    calc
      _ =
          (∏ p ∈ P, gammaSewnSynchronizedSignedRecoveryAmplitude nu x {p}) *
              (Real.sqrt (gammaSewnSynchronizedRecoveryCrossFactor x P) : ℂ) *
                ((x : ℂ) ^ (2 : ℕ) * (x : ℂ)⁻¹ ^ (2 : ℕ)) -
            (∏ p ∈ P, gammaSewnSynchronizedSignedRecoveryAmplitude nu x {p}) *
              ((x : ℂ) ^ (2 : ℕ) * (x : ℂ)⁻¹ ^ (2 : ℕ)) := by ring
      _ = _ := by rw [hinv]; ring
  apply hmain.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  rw [gammaSewnSynchronizedSignedRecoveryAmplitude_eq_prod_singleton_mul_sqrt_crossFactor
    nu hnu hx hP]
  field_simp [show (x : ℂ) ≠ 0 by exact_mod_cast hx.ne']
  push_cast
  ring

/-- A two-prime synchronized amplitude is genuinely mixed at every sufficiently
small positive aperture: it cannot collapse to its singleton product.  This is
the punctured-neighborhood form of the forced nonzero relative curvature. -/
theorem eventually_gammaSewnSynchronizedSignedRecoveryAmplitude_pair_ne_prod_singletons
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (p q : Nat.Primes) (hpq : p ≠ q) :
    ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
      gammaSewnSynchronizedSignedRecoveryAmplitude nu x {p, q} ≠
        gammaSewnSynchronizedSignedRecoveryAmplitude nu x {p} *
          gammaSewnSynchronizedSignedRecoveryAmplitude nu x {q} := by
  have hcrosspos :
      0 < gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly ({p, q} : Finset Nat.Primes) := by
    exact gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly_pos_of_two_mem
      (P := ({p, q} : Finset Nat.Primes)) (p := p) (q := q) (by simp) (by simp) hpq
  have hreal :
      -gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly ({p, q} : Finset Nat.Primes) / 2 ≠ 0 := by
    nlinarith
  have hlimit :=
    tendsto_gammaSewnSynchronizedSignedRecoveryAmplitude_sub_prod_singleton_div_sq_zero
      nu hnu ({p, q} : Finset Nat.Primes) (by simp)
  have hlimitne :
      Complex.ofReal ((-1 : ℝ) ^ ({p, q} : Finset Nat.Primes).card) *
        Complex.ofReal
          (-gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly ({p, q} : Finset Nat.Primes) / 2) ≠ 0 := by
    simpa [hpq] using Complex.ofReal_ne_zero.mpr hreal
  have hopen : IsOpen ({0}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hmem :
      Complex.ofReal ((-1 : ℝ) ^ ({p, q} : Finset Nat.Primes).card) *
        Complex.ofReal
          (-gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly ({p, q} : Finset Nat.Primes) / 2) ∈
        ({0}ᶜ : Set ℂ) := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hlimitne
  have hquotne := hlimit.eventually (hopen.mem_nhds hmem)
  have hprod (x : ℝ) :
      (∏ r ∈ ({p, q} : Finset Nat.Primes),
        gammaSewnSynchronizedSignedRecoveryAmplitude nu x {r}) =
        gammaSewnSynchronizedSignedRecoveryAmplitude nu x {p} *
          gammaSewnSynchronizedSignedRecoveryAmplitude nu x {q} := by
    rw [Finset.prod_insert (by simp [hpq]), Finset.prod_singleton]
  filter_upwards [hquotne] with x hx hEq
  apply hx
  simp only [Set.mem_singleton_iff]
  rw [hEq, hprod]
  ring

/-- **Cubic source-to-Julia cross-term law.**  The first non-primewise signed
recovery coefficient couples to every continued Xi Ward cross cell as the
explicit mixed curvature times its Cauchy tangent.  This is a local transport
identity on the existing zero-free continuation domain; it makes no global
zero or RH assertion. -/
theorem tendsto_gammaSewnSynchronizedSignedRecovery_relative_cross_julia_div_cu_zero
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (P : Finset Nat.Primes) (hP : P.Nonempty)
    {z w : ℂ}
    (hzdom : CCMContinuedCauchyDomain z)
    (hwdom : CCMContinuedCauchyDomain w)
    (hzw : z ≠ (starRingEnd ℂ) w) :
    Tendsto
      (fun x : ℝ =>
        ((gammaSewnSynchronizedSignedRecoveryAmplitude nu x P -
            ∏ p ∈ P, gammaSewnSynchronizedSignedRecoveryAmplitude nu x {p}) *
          xiWardJuliaCrossDefect z w (x : ℂ)) / (x : ℂ) ^ (3 : ℕ))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((Complex.ofReal ((-1 : ℝ) ^ P.card) *
        Complex.ofReal (-gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly P / 2)) *
          ccmContinuedCauchyKernel z w)) := by
  have hzXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain
      hzdom.1 hzdom.2.1 hzdom.2.2.1
  have hwXi : XiC ((starRingEnd ℂ) w) ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain
      hwdom.2.2.2.1 hwdom.2.2.2.2.1 hwdom.2.2.2.2.2
  have hzero : xiWardJuliaCrossDefect z w 0 = 0 := by
    simp [xiWardJuliaCrossDefect, xiWardSourcePhaseCrossRatio_zero, hzXi, hwXi]
  have hderiv :=
    hasDerivAt_xiWardJuliaCrossDefect_zero_eq_continuedCauchyKernel
      hzdom hwdom hzw
  have hjulia :
      Tendsto
        (fun x : ℝ => xiWardJuliaCrossDefect z w (x : ℂ) / (x : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 (ccmContinuedCauchyKernel z w)) := by
    simpa [hzero] using hasDerivAt_tendsto_real_slope_zero_right hderiv
  have hamp :=
    tendsto_gammaSewnSynchronizedSignedRecoveryAmplitude_sub_prod_singleton_div_sq_zero
      nu hnu P hP
  have hmain :
      Tendsto
        (fun x : ℝ =>
          ((gammaSewnSynchronizedSignedRecoveryAmplitude nu x P -
            ∏ p ∈ P, gammaSewnSynchronizedSignedRecoveryAmplitude nu x {p}) /
              (x : ℂ) ^ (2 : ℕ)) *
            (xiWardJuliaCrossDefect z w (x : ℂ) / (x : ℂ)))
        (𝓝[>] (0 : ℝ))
        (𝓝 ((Complex.ofReal ((-1 : ℝ) ^ P.card) *
          Complex.ofReal (-gammaSewnSynchronizedRecoveryQuadraticCrossAnomaly P / 2)) *
            ccmContinuedCauchyKernel z w)) :=
    hamp.mul hjulia
  apply hmain.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  field_simp [show (x : ℂ) ≠ 0 by exact_mod_cast hx.ne']

/-- The full source-level cross factor: the prime-log Cauchy boundary retains
the literal Rees source normalization, while its aperture-dependent component
is the synchronized chord factor. -/
def gammaSewnSynchronizedLcmReesCrossFactor
    (x : ℝ) (P : Finset Nat.Primes) : ℝ :=
  ((∏ p ∈ P, Real.log (p : ℝ)) / ∑ p ∈ P, Real.log (p : ℝ)) *
    gammaSewnSynchronizedRecoveryCrossFactor x P

/-- A singleton Rees-renormalized all-LCM source weight is its literal
Gamma-sewn multiplier divided by the physical prime factor. -/
theorem gammaSewnSynchronizedLcmReesRenormalizedWeight_singleton
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    gammaSewnSynchronizedLcmReesRenormalizedWeight x {p} =
      gammaSewnMobiusValuationContractionMultiplier x p / ((p : ℝ) + 1) := by
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hchord : 0 < exponentialChordFactor (x * Real.log (p : ℝ)) :=
    exponentialChordFactor_pos (mul_nonneg hx.le hlog.le)
  have hre := gammaSewnSynchronized_rees_chord_identity hx
    (P := ({p} : Finset Nat.Primes)) (by simp)
  simp only [Finset.prod_singleton, Finset.sum_singleton] at hre
  simp only [gammaSewnSynchronizedLcmReesBoundary,
    if_neg (by simp : ({p} : Finset Nat.Primes) ≠ ∅),
    Finset.prod_singleton, Finset.sum_singleton] at hre
  field_simp [hlog.ne', hchord.ne'] at hre ⊢
  linarith

/-- Exact coefficient-faithful all-LCM source assembly.  The non-product
prime-log boundary and the synchronized chord factor are both mandatory:
their product is exactly the ratio of the full Rees source weight to the
product of its singleton source weights. -/
theorem gammaSewnSynchronizedLcmReesRenormalizedWeight_eq_prod_singleton_mul_crossFactor
    {x : ℝ} (hx : 0 < x) {P : Finset Nat.Primes} (hP : P.Nonempty) :
    gammaSewnSynchronizedLcmReesRenormalizedWeight x P =
      (∏ p ∈ P, gammaSewnSynchronizedLcmReesRenormalizedWeight x {p}) *
        gammaSewnSynchronizedLcmReesCrossFactor x P := by
  have hlog (p : Nat.Primes) : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hsum : 0 < ∑ p ∈ P, Real.log (p : ℝ) :=
    Finset.sum_pos (fun p hp ↦ hlog p) hP
  have hchord : 0 < exponentialChordFactor
      (x * ∑ p ∈ P, Real.log (p : ℝ)) :=
    exponentialChordFactor_pos (mul_nonneg hx.le hsum.le)
  apply (mul_right_cancel₀ hchord.ne')
  rw [gammaSewnSynchronized_rees_chord_identity hx hP]
  simp_rw [gammaSewnSynchronizedLcmReesRenormalizedWeight_singleton hx]
  simp only [gammaSewnSynchronizedLcmReesCrossFactor,
    gammaSewnSynchronizedRecoveryCrossFactor,
    gammaSewnSynchronizedLcmReesBoundary, if_neg hP.ne_empty]
  rw [Finset.prod_mul_distrib]
  have hchord' : exponentialChordFactor
      ((∑ p ∈ P, Real.log (p : ℝ)) * x) ≠ 0 := by
    rw [mul_comm]
    exact hchord.ne'
  have hprod :
      (∏ p ∈ P, Real.log (p : ℝ) / ((p : ℝ) + 1)) *
          ∏ p ∈ P, gammaSewnMobiusValuationContractionMultiplier x p =
        (∏ p ∈ P, gammaSewnMobiusValuationContractionMultiplier x p / ((p : ℝ) + 1)) *
          ∏ p ∈ P, Real.log (p : ℝ) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    ring
  field_simp [hsum.ne', hchord.ne', hchord']
  rw [hprod]
  ring

end

end RHTower
