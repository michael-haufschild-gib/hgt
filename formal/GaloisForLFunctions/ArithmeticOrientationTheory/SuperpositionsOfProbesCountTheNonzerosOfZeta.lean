import GaloisForLFunctions.ArithmeticOrientationTheory.TheMoebiusReceiverCountsItsOffLineZeros
import GaloisForLFunctions.ArithmeticOrientationTheory.TheCalculusOfTheObstructionHull

/-!
# Superpositions of probes count the nonzeros of `ζ`

Take finitely many probes `d^{−ε_i} cos(t_i log d)` with `0 < ε_i < ½`, `t_i ≥ 0`, distinct
parameters, and real weights `a_i ≠ 0`; write `ρ_i = 1 − ε_i + i t_i`.  For the superposition
`c = Σ a_i d^{−ε_i} cos(t_i log d)`:

* **No cancellation** (`receiverBounded_probeSum_iff`): `c` is paid iff every `ρ_i` is a zero of `ζ`.
  The obstructions of different probes cannot repair one another.
* **The repairing ideal** (`mem_paidIdeal_probeSum_iff`): `k` repairs `c` iff `k̂` vanishes at `ρ_i`
  and `ρ̄_i` for every `i` with `ζ(ρ_i) ≠ 0`.
* **The count** (`finrank_quotient_paidIdeal_probeSum`, `finrank_add_card_real_probeSum`): the
  codimension of the repairing ideal is the number of these points, `2·#{i : ζ(ρ_i) ≠ 0}` minus the
  number of real ones.  The receiver index of a superposition counts the probe points off the zeros.

Mechanism: a kernel vanishing at the other probes' points but not at `ρ_j` repairs the rest of the
sum (`exists_repair_rest`), so any repair of `c` also repairs the `j`-th probe alone.
-/

open Finset ArithmeticFunction LSeries Complex

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open TransHorizonIncidenceMechanics WienerAlgebraAt

noncomputable section
set_option autoImplicit false

/-! ### Finite sums of weights -/

theorem dirichletConv_finset_sum {ι : Type*} (s : Finset ι) (f : ℕ → ℝ) (c : ι → ℕ → ℝ) :
    RHTower.dirichletConv f (fun d => ∑ i ∈ s, c i d) =
      fun n => ∑ i ∈ s, RHTower.dirichletConv f (c i) n := by
  funext n
  unfold RHTower.dirichletConv
  simp only [mul_sum]
  rw [Finset.sum_comm]

theorem receiverBounded_finset_sum {ι : Type*} (s : Finset ι) {g : ι → ℕ → ℝ}
    (hs : ∀ i ∈ s, Summable fun d : ℕ => g i d / d) (hg : ∀ i ∈ s, ReceiverBounded (g i)) :
    ReceiverBounded fun d => ∑ i ∈ s, g i d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using receiverBounded_zero
  | @insert a s ha ih =>
    simp only [sum_insert ha]
    refine receiverBounded_add (hs a (mem_insert_self a s)) ?_ (hg a (mem_insert_self a s))
      (ih (fun i hi => hs i (mem_insert_of_mem hi)) fun i hi => hg i (mem_insert_of_mem hi))
    exact (summable_sum fun i hi => hs i (mem_insert_of_mem hi)).congr fun d => (sum_div ..).symm

theorem summable_abs_finset_sum_div {ι : Type*} (s : Finset ι) {c : ι → ℕ → ℝ}
    (hc : ∀ i, Summable fun d : ℕ => |c i d / d|) :
    Summable fun d : ℕ => |(∑ i ∈ s, c i d) / d| :=
  (summable_sum fun i _ => hc i).of_nonneg_of_le (fun _ => abs_nonneg _) fun d => by
    rw [sum_div]; exact abs_sum_le_sum_abs _ _

/-- A kernel repairing every summand repairs the sum. -/
theorem mem_paidIdeal_finset_sum {ι : Type*} (s : Finset ι) {c : ι → ℕ → ℝ}
    (hc : ∀ i, Summable fun d : ℕ => |c i d / d|) {k : WienerAlgebraAt (1 / 2)}
    (hk : ∀ i ∈ s, k ∈ paidIdeal (c i) (hc i)) :
    k ∈ paidIdeal (fun d => ∑ i ∈ s, c i d) (summable_abs_finset_sum_div s hc) := by
  rw [mem_paidIdeal, dirichletConv_finset_sum, dirichletConv_finset_sum]
  refine ⟨receiverBounded_finset_sum s (fun i _ =>
      (summable_abs_dirichletConv_div (criticalWiener_rePart k) (hc i)).of_abs) fun i hi =>
      ((mem_paidIdeal _ _).1 (hk i hi)).1,
    receiverBounded_finset_sum s (fun i _ =>
      (summable_abs_dirichletConv_div (criticalWiener_imPart k) (hc i)).of_abs) fun i hi =>
      ((mem_paidIdeal _ _).1 (hk i hi)).2⟩

/-- A kernel repairing `c` and `c'` repairs `c − c'`. -/
theorem mem_paidIdeal_sub {c c' : ℕ → ℝ} (hc : Summable fun d : ℕ => |c d / d|)
    (hc' : Summable fun d : ℕ => |c' d / d|) (hcc : Summable fun d : ℕ => |(c d - c' d) / d|)
    {k : WienerAlgebraAt (1 / 2)} (hk : k ∈ paidIdeal c hc) (hk' : k ∈ paidIdeal c' hc') :
    k ∈ paidIdeal (fun d => c d - c' d) hcc := by
  have h2 : k ∈ paidIdeal (fun n => -1 * c' n) (summable_abs_smul_div hc' (-1)) := by
    rw [paidIdeal_smul hc' (by norm_num)]; exact hk'
  have h3 := paidIdeal_inf_le_add hc (summable_abs_smul_div hc' (-1)) (Submodule.mem_inf.2 ⟨hk, h2⟩)
  exact (mem_paidIdeal_congr (funext fun n => by ring) _ hcc _).1 h3

theorem dirichletConv_smul_right (f c : ℕ → ℝ) (t : ℝ) :
    RHTower.dirichletConv f (fun n => t * c n) = fun n => t * RHTower.dirichletConv f c n := by
  funext n; unfold RHTower.dirichletConv; rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring

/-- A repair of `c` repairs every multiple `t c`. -/
theorem mem_paidIdeal_smul_of_mem {c : ℕ → ℝ} (hc : Summable fun d : ℕ => |c d / d|) (t : ℝ)
    {k : WienerAlgebraAt (1 / 2)} (hk : k ∈ paidIdeal c hc) :
    k ∈ paidIdeal (fun n => t * c n) (summable_abs_smul_div hc t) := by
  by_cases ht : t = 0
  · subst ht
    rw [mem_paidIdeal, dirichletConv_smul_right, dirichletConv_smul_right]
    simp only [zero_mul]
    exact ⟨receiverBounded_zero, receiverBounded_zero⟩
  · rw [paidIdeal_smul hc ht]; exact hk

/-! ### Separating half-plane points -/

theorem bohrCharacter_pointMass_sub {ω : BohrPoint} {p : ℕ} (hp : p ≠ 0) (z : ℂ) :
    bohrEval (1 / 2) (pointMass p - z • (1 : WienerAlgebraAt (1 / 2))).toFn ω =
      ω.ω p / (p : ℂ) ^ ((1 / 2 : ℝ) : ℂ) - z := by
  rw [← WienerAlgebraAt.bohrCharacter_apply, map_sub, map_smul, _root_.map_one,
    WienerAlgebraAt.bohrCharacter_apply, toFn_pointMass, bohrEval_pointMass hp, smul_eq_mul, mul_one]

/-- Distinct half-plane points are separated by a kernel vanishing at the first. -/
theorem exists_separating {s s' : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) (hs' : (1 / 2 : ℝ) ≤ s'.re)
    (hne : s ≠ s') : ∃ f : WienerAlgebraAt (1 / 2),
      bohrEval (1 / 2) f.toFn (halfPlanePoint (1 / 2) s hs) = 0 ∧
        bohrEval (1 / 2) f.toFn (halfPlanePoint (1 / 2) s' hs') ≠ 0 := by
  have key : ∀ p : ℕ, p ≠ 0 → (halfPlanePoint (1 / 2) s hs).ω p ≠
      (halfPlanePoint (1 / 2) s' hs').ω p → ∃ f : WienerAlgebraAt (1 / 2),
        bohrEval (1 / 2) f.toFn (halfPlanePoint (1 / 2) s hs) = 0 ∧
          bohrEval (1 / 2) f.toFn (halfPlanePoint (1 / 2) s' hs') ≠ 0 := by
    intro p hp hpne
    have hp0 : (p : ℂ) ^ ((1 / 2 : ℝ) : ℂ) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; exact fun h => hp (by exact_mod_cast h.1)
    refine ⟨pointMass p - ((halfPlanePoint (1 / 2) s hs).ω p / (p : ℂ) ^ ((1 / 2 : ℝ) : ℂ)) • 1,
      ?_, ?_⟩
    · rw [bohrCharacter_pointMass_sub hp, sub_self]
    · rw [bohrCharacter_pointMass_sub hp, sub_ne_zero]
      exact fun h => hpne ((div_left_inj' hp0).1 h).symm
  by_cases h2 : (halfPlanePoint (1 / 2) s hs).ω 2 = (halfPlanePoint (1 / 2) s' hs').ω 2
  · by_cases h3 : (halfPlanePoint (1 / 2) s hs).ω 3 = (halfPlanePoint (1 / 2) s' hs').ω 3
    · exact absurd (eq_of_halfPlanePoint_two_three hs hs' h2 h3) hne
    · exact key 3 three_ne_zero h3
  · exact key 2 two_ne_zero h2

/-! ### Superpositions of probes -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Σ a_i d^{−ε_i} cos(t_i log d)`. -/
def probeSum (a ε t : ι → ℝ) (d : ℕ) : ℝ := ∑ i, a i * oscillatingSmoothPower (ε i) (t i) d

theorem summable_abs_scaledProbe_div (a : ℝ) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Summable fun d : ℕ => |a * oscillatingSmoothPower ε t d / d| :=
  summable_abs_smul_div (summable_abs_oscillatingSmoothPower_div hε t) a

omit [DecidableEq ι] in
theorem summable_abs_probeSum_div (a ε t : ι → ℝ) (hε : ∀ i, 0 < ε i) :
    Summable fun d : ℕ => |probeSum a ε t d / d| :=
  summable_abs_finset_sum_div univ fun i => summable_abs_scaledProbe_div (a i) (hε i) (t i)

theorem half_le_re_conj_osc {ε : ℝ} (hε2 : ε < 1 / 2) (t : ℝ) :
    (1 / 2 : ℝ) ≤ (starRingEnd ℂ (oscillationExponent ε t)).re :=
  half_le_re_conj_oscillationExponent hε2 t

/-- Probe points with `t ≥ 0` and distinct parameters are distinct and not conjugate. -/
theorem oscillationExponent_ne {ε ε' t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t')
    (hne : (ε, t) ≠ (ε', t')) :
    oscillationExponent ε t ≠ oscillationExponent ε' t' ∧
      oscillationExponent ε t ≠ starRingEnd ℂ (oscillationExponent ε' t') := by
  have hre : ∀ {z w : ℂ}, z = w → z.re = w.re ∧ z.im = w.im := fun h => ⟨by rw [h], by rw [h]⟩
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := hre h
    simp [oscillationExponent] at h1 h2
    exact hne (Prod.ext (by linarith) h2)
  · intro h
    obtain ⟨h1, h2⟩ := hre h
    simp [oscillationExponent] at h1 h2
    exact hne (Prod.ext (by linarith) (by linarith))

theorem probe_paid_of_zero {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (t : ℝ)
    (hz : riemannZeta (oscillationExponent ε t) = 0) (k : WienerAlgebraAt (1 / 2)) :
    k ∈ paidIdeal (oscillatingSmoothPower ε t) (summable_abs_oscillatingSmoothPower_div hε t) := by
  rw [mem_paidIdeal]
  exact ⟨(receiverBounded_dirichletConv_oscillatingSmoothPower_iff hε hε2 t
      (criticalWiener_rePart k)).2 (Or.inr hz),
    (receiverBounded_dirichletConv_oscillatingSmoothPower_iff hε hε2 t
      (criticalWiener_imPart k)).2 (Or.inr hz)⟩

/-- **Repairing the rest**: for a point `s` distinct from the points of all probes `i ≠ j`, some kernel
repairs every probe `i ≠ j` and does not vanish at `s`. -/
theorem exists_repair_rest {a ε t : ι → ℝ} (hε : ∀ i, 0 < ε i) (hε2 : ∀ i, ε i < 1 / 2) (j : ι)
    {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re)
    (hsρ : ∀ i, i ≠ j → s ≠ oscillationExponent (ε i) (t i) ∧
      s ≠ starRingEnd ℂ (oscillationExponent (ε i) (t i))) :
    ∃ k' : WienerAlgebraAt (1 / 2), (∀ i, i ≠ j → k' ∈ paidIdeal (fun d => a i *
        oscillatingSmoothPower (ε i) (t i) d) (summable_abs_scaledProbe_div (a i) (hε i) (t i))) ∧
      bohrEval (1 / 2) k'.toFn (halfPlanePoint (1 / 2) s hs) ≠ 0 := by
  have he : ∀ i, ∃ e : WienerAlgebraAt (1 / 2), i ≠ j →
      e ∈ paidIdeal (oscillatingSmoothPower (ε i) (t i))
        (summable_abs_oscillatingSmoothPower_div (hε i) (t i)) ∧
      bohrEval (1 / 2) e.toFn (halfPlanePoint (1 / 2) s hs) ≠ 0 := by
    intro i
    by_cases hij : i = j
    · exact ⟨1, fun h => absurd hij h⟩
    by_cases hz : riemannZeta (oscillationExponent (ε i) (t i)) = 0
    · refine ⟨1, fun _ => ⟨probe_paid_of_zero (hε i) (hε2 i) (t i) hz 1, ?_⟩⟩
      rw [← WienerAlgebraAt.bohrCharacter_apply, _root_.map_one]; exact one_ne_zero
    obtain ⟨f₁, hf₁, hf₁'⟩ := exists_separating (half_le_re_oscillationExponent (hε2 i) (t i)) hs
      (hsρ i hij).1.symm
    obtain ⟨f₂, hf₂, hf₂'⟩ := exists_separating (half_le_re_conj_osc (hε2 i) (t i)) hs
      (hsρ i hij).2.symm
    refine ⟨f₁ * f₂, fun _ => ⟨?_, ?_⟩⟩
    · rw [mem_paidIdeal_oscillating_iff (hε i) (hε2 i) hz, ← WienerAlgebraAt.bohrCharacter_apply,
        ← WienerAlgebraAt.bohrCharacter_apply, _root_.map_mul, _root_.map_mul,
        WienerAlgebraAt.bohrCharacter_apply, WienerAlgebraAt.bohrCharacter_apply,
        WienerAlgebraAt.bohrCharacter_apply, WienerAlgebraAt.bohrCharacter_apply]
      exact ⟨by rw [oscPoint, hf₁, zero_mul], by rw [oscPointConj, hf₂, mul_zero]⟩
    · rw [← WienerAlgebraAt.bohrCharacter_apply, _root_.map_mul, WienerAlgebraAt.bohrCharacter_apply,
        WienerAlgebraAt.bohrCharacter_apply]
      exact mul_ne_zero hf₁' hf₂'
  choose e he using he
  refine ⟨∏ i ∈ univ.erase j, e i, fun i hij => ?_, ?_⟩
  · refine mem_paidIdeal_smul_of_mem (summable_abs_oscillatingSmoothPower_div (hε i) (t i)) (a i) ?_
    rw [← Finset.mul_prod_erase (univ.erase j) e (mem_erase.2 ⟨hij, mem_univ i⟩)]
    exact Ideal.mul_mem_right _ _ (he i hij).1
  · rw [← WienerAlgebraAt.bohrCharacter_apply, map_prod]
    exact Finset.prod_ne_zero_iff.2 fun i hi => by
      rw [WienerAlgebraAt.bohrCharacter_apply]; exact (he i (ne_of_mem_erase hi)).2

theorem conj_oscillationExponent_ne {ε ε' t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t')
    (hne : (ε, t) ≠ (ε', t')) :
    starRingEnd ℂ (oscillationExponent ε t) ≠ oscillationExponent ε' t' ∧
      starRingEnd ℂ (oscillationExponent ε t) ≠ starRingEnd ℂ (oscillationExponent ε' t') := by
  obtain ⟨h1, h2⟩ := oscillationExponent_ne ht ht' hne
  obtain ⟨h1', h2'⟩ := oscillationExponent_ne ht' ht (Ne.symm hne)
  refine ⟨fun h => h2' ?_, fun h => h1 ?_⟩
  · exact h.symm
  · simpa using congrArg (starRingEnd ℂ) h

variable (a ε t : ι → ℝ)

/-- **The repairing ideal of a superposition**: `k` repairs `Σ a_i d^{−ε_i} cos(t_i log d)` iff `k̂`
vanishes at `ρ_i` and `ρ̄_i` whenever `ζ(ρ_i) ≠ 0`. -/
theorem mem_paidIdeal_probeSum_iff (hε : ∀ i, 0 < ε i) (hε2 : ∀ i, ε i < 1 / 2)
    (ht : ∀ i, 0 ≤ t i) (hinj : Function.Injective fun i => (ε i, t i)) (ha : ∀ i, a i ≠ 0)
    (k : WienerAlgebraAt (1 / 2)) :
    k ∈ paidIdeal (probeSum a ε t) (summable_abs_probeSum_div a ε t hε) ↔
      ∀ i, riemannZeta (oscillationExponent (ε i) (t i)) ≠ 0 →
        bohrEval (1 / 2) k.toFn (oscPoint (ε i) (t i) (hε2 i)) = 0 ∧
          bohrEval (1 / 2) k.toFn (oscPointConj (ε i) (t i) (hε2 i)) = 0 := by
  constructor
  · intro hk j hz
    have hsplit : (fun d => probeSum a ε t d -
        ∑ i ∈ univ.erase j, a i * oscillatingSmoothPower (ε i) (t i) d) =
        fun d => a j * oscillatingSmoothPower (ε j) (t j) d := funext fun d => by
      unfold probeSum; rw [← add_sum_erase _ _ (mem_univ j)]; ring
    have hcc : Summable fun d : ℕ => |(probeSum a ε t d -
        ∑ i ∈ univ.erase j, a i * oscillatingSmoothPower (ε i) (t i) d) / d| := by
      rw [show (fun d : ℕ => |(probeSum a ε t d - ∑ i ∈ univ.erase j,
          a i * oscillatingSmoothPower (ε i) (t i) d) / d|) =
          fun d : ℕ => |a j * oscillatingSmoothPower (ε j) (t j) d / d| from
        funext fun d => by rw [congrFun hsplit d]]
      exact summable_abs_scaledProbe_div (a j) (hε j) (t j)
    -- Any point of the `j`-th probe off the other probes' points is killed by every repair.
    have step : ∀ (s : ℂ) (hs : (1 / 2 : ℝ) ≤ s.re),
        (∀ i, i ≠ j → s ≠ oscillationExponent (ε i) (t i) ∧
          s ≠ starRingEnd ℂ (oscillationExponent (ε i) (t i))) →
        (∀ k₁ ∈ paidIdeal (oscillatingSmoothPower (ε j) (t j))
            (summable_abs_oscillatingSmoothPower_div (hε j) (t j)),
          bohrEval (1 / 2) k₁.toFn (halfPlanePoint (1 / 2) s hs) = 0) →
        bohrEval (1 / 2) k.toFn (halfPlanePoint (1 / 2) s hs) = 0 := by
      intro s hs hsρ hvan
      obtain ⟨k', hk', hne⟩ := exists_repair_rest (a := a) (t := t) hε hε2 j hs hsρ
      have h1 : k * k' ∈ paidIdeal (probeSum a ε t) (summable_abs_probeSum_div a ε t hε) :=
        Ideal.mul_mem_right _ _ hk
      have h2 := mem_paidIdeal_finset_sum (univ.erase j)
        (fun i => summable_abs_scaledProbe_div (a i) (hε i) (t i))
        (k := k * k') fun i hi => Ideal.mul_mem_left _ _ (hk' i (ne_of_mem_erase hi))
      have h3 := mem_paidIdeal_sub _ _ hcc h1 h2
      rw [mem_paidIdeal_congr hsplit _ (summable_abs_scaledProbe_div (a j) (hε j) (t j)),
        paidIdeal_smul (summable_abs_oscillatingSmoothPower_div (hε j) (t j)) (ha j)] at h3
      have h4 := hvan _ h3
      rw [← WienerAlgebraAt.bohrCharacter_apply, _root_.map_mul,
        WienerAlgebraAt.bohrCharacter_apply, WienerAlgebraAt.bohrCharacter_apply] at h4
      exact (mul_eq_zero.1 h4).resolve_right hne
    refine ⟨step _ _ (fun i hij => oscillationExponent_ne (ht j) (ht i)
        fun h => hij (hinj h).symm) fun k₁ hk₁ =>
          ((mem_paidIdeal_oscillating_iff (hε j) (hε2 j) hz k₁).1 hk₁).1,
      step _ _ (fun i hij => conj_oscillationExponent_ne (ht j) (ht i)
        fun h => hij (hinj h).symm) fun k₁ hk₁ =>
          ((mem_paidIdeal_oscillating_iff (hε j) (hε2 j) hz k₁).1 hk₁).2⟩
  · intro hk
    refine mem_paidIdeal_finset_sum univ
      (fun i => summable_abs_scaledProbe_div (a i) (hε i) (t i)) fun i _ => ?_
    refine mem_paidIdeal_smul_of_mem (summable_abs_oscillatingSmoothPower_div (hε i) (t i)) (a i) ?_
    by_cases hz : riemannZeta (oscillationExponent (ε i) (t i)) = 0
    · exact probe_paid_of_zero (hε i) (hε2 i) (t i) hz k
    · exact (mem_paidIdeal_oscillating_iff (hε i) (hε2 i) hz k).2 (hk i hz)

/-- **No cancellation**: a finite superposition of probes is paid iff every probe point is a zero of
`ζ`. -/
theorem receiverBounded_probeSum_iff (hε : ∀ i, 0 < ε i) (hε2 : ∀ i, ε i < 1 / 2)
    (ht : ∀ i, 0 ≤ t i) (hinj : Function.Injective fun i => (ε i, t i)) (ha : ∀ i, a i ≠ 0) :
    ReceiverBounded (probeSum a ε t) ↔ ∀ i, riemannZeta (oscillationExponent (ε i) (t i)) = 0 := by
  rw [← one_mem_paidIdeal_iff _ (summable_abs_probeSum_div a ε t hε),
    mem_paidIdeal_probeSum_iff a ε t hε hε2 ht hinj ha]
  constructor
  · intro h i
    by_contra hz
    have := (h i hz).1
    rw [← WienerAlgebraAt.bohrCharacter_apply, _root_.map_one] at this
    exact one_ne_zero this
  · intro h i hz
    exact absurd (h i) hz

/-! ### The count -/

/-- The probe points off the zeros of `ζ`, with their conjugates. -/
def probePoints : Finset ℂ :=
  ((univ.filter fun i => riemannZeta (oscillationExponent (ε i) (t i)) ≠ 0).image
      fun i => oscillationExponent (ε i) (t i)) ∪
    ((univ.filter fun i => riemannZeta (oscillationExponent (ε i) (t i)) ≠ 0).image
      fun i => starRingEnd ℂ (oscillationExponent (ε i) (t i)))

omit [DecidableEq ι] in
theorem half_le_re_of_mem_probePoints (hε2 : ∀ i, ε i < 1 / 2) {s : ℂ}
    (hs : s ∈ probePoints ε t) : (1 / 2 : ℝ) ≤ s.re := by
  simp only [probePoints, mem_union, mem_image, mem_filter, mem_univ, true_and] at hs
  rcases hs with ⟨i, -, rfl⟩ | ⟨i, -, rfl⟩
  · exact half_le_re_oscillationExponent (hε2 i) (t i)
  · exact half_le_re_conj_osc (hε2 i) (t i)

/-- **The count**: the repairing ideal of a superposition has codimension equal to the number of
probe points off the zeros of `ζ` (with conjugates). -/
theorem finrank_quotient_paidIdeal_probeSum (hε : ∀ i, 0 < ε i) (hε2 : ∀ i, ε i < 1 / 2)
    (ht : ∀ i, 0 ≤ t i) (hinj : Function.Injective fun i => (ε i, t i)) (ha : ∀ i, a i ≠ 0) :
    Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
      paidIdeal (probeSum a ε t) (summable_abs_probeSum_div a ε t hε)) = (probePoints ε t).card := by
  classical
  let χ : probePoints ε t → WienerAlgebraAt (1 / 2) →ₐ[ℂ] ℂ := fun s =>
    WienerAlgebraAt.bohrCharacter (1 / 2)
      (halfPlanePoint (1 / 2) s.1 (half_le_re_of_mem_probePoints ε t hε2 s.2))
  have hsep : ∀ s s', s ≠ s' → ∃ f, χ s f ≠ χ s' f := fun s s' hne => by
    obtain ⟨f, hf, hf'⟩ := exists_separating (half_le_re_of_mem_probePoints ε t hε2 s.2)
      (half_le_re_of_mem_probePoints ε t hε2 s'.2) fun h => hne (Subtype.ext h)
    refine ⟨f, ?_⟩
    simp only [χ, WienerAlgebraAt.bohrCharacter_apply, hf]
    exact Ne.symm hf'
  have hker : paidIdeal (probeSum a ε t) (summable_abs_probeSum_div a ε t hε) =
      RingHom.ker (AlgHom.pi χ) := by
    ext k
    rw [mem_paidIdeal_probeSum_iff a ε t hε hε2 ht hinj ha, RingHom.mem_ker]
    constructor
    · intro h
      funext s
      obtain ⟨s, hs⟩ := s
      have hs' := hs
      simp only [probePoints, mem_union, mem_image, mem_filter, mem_univ, true_and] at hs'
      rw [AlgHom.pi_apply]
      simp only [χ, WienerAlgebraAt.bohrCharacter_apply, Pi.zero_apply]
      rcases hs' with ⟨i, hz, rfl⟩ | ⟨i, hz, rfl⟩
      · exact (h i hz).1
      · exact (h i hz).2
    · intro h i hz
      have hm1 : oscillationExponent (ε i) (t i) ∈ probePoints ε t := by
        simp only [probePoints, mem_union, mem_image, mem_filter, mem_univ, true_and]
        exact Or.inl ⟨i, hz, rfl⟩
      have hm2 : starRingEnd ℂ (oscillationExponent (ε i) (t i)) ∈ probePoints ε t := by
        simp only [probePoints, mem_union, mem_image, mem_filter, mem_univ, true_and]
        exact Or.inr ⟨i, hz, rfl⟩
      have e1 := congrFun h ⟨_, hm1⟩
      have e2 := congrFun h ⟨_, hm2⟩
      rw [AlgHom.pi_apply] at e1 e2
      simp only [χ, WienerAlgebraAt.bohrCharacter_apply, Pi.zero_apply] at e1 e2
      exact ⟨e1, e2⟩
  rw [hker, (Ideal.quotientKerAlgEquivOfSurjective
      (surjective_pi_algHom_of_separated χ hsep)).toLinearEquiv.finrank_eq,
    Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

/-- **In terms of the probes**: the codimension plus the number of real probe points off the zeros
is twice the number of probe points off the zeros. -/
theorem card_probePoints_add (ht : ∀ i, 0 ≤ t i) (hinj : Function.Injective fun i => (ε i, t i)) :
    (probePoints ε t).card +
        (univ.filter fun i => riemannZeta (oscillationExponent (ε i) (t i)) ≠ 0 ∧ t i = 0).card =
      2 * (univ.filter fun i => riemannZeta (oscillationExponent (ε i) (t i)) ≠ 0).card := by
  classical
  unfold probePoints
  set Z := univ.filter fun i => riemannZeta (oscillationExponent (ε i) (t i)) ≠ 0
  have hρinj : Set.InjOn (fun i => oscillationExponent (ε i) (t i)) Z := fun i _ j _ h => by
    by_contra hij
    exact (oscillationExponent_ne (ht i) (ht j) fun h' => hij (hinj h')).1 h
  have hcinj : Set.InjOn (fun i => starRingEnd ℂ (oscillationExponent (ε i) (t i))) Z :=
    fun i _ j _ h => by
      by_contra hij
      exact (conj_oscillationExponent_ne (ht i) (ht j) fun h' => hij (hinj h')).2 h
  have hinter : (Z.image fun i => oscillationExponent (ε i) (t i)) ∩
      (Z.image fun i => starRingEnd ℂ (oscillationExponent (ε i) (t i))) =
      (univ.filter fun i => riemannZeta (oscillationExponent (ε i) (t i)) ≠ 0 ∧ t i = 0).image
        fun i => oscillationExponent (ε i) (t i) := by
    ext s
    simp only [Z, mem_inter, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, ⟨j, hj, hji⟩⟩
      have hij : i = j := by
        by_contra hij
        exact (oscillationExponent_ne (ht i) (ht j) fun h' => hij (hinj h')).2 hji.symm
      subst hij
      have him := congrArg Complex.im hji
      simp [oscillationExponent] at him
      exact ⟨i, ⟨hi, by linarith⟩, rfl⟩
    · rintro ⟨i, ⟨hi, hti⟩, rfl⟩
      refine ⟨⟨i, hi, rfl⟩, ⟨i, hi, ?_⟩⟩
      simp [oscillationExponent, hti, Complex.conj_ofReal]
  have h := card_union_add_card_inter (Z.image fun i => oscillationExponent (ε i) (t i))
    (Z.image fun i => starRingEnd ℂ (oscillationExponent (ε i) (t i)))
  rw [hinter, card_image_of_injOn hρinj, card_image_of_injOn hcinj,
    card_image_of_injOn (hρinj.mono fun i hi => by
      simp only [Z, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢; exact hi.1)] at h
  omega

end

end GaloisForLFunctions.ArithmeticOrientationTheory
