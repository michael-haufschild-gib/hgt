import Mathlib
import GaloisForLFunctions.HTGeometry.FiniteAmplifierFrame

/-!
# The graph-world witness: a 3-regular prism violating the Ramanujan bound

The inverse-theory independence metatheorem needs a concrete structure satisfying the
graph-world analogues of the no-go-derived axioms whose RH-conclusion fails.  This module
certifies the witness: the prism over the 16-cycle (`C₁₆ × K₂`, 3-regular on 32 vertices)
carries the explicit mean-zero cosine vector

`v(j, s) = cos(2πj/16)`

whose Rayleigh quotient against the adjacency operator is exactly `2cos(π/8) + 1`, and

`2cos(π/8) + 1 > 2√2 = 2√(d−1)`

by pure algebra (`√(2+√2) > 2√2 − 1 ⟺ 5√2 > 7 ⟺ 50 > 49`).  A poorly expanding
3-regular graph therefore has spectral mass strictly beyond the Ramanujan bound on the
mean-zero sector; the Ihara RH-analogue fails while the finite-trace axioms hold.

The sampled-cosine sums are evaluated by the discrete root-of-unity averaging of
`HTGeometry.FiniteAmplifierFrame`; no numerical computation enters.
-/

namespace RHTower

noncomputable section

open Finset Real

/-- The prism vertex set: the 16-cycle times an edge. -/
abbrev PrismV : Type := ZMod 16 × Bool

/-- The prism adjacency relation: cycle steps on the first coordinate, one rung on the
second. -/
def prismRel (p q : PrismV) : Prop :=
  (p.2 = q.2 ∧ (q.1 = p.1 + 1 ∨ p.1 = q.1 + 1)) ∨ (p.1 = q.1 ∧ p.2 ≠ q.2)

theorem prismRel_symm : Std.Symm prismRel := by
  refine ⟨fun p q h => ?_⟩
  rcases h with ⟨hs, hj | hj⟩ | ⟨hj, hs⟩
  · exact Or.inl ⟨hs.symm, Or.inr hj⟩
  · exact Or.inl ⟨hs.symm, Or.inl hj⟩
  · exact Or.inr ⟨hj.symm, hs.symm⟩

theorem prismRel_irrefl : Std.Irrefl prismRel := by
  refine ⟨fun p h => ?_⟩
  rcases h with ⟨-, hj | hj⟩ | ⟨-, hs⟩
  · exact absurd (left_eq_add.mp hj) (by decide)
  · exact absurd (left_eq_add.mp hj) (by decide)
  · exact hs rfl

/-- The prism graph `C₁₆ × K₂`. -/
def prismAdj : SimpleGraph PrismV := ⟨prismRel, prismRel_symm, prismRel_irrefl⟩

/-- The three neighbors of a prism vertex, exactly. -/
theorem prismRel_iff (p q : PrismV) :
    prismRel p q ↔ q = (p.1 + 1, p.2) ∨ q = (p.1 - 1, p.2) ∨ q = (p.1, !p.2) := by
  constructor
  · rintro (⟨hs, hj | hj⟩ | ⟨hj, hs⟩)
    · left
      exact Prod.ext hj hs.symm
    · right; left
      refine Prod.ext ?_ hs.symm
      rw [hj]
      ring
    · right; right
      refine Prod.ext hj.symm ?_
      cases hp : p.2 <;> cases hq : q.2 <;> simp_all
  · rintro (rfl | rfl | rfl)
    · exact Or.inl ⟨rfl, Or.inl rfl⟩
    · refine Or.inl ⟨rfl, Or.inr ?_⟩
      ring
    · refine Or.inr ⟨rfl, ?_⟩
      cases p.2 <;> simp

instance : DecidableRel prismRel := fun p q => by
  unfold prismRel
  infer_instance

instance : DecidableRel prismAdj.Adj :=
  (inferInstance : DecidableRel prismRel)

/-- The prism is 3-regular. -/
theorem prismAdj_degree (p : PrismV) : (prismAdj.neighborFinset p).card = 3 := by
  classical
  have hset : prismAdj.neighborFinset p
      = {(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, !p.2)} := by
    ext q
    rw [SimpleGraph.mem_neighborFinset]
    rw [show prismAdj.Adj = prismRel from rfl, prismRel_iff]
    simp [Finset.mem_insert]
  rw [hset]
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp only [Finset.mem_singleton]
    intro hcontra
    have := congrArg Prod.snd hcontra
    simp at this
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    push Not
    constructor
    · intro hcontra
      have := congrArg Prod.fst hcontra
      simp only at this
      have h2 : (2 : ZMod 16) = 0 := by
        have : p.1 + 1 - (p.1 - 1) = 0 := by rw [this]; ring
        calc (2 : ZMod 16) = p.1 + 1 - (p.1 - 1) := by ring
          _ = 0 := this
      exact absurd h2 (by decide)
    · intro hcontra
      have := congrArg Prod.snd hcontra
      simp at this

/-! ## The cosine witness vector and its exact Rayleigh data -/

/-- The mean-zero cosine vector on the prism. -/
def prismVec (p : PrismV) : ℝ := Real.cos (2 * Real.pi * (p.1.val : ℝ) / 16)

/-- The adjacency sum of a function at a vertex. -/
def prismAdjSum (v : PrismV → ℝ) (p : PrismV) : ℝ :=
  v (p.1 + 1, p.2) + v (p.1 - 1, p.2) + v (p.1, !p.2)

/-- The adjacency energy `⟨Av, v⟩`. -/
def prismEnergy (v : PrismV → ℝ) : ℝ := ∑ p : PrismV, prismAdjSum v p * v p

/-- The squared norm `⟨v, v⟩`. -/
def prismNormSq (v : PrismV → ℝ) : ℝ := ∑ p : PrismV, v p ^ 2

private theorem cos_div16_mod (m : ℕ) :
    Real.cos (2 * Real.pi * ((m % 16 : ℕ) : ℝ) / 16) = Real.cos (2 * Real.pi * m / 16) := by
  have hm := Nat.div_add_mod m 16
  have harg : 2 * Real.pi * (m : ℝ) / 16
      = 2 * Real.pi * ((m % 16 : ℕ) : ℝ) / 16 + (m / 16 : ℕ) * (2 * Real.pi) := by
    have hcast : (m : ℝ) = 16 * ((m / 16 : ℕ) : ℝ) + ((m % 16 : ℕ) : ℝ) := by
      exact_mod_cast hm.symm
    rw [hcast]
    ring
  rw [harg]
  have := Real.cos_add_int_mul_two_pi
    (2 * Real.pi * ((m % 16 : ℕ) : ℝ) / 16) ((m / 16 : ℕ) : ℤ)
  rw [← this]
  norm_cast

private theorem prismVec_add_one (j : ZMod 16) (s : Bool) :
    prismVec (j + 1, s) = Real.cos (2 * Real.pi * ((j.val : ℝ) + 1) / 16) := by
  have hval : (j + 1).val = (j.val + 1) % 16 := by
    rw [ZMod.val_add, show ZMod.val (1 : ZMod 16) = 1 from by decide]
  unfold prismVec
  rw [hval, cos_div16_mod (j.val + 1)]
  push_cast
  rfl

private theorem prismVec_sub_one (j : ZMod 16) (s : Bool) :
    prismVec (j - 1, s) = Real.cos (2 * Real.pi * ((j.val : ℝ) + 15) / 16) := by
  have hsub : j - 1 = j + 15 := by
    rw [sub_eq_add_neg, show (-1 : ZMod 16) = 15 from by decide]
  have hval : (j + 15).val = (j.val + 15) % 16 := by
    rw [ZMod.val_add, show ZMod.val (15 : ZMod 16) = 15 from by decide]
  unfold prismVec
  rw [hsub, hval, cos_div16_mod (j.val + 15)]
  push_cast
  rfl

private theorem zmod_sum_eq_range (g : ℕ → ℝ) :
    ∑ j : ZMod 16, g j.val = ∑ j ∈ Finset.range 16, g j :=
  Fin.sum_univ_eq_sum_range (fun j => g j) 16

private theorem cos_mul_cos (a b : ℝ) :
    Real.cos a * Real.cos b = (Real.cos (a - b) + Real.cos (a + b)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]
  ring

/-- The full-period cosine sum at the fundamental frequency vanishes. -/
private theorem range16_cos_sum :
    ∑ j ∈ Finset.range 16, Real.cos (2 * Real.pi * (j : ℝ) / 16) = 0 := by
  have h := HTGeometry.cos_sample_sum_zero 16 1 (by omega) (by omega)
  calc ∑ j ∈ Finset.range 16, Real.cos (2 * Real.pi * (j : ℝ) / 16)
      = ∑ j ∈ Finset.range 16, Real.cos (2 * Real.pi * (1 : ℕ) * (j : ℝ) / 16) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        push_cast
        ring
    _ = 0 := h

/-- The squared-cosine sum over one period is `8`. -/
private theorem range16_cos_sq_sum :
    ∑ j ∈ Finset.range 16, Real.cos (2 * Real.pi * (j : ℝ) / 16) ^ 2 = 8 := by
  have h2 := HTGeometry.cos_sample_sum_zero 16 2 (by omega) (by omega)
  have hpt : ∀ j : ℕ, Real.cos (2 * Real.pi * (j : ℝ) / 16) ^ 2
      = 1 / 2 + Real.cos (2 * Real.pi * (2 : ℕ) * (j : ℝ) / 16) / 2 := by
    intro j
    have := Real.cos_sq (2 * Real.pi * (j : ℝ) / 16)
    rw [this]
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl fun j _ => hpt j, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range]
  have hdiv : ∑ j ∈ Finset.range 16, Real.cos (2 * Real.pi * (2 : ℕ) * (j : ℝ) / 16) / 2
      = (∑ j ∈ Finset.range 16, Real.cos (2 * Real.pi * (2 : ℕ) * (j : ℝ) / 16)) / 2 := by
    rw [← Finset.sum_div]
  rw [nsmul_eq_mul, hdiv]
  linear_combination h2 / 2

/-- The shifted-product cosine sum: `∑ cos(2π(m+k)/16)cos(2πm/16) = 8·cos(2πk/16)` for
`k` not killing the doubled frequency. -/
private theorem range16_cos_shift_sum (k : ℕ) :
    ∑ j ∈ Finset.range 16, Real.cos (2 * Real.pi * ((j : ℝ) + k) / 16)
        * Real.cos (2 * Real.pi * (j : ℝ) / 16)
      = 8 * Real.cos (2 * Real.pi * (k : ℝ) / 16) := by
  have hphase := HTGeometry.cos_sample_sum_zero_phase 16 2 (by omega) (by omega)
    (2 * Real.pi * (k : ℝ) / 16)
  have hpt : ∀ j : ℕ, Real.cos (2 * Real.pi * ((j : ℝ) + k) / 16)
        * Real.cos (2 * Real.pi * (j : ℝ) / 16)
      = Real.cos (2 * Real.pi * (k : ℝ) / 16) / 2
        + Real.cos (2 * Real.pi * (2 : ℕ) * (j : ℝ) / 16 + 2 * Real.pi * (k : ℝ) / 16) / 2 := by
    intro j
    rw [cos_mul_cos]
    have e1 : 2 * Real.pi * ((j : ℝ) + k) / 16 - 2 * Real.pi * (j : ℝ) / 16
        = 2 * Real.pi * (k : ℝ) / 16 := by ring
    have e2 : 2 * Real.pi * ((j : ℝ) + k) / 16 + 2 * Real.pi * (j : ℝ) / 16
        = 2 * Real.pi * (2 : ℕ) * (j : ℝ) / 16 + 2 * Real.pi * (k : ℝ) / 16 := by
      push_cast
      ring
    rw [e1, e2]
    ring
  rw [Finset.sum_congr rfl fun j _ => hpt j, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range]
  have hdiv : ∑ j ∈ Finset.range 16,
      Real.cos (2 * Real.pi * (2 : ℕ) * (j : ℝ) / 16 + 2 * Real.pi * (k : ℝ) / 16) / 2
      = (∑ j ∈ Finset.range 16,
          Real.cos (2 * Real.pi * (2 : ℕ) * (j : ℝ) / 16 + 2 * Real.pi * (k : ℝ) / 16)) / 2 := by
    rw [← Finset.sum_div]
  rw [nsmul_eq_mul, hdiv]
  linear_combination hphase / 2

/-! ## The exact Rayleigh data of the witness vector -/

theorem prismVec_mean_zero : ∑ p : PrismV, prismVec p = 0 := by
  rw [Fintype.sum_prod_type]
  have hj : ∀ j : ZMod 16, ∑ s : Bool, prismVec (j, s)
      = 2 * Real.cos (2 * Real.pi * (j.val : ℝ) / 16) := by
    intro j
    rw [Fintype.sum_bool]
    unfold prismVec
    ring
  rw [Finset.sum_congr rfl fun j _ => hj j, ← Finset.mul_sum]
  have := zmod_sum_eq_range (fun m => Real.cos (2 * Real.pi * (m : ℝ) / 16))
  rw [this, range16_cos_sum, mul_zero]

theorem prismNormSq_value : prismNormSq prismVec = 16 := by
  unfold prismNormSq
  rw [Fintype.sum_prod_type]
  have hj : ∀ j : ZMod 16, ∑ s : Bool, prismVec (j, s) ^ 2
      = 2 * Real.cos (2 * Real.pi * (j.val : ℝ) / 16) ^ 2 := by
    intro j
    rw [Fintype.sum_bool]
    unfold prismVec
    ring
  rw [Finset.sum_congr rfl fun j _ => hj j, ← Finset.mul_sum]
  have := zmod_sum_eq_range (fun m => Real.cos (2 * Real.pi * (m : ℝ) / 16) ^ 2)
  rw [this, range16_cos_sq_sum]
  norm_num

theorem prismEnergy_value :
    prismEnergy prismVec = 16 * (2 * Real.cos (Real.pi / 8) + 1) := by
  unfold prismEnergy
  rw [Fintype.sum_prod_type]
  have hj : ∀ j : ZMod 16, ∑ s : Bool, prismAdjSum prismVec (j, s) * prismVec (j, s)
      = 2 * ((Real.cos (2 * Real.pi * ((j.val : ℝ) + 1) / 16)
          + Real.cos (2 * Real.pi * ((j.val : ℝ) + 15) / 16)
          + Real.cos (2 * Real.pi * (j.val : ℝ) / 16))
        * Real.cos (2 * Real.pi * (j.val : ℝ) / 16)) := by
    intro j
    rw [Fintype.sum_bool]
    unfold prismAdjSum
    rw [prismVec_add_one j true, prismVec_sub_one j true,
      prismVec_add_one j false, prismVec_sub_one j false]
    unfold prismVec
    ring
  rw [Finset.sum_congr rfl fun j _ => hj j, ← Finset.mul_sum]
  have hzr := zmod_sum_eq_range (fun m =>
    (Real.cos (2 * Real.pi * ((m : ℝ) + 1) / 16) + Real.cos (2 * Real.pi * ((m : ℝ) + 15) / 16)
      + Real.cos (2 * Real.pi * (m : ℝ) / 16)) * Real.cos (2 * Real.pi * (m : ℝ) / 16))
  rw [hzr]
  have hsplit : ∑ j ∈ Finset.range 16,
      (Real.cos (2 * Real.pi * ((j : ℝ) + 1) / 16) + Real.cos (2 * Real.pi * ((j : ℝ) + 15) / 16)
        + Real.cos (2 * Real.pi * (j : ℝ) / 16)) * Real.cos (2 * Real.pi * (j : ℝ) / 16)
      = (∑ j ∈ Finset.range 16, Real.cos (2 * Real.pi * ((j : ℝ) + 1) / 16)
            * Real.cos (2 * Real.pi * (j : ℝ) / 16))
        + (∑ j ∈ Finset.range 16, Real.cos (2 * Real.pi * ((j : ℝ) + 15) / 16)
            * Real.cos (2 * Real.pi * (j : ℝ) / 16))
        + ∑ j ∈ Finset.range 16, Real.cos (2 * Real.pi * (j : ℝ) / 16) ^ 2 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsplit]
  have h1 := range16_cos_shift_sum 1
  have h15 := range16_cos_shift_sum 15
  have hc1 : Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) / 16) = Real.cos (Real.pi / 8) := by
    congr 1
    push_cast
    ring
  have hc15 : Real.cos (2 * Real.pi * ((15 : ℕ) : ℝ) / 16) = Real.cos (Real.pi / 8) := by
    have harg : 2 * Real.pi * ((15 : ℕ) : ℝ) / 16 = 2 * Real.pi - Real.pi / 8 := by
      push_cast
      ring
    rw [harg, Real.cos_two_pi_sub]
  have hsq := range16_cos_sq_sum
  push_cast at h1 h15 hc1 hc15
  linear_combination 2 * h1 + 2 * h15 + 2 * hsq + 16 * hc1 + 16 * hc15

/-- **The Ramanujan margin.**  `2cos(π/8) + 1 > 2√2`, by `cos²(π/8) = (2+√2)/4` and
`5√2 > 7 ⟺ 50 > 49`. -/
theorem prism_margin : 2 * Real.sqrt 2 < 2 * Real.cos (Real.pi / 8) + 1 := by
  have hcos_sq : Real.cos (Real.pi / 8) ^ 2 = (2 + Real.sqrt 2) / 4 := by
    have h := Real.cos_sq (Real.pi / 8)
    rw [show 2 * (Real.pi / 8) = Real.pi / 4 by ring, Real.cos_pi_div_four] at h
    rw [h]
    ring
  have hcos_pos : 0 < Real.cos (Real.pi / 8) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have := Real.pi_pos
      linarith
    · have := Real.pi_pos
      linarith
  have h75 : (7 / 5 : ℝ) < Real.sqrt 2 := by
    have h : ((7 / 5 : ℝ)) ^ 2 < 2 := by norm_num
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
      Real.sqrt_nonneg 2, sq_nonneg (Real.sqrt 2 - 7 / 5)]
  nlinarith [hcos_sq, hcos_pos, h75, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
    Real.sqrt_nonneg 2, sq_nonneg (2 * Real.cos (Real.pi / 8) - (2 * Real.sqrt 2 - 1))]

/-- **The graph-world witness (capstone).**  The prism `C₁₆ × K₂` is 3-regular, and its
mean-zero cosine vector has Rayleigh quotient exactly `2cos(π/8) + 1`, strictly beyond the
Ramanujan bound `2√(d−1) = 2√2`: the finite spectral axioms hold while the graph RH-analogue
fails.  No derivation of RH-grade positivity from the no-go axioms alone can exist. -/
theorem prism_rayleigh_witness :
    (∀ p : PrismV, (prismAdj.neighborFinset p).card = 3) ∧
    prismNormSq prismVec = 16 ∧ (∑ p : PrismV, prismVec p = 0) ∧
    prismEnergy prismVec = (2 * Real.cos (Real.pi / 8) + 1) * prismNormSq prismVec ∧
    2 * Real.sqrt 2 * prismNormSq prismVec < prismEnergy prismVec := by
  refine ⟨prismAdj_degree, prismNormSq_value, prismVec_mean_zero, ?_, ?_⟩
  · rw [prismEnergy_value, prismNormSq_value]
    ring
  · rw [prismEnergy_value, prismNormSq_value]
    nlinarith [prism_margin]

/-! ## The eigenvalue form of the witness -/

open scoped InnerProductSpace

/-- The prism vertex space as a Euclidean space. -/
abbrev PrismE : Type := EuclideanSpace ℝ PrismV

/-- Cycle shift up. -/
def shiftUp : PrismV ≃ PrismV :=
  (Equiv.addRight (1 : ZMod 16)).prodCongr (Equiv.refl Bool)

/-- Cycle shift down. -/
def shiftDown : PrismV ≃ PrismV := shiftUp.symm

/-- Rung flip. -/
def rungFlip : PrismV ≃ PrismV :=
  (Equiv.refl (ZMod 16)).prodCongr ⟨Bool.not, Bool.not, Bool.not_not, Bool.not_not⟩

theorem shiftUp_apply (p : PrismV) : shiftUp p = (p.1 + 1, p.2) := rfl

theorem shiftDown_apply (p : PrismV) : shiftDown p = (p.1 - 1, p.2) := by
  unfold shiftDown
  rw [Equiv.symm_apply_eq, shiftUp_apply]
  refine Prod.ext ?_ rfl
  show p.1 = p.1 - 1 + 1
  ring

theorem rungFlip_apply (p : PrismV) : rungFlip p = (p.1, !p.2) := rfl

theorem shiftUp_shiftDown (p : PrismV) : shiftUp (shiftDown p) = p :=
  shiftUp.apply_symm_apply p

theorem shiftDown_shiftUp (p : PrismV) : shiftDown (shiftUp p) = p :=
  shiftUp.symm_apply_apply p

theorem rungFlip_rungFlip (p : PrismV) : rungFlip (rungFlip p) = p := by
  rw [rungFlip_apply, rungFlip_apply]
  simp

/-- The prism adjacency operator on the Euclidean vertex space: precomposition with the
three neighbor translations. -/
def prismOp : PrismE →ₗ[ℝ] PrismE :=
  (WithLp.linearEquiv 2 ℝ (PrismV → ℝ)).symm.toLinearMap
    ∘ₗ (LinearMap.funLeft ℝ ℝ shiftUp + LinearMap.funLeft ℝ ℝ shiftDown
        + LinearMap.funLeft ℝ ℝ rungFlip)
    ∘ₗ (WithLp.linearEquiv 2 ℝ (PrismV → ℝ)).toLinearMap

theorem prismOp_apply (v : PrismE) (p : PrismV) :
    prismOp v p = v (shiftUp p) + v (shiftDown p) + v (rungFlip p) := rfl

/-- The Euclidean inner product on the vertex space is the coordinate sum. -/
theorem prism_inner_eq (v w : PrismE) : ⟪v, w⟫_ℝ = ∑ p : PrismV, v p * w p := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [RCLike.inner_apply]
  ring

private theorem sum_comp_equiv (e : PrismV ≃ PrismV) (f : PrismV → ℝ) :
    ∑ p : PrismV, f (e p) = ∑ p : PrismV, f p :=
  Fintype.sum_equiv e _ _ fun _ => rfl

private theorem sum_up_mul (v w : PrismE) :
    ∑ p : PrismV, v (shiftUp p) * w p = ∑ p : PrismV, v p * w (shiftDown p) :=
  Fintype.sum_equiv shiftUp _ _ fun p => by rw [shiftDown_shiftUp]

private theorem sum_down_mul (v w : PrismE) :
    ∑ p : PrismV, v (shiftDown p) * w p = ∑ p : PrismV, v p * w (shiftUp p) :=
  Fintype.sum_equiv shiftDown _ _ fun p => by rw [shiftUp_shiftDown]

private theorem sum_flip_mul (v w : PrismE) :
    ∑ p : PrismV, v (rungFlip p) * w p = ∑ p : PrismV, v p * w (rungFlip p) :=
  Fintype.sum_equiv rungFlip _ _ fun p => by rw [rungFlip_rungFlip]

/-- The prism operator is symmetric. -/
theorem prismOp_isSymmetric : (prismOp).IsSymmetric := by
  intro v w
  rw [prism_inner_eq, prism_inner_eq]
  have hexp1 : ∑ p : PrismV, prismOp v p * w p
      = (∑ p : PrismV, v (shiftUp p) * w p) + (∑ p : PrismV, v (shiftDown p) * w p)
        + ∑ p : PrismV, v (rungFlip p) * w p := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [prismOp_apply]
    ring
  have hexp2 : ∑ p : PrismV, v p * prismOp w p
      = (∑ p : PrismV, v p * w (shiftUp p)) + (∑ p : PrismV, v p * w (shiftDown p))
        + ∑ p : PrismV, v p * w (rungFlip p) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [prismOp_apply]
    ring
  rw [hexp1, hexp2, sum_up_mul, sum_down_mul, sum_flip_mul]
  ring

/-- The Laplacian square identity: `3⟨v,v⟩ − ⟨Av,v⟩` is the nonnegative edge-difference
energy. -/
theorem prism_laplacian_identity (v : PrismE) :
    3 * ⟪v, v⟫_ℝ - ⟪prismOp v, v⟫_ℝ
      = (∑ p : PrismV, (v p - v (shiftUp p)) ^ 2)
        + (1 / 2) * ∑ p : PrismV, (v p - v (rungFlip p)) ^ 2 := by
  rw [prism_inner_eq, prism_inner_eq]
  have hupsq : ∑ p : PrismV, v (shiftUp p) ^ 2 = ∑ p : PrismV, v p ^ 2 :=
    sum_comp_equiv shiftUp (fun q => v q ^ 2)
  have hflsq : ∑ p : PrismV, v (rungFlip p) ^ 2 = ∑ p : PrismV, v p ^ 2 :=
    sum_comp_equiv rungFlip (fun q => v q ^ 2)
  have hdn : ∑ p : PrismV, v (shiftDown p) * v p = ∑ p : PrismV, v (shiftUp p) * v p := by
    rw [sum_down_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  have hexpA : ∑ p : PrismV, prismOp v p * v p
      = 2 * (∑ p : PrismV, v (shiftUp p) * v p) + ∑ p : PrismV, v (rungFlip p) * v p := by
    have h1 : ∑ p : PrismV, prismOp v p * v p
        = (∑ p : PrismV, v (shiftUp p) * v p) + (∑ p : PrismV, v (shiftDown p) * v p)
          + ∑ p : PrismV, v (rungFlip p) * v p := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [prismOp_apply]
      ring
    rw [h1, hdn]
    ring
  have hsq1 : ∑ p : PrismV, (v p - v (shiftUp p)) ^ 2
      = 2 * (∑ p : PrismV, v p ^ 2) - 2 * ∑ p : PrismV, v (shiftUp p) * v p := by
    calc ∑ p : PrismV, (v p - v (shiftUp p)) ^ 2
        = ∑ p : PrismV, (v p ^ 2 + v (shiftUp p) ^ 2 - 2 * (v (shiftUp p) * v p)) :=
          Finset.sum_congr rfl fun p _ => by ring
      _ = (∑ p : PrismV, (v p ^ 2 + v (shiftUp p) ^ 2))
          - ∑ p : PrismV, 2 * (v (shiftUp p) * v p) := by rw [Finset.sum_sub_distrib]
      _ = 2 * (∑ p : PrismV, v p ^ 2) - 2 * ∑ p : PrismV, v (shiftUp p) * v p := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hupsq]
          ring
  have hsq2 : ∑ p : PrismV, (v p - v (rungFlip p)) ^ 2
      = 2 * (∑ p : PrismV, v p ^ 2) - 2 * ∑ p : PrismV, v (rungFlip p) * v p := by
    calc ∑ p : PrismV, (v p - v (rungFlip p)) ^ 2
        = ∑ p : PrismV, (v p ^ 2 + v (rungFlip p) ^ 2 - 2 * (v (rungFlip p) * v p)) :=
          Finset.sum_congr rfl fun p _ => by ring
      _ = (∑ p : PrismV, (v p ^ 2 + v (rungFlip p) ^ 2))
          - ∑ p : PrismV, 2 * (v (rungFlip p) * v p) := by rw [Finset.sum_sub_distrib]
      _ = 2 * (∑ p : PrismV, v p ^ 2) - 2 * ∑ p : PrismV, v (rungFlip p) * v p := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hflsq]
          ring
  rw [hexpA, hsq1, hsq2]
  ring

/-- The operator bound: the Rayleigh numerator never exceeds `3⟨v,v⟩`. -/
theorem prism_energy_le (v : PrismE) : ⟪prismOp v, v⟫_ℝ ≤ 3 * ⟪v, v⟫_ℝ := by
  have h := prism_laplacian_identity v
  have h1 : 0 ≤ ∑ p : PrismV, (v p - v (shiftUp p)) ^ 2 :=
    Finset.sum_nonneg fun p _ => sq_nonneg _
  have h2 : 0 ≤ ∑ p : PrismV, (v p - v (rungFlip p)) ^ 2 :=
    Finset.sum_nonneg fun p _ => sq_nonneg _
  nlinarith

/-- Edge-difference energy zero forces global constancy on the prism (explicit cycle plus
rung induction; no connectivity machinery). -/
theorem prism_constant_of_edge_zero (v : PrismE)
    (hcyc : ∀ p : PrismV, v p = v (shiftUp p))
    (hflip : ∀ p : PrismV, v p = v (rungFlip p)) :
    ∀ p : PrismV, v p = v ((0 : ZMod 16), false) := by
  have hnat : ∀ (m : ℕ) (s : Bool), v ((m : ZMod 16), s) = v ((0 : ZMod 16), s) := by
    intro m s
    induction m with
    | zero => rw [Nat.cast_zero]
    | succ n ih =>
        have hstep := hcyc ((n : ZMod 16), s)
        rw [shiftUp_apply] at hstep
        have hcast : ((n + 1 : ℕ) : ZMod 16) = (n : ZMod 16) + 1 := by push_cast; ring
        rw [hcast, ← hstep, ih]
  rintro ⟨j, s⟩
  have hj : ((j.val : ℕ) : ZMod 16) = j := ZMod.natCast_zmod_val j
  have h1 : v (j, s) = v ((0 : ZMod 16), s) := by
    rw [← hj]
    exact hnat j.val s
  rcases s with _ | _
  · exact h1
  · have hf := hflip ((0 : ZMod 16), false)
    rw [rungFlip_apply] at hf
    rw [h1]
    exact hf.symm

/-! ## The eigenvalue assembly -/

/-- The all-ones vector. -/
def onePE : PrismE := WithLp.toLp 2 (fun _ => 1)

theorem onePE_apply (p : PrismV) : onePE p = 1 := rfl

/-- The mean-zero hyperplane. -/
def meanZero : Submodule ℝ PrismE := (Submodule.span ℝ {onePE})ᗮ

theorem sum_eq_zero_of_mem_meanZero {x : PrismE} (hx : x ∈ meanZero) :
    ∑ p : PrismV, x p = 0 := by
  have h := (Submodule.mem_orthogonal _ x).mp hx onePE
    (Submodule.mem_span_singleton_self onePE)
  rw [prism_inner_eq] at h
  calc ∑ p : PrismV, x p = ∑ p : PrismV, onePE p * x p := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [onePE_apply, one_mul]
    _ = 0 := h

theorem mem_meanZero_of_sum_eq_zero {x : PrismE} (hs : ∑ p : PrismV, x p = 0) :
    x ∈ meanZero := by
  rw [meanZero, Submodule.mem_orthogonal]
  intro u hu
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
  rw [real_inner_smul_left, prism_inner_eq]
  have : ∑ p : PrismV, onePE p * x p = 0 := by
    calc ∑ p : PrismV, onePE p * x p = ∑ p : PrismV, x p := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [onePE_apply, one_mul]
      _ = 0 := hs
  rw [this, mul_zero]

theorem prismOp_mem_meanZero {x : PrismE} (hx : x ∈ meanZero) :
    prismOp x ∈ meanZero := by
  refine mem_meanZero_of_sum_eq_zero ?_
  have hs := sum_eq_zero_of_mem_meanZero hx
  have hup := sum_comp_equiv shiftUp (fun q => x q)
  have hdn := sum_comp_equiv shiftDown (fun q => x q)
  have hfl := sum_comp_equiv rungFlip (fun q => x q)
  calc ∑ p : PrismV, prismOp x p
      = (∑ p : PrismV, x (shiftUp p)) + (∑ p : PrismV, x (shiftDown p))
        + ∑ p : PrismV, x (rungFlip p) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun p _ => prismOp_apply x p
    _ = 0 := by rw [hup, hdn, hfl, hs]; ring

/-- The prism operator restricted to the mean-zero hyperplane. -/
def prismT : meanZero →ₗ[ℝ] meanZero :=
  prismOp.restrict fun _ hx => prismOp_mem_meanZero hx

theorem prismT_coe (x : meanZero) : (prismT x : PrismE) = prismOp (x : PrismE) := rfl

theorem prismT_isSymmetric : prismT.IsSymmetric := by
  intro x y
  rw [Submodule.coe_inner, Submodule.coe_inner, prismT_coe, prismT_coe]
  exact prismOp_isSymmetric (x : PrismE) (y : PrismE)

/-- The witness vector as a Euclidean element. -/
def prismVecE : PrismE := WithLp.toLp 2 prismVec

theorem prismVecE_apply (p : PrismV) : prismVecE p = prismVec p := rfl

theorem prismOp_prismVecE_apply (p : PrismV) :
    prismOp prismVecE p = prismAdjSum prismVec p := by
  rw [prismOp_apply]
  unfold prismAdjSum
  rw [shiftUp_apply, shiftDown_apply, rungFlip_apply]
  rfl

theorem inner_prismVecE_self : ⟪prismVecE, prismVecE⟫_ℝ = 16 := by
  rw [prism_inner_eq]
  have : ∑ p : PrismV, prismVecE p * prismVecE p = prismNormSq prismVec := by
    unfold prismNormSq
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [prismVecE_apply]
    ring
  rw [this, prismNormSq_value]

theorem inner_prismOp_prismVecE : ⟪prismOp prismVecE, prismVecE⟫_ℝ
    = 16 * (2 * Real.cos (Real.pi / 8) + 1) := by
  rw [prism_inner_eq]
  have : ∑ p : PrismV, prismOp prismVecE p * prismVecE p = prismEnergy prismVec := by
    unfold prismEnergy
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [prismOp_prismVecE_apply, prismVecE_apply]
  rw [this, prismEnergy_value]

theorem prismVecE_mem_meanZero : prismVecE ∈ meanZero := by
  refine mem_meanZero_of_sum_eq_zero ?_
  have : ∑ p : PrismV, prismVecE p = ∑ p : PrismV, prismVec p :=
    Finset.sum_congr rfl fun p _ => prismVecE_apply p
  rw [this, prismVec_mean_zero]

theorem prismVecE_ne_zero : prismVecE ≠ 0 := by
  intro hcontra
  have := inner_prismVecE_self
  rw [hcontra, inner_zero_left] at this
  norm_num at this

/-- The eigenvalue of the restricted operator at the Rayleigh supremum lies strictly
between the Ramanujan bound and the degree. -/
theorem prism_nonRamanujan_eigenvalue :
    ∃ μ : ℝ, 2 * Real.sqrt 2 < μ ∧ μ < 3 ∧
      Module.End.HasEigenvalue (prismOp : Module.End ℝ PrismE) μ := by
  haveI hNontriv : Nontrivial meanZero := by
    refine ⟨⟨⟨prismVecE, prismVecE_mem_meanZero⟩, 0, fun hcontra => ?_⟩⟩
    exact prismVecE_ne_zero (by simpa using congrArg Subtype.val hcontra)
  have hEig := prismT_isSymmetric.hasEigenvalue_iSup_of_finiteDimensional
  set μ : ℝ := ⨆ x : { x : meanZero // x ≠ 0 },
    RCLike.re ⟪prismT x, (x : meanZero)⟫_ℝ / ‖(x : meanZero)‖ ^ 2 with hμ
  -- the quotient bound `≤ 3`
  have hquot3 : ∀ x : { x : meanZero // x ≠ 0 },
      RCLike.re ⟪prismT x, (x : meanZero)⟫_ℝ / ‖(x : meanZero)‖ ^ 2 ≤ 3 := by
    rintro ⟨x, hxne⟩
    have hnorm : (0 : ℝ) < ‖x‖ ^ 2 := by
      have : x ≠ 0 := hxne
      positivity
    rw [div_le_iff₀ hnorm]
    have hle := prism_energy_le (x : PrismE)
    have hinner : ⟪prismT x, x⟫_ℝ = ⟪prismOp (x : PrismE), (x : PrismE)⟫_ℝ := by
      rw [Submodule.coe_inner, prismT_coe]
    have hnormcoe : ‖x‖ ^ 2 = ⟪(x : PrismE), (x : PrismE)⟫_ℝ := by
      rw [real_inner_self_eq_norm_sq, Submodule.coe_norm]
    simp only [RCLike.re_to_real]
    rw [hinner, hnormcoe]
    linarith
  have hne : Nonempty { x : meanZero // x ≠ 0 } := by
    refine ⟨⟨⟨prismVecE, prismVecE_mem_meanZero⟩, fun hcontra => ?_⟩⟩
    exact prismVecE_ne_zero (by simpa using congrArg Subtype.val hcontra)
  have hbdd : BddAbove (Set.range fun x : { x : meanZero // x ≠ 0 } =>
      RCLike.re ⟪prismT x, (x : meanZero)⟫_ℝ / ‖(x : meanZero)‖ ^ 2) := by
    refine ⟨3, ?_⟩
    rintro y ⟨x, rfl⟩
    exact hquot3 x
  have hsup3 : μ ≤ 3 := ciSup_le hquot3
  -- the lower bound through the witness vector
  have hlow : 2 * Real.cos (Real.pi / 8) + 1 ≤ μ := by
    let hx₀ : { x : meanZero // x ≠ 0 } := ⟨⟨prismVecE, prismVecE_mem_meanZero⟩,
      fun hcontra => prismVecE_ne_zero (by simpa using congrArg Subtype.val hcontra)⟩
    have hval : RCLike.re ⟪prismT hx₀, (hx₀ : meanZero)⟫_ℝ / ‖(hx₀ : meanZero)‖ ^ 2
        = 2 * Real.cos (Real.pi / 8) + 1 := by
      have hinner : ⟪prismT hx₀, (hx₀ : meanZero)⟫_ℝ
          = 16 * (2 * Real.cos (Real.pi / 8) + 1) := by
        rw [Submodule.coe_inner, prismT_coe]
        show ⟪prismOp prismVecE, prismVecE⟫_ℝ = _
        exact inner_prismOp_prismVecE
      have hnorm : ‖(hx₀ : meanZero)‖ ^ 2 = 16 := by
        rw [Submodule.coe_norm, ← real_inner_self_eq_norm_sq]
        show ⟪prismVecE, prismVecE⟫_ℝ = _
        exact inner_prismVecE_self
      simp only [RCLike.re_to_real]
      rw [hinner, hnorm]
      norm_num
    calc 2 * Real.cos (Real.pi / 8) + 1 = _ := hval.symm
      _ ≤ μ := le_ciSup hbdd hx₀
  -- the eigenvector, and the strict upper bound by the equality analysis
  obtain ⟨u, hu⟩ := hEig.exists_hasEigenvector
  have huT : prismT u = μ • u := hu.apply_eq_smul
  have huA : prismOp (u : PrismE) = μ • (u : PrismE) := by
    have := congrArg (Subtype.val) huT
    rw [prismT_coe] at this  -- hmm prismT_coe is about coercion of application
    exact this
  have hune : (u : PrismE) ≠ 0 := fun hcontra => hu.2 (by
    apply Subtype.val_injective
    simpa using hcontra)
  have hμ3 : μ ≠ 3 := by
    intro hcontra
    have hAu3 : prismOp (u : PrismE) = (3 : ℝ) • (u : PrismE) := by rw [← hcontra]; exact huA
    have hlap := prism_laplacian_identity (u : PrismE)
    have hinner3 : ⟪prismOp (u : PrismE), (u : PrismE)⟫_ℝ
        = 3 * ⟪(u : PrismE), (u : PrismE)⟫_ℝ := by
      rw [hAu3, real_inner_smul_left]
    rw [hinner3] at hlap
    have hzero : (∑ p : PrismV, ((u : PrismE) p - (u : PrismE) (shiftUp p)) ^ 2)
        + (1 / 2) * ∑ p : PrismV, ((u : PrismE) p - (u : PrismE) (rungFlip p)) ^ 2 = 0 := by
      linarith
    have h1 : 0 ≤ ∑ p : PrismV, ((u : PrismE) p - (u : PrismE) (shiftUp p)) ^ 2 :=
      Finset.sum_nonneg fun p _ => sq_nonneg _
    have h2 : 0 ≤ ∑ p : PrismV, ((u : PrismE) p - (u : PrismE) (rungFlip p)) ^ 2 :=
      Finset.sum_nonneg fun p _ => sq_nonneg _
    have h1z : ∑ p : PrismV, ((u : PrismE) p - (u : PrismE) (shiftUp p)) ^ 2 = 0 := by
      linarith
    have h2z : ∑ p : PrismV, ((u : PrismE) p - (u : PrismE) (rungFlip p)) ^ 2 = 0 := by
      linarith
    have hcyc : ∀ p : PrismV, (u : PrismE) p = (u : PrismE) (shiftUp p) := by
      intro p
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun q _ => sq_nonneg ((u : PrismE) q - (u : PrismE) (shiftUp q)))).mp h1z
        p (Finset.mem_univ p)
      have hdiff := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      linarith [sub_eq_zero.mp hdiff]
    have hflip : ∀ p : PrismV, (u : PrismE) p = (u : PrismE) (rungFlip p) := by
      intro p
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun q _ => sq_nonneg ((u : PrismE) q - (u : PrismE) (rungFlip q)))).mp h2z
        p (Finset.mem_univ p)
      have hdiff := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      linarith [sub_eq_zero.mp hdiff]
    have hconst := prism_constant_of_edge_zero (u : PrismE) hcyc hflip
    have hsum := sum_eq_zero_of_mem_meanZero u.2
    have hval0 : (u : PrismE) ((0 : ZMod 16), false) = 0 := by
      have hsum2 : ∑ p : PrismV, (u : PrismE) p
          = (Fintype.card PrismV : ℝ) * (u : PrismE) ((0 : ZMod 16), false) := by
        rw [Finset.sum_congr rfl fun p _ => hconst p, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
      rw [hsum] at hsum2
      have hcard : (Fintype.card PrismV : ℝ) = 32 := by
        simp [Fintype.card_prod]
      rw [hcard] at hsum2
      linarith
    have huval : (u : PrismE) = 0 := by
      have hfun : ∀ p : PrismV, (u : PrismE) p = 0 := by
        intro p
        rw [hconst p, hval0]
      calc (u : PrismE) = WithLp.toLp 2 (u : PrismE).ofLp := rfl
        _ = WithLp.toLp 2 (fun _ => (0 : ℝ)) := by
            congr 1
            funext p
            exact hfun p
        _ = 0 := rfl
    exact hune huval
  refine ⟨μ, ?_, lt_of_le_of_ne hsup3 hμ3, ?_⟩
  · have := prism_margin
    linarith
  · exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr huA, hune⟩

/-- **The graph-world witness, eigenvalue form (capstone).**  The prism `C₁₆ × K₂` is a
3-regular graph whose adjacency operator has an eigenvalue strictly between the Ramanujan
bound `2√(d−1) = 2√2` and the degree `3`: the graph RH-analogue fails while the finite
spectral axioms hold, so the no-go-derived axioms alone cannot imply RH-grade positivity. -/
theorem prism_graph_violates_ramanujan :
    (∀ p : PrismV, (prismAdj.neighborFinset p).card = 3) ∧
    ∃ μ : ℝ, 2 * Real.sqrt 2 < μ ∧ μ < 3 ∧
      Module.End.HasEigenvalue (prismOp : Module.End ℝ PrismE) μ :=
  ⟨prismAdj_degree, prism_nonRamanujan_eigenvalue⟩

/-! ## The Perron pair and the independence capstone -/

/-- The degree eigenvalue: the all-ones vector is a `3`-eigenvector. -/
theorem prismOp_onePE : prismOp onePE = (3 : ℝ) • onePE := by
  calc prismOp onePE = WithLp.toLp 2 (prismOp onePE).ofLp := rfl
    _ = WithLp.toLp 2 ((3 : ℝ) • onePE).ofLp := by
        congr 1
        funext p
        show prismOp onePE p = ((3 : ℝ) • onePE) p
        rw [prismOp_apply, onePE_apply, onePE_apply, onePE_apply]
        show (1 : ℝ) + 1 + 1 = ((3 : ℝ) • onePE) p
        rw [PiLp.smul_apply, onePE_apply, smul_eq_mul]
        norm_num
    _ = (3 : ℝ) • onePE := rfl

theorem onePE_ne_zero : onePE ≠ 0 := by
  intro hcontra
  have := congrArg (fun v : PrismE => v ((0 : ZMod 16), false)) hcontra
  simp only [onePE_apply] at this
  norm_num at this

/-- The Perron eigenvalue `d = 3` of the prism. -/
theorem prism_perron_eigenvalue :
    Module.End.HasEigenvalue (prismOp : Module.End ℝ PrismE) 3 :=
  Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.mpr prismOp_onePE, onePE_ne_zero⟩

/-- **The independence witness, bundled.**  The prism carries the graph-world spectral
axioms — a symmetric finite-dimensional operator (finite trace: N2/N3/N5), 3-regularity
with the consumed Perron eigenvalue `d = 3` (N6), the combinatorial length spectrum (N1/N4,
per the card's graph forms) — while the Ramanujan RH-analogue fails: an eigenvalue lies
strictly inside `(2√(d−1), d)`.  No derivation of RH-grade positivity from the
no-go-derived axioms alone can exist in any formulation transferring to graph analogues. -/
theorem prism_independence_witness :
    prismOp.IsSymmetric ∧
    Module.End.HasEigenvalue (prismOp : Module.End ℝ PrismE) 3 ∧
    (∀ p : PrismV, (prismAdj.neighborFinset p).card = 3) ∧
    ∃ μ : ℝ, 2 * Real.sqrt 2 < μ ∧ μ < 3 ∧
      Module.End.HasEigenvalue (prismOp : Module.End ℝ PrismE) μ :=
  ⟨prismOp_isSymmetric, prism_perron_eigenvalue, prismAdj_degree,
    prism_nonRamanujan_eigenvalue⟩

end

end RHTower
