import GaloisForLFunctions.ArithmeticScatteringHolography.TheRigidityOfHeckeOnResonances
import GaloisForLFunctions.ArithmeticScatteringHolography.TheHasseWindow

/-!
# Hecke at a place of degree two

Rational places could be too few to see the trace, so the test is whether a place of degree two excludes the fakes. A
place `v` of degree two on an elliptic curve has two invariants: its class `Q₀ ∈ G`, and a class `w ∈ G'`, the rational
points of the quadratic twist, with `#G + #G' = 2(q+1)`. The dead ends are the classes `±Q` of nonzero points of `G'`: they are
the bundles descended from `𝔽_{q²}`, and modification at `v` translates them by `±w`.

The operator is explicit (`heckeTwo`), it has `q² + 1` edges at every vertex (`Channels.heckeTwo_one`), its coefficients are
nonnegative (`Channels.heckeTwo_nonneg`), it commutes with the wave operator, with Hecke at rational places, and with the
other places of degree two (`Channels.heckeTwo_comm_waveOp`, `Channels.heckeTwo_comm_heckeOp`, `Channels.heckeTwo_comm`), and in
the cusps it is the shift by two, moving the cusp by `±Q₀`. **All of this holds for every pair of groups of odd order with
`#G + #G' = 2(q+1)`**, whether or not a curve exists, and in particular above the critical discriminant
(`universal_damping_not_forced_with_degree_two`). So positivity of Hecke at degree two does not exclude the fakes, and by
`hecke_rigidity` the operator acts on every resonance by `X² + Y²` (`Channels.heckeTwo_resonance`).

The check at the core is `T(o, o) = q² - q + t = q² + 1 - h`, and on the dead ends the coefficient is `q + 1`, or `1` at
the two translates. The trace enters through the group `G'` and the counts only.
-/

open Finset ComplexConjugate
open scoped ComplexOrder

noncomputable section

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.ArithmeticScatteringHolography

variable {G G' : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] [AddCommGroup G'] [DecidableEq G']
  [Fintype G']

/-! ### Classes of the second group -/

instance : Finite (Branch G') := Quotient.finite _

instance : Fintype (Branch G') := Fintype.ofFinite _

open Classical in
instance : DecidableEq (Branch G') := Classical.decEq _

/-- The labels of the dead ends: the classes `±Q` of nonzero points of `G'`. -/
abbrev DeadLabel (G' : Type*) [AddCommGroup G'] := {x : Branch G' // x ≠ Branch.mk 0}

theorem mk_eq_mk_iff {P R : G'} : Branch.mk P = Branch.mk R ↔ R = P ∨ R = -P :=
  Quotient.eq (r := negSetoid G')

/-- The weight of a point in a sum over classes, with values in `ℂ`. -/
theorem fibre_weight (P₀ : G') :
    ∑ P ∈ univ.filter (fun P : G' => Branch.mk P = Branch.mk P₀), branchWeight P = 1 := by
  by_cases htors : 2 • P₀ = 0
  · have hneg : -P₀ = P₀ := by
      have : P₀ + P₀ = 0 := by rw [← two_nsmul]; exact htors
      exact neg_eq_of_add_eq_zero_left this
    have hf : (univ.filter fun P : G' => Branch.mk P = Branch.mk P₀) = {P₀} := by
      ext R
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [mk_eq_mk_iff]
      constructor
      · rintro (h | h)
        · exact h.symm
        · have hR : R = -P₀ := by rw [h, neg_neg]
          rw [hR, hneg]
      · intro h
        exact Or.inl h.symm
    rw [hf, Finset.sum_singleton]
    simp [branchWeight, htors]
  · have hne : P₀ ≠ -P₀ := by
      intro h
      apply htors
      rw [two_nsmul]
      nth_rewrite 1 [h]
      simp
    have hf : (univ.filter fun P : G' => Branch.mk P = Branch.mk P₀) = {P₀, -P₀} := by
      ext R
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      rw [mk_eq_mk_iff]
      constructor
      · rintro (h | h)
        · exact Or.inl h.symm
        · right
          rw [h, neg_neg]
      · rintro (h | h)
        · exact Or.inl h.symm
        · right
          rw [h, neg_neg]
    rw [hf, Finset.sum_pair hne]
    have h' : ¬ 2 • (-P₀) = 0 := by rwa [two_nsmul_neg_eq_zero_iff]
    simp only [branchWeight, if_neg htors, if_neg h']
    norm_num

/-- **The sum over classes is the weighted sum over points.** -/
theorem sum_branch_eq_weighted (F : Branch G' → ℂ) :
    ∑ x : Branch G', F x = ∑ P : G', branchWeight P * F (Branch.mk P) := by
  rw [← Finset.sum_fiberwise (s := univ) (g := fun P : G' => Branch.mk P)
    (f := fun P : G' => branchWeight P * F (Branch.mk P))]
  refine Finset.sum_congr rfl fun x _ => ?_
  induction x using Quotient.inductionOn with
  | h P₀ =>
    change F (Branch.mk P₀) = _
    have hcongr : ∑ P ∈ univ.filter (fun P : G' => Branch.mk P = Branch.mk P₀),
        branchWeight P * F (Branch.mk P) =
        ∑ P ∈ univ.filter (fun P : G' => Branch.mk P = Branch.mk P₀),
          branchWeight P * F (Branch.mk P₀) := by
      refine Finset.sum_congr rfl fun P hP => ?_
      rw [(Finset.mem_filter.mp hP).2]
    change _ = ∑ P ∈ univ.filter (fun P : G' => Branch.mk P = Branch.mk P₀), _
    rw [hcongr, ← Finset.sum_mul, fibre_weight, one_mul]

/-- The sum over dead ends is the sum over classes without the class of zero. -/
theorem sum_deadLabel (F : Branch G' → ℂ) :
    ∑ d : DeadLabel G', F d.1 = ∑ P : G', branchWeight P * F (Branch.mk P) - F (Branch.mk 0) := by
  rw [← sum_branch_eq_weighted, Fintype.sum_eq_add_sum_subtype_ne F (Branch.mk 0)]
  ring

/-! ### The operator -/

/-- The cap of the point zero. -/
def capZero (G : Type*) [AddCommGroup G] : TwoTorsion G := ⟨0, by simp⟩

/-- The term of a class of `G'`: `q` times the dead end, and at zero the combination of the pin and the cap that the
descended bundle of the trivial character becomes. -/
def deadTermB (q : ℕ) (f : Vertex G (DeadLabel G') → ℂ) (x : Branch G') : ℂ :=
  if h : x = Branch.mk 0 then ((q : ℂ) + 1) * f (.neck (Branch.mk 0)) - f (.cap (capZero G))
  else (q : ℂ) * f (.dead ⟨x, h⟩)

/-- The term of a point of `G'`. -/
def deadTerm (q : ℕ) (f : Vertex G (DeadLabel G') → ℂ) (Q : G') : ℂ := deadTermB q f (Branch.mk Q)

theorem deadTerm_neg (q : ℕ) (f : Vertex G (DeadLabel G') → ℂ) (Q : G') :
    deadTerm q f (-Q) = deadTerm q f Q := by
  unfold deadTerm
  rw [Branch.mk_neg]

/-- The translate of a dead end by `±w`. -/
def deadShift (q : ℕ) (f : Vertex G (DeadLabel G') → ℂ) (w Q : G') : ℂ :=
  deadTerm q f (Q + w) + deadTerm q f (Q - w)

theorem deadShift_neg (q : ℕ) (f : Vertex G (DeadLabel G') → ℂ) (w Q : G') :
    deadShift q f w (-Q) = deadShift q f w Q := by
  unfold deadShift
  rw [show -Q + w = -(Q - w) by abel, show -Q - w = -(Q + w) by abel, deadTerm_neg, deadTerm_neg]
  ring

/-- The operator at the neck of `P`. -/
def neckTwo (q : ℕ) (Q₀ : G) (w : G') (f : Vertex G (DeadLabel G') → ℂ) (S : ℂ) (P : G) : ℂ :=
  if 2 • P = 0 then (q : ℂ) * S - deadTerm q f w + f (.ray (P - Q₀) 1)
  else ((q : ℂ) - 1) * S + f (.ray (P - Q₀) 1) + f (.ray (-P - Q₀) 1)

theorem neckTwo_neg (q : ℕ) (Q₀ : G) (w : G') (f : Vertex G (DeadLabel G') → ℂ) (S : ℂ) (P : G) :
    neckTwo q Q₀ w f S (-P) = neckTwo q Q₀ w f S P := by
  unfold neckTwo
  by_cases h : 2 • P = 0
  · have hneg : -P = P := by
      have : P + P = 0 := by rw [← two_nsmul]; exact h
      exact neg_eq_of_add_eq_zero_left this
    rw [if_pos (by rwa [two_nsmul_neg_eq_zero_iff]), if_pos h, hneg]
  · rw [if_neg h, if_neg (by rwa [two_nsmul_neg_eq_zero_iff]), neg_neg]
    ring

/-- **Hecke at a place of degree two**, of class `Q₀ ∈ G` and `w ∈ G'`. -/
def heckeTwo (q : ℕ) (t : ℂ) (Q₀ : G) (w : G') (f : Vertex G (DeadLabel G') → ℂ) :
    Vertex G (DeadLabel G') → ℂ
  | .core => ((q : ℂ) ^ 2 - q + t) * f .core + ∑ P, f (.ray P 0)
  | .dead d => Quotient.liftOn d.1
      (fun Q => ((q : ℂ) + 1) * waveOp q f .core - deadShift q f w Q)
      (fun P R h => by
        rcases h with rfl | rfl
        · rfl
        · show ((q : ℂ) + 1) * waveOp q f .core - deadShift q f w P =
            ((q : ℂ) + 1) * waveOp q f .core - deadShift q f w (-P)
          rw [deadShift_neg])
  | .neck x => Quotient.liftOn x (neckTwo q Q₀ w f (waveOp q f .core)) (fun P R h => by
      rcases h with rfl | rfl
      · rfl
      · exact (neckTwo_neg q Q₀ w f _ P).symm)
  | .cap L => ((q : ℂ) + 1) * f (.ray (L.1 - Q₀) 1) + ((q : ℂ) - 1) * deadTerm q f w
  | .ray P 0 => (q : ℂ) * ((q : ℂ) - 1) * f .core + (q : ℂ) * f (.ray (-P - Q₀) 0) + f (.ray (P - Q₀) 2)
  | .ray P 1 => (q : ℂ) * gapOp q f (P + Q₀) + f (.ray (P - Q₀) 3)
  | .ray P (k + 2) => (q : ℂ) ^ 2 * f (.ray (P + Q₀) k) + f (.ray (P - Q₀) (k + 4))

variable (q : ℕ) (t : ℂ) (Q₀ : G) (w : G') (f : Vertex G (DeadLabel G') → ℂ)

@[simp] theorem heckeTwo_core : heckeTwo q t Q₀ w f .core =
    ((q : ℂ) ^ 2 - q + t) * f .core + ∑ P, f (.ray P 0) := rfl
theorem heckeTwo_dead (Q : G') (h : Branch.mk Q ≠ Branch.mk 0) :
    heckeTwo q t Q₀ w f (.dead ⟨Branch.mk Q, h⟩) =
      ((q : ℂ) + 1) * waveOp q f .core - deadShift q f w Q := rfl
@[simp] theorem heckeTwo_neck (P : G) : heckeTwo q t Q₀ w f (.neck (Branch.mk P)) =
    neckTwo q Q₀ w f (waveOp q f .core) P := rfl
@[simp] theorem heckeTwo_cap (L : TwoTorsion G) : heckeTwo q t Q₀ w f (.cap L) =
    ((q : ℂ) + 1) * f (.ray (L.1 - Q₀) 1) + ((q : ℂ) - 1) * deadTerm q f w := rfl
@[simp] theorem heckeTwo_ray_zero (P : G) : heckeTwo q t Q₀ w f (.ray P 0) =
    (q : ℂ) * ((q : ℂ) - 1) * f .core + (q : ℂ) * f (.ray (-P - Q₀) 0) + f (.ray (P - Q₀) 2) := rfl
@[simp] theorem heckeTwo_ray_one (P : G) : heckeTwo q t Q₀ w f (.ray P 1) =
    (q : ℂ) * gapOp q f (P + Q₀) + f (.ray (P - Q₀) 3) := rfl
@[simp] theorem heckeTwo_ray_add_two (P : G) (k : ℕ) : heckeTwo q t Q₀ w f (.ray P (k + 2)) =
    (q : ℂ) ^ 2 * f (.ray (P + Q₀) k) + f (.ray (P - Q₀) (k + 4)) := rfl

/-! ### Sums -/

/-- The lift of the translate of a dead end to the classes. -/
def deadShiftB (q : ℕ) (f : Vertex G (DeadLabel G') → ℂ) (w : G') (x : Branch G') : ℂ :=
  Quotient.liftOn x (deadShift q f w) (fun P R h => by
    rcases h with rfl | rfl
    · rfl
    · exact (deadShift_neg q f w P).symm)

/-- The operator at a dead end, for any label. -/
theorem heckeTwo_dead' (d : DeadLabel G') : heckeTwo q t Q₀ w f (.dead d) =
    ((q : ℂ) + 1) * waveOp q f .core - deadShiftB q f w d.1 := by
  obtain ⟨x, hx⟩ := d
  induction x using Quotient.inductionOn with
  | h Q => rfl

section OddSecondGroup

variable (hG' : ∀ Q : G', 2 • Q = 0 → Q = 0)

include hG' in
/-- The weight of a point of an odd group: `½` plus `½` at zero. -/
theorem sum_weighted_odd (F : G' → ℂ) :
    ∑ Q : G', branchWeight Q * F Q = (1 / 2 : ℂ) * ∑ Q, F Q + (1 / 2 : ℂ) * F 0 := by
  have hw (Q : G') : branchWeight Q * F Q =
      (1 / 2 : ℂ) * F Q + (1 / 2 : ℂ) * (if 2 • Q = 0 then F Q else 0) := by
    unfold branchWeight
    split_ifs <;> ring
  have hone : ∑ Q : G', (if 2 • Q = 0 then F Q else 0) = F 0 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hb
      rw [if_neg fun h => hb (hG' b h)]
    · simp
  simp only [hw, Finset.sum_add_distrib, ← Finset.mul_sum, hone]

include hG' in
/-- The sum of the dead terms over `G'`. -/
theorem sum_deadTerm :
    ∑ Q : G', deadTerm q f Q =
      deadTerm q f 0 + 2 * ((q : ℂ) * ∑ d : DeadLabel G', f (.dead d)) := by
  have hdead : ∑ d : DeadLabel G', deadTermB q f d.1 = (q : ℂ) * ∑ d : DeadLabel G', f (.dead d) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    unfold deadTermB
    rw [dif_neg d.2]
  have hsum := sum_deadLabel (G' := G') (deadTermB q f)
  rw [hdead, show (∑ P : G', branchWeight P * deadTermB q f (Branch.mk P)) =
    ∑ P : G', branchWeight P * deadTerm q f P from rfl, sum_weighted_odd hG'] at hsum
  have e0 : deadTermB q f (Branch.mk 0) = deadTerm q f 0 := rfl
  rw [e0] at hsum
  linear_combination (-2 : ℂ) * hsum

include hG' in
/-- The sum of the translates over the dead ends. -/
theorem sum_deadShift :
    ∑ d : DeadLabel G', deadShiftB q f w d.1 =
      deadTerm q f 0 + 2 * ((q : ℂ) * ∑ d : DeadLabel G', f (.dead d)) - deadTerm q f w := by
  have hsum := sum_deadLabel (G' := G') (deadShiftB q f w)
  have e (P : G') : deadShiftB q f w (Branch.mk P) = deadShift q f w P := rfl
  simp only [e] at hsum
  rw [sum_weighted_odd hG'] at hsum
  have h1 : ∑ Q : G', deadTerm q f (Q + w) = ∑ Q, deadTerm q f Q :=
    Equiv.sum_comp (Equiv.addRight w) (deadTerm q f)
  have h2 : ∑ Q : G', deadTerm q f (Q - w) = ∑ Q, deadTerm q f Q :=
    Equiv.sum_comp (Equiv.subRight w) (deadTerm q f)
  have h3 : deadShift q f w 0 = 2 * deadTerm q f w := by
    unfold deadShift
    rw [zero_add, zero_sub, deadTerm_neg]
    ring
  have h4 : ∑ Q : G', deadShift q f w Q = 2 * ∑ Q, deadTerm q f Q := by
    unfold deadShift
    rw [Finset.sum_add_distrib, h1, h2]
    ring
  rw [hsum, h3, h4, sum_deadTerm q f hG']
  ring

end OddSecondGroup

/-- The sum of the neck coefficients together with the dead ends: the first return. -/
theorem Channels.kappa_sum (B : Channels G (DeadLabel G')) :
    (Fintype.card (DeadLabel G') : ℂ) * ((B.q : ℂ) + 1) +
        ∑ P : G, branchWeight P * (if 2 • P = 0 then (B.q : ℂ) else (B.q : ℂ) - 1) =
      (B.q : ℂ) ^ 2 + B.q + B.trace := by
  have hh := B.cuspCount_eq
  have hcount := B.count_complex
  have e : ∀ P : G, branchWeight P * (if 2 • P = 0 then (B.q : ℂ) else (B.q : ℂ) - 1) =
      if 2 • P = 0 then (B.q : ℂ) else ((B.q : ℂ) - 1) / 2 := by
    intro P
    unfold branchWeight
    split_ifs <;> ring
  simp only [e]
  rw [sum_ite_torsion]
  linear_combination ((B.q : ℂ) + 1) / 2 * hcount - hh

/-- The second iterate of the wave operator at the core. -/
theorem Channels.waveOp_waveOp_core (B : Channels G (DeadLabel G')) (f : Vertex G (DeadLabel G') → ℂ) :
    waveOp B.q (waveOp B.q f) .core =
      ((B.q : ℂ) ^ 2 + B.q + B.trace) * f .core + ∑ P, f (.ray P 0) := by
  have hne (P : G) : neckOp B.q f P = neckHecke B.q (0 : G) f P := by
    simp [neckHecke, neckOp]
  rw [waveOp_core]
  simp only [waveOp_dead, waveOp_neck, hne, sum_neckHecke, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [← B.kappa_sum]
  ring

section OddGroups

variable (hG : ∀ P : G, 2 • P = 0 → P = 0)

include hG in
/-- The sum of the gap terms: everything is `2q` times the weighted necks, except at zero. -/
theorem sum_gapOp (B : Channels G (DeadLabel G')) (f : Vertex G (DeadLabel G') → ℂ) :
    ∑ P, gapOp B.q f P =
      2 * (B.q : ℂ) * (∑ P, branchWeight P * f (.neck (Branch.mk P))) - deadTerm B.q f (0 : G') := by
  have hterm (P : G) : gapOp B.q f P = 2 * (B.q : ℂ) * (branchWeight P * f (.neck (Branch.mk P))) -
      (if 2 • P = 0 then deadTerm B.q f (0 : G') else 0) := by
    unfold gapOp branchWeight
    by_cases h : 2 • P = 0
    · have h0 := hG P h
      subst h0
      have hc : (⟨0, h⟩ : TwoTorsion G) = capZero G := rfl
      simp only [dif_pos h, if_pos h, hc]
      unfold deadTerm deadTermB
      rw [dif_pos rfl]
      ring
    · simp only [dif_neg h, if_neg h]
      ring
  have hone : ∑ P : G, (if 2 • P = 0 then deadTerm B.q f (0 : G') else 0) = deadTerm B.q f (0 : G') := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hb
      rw [if_neg fun h => hb (hG b h)]
    · simp
  simp only [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, hone]

end OddGroups

/-- The gap term of `A f`, in one closed form. -/
theorem gapOp_waveOp (B : Channels G (DeadLabel G')) (f : Vertex G (DeadLabel G') → ℂ) (R : G) :
    gapOp B.q (waveOp B.q f) R =
      (B.q : ℂ) * (((B.q : ℂ) - 1) * f .core) + (B.q : ℂ) * f (.ray R 0) + (B.q : ℂ) * f (.ray (-R) 0) := by
  have h := gapOp_heckeOp B (0 : G) f R
  have hfun : heckeOp B.q (0 : G) f = waveOp B.q f := funext (heckeOp_zero B.q f)
  rw [hfun] at h
  simpa using h

/-- The dead term of `A f`: the same at every point. -/
theorem deadTerm_waveOp (B : Channels G (DeadLabel G')) (f : Vertex G (DeadLabel G') → ℂ) (Q : G') :
    deadTerm B.q (waveOp B.q f) Q = (B.q : ℂ) * (((B.q : ℂ) + 1) * f .core) := by
  unfold deadTerm deadTermB
  by_cases h : Branch.mk Q = Branch.mk 0
  · rw [dif_pos h, waveOp_neck, waveOp_cap]
    unfold neckOp capZero
    simp only [if_pos (by simp : 2 • (0 : G) = 0)]
    ring
  · rw [dif_neg h, waveOp_dead]

/-! ### Commutation with the wave operator -/

/-- **Hecke of degree two commutes with the wave operator**, on every pair of odd groups. -/
theorem Channels.heckeTwo_comm_waveOp (B : Channels G (DeadLabel G'))
    (hG : ∀ P : G, 2 • P = 0 → P = 0) (hG' : ∀ Q : G', 2 • Q = 0 → Q = 0) (Q₀ : G) (w : G')
    (f : Vertex G (DeadLabel G') → ℂ) (v : Vertex G (DeadLabel G')) :
    waveOp B.q (heckeTwo B.q B.trace Q₀ w f) v =
      heckeTwo B.q B.trace Q₀ w (waveOp B.q f) v := by
  have hSeq : waveOp B.q f .core =
      ∑ d, f (.dead d) + ∑ P, branchWeight P * f (.neck (Branch.mk P)) := rfl
  have hcoreA := B.waveOp_waveOp_core f
  rcases v with _ | d | x | L | ⟨P, _ | _ | _ | k⟩
  · -- the core: the only place where the groups enter
    rw [waveOp_core]
    simp only [heckeTwo_dead', heckeTwo_neck]
    rw [Finset.sum_sub_distrib, sum_deadShift B.q w f hG']
    have hterm (P : G) : branchWeight P * neckTwo B.q Q₀ w f (waveOp B.q f .core) P =
        branchWeight P * (if 2 • P = 0 then (B.q : ℂ) else (B.q : ℂ) - 1) * waveOp B.q f .core -
          (if 2 • P = 0 then deadTerm B.q f w else 0) +
          ((1 / 2 : ℂ) * f (.ray (P - Q₀) 1) + (1 / 2 : ℂ) * f (.ray (-P - Q₀) 1)) := by
      unfold neckTwo branchWeight
      by_cases h : 2 • P = 0
      · have hneg : -P = P := by
          have : P + P = 0 := by rw [← two_nsmul]; exact h
          exact neg_eq_of_add_eq_zero_left this
        simp only [if_pos h, hneg]
        ring
      · simp only [if_neg h]
        ring
    have hone : ∑ P : G, (if 2 • P = 0 then deadTerm B.q f w else 0) = deadTerm B.q f w := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro b _ hb
        rw [if_neg fun h => hb (hG b h)]
      · simp
    have e1 : ∑ P : G, f (.ray (P - Q₀) 1) = ∑ P, f (.ray P 1) :=
      Equiv.sum_comp (Equiv.subRight Q₀) (fun P => f (.ray P 1))
    have e2 : ∑ P : G, f (.ray (-P - Q₀) 1) = ∑ P, f (.ray P 1) :=
      Equiv.sum_comp ((Equiv.neg G).trans (Equiv.subRight Q₀)) (fun P => f (.ray P 1))
    have hnecksum : ∑ P : G, branchWeight P * neckTwo B.q Q₀ w f (waveOp B.q f .core) P =
        (∑ P : G, branchWeight P * (if 2 • P = 0 then (B.q : ℂ) else (B.q : ℂ) - 1)) *
            waveOp B.q f .core - deadTerm B.q f w + ∑ P, f (.ray P 1) := by
      simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
        ← Finset.mul_sum, hone, e1, e2]
      ring
    rw [hnecksum, heckeTwo_core]
    simp only [waveOp_ray_zero, Finset.sum_add_distrib]
    rw [sum_gapOp hG B f]
    have hkappa := B.kappa_sum
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linear_combination (waveOp B.q f .core) * hkappa + (2 * (B.q : ℂ)) * hSeq
  · -- a dead end
    rw [waveOp_dead, heckeTwo_core, heckeTwo_dead']
    have hshift : deadShiftB B.q (waveOp B.q f) w d.1 =
        2 * ((B.q : ℂ) * (((B.q : ℂ) + 1) * f .core)) := by
      obtain ⟨x, hx⟩ := d
      induction x using Quotient.inductionOn with
      | h Q =>
        change deadShift B.q (waveOp B.q f) w Q = _
        unfold deadShift
        rw [deadTerm_waveOp, deadTerm_waveOp]
        ring
    rw [hshift, hcoreA]
    ring
  · -- a neck
    induction x using Quotient.inductionOn with
    | h P =>
      change waveOp B.q _ (.neck (Branch.mk P)) = heckeTwo B.q B.trace Q₀ w _ (.neck (Branch.mk P))
      rw [waveOp_neck, heckeTwo_neck, hcoreA]
      unfold neckOp neckTwo
      by_cases h : 2 • P = 0
      · simp only [if_pos h, heckeTwo_core, heckeTwo_ray_zero, waveOp_ray_succ, deadTerm_waveOp]
        have e : ∀ a b : ℂ, a + (B.q : ℂ) * ((B.q : ℂ) - 1) * b = a + (B.q : ℂ) * ((B.q : ℂ) - 1) * b :=
          fun _ _ => rfl
        have hneg : -P = P := by
          have : P + P = 0 := by rw [← two_nsmul]; exact h
          exact neg_eq_of_add_eq_zero_left this
        rw [hneg]
        ring
      · simp only [if_neg h, heckeTwo_core, heckeTwo_ray_zero, waveOp_ray_succ, neg_neg]
        ring
  · -- a cap
    rw [waveOp_cap, heckeTwo_ray_zero, heckeTwo_cap, waveOp_ray_succ, deadTerm_waveOp]
    have hneg : -L.1 = L.1 := by
      have : L.1 + L.1 = 0 := by rw [← two_nsmul]; exact L.2
      exact neg_eq_of_add_eq_zero_left this
    rw [hneg]
    ring
  · -- the root of a ray
    have hgap : gapOp B.q (heckeTwo B.q B.trace Q₀ w f) P =
        (B.q : ℂ) * ((B.q : ℂ) - 1) * waveOp B.q f .core + (B.q : ℂ) * f (.ray (P - Q₀) 1) +
          (B.q : ℂ) * f (.ray (-P - Q₀) 1) := by
      unfold gapOp
      by_cases h : 2 • P = 0
      · have hneg : -P = P := by
          have : P + P = 0 := by rw [← two_nsmul]; exact h
          exact neg_eq_of_add_eq_zero_left this
        rw [dif_pos h, heckeTwo_neck, heckeTwo_cap]
        unfold neckTwo
        simp only [if_pos h, hneg]
        ring
      · rw [dif_neg h, heckeTwo_neck]
        unfold neckTwo
        simp only [if_neg h]
        ring
    have hneggap : gapOp B.q f (-P - Q₀) = gapOp B.q f (P + Q₀) := by
      rw [show -P - Q₀ = -(P + Q₀) by abel, gapOp_neg]
    have e1 : waveOp B.q (heckeTwo B.q B.trace Q₀ w f) (.ray P 0) =
        gapOp B.q (heckeTwo B.q B.trace Q₀ w f) P +
          ((B.q : ℂ) * gapOp B.q f (P + Q₀) + f (.ray (P - Q₀) 3)) := rfl
    have e2 : heckeTwo B.q B.trace Q₀ w (waveOp B.q f) (.ray P 0) =
        (B.q : ℂ) * ((B.q : ℂ) - 1) * waveOp B.q f .core +
          (B.q : ℂ) * (gapOp B.q f (-P - Q₀) + f (.ray (-P - Q₀) 1)) +
          ((B.q : ℂ) * f (.ray (P - Q₀) 1) + f (.ray (P - Q₀) 3)) := rfl
    rw [e1, e2, hgap, hneggap]
    ring
  · -- depth one
    have e1 : waveOp B.q (heckeTwo B.q B.trace Q₀ w f) (.ray P (0 + 1)) =
        (B.q : ℂ) * ((B.q : ℂ) * ((B.q : ℂ) - 1) * f .core + (B.q : ℂ) * f (.ray (-P - Q₀) 0) +
          f (.ray (P - Q₀) 2)) +
          ((B.q : ℂ) ^ 2 * f (.ray (P + Q₀) 0) + f (.ray (P - Q₀) 4)) := rfl
    have e2 : heckeTwo B.q B.trace Q₀ w (waveOp B.q f) (.ray P (0 + 1)) =
        (B.q : ℂ) * gapOp B.q (waveOp B.q f) (P + Q₀) +
          ((B.q : ℂ) * f (.ray (P - Q₀) 2) + f (.ray (P - Q₀) 4)) := rfl
    rw [e1, e2, gapOp_waveOp, show -(P + Q₀) = -P - Q₀ by abel]
    ring
  · -- depth two
    have e1 : waveOp B.q (heckeTwo B.q B.trace Q₀ w f) (.ray P (0 + 1 + 1)) =
        (B.q : ℂ) * ((B.q : ℂ) * gapOp B.q f (P + Q₀) + f (.ray (P - Q₀) 3)) +
          ((B.q : ℂ) ^ 2 * f (.ray (P + Q₀) 1) + f (.ray (P - Q₀) 5)) := rfl
    have e2 : heckeTwo B.q B.trace Q₀ w (waveOp B.q f) (.ray P (0 + 1 + 1)) =
        (B.q : ℂ) ^ 2 * (gapOp B.q f (P + Q₀) + f (.ray (P + Q₀) 1)) +
          ((B.q : ℂ) * f (.ray (P - Q₀) 3) + f (.ray (P - Q₀) 5)) := rfl
    rw [e1, e2]
    ring
  · -- deep in the cusp
    have e1 : waveOp B.q (heckeTwo B.q B.trace Q₀ w f) (.ray P (k + 1 + 1 + 1)) =
        (B.q : ℂ) * ((B.q : ℂ) ^ 2 * f (.ray (P + Q₀) k) + f (.ray (P - Q₀) (k + 4))) +
          ((B.q : ℂ) ^ 2 * f (.ray (P + Q₀) (k + 2)) + f (.ray (P - Q₀) (k + 6))) := rfl
    have e2 : heckeTwo B.q B.trace Q₀ w (waveOp B.q f) (.ray P (k + 1 + 1 + 1)) =
        (B.q : ℂ) ^ 2 * ((B.q : ℂ) * f (.ray (P + Q₀) k) + f (.ray (P + Q₀) (k + 2))) +
          ((B.q : ℂ) * f (.ray (P - Q₀) (k + 4)) + f (.ray (P - Q₀) (k + 6))) := rfl
    rw [e1, e2]
    ring

/-! ### The commutative algebra -/

/-- The gap term of `T f`, in one closed form for both kinds of point. -/
theorem gapOp_heckeTwo (B : Channels G (DeadLabel G')) (Q₀ : G) (w : G')
    (f : Vertex G (DeadLabel G') → ℂ) (R : G) :
    gapOp B.q (heckeTwo B.q B.trace Q₀ w f) R =
      (B.q : ℂ) * ((B.q : ℂ) - 1) * waveOp B.q f .core + (B.q : ℂ) * f (.ray (R - Q₀) 1) +
        (B.q : ℂ) * f (.ray (-R - Q₀) 1) := by
  unfold gapOp
  by_cases h : 2 • R = 0
  · have hneg : -R = R := by
      have : R + R = 0 := by rw [← two_nsmul]; exact h
      exact neg_eq_of_add_eq_zero_left this
    rw [dif_pos h, heckeTwo_neck, heckeTwo_cap]
    unfold neckTwo
    simp only [if_pos h, hneg]
    ring
  · rw [dif_neg h, heckeTwo_neck]
    unfold neckTwo
    simp only [if_neg h]
    ring

/-- The dead term of `T f`, in one closed form. -/
theorem deadTerm_heckeTwo (B : Channels G (DeadLabel G')) (Q₀ : G) (w : G')
    (f : Vertex G (DeadLabel G') → ℂ) (Q : G') :
    deadTerm B.q (heckeTwo B.q B.trace Q₀ w f) Q =
      (B.q : ℂ) * (((B.q : ℂ) + 1) * waveOp B.q f .core - deadShift B.q f w Q) := by
  have hzero : deadShift B.q f w 0 = 2 * deadTerm B.q f w := by
    unfold deadShift
    rw [zero_add, zero_sub, deadTerm_neg]
    ring
  unfold deadTerm deadTermB
  by_cases h : Branch.mk Q = Branch.mk 0
  · have hQ : Q = 0 := by
      rcases mk_eq_mk_iff.mp h with h | h
      · exact h.symm
      · simpa [eq_comm] using h
    subst hQ
    rw [dif_pos rfl, heckeTwo_neck, heckeTwo_cap]
    have hcz : (capZero G).1 = 0 := rfl
    unfold neckTwo
    simp only [if_pos (by simp : 2 • (0 : G) = 0), hcz]
    rw [show deadShift B.q f w 0 = 2 * deadTerm B.q f w from hzero]
    unfold deadTerm deadTermB
    ring
  · rw [dif_neg h]
    obtain ⟨x, hx⟩ : ∃ x : DeadLabel G', x = ⟨Branch.mk Q, h⟩ := ⟨_, rfl⟩
    rw [← hx, heckeTwo_dead', hx]
    rfl

/-- **Hecke at degree two commutes with Hecke at rational places.** -/
theorem Channels.heckeTwo_comm_heckeOp (B : Channels G (DeadLabel G'))
    (hG : ∀ P : G, 2 • P = 0 → P = 0) (hG' : ∀ Q : G', 2 • Q = 0 → Q = 0) (Q₀ Q : G) (w : G')
    (f : Vertex G (DeadLabel G') → ℂ) (v : Vertex G (DeadLabel G')) :
    heckeOp B.q Q (heckeTwo B.q B.trace Q₀ w f) v =
      heckeTwo B.q B.trace Q₀ w (heckeOp B.q Q f) v := by
  have hcore : waveOp B.q (heckeOp B.q Q f) .core = waveOp B.q (waveOp B.q f) .core := by
    rw [heckeOp_comm_waveOp]
    rfl
  have hA := B.heckeTwo_comm_waveOp hG hG' Q₀ w f .core
  have hsumP : ∑ P : G, gapOp B.q f (P + Q) = ∑ P, gapOp B.q f P :=
    Equiv.sum_comp (Equiv.addRight Q) (gapOp B.q f)
  have hsum1 : ∑ P : G, f (.ray (P - Q) 1) = ∑ P, f (.ray P 1) :=
    Equiv.sum_comp (Equiv.subRight Q) (fun P => f (.ray P 1))
  have hsum0 : ∑ P : G, f (.ray (P - Q) 0) = ∑ P, f (.ray P 0) :=
    Equiv.sum_comp (Equiv.subRight Q) (fun P => f (.ray P 0))
  have hdead (Q' : G') : deadTerm B.q (heckeOp B.q Q f) Q' = (B.q : ℂ) * (((B.q : ℂ) + 1) * f .core) := by
    unfold deadTerm deadTermB
    by_cases h : Branch.mk Q' = Branch.mk 0
    · rw [dif_pos h, heckeOp_neck, heckeOp_cap]
      unfold neckHecke capZero
      simp only [if_pos (by simp : 2 • (0 : G) = 0)]
      ring
    · rw [dif_neg h, heckeOp_dead]
  have hcoreRow : heckeOp B.q Q (heckeTwo B.q B.trace Q₀ w f) .core =
      waveOp B.q (heckeTwo B.q B.trace Q₀ w f) .core := rfl
  rcases v with _ | d | x | L | ⟨P, _ | _ | _ | k⟩
  · rw [hcoreRow, hA, heckeTwo_core, heckeTwo_core]
    simp only [heckeOp_ray_zero, waveOp_ray_zero, Finset.sum_add_distrib, hsumP, hsum1]
    rw [show heckeOp B.q Q f .core = waveOp B.q f .core from rfl]
  · rw [heckeOp_dead, heckeTwo_core, heckeTwo_dead', hcore, B.waveOp_waveOp_core]
    have hshift : deadShiftB B.q (heckeOp B.q Q f) w d.1 =
        2 * ((B.q : ℂ) * (((B.q : ℂ) + 1) * f .core)) := by
      obtain ⟨x, hx⟩ := d
      induction x using Quotient.inductionOn with
      | h Q' =>
        change deadShift B.q (heckeOp B.q Q f) w Q' = _
        unfold deadShift
        rw [hdead, hdead]
        ring
    rw [hshift]
    ring
  · induction x using Quotient.inductionOn with
    | h P =>
      change neckHecke B.q Q _ P = neckTwo B.q Q₀ w _ (waveOp B.q _ .core) P
      rw [hcore, B.waveOp_waveOp_core]
      unfold neckHecke neckTwo
      by_cases h : 2 • P = 0
      · simp only [if_pos h, heckeTwo_core, heckeTwo_ray_zero, hdead]
        have hneg : -P = P := by
          have : P + P = 0 := by rw [← two_nsmul]; exact h
          exact neg_eq_of_add_eq_zero_left this
        have e1 : heckeOp B.q Q f (.ray (P - Q₀) 1) =
            (B.q : ℂ) * f (.ray (P - Q₀ + Q) 0) + f (.ray (P - Q₀ - Q) 2) := rfl
        have e3 : -(P - Q) - Q₀ = P - Q₀ + Q := by
          calc -(P - Q) - Q₀ = -P + Q - Q₀ := by abel
            _ = P + Q - Q₀ := by rw [hneg]
            _ = P - Q₀ + Q := by abel
        rw [e1, e3, show P - Q - Q₀ = P - Q₀ - Q by abel]
        ring
      · simp only [if_neg h, heckeTwo_core, heckeTwo_ray_zero]
        have e1 : heckeOp B.q Q f (.ray (P - Q₀) 1) =
            (B.q : ℂ) * f (.ray (P - Q₀ + Q) 0) + f (.ray (P - Q₀ - Q) 2) := rfl
        have e2 : heckeOp B.q Q f (.ray (-P - Q₀) 1) =
            (B.q : ℂ) * f (.ray (-P - Q₀ + Q) 0) + f (.ray (-P - Q₀ - Q) 2) := rfl
        rw [e1, e2, show -(P - Q) - Q₀ = -P - Q₀ + Q by abel, show -(-P - Q) - Q₀ = P - Q₀ + Q by abel,
          show P - Q - Q₀ = P - Q₀ - Q by abel, show -P - Q - Q₀ = -P - Q₀ - Q by abel]
        ring
  · rw [heckeOp_cap, heckeTwo_ray_zero, heckeTwo_cap, hdead]
    have e1 : heckeOp B.q Q f (.ray (L.1 - Q₀) 1) =
        (B.q : ℂ) * f (.ray (L.1 - Q₀ + Q) 0) + f (.ray (L.1 - Q₀ - Q) 2) := rfl
    have hneg : -L.1 = L.1 := by
      have : L.1 + L.1 = 0 := by rw [← two_nsmul]; exact L.2
      exact neg_eq_of_add_eq_zero_left this
    have e3 : -(L.1 - Q) - Q₀ = L.1 - Q₀ + Q := by
      calc -(L.1 - Q) - Q₀ = -L.1 + Q - Q₀ := by abel
        _ = L.1 + Q - Q₀ := by rw [hneg]
        _ = L.1 - Q₀ + Q := by abel
    rw [e1, e3, show L.1 - Q - Q₀ = L.1 - Q₀ - Q by abel]
    ring
  · have e1 : heckeOp B.q Q (heckeTwo B.q B.trace Q₀ w f) (.ray P 0) =
        gapOp B.q (heckeTwo B.q B.trace Q₀ w f) (P + Q) +
          ((B.q : ℂ) * gapOp B.q f (P - Q + Q₀) + f (.ray (P - Q - Q₀) 3)) := rfl
    have e2 : heckeTwo B.q B.trace Q₀ w (heckeOp B.q Q f) (.ray P 0) =
        (B.q : ℂ) * ((B.q : ℂ) - 1) * waveOp B.q f .core +
          (B.q : ℂ) * (gapOp B.q f (-P - Q₀ + Q) + f (.ray (-P - Q₀ - Q) 1)) +
          ((B.q : ℂ) * f (.ray (P - Q₀ + Q) 1) + f (.ray (P - Q₀ - Q) 3)) := rfl
    rw [e1, e2, gapOp_heckeTwo, show -P - Q₀ + Q = -(P - Q + Q₀) by abel, gapOp_neg,
      show P + Q - Q₀ = P - Q₀ + Q by abel, show -(P + Q) - Q₀ = -P - Q₀ - Q by abel,
      show P - Q - Q₀ = P - Q₀ - Q by abel]
    ring
  · have e1 : heckeOp B.q Q (heckeTwo B.q B.trace Q₀ w f) (.ray P (0 + 1)) =
        (B.q : ℂ) * ((B.q : ℂ) * ((B.q : ℂ) - 1) * f .core + (B.q : ℂ) * f (.ray (-(P + Q) - Q₀) 0) +
          f (.ray (P + Q - Q₀) 2)) +
          ((B.q : ℂ) ^ 2 * f (.ray (P - Q + Q₀) 0) + f (.ray (P - Q - Q₀) 4)) := rfl
    have e2 : heckeTwo B.q B.trace Q₀ w (heckeOp B.q Q f) (.ray P (0 + 1)) =
        (B.q : ℂ) * gapOp B.q (heckeOp B.q Q f) (P + Q₀) +
          ((B.q : ℂ) * f (.ray (P - Q₀ + Q) 2) + f (.ray (P - Q₀ - Q) 4)) := rfl
    rw [e1, e2, gapOp_heckeOp, show P + Q - Q₀ = P - Q₀ + Q by abel,
      show P + Q₀ - Q = P - Q + Q₀ by abel, show -(P + Q₀) - Q = -(P + Q) - Q₀ by abel,
      show P - Q - Q₀ = P - Q₀ - Q by abel]
    ring
  · have e1 : heckeOp B.q Q (heckeTwo B.q B.trace Q₀ w f) (.ray P (0 + 1 + 1)) =
        (B.q : ℂ) * ((B.q : ℂ) * gapOp B.q f (P + Q + Q₀) + f (.ray (P + Q - Q₀) 3)) +
          ((B.q : ℂ) ^ 2 * f (.ray (P - Q + Q₀) 1) + f (.ray (P - Q - Q₀) 5)) := rfl
    have e2 : heckeTwo B.q B.trace Q₀ w (heckeOp B.q Q f) (.ray P (0 + 1 + 1)) =
        (B.q : ℂ) ^ 2 * (gapOp B.q f (P + Q₀ + Q) + f (.ray (P + Q₀ - Q) 1)) +
          ((B.q : ℂ) * f (.ray (P - Q₀ + Q) 3) + f (.ray (P - Q₀ - Q) 5)) := rfl
    rw [e1, e2, show P + Q + Q₀ = P + Q₀ + Q by abel, show P + Q - Q₀ = P - Q₀ + Q by abel,
      show P - Q + Q₀ = P + Q₀ - Q by abel, show P - Q - Q₀ = P - Q₀ - Q by abel]
    ring
  · have e1 : heckeOp B.q Q (heckeTwo B.q B.trace Q₀ w f) (.ray P (k + 1 + 1 + 1)) =
        (B.q : ℂ) * ((B.q : ℂ) ^ 2 * f (.ray (P + Q + Q₀) k) + f (.ray (P + Q - Q₀) (k + 4))) +
          ((B.q : ℂ) ^ 2 * f (.ray (P - Q + Q₀) (k + 2)) + f (.ray (P - Q - Q₀) (k + 6))) := rfl
    have e2 : heckeTwo B.q B.trace Q₀ w (heckeOp B.q Q f) (.ray P (k + 1 + 1 + 1)) =
        (B.q : ℂ) ^ 2 * ((B.q : ℂ) * f (.ray (P + Q₀ + Q) k) + f (.ray (P + Q₀ - Q) (k + 2))) +
          ((B.q : ℂ) * f (.ray (P - Q₀ + Q) (k + 4)) + f (.ray (P - Q₀ - Q) (k + 6))) := rfl
    rw [e1, e2, show P + Q + Q₀ = P + Q₀ + Q by abel, show P + Q - Q₀ = P - Q₀ + Q by abel,
      show P - Q + Q₀ = P + Q₀ - Q by abel, show P - Q - Q₀ = P - Q₀ - Q by abel]
    ring

/-- The sum over the cusps of the root value of `T f` does not depend on the place. -/
theorem sum_ray_zero_heckeTwo (q : ℕ) (t : ℂ) (Q₀ : G) (w : G') (f : Vertex G (DeadLabel G') → ℂ) :
    ∑ P : G, heckeTwo q t Q₀ w f (.ray P 0) =
      (Fintype.card G : ℂ) * ((q : ℂ) * ((q : ℂ) - 1) * f .core) + (q : ℂ) * ∑ P, f (.ray P 0) +
        ∑ P, f (.ray P 2) := by
  have e1 : ∑ P : G, f (.ray (-P - Q₀) 0) = ∑ P, f (.ray P 0) :=
    Equiv.sum_comp ((Equiv.neg G).trans (Equiv.subRight Q₀)) (fun P => f (.ray P 0))
  have e2 : ∑ P : G, f (.ray (P - Q₀) 2) = ∑ P, f (.ray P 2) :=
    Equiv.sum_comp (Equiv.subRight Q₀) (fun P => f (.ray P 2))
  simp only [heckeTwo_ray_zero, Finset.sum_add_distrib, ← Finset.mul_sum, e1, e2, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  ring

/-- **Hecke operators at places of degree two commute.** -/
theorem Channels.heckeTwo_comm (B : Channels G (DeadLabel G')) (hG : ∀ P : G, 2 • P = 0 → P = 0)
    (hG' : ∀ Q : G', 2 • Q = 0 → Q = 0) (Q₀ Q₁ : G) (w u : G') (f : Vertex G (DeadLabel G') → ℂ)
    (v : Vertex G (DeadLabel G')) :
    heckeTwo B.q B.trace Q₀ w (heckeTwo B.q B.trace Q₁ u f) v =
      heckeTwo B.q B.trace Q₁ u (heckeTwo B.q B.trace Q₀ w f) v := by
  have hS₁ := B.heckeTwo_comm_waveOp hG hG' Q₁ u f .core
  have hS₀ := B.heckeTwo_comm_waveOp hG hG' Q₀ w f .core
  rw [heckeTwo_core] at hS₁ hS₀
  have hS : waveOp B.q (heckeTwo B.q B.trace Q₁ u f) .core =
      waveOp B.q (heckeTwo B.q B.trace Q₀ w f) .core := by rw [hS₁, hS₀]
  have hshift (a b : G') : deadShift B.q f b a = deadShift B.q f a b := by
    unfold deadShift
    rw [show a - b = -(b - a) by abel, deadTerm_neg, add_comm a b]
  have hdouble (Q : G') : deadShift B.q f u (Q + w) + deadShift B.q f u (Q - w) =
      deadShift B.q f w (Q + u) + deadShift B.q f w (Q - u) := by
    unfold deadShift
    rw [show Q + w + u = Q + u + w by abel, show Q + w - u = Q - u + w by abel,
      show Q - w + u = Q + u - w by abel, show Q - w - u = Q - u - w by abel]
    ring
  rcases v with _ | d | x | L | ⟨P, _ | _ | _ | _ | k⟩
  · simp only [heckeTwo_core, sum_ray_zero_heckeTwo]
  · rw [heckeTwo_dead', heckeTwo_dead', hS]
    obtain ⟨x, hx⟩ := d
    induction x using Quotient.inductionOn with
    | h Q =>
      change _ - deadShift B.q _ w Q = _ - deadShift B.q _ u Q
      unfold deadShift
      rw [deadTerm_heckeTwo, deadTerm_heckeTwo, deadTerm_heckeTwo, deadTerm_heckeTwo]
      linear_combination ((B.q : ℂ)) * hdouble Q
  · induction x using Quotient.inductionOn with
    | h P =>
      change heckeTwo B.q B.trace Q₀ w _ (.neck (Branch.mk P)) =
        heckeTwo B.q B.trace Q₁ u _ (.neck (Branch.mk P))
      rw [heckeTwo_neck, heckeTwo_neck, hS]
      unfold neckTwo
      by_cases h : 2 • P = 0
      · have hneg : -P = P := by
          have : P + P = 0 := by rw [← two_nsmul]; exact h
          exact neg_eq_of_add_eq_zero_left this
        simp only [if_pos h, deadTerm_heckeTwo]
        have e1 : heckeTwo B.q B.trace Q₁ u f (.ray (P - Q₀) 1) =
            (B.q : ℂ) * gapOp B.q f (P - Q₀ + Q₁) + f (.ray (P - Q₀ - Q₁) 3) := rfl
        have e2 : heckeTwo B.q B.trace Q₀ w f (.ray (P - Q₁) 1) =
            (B.q : ℂ) * gapOp B.q f (P - Q₁ + Q₀) + f (.ray (P - Q₁ - Q₀) 3) := rfl
        have e3 : gapOp B.q f (P - Q₀ + Q₁) = gapOp B.q f (P - Q₁ + Q₀) := by
          rw [← gapOp_neg]
          congr 1
          calc -(P - Q₀ + Q₁) = -P + Q₀ - Q₁ := by abel
            _ = P + Q₀ - Q₁ := by rw [hneg]
            _ = P - Q₁ + Q₀ := by abel
        rw [e1, e2, e3, show P - Q₁ - Q₀ = P - Q₀ - Q₁ by abel, hshift u w]
      · simp only [if_neg h]
        have e1 : heckeTwo B.q B.trace Q₁ u f (.ray (P - Q₀) 1) =
            (B.q : ℂ) * gapOp B.q f (P - Q₀ + Q₁) + f (.ray (P - Q₀ - Q₁) 3) := rfl
        have e2 : heckeTwo B.q B.trace Q₁ u f (.ray (-P - Q₀) 1) =
            (B.q : ℂ) * gapOp B.q f (-P - Q₀ + Q₁) + f (.ray (-P - Q₀ - Q₁) 3) := rfl
        have e3 : heckeTwo B.q B.trace Q₀ w f (.ray (P - Q₁) 1) =
            (B.q : ℂ) * gapOp B.q f (P - Q₁ + Q₀) + f (.ray (P - Q₁ - Q₀) 3) := rfl
        have e4 : heckeTwo B.q B.trace Q₀ w f (.ray (-P - Q₁) 1) =
            (B.q : ℂ) * gapOp B.q f (-P - Q₁ + Q₀) + f (.ray (-P - Q₁ - Q₀) 3) := rfl
        have g1 : gapOp B.q f (P - Q₀ + Q₁) = gapOp B.q f (-P - Q₁ + Q₀) := by
          rw [← gapOp_neg]
          congr 1
          abel
        have g2 : gapOp B.q f (-P - Q₀ + Q₁) = gapOp B.q f (P - Q₁ + Q₀) := by
          rw [← gapOp_neg]
          congr 1
          abel
        rw [e1, e2, e3, e4, g1, g2, show P - Q₁ - Q₀ = P - Q₀ - Q₁ by abel,
          show -P - Q₁ - Q₀ = -P - Q₀ - Q₁ by abel]
        ring
  · rw [heckeTwo_cap, heckeTwo_cap, deadTerm_heckeTwo, deadTerm_heckeTwo, hshift u w]
    have hneg : -L.1 = L.1 := by
      have : L.1 + L.1 = 0 := by rw [← two_nsmul]; exact L.2
      exact neg_eq_of_add_eq_zero_left this
    have e1 : heckeTwo B.q B.trace Q₁ u f (.ray (L.1 - Q₀) 1) =
        (B.q : ℂ) * gapOp B.q f (L.1 - Q₀ + Q₁) + f (.ray (L.1 - Q₀ - Q₁) 3) := rfl
    have e2 : heckeTwo B.q B.trace Q₀ w f (.ray (L.1 - Q₁) 1) =
        (B.q : ℂ) * gapOp B.q f (L.1 - Q₁ + Q₀) + f (.ray (L.1 - Q₁ - Q₀) 3) := rfl
    have e3 : gapOp B.q f (L.1 - Q₀ + Q₁) = gapOp B.q f (L.1 - Q₁ + Q₀) := by
      rw [← gapOp_neg]
      congr 1
      calc -(L.1 - Q₀ + Q₁) = -L.1 + Q₀ - Q₁ := by abel
        _ = L.1 + Q₀ - Q₁ := by rw [hneg]
        _ = L.1 - Q₁ + Q₀ := by abel
    rw [e1, e2, e3, show L.1 - Q₁ - Q₀ = L.1 - Q₀ - Q₁ by abel]
  · have e1 : heckeTwo B.q B.trace Q₀ w (heckeTwo B.q B.trace Q₁ u f) (.ray P 0) =
        (B.q : ℂ) * ((B.q : ℂ) - 1) * heckeTwo B.q B.trace Q₁ u f .core +
          (B.q : ℂ) * ((B.q : ℂ) * ((B.q : ℂ) - 1) * f .core +
            (B.q : ℂ) * f (.ray (-(-P - Q₀) - Q₁) 0) + f (.ray (-P - Q₀ - Q₁) 2)) +
          ((B.q : ℂ) ^ 2 * f (.ray (P - Q₀ + Q₁) 0) + f (.ray (P - Q₀ - Q₁) 4)) := rfl
    have e2 : heckeTwo B.q B.trace Q₁ u (heckeTwo B.q B.trace Q₀ w f) (.ray P 0) =
        (B.q : ℂ) * ((B.q : ℂ) - 1) * heckeTwo B.q B.trace Q₀ w f .core +
          (B.q : ℂ) * ((B.q : ℂ) * ((B.q : ℂ) - 1) * f .core +
            (B.q : ℂ) * f (.ray (-(-P - Q₁) - Q₀) 0) + f (.ray (-P - Q₁ - Q₀) 2)) +
          ((B.q : ℂ) ^ 2 * f (.ray (P - Q₁ + Q₀) 0) + f (.ray (P - Q₁ - Q₀) 4)) := rfl
    rw [e1, e2, heckeTwo_core, heckeTwo_core, show -(-P - Q₀) - Q₁ = P - Q₁ + Q₀ by abel,
      show -(-P - Q₁) - Q₀ = P - Q₀ + Q₁ by abel, show -P - Q₁ - Q₀ = -P - Q₀ - Q₁ by abel,
      show P - Q₁ - Q₀ = P - Q₀ - Q₁ by abel]
    have e3 : ∑ P : G, f (.ray P 0) = ∑ P : G, f (.ray P 0) := rfl
    ring
  · have e1 : heckeTwo B.q B.trace Q₀ w (heckeTwo B.q B.trace Q₁ u f) (.ray P (0 + 1)) =
        (B.q : ℂ) * gapOp B.q (heckeTwo B.q B.trace Q₁ u f) (P + Q₀) +
          ((B.q : ℂ) ^ 2 * f (.ray (P - Q₀ + Q₁) 1) + f (.ray (P - Q₀ - Q₁) 5)) := rfl
    have e2 : heckeTwo B.q B.trace Q₁ u (heckeTwo B.q B.trace Q₀ w f) (.ray P (0 + 1)) =
        (B.q : ℂ) * gapOp B.q (heckeTwo B.q B.trace Q₀ w f) (P + Q₁) +
          ((B.q : ℂ) ^ 2 * f (.ray (P - Q₁ + Q₀) 1) + f (.ray (P - Q₁ - Q₀) 5)) := rfl
    rw [e1, e2, gapOp_heckeTwo, gapOp_heckeTwo, show P + Q₀ - Q₁ = P - Q₁ + Q₀ by abel,
      show P + Q₁ - Q₀ = P - Q₀ + Q₁ by abel, show -(P + Q₀) - Q₁ = -(P + Q₁) - Q₀ by abel,
      show P - Q₁ - Q₀ = P - Q₀ - Q₁ by abel]
    ring
  · have e1 : heckeTwo B.q B.trace Q₀ w (heckeTwo B.q B.trace Q₁ u f) (.ray P (0 + 1 + 1)) =
        (B.q : ℂ) ^ 2 * ((B.q : ℂ) * ((B.q : ℂ) - 1) * f .core +
            (B.q : ℂ) * f (.ray (-(P + Q₀) - Q₁) 0) + f (.ray (P + Q₀ - Q₁) 2)) +
          ((B.q : ℂ) ^ 2 * f (.ray (P - Q₀ + Q₁) 2) + f (.ray (P - Q₀ - Q₁) 6)) := rfl
    have e2 : heckeTwo B.q B.trace Q₁ u (heckeTwo B.q B.trace Q₀ w f) (.ray P (0 + 1 + 1)) =
        (B.q : ℂ) ^ 2 * ((B.q : ℂ) * ((B.q : ℂ) - 1) * f .core +
            (B.q : ℂ) * f (.ray (-(P + Q₁) - Q₀) 0) + f (.ray (P + Q₁ - Q₀) 2)) +
          ((B.q : ℂ) ^ 2 * f (.ray (P - Q₁ + Q₀) 2) + f (.ray (P - Q₁ - Q₀) 6)) := rfl
    rw [e1, e2, show -(P + Q₁) - Q₀ = -(P + Q₀) - Q₁ by abel, show P + Q₁ - Q₀ = P - Q₀ + Q₁ by abel,
      show P - Q₁ + Q₀ = P + Q₀ - Q₁ by abel, show P - Q₁ - Q₀ = P - Q₀ - Q₁ by abel]
    ring
  · have e1 : heckeTwo B.q B.trace Q₀ w (heckeTwo B.q B.trace Q₁ u f) (.ray P (0 + 1 + 1 + 1)) =
        (B.q : ℂ) ^ 2 * ((B.q : ℂ) * gapOp B.q f (P + Q₀ + Q₁) + f (.ray (P + Q₀ - Q₁) 3)) +
          ((B.q : ℂ) ^ 2 * f (.ray (P - Q₀ + Q₁) 3) + f (.ray (P - Q₀ - Q₁) 7)) := rfl
    have e2 : heckeTwo B.q B.trace Q₁ u (heckeTwo B.q B.trace Q₀ w f) (.ray P (0 + 1 + 1 + 1)) =
        (B.q : ℂ) ^ 2 * ((B.q : ℂ) * gapOp B.q f (P + Q₁ + Q₀) + f (.ray (P + Q₁ - Q₀) 3)) +
          ((B.q : ℂ) ^ 2 * f (.ray (P - Q₁ + Q₀) 3) + f (.ray (P - Q₁ - Q₀) 7)) := rfl
    rw [e1, e2, show P + Q₁ + Q₀ = P + Q₀ + Q₁ by abel, show P + Q₁ - Q₀ = P - Q₀ + Q₁ by abel,
      show P - Q₁ + Q₀ = P + Q₀ - Q₁ by abel, show P - Q₁ - Q₀ = P - Q₀ - Q₁ by abel]
    ring
  · have e1 : heckeTwo B.q B.trace Q₀ w (heckeTwo B.q B.trace Q₁ u f) (.ray P (k + 1 + 1 + 1 + 1)) =
        (B.q : ℂ) ^ 2 * ((B.q : ℂ) ^ 2 * f (.ray (P + Q₀ + Q₁) k) + f (.ray (P + Q₀ - Q₁) (k + 4))) +
          ((B.q : ℂ) ^ 2 * f (.ray (P - Q₀ + Q₁) (k + 4)) + f (.ray (P - Q₀ - Q₁) (k + 8))) := rfl
    have e2 : heckeTwo B.q B.trace Q₁ u (heckeTwo B.q B.trace Q₀ w f) (.ray P (k + 1 + 1 + 1 + 1)) =
        (B.q : ℂ) ^ 2 * ((B.q : ℂ) ^ 2 * f (.ray (P + Q₁ + Q₀) k) + f (.ray (P + Q₁ - Q₀) (k + 4))) +
          ((B.q : ℂ) ^ 2 * f (.ray (P - Q₁ + Q₀) (k + 4)) + f (.ray (P - Q₁ - Q₀) (k + 8))) := rfl
    rw [e1, e2, show P + Q₁ + Q₀ = P + Q₀ + Q₁ by abel, show P + Q₁ - Q₀ = P - Q₀ + Q₁ by abel,
      show P - Q₁ + Q₀ = P + Q₀ - Q₁ by abel, show P - Q₁ - Q₀ = P - Q₀ - Q₁ by abel]
    ring

/-! ### Edges and positivity -/

/-- **`q² + 1` edges at every vertex.** -/
theorem Channels.heckeTwo_one (B : Channels G (DeadLabel G')) (Q₀ : G) (w : G')
    (v : Vertex G (DeadLabel G')) :
    heckeTwo B.q B.trace Q₀ w (fun _ => (1 : ℂ)) v = (B.q : ℂ) ^ 2 + 1 := by
  have hS : waveOp B.q (fun _ => (1 : ℂ)) (.core : Vertex G (DeadLabel G')) = (B.q : ℂ) + 1 :=
    B.waveOp_one _
  have hdt (Q : G') : deadTerm B.q (fun _ : Vertex G (DeadLabel G') => (1 : ℂ)) Q = (B.q : ℂ) := by
    unfold deadTerm deadTermB
    split_ifs <;> ring
  have hgap (R : G) : gapOp B.q (fun _ : Vertex G (DeadLabel G') => (1 : ℂ)) R = (B.q : ℂ) := by
    unfold gapOp
    split_ifs <;> ring
  rcases v with _ | d | x | L | ⟨P, _ | _ | k⟩
  · rw [heckeTwo_core]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have hh := B.cuspCount_eq
    unfold cuspCount at hh
    rw [hh]
    ring
  · rw [heckeTwo_dead']
    obtain ⟨x, hx⟩ := d
    induction x using Quotient.inductionOn with
    | h Q =>
      change _ - deadShift B.q _ w Q = _
      unfold deadShift
      rw [hdt, hdt, hS]
      ring
  · induction x using Quotient.inductionOn with
    | h P =>
      change heckeTwo B.q B.trace Q₀ w _ (.neck (Branch.mk P)) = _
      rw [heckeTwo_neck, hS]
      unfold neckTwo
      split_ifs
      · rw [hdt]
        ring
      · ring
  · rw [heckeTwo_cap, hdt]
    ring
  · rw [heckeTwo_ray_zero]
    ring
  · have e : heckeTwo B.q B.trace Q₀ w (fun _ => (1 : ℂ)) (.ray P (0 + 1)) =
        (B.q : ℂ) * gapOp B.q (fun _ => (1 : ℂ)) (P + Q₀) + 1 := rfl
    rw [e, hgap]
    ring
  · have e : heckeTwo B.q B.trace Q₀ w (fun _ => (1 : ℂ)) (.ray P (k + 1 + 1)) =
        (B.q : ℂ) ^ 2 * 1 + 1 := rfl
    rw [e]
    ring

/-- **The coefficients are nonnegative**, on every pair of odd groups, for `w ≠ 0`. -/
theorem Channels.heckeTwo_nonneg (B : Channels G (DeadLabel G')) (hG' : ∀ Q : G', 2 • Q = 0 → Q = 0)
    (Q₀ : G) {w : G'} (hw : w ≠ 0) {f : Vertex G (DeadLabel G') → ℂ} (hf : ∀ v, 0 ≤ f v)
    (v : Vertex G (DeadLabel G')) : 0 ≤ heckeTwo B.q B.trace Q₀ w f v := by
  have hqr := B.q_pos
  have hq0 : (0 : ℂ) ≤ (B.q : ℂ) := by simp
  have hq1 : (0 : ℂ) ≤ (B.q : ℂ) - 1 := by
    have := Complex.zero_le_real.mpr (show (0 : ℝ) ≤ (B.q : ℝ) - 1 by linarith)
    simpa using this
  have hq2 : (0 : ℂ) ≤ (B.q : ℂ) + 1 := by
    have := Complex.zero_le_real.mpr (show (0 : ℝ) ≤ (B.q : ℝ) + 1 by linarith)
    simpa using this
  have hq3 : (0 : ℂ) ≤ (B.q : ℂ) ^ 2 - B.q + B.trace := by
    rw [B.trace_eq_ofReal]
    have hle := (abs_le.mp B.abs_traceR_le).1
    have := Complex.zero_le_real.mpr
      (show (0 : ℝ) ≤ (B.q : ℝ) ^ 2 - B.q + B.traceR by nlinarith)
    simpa using this
  have hw' := branchWeight_nonneg (G := G)
  have hDrest (F : Finset (DeadLabel G')) : 0 ≤ ∑ d ∈ F, f (.dead d) :=
    Finset.sum_nonneg fun _ _ => hf _
  have hNsum : 0 ≤ ∑ P : G, branchWeight P * f (.neck (Branch.mk P)) :=
    Finset.sum_nonneg fun P _ => mul_nonneg (hw' P) (hf _)
  have hN0 : ∑ P : G, branchWeight P * f (.neck (Branch.mk P)) =
      f (.neck (Branch.mk 0)) + ∑ P ∈ univ.erase (0 : G), branchWeight P * f (.neck (Branch.mk P)) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : G))]
    simp [branchWeight]
  have hNrest : 0 ≤ ∑ P ∈ univ.erase (0 : G), branchWeight P * f (.neck (Branch.mk P)) :=
    Finset.sum_nonneg fun P _ => mul_nonneg (hw' P) (hf _)
  have hgapnn (R : G) : 0 ≤ gapOp B.q f R := by
    unfold gapOp
    split_ifs
    · exact add_nonneg (mul_nonneg hq1 (hf _)) (hf _)
    · exact mul_nonneg hq0 (hf _)
  -- the dead term at a nonzero class
  have hdtne {Q : G'} (h : Branch.mk Q ≠ Branch.mk 0) :
      deadTerm B.q f Q = (B.q : ℂ) * f (.dead ⟨Branch.mk Q, h⟩) := by
    unfold deadTerm deadTermB
    rw [dif_neg h]
  have hdt0 {Q : G'} (h : Branch.mk Q = Branch.mk 0) :
      deadTerm B.q f Q = ((B.q : ℂ) + 1) * f (.neck (Branch.mk 0)) - f (.cap (capZero G)) := by
    unfold deadTerm deadTermB
    rw [dif_pos h]
  have hmkw : Branch.mk w ≠ Branch.mk (0 : G') := by
    intro h
    rcases mk_eq_mk_iff.mp h with h | h
    · exact hw h.symm
    · apply hw
      simpa [neg_eq_zero, eq_comm] using h
  rcases v with _ | d | x | L | ⟨P, _ | _ | k⟩
  · rw [heckeTwo_core]
    exact add_nonneg (mul_nonneg hq3 (hf _)) (Finset.sum_nonneg fun _ _ => hf _)
  · rw [heckeTwo_dead']
    obtain ⟨x, hx⟩ := d
    induction x using Quotient.inductionOn with
    | h Q =>
      change (0 : ℂ) ≤ _ - deadShift B.q f w Q
      have hQ0 : Q ≠ 0 := by
        rintro rfl
        exact hx rfl
      unfold deadShift
      rw [show waveOp B.q f .core = ∑ d, f (.dead d) +
        ∑ P, branchWeight P * f (.neck (Branch.mk P)) from rfl]
      have hne : Branch.mk (Q + w) ≠ Branch.mk (Q - w) := by
        intro h
        rcases mk_eq_mk_iff.mp h with h | h
        · apply hw
          apply hG'
          rw [two_nsmul]
          have : Q - w + -(Q + w) = 0 := by rw [h]; abel
          have h2 : w + w = 0 := by
            have e : Q - w = Q + w := h
            have : (Q + w) - (Q - w) = 0 := by rw [e]; abel
            have e2 : (Q + w) - (Q - w) = w + w := by abel
            rw [← e2, this]
          exact h2
        · apply hQ0
          apply hG'
          rw [two_nsmul]
          have e2 : Q + Q = (Q - w) + (Q + w) := by abel
          rw [e2, h]
          abel
      by_cases h₁ : Branch.mk (Q + w) = Branch.mk 0
      · have h₂ : Branch.mk (Q - w) ≠ Branch.mk 0 := fun h => hne (h₁.trans h.symm)
        rw [hdt0 h₁, hdtne h₂, ← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨_, h₂⟩ : DeadLabel G')), hN0]
        set D₂ := ∑ d ∈ univ.erase (⟨_, h₂⟩ : DeadLabel G'), f (.dead d)
        set N₂ := ∑ P ∈ univ.erase (0 : G), branchWeight P * f (.neck (Branch.mk P))
        have e : ((B.q : ℂ) + 1) * (f (.dead ⟨_, h₂⟩) + D₂ + (f (.neck (Branch.mk 0)) + N₂)) -
            (((B.q : ℂ) + 1) * f (.neck (Branch.mk 0)) - f (.cap (capZero G)) +
              (B.q : ℂ) * f (.dead ⟨_, h₂⟩)) =
            ((B.q : ℂ) + 1) * (D₂ + N₂) + f (.dead ⟨_, h₂⟩) + f (.cap (capZero G)) := by ring
        rw [e]
        exact add_nonneg (add_nonneg (mul_nonneg hq2 (add_nonneg (hDrest _) hNrest)) (hf _)) (hf _)
      · by_cases h₂ : Branch.mk (Q - w) = Branch.mk 0
        · rw [hdtne h₁, hdt0 h₂,
            ← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨_, h₁⟩ : DeadLabel G')), hN0]
          set D₂ := ∑ d ∈ univ.erase (⟨_, h₁⟩ : DeadLabel G'), f (.dead d)
          set N₂ := ∑ P ∈ univ.erase (0 : G), branchWeight P * f (.neck (Branch.mk P))
          have e : ((B.q : ℂ) + 1) * (f (.dead ⟨_, h₁⟩) + D₂ + (f (.neck (Branch.mk 0)) + N₂)) -
              ((B.q : ℂ) * f (.dead ⟨_, h₁⟩) +
                (((B.q : ℂ) + 1) * f (.neck (Branch.mk 0)) - f (.cap (capZero G)))) =
              ((B.q : ℂ) + 1) * (D₂ + N₂) + f (.dead ⟨_, h₁⟩) + f (.cap (capZero G)) := by ring
          rw [e]
          exact add_nonneg (add_nonneg (mul_nonneg hq2 (add_nonneg (hDrest _) hNrest)) (hf _)) (hf _)
        · have hne' : (⟨_, h₂⟩ : DeadLabel G') ≠ ⟨_, h₁⟩ := by
            intro h
            exact hne (congrArg Subtype.val h).symm
          rw [hdtne h₁, hdtne h₂,
            ← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨_, h₁⟩ : DeadLabel G')),
            ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne', Finset.mem_univ _⟩)]
          set D₂ := ∑ d ∈ (univ.erase (⟨_, h₁⟩ : DeadLabel G')).erase ⟨_, h₂⟩, f (.dead d)
          set N₂ := ∑ P : G, branchWeight P * f (.neck (Branch.mk P))
          have e : ((B.q : ℂ) + 1) * (f (.dead ⟨_, h₁⟩) + (f (.dead ⟨_, h₂⟩) + D₂) + N₂) -
              ((B.q : ℂ) * f (.dead ⟨_, h₁⟩) + (B.q : ℂ) * f (.dead ⟨_, h₂⟩)) =
              ((B.q : ℂ) + 1) * (D₂ + N₂) + f (.dead ⟨_, h₁⟩) + f (.dead ⟨_, h₂⟩) := by ring
          rw [e]
          exact add_nonneg (add_nonneg (mul_nonneg hq2 (add_nonneg (hDrest _) hNsum)) (hf _)) (hf _)
  · induction x using Quotient.inductionOn with
    | h P =>
      change (0 : ℂ) ≤ heckeTwo B.q B.trace Q₀ w f (.neck (Branch.mk P))
      rw [heckeTwo_neck]
      unfold neckTwo
      rw [show waveOp B.q f .core = ∑ d, f (.dead d) +
        ∑ P, branchWeight P * f (.neck (Branch.mk P)) from rfl]
      split_ifs
      · rw [hdtne hmkw, ← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨_, hmkw⟩ : DeadLabel G'))]
        set D₂ := ∑ d ∈ univ.erase (⟨_, hmkw⟩ : DeadLabel G'), f (.dead d)
        set N₂ := ∑ P : G, branchWeight P * f (.neck (Branch.mk P))
        have e : (B.q : ℂ) * (f (.dead ⟨_, hmkw⟩) + D₂ + N₂) - (B.q : ℂ) * f (.dead ⟨_, hmkw⟩) +
            f (.ray (P - Q₀) 1) = (B.q : ℂ) * (D₂ + N₂) + f (.ray (P - Q₀) 1) := by ring
        rw [e]
        exact add_nonneg (mul_nonneg hq0 (add_nonneg (hDrest _) hNsum)) (hf _)
      · exact add_nonneg (add_nonneg (mul_nonneg hq1 (add_nonneg (hDrest _) hNsum)) (hf _)) (hf _)
  · rw [heckeTwo_cap, hdtne hmkw]
    exact add_nonneg (mul_nonneg hq2 (hf _)) (mul_nonneg hq1 (mul_nonneg hq0 (hf _)))
  · rw [heckeTwo_ray_zero]
    exact add_nonneg (add_nonneg (mul_nonneg (mul_nonneg hq0 hq1) (hf _)) (mul_nonneg hq0 (hf _))) (hf _)
  · change (0 : ℂ) ≤ (B.q : ℂ) * gapOp B.q f (P + Q₀) + f (.ray (P - Q₀) 3)
    exact add_nonneg (mul_nonneg hq0 (hgapnn _)) (hf _)
  · change (0 : ℂ) ≤ (B.q : ℂ) ^ 2 * f (.ray (P + Q₀) k) + f (.ray (P - Q₀) (k + 4))
    exact add_nonneg (mul_nonneg (by simpa [pow_two] using mul_nonneg hq0 hq0) (hf _)) (hf _)

/-! ### Rigidity at degree two -/

theorem deadTerm_smul (q : ℕ) (a : ℂ) (f : Vertex G (DeadLabel G') → ℂ) (Q : G') :
    deadTerm q (fun u => a * f u) Q = a * deadTerm q f Q := by
  unfold deadTerm deadTermB
  split_ifs <;> ring

theorem gapOp_smul (q : ℕ) (a : ℂ) (f : Vertex G (DeadLabel G') → ℂ) (R : G) :
    gapOp q (fun u => a * f u) R = a * gapOp q f R := by
  unfold gapOp
  split_ifs <;> ring

theorem heckeTwo_smul (q : ℕ) (t : ℂ) (Q₀ : G) (w : G') (a : ℂ) (f : Vertex G (DeadLabel G') → ℂ)
    (v : Vertex G (DeadLabel G')) :
    heckeTwo q t Q₀ w (fun u => a * f u) v = a * heckeTwo q t Q₀ w f v := by
  have hS : waveOp q (fun u => a * f u) (.core : Vertex G (DeadLabel G')) = a * waveOp q f .core :=
    waveOp_smul q a f .core
  rcases v with _ | d | x | L | ⟨P, _ | _ | k⟩
  · simp only [heckeTwo_core, mul_add, Finset.mul_sum]
    ring
  · rw [heckeTwo_dead', heckeTwo_dead', hS]
    obtain ⟨x, hx⟩ := d
    induction x using Quotient.inductionOn with
    | h Q =>
      change _ - deadShift q _ w Q = a * (_ - deadShift q f w Q)
      unfold deadShift
      rw [deadTerm_smul, deadTerm_smul]
      ring
  · induction x using Quotient.inductionOn with
    | h P =>
      change heckeTwo q t Q₀ w _ (.neck (Branch.mk P)) = a * heckeTwo q t Q₀ w f (.neck (Branch.mk P))
      rw [heckeTwo_neck, heckeTwo_neck, hS]
      unfold neckTwo
      split_ifs
      · rw [deadTerm_smul]
        ring
      · ring
  · simp only [heckeTwo_cap, deadTerm_smul]
    ring
  · simp only [heckeTwo_ray_zero]
    ring
  · change (q : ℂ) * gapOp q _ (P + Q₀) + a * f (.ray (P - Q₀) 3) =
      a * ((q : ℂ) * gapOp q f (P + Q₀) + f (.ray (P - Q₀) 3))
    rw [gapOp_smul]
    ring
  · change (q : ℂ) ^ 2 * (a * f (.ray (P + Q₀) k)) + a * f (.ray (P - Q₀) (k + 4)) =
      a * ((q : ℂ) ^ 2 * f (.ray (P + Q₀) k) + f (.ray (P - Q₀) (k + 4)))
    ring

/-- **Hecke of degree two acts on a resonance by `X² + Y²`**, wherever the resonance is. -/
theorem Channels.heckeTwo_resonance (B : Channels G (DeadLabel G'))
    (hG : ∀ P : G, 2 • P = 0 → P = 0) (hG' : ∀ Q : G', 2 • Q = 0 → Q = 0) (Q₀ : G) (w : G') {X Y : ℂ}
    (hXY : X * Y = B.q) (hne : X ≠ Y) (hlam : X + Y ≠ 0) {f : Vertex G (DeadLabel G') → ℂ} {c : G → ℂ}
    (hf : IsOutgoing B.q X Y f c) (v : Vertex G (DeadLabel G')) :
    heckeTwo B.q B.trace Q₀ w f v = (X ^ 2 + Y ^ 2) * f v := by
  refine hecke_rigidity B (heckeTwo B.q B.trace Q₀ w) (heckeTwo_smul _ _ _ _)
    (B.heckeTwo_comm_waveOp hG hG' Q₀ w) 2 (fun P => P + Q₀) (fun P => P - Q₀) ?_ hXY hne hlam hf v
  intro g P j
  rw [show 2 + j = j + 2 by ring, heckeTwo_ray_add_two, show 2 * 2 + j = j + 4 by ring]

/-! ### The fakes carry it -/

/-- The classes of nonzero points of an odd group are counted by `(#G' - 1)/2`. -/
theorem two_card_deadLabel (hG' : ∀ Q : G', 2 • Q = 0 → Q = 0) :
    2 * Fintype.card (DeadLabel G') + 1 = Fintype.card G' := by
  have hsum := sum_deadLabel (G' := G') (fun _ => (1 : ℂ))
  rw [sum_weighted_odd hG'] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hsum
  have hc : (2 * (Fintype.card (DeadLabel G') : ℂ) + 1) = Fintype.card G' := by
    linear_combination 2 * hsum
  exact_mod_cast hc

/-- In a cyclic group of odd order, only zero is two-torsion. -/
theorem two_nsmul_eq_zero_zmod {N : ℕ} [NeZero N] (hN : Odd N) (P : ZMod N) (h : 2 • P = 0) : P = 0 := by
  have hunit : IsUnit (2 : ZMod N) := by
    have : IsUnit ((2 : ℕ) : ZMod N) :=
      (ZMod.isUnit_iff_coprime 2 N).mpr (Nat.coprime_two_left.mpr hN)
    simpa using this
  have h2 : (2 : ZMod N) * P = 0 := by simpa [two_nsmul, two_mul] using h
  exact (hunit.mul_right_eq_zero).mp h2

/-- **A pair of cyclic groups of odd order with `N + N' = 2(q+1)` gives a black hole**, with its second group. No
curve is needed. -/
def oddPairChannels (q N N' : ℕ) [NeZero N] [NeZero N'] (hN : Odd N) (hN' : Odd N') (hq : 2 ≤ q)
    (hsum : N + N' = 2 * (q + 1)) : Channels (ZMod N) (DeadLabel (ZMod N')) where
  q := q
  two_le := hq
  count := by
    have h := two_card_deadLabel (two_nsmul_eq_zero_zmod hN')
    rw [card_twoTorsion_zmod hN, ZMod.card]
    rw [ZMod.card] at h
    omega

/-- **Positivity of Hecke at degree two does not exclude the fakes.** For `q ≥ 8`, the black hole with `N = 3`, `N' =
2q - 1` carries commuting positive operators at every place of degree two, with `q² + 1` edges, and has a resonance slower than
universal. -/
theorem universal_damping_not_forced_with_degree_two {q : ℕ} (hq : 8 ≤ q) :
    let B := oddPairChannels q 3 (2 * (q - 1) + 1) (by decide) ⟨q - 1, rfl⟩ (by omega) (by omega)
    (∀ (Q₀ : ZMod 3) (w : ZMod (2 * (q - 1) + 1)) (f) (v),
        waveOp B.q (heckeTwo B.q B.trace Q₀ w f) v = heckeTwo B.q B.trace Q₀ w (waveOp B.q f) v) ∧
      (∀ (Q₀ Q₁ : ZMod 3) (w u : ZMod (2 * (q - 1) + 1)) (f) (v),
        heckeTwo B.q B.trace Q₀ w (heckeTwo B.q B.trace Q₁ u f) v =
          heckeTwo B.q B.trace Q₁ u (heckeTwo B.q B.trace Q₀ w f) v) ∧
      (∀ (Q₀ : ZMod 3) (w : ZMod (2 * (q - 1) + 1)), w ≠ 0 → ∀ f, (∀ v, 0 ≤ f v) → ∀ v,
        0 ≤ heckeTwo B.q B.trace Q₀ w f v) ∧
      (∀ (Q₀ : ZMod 3) (w : ZMod (2 * (q - 1) + 1)) (v),
        heckeTwo B.q B.trace Q₀ w (fun _ => (1 : ℂ)) v = (B.q : ℂ) ^ 2 + 1) ∧
      ∃ (X Y : ℂ) (f : Vertex (ZMod 3) (DeadLabel (ZMod (2 * (q - 1) + 1))) → ℂ) (c : ZMod 3 → ℂ),
        f ≠ 0 ∧ IsOutgoing B.q X Y f c ∧ (B.q : ℝ) < Complex.normSq (X ^ 2) := by
  intro B
  have hG : ∀ P : ZMod 3, 2 • P = 0 → P = 0 := two_nsmul_eq_zero_zmod (by decide)
  have hG' : ∀ Q : ZMod (2 * (q - 1) + 1), 2 • Q = 0 → Q = 0 :=
    two_nsmul_eq_zero_zmod ⟨q - 1, rfl⟩
  refine ⟨fun Q₀ w f v => B.heckeTwo_comm_waveOp hG hG' Q₀ w f v,
    fun Q₀ Q₁ w u f v => B.heckeTwo_comm hG hG' Q₀ Q₁ w u f v, fun Q₀ w hw f hf v => B.heckeTwo_nonneg hG' Q₀ hw hf v, fun Q₀ w v => B.heckeTwo_one Q₀ w v, ?_⟩
  have htr : B.traceR = (q : ℝ) - 2 := by
    show (q : ℝ) + 1 - Fintype.card (ZMod 3) = _
    rw [ZMod.card]
    push_cast
    ring
  have hq' : (8 : ℝ) ≤ q := by exact_mod_cast hq
  have hBq : (B.q : ℝ) = q := rfl
  obtain ⟨X, Y, f, c, hf0, hf, hbig, _⟩ := exists_slow_resonance B (by rw [htr, hBq]; nlinarith)
  exact ⟨X, Y, f, c, hf0, hf, hbig⟩

end GaloisForLFunctions.ArithmeticScatteringHolography

end
