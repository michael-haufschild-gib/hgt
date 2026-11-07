import GaloisForLFunctions.ArithmeticScatteringHolography.TheFullHeckeFamily

/-!
# Hecke at every class

`P_d(T_Q)` has class `d Q`, so it misses the classes outside `d·G`. A place of degree `d` can have any class, and the operators exist on every black hole with odd groups. They are polynomials in `A`, `T_Q` and
`heckeTwo`:

  `S(1, Q) = T_Q`, `S(2, Q) = T_{Q, 0}`, `S(d + 2, Q) = A S(d + 1, Q) - q S(d, Q)`  (`heckeClass`).

So they commute with each other (`heckeClass_comm`), they have the shape of Hecke of degree `d` and class `Q` in the cusps (`heckeClass_ray`), `q^d + 1` edges (`heckeClass_one`), and they act on a resonance by `X^d + Y^d`
(`heckeClass_resonance`). Off the rays they are the propagator of the function with its cusps translated by `Q` (`heckeClass_off_ray`), so their positivity comes from the positivity of the propagator: all coefficients are
nonnegative for `d ≥ 3` and `q ≥ 7` (`heckeClass_nonneg`), and the correction `(-q)^m Λ_w` at even degree keeps this for `w ≠ 0` (`heckeClass_add_theta_nonneg`). So every class at every degree is carried by the fakes
(`universal_damping_not_forced_at_every_class`).
-/

open Finset
open scoped ComplexOrder

noncomputable section

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.ArithmeticScatteringHolography

variable {G G' : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] [AddCommGroup G'] [DecidableEq G']
  [Fintype G']

/-- **Hecke of degree `d` and class `Q`.** -/
def heckeClass (q : ℕ) (t : ℂ) (Q : G) : ℕ → (Vertex G (DeadLabel G') → ℂ) → Vertex G (DeadLabel G') → ℂ
  | 0, f => f
  | 1, f => heckeOp q Q f
  | 2, f => heckeTwo q t Q (0 : G') f
  | d + 3, f => fun v => waveOp q (heckeClass q t Q (d + 2) f) v - (q : ℂ) * heckeClass q t Q (d + 1) f v

theorem heckeClass_add_three (q : ℕ) (t : ℂ) (Q : G) (d : ℕ) (f : Vertex G (DeadLabel G') → ℂ)
    (v : Vertex G (DeadLabel G')) :
    heckeClass q t Q (d + 3) f v =
      waveOp q (heckeClass q t Q (d + 2) f) v - (q : ℂ) * heckeClass q t Q (d + 1) f v := rfl

/-- The cusps translated by `Q`. -/
def transCusp (Q : G) : Vertex G (DeadLabel G') → Vertex G (DeadLabel G')
  | .ray R j => .ray (R - Q) j
  | v => v

/-- The function with its cusps translated. -/
def shiftQ (Q : G) (f : Vertex G (DeadLabel G') → ℂ) : Vertex G (DeadLabel G') → ℂ :=
  fun v => f (transCusp Q v)

variable (B : Channels G (DeadLabel G')) (hG : ∀ P : G, 2 • P = 0 → P = 0)
  (hG' : ∀ Q : G', 2 • Q = 0 → Q = 0)

local notation "Sc" => heckeClass B.q B.trace

/-- The rows of `P₂` of the translated function. -/
theorem chebOp_two_shift (Q : G) (f : Vertex G (DeadLabel G') → ℂ) (v : Vertex G (DeadLabel G')) :
    chebOp B.q 2 (shiftQ Q f) v =
      waveOp B.q (waveOp B.q (shiftQ Q f)) v - (B.q : ℂ) * (2 * shiftQ Q f v) := rfl

theorem gapOp_shiftQ (q : ℕ) (Q R : G) (f : Vertex G (DeadLabel G') → ℂ) :
    gapOp q (shiftQ Q f) R = gapOp q f R := by
  unfold gapOp
  split_ifs <;> rfl

theorem waveOp_shiftQ_core (q : ℕ) (Q : G) (f : Vertex G (DeadLabel G') → ℂ) :
    waveOp q (shiftQ Q f) .core = waveOp q f .core := rfl

theorem sum_shift_ray (Q : G) (f : Vertex G (DeadLabel G') → ℂ) (k : ℕ) :
    ∑ P : G, shiftQ Q f (.ray P k) = ∑ P, f (.ray P k) :=
  Equiv.sum_comp (Equiv.subRight Q) (fun P => f (.ray P k))

/-- **At degree one the operator is the wave operator of the translated function, off the rays.** -/
theorem off_ray_one (Q : G) (f : Vertex G (DeadLabel G') → ℂ) :
    heckeOp B.q Q f .core = waveOp B.q (shiftQ Q f) .core ∧
      (∀ d, heckeOp B.q Q f (.dead d) = waveOp B.q (shiftQ Q f) (.dead d)) ∧
      (∀ P, heckeOp B.q Q f (.neck (Branch.mk P)) = waveOp B.q (shiftQ Q f) (.neck (Branch.mk P))) ∧
      (∀ L, heckeOp B.q Q f (.cap L) = waveOp B.q (shiftQ Q f) (.cap L)) := by
  refine ⟨rfl, fun _ => rfl, fun P => ?_, fun _ => rfl⟩
  rw [heckeOp_neck, waveOp_neck]
  rfl

/-- **At degree two the operator is `P₂` of the translated function, off the rays.** -/
theorem off_ray_two (Q : G) (f : Vertex G (DeadLabel G') → ℂ) :
    heckeTwo B.q B.trace Q (0 : G') f .core = chebOp B.q 2 (shiftQ Q f) .core ∧
      (∀ d, heckeTwo B.q B.trace Q (0 : G') f (.dead d) = chebOp B.q 2 (shiftQ Q f) (.dead d)) ∧
      (∀ P, heckeTwo B.q B.trace Q (0 : G') f (.neck (Branch.mk P)) =
        chebOp B.q 2 (shiftQ Q f) (.neck (Branch.mk P))) ∧
      (∀ L, heckeTwo B.q B.trace Q (0 : G') f (.cap L) = chebOp B.q 2 (shiftQ Q f) (.cap L)) := by
  have hS : waveOp B.q (shiftQ Q f) .core = waveOp B.q f .core := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [chebOp_two_shift, B.waveOp_waveOp_core, heckeTwo_core, sum_shift_ray]
    show _ = _ - (B.q : ℂ) * (2 * f .core)
    show _ = ((B.q : ℂ) ^ 2 + B.q + B.trace) * f .core + _ - _
    ring
  · intro d
    rw [chebOp_two_shift, heckeTwo_dead', waveOp_dead, hS]
    obtain ⟨x, hx⟩ := d
    induction x using Quotient.inductionOn with
    | h R =>
      have hx' : Branch.mk R ≠ Branch.mk 0 := hx
      change _ - deadShift B.q f 0 R = _ - (B.q : ℂ) * (2 * f (.dead ⟨Branch.mk R, hx'⟩))
      unfold deadShift
      rw [add_zero, sub_zero]
      have e : deadTerm B.q f R = (B.q : ℂ) * f (.dead ⟨Branch.mk R, hx'⟩) := by
        unfold deadTerm deadTermB
        rw [dif_neg hx']
      rw [e]
      ring
  · intro P
    rw [chebOp_two_shift, heckeTwo_neck, waveOp_neck]
    unfold neckTwo neckOp
    by_cases h : 2 • P = 0
    · have hneg : -P = P := by
        have : P + P = 0 := by rw [← two_nsmul]; exact h
        exact neg_eq_of_add_eq_zero_left this
      simp only [if_pos h, waveOp_ray_zero, gapOp_shiftQ, hS]
      have e1 : shiftQ Q f (.ray P 1) = f (.ray (P - Q) 1) := rfl
      have e2 : shiftQ Q f (.neck (Branch.mk P)) = f (.neck (Branch.mk P)) := rfl
      rw [e1, e2]
      unfold gapOp deadTerm deadTermB
      obtain rfl : P = 0 := hG P h
      rw [dif_pos h, dif_pos rfl]
      have hc : (⟨0, h⟩ : TwoTorsion G) = capZero G := rfl
      rw [hc]
      ring
    · simp only [if_neg h, waveOp_ray_zero, gapOp_shiftQ, hS]
      have e1 : shiftQ Q f (.ray P 1) = f (.ray (P - Q) 1) := rfl
      have e2 : shiftQ Q f (.ray (-P) 1) = f (.ray (-P - Q) 1) := rfl
      have e3 : shiftQ Q f (.neck (Branch.mk P)) = f (.neck (Branch.mk P)) := rfl
      rw [e1, e2, e3]
      have h' : ¬ 2 • (-P) = 0 := by rwa [two_nsmul_neg_eq_zero_iff]
      unfold gapOp
      rw [dif_neg h, dif_neg h', Branch.mk_neg]
      ring
  · intro L
    have hL : L = capZero G := Subtype.ext (hG L.1 L.2)
    subst hL
    rw [chebOp_two_shift, heckeTwo_cap, waveOp_cap, waveOp_ray_zero, gapOp_shiftQ]
    have hz : (capZero G).1 = 0 := rfl
    have e1 : shiftQ Q f (.ray (capZero G).1 1) = f (.ray (0 - Q) 1) := rfl
    have e2 : shiftQ Q f (.cap (capZero G)) = f (.cap (capZero G)) := rfl
    have e3 : deadTerm B.q f (0 : G') = ((B.q : ℂ) + 1) * f (.neck (Branch.mk 0)) - f (.cap (capZero G)) :=
      deadTerm_zero_eq B.q f
    rw [e1, e2, hz, gapOp_zero_eq, e3]
    ring

end GaloisForLFunctions.ArithmeticScatteringHolography

end
