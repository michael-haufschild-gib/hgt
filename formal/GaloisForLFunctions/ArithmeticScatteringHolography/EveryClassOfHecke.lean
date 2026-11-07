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

include hG in
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

/-! ### Rows of the family -/

/-- `S(d, Q)` agrees with the propagator of the translated function off the rays. -/
def OffRay (Q : G) (d : ℕ) (f : Vertex G (DeadLabel G') → ℂ) : Prop :=
  Sc Q d f .core = chebOp B.q d (shiftQ Q f) .core ∧
    (∀ x, Sc Q d f (.dead x) = chebOp B.q d (shiftQ Q f) (.dead x)) ∧
    (∀ P, Sc Q d f (.neck (Branch.mk P)) = chebOp B.q d (shiftQ Q f) (.neck (Branch.mk P))) ∧
    (∀ L, Sc Q d f (.cap L) = chebOp B.q d (shiftQ Q f) (.cap L))

theorem OffRay.gap {Q : G} {d : ℕ} {f : Vertex G (DeadLabel G') → ℂ} (h : OffRay B Q d f) (R : G) :
    gapOp B.q (Sc Q d f) R = gapOp B.q (chebOp B.q d (shiftQ Q f)) R := by
  obtain ⟨_, _, h3, h4⟩ := h
  unfold gapOp
  split_ifs
  · rw [h3, h4]
  · rw [h3]

/-- d'Alembert for the family: the backward part of the ray only feels the depth. -/
theorem heckeClass_ray_succ (Q : G) (d : ℕ) (f : Vertex G (DeadLabel G') → ℂ) (R : G) (k : ℕ) :
    Sc Q (d + 2) f (.ray R (k + 1)) =
      (B.q : ℂ) * Sc Q (d + 1) f (.ray R k) + f (.ray (R - Q) (k + d + 3)) -
        (B.q : ℂ) * f (.ray (R - Q) (k + d + 1)) := by
  induction d generalizing k with
  | zero =>
    show heckeTwo B.q B.trace Q (0 : G') f (.ray R (k + 1)) =
      (B.q : ℂ) * heckeOp B.q Q f (.ray R k) + _ - _
    rcases k with _ | k
    · have e1 : heckeTwo B.q B.trace Q (0 : G') f (.ray R (0 + 1)) =
          (B.q : ℂ) * gapOp B.q f (R + Q) + f (.ray (R - Q) 3) := rfl
      rw [e1, heckeOp_ray_zero]
      simp only [zero_add]
      ring
    · have e1 : heckeTwo B.q B.trace Q (0 : G') f (.ray R (k + 1 + 1)) =
          (B.q : ℂ) ^ 2 * f (.ray (R + Q) k) + f (.ray (R - Q) (k + 4)) := rfl
      rw [e1, heckeOp_ray_succ]
      simp only [add_zero]
      rw [show k + 1 + 0 + 3 = k + 4 by ring, show k + 1 + 0 + 1 = k + 2 by ring]
      ring
  | succ d ih =>
    rw [show d + 1 + 2 = d + 3 by ring, heckeClass_add_three, waveOp_ray_succ, ih (k + 1)]
    rw [show d + 2 = d + 1 + 1 by ring]
    rw [show k + 1 + d + 3 = k + (d + 1) + 3 by ring, show k + 1 + d + 1 = k + (d + 1) + 1 by ring]
    ring

/-- The echo part of the family. -/
def classEcho (Q : G) (f : Vertex G (DeadLabel G') → ℂ) (R : G) (d k : ℕ) : ℂ :=
  Sc Q d f (.ray R k) - f (.ray (R - Q) (k + d))

theorem classEcho_succ (Q : G) (d : ℕ) (f : Vertex G (DeadLabel G') → ℂ) (R : G) (k : ℕ) :
    classEcho B Q f R (d + 2) (k + 1) = (B.q : ℂ) * classEcho B Q f R (d + 1) k := by
  unfold classEcho
  rw [heckeClass_ray_succ, show k + 1 + (d + 2) = k + d + 3 by ring, show k + (d + 1) = k + d + 1 by ring]
  ring

/-- The root of a ray in the family, from the gap term. -/
theorem heckeClass_root (Q : G) (d : ℕ) (f : Vertex G (DeadLabel G') → ℂ) (R : G) :
    Sc Q (d + 3) f (.ray R 0) =
      gapOp B.q (Sc Q (d + 2) f) R + f (.ray (R - Q) (d + 3)) -
        (B.q : ℂ) * f (.ray (R - Q) (d + 1)) := by
  rw [heckeClass_add_three, waveOp_ray_zero, show (1 : ℕ) = 0 + 1 from rfl, heckeClass_ray_succ]
  rw [show 0 + (d) + 3 = d + 3 by ring, show 0 + d + 1 = d + 1 by ring]
  ring

/-- The root of a ray in the propagator, from the gap term. -/
theorem chebOp_root (d : ℕ) (g : Vertex G (DeadLabel G') → ℂ) (R : G) :
    chebOp B.q (d + 2) g (.ray R 0) =
      gapOp B.q (chebOp B.q (d + 1) g) R + g (.ray R (d + 2)) - (B.q : ℂ) * g (.ray R d) := by
  rw [chebOp_add_two, waveOp_ray_zero, show (1 : ℕ) = 0 + 1 from rfl, chebOp_ray_succ]
  rw [show 0 + d + 2 = d + 2 by ring, show 0 + d = d by ring]
  ring

include hG in
/-- **Off the rays the family is the propagator of the translated function**, at every degree `d ≥ 1`. -/
theorem heckeClass_off_ray (Q : G) (d : ℕ) (f : Vertex G (DeadLabel G') → ℂ) : OffRay B Q (d + 1) f := by
  have hmain : ∀ n : ℕ, OffRay B Q (n + 1) f ∧ OffRay B Q (n + 2) f := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · obtain ⟨h1, h2, h3, h4⟩ := off_ray_one B Q f
        exact ⟨h1, h2, h3, h4⟩
      · obtain ⟨h1, h2, h3, h4⟩ := off_ray_two B hG Q f
        exact ⟨h1, h2, h3, h4⟩
    | succ n ih =>
      obtain ⟨hn1, hn2⟩ := ih
      refine ⟨hn2, ?_⟩
      -- the root of the ray agrees at degree `n + 2`
      have hroot (R : G) : Sc Q (n + 2) f (.ray R 0) = chebOp B.q (n + 2) (shiftQ Q f) (.ray R 0) := by
        rcases n with _ | m
        · show heckeTwo B.q B.trace Q (0 : G') f (.ray R 0) = chebOp B.q 2 (shiftQ Q f) (.ray R 0)
          rw [chebOp_two_shift, heckeTwo_ray_zero, waveOp_ray_zero]
          have e1 : gapOp B.q (waveOp B.q (shiftQ Q f)) R =
              (B.q : ℂ) * (((B.q : ℂ) - 1) * shiftQ Q f .core) + (B.q : ℂ) * shiftQ Q f (.ray R 0) +
                (B.q : ℂ) * shiftQ Q f (.ray (-R) 0) := gapOp_waveOp B (shiftQ Q f) R
          have e2 : waveOp B.q (shiftQ Q f) (.ray R 1) =
              (B.q : ℂ) * shiftQ Q f (.ray R 0) + shiftQ Q f (.ray R 2) := rfl
          rw [e1, e2]
          show _ = _ - (B.q : ℂ) * (2 * f (.ray (R - Q) 0))
          show _ = (B.q : ℂ) * (((B.q : ℂ) - 1) * f .core) + (B.q : ℂ) * f (.ray (R - Q) 0) +
            (B.q : ℂ) * f (.ray (-R - Q) 0) + ((B.q : ℂ) * f (.ray (R - Q) 0) + f (.ray (R - Q) 2)) - _
          ring
        · rw [show m + 1 + 2 = m + 3 by ring, heckeClass_root, chebOp_root,
            show m + 3 = m + 1 + 2 by ring]
          have hg := OffRay.gap B hn1 R
          rw [show m + 1 + 1 = m + 2 by ring] at hg
          rw [hg]
          show _ = _ + f (.ray (R - Q) (m + 1 + 2)) - (B.q : ℂ) * f (.ray (R - Q) (m + 1))
          rfl
      obtain ⟨h1, h2, h3, h4⟩ := hn2
      have hA (v : Vertex G (DeadLabel G')) : Sc Q (n + 3) f v =
          waveOp B.q (Sc Q (n + 2) f) v - (B.q : ℂ) * Sc Q (n + 1) f v := rfl
      have hB (v : Vertex G (DeadLabel G')) : chebOp B.q (n + 3) (shiftQ Q f) v =
          waveOp B.q (chebOp B.q (n + 2) (shiftQ Q f)) v - (B.q : ℂ) * chebOp B.q (n + 1) (shiftQ Q f) v := rfl
      obtain ⟨g1, g2, g3, g4⟩ := hn1
      refine ⟨?_, ?_, ?_, ?_⟩
      · show Sc Q (n + 3) f _ = chebOp B.q (n + 3) _ _
        rw [hA, hB, g1, waveOp_core, waveOp_core]
        simp only [h2, h3]
      · intro x
        show Sc Q (n + 3) f _ = chebOp B.q (n + 3) _ _
        rw [hA, hB, g2, waveOp_dead, waveOp_dead, h1]
      · intro P
        show Sc Q (n + 3) f _ = chebOp B.q (n + 3) _ _
        rw [hA, hB, g3, waveOp_neck, waveOp_neck]
        unfold neckOp
        simp only [h1, hroot]
      · intro L
        show Sc Q (n + 3) f _ = chebOp B.q (n + 3) _ _
        rw [hA, hB, g4, waveOp_cap, waveOp_cap, hroot]
  exact (hmain d).1

/-! ### The algebra -/

include hG hG' in
/-- `heckeTwo` is linear. -/
theorem heckeTwo_sub_smul (Q : G) (w : G') (g h : Vertex G (DeadLabel G') → ℂ) (a : ℂ)
    (v : Vertex G (DeadLabel G')) :
    heckeTwo B.q B.trace Q w (fun u => g u - a * h u) v =
      heckeTwo B.q B.trace Q w g v - a * heckeTwo B.q B.trace Q w h v := by
  obtain ⟨R, rfl⟩ := two_nsmul_surjective hG Q
  simp only [heckeTwo_eq B hG hG']
  rw [heckeDeg_sub_smul, thetaOp_sub_smul]
  ring

include hG hG' in
theorem heckeClass_sub_smul (Q : G) (d : ℕ) (g h : Vertex G (DeadLabel G') → ℂ) (a : ℂ)
    (v : Vertex G (DeadLabel G')) :
    Sc Q (d + 1) (fun u => g u - a * h u) v = Sc Q (d + 1) g v - a * Sc Q (d + 1) h v := by
  have hmain : ∀ n : ℕ, (∀ v, Sc Q (n + 1) (fun u => g u - a * h u) v = Sc Q (n + 1) g v - a * Sc Q (n + 1) h v) ∧
      (∀ v, Sc Q (n + 2) (fun u => g u - a * h u) v = Sc Q (n + 2) g v - a * Sc Q (n + 2) h v) := by
    intro n
    induction n with
    | zero =>
      exact ⟨fun v => heckeOp_sub_smul B.q Q g h a v, fun v => heckeTwo_sub_smul B hG hG' Q 0 g h a v⟩
    | succ n ih =>
      refine ⟨ih.2, fun v => ?_⟩
      have e : Sc Q (n + 2) (fun u => g u - a * h u) =
          fun u => Sc Q (n + 2) g u - a * Sc Q (n + 2) h u := funext ih.2
      show Sc Q (n + 3) _ v = Sc Q (n + 3) g v - a * Sc Q (n + 3) h v
      rw [heckeClass_add_three, heckeClass_add_three, heckeClass_add_three, e, waveOp_sub_smul, ih.1 v]
      ring
  exact (hmain d).1 v

theorem heckeClass_add_three' (Q : G) (d : ℕ) (f : Vertex G (DeadLabel G') → ℂ) :
    Sc Q (d + 3) f = fun v => waveOp B.q (Sc Q (d + 2) f) v - (B.q : ℂ) * Sc Q (d + 1) f v := rfl

include hG hG' in
/-- **The operator of every class commutes with the wave operator.** -/
theorem heckeClass_comm_waveOp (Q : G) (d : ℕ) (f : Vertex G (DeadLabel G') → ℂ)
    (v : Vertex G (DeadLabel G')) :
    waveOp B.q (Sc Q (d + 1) f) v = Sc Q (d + 1) (waveOp B.q f) v := by
  have hmain : ∀ n : ℕ, (∀ v, waveOp B.q (Sc Q (n + 1) f) v = Sc Q (n + 1) (waveOp B.q f) v) ∧
      (∀ v, waveOp B.q (Sc Q (n + 2) f) v = Sc Q (n + 2) (waveOp B.q f) v) := by
    intro n
    induction n with
    | zero =>
      exact ⟨fun v => heckeOp_comm_waveOp B Q f v, fun v => B.heckeTwo_comm_waveOp hG hG' Q 0 f v⟩
    | succ n ih =>
      refine ⟨ih.2, fun v => ?_⟩
      show waveOp B.q (Sc Q (n + 3) f) v = Sc Q (n + 3) _ v
      rw [heckeClass_add_three', waveOp_sub_smul, heckeClass_add_three, ih.1 v]
      have e : waveOp B.q (Sc Q (n + 2) f) = Sc Q (n + 2) (waveOp B.q f) := funext ih.2
      rw [e]
  exact (hmain d).1 v

include hG hG' in
/-- A linear operator that commutes with `A`, `T_Q` and `T_{Q,0}` commutes with the whole family of class `Q`. -/
theorem commutes_heckeClass (X : (Vertex G (DeadLabel G') → ℂ) → Vertex G (DeadLabel G') → ℂ)
    (hlin : ∀ (g h : Vertex G (DeadLabel G') → ℂ) (a : ℂ) v,
      X (fun u => g u - a * h u) v = X g v - a * X h v)
    (hA : ∀ g v, X (waveOp B.q g) v = waveOp B.q (X g) v)
    (h1 : ∀ (R : G) g v, X (heckeOp B.q R g) v = heckeOp B.q R (X g) v)
    (h2 : ∀ (R : G) g v, X (heckeTwo B.q B.trace R (0 : G') g) v = heckeTwo B.q B.trace R (0 : G') (X g) v)
    (Q : G) (d : ℕ) (f : Vertex G (DeadLabel G') → ℂ) (v : Vertex G (DeadLabel G')) :
    X (Sc Q (d + 1) f) v = Sc Q (d + 1) (X f) v := by
  have hmain : ∀ n : ℕ, (∀ v, X (Sc Q (n + 1) f) v = Sc Q (n + 1) (X f) v) ∧
      (∀ v, X (Sc Q (n + 2) f) v = Sc Q (n + 2) (X f) v) := by
    intro n
    induction n with
    | zero => exact ⟨fun v => h1 Q f v, fun v => h2 Q f v⟩
    | succ n ih =>
      refine ⟨ih.2, fun v => ?_⟩
      show X (Sc Q (n + 3) f) v = Sc Q (n + 3) (X f) v
      rw [heckeClass_add_three', hlin, hA, heckeClass_add_three, ih.1 v]
      have e : X (Sc Q (n + 2) f) = Sc Q (n + 2) (X f) := funext ih.2
      rw [e]
  exact (hmain d).1 v

include hG hG' in
/-- `T_R` commutes with the family. -/
theorem heckeOp_comm_heckeClass (R Q : G) (d : ℕ) (f : Vertex G (DeadLabel G') → ℂ)
    (v : Vertex G (DeadLabel G')) :
    heckeOp B.q R (Sc Q (d + 1) f) v = Sc Q (d + 1) (heckeOp B.q R f) v :=
  commutes_heckeClass B hG hG' (heckeOp B.q R) (heckeOp_sub_smul B.q R)
    (fun g v => (heckeOp_comm_waveOp B R g v).symm) (fun S g v => heckeOp_comm B R S g v)
    (fun S g v => B.heckeTwo_comm_heckeOp hG hG' S R 0 g v) Q d f v

include hG hG' in
/-- `T_{R,0}` commutes with the family. -/
theorem heckeTwo_comm_heckeClass (R Q : G) (d : ℕ) (f : Vertex G (DeadLabel G') → ℂ)
    (v : Vertex G (DeadLabel G')) :
    heckeTwo B.q B.trace R (0 : G') (Sc Q (d + 1) f) v =
      Sc Q (d + 1) (heckeTwo B.q B.trace R (0 : G') f) v :=
  commutes_heckeClass B hG hG' (heckeTwo B.q B.trace R (0 : G')) (heckeTwo_sub_smul B hG hG' R 0)
    (fun g v => (B.heckeTwo_comm_waveOp hG hG' R 0 g v).symm)
    (fun S g v => (B.heckeTwo_comm_heckeOp hG hG' R S 0 g v).symm)
    (fun S g v => B.heckeTwo_comm hG hG' R S 0 0 g v) Q d f v

include hG hG' in
/-- **The operators of all classes and degrees commute.** -/
theorem heckeClass_comm (Q R : G) (d e : ℕ) (f : Vertex G (DeadLabel G') → ℂ)
    (v : Vertex G (DeadLabel G')) :
    Sc Q (d + 1) (Sc R (e + 1) f) v = Sc R (e + 1) (Sc Q (d + 1) f) v :=
  commutes_heckeClass B hG hG' (Sc Q (d + 1)) (heckeClass_sub_smul B hG hG' Q d)
    (fun g v => (heckeClass_comm_waveOp B hG hG' Q d g v).symm)
    (fun S g v => (heckeOp_comm_heckeClass B hG hG' S Q d g v).symm)
    (fun S g v => (heckeTwo_comm_heckeClass B hG hG' S Q d g v).symm) R e f v

/-- **Hecke of degree `d` and class `Q` in the cusps.** -/
theorem heckeClass_ray (Q : G) (d : ℕ) (f : Vertex G (DeadLabel G') → ℂ) (P : G) (j : ℕ) :
    Sc Q (d + 1) f (.ray P (d + 1 + j)) =
      (B.q : ℂ) ^ (d + 1) * f (.ray (P + Q) j) + f (.ray (P - Q) (2 * (d + 1) + j)) := by
  have hmain : ∀ n : ℕ, (∀ j, Sc Q (n + 1) f (.ray P (n + 1 + j)) =
        (B.q : ℂ) ^ (n + 1) * f (.ray (P + Q) j) + f (.ray (P - Q) (2 * (n + 1) + j))) ∧
      (∀ j, Sc Q (n + 2) f (.ray P (n + 2 + j)) =
        (B.q : ℂ) ^ (n + 2) * f (.ray (P + Q) j) + f (.ray (P - Q) (2 * (n + 2) + j))) := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun j => ?_, fun j => ?_⟩
      · show heckeOp B.q Q f _ = _
        rw [show 0 + 1 + j = j + 1 by ring, heckeOp_ray_succ, show 2 * (0 + 1) + j = j + 2 by ring,
          zero_add, pow_one]
      · show heckeTwo B.q B.trace Q (0 : G') f _ = _
        rw [show 0 + 2 + j = j + 2 by ring, heckeTwo_ray_add_two, show 2 * (0 + 2) + j = j + 4 by ring]
    | succ n ih =>
      refine ⟨ih.2, fun j => ?_⟩
      show Sc Q (n + 3) f _ = _
      rw [heckeClass_add_three, show n + 1 + 2 + j = (n + 2 + j) + 1 by ring, waveOp_ray_succ, ih.2 j,
        show n + 2 + j + 2 = n + 2 + (j + 2) by ring, ih.2 (j + 2),
        show n + 2 + j + 1 = n + 1 + (j + 2) by ring, ih.1 (j + 2),
        show 2 * (n + 2) + (j + 2) = 2 * (n + 1 + 2) + j by ring,
        show 2 * (n + 2) + j = 2 * (n + 1) + (j + 2) by ring]
      ring
  exact (hmain d).1 j

/-- **The operator of degree `d` has `q^d + 1` edges.** -/
theorem heckeClass_one (Q : G) (d : ℕ) (v : Vertex G (DeadLabel G')) :
    Sc Q (d + 1) (fun _ => (1 : ℂ)) v = (B.q : ℂ) ^ (d + 1) + 1 := by
  have hmain : ∀ n : ℕ, (∀ v : Vertex G (DeadLabel G'), Sc Q (n + 1) (fun _ => (1 : ℂ)) v = (B.q : ℂ) ^ (n + 1) + 1) ∧
      (∀ v : Vertex G (DeadLabel G'), Sc Q (n + 2) (fun _ => (1 : ℂ)) v = (B.q : ℂ) ^ (n + 2) + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun v => ?_, fun v => ?_⟩
      · show heckeOp B.q Q _ v = _
        rw [B.heckeOp_one]
        ring
      · exact B.heckeTwo_one Q 0 v
    | succ n ih =>
      refine ⟨ih.2, fun v => ?_⟩
      show Sc Q (n + 3) _ v = _
      rw [heckeClass_add_three]
      have e : Sc Q (n + 2) (fun _ : Vertex G (DeadLabel G') => (1 : ℂ)) = fun _ => (((B.q : ℂ) ^ (n + 2) + 1)) * 1 := by
        funext u
        rw [ih.2 u, mul_one]
      rw [e, waveOp_smul, B.waveOp_one, ih.1 v]
      ring
  exact (hmain d).1 v

include hG hG' in
/-- **The family acts on a resonance by the dispersion relation.** -/
theorem heckeClass_resonance (Q : G) (d : ℕ) {X Y : ℂ} (hXY : X * Y = B.q) (hne : X ≠ Y)
    (hlam : X + Y ≠ 0) {f : Vertex G (DeadLabel G') → ℂ} {c : G → ℂ} (hf : IsOutgoing B.q X Y f c)
    (v : Vertex G (DeadLabel G')) :
    Sc Q (d + 1) f v = (X ^ (d + 1) + Y ^ (d + 1)) * f v := by
  refine hecke_rigidity B (Sc Q (d + 1)) ?_ (heckeClass_comm_waveOp B hG hG' Q d) (d + 1)
    (fun P => P + Q) (fun P => P - Q) (heckeClass_ray B Q d) hXY hne hlam hf v
  intro a g w
  have h := heckeClass_sub_smul B hG hG' Q d (fun _ => (0 : ℂ)) g (-a) w
  have hz : Sc Q (d + 1) (fun _ => (0 : ℂ)) w = 0 := by
    have h0 := heckeClass_sub_smul B hG hG' Q d (fun _ => (0 : ℂ)) (fun _ => (0 : ℂ)) 1 w
    simp only [one_mul, sub_self] at h0
    simpa using h0
  simp only [zero_sub, neg_mul, neg_neg] at h
  rw [h, hz]
  ring

/-! ### Positivity -/

section Positivity

variable (hq : 7 ≤ B.q) {f : Vertex G (DeadLabel G') → ℂ} (hf : ∀ v, 0 ≤ f v)

include hf in
theorem shiftQ_nonneg (Q : G) (v : Vertex G (DeadLabel G')) : 0 ≤ shiftQ Q f v := hf _

include hG hG' hq hf in
/-- The echo of the family is nonnegative. -/
theorem classEcho_nonneg (Q R : G) (k d : ℕ) : 0 ≤ classEcho B Q f R (d + 1) k := by
  have hq0 : (0 : ℂ) ≤ (B.q : ℂ) := by simp
  have h7 := qr_ge B hq
  have hq1 : (0 : ℂ) ≤ (B.q : ℂ) - 1 := by
    simpa using ofReal_nonneg' (show (0 : ℝ) ≤ (B.q : ℝ) - 1 by linarith)
  have hg := shiftQ_nonneg hf Q
  induction k generalizing d with
  | zero =>
    rcases d with _ | _ | d
    · have e : classEcho B Q f R (0 + 1) 0 = gapOp B.q f (R + Q) := by
        unfold classEcho
        show heckeOp B.q Q f (.ray R 0) - _ = _
        rw [heckeOp_ray_zero]
        simp
      rw [e]
      unfold gapOp
      split_ifs
      · exact add_nonneg (mul_nonneg hq1 (hf _)) (hf _)
      · exact mul_nonneg hq0 (hf _)
    · have e : classEcho B Q f R (0 + 1 + 1) 0 =
          (B.q : ℂ) * ((B.q : ℂ) - 1) * f .core + (B.q : ℂ) * f (.ray (-R - Q) 0) := by
        unfold classEcho
        show heckeTwo B.q B.trace Q (0 : G') f (.ray R 0) - _ = _
        rw [heckeTwo_ray_zero]
        simp
      rw [e]
      exact add_nonneg (mul_nonneg (mul_nonneg hq0 hq1) (hf _)) (mul_nonneg hq0 (hf _))
    · have hgap := OffRay.gap B (heckeClass_off_ray B hG Q (d + 1) f) R
      have hform := gap_formula B (shiftQ Q f) (d + 1) R
      have e : classEcho B Q f R (d + 1 + 1 + 1) 0 =
          (B.q : ℂ) * f (.ray (-R - Q) (d + 1)) +
            (B.q : ℂ) * ((B.q : ℂ) - 1) * coreW B.q (shiftQ Q f) (d + 1) := by
        unfold classEcho
        rw [show d + 1 + 1 + 1 = d + 3 by ring, heckeClass_root]
        rw [show d + 1 + 1 = d + 2 by ring] at hgap hform
        rw [hgap, hform]
        rw [show 0 + (d + 3) = d + 3 by ring]
        show (B.q : ℂ) * (f (.ray (R - Q) (d + 1)) + f (.ray (-R - Q) (d + 1)) +
          ((B.q : ℂ) - 1) * coreW B.q (shiftQ Q f) (d + 1)) + _ - _ - _ = _
        ring
      rw [e]
      exact add_nonneg (mul_nonneg hq0 (hf _))
        (mul_nonneg (mul_nonneg hq0 hq1) (coreW_nonneg B hG hG' hq hg _))
  | succ k ih =>
    rcases d with _ | d
    · have e : classEcho B Q f R (0 + 1) (k + 1) = (B.q : ℂ) * f (.ray (R + Q) k) := by
        unfold classEcho
        show heckeOp B.q Q f (.ray R (k + 1)) - _ = _
        rw [heckeOp_ray_succ, show k + 1 + (0 + 1) = k + 2 by ring]
        ring
      rw [e]
      exact mul_nonneg hq0 (hf _)
    · rw [show d + 1 + 1 = d + 2 by ring, classEcho_succ]
      exact mul_nonneg hq0 (ih d)

include hG hG' hq hf in
/-- **The family is positive at every degree `d ≥ 3` and every class.** -/
theorem heckeClass_nonneg (Q : G) {d : ℕ} (hd : 3 ≤ d) (v : Vertex G (DeadLabel G')) :
    0 ≤ Sc Q d f v := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hoff := heckeClass_off_ray B hG Q e f
  have hg := shiftQ_nonneg hf Q
  have hprop := chebOp_nonneg B hG hG' hq hg hd
  obtain ⟨h1, h2, h3, h4⟩ := hoff
  rcases v with _ | x | y | L | ⟨P, k⟩
  · rw [h1]
    exact hprop _
  · rw [h2]
    exact hprop _
  · induction y using Quotient.inductionOn with
    | h P =>
      change 0 ≤ Sc Q (e + 1) f (.neck (Branch.mk P))
      rw [h3]
      exact hprop _
  · rw [h4]
    exact hprop _
  · have e1 : Sc Q (e + 1) f (.ray P k) = f (.ray (P - Q) (k + (e + 1))) + classEcho B Q f P (e + 1) k := by
      unfold classEcho
      ring
    rw [e1]
    exact add_nonneg (hf _) (classEcho_nonneg B hG hG' hq hf Q P k e)

/-- The translation of the cusps does not move the shadow. -/
theorem thetaOp_shiftQ (q : ℕ) (Q : G) (w : G') (f : Vertex G (DeadLabel G') → ℂ)
    (v : Vertex G (DeadLabel G')) : thetaOp q w (shiftQ Q f) v = thetaOp q w f v := by
  have ht (Q' : G') : thetaTerm q (shiftQ Q f) Q' = thetaTerm q f Q' := by
    unfold thetaTerm deadTerm deadTermB
    split_ifs <;> rfl
  rcases v with _ | d | x | L | ⟨P, k⟩
  · rfl
  · rw [thetaOp_dead', thetaOp_dead']
    obtain ⟨x, hx⟩ := d
    induction x using Quotient.inductionOn with
    | h R =>
      change thetaDiff q _ w R = thetaDiff q f w R
      unfold thetaDiff
      rw [ht, ht, ht]
  · induction x using Quotient.inductionOn with
    | h P =>
      change thetaNeck q _ w P = thetaNeck q f w P
      unfold thetaNeck
      rw [ht, ht]
  · rw [thetaOp_cap, thetaOp_cap, ht, ht]
  · rfl

include hG hG' hq hf in
/-- **The correction of the cusp forms keeps the positivity, at every class.** -/
theorem heckeClass_add_theta_nonneg (Q : G) (n : ℕ) {w : G'} (hw : w ≠ 0) (v : Vertex G (DeadLabel G')) :
    0 ≤ Sc Q (2 * (n + 1) + 2) f v + (-(B.q : ℂ)) ^ (n + 2) * thetaOp B.q w f v := by
  have hoff := heckeClass_off_ray B hG Q (2 * (n + 1) + 1) f
  have hg := shiftQ_nonneg hf Q
  have hprop := chebOp_add_theta_nonneg B hG hG' hq hg n hw
  obtain ⟨h1, h2, h3, h4⟩ := hoff
  rw [← thetaOp_shiftQ B.q Q w f v]
  rcases v with _ | x | y | L | ⟨P, k⟩
  · have := hprop .core
    rwa [← h1] at this
  · have := hprop (.dead x)
    rwa [← h2] at this
  · induction y using Quotient.inductionOn with
    | h P =>
      have := hprop (.neck (Branch.mk P))
      rw [← h3] at this
      exact this
  · have := hprop (.cap L)
    rwa [← h4] at this
  · rw [thetaOp_ray, mul_zero, add_zero]
    exact heckeClass_nonneg B hG hG' hq hf Q (by omega) _

end Positivity

/-- **Every class at every degree is carried by the fakes.** For `q ≥ 8`, the black hole with `N = 3`, `N' = 2q - 1` carries a positive commuting family at all classes and all degrees, with the shape of Hecke
in the cusps, and it has a resonance slower than universal. -/
theorem universal_damping_not_forced_at_every_class {q : ℕ} (hq : 8 ≤ q) :
    let B := oddPairChannels q 3 (2 * (q - 1) + 1) (by decide) ⟨q - 1, rfl⟩ (by omega) (by omega)
    (∀ (Q R : ZMod 3) (d e : ℕ) (f : Vertex (ZMod 3) (DeadLabel (ZMod (2 * (q - 1) + 1))) → ℂ) (v),
        heckeClass B.q B.trace Q (d + 1) (heckeClass B.q B.trace R (e + 1) f) v =
          heckeClass B.q B.trace R (e + 1) (heckeClass B.q B.trace Q (d + 1) f) v) ∧
      (∀ (Q : ZMod 3) (d : ℕ) (f : Vertex (ZMod 3) (DeadLabel (ZMod (2 * (q - 1) + 1))) → ℂ) (v),
        waveOp B.q (heckeClass B.q B.trace Q (d + 1) f) v =
          heckeClass B.q B.trace Q (d + 1) (waveOp B.q f) v) ∧
      (∀ (Q : ZMod 3) (d : ℕ), 3 ≤ d →
        ∀ f : Vertex (ZMod 3) (DeadLabel (ZMod (2 * (q - 1) + 1))) → ℂ, (∀ v, 0 ≤ f v) → ∀ v,
          0 ≤ heckeClass B.q B.trace Q d f v) ∧
      ∃ (X Y : ℂ) (f : Vertex (ZMod 3) (DeadLabel (ZMod (2 * (q - 1) + 1))) → ℂ) (c : ZMod 3 → ℂ),
        f ≠ 0 ∧ IsOutgoing B.q X Y f c ∧ (B.q : ℝ) < Complex.normSq (X ^ 2) := by
  intro B
  have hG : ∀ P : ZMod 3, 2 • P = 0 → P = 0 := two_nsmul_eq_zero_zmod (by decide)
  have hG' : ∀ Q : ZMod (2 * (q - 1) + 1), 2 • Q = 0 → Q = 0 :=
    two_nsmul_eq_zero_zmod ⟨q - 1, rfl⟩
  have h7 : 7 ≤ B.q := by
    show 7 ≤ q
    omega
  refine ⟨fun Q R d e f v => heckeClass_comm B hG hG' Q R d e f v,
    fun Q d f v => heckeClass_comm_waveOp B hG hG' Q d f v,
    fun Q d hd f hf v => heckeClass_nonneg B hG hG' h7 hf Q hd v, ?_⟩
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
