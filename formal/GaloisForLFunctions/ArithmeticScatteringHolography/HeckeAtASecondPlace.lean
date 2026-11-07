import GaloisForLFunctions.ArithmeticScatteringHolography.TheScatteringMatrix
import Mathlib.Algebra.Group.AddChar

/-!
# Hecke at a second place

On the black hole of an elliptic curve, translation by a rational point acts on the bundles, and it moves
the place `∞` to another rational place. So the Hecke operator at that place is the wave operator
conjugated by a translation of the cusps. On rays:

  `(T_Q f)(P, k+1) = q f(P + Q, k) + f(P - Q, k + 2)`.

The second place acts on the cusp group, and at `Q = 0` it is the wave operator itself. This family makes
sense on every black hole `(q, G, D)`, true or fake, and it has all the properties one asks of Hecke:

* `T_Q` commute with each other and with `A` (`heckeOp_comm`, `heckeOp_comm_waveOp`);
* nonnegative coefficients, `T_Q 1 = (q+1) 1`, and it is a conjugate of `A` by a measure-preserving
  bijection, so it is symmetric (`heckeOp_eq_conj`, `truncSum_heckeGreen`);
* it sends waves to waves (`IsWave.hecke`), and gives one conserved energy per place (`hecke_energy_balance`).

**It imposes no constraint on the resonances.** On the radial sector of the core, `T_Q` *is* `A`
(`heckeOp_balanced`). Every resonance lies there, so the second place acts on it by the same `λ`, wherever it
is (`IsOutgoing.hecke_eigen`). The other sectors are the zero-mean amplitudes on the cusps: they have no
resonance at all (`zeroMeanField_eigen`), and on a character `T_Q` has the eigenvalue
`χ(-Q) X + χ(Q) Y` (`chi_hecke_eigen`). So Hecke at a second place is an exact symmetry that decides
nothing about the position of a resonance.
-/

open Finset ComplexConjugate

noncomputable section

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.ArithmeticScatteringHolography

variable {G D : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] [Fintype D]

/-- The Hecke operator at the neck of `P`. -/
def neckHecke (q : ℕ) (Q : G) (f : Vertex G D → ℂ) (P : G) : ℂ :=
  if 2 • P = 0 then (q : ℂ) * f .core + f (.ray (P - Q) 0)
  else ((q : ℂ) - 1) * f .core + f (.ray (P - Q) 0) + f (.ray (-P - Q) 0)

theorem neckHecke_neg (q : ℕ) (Q : G) (f : Vertex G D → ℂ) (P : G) :
    neckHecke q Q f (-P) = neckHecke q Q f P := by
  unfold neckHecke
  by_cases h : 2 • P = 0
  · rw [if_pos (by rwa [two_nsmul_neg_eq_zero_iff]), if_pos h, eq_neg_of_two_nsmul h]
  · rw [if_neg h, if_neg (by rwa [two_nsmul_neg_eq_zero_iff]), neg_neg]
    ring

/-- **The Hecke operator** at the second place of class `Q`. -/
def heckeOp (q : ℕ) (Q : G) (f : Vertex G D → ℂ) : Vertex G D → ℂ
  | .core => ∑ d, f (.dead d) + ∑ P, branchWeight P * f (.neck (Branch.mk P))
  | .dead _ => ((q : ℂ) + 1) * f .core
  | .neck x =>
      Quotient.liftOn x (neckHecke q Q f) (fun P R h => by
        rcases h with rfl | rfl
        · rfl
        · exact (neckHecke_neg q Q f P).symm)
  | .cap L => ((q : ℂ) + 1) * f (.ray (L.1 - Q) 0)
  | .ray P 0 => gapOp q f (P + Q) + f (.ray (P - Q) 1)
  | .ray P (k + 1) => (q : ℂ) * f (.ray (P + Q) k) + f (.ray (P - Q) (k + 2))

@[simp] theorem heckeOp_core (q : ℕ) (Q : G) (f : Vertex G D → ℂ) :
    heckeOp q Q f .core = ∑ d, f (.dead d) + ∑ P, branchWeight P * f (.neck (Branch.mk P)) := rfl
@[simp] theorem heckeOp_dead (q : ℕ) (Q : G) (f : Vertex G D → ℂ) (d : D) :
    heckeOp q Q f (.dead d) = ((q : ℂ) + 1) * f .core := rfl
@[simp] theorem heckeOp_neck (q : ℕ) (Q : G) (f : Vertex G D → ℂ) (P : G) :
    heckeOp q Q f (.neck (Branch.mk P)) = neckHecke q Q f P := rfl
@[simp] theorem heckeOp_cap (q : ℕ) (Q : G) (f : Vertex G D → ℂ) (L : TwoTorsion G) :
    heckeOp q Q f (.cap L) = ((q : ℂ) + 1) * f (.ray (L.1 - Q) 0) := rfl
@[simp] theorem heckeOp_ray_zero (q : ℕ) (Q : G) (f : Vertex G D → ℂ) (P : G) :
    heckeOp q Q f (.ray P 0) = gapOp q f (P + Q) + f (.ray (P - Q) 1) := rfl
@[simp] theorem heckeOp_ray_succ (q : ℕ) (Q : G) (f : Vertex G D → ℂ) (P : G) (k : ℕ) :
    heckeOp q Q f (.ray P (k + 1)) = (q : ℂ) * f (.ray (P + Q) k) + f (.ray (P - Q) (k + 2)) := rfl

/-- **At the trivial class the Hecke operator is the wave operator.** -/
theorem heckeOp_zero (q : ℕ) (f : Vertex G D → ℂ) (v : Vertex G D) :
    heckeOp q (0 : G) f v = waveOp q f v := by
  rcases v with _ | d | x | L | ⟨P, _ | k⟩
  · rfl
  · rfl
  · induction x using Quotient.inductionOn with
    | h P =>
      change neckHecke q 0 f P = neckOp q f P
      simp [neckHecke, neckOp]
  · simp
  · simp
  · simp

theorem gapOp_neg (q : ℕ) (f : Vertex G D → ℂ) (R : G) : gapOp q f (-R) = gapOp q f R := by
  unfold gapOp
  by_cases h : 2 • R = 0
  · have e := eq_neg_of_two_nsmul h
    have h' : 2 • (-R) = 0 := (two_nsmul_neg_eq_zero_iff R).mpr h
    rw [dif_pos h', dif_pos h]
    congr 3
    all_goals simp only [e]
  · rw [dif_neg (by rwa [two_nsmul_neg_eq_zero_iff]), dif_neg h, Branch.mk_neg]

/-- The gap term of `T_Q f`, in one closed form for both kinds of point. -/
theorem gapOp_heckeOp (B : Channels G D) (Q : G) (f : Vertex G D → ℂ) (R : G) :
    gapOp B.q (heckeOp B.q Q f) R =
      (B.q : ℂ) * (((B.q : ℂ) - 1) * f .core) + (B.q : ℂ) * f (.ray (R - Q) 0) +
        (B.q : ℂ) * f (.ray (-R - Q) 0) := by
  unfold gapOp
  by_cases h : 2 • R = 0
  · rw [dif_pos h, heckeOp_neck, heckeOp_cap]
    unfold neckHecke
    rw [if_pos h, eq_neg_of_two_nsmul h]
    ring
  · rw [dif_neg h, heckeOp_neck]
    unfold neckHecke
    rw [if_neg h]
    ring

/-- The neck sum of `T_Q f` does not depend on `Q`: the cusps are permuted. -/
theorem sum_neckHecke (q : ℕ) (Q : G) (f : Vertex G D → ℂ) :
    ∑ P, branchWeight P * neckHecke q Q f P =
      (∑ P : G, branchWeight P * (if 2 • P = 0 then (q : ℂ) else (q : ℂ) - 1)) * f .core +
        ∑ P, f (.ray P 0) := by
  have hterm (P : G) : branchWeight P * neckHecke q Q f P =
      branchWeight P * (if 2 • P = 0 then (q : ℂ) else (q : ℂ) - 1) * f .core +
        ((1 / 2 : ℂ) * f (.ray (P - Q) 0) + (1 / 2 : ℂ) * f (.ray (-P - Q) 0)) := by
    unfold neckHecke branchWeight
    by_cases h : 2 • P = 0
    · simp only [if_pos h, eq_neg_of_two_nsmul h]
      ring
    · simp only [if_neg h]
      ring
  simp only [hterm, Finset.sum_add_distrib, ← Finset.sum_mul]
  have e1 : ∑ P : G, f (.ray (P - Q) 0) = ∑ P : G, f (.ray P 0) :=
    Equiv.sum_comp (Equiv.subRight Q) (fun P => f (.ray P 0))
  have e2 : ∑ P : G, f (.ray (-P - Q) 0) = ∑ P : G, f (.ray P 0) :=
    Equiv.sum_comp ((Equiv.neg G).trans (Equiv.subRight Q)) (fun P => f (.ray P 0))
  simp only [← Finset.mul_sum, e1, e2]
  ring

/-- **The Hecke operators commute**, for every abelian group of cusps and every number of dead ends. -/
theorem heckeOp_comm (B : Channels G D) (Q Q' : G) (f : Vertex G D → ℂ) (v : Vertex G D) :
    heckeOp B.q Q (heckeOp B.q Q' f) v = heckeOp B.q Q' (heckeOp B.q Q f) v := by
  rcases v with _ | d | x | L | ⟨P, _ | _ | k⟩
  · rw [heckeOp_core, heckeOp_core]
    simp only [heckeOp_dead, heckeOp_neck, sum_neckHecke]
  · simp only [heckeOp_dead, heckeOp_core]
  · induction x using Quotient.inductionOn with
    | h P =>
      change neckHecke B.q Q (heckeOp B.q Q' f) P = neckHecke B.q Q' (heckeOp B.q Q f) P
      unfold neckHecke
      by_cases h : 2 • P = 0
      · simp only [if_pos h, heckeOp_core, heckeOp_ray_zero]
        have hP := eq_neg_of_two_nsmul h
        have g1 : gapOp B.q f (P - Q + Q') = gapOp B.q f (P - Q' + Q) := by
          rw [← gapOp_neg]
          congr 1
          nth_rewrite 1 [neg_add, neg_sub, ← hP]
          abel
        have e1 : P - Q - Q' = P - Q' - Q := by abel
        rw [g1, e1]
      · simp only [if_neg h, heckeOp_core, heckeOp_ray_zero]
        have g1 : gapOp B.q f (P - Q + Q') = gapOp B.q f (-P - Q' + Q) := by
          rw [← gapOp_neg]
          congr 1
          abel
        have g2 : gapOp B.q f (-P - Q + Q') = gapOp B.q f (P - Q' + Q) := by
          rw [← gapOp_neg]
          congr 1
          abel
        have e1 : P - Q - Q' = P - Q' - Q := by abel
        have e2 : -P - Q - Q' = -P - Q' - Q := by abel
        rw [g1, g2, e1, e2]
        ring
  · simp only [heckeOp_cap, heckeOp_ray_zero]
    have hL := eq_neg_of_two_nsmul L.2
    have g1 : gapOp B.q f (L.1 - Q + Q') = gapOp B.q f (L.1 - Q' + Q) := by
      rw [← gapOp_neg]
      congr 1
      nth_rewrite 1 [neg_add, neg_sub, ← hL]
      abel
    have e1 : L.1 - Q - Q' = L.1 - Q' - Q := by abel
    rw [g1, e1]
  · rw [heckeOp_ray_zero, heckeOp_ray_zero, gapOp_heckeOp, gapOp_heckeOp]
    simp only [zero_add, heckeOp_ray_succ]
    have e1 : P + Q - Q' = P - Q' + Q := by abel
    have e2 : -(P + Q) - Q' = -(P + Q') - Q := by abel
    have e3 : P - Q + Q' = P + Q' - Q := by abel
    have e4 : P - Q - Q' = P - Q' - Q := by abel
    rw [e1, e2, e3, e4]
    ring
  · simp only [zero_add, heckeOp_ray_succ, heckeOp_ray_zero]
    have g1 : P + Q + Q' = P + Q' + Q := by abel
    have e1 : P + Q - Q' = P - Q' + Q := by abel
    have e3 : P - Q + Q' = P + Q' - Q := by abel
    have e4 : P - Q - Q' = P - Q' - Q := by abel
    rw [g1, e1, e3, e4]
    ring
  · simp only [heckeOp_ray_succ]
    have g1 : P + Q + Q' = P + Q' + Q := by abel
    have e1 : P + Q - Q' = P - Q' + Q := by abel
    have e3 : P - Q + Q' = P + Q' - Q := by abel
    have e4 : P - Q - Q' = P - Q' - Q := by abel
    rw [g1, e1, e3, e4]
    ring

/-- **Hecke commutes with the wave operator.** -/
theorem heckeOp_comm_waveOp (B : Channels G D) (Q : G) (f : Vertex G D → ℂ) (v : Vertex G D) :
    waveOp B.q (heckeOp B.q Q f) v = heckeOp B.q Q (waveOp B.q f) v := by
  have h1 := heckeOp_comm B (0 : G) Q f v
  rw [heckeOp_zero] at h1
  rw [h1]
  have hfun : heckeOp B.q (0 : G) f = waveOp B.q f := funext (heckeOp_zero B.q f)
  rw [hfun]

/-! ### Linearity, waves, energies -/

theorem heckeOp_add (q : ℕ) (Q : G) (f g : Vertex G D → ℂ) (v : Vertex G D) :
    heckeOp q Q (fun w => f w + g w) v = heckeOp q Q f v + heckeOp q Q g v := by
  rcases v with _ | d | x | L | ⟨P, _ | k⟩
  · simp only [heckeOp_core, mul_add, Finset.sum_add_distrib]
    ring
  · simp only [heckeOp_dead]
    ring
  · induction x using Quotient.inductionOn with
    | h P =>
      change heckeOp q Q _ (.neck (Branch.mk P)) =
        heckeOp q Q f (.neck (Branch.mk P)) + heckeOp q Q g (.neck (Branch.mk P))
      rw [heckeOp_neck, heckeOp_neck, heckeOp_neck]
      unfold neckHecke
      split_ifs <;> ring
  · simp only [heckeOp_cap]
    ring
  · simp only [heckeOp_ray_zero]
    unfold gapOp
    split_ifs <;> ring
  · simp only [heckeOp_ray_succ]
    ring

theorem heckeOp_smul (q : ℕ) (Q : G) (a : ℂ) (f : Vertex G D → ℂ) (v : Vertex G D) :
    heckeOp q Q (fun w => a * f w) v = a * heckeOp q Q f v := by
  rcases v with _ | d | x | L | ⟨P, _ | k⟩
  · simp only [heckeOp_core, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun P _ => ?_
    ring
  · simp only [heckeOp_dead]
    ring
  · induction x using Quotient.inductionOn with
    | h P =>
      change heckeOp q Q _ (.neck (Branch.mk P)) = a * heckeOp q Q f (.neck (Branch.mk P))
      rw [heckeOp_neck, heckeOp_neck]
      unfold neckHecke
      split_ifs <;> ring
  · simp only [heckeOp_cap]
    ring
  · simp only [heckeOp_ray_zero]
    unfold gapOp
    split_ifs <;> ring
  · simp only [heckeOp_ray_succ]
    ring

/-- **Hecke sends waves to waves.** -/
theorem IsWave.hecke (B : Channels G D) {u : ℤ → Vertex G D → ℂ} (hu : IsWave B.q u) (Q : G) :
    IsWave B.q fun τ => heckeOp B.q Q (u τ) := by
  intro τ v
  rw [heckeOp_comm_waveOp, ← heckeOp_smul, ← heckeOp_add]
  have : (fun w => u (τ + 1) w + (B.q : ℂ) * u (τ + (-1)) w) = waveOp B.q (u τ) :=
    funext fun w => hu τ w
  rw [this]

/-- **One conserved energy per place.** A wave paired with its image under `T_Q` has an energy that changes
only by the flux. -/
theorem hecke_energy_balance (B : Channels G D) {u : ℤ → Vertex G D → ℂ} (hu : IsWave B.q u) (Q : G)
    (K : ℕ) (τ : ℤ) :
    energy B.q (K + 1) (fun τ => heckeOp B.q Q (u τ)) u τ -
        energy B.q (K + 1) (fun τ => heckeOp B.q Q (u τ)) u (τ + (-1)) =
      -((B.q : ℂ) ^ (-(τ + 1)) *
        ∑ P : G, rayFlux B.q (heckeOp B.q Q (u (τ + 1))) (fun v => conj (u τ v)) P K) :=
  energy_balance B (hu.hecke B Q) hu K τ

/-! ### Translations -/

/-- The translation of the cusps by `Q`: depth `k` is moved by `(k+1) Q`, and gap zero is fixed. -/
def transl (Q : G) : Vertex G D → Vertex G D
  | .core => .core
  | .dead d => .dead d
  | .neck x => .neck x
  | .cap L => .cap L
  | .ray P k => .ray (P + (k + 1) • Q) k

theorem transl_transl (Q : G) (v : Vertex G D) : transl (-Q) (transl Q v) = v := by
  rcases v with _ | d | x | L | ⟨P, k⟩ <;> simp [transl]

theorem transl_neg_transl (Q : G) (v : Vertex G D) : transl Q (transl (-Q) v) = v := by
  rcases v with _ | d | x | L | ⟨P, k⟩ <;> simp [transl]

/-- **Hecke is the wave operator conjugated by the translation.** -/
theorem heckeOp_eq_conj (q : ℕ) (Q : G) (f : Vertex G D → ℂ) (v : Vertex G D) :
    heckeOp q Q f v = waveOp q (fun w => f (transl (-Q) w)) (transl Q v) := by
  have hg (R : G) : gapOp q (fun w => f (transl (-Q) w)) R = gapOp q f R := by
    unfold gapOp
    split_ifs <;> simp [transl]
  rcases v with _ | d | x | L | ⟨P, _ | k⟩
  · simp [transl]
  · simp [transl]
  · induction x using Quotient.inductionOn with
    | h P =>
      change neckHecke q Q f P = waveOp q _ (.neck (Branch.mk P))
      rw [waveOp_neck]
      unfold neckHecke neckOp
      simp [transl, sub_eq_add_neg]
  · simp [transl, sub_eq_add_neg]
  · have e0 : transl Q (.ray P 0 : Vertex G D) = .ray (P + Q) 0 := by simp [transl]
    have e1 : transl (-Q) (.ray (P + Q) 1 : Vertex G D) = .ray (P - Q) 1 := by
      simp only [transl]
      congr 1
      rw [smul_neg, show 1 + 1 = 2 from rfl, two_nsmul]
      abel
    rw [e0, heckeOp_ray_zero, waveOp_ray_zero, hg, e1]
  · have e0 : transl Q (.ray P (k + 1) : Vertex G D) = .ray (P + (k + 1 + 1) • Q) (k + 1) := rfl
    have e1 : transl (-Q) (.ray (P + (k + 1 + 1) • Q) k : Vertex G D) = .ray (P + Q) k := by
      simp only [transl]
      congr 1
      rw [smul_neg, add_smul (k + 1) 1 Q, one_smul]
      abel
    have e2 : transl (-Q) (.ray (P + (k + 1 + 1) • Q) (k + 2) : Vertex G D) = .ray (P - Q) (k + 2) := by
      simp only [transl]
      congr 1
      rw [smul_neg, show k + 2 + 1 = (k + 1 + 1) + 1 by ring, add_smul (k + 1 + 1) 1 Q, one_smul]
      abel
    rw [e0, heckeOp_ray_succ, waveOp_ray_succ, e1, e2]

/-- Translation preserves the measure. -/
theorem mass_transl (q : ℕ) (Q : G) (v : Vertex G D) : mass q (transl Q v) = mass q v := by
  rcases v with _ | d | x | L | ⟨P, k⟩ <;> rfl

/-- Translation preserves the truncated sums: it permutes each depth. -/
theorem truncSum_transl (K : ℕ) (Q : G) (F : Vertex G D → ℂ) :
    truncSum K (fun v => F (transl Q v)) = truncSum K F := by
  unfold truncSum
  simp only [transl]
  congr 1
  rw [Finset.sum_comm, Finset.sum_comm (s := (univ : Finset G))]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact Equiv.sum_comp (Equiv.addRight ((k + 1) • Q)) (fun P => F (.ray P k))

/-- **Hecke is symmetric.** Green's identity for `T_Q` has only the flux on the rays, of the translated
functions. -/
theorem truncSum_heckeGreen (B : Channels G D) (Q : G) (f g : Vertex G D → ℂ) (K : ℕ) :
    truncSum (K + 1) (fun v => mass B.q v * (heckeOp B.q Q f v * g v - f v * heckeOp B.q Q g v)) =
      ∑ P : G, rayFlux B.q (fun w => f (transl (-Q) w)) (fun w => g (transl (-Q) w)) P K := by
  rw [← truncSum_greenDensity B]
  rw [← truncSum_transl (K + 1) Q (greenDensity B.q _ _)]
  refine truncSum_congr _ fun v => ?_
  unfold greenDensity
  rw [mass_transl, ← heckeOp_eq_conj, ← heckeOp_eq_conj]
  beta_reduce
  rw [transl_transl]

/-! ### The radial sector and resonances -/

/-- Radial data in the sector of the core: the neck and the pin and cap feed the ray equally. -/
def RadialData.Balanced (q : ℂ) (R : RadialData) : Prop := q * R.neck = (q - 1) * R.pin + R.cap

/-- On balanced radial data the gap term does not depend on the point. -/
theorem gapOp_toFun {q : ℕ} {R : RadialData} (hR : R.Balanced q) (P : G) :
    gapOp q (R.toFun : Vertex G D → ℂ) P = (q : ℂ) * R.neck := by
  unfold gapOp
  by_cases h : 2 • P = 0
  · rw [dif_pos h, RadialData.toFun_neck, if_pos h, RadialData.toFun_cap, hR]
  · rw [dif_neg h, RadialData.toFun_neck, if_neg h]

/-- **On the radial sector of the core the second place is the first place.** -/
theorem heckeOp_balanced {q : ℕ} (Q : G) {R : RadialData} (hR : R.Balanced q) (v : Vertex G D) :
    heckeOp q Q (R.toFun : Vertex G D → ℂ) v = waveOp q R.toFun v := by
  rcases v with _ | d | x | L | ⟨P, _ | k⟩
  · rfl
  · rfl
  · induction x using Quotient.inductionOn with
    | h P =>
      change neckHecke q Q R.toFun P = neckOp q R.toFun P
      unfold neckHecke neckOp
      simp
  · simp
  · simp only [heckeOp_ray_zero, waveOp_ray_zero, gapOp_toFun hR, RadialData.toFun_ray]
  · simp

/-- The regular solution lies in the balanced sector. -/
theorem regularData_balanced (q t h lam : ℂ) : (regularData q t h lam).Balanced q := by
  unfold RadialData.Balanced regularData
  simp only [regSeq]
  ring

/-- The regular solution is an eigenfunction of every Hecke operator, with the same eigenvalue `λ`. -/
theorem Channels.heckeOp_regular (B : Channels G D) (Q : G) (lam : ℂ) (v : Vertex G D) :
    heckeOp B.q Q (B.regular lam) v = lam * B.regular lam v := by
  unfold Channels.regular
  rw [heckeOp_balanced Q (regularData_balanced _ _ _ _)]
  exact B.waveOp_regular lam v

/-- The pulse lies in the balanced sector. -/
theorem pulseData_balanced (q t h : ℂ) (τ : ℤ) : (pulseData q t h τ).Balanced q := by
  unfold RadialData.Balanced pulseData
  ring

/-- **The pulse does not feel the second place.** `T_Q u(τ) = A u(τ)` for all `τ`, so the reflected signal
carries no more information about `Q` than about `A`. -/
theorem Channels.heckeOp_pulse (B : Channels G D) (Q : G) (τ : ℤ) (v : Vertex G D) :
    heckeOp B.q Q (B.pulse τ) v = waveOp B.q (B.pulse τ) v :=
  heckeOp_balanced Q (pulseData_balanced _ _ _ _) v

/-- `T_Q 1 = (q + 1) 1`. -/
theorem Channels.heckeOp_one (B : Channels G D) (Q : G) (v : Vertex G D) :
    heckeOp B.q Q (fun _ => (1 : ℂ)) v = (B.q : ℂ) + 1 := by
  let R : RadialData := ⟨1, 1, 1, 1, 1, fun _ => 1⟩
  have hfun : (fun _ : Vertex G D => (1 : ℂ)) = R.toFun := by
    funext w
    rcases w with _ | d | x | L | ⟨P, k⟩
    · rfl
    · rfl
    · induction x using Quotient.inductionOn with
      | h P =>
        change (1 : ℂ) = R.toFun (.neck (Branch.mk P))
        rw [RadialData.toFun_neck]
        simp [R]
    · rfl
    · rfl
  have hbal : R.Balanced (B.q : ℂ) := by
    unfold RadialData.Balanced
    simp [R]
  rw [hfun, heckeOp_balanced Q hbal, ← hfun, B.waveOp_one]

/-- **A resonance does not feel the second place.** An outgoing solution is an eigenfunction of every
`T_Q`, with the eigenvalue `λ` of the wave operator, wherever the resonance is. -/
theorem IsOutgoing.hecke_eigen (B : Channels G D) {X Y : ℂ} (hXY : X * Y = B.q) (hne : X ≠ Y)
    {f : Vertex G D → ℂ} {c : G → ℂ} (hf : IsOutgoing B.q X Y f c) (Q : G) (v : Vertex G D) :
    heckeOp B.q Q f v = (X + Y) * f v := by
  have hXYsub : X - Y ≠ 0 := sub_ne_zero.mpr hne
  have hconst : ∀ P, c P = c 0 := fun P =>
    mul_right_cancel₀ hXYsub
      ((hf.core_relation B hXY P).symm.trans (hf.core_relation B hXY 0))
  have hgap (R : G) : gapOp B.q f R = X * c 0 := by
    have h := hf.eigen (.ray R 0)
    rw [waveOp_ray_zero, hf.ray R 1, hf.ray R 0, hconst R] at h
    simp only [pow_one, pow_zero, mul_one] at h
    linear_combination h
  rcases v with _ | d | x | L | ⟨P, _ | k⟩
  · rw [heckeOp_core, ← hf.eigen .core, waveOp_core]
  · rw [heckeOp_dead, ← hf.eigen (.dead d), waveOp_dead]
  · induction x using Quotient.inductionOn with
    | h P =>
      change neckHecke B.q Q f P = (X + Y) * f (.neck (Branch.mk P))
      rw [← hf.eigen (.neck (Branch.mk P)), waveOp_neck]
      unfold neckHecke neckOp
      simp only [hf.ray, hconst]
  · rw [heckeOp_cap, ← hf.eigen (.cap L), waveOp_cap]
    simp only [hf.ray, hconst]
  · rw [heckeOp_ray_zero, hgap, hf.ray, hf.ray, hconst (P - Q), hconst P]
    ring
  · rw [heckeOp_ray_succ, hf.ray, hf.ray, hf.ray, hconst (P + Q), hconst (P - Q), hconst P, ← hXY]
    ring

/-! ### Characters of the cusp group -/

/-- A nontrivial character of the cusps has mean zero. -/
theorem sum_addChar_eq_zero {χ : AddChar G ℂ} (hχ : χ ≠ 1) : ∑ P, χ P = 0 := by
  obtain ⟨Q, hQ⟩ : ∃ Q, χ Q ≠ 1 := by
    by_contra hall
    apply hχ
    ext P
    by_contra hP
    exact hall ⟨P, by simpa using hP⟩
  have h : χ Q * ∑ P, χ P = ∑ P, χ P := by
    rw [Finset.mul_sum]
    calc ∑ P, χ Q * χ P = ∑ P, χ (P + Q) := by
          refine Finset.sum_congr rfl fun P _ => ?_
          rw [AddChar.map_add_eq_mul]
          ring
      _ = ∑ P, χ P := Equiv.sum_comp (Equiv.addRight Q) (fun P => χ P)
  have h2 : (χ Q - 1) * ∑ P, χ P = 0 := by linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hQ)

/-- **The Hecke eigenvalue of a character.** On the sector of `χ ≠ 1`, for every `X ≠ 0`, the second place
of class `Q` acts by `χ(-Q) X + χ(Q) Y`. This is the only place where `T_Q` differs from `A`, and that
sector has no resonance. -/
theorem chi_hecke_eigen {q : ℕ} {X Y : ℂ} (hXY : X * Y = q) (hX : X ≠ 0) {χ : AddChar G ℂ}
    (hχ : χ ≠ 1) (Q : G) (v : Vertex G D) :
    heckeOp q Q (zeroMeanField q X Y (fun P => χ P)) v =
      (χ (-Q) * X + χ Q * Y) * zeroMeanField q X Y (fun P => χ P) v := by
  have hsum := sum_addChar_eq_zero hχ
  have split_sub (P R : G) : χ (P - R) = χ P * χ (-R) := by
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
  have split_add (P R : G) : χ (P + R) = χ P * χ R := AddChar.map_add_eq_mul χ P R
  have hnegsub (P R : G) : χ (-(P - R)) = χ (-P) * χ R := by
    rw [show -(P - R) = -P + R by abel, AddChar.map_add_eq_mul]
  rcases v with _ | d | x | L | ⟨P, _ | k⟩
  · rw [heckeOp_core]
    simp only [zeroMeanField_dead, zeroMeanField_neck, zeroMeanField_core, Finset.sum_const_zero]
    rw [sum_zeroMeanNeck X hsum]
    simp
  · simp
  · induction x using Quotient.inductionOn with
    | h P =>
      change heckeOp q Q _ (.neck (Branch.mk P)) = _ * zeroMeanField q X Y _ (.neck (Branch.mk P))
      rw [heckeOp_neck, zeroMeanField_neck]
      unfold neckHecke zeroMeanNeck
      by_cases h : 2 • P = 0
      · have e := eq_neg_of_two_nsmul h
        simp only [if_pos h, zeroMeanField_core, zeroMeanField_ray, pow_zero, mul_one, mul_zero,
          zero_add, split_sub, hnegsub, e]
        field_simp
      · simp only [if_neg h, zeroMeanField_core, zeroMeanField_ray, pow_zero, mul_one, mul_zero,
          zero_add, split_sub, hnegsub, neg_neg]
        field_simp
        ring
  · have e := eq_neg_of_two_nsmul L.2
    simp only [heckeOp_cap, zeroMeanField_cap, zeroMeanField_ray, pow_zero, mul_one, split_sub, hnegsub,
      e]
    field_simp
  · rw [heckeOp_ray_zero, gapOp_zeroMeanField hXY hX]
    have e1 : χ (-(P + Q)) = χ (-P) * χ (-Q) := by
      rw [neg_add, split_add]
    simp only [zeroMeanField_ray, pow_zero, mul_one, pow_one, split_add, split_sub, hnegsub, e1]
    field_simp
    ring
  · rw [heckeOp_ray_succ]
    have e1 : χ (-(P + Q)) = χ (-P) * χ (-Q) := by
      rw [neg_add, split_add]
    simp only [zeroMeanField_ray, split_add, split_sub, hnegsub, e1]
    rw [← hXY]
    field_simp
    ring

end GaloisForLFunctions.ArithmeticScatteringHolography

end
