import GaloisForLFunctions.ArithmeticScatteringHolography.HeckeAtASecondPlace
import GaloisForLFunctions.ArithmeticScatteringHolography.TheHorocycleIsTheWave

/-!
# The rigidity of Hecke on resonances

Take any linear operator that commutes with the wave operator and acts deep in the cusps as a shift of depth by `d`,
with any permutation of the cusps:

  `(T f)(P, k) = q^d f(σ P, k - d) + f(σ' P, k + d)`,  `k ≥ d`.

Hecke at a place of degree `d` has this form. Then `T` acts on every resonant state by the scalar `X^d + Y^d`
(`hecke_rigidity`), wherever the resonance is. The proof uses only that an outgoing solution is determined by its
amplitude. So **no Hecke operator at any place, of any degree, can constrain the position of a resonance**: its action there
is forced by the dispersion relation.

Such operators exist on every black hole and at every degree: the polynomials `P_d(A)` with `P_d(X + Y) = X^d + Y^d`
(`chebOp`), which commute with `A` and with `T_Q` and have the required form in the cusps (`chebOp_ray`). On a curve, the
true Hecke operator at a place of degree `d` is `P_d(A)` on the sector of the core: its value at the core at degree two is
`q² + 1 - h` (`chebOp_two_deltaCore`), the number of modifications of the stable bundle that are stable.
-/

open Finset

noncomputable section

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.ArithmeticScatteringHolography

variable {G D : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] [Fintype D]

/-- The wave operator is linear. -/
theorem waveOp_sub_smul (q : ℕ) (h f : Vertex G D → ℂ) (a : ℂ) (v : Vertex G D) :
    waveOp q (fun w => h w - a * f w) v = waveOp q h v - a * waveOp q f v := by
  rcases v with _ | d | x | L | ⟨P, _ | k⟩
  · simp only [waveOp_core, mul_sub, Finset.sum_sub_distrib, mul_add, Finset.mul_sum]
    have e : ∀ P : G, branchWeight P * (a * f (.neck (Branch.mk P))) =
        a * (branchWeight P * f (.neck (Branch.mk P))) := fun P => by ring
    simp only [e]
    ring
  · simp only [waveOp_dead]
    ring
  · induction x using Quotient.inductionOn with
    | h P =>
      change waveOp q _ (.neck (Branch.mk P)) =
        waveOp q h (.neck (Branch.mk P)) - a * waveOp q f (.neck (Branch.mk P))
      rw [waveOp_neck, waveOp_neck, waveOp_neck]
      unfold neckOp
      split_ifs <;> ring
  · simp only [waveOp_cap]
    ring
  · simp only [waveOp_ray_zero]
    unfold gapOp
    split_ifs <;> ring
  · simp only [waveOp_ray_succ]
    ring

theorem waveOp_zero (q : ℕ) (v : Vertex G D) : waveOp q (fun _ => (0 : ℂ)) v = 0 := by
  rcases v with _ | d | x | L | ⟨P, _ | k⟩
  · simp
  · simp
  · induction x using Quotient.inductionOn with
    | h P =>
      change waveOp q _ (.neck (Branch.mk P)) = 0
      rw [waveOp_neck]
      unfold neckOp
      split_ifs <;> simp
  · simp
  · simp only [waveOp_ray_zero]
    unfold gapOp
    split_ifs <;> simp
  · simp

theorem waveOp_smul (q : ℕ) (a : ℂ) (f : Vertex G D → ℂ) (v : Vertex G D) :
    waveOp q (fun w => a * f w) v = a * waveOp q f v := by
  have h := waveOp_sub_smul q (fun _ => (0 : ℂ)) f (-a) v
  simp only [zero_sub, neg_mul, neg_neg] at h
  rw [h, waveOp_zero]
  ring

/-- An eigenfunction on a ray is determined downwards: if it is `c Y^k` from depth `d` on, then it is `c Y^k` at all
depths. -/
theorem ray_of_ray_ge {q : ℕ} (hq : (q : ℂ) ≠ 0) {X Y : ℂ} (hXY : X * Y = q) {g : Vertex G D → ℂ}
    (hg : ∀ v, waveOp q g v = (X + Y) * g v) {c : ℂ} {P : G} {d : ℕ}
    (hd : ∀ k, d ≤ k → g (.ray P k) = c * Y ^ k) (k : ℕ) : g (.ray P k) = c * Y ^ k := by
  have key : ∀ n k, d ≤ k + n → g (.ray P k) = c * Y ^ k := by
    intro n
    induction n with
    | zero => exact fun k hk => hd k (by omega)
    | succ n ih =>
      intro k hk
      have h1 := ih (k + 1) (by omega)
      have h2 := ih (k + 2) (by omega)
      have hw := hg (.ray P (k + 1))
      rw [waveOp_ray_succ, h1, show k + 2 = k + 2 from rfl, h2] at hw
      apply mul_left_cancel₀ hq
      rw [← hXY] at hw ⊢
      linear_combination hw
  exact key d k (by omega)

/-- **The rigidity of Hecke on resonances.** A linear operator commuting with the wave operator, acting deep in the cusps as
a shift of depth by `d` with any permutation of the cusps, acts on every resonant state by the scalar `X^d + Y^d`. So no
such operator constrains the position of a resonance. -/
theorem hecke_rigidity (B : Channels G D) (T : (Vertex G D → ℂ) → Vertex G D → ℂ)
    (hsmul : ∀ (a : ℂ) f v, T (fun w => a * f w) v = a * T f v)
    (hcomm : ∀ f v, waveOp B.q (T f) v = T (waveOp B.q f) v) (d : ℕ) (σ σ' : G → G)
    (hray : ∀ f P j, T f (.ray P (d + j)) =
      (B.q : ℂ) ^ d * f (.ray (σ P) j) + f (.ray (σ' P) (2 * d + j)))
    {X Y : ℂ} (hXY : X * Y = B.q) (hne : X ≠ Y) (hlam : X + Y ≠ 0) {f : Vertex G D → ℂ} {c : G → ℂ}
    (hf : IsOutgoing B.q X Y f c) (v : Vertex G D) :
    T f v = (X ^ d + Y ^ d) * f v := by
  have hq0 := B.q_ne_zero
  have hX0 : X ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hXY
    exact hq0 hXY.symm
  have hXYsub : X - Y ≠ 0 := sub_ne_zero.mpr hne
  have hconst : ∀ P, c P = c 0 := fun P =>
    mul_right_cancel₀ hXYsub
      ((hf.core_relation B hXY P).symm.trans (hf.core_relation B hXY 0))
  have hfun : waveOp B.q f = fun w => (X + Y) * f w := funext hf.eigen
  have heig : ∀ w, waveOp B.q (T f) w = (X + Y) * T f w := fun w => by
    rw [hcomm, hfun, hsmul]
  -- the difference is an outgoing solution with zero amplitude
  set A : ℂ := X ^ d + Y ^ d with hA
  set g : Vertex G D → ℂ := fun w => T f w - A * f w with hg
  have hgeig : ∀ w, waveOp B.q g w = (X + Y) * g w := fun w => by
    rw [hg, waveOp_sub_smul, heig, hf.eigen]
    ring
  have hgray0 (P : G) (k : ℕ) (hk : d ≤ k) : g (.ray P k) = 0 * Y ^ k := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    simp only [hg]
    rw [hray, hf.ray, hf.ray, hf.ray, hconst (σ P), hconst (σ' P), hconst P, hA, ← hXY]
    rw [pow_add Y d j, show 2 * d + j = d + d + j by ring, pow_add Y (d + d) j, pow_add Y d d, mul_pow]
    ring
  have hout : IsOutgoing B.q X Y g (fun _ => 0) :=
    ⟨hgeig, fun P k => ray_of_ray_ge hq0 hXY hgeig (hgray0 P) k⟩
  have hzero := hout.eq_zero_of_amplitude B hXY hlam fun _ => rfl
  have hv := congrFun hzero v
  simp only [hg, Pi.zero_apply] at hv
  linear_combination hv

/-! ### Hecke at every degree -/

/-- The operator `P_d(A)` with `P_d(X + Y) = X^d + Y^d`: what Hecke at a place of degree `d` must be on the sector of the
core. -/
def chebOp (q : ℕ) : ℕ → (Vertex G D → ℂ) → Vertex G D → ℂ
  | 0, f => fun v => 2 * f v
  | 1, f => waveOp q f
  | d + 2, f => fun v => waveOp q (chebOp q (d + 1) f) v - (q : ℂ) * chebOp q d f v

theorem chebOp_add_two (q d : ℕ) (f : Vertex G D → ℂ) (v : Vertex G D) :
    chebOp q (d + 2) f v = waveOp q (chebOp q (d + 1) f) v - (q : ℂ) * chebOp q d f v := rfl

/-- On an eigenfunction `P_d(A)` is the scalar `X^d + Y^d`. -/
theorem chebOp_eigen {q : ℕ} {X Y : ℂ} (hXY : X * Y = q) {f : Vertex G D → ℂ}
    (hf : ∀ v, waveOp q f v = (X + Y) * f v) (d : ℕ) (v : Vertex G D) :
    chebOp q d f v = (X ^ d + Y ^ d) * f v := by
  induction d using Nat.twoStepInduction generalizing v with
  | zero =>
    simp only [chebOp, pow_zero]
    ring
  | one =>
    simp only [chebOp, pow_one]
    exact hf v
  | more d h0 h1 =>
    rw [chebOp_add_two]
    have hfun : chebOp q (d + 1) f = fun w => (X ^ (d + 1) + Y ^ (d + 1)) * f w := funext h1
    have hlin : waveOp q (chebOp q (d + 1) f) v = (X ^ (d + 1) + Y ^ (d + 1)) * ((X + Y) * f v) := by
      rw [hfun, waveOp_smul, hf]
    rw [hlin, h0, ← hXY]
    ring

/-- `P_d(A)` commutes with the wave operator. -/
theorem chebOp_comm_waveOp (q d : ℕ) (f : Vertex G D → ℂ) (v : Vertex G D) :
    waveOp q (chebOp q d f) v = chebOp q d (waveOp q f) v := by
  induction d using Nat.twoStepInduction generalizing v f with
  | zero =>
    exact waveOp_smul q 2 f v
  | one =>
    rfl
  | more d h0 h1 =>
    have e : chebOp q (d + 2) f = fun w => waveOp q (chebOp q (d + 1) f) w - (q : ℂ) * chebOp q d f w :=
      rfl
    rw [e, waveOp_sub_smul, chebOp_add_two]
    have e1 : chebOp q (d + 1) (waveOp q f) = waveOp q (chebOp q (d + 1) f) :=
      funext fun w => (h1 f w).symm
    rw [e1, h0 f v]

/-- `P_d(A)` commutes with the Hecke operators at rational places. -/
theorem chebOp_comm_heckeOp (B : Channels G D) (Q : G) (d : ℕ) (f : Vertex G D → ℂ) (v : Vertex G D) :
    heckeOp B.q Q (chebOp B.q d f) v = chebOp B.q d (heckeOp B.q Q f) v := by
  induction d using Nat.twoStepInduction generalizing v f with
  | zero =>
    exact heckeOp_smul B.q Q 2 f v
  | one =>
    exact (heckeOp_comm_waveOp B Q f v).symm
  | more d h0 h1 =>
    have e : chebOp B.q (d + 2) f = fun w => waveOp B.q (chebOp B.q (d + 1) f) w +
        (-(B.q : ℂ)) * chebOp B.q d f w := by
      funext w
      rw [chebOp_add_two]
      ring
    rw [e, heckeOp_add, heckeOp_smul, chebOp_add_two, ← heckeOp_comm_waveOp B Q]
    have e1 : heckeOp B.q Q (chebOp B.q (d + 1) f) = chebOp B.q (d + 1) (heckeOp B.q Q f) :=
      funext fun w => h1 f w
    rw [e1, h0 f v]
    ring

/-- **Hecke of degree `d` in the cusps.** -/
theorem chebOp_ray (q d : ℕ) (f : Vertex G D → ℂ) (P : G) (j : ℕ) :
    chebOp q d f (.ray P (d + j)) = (q : ℂ) ^ d * f (.ray P j) + f (.ray P (2 * d + j)) := by
  induction d using Nat.twoStepInduction generalizing j with
  | zero =>
    simp only [chebOp, pow_zero, zero_add, mul_zero]
    ring
  | one =>
    simp only [chebOp, pow_one]
    rw [show 1 + j = j + 1 by ring, waveOp_ray_succ, show 2 * 1 + j = j + 2 by ring]
  | more d h0 h1 =>
    rw [chebOp_add_two]
    rw [show d + 2 + j = (d + 1 + j) + 1 by ring, waveOp_ray_succ, h1 j,
      show d + 1 + j + 2 = d + 1 + (j + 2) by ring, h1 (j + 2)]
    rw [show d + 1 + j + 1 = d + (j + 2) by ring, h0 (j + 2)]
    rw [show 2 * (d + 1) + (j + 2) = 2 * (d + 2) + j by ring,
      show 2 * (d + 1) + j = 2 * d + (j + 2) by ring]
    ring

/-- **The first return of Hecke at degree two reads the channels.** `q² + 1 - h` at the core, nonnegative on every black
hole. -/
theorem Channels.chebOp_two_deltaCore (B : Channels G D) :
    chebOp B.q 2 (deltaCore : Vertex G D → ℂ) .core = (B.q : ℂ) ^ 2 + 1 - cuspCount G := by
  rw [show (2 : ℕ) = 0 + 2 from rfl, chebOp_add_two]
  have h1 : chebOp B.q (0 + 1) (deltaCore : Vertex G D → ℂ) = waveOp B.q deltaCore := rfl
  rw [h1, B.waveOp_waveOp_deltaCore]
  simp only [chebOp, deltaCore]
  rw [B.cuspCount_eq]
  ring

end GaloisForLFunctions.ArithmeticScatteringHolography

end
