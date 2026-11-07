import GaloisForLFunctions.ArithmeticScatteringHolography.TheWavePropagatorIsPositive

/-!
# The cuspidal sector

Every function on a black hole with odd groups has a shadow on the second group: the even function `g(Q) = deadTerm(Q)/q` on `G'`,
which is `f` on the dead ends and `((q+1) f(pin) - f(cap))/q` at zero. The cuspidal sector is where this shadow lives alone. For a
nontrivial character `ψ` of `G'` the function `θ_ψ`, equal to `ψ + ψ⁻¹` on the dead ends, `1` on the pin and `1 - q` on the cap, vanishes on
the core and on every ray: it is a compactly supported eigenfunction of `A` with eigenvalue `0` (`thetaField_wave`). These are the cusp
forms of `Γ\T`, induced from the constant extension `𝔽_{q²}`.

The translation operator `Λ_w` of the second group (`thetaOp`) acts on the shadow by `g(Q + w) + g(Q - w) - 2 g(Q)` (`thetaTerm_thetaOp`),
and is killed by `A` and `T_Q` on both sides. So Hecke of degree two is the propagator corrected on this sector only (`heckeTwo_eq`):

  `T_{2Q, w} = P₂(T_Q) - q Λ_w`,

and on `θ_ψ` it has the eigenvalue `-q(ψ(w) + ψ(-w))` (`heckeTwo_thetaField`), while `A` and `T_Q` have the eigenvalue `0`.

**This answers where Hecke at a second place is an independent constraint.** On the sector of the cusp forms it is independent of the wave
operator: it separates forms with the same `λ` (`heckeTwo_separates`). There it constrains nothing either, since this sector has no flux
and no resonance. On the sector of the resonances it is not independent (`hecke_rigidity`). The two sectors do not meet.

`Λ_w` is symmetric for the mass (`truncSum_thetaOp_green`), so the operators of every degree are symmetric on compactly supported functions
(`heckeDeg_symmetric`, `heckeTwo_symmetric`).
-/

open Finset

noncomputable section

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.ArithmeticScatteringHolography

variable {G G' : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] [AddCommGroup G'] [DecidableEq G']
  [Fintype G']

/-- The shadow of `f` on the second group. -/
def thetaTerm (q : ℕ) (f : Vertex G (DeadLabel G') → ℂ) (Q : G') : ℂ := deadTerm q f Q / q

theorem thetaTerm_neg (q : ℕ) (f : Vertex G (DeadLabel G') → ℂ) (Q : G') :
    thetaTerm q f (-Q) = thetaTerm q f Q := by
  unfold thetaTerm
  rw [deadTerm_neg]

/-- The second difference of the shadow in the direction `w`. -/
def thetaDiff (q : ℕ) (f : Vertex G (DeadLabel G') → ℂ) (w Q : G') : ℂ :=
  thetaTerm q f (Q + w) + thetaTerm q f (Q - w) - 2 * thetaTerm q f Q

theorem thetaDiff_neg (q : ℕ) (f : Vertex G (DeadLabel G') → ℂ) (w Q : G') :
    thetaDiff q f w (-Q) = thetaDiff q f w Q := by
  unfold thetaDiff
  rw [show -Q + w = -(Q - w) by abel, show -Q - w = -(Q + w) by abel, thetaTerm_neg, thetaTerm_neg,
    thetaTerm_neg]
  ring

/-- The value of `Λ_w` at the neck of `P`: only the pins carry it. -/
def thetaNeck (q : ℕ) (f : Vertex G (DeadLabel G') → ℂ) (w : G') (P : G) : ℂ :=
  if 2 • P = 0 then thetaTerm q f w - thetaTerm q f 0 else 0

theorem thetaNeck_neg (q : ℕ) (f : Vertex G (DeadLabel G') → ℂ) (w : G') (P : G) :
    thetaNeck q f w (-P) = thetaNeck q f w P := by
  unfold thetaNeck
  simp only [two_nsmul_neg_eq_zero_iff]

/-- **The translation operator of the second group.** -/
def thetaOp (q : ℕ) (w : G') (f : Vertex G (DeadLabel G') → ℂ) : Vertex G (DeadLabel G') → ℂ
  | .core => 0
  | .dead d => Quotient.liftOn d.1 (thetaDiff q f w) (fun P R h => by
      rcases h with rfl | rfl
      · rfl
      · exact (thetaDiff_neg q f w P).symm)
  | .neck x => Quotient.liftOn x (thetaNeck q f w) (fun P R h => by
      rcases h with rfl | rfl
      · rfl
      · exact (thetaNeck_neg q f w P).symm)
  | .cap _ => -((q : ℂ) - 1) * (thetaTerm q f w - thetaTerm q f 0)
  | .ray _ _ => 0

variable (q : ℕ) (w : G') (f : Vertex G (DeadLabel G') → ℂ)

@[simp] theorem thetaOp_core : thetaOp q w f .core = 0 := rfl
theorem thetaOp_dead (Q : G') (h : Branch.mk Q ≠ Branch.mk 0) :
    thetaOp q w f (.dead ⟨Branch.mk Q, h⟩) = thetaDiff q f w Q := rfl
@[simp] theorem thetaOp_neck (P : G) :
    thetaOp q w f (.neck (Branch.mk P)) = thetaNeck q f w P := rfl
@[simp] theorem thetaOp_cap (L : TwoTorsion G) :
    thetaOp q w f (.cap L) = -((q : ℂ) - 1) * (thetaTerm q f w - thetaTerm q f 0) := rfl
@[simp] theorem thetaOp_ray (P : G) (k : ℕ) : thetaOp q w f (.ray P k) = 0 := rfl

/-- The lift of the second difference to the classes. -/
def thetaDiffB (q : ℕ) (f : Vertex G (DeadLabel G') → ℂ) (w : G') (x : Branch G') : ℂ :=
  Quotient.liftOn x (thetaDiff q f w) (fun P R h => by
    rcases h with rfl | rfl
    · rfl
    · exact (thetaDiff_neg q f w P).symm)

theorem thetaOp_dead' (d : DeadLabel G') : thetaOp q w f (.dead d) = thetaDiffB q f w d.1 := by
  obtain ⟨x, hx⟩ := d
  induction x using Quotient.inductionOn with
  | h Q => rfl

section Odd

variable (hG : ∀ P : G, 2 • P = 0 → P = 0) (hG' : ∀ Q : G', 2 • Q = 0 → Q = 0)

/-- The second differences sum to zero. -/
theorem sum_thetaDiff : ∑ Q : G', thetaDiff q f w Q = 0 := by
  unfold thetaDiff
  have h1 : ∑ Q : G', thetaTerm q f (Q + w) = ∑ Q, thetaTerm q f Q :=
    Equiv.sum_comp (Equiv.addRight w) (thetaTerm q f)
  have h2 : ∑ Q : G', thetaTerm q f (Q - w) = ∑ Q, thetaTerm q f Q :=
    Equiv.sum_comp (Equiv.subRight w) (thetaTerm q f)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, h1, h2, ← Finset.mul_sum]
  ring

include hG in
/-- A sum over `G` weighted on the necks that is carried by the two-torsion alone. -/
theorem sum_neck_of_torsion (c : ℂ) :
    ∑ P : G, branchWeight P * (if 2 • P = 0 then c else 0) = c := by
  rw [Finset.sum_eq_single 0]
  · simp [branchWeight]
  · intro b _ hb
    have hb' : ¬ 2 • b = 0 := fun h => hb (hG b h)
    simp [hb']
  · simp

end Odd

/-- The shadow of `A f` is constant. -/
theorem thetaTerm_waveOp (B : Channels G (DeadLabel G')) (f : Vertex G (DeadLabel G') → ℂ) (Q : G') :
    thetaTerm B.q (waveOp B.q f) Q = ((B.q : ℂ) + 1) * f .core := by
  unfold thetaTerm
  rw [deadTerm_waveOp]
  have := B.q_ne_zero
  field_simp

/-- The shadow of `T_Q f` is constant. -/
theorem thetaTerm_heckeOp (B : Channels G (DeadLabel G')) (R : G) (f : Vertex G (DeadLabel G') → ℂ)
    (Q : G') : thetaTerm B.q (heckeOp B.q R f) Q = ((B.q : ℂ) + 1) * f .core := by
  have h : deadTerm B.q (heckeOp B.q R f) Q = (B.q : ℂ) * (((B.q : ℂ) + 1) * f .core) := by
    unfold deadTerm deadTermB
    by_cases h : Branch.mk Q = Branch.mk 0
    · rw [dif_pos h, heckeOp_neck, heckeOp_cap]
      unfold neckHecke capZero
      simp only [if_pos (by simp : 2 • (0 : G) = 0)]
      ring
    · rw [dif_neg h, heckeOp_dead]
  unfold thetaTerm
  rw [h]
  have := B.q_ne_zero
  field_simp

/-- `Λ_w` kills the image of a function with constant shadow. -/
theorem thetaOp_of_const (q : ℕ) (w : G') {g : Vertex G (DeadLabel G') → ℂ} {c : ℂ}
    (hg : ∀ Q, thetaTerm q g Q = c) (v : Vertex G (DeadLabel G')) : thetaOp q w g v = 0 := by
  rcases v with _ | d | x | L | ⟨P, k⟩
  · rfl
  · rw [thetaOp_dead']
    obtain ⟨x, hx⟩ := d
    induction x using Quotient.inductionOn with
    | h Q =>
      change thetaDiff q g w Q = 0
      unfold thetaDiff
      rw [hg, hg, hg]
      ring
  · induction x using Quotient.inductionOn with
    | h P =>
      change thetaNeck q g w P = 0
      unfold thetaNeck
      rw [hg, hg]
      simp
  · rw [thetaOp_cap, hg, hg]
    ring
  · rfl

theorem thetaOp_waveOp (B : Channels G (DeadLabel G')) (w : G') (f : Vertex G (DeadLabel G') → ℂ)
    (v : Vertex G (DeadLabel G')) : thetaOp B.q w (waveOp B.q f) v = 0 :=
  thetaOp_of_const B.q w (thetaTerm_waveOp B f) v

theorem thetaOp_heckeOp (B : Channels G (DeadLabel G')) (R : G) (w : G')
    (f : Vertex G (DeadLabel G') → ℂ) (v : Vertex G (DeadLabel G')) :
    thetaOp B.q w (heckeOp B.q R f) v = 0 :=
  thetaOp_of_const B.q w (thetaTerm_heckeOp B R f) v

section Odd2

variable (B : Channels G (DeadLabel G')) (hG : ∀ P : G, 2 • P = 0 → P = 0)
  (hG' : ∀ Q : G', 2 • Q = 0 → Q = 0)

/-- The gap term of `Λ_w f` vanishes: the pin and the cap cancel at the root of the ray. -/
theorem gapOp_thetaOp (w : G') (f : Vertex G (DeadLabel G') → ℂ) (R : G) :
    gapOp B.q (thetaOp B.q w f) R = 0 := by
  unfold gapOp
  by_cases h : 2 • R = 0
  · rw [dif_pos h, thetaOp_neck, thetaOp_cap]
    unfold thetaNeck
    rw [if_pos h]
    ring
  · rw [dif_neg h, thetaOp_neck]
    unfold thetaNeck
    rw [if_neg h]
    ring

include hG hG' in
/-- The core row of `Λ_w`: the dead ends and the pin balance. -/
theorem core_thetaOp (w : G') (f : Vertex G (DeadLabel G') → ℂ) :
    ∑ d : DeadLabel G', thetaOp B.q w f (.dead d) +
        ∑ P : G, branchWeight P * thetaOp B.q w f (.neck (Branch.mk P)) = 0 := by
  simp only [thetaOp_dead', thetaOp_neck]
  have hsum := sum_deadLabel (G' := G') (thetaDiffB B.q f w)
  have e (P : G') : thetaDiffB B.q f w (Branch.mk P) = thetaDiff B.q f w P := rfl
  simp only [e] at hsum
  rw [sum_weighted_odd hG', sum_thetaDiff] at hsum
  rw [hsum]
  have hneck : ∑ P : G, branchWeight P * thetaNeck B.q f w P =
      thetaTerm B.q f w - thetaTerm B.q f 0 := by
    unfold thetaNeck
    exact sum_neck_of_torsion hG _
  rw [hneck]
  unfold thetaDiff
  rw [zero_add, zero_sub, thetaTerm_neg]
  ring

include hG hG' in
/-- **`A Λ_w = 0`**: the image of `Λ_w` lies in the kernel of the wave operator. -/
theorem waveOp_thetaOp (w : G') (f : Vertex G (DeadLabel G') → ℂ) (v : Vertex G (DeadLabel G')) :
    waveOp B.q (thetaOp B.q w f) v = 0 := by
  rcases v with _ | d | x | L | ⟨P, _ | k⟩
  · exact core_thetaOp B hG hG' w f
  · simp
  · induction x using Quotient.inductionOn with
    | h P =>
      change neckOp B.q (thetaOp B.q w f) P = 0
      unfold neckOp
      simp
  · simp
  · rw [waveOp_ray_zero, gapOp_thetaOp]
    simp
  · simp

include hG hG' in
/-- `T_R Λ_w = 0`. -/
theorem heckeOp_thetaOp (R : G) (w : G') (f : Vertex G (DeadLabel G') → ℂ)
    (v : Vertex G (DeadLabel G')) : heckeOp B.q R (thetaOp B.q w f) v = 0 := by
  rcases v with _ | d | x | L | ⟨P, _ | k⟩
  · exact core_thetaOp B hG hG' w f
  · simp
  · induction x using Quotient.inductionOn with
    | h P =>
      change neckHecke B.q R (thetaOp B.q w f) P = 0
      unfold neckHecke
      simp
  · simp
  · rw [heckeOp_ray_zero, gapOp_thetaOp]
    simp
  · simp

/-- The shadow of `Λ_w f` is the second difference of the shadow of `f`. -/
theorem thetaTerm_thetaOp (w : G') (f : Vertex G (DeadLabel G') → ℂ) (Q : G') :
    thetaTerm B.q (thetaOp B.q w f) Q = thetaDiff B.q f w Q := by
  have hq := B.q_ne_zero
  unfold thetaTerm
  by_cases h : Branch.mk Q = Branch.mk 0
  · have hQ : Q = 0 := by
      rcases mk_eq_mk_iff.mp h with h | h
      · exact h.symm
      · simpa [eq_comm] using h
    subst hQ
    rw [deadTerm_zero_eq, thetaOp_neck, thetaOp_cap]
    unfold thetaNeck
    rw [if_pos (by simp : 2 • (0 : G) = 0)]
    unfold thetaDiff
    rw [zero_add, zero_sub, thetaTerm_neg]
    field_simp
    ring
  · unfold deadTerm deadTermB
    rw [dif_neg h, thetaOp_dead]
    field_simp

/-- **The operators `Λ_w` commute**: they act on the shadow by convolution on `G'`. -/
theorem thetaOp_comm (w u : G') (f : Vertex G (DeadLabel G') → ℂ) (v : Vertex G (DeadLabel G')) :
    thetaOp B.q w (thetaOp B.q u f) v = thetaOp B.q u (thetaOp B.q w f) v := by
  have hdiff (Q : G') : thetaDiff B.q (thetaOp B.q u f) w Q = thetaDiff B.q (thetaOp B.q w f) u Q := by
    unfold thetaDiff
    simp only [thetaTerm_thetaOp]
    unfold thetaDiff
    rw [show Q + w + u = Q + u + w by abel, show Q + w - u = Q - u + w by abel,
      show Q - w + u = Q + u - w by abel, show Q - w - u = Q - u - w by abel]
    ring
  have hzero : thetaTerm B.q (thetaOp B.q u f) w - thetaTerm B.q (thetaOp B.q u f) 0 =
      thetaTerm B.q (thetaOp B.q w f) u - thetaTerm B.q (thetaOp B.q w f) 0 := by
    have h := hdiff 0
    unfold thetaDiff at h
    simp only [zero_add, zero_sub, thetaTerm_neg] at h
    apply mul_left_cancel₀ (two_ne_zero (α := ℂ))
    linear_combination h
  rcases v with _ | d | x | L | ⟨P, k⟩
  · rfl
  · rw [thetaOp_dead', thetaOp_dead']
    obtain ⟨x, hx⟩ := d
    induction x using Quotient.inductionOn with
    | h Q => exact hdiff Q
  · induction x using Quotient.inductionOn with
    | h P =>
      change thetaNeck B.q _ w P = thetaNeck B.q _ u P
      unfold thetaNeck
      rw [hzero]
  · rw [thetaOp_cap, thetaOp_cap, hzero]
  · rfl

/-! ### The cusp forms -/

/-- **The cusp form of a character of the second group**: `ψ + ψ⁻¹` on the dead ends, `1` on the pins, `1 - q` on the caps. -/
def thetaField (G : Type*) [AddCommGroup G] [DecidableEq G] [Fintype G] (q : ℕ) (ψ : AddChar G' ℂ) :
    Vertex G (DeadLabel G') → ℂ
  | .core => 0
  | .dead d => Quotient.liftOn d.1 (fun Q => ψ Q + ψ (-Q)) (fun P R h => by
      rcases h with rfl | rfl
      · rfl
      · simp only [neg_neg]
        ring)
  | .neck x => Quotient.liftOn x (fun P : G => if 2 • P = 0 then (1 : ℂ) else 0) (fun P R h => by
      rcases h with rfl | rfl
      · rfl
      · simp only [two_nsmul_neg_eq_zero_iff])
  | .cap _ => 1 - (q : ℂ)
  | .ray _ _ => 0

section Field

variable (ψ : AddChar G' ℂ)

@[simp] theorem thetaField_core : thetaField G B.q ψ .core = (0 : ℂ) := rfl
@[simp] theorem thetaField_neck (P : G) :
    thetaField G B.q ψ (.neck (Branch.mk P)) = if 2 • P = 0 then (1 : ℂ) else 0 := rfl
@[simp] theorem thetaField_cap (L : TwoTorsion G) : thetaField G B.q ψ (.cap L) = 1 - (B.q : ℂ) := rfl
@[simp] theorem thetaField_ray (P : G) (k : ℕ) : thetaField G B.q ψ (.ray P k) = (0 : ℂ) := rfl
theorem thetaField_dead (Q : G') (h : Branch.mk Q ≠ Branch.mk 0) :
    thetaField G B.q ψ (.dead ⟨Branch.mk Q, h⟩) = ψ Q + ψ (-Q) := rfl

/-- The shadow of `θ_ψ` is `ψ + ψ⁻¹` on the whole of `G'`. -/
theorem thetaTerm_thetaField (Q : G') :
    thetaTerm B.q (thetaField G B.q ψ) Q = ψ Q + ψ (-Q) := by
  have hq := B.q_ne_zero
  unfold thetaTerm
  by_cases h : Branch.mk Q = Branch.mk 0
  · have hQ : Q = 0 := by
      rcases mk_eq_mk_iff.mp h with h | h
      · exact h.symm
      · simpa [eq_comm] using h
    subst hQ
    rw [deadTerm_zero_eq, thetaField_neck]
    simp only [capZero, thetaField_cap, if_pos (by simp : 2 • (0 : G) = 0), neg_zero,
      AddChar.map_zero_eq_one]
    field_simp
    ring
  · unfold deadTerm deadTermB
    rw [dif_neg h, thetaField_dead]
    field_simp

theorem deadTerm_thetaField (Q : G') :
    deadTerm B.q (thetaField G B.q ψ) Q = (B.q : ℂ) * (ψ Q + ψ (-Q)) := by
  have h := thetaTerm_thetaField B ψ (G := G) Q
  unfold thetaTerm at h
  have hq := B.q_ne_zero
  field_simp at h
  linear_combination h

theorem gapOp_thetaField (R : G) :
    gapOp B.q (thetaField G B.q ψ) R = 0 := by
  unfold gapOp
  by_cases h : 2 • R = 0
  · rw [dif_pos h, thetaField_neck, thetaField_cap, if_pos h]
    ring
  · rw [dif_neg h, thetaField_neck, if_neg h]
    ring

include hG hG' in
/-- The sum of `θ_ψ` over the neighbours of the core vanishes. -/
theorem core_thetaField {ψ : AddChar G' ℂ} (hψ : ψ ≠ 1) :
    waveOp B.q (thetaField G B.q ψ) .core = 0 := by
  rw [waveOp_core]
  simp only [thetaField_neck]
  have hsum := sum_deadLabel (G' := G')
    (fun x => Quotient.liftOn x (fun Q => ψ Q + ψ (-Q)) (fun P R h => by
      rcases h with rfl | rfl
      · rfl
      · simp only [neg_neg]
        ring))
  have e (P : G') : (Quotient.liftOn (Branch.mk P) (fun Q => ψ Q + ψ (-Q)) (fun P R h => by
      rcases h with rfl | rfl
      · rfl
      · simp only [neg_neg]
        ring) : ℂ) = ψ P + ψ (-P) := rfl
  simp only [e] at hsum
  rw [sum_weighted_odd hG'] at hsum
  have h1 : ∑ Q : G', ψ Q = 0 := sum_addChar_eq_zero hψ
  have h2 : ∑ Q : G', ψ (-Q) = 0 := (Equiv.sum_comp (Equiv.neg G') (fun Q => ψ Q)).trans h1
  have hd : ∑ d : DeadLabel G', thetaField G B.q ψ (.dead d : Vertex G (DeadLabel G')) =
      ∑ d : DeadLabel G', Quotient.liftOn d.1 (fun Q => ψ Q + ψ (-Q)) (fun P R h => by
        rcases h with rfl | rfl
        · rfl
        · simp only [neg_neg]
          ring) := rfl
  rw [hd, hsum, Finset.sum_add_distrib, h1, h2, sum_neck_of_torsion hG]
  simp
  ring

include hG hG' in
/-- **The cusp forms have eigenvalue `0`**, and they vanish on the cusps. -/
theorem thetaField_wave {ψ : AddChar G' ℂ} (hψ : ψ ≠ 1) (v : Vertex G (DeadLabel G')) :
    waveOp B.q (thetaField G B.q ψ) v = 0 := by
  rcases v with _ | d | x | L | ⟨P, _ | k⟩
  · exact core_thetaField B hG hG' hψ
  · simp
  · induction x using Quotient.inductionOn with
    | h P =>
      change neckOp B.q _ P = 0
      unfold neckOp
      simp
  · simp
  · rw [waveOp_ray_zero, gapOp_thetaField]
    simp
  · simp

include hG hG' in
/-- The rational places also act by zero on the cusp forms. -/
theorem heckeOp_thetaField {ψ : AddChar G' ℂ} (hψ : ψ ≠ 1) (R : G) (v : Vertex G (DeadLabel G')) :
    heckeOp B.q R (thetaField G B.q ψ) v = 0 := by
  rcases v with _ | d | x | L | ⟨P, _ | k⟩
  · exact core_thetaField B hG hG' hψ
  · simp
  · induction x using Quotient.inductionOn with
    | h P =>
      change neckHecke B.q R _ P = 0
      unfold neckHecke
      simp
  · simp
  · rw [heckeOp_ray_zero, gapOp_thetaField]
    simp
  · simp

theorem thetaField_ne_zero : (thetaField G B.q ψ) ≠ 0 := by
  intro h
  have h0 := congrFun h (.neck (Branch.mk 0))
  rw [thetaField_neck, if_pos (by simp)] at h0
  simp at h0

include hG hG' in
/-- **Hecke of degree two on the cusp forms**: the eigenvalue `-q(ψ(w) + ψ(-w))` depends on `w`, while `A` and `T_Q` act by `0`. -/
theorem heckeTwo_thetaField {ψ : AddChar G' ℂ} (hψ : ψ ≠ 1) (Q₀ : G) (w : G')
    (v : Vertex G (DeadLabel G')) :
    heckeTwo B.q B.trace Q₀ w (thetaField G B.q ψ) v =
      -(B.q : ℂ) * (ψ w + ψ (-w)) * thetaField G B.q ψ v := by
  have hS := core_thetaField B hG hG' hψ
  have hsplit (Q R : G') : ψ (Q + R) = ψ Q * ψ R := AddChar.map_add_eq_mul ψ Q R
  rcases v with _ | d | x | L | ⟨P, _ | _ | k⟩
  · simp
  · rw [heckeTwo_dead', hS]
    obtain ⟨x, hx⟩ := d
    induction x using Quotient.inductionOn with
    | h Q =>
      change _ - deadShift B.q _ w Q = _ * thetaField G B.q ψ (.dead ⟨Branch.mk Q, hx⟩)
      rw [thetaField_dead]
      unfold deadShift
      rw [deadTerm_thetaField, deadTerm_thetaField]
      rw [show -(Q + w) = -Q + -w by abel, show Q - w = Q + -w by abel, show -(Q + -w) = -Q + w by abel]
      simp only [hsplit]
      ring
  · induction x using Quotient.inductionOn with
    | h P =>
      change heckeTwo B.q B.trace Q₀ w _ (.neck (Branch.mk P)) = _ * thetaField G B.q ψ (.neck (Branch.mk P))
      rw [heckeTwo_neck, hS, thetaField_neck]
      unfold neckTwo
      by_cases h : 2 • P = 0
      · simp only [if_pos h, thetaField_ray, deadTerm_thetaField]
        ring
      · simp only [if_neg h, thetaField_ray]
        ring
  · rw [heckeTwo_cap, deadTerm_thetaField, thetaField_ray, thetaField_cap]
    ring
  · simp
  · simp [gapOp_thetaField]
  · simp

include hG hG' in
/-- **The translations of `G'` on the cusp forms.** -/
theorem thetaOp_thetaField (w : G') (v : Vertex G (DeadLabel G')) :
    thetaOp B.q w (thetaField G B.q ψ) v = (ψ w + ψ (-w) - 2) * thetaField G B.q ψ v := by
  have hsplit (Q R : G') : ψ (Q + R) = ψ Q * ψ R := AddChar.map_add_eq_mul ψ Q R
  have h0 : ψ 0 = 1 := AddChar.map_zero_eq_one ψ
  rcases v with _ | d | x | L | ⟨P, k⟩
  · simp
  · rw [thetaOp_dead']
    obtain ⟨x, hx⟩ := d
    induction x using Quotient.inductionOn with
    | h Q =>
      change thetaDiff B.q _ w Q = _ * thetaField G B.q ψ (.dead ⟨Branch.mk Q, hx⟩)
      rw [thetaField_dead]
      unfold thetaDiff
      simp only [thetaTerm_thetaField]
      rw [show -(Q + w) = -Q + -w by abel, show Q - w = Q + -w by abel, show -(Q + -w) = -Q + w by abel]
      simp only [hsplit]
      ring
  · induction x using Quotient.inductionOn with
    | h P =>
      change thetaNeck B.q _ w P = _ * thetaField G B.q ψ (.neck (Branch.mk P))
      rw [thetaField_neck]
      unfold thetaNeck
      simp only [thetaTerm_thetaField, neg_zero, h0]
      by_cases h : 2 • P = 0
      · simp only [if_pos h]
        ring
      · simp only [if_neg h]
        ring
  · rw [thetaOp_cap, thetaField_cap]
    simp only [thetaTerm_thetaField, neg_zero, h0]
    ring
  · simp

end Field

/-! ### Hecke of degree two is the propagator on the other sectors -/

include hG hG' in
/-- **`T_{2Q, w} = P₂(T_Q) - q Λ_w`.** -/
theorem heckeTwo_eq (Q : G) (w : G') (f : Vertex G (DeadLabel G') → ℂ) (v : Vertex G (DeadLabel G')) :
    heckeTwo B.q B.trace (2 • Q) w f v =
      heckeDeg B.q Q 2 f v - (B.q : ℂ) * thetaOp B.q w f v := by
  have hq := B.q_ne_zero
  have e0 : heckeDeg B.q Q 2 f v = heckeOp B.q Q (heckeOp B.q Q f) v - (B.q : ℂ) * (2 * f v) := by
    have h := heckeDeg_add_two B.q Q 0 f v
    have e1 : heckeDeg B.q Q (0 + 1) f = heckeOp B.q Q f := funext (heckeDeg_one B.q Q f)
    rw [show (0 + 2 : ℕ) = 2 from rfl, e1, heckeDeg_zero] at h
    exact h
  have h2Q : 2 • Q = Q + Q := two_nsmul Q
  have hS : heckeOp B.q Q f .core = waveOp B.q f .core := rfl
  rw [e0]
  rcases v with _ | d | x | L | ⟨P, _ | _ | k⟩
  · -- the core
    rw [heckeTwo_core, thetaOp_core, heckeOp_core]
    simp only [heckeOp_dead, heckeOp_neck, sum_neckHecke, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    have hk := B.kappa_sum
    linear_combination (-(f .core)) * hk
  · -- a dead end
    rw [heckeTwo_dead', heckeOp_dead, hS]
    rw [thetaOp_dead']
    obtain ⟨x, hx⟩ := d
    induction x using Quotient.inductionOn with
    | h R =>
      have hx' : Branch.mk R ≠ Branch.mk 0 := hx
      change _ - deadShift B.q f w R = _ - _ * (2 * f (.dead ⟨Branch.mk R, hx'⟩)) -
        (B.q : ℂ) * thetaDiff B.q f w R
      unfold deadShift thetaDiff thetaTerm
      have hR : deadTerm B.q f R = (B.q : ℂ) * f (.dead ⟨Branch.mk R, hx'⟩) := by
        unfold deadTerm deadTermB
        rw [dif_neg hx']
      rw [hR]
      field_simp
      ring
  · -- a neck
    induction x using Quotient.inductionOn with
    | h P =>
      change heckeTwo B.q B.trace (2 • Q) w f (.neck (Branch.mk P)) =
        heckeOp B.q Q (heckeOp B.q Q f) (.neck (Branch.mk P)) -
          (B.q : ℂ) * (2 * f (.neck (Branch.mk P))) - (B.q : ℂ) * thetaOp B.q w f (.neck (Branch.mk P))
      rw [heckeTwo_neck, heckeOp_neck, thetaOp_neck]
      unfold neckTwo neckHecke thetaNeck
      by_cases h : 2 • P = 0
      · have hP : P = 0 := hG P h
        subst hP
        simp only [if_pos h, heckeOp_core, heckeOp_ray_zero]
        have e1 : gapOp B.q f (0 - Q + Q) = ((B.q : ℂ) - 1) * f (.neck (Branch.mk 0)) +
            f (.cap (capZero G)) := by
          rw [show (0 : G) - Q + Q = 0 by abel, gapOp_zero_eq]
        rw [e1, show (0 : G) - Q - Q = 0 - 2 • Q by rw [h2Q]; abel]
        unfold thetaTerm
        rw [deadTerm_zero_eq]
        change _ = (B.q : ℂ) * waveOp B.q f .core + _ - _ - _
        field_simp
        ring
      · have hg (R : G) (hR : ¬ 2 • R = 0) : gapOp B.q f R = (B.q : ℂ) * f (.neck (Branch.mk R)) := by
          unfold gapOp
          rw [dif_neg hR]
        have h' : ¬ 2 • (-P) = 0 := by rwa [two_nsmul_neg_eq_zero_iff]
        simp only [if_neg h, heckeOp_core, heckeOp_ray_zero]
        rw [show P - Q + Q = P by abel, show -P - Q + Q = -P by abel, hg P h, hg (-P) h', Branch.mk_neg,
          show P - Q - Q = P - 2 • Q by rw [h2Q]; abel, show -P - Q - Q = -P - 2 • Q by rw [h2Q]; abel]
        change _ = ((B.q : ℂ) - 1) * waveOp B.q f .core + _ + _ - _ - _
        ring
  · -- a cap
    have hL : L = capZero G := Subtype.ext (hG L.1 L.2)
    subst hL
    rw [heckeTwo_cap, heckeOp_cap, heckeOp_ray_zero, thetaOp_cap]
    have hz : (capZero G).1 = 0 := rfl
    rw [hz, show (0 : G) - Q + Q = 0 by abel, gapOp_zero_eq,
      show (0 : G) - Q - Q = 0 - 2 • Q by rw [h2Q]; abel]
    unfold thetaTerm
    rw [deadTerm_zero_eq]
    field_simp
    ring
  · -- the root of a ray
    rw [heckeTwo_ray_zero, heckeOp_ray_zero, gapOp_heckeOp, thetaOp_ray]
    have e1 : heckeOp B.q Q f (.ray (P - Q) 1) =
        (B.q : ℂ) * f (.ray (P - Q + Q) 0) + f (.ray (P - Q - Q) 2) := rfl
    rw [e1, show P + Q - Q = P by abel, show P - Q + Q = P by abel,
      show -(P + Q) - Q = -P - 2 • Q by rw [h2Q]; abel, show P - Q - Q = P - 2 • Q by rw [h2Q]; abel]
    ring
  · -- depth one
    have e1 : heckeOp B.q Q (heckeOp B.q Q f) (.ray P (0 + 1)) =
        (B.q : ℂ) * (gapOp B.q f (P + Q + Q) + f (.ray (P + Q - Q) 1)) +
          ((B.q : ℂ) * f (.ray (P - Q + Q) 1) + f (.ray (P - Q - Q) 3)) := rfl
    have e2 : heckeTwo B.q B.trace (2 • Q) w f (.ray P (0 + 1)) =
        (B.q : ℂ) * gapOp B.q f (P + 2 • Q) + f (.ray (P - 2 • Q) 3) := rfl
    rw [e1, e2, thetaOp_ray, show P + Q - Q = P by abel, show P - Q + Q = P by abel,
      show P + Q + Q = P + 2 • Q by rw [h2Q]; abel, show P - Q - Q = P - 2 • Q by rw [h2Q]; abel]
    ring
  · -- deep in the cusp
    have e1 : heckeOp B.q Q (heckeOp B.q Q f) (.ray P (k + 1 + 1)) =
        (B.q : ℂ) * ((B.q : ℂ) * f (.ray (P + Q + Q) k) + f (.ray (P + Q - Q) (k + 2))) +
          ((B.q : ℂ) * f (.ray (P - Q + Q) (k + 2)) + f (.ray (P - Q - Q) (k + 4))) := rfl
    have e2 : heckeTwo B.q B.trace (2 • Q) w f (.ray P (k + 1 + 1)) =
        (B.q : ℂ) ^ 2 * f (.ray (P + 2 • Q) k) + f (.ray (P - 2 • Q) (k + 4)) := rfl
    rw [e1, e2, thetaOp_ray, show P + Q - Q = P by abel, show P - Q + Q = P by abel,
      show P + Q + Q = P + 2 • Q by rw [h2Q]; abel, show P - Q - Q = P - 2 • Q by rw [h2Q]; abel]
    ring

/-! ### Separation by the places of degree two -/

include hG' in
/-- On an odd group, doubling is onto. -/
theorem two_nsmul_surjective : Function.Surjective fun Q : G' => 2 • Q := by
  apply Finite.injective_iff_surjective.mp
  intro P R h
  have h' : 2 • (P - R) = 0 := by
    rw [smul_sub, sub_eq_zero]
    exact h
  exact sub_eq_zero.mp (hG' _ h')

include hG' in
/-- On an odd group, a nontrivial character is not its own inverse. -/
theorem char_mul_self_ne_one {ψ : AddChar G' ℂ} (hψ : ψ ≠ 1) : ψ⁻¹ * ψ⁻¹ ≠ 1 := by
  intro h
  apply hψ
  ext Q
  obtain ⟨R, rfl⟩ := two_nsmul_surjective hG' Q
  have hR := DFunLike.congr_fun h (-R)
  simp only [AddChar.mul_apply, AddChar.inv_apply, neg_neg, AddChar.one_apply] at hR
  have e : ψ (2 • R) = ψ R * ψ R := by
    rw [two_nsmul, AddChar.map_add_eq_mul]
  simp only [e, AddChar.one_apply]
  exact hR

include hG' in
/-- **The places of degree two separate the cusp forms.** If two cusp forms have the same eigenvalue at every place of degree two, they
are the same form: `θ_{ψ⁻¹} = θ_ψ`. All cusp forms have the same eigenvalue `0` under `A`, so this operator is genuinely independent of the
wave operator on this sector. -/
theorem heckeTwo_separates {ψ ψ' : AddChar G' ℂ} (hψ : ψ ≠ 1)
    (hsep : ∀ w, ψ w + ψ (-w) = ψ' w + ψ' (-w)) : ψ' = ψ ∨ ψ' = ψ⁻¹ := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hc1 : ψ' * ψ⁻¹ ≠ 1 := by
    intro h
    exact h1 (by simpa using mul_inv_eq_one.mp h)
  have hc2 : ψ'⁻¹ * ψ⁻¹ ≠ 1 := by
    intro h
    apply h2
    have := mul_eq_one_iff_eq_inv.mp h
    rw [inv_inj] at this
    rw [← this]
  have s1 := sum_addChar_eq_zero hc1
  have s2 := sum_addChar_eq_zero hc2
  have s3 := sum_addChar_eq_zero (char_mul_self_ne_one hG' hψ)
  simp only [AddChar.mul_apply, AddChar.inv_apply] at s1 s2 s3
  have hone (w : G') : ψ w * ψ (-w) = 1 := by
    rw [← AddChar.map_add_eq_mul]
    simp
  have hsum : ∑ w : G', (ψ w + ψ (-w)) * ψ (-w) = ∑ w : G', (ψ' w + ψ' (-w)) * ψ (-w) :=
    Finset.sum_congr rfl fun w _ => by rw [hsep w]
  simp only [add_mul, Finset.sum_add_distrib, hone] at hsum
  rw [s1, s2, s3] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, add_zero] at hsum
  have hcard : (Fintype.card G' : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact hcard hsum

include hG hG' in
/-- The operators of every degree on the cusp forms: `0` at odd degree and `2(-q)^n` at degree `2n`. -/
theorem heckeDeg_thetaField {ψ : AddChar G' ℂ} (hψ : ψ ≠ 1) (Q : G) (n : ℕ)
    (v : Vertex G (DeadLabel G')) :
    heckeDeg B.q Q (2 * n + 1) (thetaField G B.q ψ) v = 0 ∧
      heckeDeg B.q Q (2 * n) (thetaField G B.q ψ) v = 2 * (-(B.q : ℂ)) ^ n * thetaField G B.q ψ v := by
  have hT := heckeOp_thetaField B hG hG' hψ Q
  induction n generalizing v with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [show 2 * 0 + 1 = 1 from rfl, heckeDeg_one]
      exact hT v
    · rw [show 2 * 0 = 0 from rfl, heckeDeg_zero]
      ring
  | succ n ih =>
    have heven : heckeDeg B.q Q (2 * (n + 1)) (thetaField G B.q ψ) v =
        2 * (-(B.q : ℂ)) ^ (n + 1) * thetaField G B.q ψ v := by
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, heckeDeg_add_two, (ih v).2]
      have e : heckeDeg B.q Q (2 * n + 1) (thetaField G B.q ψ) =
          fun u => (0 : ℂ) * thetaField G B.q ψ u := by
        funext u
        rw [(ih u).1]
        ring
      rw [e, heckeOp_smul, pow_succ]
      ring
    refine ⟨?_, heven⟩
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, heckeDeg_add_two, (ih v).1]
    have e : heckeDeg B.q Q (2 * n + 1 + 1) (thetaField G B.q ψ) =
        fun u => (2 * (-(B.q : ℂ)) ^ (n + 1)) * thetaField G B.q ψ u := by
      funext u
      have := heckeDeg_add_two B.q Q (2 * n) (thetaField G B.q ψ) u
      rw [show 2 * n + 1 + 1 = 2 * n + 2 by ring, this, (ih u).2]
      have e2 : heckeDeg B.q Q (2 * n + 1) (thetaField G B.q ψ) =
          fun u => (0 : ℂ) * thetaField G B.q ψ u := by
        funext u
        rw [(ih u).1]
        ring
      rw [e2, heckeOp_smul, pow_succ]
      ring
    rw [e, heckeOp_smul, hT]
    ring

/-! ### Symmetry on compactly supported functions -/

/-- `f` vanishes on the cusps from depth `K` on. -/
def CompactAt {D : Type*} (f : Vertex G D → ℂ) (K : ℕ) : Prop := ∀ P k, K ≤ k → f (.ray P k) = 0

theorem CompactAt.mono {D : Type*} {f : Vertex G D → ℂ} {K K' : ℕ} (h : CompactAt f K) (hK : K ≤ K') :
    CompactAt f K' := fun P k hk => h P k (hK.trans hk)

theorem heckeOp_compact {D : Type*} [Fintype D] (q : ℕ) (Q : G) {f : Vertex G D → ℂ} {K : ℕ}
    (h : CompactAt f K) : CompactAt (heckeOp q Q f) (K + 1) := by
  intro P k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [heckeOp_ray_succ, h _ j (by omega), h _ (j + 2) (by omega)]
  ring

theorem heckeDeg_compact {D : Type*} [Fintype D] (q : ℕ) (Q : G) (d : ℕ) {f : Vertex G D → ℂ} {K : ℕ}
    (h : CompactAt f K) : CompactAt (heckeDeg q Q d f) (K + d) := by
  induction d using Nat.twoStepInduction with
  | zero =>
    intro P k hk
    rw [heckeDeg_zero, h P k (by omega)]
    ring
  | one =>
    intro P k hk
    rw [heckeDeg_one]
    exact heckeOp_compact q Q h P k hk
  | more d h0 h1 =>
    intro P k hk
    rw [heckeDeg_add_two, h0 P k (by omega), heckeOp_compact q Q h1 P k (by omega)]
    ring

/-- **`T_Q` is symmetric on compactly supported functions.** -/
theorem heckeOp_symmetric {D : Type*} [Fintype D] (B : Channels G D) (Q : G) {f : Vertex G D → ℂ}
    (g : Vertex G D → ℂ) {K M : ℕ} (hf : CompactAt f K) (hM : K + 1 ≤ M) :
    truncSum M (fun v => mass B.q v * (heckeOp B.q Q f v * g v - f v * heckeOp B.q Q g v)) = 0 := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  rw [truncSum_heckeGreen]
  refine Finset.sum_eq_zero fun P _ => ?_
  unfold rayFlux
  have a1 : f (transl (-Q) (.ray P (M' + 1))) = 0 := hf _ _ (by omega)
  have a2 : f (transl (-Q) (.ray P M')) = 0 := hf _ _ (by omega)
  simp only [a1, a2]
  ring

/-- **The operators of every degree are symmetric on compactly supported functions.** -/
theorem heckeDeg_symmetric {D : Type*} [Fintype D] (B : Channels G D) (Q : G) (d : ℕ)
    {f : Vertex G D → ℂ} (g : Vertex G D → ℂ) {K M : ℕ} (hf : CompactAt f K) (hM : K + d + 1 ≤ M) :
    truncSum M (fun v => mass B.q v * (heckeDeg B.q Q d f v * g v - f v * heckeDeg B.q Q d g v)) = 0 := by
  induction d using Nat.twoStepInduction generalizing g with
  | zero =>
    have : ∀ v, mass B.q v * (heckeDeg B.q Q 0 f v * g v - f v * heckeDeg B.q Q 0 g v) = 0 := fun v => by
      rw [heckeDeg_zero, heckeDeg_zero]
      ring
    rw [truncSum_congr M this]
    simpa using truncSum_smul M 0 (fun _ : Vertex G D => (0 : ℂ))
  | one =>
    have e : ∀ h : Vertex G D → ℂ, heckeDeg B.q Q 1 h = heckeOp B.q Q h :=
      fun h => funext (heckeDeg_one B.q Q h)
    simp only [e]
    exact heckeOp_symmetric B Q g hf (by omega)
  | more d h0 h1 =>
    have x1 := heckeOp_symmetric B Q g (heckeDeg_compact B.q Q (d + 1) hf)
      (show K + (d + 1) + 1 ≤ M by omega)
    have x2 := h1 (heckeOp B.q Q g) (by omega)
    have x3 := h0 g (by omega)
    have key : ∀ v, mass B.q v * (heckeDeg B.q Q (d + 2) f v * g v - f v * heckeDeg B.q Q (d + 2) g v) =
        mass B.q v * (heckeOp B.q Q (heckeDeg B.q Q (d + 1) f) v * g v -
            heckeDeg B.q Q (d + 1) f v * heckeOp B.q Q g v) +
          (mass B.q v * (heckeDeg B.q Q (d + 1) f v * heckeOp B.q Q g v -
            f v * heckeDeg B.q Q (d + 1) (heckeOp B.q Q g) v) +
          (-(B.q : ℂ)) * (mass B.q v * (heckeDeg B.q Q d f v * g v - f v * heckeDeg B.q Q d g v))) := by
      intro v
      rw [heckeDeg_add_two, heckeDeg_add_two, ← heckeDeg_comm_heckeOp B Q Q (d + 1) g v]
      ring
    rw [truncSum_congr M key, truncSum_add, truncSum_add, truncSum_smul, x1, x2, x3]
    ring

include hG' in
/-- **`Λ_w` is symmetric for the mass**, exactly: it has no boundary term. -/
theorem truncSum_thetaOp_green (hG : ∀ P : G, 2 • P = 0 → P = 0) (w : G')
    (f g : Vertex G (DeadLabel G') → ℂ) (M : ℕ) :
    truncSum M (fun v => mass B.q v * (thetaOp B.q w f v * g v - f v * thetaOp B.q w g v)) = 0 := by
  have hq := B.q_ne_zero
  have hq1 := B.q_sub_one_ne_zero
  have hq2 := B.q_add_one_ne_zero
  set gf := thetaTerm B.q f with hgf
  set gg := thetaTerm B.q g with hgg
  -- the function on the second group
  let H : G' → ℂ := fun Q => thetaDiff B.q f w Q * gg Q - gf Q * thetaDiff B.q g w Q
  have Heven (Q : G') : H (-Q) = H Q := by
    simp only [H, thetaDiff_neg, hgf, hgg, thetaTerm_neg]
  let HB : Branch G' → ℂ := fun x => Quotient.liftOn x H (fun P R h => by
    rcases h with rfl | rfl
    · rfl
    · exact (Heven P).symm)
  have hHsum : ∑ Q : G', H Q = 0 := by
    have r1 : ∑ Q : G', gf (Q + w) * gg Q = ∑ Q : G', gf Q * gg (Q - w) := by
      have := Equiv.sum_comp (Equiv.addRight w) (fun Q : G' => gf Q * gg (Q - w))
      simp only [Equiv.coe_addRight, add_sub_cancel_right] at this
      exact this
    have r2 : ∑ Q : G', gf (Q - w) * gg Q = ∑ Q : G', gf Q * gg (Q + w) := by
      have := Equiv.sum_comp (Equiv.subRight w) (fun Q : G' => gf Q * gg (Q + w))
      simp only [Equiv.subRight_apply, sub_add_cancel] at this
      exact this
    have hexp (Q : G') : H Q = gf (Q + w) * gg Q + gf (Q - w) * gg Q - gf Q * gg (Q + w) -
        gf Q * gg (Q - w) := by
      simp only [H]
      unfold thetaDiff
      ring
    simp only [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib, r1, r2]
    ring
  have hdead : ∑ d : DeadLabel G', HB d.1 = -((1 / 2 : ℂ) * H 0) := by
    have h := sum_deadLabel (G' := G') HB
    have e (P : G') : HB (Branch.mk P) = H P := rfl
    simp only [e] at h
    rw [sum_weighted_odd hG', hHsum] at h
    rw [h]
    ring
  -- the term at a dead end
  have hF (d : DeadLabel G') :
      mass B.q (.dead d : Vertex G (DeadLabel G')) *
          (thetaOp B.q w f (.dead d) * g (.dead d) - f (.dead d) * thetaOp B.q w g (.dead d)) =
        (1 / ((B.q : ℂ) + 1)) * HB d.1 := by
    obtain ⟨x, hx⟩ := d
    induction x using Quotient.inductionOn with
    | h Q =>
      have hx' : Branch.mk Q ≠ Branch.mk 0 := hx
      have e1 : gf Q = f (.dead ⟨Branch.mk Q, hx'⟩) := by
        simp only [hgf]
        unfold thetaTerm deadTerm deadTermB
        rw [dif_neg hx']
        field_simp
      have e2 : gg Q = g (.dead ⟨Branch.mk Q, hx'⟩) := by
        simp only [hgg]
        unfold thetaTerm deadTerm deadTermB
        rw [dif_neg hx']
        field_simp
      change (1 / ((B.q : ℂ) + 1)) * (thetaDiff B.q f w Q * g (.dead ⟨Branch.mk Q, hx'⟩) -
        f (.dead ⟨Branch.mk Q, hx'⟩) * thetaDiff B.q g w Q) = (1 / ((B.q : ℂ) + 1)) * H Q
      simp only [H, e1, e2]
  have hneck : ∑ P : G, branchWeight P * (mass B.q (.neck (Branch.mk P) : Vertex G (DeadLabel G')) *
      (thetaOp B.q w f (.neck (Branch.mk P)) * g (.neck (Branch.mk P)) -
        f (.neck (Branch.mk P)) * thetaOp B.q w g (.neck (Branch.mk P)))) =
      (1 / (B.q : ℂ)) * ((gf w - gf 0) * g (.neck (Branch.mk 0)) -
        f (.neck (Branch.mk 0)) * (gg w - gg 0)) := by
    rw [Finset.sum_eq_single 0]
    · simp only [branchWeight, mass_neck, thetaOp_neck, neckMass, thetaNeck,
        if_pos (by simp : 2 • (0 : G) = 0), one_mul]
      rfl
    · intro b _ hb
      have hb' : ¬ 2 • b = 0 := fun h => hb (hG b h)
      simp only [thetaOp_neck, thetaNeck, if_neg hb']
      ring
    · simp
  have hcap : ∑ P : G, (if h : 2 • P = 0 then mass B.q (.cap ⟨P, h⟩ : Vertex G (DeadLabel G')) *
      (thetaOp B.q w f (.cap ⟨P, h⟩) * g (.cap ⟨P, h⟩) -
        f (.cap ⟨P, h⟩) * thetaOp B.q w g (.cap ⟨P, h⟩)) else 0) =
      (1 / (((B.q : ℂ) ^ 2 - 1) * B.q)) * (-((B.q : ℂ) - 1) * (gf w - gf 0) * g (.cap (capZero G)) -
        f (.cap (capZero G)) * (-((B.q : ℂ) - 1) * (gg w - gg 0))) := by
    rw [Finset.sum_eq_single 0]
    · rw [dif_pos (by simp : 2 • (0 : G) = 0)]
      rfl
    · intro b _ hb
      rw [dif_neg fun h => hb (hG b h)]
    · simp
  have hg0 : gg 0 = (((B.q : ℂ) + 1) * g (.neck (Branch.mk 0)) - g (.cap (capZero G))) / B.q := by
    simp only [hgg]
    unfold thetaTerm
    rw [deadTerm_zero_eq]
  have hf0 : gf 0 = (((B.q : ℂ) + 1) * f (.neck (Branch.mk 0)) - f (.cap (capZero G))) / B.q := by
    simp only [hgf]
    unfold thetaTerm
    rw [deadTerm_zero_eq]
  have hH0 : H 0 = 2 * (gf w - gf 0) * gg 0 - gf 0 * (2 * (gg w - gg 0)) := by
    simp only [H]
    unfold thetaDiff
    simp only [zero_add, zero_sub, thetaTerm_neg]
    ring
  unfold truncSum
  simp only [thetaOp_ray, thetaOp_core, zero_mul, mul_zero, sub_zero, Finset.sum_const_zero, add_zero]
  have hD : ∑ d : DeadLabel G', mass B.q (.dead d : Vertex G (DeadLabel G')) *
      (thetaOp B.q w f (.dead d) * g (.dead d) - f (.dead d) * thetaOp B.q w g (.dead d)) =
      (1 / ((B.q : ℂ) + 1)) * (-((1 / 2 : ℂ) * H 0)) := by
    rw [Finset.sum_congr rfl fun d _ => hF d, ← Finset.mul_sum, hdead]
  rw [hD, hneck, hcap, hH0, hg0, hf0]
  have hsq : (B.q : ℂ) ^ 2 - 1 = ((B.q : ℂ) - 1) * ((B.q : ℂ) + 1) := by ring
  rw [hsq]
  field_simp
  ring

include hG hG' in
/-- **Hecke of degree two is symmetric on compactly supported functions.** -/
theorem heckeTwo_symmetric (Q₀ : G) (w : G') {f : Vertex G (DeadLabel G') → ℂ}
    (g : Vertex G (DeadLabel G') → ℂ) {K M : ℕ} (hf : CompactAt f K) (hM : K + 3 ≤ M) :
    truncSum M (fun v => mass B.q v *
      (heckeTwo B.q B.trace Q₀ w f v * g v - f v * heckeTwo B.q B.trace Q₀ w g v)) = 0 := by
  obtain ⟨Q, rfl⟩ := two_nsmul_surjective hG Q₀
  have key : ∀ v, mass B.q v * (heckeTwo B.q B.trace (2 • Q) w f v * g v -
        f v * heckeTwo B.q B.trace (2 • Q) w g v) =
      mass B.q v * (heckeDeg B.q Q 2 f v * g v - f v * heckeDeg B.q Q 2 g v) +
        (-(B.q : ℂ)) * (mass B.q v * (thetaOp B.q w f v * g v - f v * thetaOp B.q w g v)) := by
    intro v
    rw [heckeTwo_eq B hG hG', heckeTwo_eq B hG hG']
    ring
  rw [truncSum_congr M key, truncSum_add, truncSum_smul, heckeDeg_symmetric B Q 2 g hf (by omega),
    truncSum_thetaOp_green B hG' hG]
  ring

/-! ### The sector inside the algebra -/

/-- `Λ_w` is linear. -/
theorem thetaTerm_sub_smul (g h : Vertex G (DeadLabel G') → ℂ) (a : ℂ) (Q : G') :
    thetaTerm B.q (fun v => g v - a * h v) Q = thetaTerm B.q g Q - a * thetaTerm B.q h Q := by
  unfold thetaTerm
  rw [deadTerm_sub_smul]
  have hq := B.q_ne_zero
  field_simp

theorem thetaOp_sub_smul (w : G') (g h : Vertex G (DeadLabel G') → ℂ) (a : ℂ)
    (v : Vertex G (DeadLabel G')) :
    thetaOp B.q w (fun u => g u - a * h u) v = thetaOp B.q w g v - a * thetaOp B.q w h v := by
  have ht := thetaTerm_sub_smul B g h a
  rcases v with _ | d | x | L | ⟨P, k⟩
  · simp
  · simp only [thetaOp_dead']
    obtain ⟨x, hx⟩ := d
    induction x using Quotient.inductionOn with
    | h Q =>
      change thetaDiff B.q _ w Q = thetaDiff B.q g w Q - a * thetaDiff B.q h w Q
      unfold thetaDiff
      rw [ht, ht, ht]
      ring
  · induction x using Quotient.inductionOn with
    | h P =>
      change thetaNeck B.q _ w P = thetaNeck B.q g w P - a * thetaNeck B.q h w P
      unfold thetaNeck
      split_ifs
      · rw [ht, ht]
        ring
      · ring
  · simp only [thetaOp_cap, ht]
    ring
  · simp

theorem thetaOp_smul (w : G') (a : ℂ) (g : Vertex G (DeadLabel G') → ℂ) (v : Vertex G (DeadLabel G')) :
    thetaOp B.q w (fun u => a * g u) v = a * thetaOp B.q w g v := by
  have h := thetaOp_sub_smul B w (fun _ => (0 : ℂ)) g (-a) v
  have hz : thetaOp B.q w (fun _ => (0 : ℂ)) v = 0 := by
    have h0 := thetaOp_sub_smul B w (fun _ => (0 : ℂ)) (fun _ => (0 : ℂ)) 1 v
    simp only [one_mul, sub_self] at h0
    simpa using h0
  simp only [zero_sub, neg_mul, neg_neg] at h
  rw [h, hz]
  ring

include hG hG' in
/-- `P_{2n}(T_Q) Λ_u = 2(-q)^n Λ_u` and `P_{2n+1}(T_Q) Λ_u = 0`: the image of `Λ_u` lies in the sector of the cusp forms. -/
theorem heckeDeg_thetaOp (Q : G) (u : G') (f : Vertex G (DeadLabel G') → ℂ) (n : ℕ)
    (v : Vertex G (DeadLabel G')) :
    heckeDeg B.q Q (2 * n + 1) (thetaOp B.q u f) v = 0 ∧
      heckeDeg B.q Q (2 * n) (thetaOp B.q u f) v = 2 * (-(B.q : ℂ)) ^ n * thetaOp B.q u f v := by
  have hT := heckeOp_thetaOp B hG hG' Q u f
  induction n generalizing v with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [show 2 * 0 + 1 = 1 from rfl, heckeDeg_one]
      exact hT v
    · rw [show 2 * 0 = 0 from rfl, heckeDeg_zero]
      ring
  | succ n ih =>
    have e2 : heckeDeg B.q Q (2 * n + 1) (thetaOp B.q u f) =
        fun x => (0 : ℂ) * thetaOp B.q u f x := by
      funext x
      rw [(ih x).1]
      ring
    have heven (x : Vertex G (DeadLabel G')) : heckeDeg B.q Q (2 * n + 2) (thetaOp B.q u f) x =
        2 * (-(B.q : ℂ)) ^ (n + 1) * thetaOp B.q u f x := by
      rw [heckeDeg_add_two, (ih x).2, show 2 * n + 1 = 2 * n + 1 from rfl, e2, heckeOp_smul, pow_succ]
      ring
    refine ⟨?_, ?_⟩
    · rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, heckeDeg_add_two, (ih v).1]
      have e3 : heckeDeg B.q Q (2 * n + 1 + 1) (thetaOp B.q u f) =
          fun x => (2 * (-(B.q : ℂ)) ^ (n + 1)) * thetaOp B.q u f x := funext heven
      rw [e3, heckeOp_smul, hT]
      ring
    · rw [show 2 * (n + 1) = 2 * n + 2 by ring]
      exact heven v

/-- `Λ_w P_{2n}(T_Q) = 2(-q)^n Λ_w`, and `Λ_w P_{2n+1}(T_Q) = 0`. -/
theorem thetaOp_heckeDeg (Q : G) (w : G') (f : Vertex G (DeadLabel G') → ℂ) (n : ℕ)
    (v : Vertex G (DeadLabel G')) :
    thetaOp B.q w (heckeDeg B.q Q (2 * n + 1) f) v = 0 ∧
      thetaOp B.q w (heckeDeg B.q Q (2 * n) f) v = 2 * (-(B.q : ℂ)) ^ n * thetaOp B.q w f v := by
  induction n generalizing v with
  | zero =>
    refine ⟨?_, ?_⟩
    · have e : heckeDeg B.q Q (2 * 0 + 1) f = heckeOp B.q Q f := funext (heckeDeg_one B.q Q f)
      rw [e]
      exact thetaOp_heckeOp B Q w f v
    · have e : heckeDeg B.q Q (2 * 0) f = fun x => 2 * f x := funext (heckeDeg_zero B.q Q f)
      rw [e, thetaOp_smul]
      ring
  | succ n ih =>
    have e1 (m : ℕ) : heckeDeg B.q Q (m + 2) f = fun x =>
        heckeOp B.q Q (heckeDeg B.q Q (m + 1) f) x - (B.q : ℂ) * heckeDeg B.q Q m f x :=
      funext (heckeDeg_add_two B.q Q m f)
    refine ⟨?_, ?_⟩
    · rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, e1, thetaOp_sub_smul, thetaOp_heckeOp, (ih v).1]
      ring
    · rw [show 2 * (n + 1) = 2 * n + 2 by ring, e1, thetaOp_sub_smul, thetaOp_heckeOp, (ih v).2, pow_succ]
      ring

end Odd2

end GaloisForLFunctions.ArithmeticScatteringHolography

end
