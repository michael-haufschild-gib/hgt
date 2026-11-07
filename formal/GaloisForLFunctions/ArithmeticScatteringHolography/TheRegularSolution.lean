import GaloisForLFunctions.ArithmeticScatteringHolography.TheEllipticBlackHole

/-!
# The regular solution, the Jost function and the resonances

Write `h = #G` for the number of cusps and `t = q + 1 - h`; `t` is the trace of Frobenius when the graph
comes from a curve. For every `λ` the equation `A e = λ e` has a solution from the core whose values are
polynomials in `λ` (`waveOp_regular`). With `λ = X + Y`, `XY = q`, its value on a ray is

  `(X - Y) e(P, k) = j(Y, X) Y^{k+1} - j(X, Y) X^{k+1}`,  `j(X, Y) = (Y² - 1)(X³ - tX + Y)`

(`regSeq_jost`). So `j` is the Jost function. A nonzero eigenfunction with no incoming part on any ray
exists exactly when `j(X, Y) = 0` (`exists_outgoing_iff`): `Y² = 1`, the two ground states, or
`X⁴ - tX² + q = 0`, the Frobenius polynomial in `a = X²`. Every resonance lies in the radial sector, and
its position depends on the graph only through `(q, t)`. Unitarity places no further condition on `t`.
-/

open Finset

noncomputable section

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.ArithmeticScatteringHolography

variable {G D : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] [Fintype D]

/-- The trace `t = q + 1 - h`. -/
def Channels.trace (B : Channels G D) : ℂ := (B.q : ℂ) + 1 - cuspCount G

theorem Channels.cuspCount_eq (B : Channels G D) : cuspCount G = (B.q : ℂ) + 1 - B.trace := by
  unfold Channels.trace
  ring

/-- The regular solution on a ray: `regSeq n` is the value at depth `n - 1`, and `regSeq 0` is the value
at a neck of a non-two-torsion point. -/
def regSeq (q t lam : ℂ) : ℕ → ℂ
  | 0 => 2 * lam ^ 2 - (q + 1) * (q + 1 + t)
  | 1 => lam * (lam ^ 2 - q ^ 2 - q - t)
  | n + 2 => lam * regSeq q t lam (n + 1) - q * regSeq q t lam n

theorem regSeq_add_two (q t lam : ℂ) (n : ℕ) :
    regSeq q t lam (n + 2) = lam * regSeq q t lam (n + 1) - q * regSeq q t lam n := rfl

/-- The Jost function `j(X, Y) = (Y² - 1)(X³ - tX + Y)`. -/
def jost (t X Y : ℂ) : ℂ := (Y ^ 2 - 1) * (X ^ 3 - t * X + Y)

/-- **The Jost decomposition** of the regular solution, with `λ = X + Y`, `q = XY`. -/
theorem regSeq_jost (t X Y : ℂ) (n : ℕ) :
    (X - Y) * regSeq (X * Y) t (X + Y) n = Y ^ n * jost t Y X - X ^ n * jost t X Y := by
  induction n using Nat.twoStepInduction with
  | zero =>
    simp only [regSeq, jost, pow_zero, one_mul]
    ring
  | one =>
    simp only [regSeq, jost, pow_one]
    ring
  | more n h0 h1 =>
    rw [regSeq_add_two]
    have e : (X - Y) * ((X + Y) * regSeq (X * Y) t (X + Y) (n + 1) -
        X * Y * regSeq (X * Y) t (X + Y) n) =
        (X + Y) * ((X - Y) * regSeq (X * Y) t (X + Y) (n + 1)) -
          X * Y * ((X - Y) * regSeq (X * Y) t (X + Y) n) := by ring
    rw [e, h0, h1]
    ring

/-- The value of the regular solution at the neck of `P`: a pin value at a two-torsion point. -/
def neckValue (q t lam : ℂ) (P : G) : ℂ :=
  if 2 • P = 0 then lam ^ 2 - t * (q + 1) else regSeq q t lam 0

theorem neckValue_neg (q t lam : ℂ) (P : G) : neckValue q t lam (-P) = neckValue q t lam P := by
  simp only [neckValue, two_nsmul_neg_eq_zero_iff]

/-- A **radial** function: its value depends only on the kind of vertex. -/
structure RadialData where
  core : ℂ
  dead : ℂ
  neck : ℂ
  pin : ℂ
  cap : ℂ
  ray : ℕ → ℂ

/-- The function on the graph of a radial datum. -/
def RadialData.toFun (R : RadialData) : Vertex G D → ℂ
  | .core => R.core
  | .dead _ => R.dead
  | .neck x => Quotient.liftOn x (fun P => if 2 • P = 0 then R.pin else R.neck) (fun P Q h => by
      rcases h with rfl | rfl
      · rfl
      · simp only [two_nsmul_neg_eq_zero_iff])
  | .cap _ => R.cap
  | .ray _ k => R.ray k

@[simp] theorem RadialData.toFun_core (R : RadialData) : R.toFun (.core : Vertex G D) = R.core := rfl
@[simp] theorem RadialData.toFun_dead (R : RadialData) (d : D) :
    R.toFun (.dead d : Vertex G D) = R.dead := rfl
@[simp] theorem RadialData.toFun_neck (R : RadialData) (P : G) :
    R.toFun (.neck (Branch.mk P) : Vertex G D) = if 2 • P = 0 then R.pin else R.neck := rfl
@[simp] theorem RadialData.toFun_cap (R : RadialData) (L : TwoTorsion G) :
    R.toFun (.cap L : Vertex G D) = R.cap := rfl
@[simp] theorem RadialData.toFun_ray (R : RadialData) (P : G) (k : ℕ) :
    R.toFun (.ray P k : Vertex G D) = R.ray k := rfl

/-- The wave operator on radial data, read at the core. -/
theorem waveOp_toFun_core (q : ℕ) (R : RadialData) :
    waveOp q (R.toFun : Vertex G D → ℂ) .core =
      (Fintype.card D : ℂ) * R.dead + torsionCount G * R.pin +
        (cuspCount G - torsionCount G) * (R.neck / 2) := by
  rw [waveOp_core]
  simp only [RadialData.toFun_dead, RadialData.toFun_neck, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, branchWeight]
  have e : ∀ P : G, (if 2 • P = 0 then (1 : ℂ) else 1 / 2) * (if 2 • P = 0 then R.pin else R.neck) =
      if 2 • P = 0 then R.pin else R.neck / 2 := by
    intro P
    split_ifs <;> ring
  simp only [e]
  rw [sum_ite_torsion]
  ring

/-- The regular solution as radial data. -/
def regularData (q t h lam : ℂ) : RadialData where
  core := h * lam
  dead := (q + 1) * h
  neck := regSeq q t lam 0
  pin := lam ^ 2 - t * (q + 1)
  cap := (q + 1) * (lam ^ 2 - q ^ 2 - q - t)
  ray k := regSeq q t lam (k + 1)

/-- The regular solution of `A e = λ e`. -/
def Channels.regular (B : Channels G D) (lam : ℂ) : Vertex G D → ℂ :=
  (regularData (B.q : ℂ) B.trace (cuspCount G) lam).toFun

/-- **The regular solution.** `A e = λ e` everywhere on the graph, for every `λ`. -/
theorem Channels.waveOp_regular (B : Channels G D) (lam : ℂ) (v : Vertex G D) :
    waveOp B.q (B.regular lam) v = lam * B.regular lam v := by
  have hh := B.cuspCount_eq
  have hcount := B.count_complex
  unfold Channels.regular
  rcases v with _ | d | x | L | ⟨P, _ | k⟩
  · rw [waveOp_toFun_core]
    simp only [regularData, RadialData.toFun_core, regSeq]
    linear_combination (((B.q : ℂ) + 1) * cuspCount G / 2) * hcount -
      (((B.q : ℂ) + 1) * (cuspCount G + torsionCount G) / 2) * hh
  · simp only [waveOp_dead, RadialData.toFun_core, RadialData.toFun_dead, regularData]
    ring
  · induction x using Quotient.inductionOn with
    | h P =>
      change waveOp B.q _ (.neck (Branch.mk P)) = _ * RadialData.toFun _ (.neck (Branch.mk P))
      rw [waveOp_neck]
      unfold neckOp
      simp only [RadialData.toFun_core, RadialData.toFun_ray, RadialData.toFun_neck, regularData,
        zero_add]
      split_ifs
      · simp only [regSeq]
        linear_combination ((B.q : ℂ) * lam) * hh
      · simp only [regSeq]
        linear_combination (((B.q : ℂ) - 1) * lam) * hh
  · simp only [waveOp_cap, RadialData.toFun_cap, RadialData.toFun_ray, regularData, regSeq]
    ring
  · rw [waveOp_ray_zero]
    unfold gapOp
    simp only [RadialData.toFun_neck, RadialData.toFun_ray, regularData, zero_add]
    split_ifs
    · simp only [RadialData.toFun_cap, regSeq]
      ring
    · simp only [regSeq]
      ring
  · rw [waveOp_ray_succ]
    simp only [RadialData.toFun_ray, regularData]
    rw [show k + 2 + 1 = k + 1 + 2 by ring, regSeq_add_two (B.q : ℂ) B.trace lam (k + 1)]
    ring

/-- The number of cusps is nonzero: `G` has a neutral element. -/
theorem cuspCount_ne_zero : cuspCount G ≠ 0 := by
  unfold cuspCount
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/-! ### Outgoing solutions and resonances -/

/-- An eigenfunction at `λ = X + Y` with **no incoming part**: on every ray it is `c_P Y^k`. -/
structure IsOutgoing (q : ℕ) (X Y : ℂ) (f : Vertex G D → ℂ) (c : G → ℂ) : Prop where
  eigen : ∀ v, waveOp q f v = (X + Y) * f v
  ray : ∀ P k, f (.ray P k) = c P * Y ^ k

/-- At an outgoing solution the core value is `(X - Y) c_P / ((q-1) Y)` at every cusp `P`. The relation
comes from the neck, or from the pin and the cap at a two-torsion point. -/
theorem IsOutgoing.core_relation (B : Channels G D) {X Y : ℂ} (hXY : X * Y = B.q)
    {f : Vertex G D → ℂ} {c : G → ℂ} (hf : IsOutgoing B.q X Y f c) (P : G) :
    ((B.q : ℂ) - 1) * f .core * Y = c P * (X - Y) := by
  have hq0 := B.q_ne_zero
  have hX : X ≠ 0 := by
    intro h
    rw [h, zero_mul] at hXY
    exact hq0 hXY.symm
  have hr0 := hf.eigen (.ray P 0)
  rw [waveOp_ray_zero, hf.ray P 1, hf.ray P 0] at hr0
  simp only [pow_zero, pow_one, mul_one] at hr0
  have hn := hf.eigen (.neck (Branch.mk P))
  rw [waveOp_neck] at hn
  unfold neckOp at hn
  unfold gapOp at hr0
  by_cases htors : 2 • P = 0
  · rw [dif_pos htors] at hr0
    rw [if_pos htors, hf.ray P 0] at hn
    simp only [pow_zero, mul_one] at hn
    have hcap := hf.eigen (.cap ⟨P, htors⟩)
    rw [waveOp_cap, hf.ray P 0] at hcap
    simp only [pow_zero, mul_one] at hcap
    rw [← hXY] at hr0 hn hcap ⊢
    apply mul_left_cancel₀ hX
    linear_combination (X * Y - 1) * hn + hcap + (X + Y) * hr0
  · rw [dif_neg htors] at hr0
    rw [if_neg htors, hf.ray P 0, hf.ray (-P) 0] at hn
    simp only [pow_zero, mul_one] at hn
    have hneg : c (-P) = c P := by
      have hr0' := hf.eigen (.ray (-P) 0)
      rw [waveOp_ray_zero, hf.ray (-P) 1, hf.ray (-P) 0] at hr0'
      simp only [pow_zero, pow_one, mul_one] at hr0'
      unfold gapOp at hr0'
      rw [dif_neg (by rwa [two_nsmul_neg_eq_zero_iff]), Branch.mk_neg] at hr0'
      apply mul_left_cancel₀ hX
      linear_combination hr0 - hr0'
    rw [hneg] at hn
    rw [← hXY] at hr0 hn ⊢
    have hfn' : f (.neck (Branch.mk P)) * Y = c P := by
      apply mul_left_cancel₀ hX
      linear_combination hr0
    linear_combination Y * hn + (X + Y) * hfn'

/-- An outgoing solution with zero amplitude on every ray vanishes: the graph has no compactly supported
eigenfunction away from `λ = 0`. -/
theorem IsOutgoing.eq_zero_of_amplitude (B : Channels G D) {X Y : ℂ} (hXY : X * Y = B.q)
    (hlam : X + Y ≠ 0) {f : Vertex G D → ℂ} {c : G → ℂ} (hf : IsOutgoing B.q X Y f c)
    (hc : ∀ P, c P = 0) : f = 0 := by
  have hq0 := B.q_ne_zero
  have hq1 := B.q_sub_one_ne_zero
  have hY : Y ≠ 0 := by
    intro h
    rw [h, mul_zero] at hXY
    exact hq0 hXY.symm
  have hφ : f .core = 0 := by
    have := hf.core_relation B hXY 0
    rw [hc, zero_mul] at this
    have h3 : ((B.q : ℂ) - 1) * Y * f .core = 0 := by linear_combination this
    exact (mul_eq_zero.mp h3).resolve_left (mul_ne_zero hq1 hY)
  have hrayz : ∀ P k, f (.ray P k) = 0 := fun P k => by rw [hf.ray, hc, zero_mul]
  funext v
  rcases v with _ | d | x | L | ⟨P, k⟩
  · exact hφ
  · have := hf.eigen (.dead d)
    rw [waveOp_dead, hφ, mul_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hlam
  · induction x using Quotient.inductionOn with
    | h P =>
      change f (.neck (Branch.mk P)) = 0
      have hn := hf.eigen (.neck (Branch.mk P))
      rw [waveOp_neck] at hn
      unfold neckOp at hn
      simp only [hφ, hrayz, mul_zero, add_zero, ite_self] at hn
      exact (mul_eq_zero.mp hn.symm).resolve_left hlam
  · have hc' := hf.eigen (.cap L)
    rw [waveOp_cap, hrayz, mul_zero] at hc'
    exact (mul_eq_zero.mp hc'.symm).resolve_left hlam
  · exact hrayz P k

/-- The Jost function in terms of the core equation: with `q = XY`,
`j(X, Y) = (Y - X)(λ² - q(q+1) - t) + (q-1) Y (q + 1 - t)`. -/
theorem jost_eq_core (t X Y : ℂ) :
    jost t X Y = (Y - X) * ((X + Y) ^ 2 - X * Y * (X * Y + 1) - t) +
      (X * Y - 1) * Y * (X * Y + 1 - t) := by
  unfold jost
  ring

/-- **Classification of resonances.** Away from `λ = 0` and `X = Y`, a nonzero outgoing eigenfunction
exists exactly at the zeros of the Jost function. All of them are radial. -/
theorem exists_outgoing_iff (B : Channels G D) {X Y : ℂ} (hXY : X * Y = B.q) (hne : X ≠ Y)
    (hlam : X + Y ≠ 0) :
    (∃ (f : Vertex G D → ℂ) (c : G → ℂ), f ≠ 0 ∧ IsOutgoing B.q X Y f c) ↔ jost B.trace X Y = 0 := by
  have hq0 := B.q_ne_zero
  have hq1 := B.q_sub_one_ne_zero
  have hq2 := B.q_add_one_ne_zero
  have hY : Y ≠ 0 := by
    intro h
    rw [h, mul_zero] at hXY
    exact hq0 hXY.symm
  have hXYsub : X - Y ≠ 0 := sub_ne_zero.mpr hne
  constructor
  · rintro ⟨f, c, hf0, hf⟩
    have hrel := fun P => hf.core_relation B hXY P
    have hconst : ∀ P, c P = c 0 := fun P =>
      mul_right_cancel₀ hXYsub ((hrel P).symm.trans (hrel 0))
    have hdead : ∀ d, (X + Y) * f (.dead d) = ((B.q : ℂ) + 1) * f .core := fun d => by
      have := hf.eigen (.dead d)
      rw [waveOp_dead] at this
      exact this.symm
    have hneck : ∀ P : G, (X + Y) * (branchWeight P * f (.neck (Branch.mk P))) =
        if 2 • P = 0 then (B.q : ℂ) * f .core + c 0
        else (((B.q : ℂ) - 1) * f .core + 2 * c 0) / 2 := by
      intro P
      have hn := hf.eigen (.neck (Branch.mk P))
      rw [waveOp_neck] at hn
      unfold neckOp at hn
      unfold branchWeight
      split_ifs with htors
      · rw [if_pos htors, hf.ray P 0, hconst P] at hn
        simp only [pow_zero, mul_one] at hn
        linear_combination -hn
      · rw [if_neg htors, hf.ray P 0, hf.ray (-P) 0, hconst P, hconst (-P)] at hn
        simp only [pow_zero, mul_one] at hn
        linear_combination (-1 / 2 : ℂ) * hn
    have hcore := hf.eigen .core
    rw [waveOp_core] at hcore
    have e1 : (X + Y) * ∑ d, f (.dead d) =
        (Fintype.card D : ℂ) * (((B.q : ℂ) + 1) * f .core) := by
      rw [Finset.mul_sum, Finset.sum_congr rfl fun d _ => hdead d]
      simp
    have e2 : (X + Y) * ∑ P, branchWeight P * f (.neck (Branch.mk P)) =
        torsionCount G * ((B.q : ℂ) * f .core + c 0) +
          (cuspCount G - torsionCount G) * ((((B.q : ℂ) - 1) * f .core + 2 * c 0) / 2) := by
      rw [Finset.mul_sum, Finset.sum_congr rfl fun P _ => hneck P, sum_ite_torsion]
    have hcount := B.count_complex
    have hh := B.cuspCount_eq
    -- the core equation: `(λ² - q(q+1) - t) φ = h c`
    have hΩ : ((X + Y) ^ 2 - (B.q : ℂ) * ((B.q : ℂ) + 1) - B.trace) * f .core =
        ((B.q : ℂ) + 1 - B.trace) * c 0 := by
      rw [← hh]
      linear_combination -(X + Y) * hcore + e1 + e2 +
        (f .core * ((B.q : ℂ) + 1) / 2) * hcount - f .core * hh
    have hrel0 := hrel 0
    have hjost : c 0 * jost B.trace X Y = 0 := by
      rw [jost_eq_core]
      rw [← hXY] at hΩ hrel0
      linear_combination ((X + Y) ^ 2 - X * Y * (X * Y + 1) - B.trace) * hrel0 -
        (X * Y - 1) * Y * hΩ
    rcases mul_eq_zero.mp hjost with h0 | hj
    · exfalso
      exact hf0 (hf.eq_zero_of_amplitude B hXY hlam fun P => by rw [hconst P, h0])
    · exact hj
  · intro hj
    refine ⟨B.regular (X + Y), fun _ => (Y * jost B.trace Y X) / (X - Y), ?_, ?_, ?_⟩
    · intro h
      have h0 := congrFun h .core
      simp only [Channels.regular, regularData, RadialData.toFun_core, Pi.zero_apply] at h0
      exact (mul_ne_zero cuspCount_ne_zero hlam) h0
    · exact fun v => B.waveOp_regular (X + Y) v
    · intro P k
      simp only [Channels.regular, RadialData.toFun_ray, regularData]
      have hjd := regSeq_jost B.trace X Y (k + 1)
      rw [hj, hXY] at hjd
      field_simp
      linear_combination hjd

/-- A zero of the Jost function with `X ≠ 0`: either a ground state, `Y² = 1`, or a root of the
Frobenius polynomial in `a = X²`. -/
theorem jost_eq_zero_iff {t X Y : ℂ} {q : ℂ} (hXY : X * Y = q) (hX : X ≠ 0) :
    jost t X Y = 0 ↔ Y ^ 2 = 1 ∨ (X ^ 2) ^ 2 - t * X ^ 2 + q = 0 := by
  unfold jost
  rw [mul_eq_zero, sub_eq_zero]
  refine or_congr Iff.rfl ?_
  have e : (X ^ 2) ^ 2 - t * X ^ 2 + q = X * (X ^ 3 - t * X + Y) := by
    rw [← hXY]
    ring
  rw [e, mul_eq_zero]
  simp [hX]

end GaloisForLFunctions.ArithmeticScatteringHolography

end
