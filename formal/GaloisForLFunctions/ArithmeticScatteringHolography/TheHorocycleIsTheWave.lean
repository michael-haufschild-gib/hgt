import GaloisForLFunctions.ArithmeticScatteringHolography.TheKreinFluxLaw
import GaloisForLFunctions.ArithmeticScatteringHolography.HeckeAtASecondPlace

/-!
# The horocycle is the wave

On a `(q+1)`-regular tree with a horofunction `b`, each vertex has one neighbour one level up and `q`
neighbours one level down. So the indicators of the horospheres satisfy

  `A 1_{b = τ} = 1_{b = τ + 1} + q 1_{b = τ - 1}`

(`horosphere_isWave`), which is the discrete wave equation, with depth as time. Hence **horocycle
renormalization is the wave equation**: pushing a long horocycle one level is one tick of the wave, and
a pulse coming in from a cusp is the push-forward of the horospheres. This is the Eisenstein series in the
time domain, and the echo train is the image sum over geodesics from the cusp back to it.

The rate of equidistribution of a long horocycle is therefore a ringdown rate. Take the pulse at the core at
time `2m`: it grows as a constant times `q^{2m}`, the volume term. With the ground mode removed, the rest has size
`O((m+1) q^{m/2})` exactly under universal damping (`horocycle_rate_iff`). Relative to the volume, at height
`y = q^{-τ}`, `τ = 2m`, this is `y^{3/4}`. So the graph form of Zagier's theorem holds: **equidistribution of
long horocycles at rate `y^{3/4}` is universal damping**, and `3/4 = 1/2 + 1/4` is the volume exponent plus the
universal rate.

The pulse at the core also reads the trace directly: its first return is `q² + q + t`
(`Channels.waveOp_waveOp_deltaCore`).
-/

open Finset

noncomputable section

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.ArithmeticScatteringHolography

/-! ### Horospheres on a tree -/

/-- A horofunction on a graph with neighbour sets: one neighbour one level up, `q` one level down, and no
others. This is the Busemann function of an end of the `(q+1)`-regular tree. -/
structure Horofunction (V : Type*) [DecidableEq V] (nbrs : V → Finset V) (q : ℕ) where
  level : V → ℤ
  step : ∀ v, ∀ w ∈ nbrs v, level w = level v + 1 ∨ level w = level v - 1
  up : ∀ v, ((nbrs v).filter fun w => level w = level v - 1).card = 1
  down : ∀ v, ((nbrs v).filter fun w => level w = level v + 1).card = q

variable {V : Type*} [DecidableEq V] {nbrs : V → Finset V} {q : ℕ}

/-- The indicator of the horosphere at level `τ`. -/
def Horofunction.sphere (b : Horofunction V nbrs q) (τ : ℤ) (v : V) : ℂ :=
  if b.level v = τ then 1 else 0

/-- **Horocycle renormalization is the discrete wave equation.** -/
theorem horosphere_isWave (b : Horofunction V nbrs q) (τ : ℤ) (v : V) :
    b.sphere (τ + 1) v + (q : ℂ) * b.sphere (τ - 1) v = ∑ w ∈ nbrs v, b.sphere τ w := by
  have hcount : ∑ w ∈ nbrs v, b.sphere τ w = (((nbrs v).filter fun w => b.level w = τ).card : ℂ) := by
    simp only [Horofunction.sphere]
    rw [Finset.sum_boole]
  rw [hcount]
  unfold Horofunction.sphere
  by_cases h1 : b.level v = τ + 1
  · have hne : ¬ b.level v = τ - 1 := by omega
    rw [if_pos h1, if_neg hne]
    have e : ((nbrs v).filter fun w => b.level w = τ) =
        (nbrs v).filter fun w => b.level w = b.level v - 1 := by
      refine Finset.filter_congr fun w _ => ?_
      rw [h1]
      constructor <;> intro h <;> omega
    rw [e, b.up]
    simp
  · by_cases h2 : b.level v = τ - 1
    · rw [if_neg h1, if_pos h2]
      have e : ((nbrs v).filter fun w => b.level w = τ) =
          (nbrs v).filter fun w => b.level w = b.level v + 1 := by
        refine Finset.filter_congr fun w _ => ?_
        rw [h2]
        constructor <;> intro h <;> omega
      rw [e, b.down]
      simp
    · rw [if_neg h1, if_neg h2]
      have e : ((nbrs v).filter fun w => b.level w = τ) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro w hw hlevel
        rcases b.step v w hw with h | h <;> omega
      rw [e]
      simp

/-! ### The horocycle at the core -/

/-- The core value of the pulse in double ticks, without the factor `h`: the mass of a long horocycle at the
core. -/
def horoCore (q t : ℂ) (m : ℕ) : ℂ := coreTime q t (2 * (m : ℤ) + (-2)) - q ^ 2 * coreTime q t (2 * (m : ℤ) + (-6))

/-- The horocycle with the ground mode (the volume term) removed. -/
def horoSignal (q t : ℂ) (m : ℕ) : ℂ := horoCore q t (m + 3) - q ^ 2 * horoCore q t (m + 2)

/-- The horocycle mass at double tick `m + 1`. -/
theorem horoCore_succ (q t : ℂ) (m : ℕ) :
    horoCore q t (m + 1) = coreSeq q t m - q ^ 2 * coreZ q t ((m : ℤ) + (-2)) := by
  unfold horoCore
  have e1 : 2 * ((m + 1 : ℕ) : ℤ) + (-2) = 2 * (m : ℤ) := by push_cast; ring
  have e2 : 2 * ((m + 1 : ℕ) : ℤ) + (-6) = 2 * ((m : ℤ) + (-2)) := by push_cast; ring
  rw [e1, e2, coreTime_two_mul, coreTime_two_mul, coreZ_natCast]

/-- **The horocycle through the ground-mode probe is a Lucas combination**:
`l_{m+2} - q² l_m = t l_{m+1} - q(1+q) l_m`. -/
theorem horoSignal_eq (q t : ℂ) (m : ℕ) :
    horoSignal q t m = t * lucas q t (m + 1) - q * (1 + q) * lucas q t m := by
  unfold horoSignal
  rw [show m + 3 = (m + 2) + 1 from rfl, horoCore_succ, show m + 2 = (m + 1) + 1 from rfl, horoCore_succ]
  have e1 : ((m + 1 + 1 : ℕ) : ℤ) + (-2) = ((m : ℕ) : ℤ) := by push_cast; ring
  rw [e1, coreZ_natCast]
  have h3 := coreSeq_sub_ground q t (m + 1)
  have hl := lucas_add_two q t m
  have h3' : coreSeq q t (m + 2) - q ^ 2 * coreSeq q t (m + 1) = lucas q t (m + 2) := h3
  have hlow : coreSeq q t m - q ^ 2 * coreZ q t (((m + 1 : ℕ) : ℤ) + (-2)) = lucas q t m := by
    rcases m with _ | k
    · have : ((0 + 1 : ℕ) : ℤ) + (-2) = -1 := by norm_num
      rw [this, coreZ_of_neg q t (by norm_num)]
      simp [coreSeq, lucas]
    · have : ((k + 1 + 1 : ℕ) : ℤ) + (-2) = ((k : ℕ) : ℤ) := by push_cast; ring
      rw [this, coreZ_natCast]
      exact coreSeq_sub_ground q t k
  have goal : coreSeq q t (m + 1 + 1) - q ^ 2 * coreSeq q t m -
      q ^ 2 * (coreSeq q t (m + 1) - q ^ 2 * coreZ q t (((m + 1 : ℕ) : ℤ) + (-2))) =
      lucas q t (m + 2) - q ^ 2 * lucas q t m := by
    linear_combination h3' - q ^ 2 * hlow
  rw [goal, hl]
  ring

/-- **Zagier's theorem on the graph.** Long horocycles equidistribute at the universal rate exactly when no
mode is slower than universal. In the variable `y = q^{-2m}`, the bound below is `y^{3/4}` relative to the volume
term `q^{2m}`. The excitation of the slow mode is `a² - q²`, nonzero as long as `|t| ≠ q + 1`. -/
theorem horocycle_rate_iff {q t : ℝ} (hq : 0 < q) (hedge : |t| ≠ q + 1) :
    (∃ C : ℝ, ∀ n : ℕ, ‖horoSignal (q : ℂ) (t : ℂ) n‖ ≤ C * (n + 1) * Real.sqrt q ^ n) ↔
      t ^ 2 ≤ 4 * q := by
  have h := lucasMix_rate_iff (q := q) (t := t) (A := t) (B := -(q * (1 + q))) hq (by
    intro x hx hzero
    apply hedge
    have hsq : x ^ 2 = q ^ 2 := by nlinarith
    have hq' : t * x = x ^ 2 + q := by linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hxe | hxe
    · rw [hxe] at hq'
      have : t = q + 1 := by
        have : q * (t - (q + 1)) = 0 := by nlinarith
        have := (mul_eq_zero.mp this).resolve_left hq.ne'
        linarith
      rw [this, abs_of_pos (by linarith)]
    · rw [hxe] at hq'
      have : t = -(q + 1) := by
        have : q * (t + (q + 1)) = 0 := by nlinarith
        have := (mul_eq_zero.mp this).resolve_left hq.ne'
        linarith
      rw [this, abs_neg, abs_of_pos (by linarith)])
  rw [← h]
  refine exists_congr fun C => forall_congr' fun n => ?_
  rw [horoSignal_eq]
  have e : (t : ℂ) * lucas (q : ℂ) (t : ℂ) (n + 1) - (q : ℂ) * (1 + q) * lucas (q : ℂ) (t : ℂ) n =
      (t : ℂ) * lucas (q : ℂ) (t : ℂ) (n + 1) + ((-(q * (1 + q)) : ℝ) : ℂ) * lucas (q : ℂ) (t : ℂ) n := by
    push_cast
    ring
  rw [e]

/-! ### The first return reads the trace -/

variable {G D : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] [Fintype D]

/-- The unit impulse at the core. -/
def deltaCore : Vertex G D → ℂ
  | .core => 1
  | _ => 0

/-- **The first return reads the trace.** A unit impulse at the core comes back after two ticks with amplitude
`q² + q + t`, on every black hole. So the first return is a difference of channel counts, up to the volume
term. -/
theorem Channels.waveOp_waveOp_deltaCore (B : Channels G D) :
    waveOp B.q (waveOp B.q (deltaCore : Vertex G D → ℂ)) .core =
      (B.q : ℂ) ^ 2 + (B.q : ℂ) + B.trace := by
  have hh := B.cuspCount_eq
  have hcount := B.count_complex
  have hneck (P : G) : waveOp B.q (deltaCore : Vertex G D → ℂ) (.neck (Branch.mk P)) =
      if 2 • P = 0 then (B.q : ℂ) else (B.q : ℂ) - 1 := by
    rw [waveOp_neck]
    unfold neckOp
    simp only [deltaCore]
    split_ifs <;> ring
  have hdead (d : D) : waveOp B.q (deltaCore : Vertex G D → ℂ) (.dead d) = (B.q : ℂ) + 1 := by
    rw [waveOp_dead]
    simp [deltaCore]
  rw [waveOp_core]
  simp only [hdead, hneck, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, branchWeight]
  have e : ∀ P : G, (if 2 • P = 0 then (1 : ℂ) else 1 / 2) *
      (if 2 • P = 0 then (B.q : ℂ) else (B.q : ℂ) - 1) =
      if 2 • P = 0 then (B.q : ℂ) else ((B.q : ℂ) - 1) / 2 := by
    intro P
    split_ifs <;> ring
  simp only [e]
  rw [sum_ite_torsion]
  linear_combination ((B.q : ℂ) + 1) / 2 * hcount - hh

end GaloisForLFunctions.ArithmeticScatteringHolography

end
