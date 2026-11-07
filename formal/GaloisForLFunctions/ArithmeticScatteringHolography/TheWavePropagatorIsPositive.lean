import GaloisForLFunctions.ArithmeticScatteringHolography.HeckeAtAPlaceOfDegreeTwo
import GaloisForLFunctions.ArithmeticScatteringHolography.ThePropagatorCoefficients

/-!
# The wave propagator is a positive operator

`P_d(A)`, with `P_d(X + Y) = X^d + Y^d`, is the solution at time `d` of the wave equation. On the tree it has negative entries. On a
black hole with odd groups `G`, `G'` and `q ≥ 7`, **every entry of `P_d(A)` is nonnegative for every `d ≥ 3`**, including on the fakes
(`chebOp_nonneg`). At `d = 2` the entries on the dead ends are `1 - q`, and this is what `heckeTwo` corrects.

The mechanism has three steps.

* The whole wave is read from one sequence at the core. On a ray the wave is d'Alembert plus a reflected echo
  (`chebOp_ray_succ`, `echoPart_succ`), and that echo, the necks, the pins and the dead ends are geometric sums over the core sequence
  (`gap_formula`, `deadTerm_odd`, `deadTerm_even`).
* The core sequence satisfies a closed recursion (`core_even`, `core_odd`), solved by the power series
  `1/((1 - q² z)(1 - t z + q z²))` (`even_closed`, `odd_closed`). Its pole at the constant function dominates for every `|t| ≤ q`, so the
  position of the resonances does not affect the sign.
* The only negative contributions are `(-q)^{d/2}` on the sector of the cusp forms, and they are smaller than the coefficients of
  the core sequence as soon as `d ≥ 3` (`ThePropagatorCoefficients`).

So the operators `P_d(T_Q)` at all degrees form a commuting family of positive operators on the fakes
(`universal_damping_not_forced_at_every_degree`), each acting on a resonance by `X^d + Y^d`. **Positivity of Hecke at all degrees
does not exclude the fakes.**
-/

open Finset
open scoped ComplexOrder

noncomputable section

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.ArithmeticScatteringHolography

variable {G G' : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] [AddCommGroup G'] [DecidableEq G']
  [Fintype G']

local notation "Vt" => Vertex G (DeadLabel G')

/-! ### Linearity of the boundary terms -/

theorem gapOp_sub_smul (q : ℕ) (g h : Vt → ℂ) (a : ℂ) (R : G) :
    gapOp q (fun v => g v - a * h v) R = gapOp q g R - a * gapOp q h R := by
  unfold gapOp
  split_ifs <;> ring

theorem deadTerm_sub_smul (q : ℕ) (g h : Vt → ℂ) (a : ℂ) (Q : G') :
    deadTerm q (fun v => g v - a * h v) Q = deadTerm q g Q - a * deadTerm q h Q := by
  unfold deadTerm deadTermB
  split_ifs <;> ring

theorem gapOp_chebOp_zero (q : ℕ) (f : Vt → ℂ) (R : G) : gapOp q (chebOp q 0 f) R = 2 * gapOp q f R := by
  show gapOp q (fun v => 2 * f v) R = _
  unfold gapOp
  split_ifs <;> ring

theorem deadTerm_chebOp_zero (q : ℕ) (f : Vt → ℂ) (Q : G') :
    deadTerm q (chebOp q 0 f) Q = 2 * deadTerm q f Q := by
  show deadTerm q (fun v => 2 * f v) Q = _
  unfold deadTerm deadTermB
  split_ifs <;> ring

/-! ### The sequence at the core -/

/-- The wave at the core at time `d`, with half the initial value at time zero. -/
def coreT (q : ℕ) (f : Vt → ℂ) : ℕ → ℂ
  | 0 => f .core
  | d + 1 => chebOp q (d + 1) f .core

/-- The geometric sum `c_d + q c_{d-2} + q² c_{d-4} + ...`: it feeds the necks. -/
def coreW (q : ℕ) (f : Vt → ℂ) : ℕ → ℂ
  | 0 => f .core
  | 1 => waveOp q f .core
  | d + 2 => coreT q f (d + 2) + (q : ℂ) * coreW q f d

/-- The alternating sum `c_d - q c_{d-2} + q² c_{d-4} - ...`: it feeds the dead ends. -/
def coreV (q : ℕ) (f : Vt → ℂ) : ℕ → ℂ
  | 0 => f .core
  | 1 => waveOp q f .core
  | d + 2 => coreT q f (d + 2) - (q : ℂ) * coreV q f d

/-! ### The rays -/

/-- **d'Alembert on a ray.** -/
theorem chebOp_ray_succ (q d : ℕ) (f : Vt → ℂ) (R : G) (k : ℕ) :
    chebOp q (d + 1) f (.ray R (k + 1)) =
      (q : ℂ) * chebOp q d f (.ray R k) + f (.ray R (k + d + 2)) - (q : ℂ) * f (.ray R (k + d)) := by
  induction d generalizing k with
  | zero =>
    simp only [chebOp, waveOp_ray_succ, add_zero]
    ring
  | succ d ih =>
    rw [chebOp_add_two, waveOp_ray_succ, ih (k + 1)]
    rw [show k + 1 + d + 2 = k + (d + 1) + 2 by ring, show k + 1 + d = k + (d + 1) by ring]
    ring

/-- The part of the wave on a ray that has met the core or is coming down. -/
def echoPart (q : ℕ) (f : Vt → ℂ) (R : G) (d k : ℕ) : ℂ :=
  chebOp q d f (.ray R k) - f (.ray R (k + d))

theorem echoPart_succ (q d : ℕ) (f : Vt → ℂ) (R : G) (k : ℕ) :
    echoPart q f R (d + 1) (k + 1) = (q : ℂ) * echoPart q f R d k := by
  unfold echoPart
  rw [chebOp_ray_succ, show k + 1 + (d + 1) = k + d + 2 by ring]
  ring

theorem echoPart_zero (q : ℕ) (f : Vt → ℂ) (R : G) (k : ℕ) : echoPart q f R 0 k = f (.ray R k) := by
  unfold echoPart
  simp only [chebOp, add_zero]
  ring

/-! ### The necks -/

variable (B : Channels G (DeadLabel G')) (f : Vertex G (DeadLabel G') → ℂ)

theorem gap_rec (d : ℕ) (R : G) :
    gapOp B.q (chebOp B.q (d + 2) f) R =
      (B.q : ℂ) * (((B.q : ℂ) - 1) * chebOp B.q (d + 1) f .core) +
        (B.q : ℂ) * chebOp B.q (d + 1) f (.ray R 0) + (B.q : ℂ) * chebOp B.q (d + 1) f (.ray (-R) 0) -
        (B.q : ℂ) * gapOp B.q (chebOp B.q d f) R := by
  have e : chebOp B.q (d + 2) f =
      fun v => waveOp B.q (chebOp B.q (d + 1) f) v - (B.q : ℂ) * chebOp B.q d f v := rfl
  rw [e, gapOp_sub_smul]
  have hg := gapOp_waveOp B (chebOp B.q (d + 1) f) R
  have e2 : gapOp B.q (waveOp B.q (chebOp B.q (d + 1) f)) R =
      gapOp B.q (fun v => waveOp B.q (chebOp B.q (d + 1) f) v) R := rfl
  rw [← e2, hg]

theorem root_of_gap {d : ℕ} {R : G}
    (hg : gapOp B.q (chebOp B.q (d + 1) f) R =
      (B.q : ℂ) * (f (.ray R d) + f (.ray (-R) d) + ((B.q : ℂ) - 1) * coreW B.q f d)) :
    chebOp B.q (d + 2) f (.ray R 0) =
      f (.ray R (d + 2)) + (B.q : ℂ) * f (.ray (-R) d) +
        (B.q : ℂ) * ((B.q : ℂ) - 1) * coreW B.q f d := by
  rw [chebOp_add_two, waveOp_ray_zero, hg]
  have h := chebOp_ray_succ B.q d f R 0
  rw [show (0 : ℕ) + 1 = 1 from rfl, show 0 + d + 2 = d + 2 by ring, show 0 + d = d by ring] at h
  rw [h]
  ring

/-- **The necks read the geometric sum.** -/
theorem gap_formula (d : ℕ) (R : G) :
    gapOp B.q (chebOp B.q (d + 1) f) R =
      (B.q : ℂ) * (f (.ray R d) + f (.ray (-R) d) + ((B.q : ℂ) - 1) * coreW B.q f d) := by
  induction d using Nat.twoStepInduction generalizing R with
  | zero =>
    have h := gapOp_waveOp B f R
    show gapOp B.q (waveOp B.q f) R = _
    rw [h]
    show _ = (B.q : ℂ) * (f (.ray R 0) + f (.ray (-R) 0) + ((B.q : ℂ) - 1) * f .core)
    ring
  | one =>
    rw [show 1 + 1 = 0 + 2 from rfl, gap_rec, gapOp_chebOp_zero]
    have e1 (S : G) : chebOp B.q (0 + 1) f (.ray S 0) = gapOp B.q f S + f (.ray S 1) := rfl
    rw [e1, e1, gapOp_neg]
    show _ = (B.q : ℂ) * (f (.ray R 1) + f (.ray (-R) 1) + ((B.q : ℂ) - 1) * waveOp B.q f .core)
    have e2 : chebOp B.q (0 + 1) f .core = waveOp B.q f .core := rfl
    rw [e2]
    ring
  | more d h0 h1 =>
    rw [show d + 2 + 1 = (d + 1) + 2 by ring, gap_rec]
    have hR := root_of_gap B f (h0 R)
    have hR' := root_of_gap B f (h0 (-R))
    rw [neg_neg] at hR'
    rw [show d + 1 + 1 = d + 2 by ring, hR, hR', h0 R]
    have e : coreW B.q f (d + 2) = chebOp B.q (d + 2) f .core + (B.q : ℂ) * coreW B.q f d := rfl
    rw [e]
    ring

/-- The wave at the root of a ray. -/
theorem root_formula (d : ℕ) (R : G) :
    chebOp B.q (d + 2) f (.ray R 0) =
      f (.ray R (d + 2)) + (B.q : ℂ) * f (.ray (-R) d) +
        (B.q : ℂ) * ((B.q : ℂ) - 1) * coreW B.q f d :=
  root_of_gap B f (gap_formula B f d R)

/-! ### The dead ends -/

theorem deadTerm_rec (d : ℕ) (Q : G') :
    deadTerm B.q (chebOp B.q (d + 2) f) Q =
      (B.q : ℂ) * (((B.q : ℂ) + 1) * chebOp B.q (d + 1) f .core) -
        (B.q : ℂ) * deadTerm B.q (chebOp B.q d f) Q := by
  have e : chebOp B.q (d + 2) f =
      fun v => waveOp B.q (chebOp B.q (d + 1) f) v - (B.q : ℂ) * chebOp B.q d f v := rfl
  rw [e, deadTerm_sub_smul]
  have h := deadTerm_waveOp B (chebOp B.q (d + 1) f) Q
  have e2 : deadTerm B.q (waveOp B.q (chebOp B.q (d + 1) f)) Q =
      deadTerm B.q (fun v => waveOp B.q (chebOp B.q (d + 1) f) v) Q := rfl
  rw [← e2, h]

/-- At odd time the dead term carries no memory of the dead end. -/
theorem deadTerm_odd (n : ℕ) (Q : G') :
    deadTerm B.q (chebOp B.q (2 * n + 1) f) Q = (B.q : ℂ) * (((B.q : ℂ) + 1) * coreV B.q f (2 * n)) := by
  induction n with
  | zero => exact deadTerm_waveOp B f Q
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, deadTerm_rec, ih]
    have e : coreV B.q f (2 * (n + 1)) = chebOp B.q (2 * n + 1 + 1) f .core - (B.q : ℂ) * coreV B.q f (2 * n) :=
      rfl
    rw [e]
    ring

/-- At even time the dead term remembers the dead end, with the weight `(-q)^{d/2}` of the cusp forms. -/
theorem deadTerm_even (n : ℕ) (Q : G') :
    deadTerm B.q (chebOp B.q (2 * n + 2) f) Q =
      (B.q : ℂ) * (((B.q : ℂ) + 1) * coreV B.q f (2 * n + 1)) +
        2 * (-(B.q : ℂ)) ^ (n + 1) * deadTerm B.q f Q := by
  induction n with
  | zero =>
    rw [show 2 * 0 + 2 = 0 + 2 from rfl, deadTerm_rec, deadTerm_chebOp_zero]
    show (B.q : ℂ) * (((B.q : ℂ) + 1) * waveOp B.q f .core) - _ =
      (B.q : ℂ) * (((B.q : ℂ) + 1) * waveOp B.q f .core) + _
    ring
  | succ n ih =>
    rw [show 2 * (n + 1) + 2 = (2 * n + 2) + 2 by ring, deadTerm_rec, ih]
    have e : coreV B.q f (2 * (n + 1) + 1) =
        chebOp B.q (2 * n + 2 + 1) f .core - (B.q : ℂ) * coreV B.q f (2 * n + 1) := rfl
    rw [e, pow_succ (-(B.q : ℂ)) (n + 1)]
    ring

/-! ### The core equation -/

/-- The sum of the necks, with the combination of the pin and the cap at zero. -/
def sOne (q : ℕ) (f : Vertex G (DeadLabel G') → ℂ) : ℂ := (∑ P, gapOp q f P) / q

/-- The sum of the dead ends over `G'`, with the combination of the pin and the cap at zero. -/
def sTwo (q : ℕ) (f : Vertex G (DeadLabel G') → ℂ) : ℂ := (∑ Q, deadTerm q f Q) / q

/-- The sum over the cusps at one depth. -/
def aS (f : Vertex G (DeadLabel G') → ℂ) (k : ℕ) : ℂ := ∑ P, f (.ray P k)

section OddGroups

variable (hG : ∀ P : G, 2 • P = 0 → P = 0) (hG' : ∀ Q : G', 2 • Q = 0 → Q = 0)

include hG hG' in
/-- The wave operator at the core is read from the boundary terms. -/
theorem two_q_waveOp_core (g : Vertex G (DeadLabel G') → ℂ) :
    2 * (B.q : ℂ) * waveOp B.q g .core = ∑ Q, deadTerm B.q g Q + ∑ P, gapOp B.q g P := by
  rw [sum_deadTerm B.q g hG', sum_gapOp hG B g, waveOp_core]
  ring

include hG hG' in
theorem waveOp_core_eq_half : waveOp B.q f .core = (sOne B.q f + sTwo B.q f) / 2 := by
  have h := two_q_waveOp_core B hG hG' f
  have hq := B.q_ne_zero
  unfold sOne sTwo
  field_simp
  linear_combination h

include hG hG' in
/-- The second group has `q + 1 + t` points. -/
theorem card_second_eq : (Fintype.card G' : ℂ) = (B.q : ℂ) + 1 + B.trace := by
  have h1 : Fintype.card (TwoTorsion G) = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨⟨0, by simp⟩, fun y => Subtype.ext (hG y.1 y.2)⟩
  have h2 := two_card_deadLabel hG'
  have h3 := B.count
  rw [h1] at h3
  have h4 : (Fintype.card G' : ℂ) + Fintype.card G = 2 * ((B.q : ℂ) + 1) := by
    have : Fintype.card G' + Fintype.card G = 2 * (B.q + 1) := by omega
    exact_mod_cast this
  unfold Channels.trace cuspCount
  linear_combination h4

theorem card_first_eq : (Fintype.card G : ℂ) = (B.q : ℂ) + 1 - B.trace := B.cuspCount_eq

/-- The weight of the dead ends in the core equation. -/
def kOne (B : Channels G (DeadLabel G')) : ℝ := kappaOne (B.q : ℝ) B.traceR
/-- The weight of the necks in the core equation. -/
def kTwo (B : Channels G (DeadLabel G')) : ℝ := kappaTwo (B.q : ℝ) B.traceR

include hG hG' in
theorem kOne_eq : (Fintype.card G' : ℂ) * ((B.q : ℂ) + 1) / 2 = (kOne B : ℂ) := by
  rw [card_second_eq B hG hG', B.trace_eq_ofReal]
  simp only [kOne, kappaOne]
  push_cast
  ring

theorem kTwo_eq : (Fintype.card G : ℂ) * ((B.q : ℂ) - 1) / 2 = (kTwo B : ℂ) := by
  rw [card_first_eq B, B.trace_eq_ofReal]
  simp only [kTwo, kappaTwo]
  push_cast
  ring

/-- The sum of the gap terms of the wave at time `d + 1`. -/
theorem sum_gap_formula (d : ℕ) :
    ∑ P, gapOp B.q (chebOp B.q (d + 1) f) P =
      (B.q : ℂ) * (2 * aS f d + (Fintype.card G : ℂ) * (((B.q : ℂ) - 1) * coreW B.q f d)) := by
  simp only [gap_formula, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  have e : ∑ P : G, f (.ray (-P) d) = aS f d := Equiv.sum_comp (Equiv.neg G) (fun P => f (.ray P d))
  rw [e]
  have e' : ∑ P : G, f (.ray P d) = aS f d := rfl
  rw [e']
  ring

include hG hG' in
/-- **The core equation at even time.** -/
theorem core_even (n : ℕ) :
    waveOp B.q (chebOp B.q (2 * n + 1) f) .core =
      (kOne B : ℂ) * coreV B.q f (2 * n) + aS f (2 * n) + (kTwo B : ℂ) * coreW B.q f (2 * n) := by
  have h := two_q_waveOp_core B hG hG' (chebOp B.q (2 * n + 1) f)
  rw [sum_gap_formula] at h
  simp only [deadTerm_odd, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  rw [← kOne_eq B hG hG', ← kTwo_eq B]
  have hq := B.q_ne_zero
  apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hq)
  rw [h]
  ring

include hG hG' in
/-- **The core equation at odd time**, with the source of the cusp forms. -/
theorem core_odd (n : ℕ) :
    waveOp B.q (chebOp B.q (2 * n + 2) f) .core =
      (kOne B : ℂ) * coreV B.q f (2 * n + 1) + aS f (2 * n + 1) +
        (kTwo B : ℂ) * coreW B.q f (2 * n + 1) + (-(B.q : ℂ)) ^ (n + 1) * sTwo B.q f := by
  have h := two_q_waveOp_core B hG hG' (chebOp B.q (2 * n + 2) f)
  rw [show 2 * n + 2 = 2 * n + 1 + 1 by ring, sum_gap_formula] at h
  rw [show 2 * n + 1 + 1 = 2 * n + 2 by ring] at h
  simp only [deadTerm_even, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum] at h
  rw [← kOne_eq B hG hG', ← kTwo_eq B]
  have hq := B.q_ne_zero
  apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hq)
  rw [h]
  unfold sTwo
  field_simp
  ring

end OddGroups

/-! ### Convolutions -/

/-- The convolution of a real sequence with a source. -/
def convC (x : ℕ → ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ := ∑ k ∈ range n, (x (n - 1 - k) : ℂ) * a k

@[simp] theorem convC_zero (x : ℕ → ℝ) (a : ℕ → ℂ) : convC x a 0 = 0 := by simp [convC]

theorem convC_succ (x : ℕ → ℝ) (a : ℕ → ℂ) (n : ℕ) :
    convC x a (n + 1) = (x 0 : ℂ) * a n + convC (fun j => x (j + 1)) a n := by
  unfold convC
  rw [Finset.sum_range_succ, add_comm]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [show n + 1 - 1 - k = n - 1 - k + 1 by omega]

/-- A linear relation between sequences passes to the convolutions. -/
theorem convC_linear {x y z w : ℕ → ℝ} {A B' C : ℝ} (h : ∀ j, x j = A * y j + B' * z j + C * w j)
    (a : ℕ → ℂ) (n : ℕ) :
    convC x a n = (A : ℂ) * convC y a n + (B' : ℂ) * convC z a n + (C : ℂ) * convC w a n := by
  unfold convC
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h]
  push_cast
  ring

theorem convC_step {x y : ℕ → ℝ} {c : ℝ} (h0 : x 0 = y 0) (h : ∀ j, x (j + 1) = y (j + 1) + c * x j)
    (a : ℕ → ℂ) (n : ℕ) :
    convC x a (n + 1) = convC y a (n + 1) + (c : ℂ) * convC x a n := by
  rw [convC_succ, convC_succ, h0]
  have e : convC (fun j => x (j + 1)) a n = convC (fun j => y (j + 1)) a n + (c : ℂ) * convC x a n := by
    have := convC_linear (x := fun j => x (j + 1)) (y := fun j => y (j + 1)) (z := x)
      (w := fun _ => 0) (A := 1) (B' := c) (C := 0) (fun j => by simp [h j]) a n
    simpa using this
  rw [e]
  ring

theorem convC_nonneg {x : ℕ → ℝ} (hx : ∀ j, 0 ≤ x j) {a : ℕ → ℂ} (ha : ∀ k, 0 ≤ a k) (n : ℕ) :
    0 ≤ convC x a n :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Complex.zero_le_real.mpr (hx _)) (ha _)

/-! ### The closed forms -/

section ClosedForms

variable (hG : ∀ P : G, 2 • P = 0 → P = 0) (hG' : ∀ Q : G', 2 • Q = 0 → Q = 0)

local notation "qr" => (B.q : ℝ)
local notation "tr" => B.traceR

include hG hG' in
/-- **The closed form at even time.** The coefficient of the core is `φ`, those of the cusps are `ρ`. -/
theorem even_closed (n : ℕ) :
    coreT B.q f (2 * n) = (phiS qr tr n : ℂ) * f .core + convC (rhoS qr tr) (fun k => aS f (2 * k)) n ∧
      coreW B.q f (2 * n) =
        (rhoS qr tr n : ℂ) * f .core + convC (sigmaS qr tr) (fun k => aS f (2 * k)) n ∧
      coreV B.q f (2 * n) =
        (gammaS qr tr n : ℂ) * f .core + convC (etaS qr tr) (fun k => aS f (2 * k)) n := by
  have hstepT : ∀ m, coreT B.q f (2 * (m + 1)) =
      (phiS qr tr (m + 1) : ℂ) * f .core + convC (rhoS qr tr) (fun k => aS f (2 * k)) (m + 1) →
      coreW B.q f (2 * m) =
        (rhoS qr tr m : ℂ) * f .core + convC (sigmaS qr tr) (fun k => aS f (2 * k)) m →
      coreV B.q f (2 * m) =
        (gammaS qr tr m : ℂ) * f .core + convC (etaS qr tr) (fun k => aS f (2 * k)) m →
      coreW B.q f (2 * (m + 1)) =
          (rhoS qr tr (m + 1) : ℂ) * f .core +
            convC (sigmaS qr tr) (fun k => aS f (2 * k)) (m + 1) ∧
        coreV B.q f (2 * (m + 1)) =
          (gammaS qr tr (m + 1) : ℂ) * f .core +
            convC (etaS qr tr) (fun k => aS f (2 * k)) (m + 1) := by
    intro m hT hW hV
    have eW : coreW B.q f (2 * (m + 1)) = coreT B.q f (2 * (m + 1)) + (B.q : ℂ) * coreW B.q f (2 * m) := rfl
    have eV : coreV B.q f (2 * (m + 1)) = coreT B.q f (2 * (m + 1)) - (B.q : ℂ) * coreV B.q f (2 * m) := rfl
    have r1 : ((rhoS qr tr (m + 1) : ℝ) : ℂ) = (phiS qr tr (m + 1) : ℂ) + (B.q : ℂ) * (rhoS qr tr m : ℂ) := by
      have := rhoS_succ qr tr m
      rw [this]
      push_cast
      ring
    have r2 : ((gammaS qr tr (m + 1) : ℝ) : ℂ) =
        (phiS qr tr (m + 1) : ℂ) - (B.q : ℂ) * (gammaS qr tr m : ℂ) := by
      have := gammaS_succ qr tr m
      rw [this]
      push_cast
      ring
    have c1 := convC_step (x := sigmaS qr tr) (y := rhoS qr tr) (c := qr) (by simp)
      (fun j => sigmaS_succ qr tr j) (fun k => aS f (2 * k)) m
    have c2 := convC_step (x := etaS qr tr) (y := rhoS qr tr) (c := -qr) (by simp)
      (fun j => by rw [etaS_succ]; ring) (fun k => aS f (2 * k)) m
    push_cast at c1 c2
    constructor
    · rw [eW, hT, hW, c1, r1]
      ring
    · rw [eV, hT, hV, c2, r2]
      ring
  induction n with
  | zero => simp [coreT, coreW, coreV]
  | succ n ih =>
    obtain ⟨hT, hW, hV⟩ := ih
    have hcore := core_even B f hG hG' n
    have hT' : coreT B.q f (2 * (n + 1)) =
        (phiS qr tr (n + 1) : ℂ) * f .core +
          convC (rhoS qr tr) (fun k => aS f (2 * k)) (n + 1) := by
      have e1 : coreT B.q f (2 * (n + 1)) = chebOp B.q (2 * n + 2) f .core := rfl
      rw [e1, chebOp_add_two, hcore, hW, hV, convC_succ]
      have c1 := convC_linear (x := fun j => rhoS qr tr (j + 1)) (y := rhoS qr tr) (z := etaS qr tr)
        (w := sigmaS qr tr) (A := -qr) (B' := kOne B) (C := kTwo B)
        (fun j => by
          have := rhoS_rec qr tr j
          simp only [kOne, kTwo]
          linarith) (fun k => aS f (2 * k)) n
      rw [c1]
      push_cast
      cases n with
      | zero =>
        have hphi := phiS_one qr tr
        have hphiC : ((phiS qr tr 1 : ℝ) : ℂ) = (kOne B : ℂ) + (kTwo B : ℂ) - 2 * (B.q : ℂ) := by
          rw [hphi]
          simp only [kOne, kTwo]
          push_cast
          ring
        have e0 : chebOp B.q (2 * 0) f .core = 2 * f .core := rfl
        rw [e0, show (0 : ℕ) + 1 = 1 from rfl, hphiC]
        simp
        unfold aS
        ring
      | succ m =>
        have e0 : chebOp B.q (2 * (m + 1)) f .core = coreT B.q f (2 * (m + 1)) := rfl
        rw [e0, hT]
        have hphi := phiS_rec qr tr m
        have hphiC : ((phiS qr tr (m + 1 + 1) : ℝ) : ℂ) =
            (kOne B : ℂ) * (gammaS qr tr (m + 1) : ℂ) + (kTwo B : ℂ) * (rhoS qr tr (m + 1) : ℂ) -
              (B.q : ℂ) * (phiS qr tr (m + 1) : ℂ) := by
          have h2 : phiS qr tr (m + 1 + 1) = kappaOne qr tr * gammaS qr tr (m + 1) +
              kappaTwo qr tr * rhoS qr tr (m + 1) - qr * phiS qr tr (m + 1) := by
            rw [show m + 1 + 1 = m + 2 by ring]
            linarith
          rw [h2]
          simp only [kOne, kTwo]
          push_cast
          ring
        rw [hphiC]
        simp
        ring
    obtain ⟨hW', hV'⟩ := hstepT n hT' hW hV
    exact ⟨hT', hW', hV'⟩

include hG hG' in
/-- **The closed form at odd time.** The coefficients of the two sums over the groups are different, and the source
`(-q)^{n+1}` of the cusp forms enters only through the second one. -/
theorem odd_closed (n : ℕ) :
    coreT B.q f (2 * n + 1) =
        (1 / 2 : ℂ) * (rhoS qr tr n : ℂ) * sOne B.q f + (1 / 2 : ℂ) * (gammaS qr tr n : ℂ) * sTwo B.q f +
          convC (rhoS qr tr) (fun k => aS f (2 * k + 1)) n ∧
      coreW B.q f (2 * n + 1) =
        (1 / 2 : ℂ) * (sigmaS qr tr n : ℂ) * sOne B.q f + (1 / 2 : ℂ) * (etaS qr tr n : ℂ) * sTwo B.q f +
          convC (sigmaS qr tr) (fun k => aS f (2 * k + 1)) n ∧
      coreV B.q f (2 * n + 1) =
        (1 / 2 : ℂ) * (etaS qr tr n : ℂ) * sOne B.q f + (1 / 2 : ℂ) * (gpS qr tr n : ℂ) * sTwo B.q f +
          convC (etaS qr tr) (fun k => aS f (2 * k + 1)) n := by
  have hS := waveOp_core_eq_half B f hG hG'
  induction n with
  | zero =>
    have e1 : coreT B.q f (2 * 0 + 1) = waveOp B.q f .core := rfl
    have e2 : coreW B.q f (2 * 0 + 1) = waveOp B.q f .core := rfl
    have e3 : coreV B.q f (2 * 0 + 1) = waveOp B.q f .core := rfl
    rw [e1, e2, e3, hS]
    simp
    ring
  | succ n ih =>
    obtain ⟨hT, hW, hV⟩ := ih
    have hcore := core_odd B f hG hG' n
    have hrho : ((rhoS qr tr (n + 1) : ℝ) : ℂ) =
        (kOne B : ℂ) * (etaS qr tr n : ℂ) + (kTwo B : ℂ) * (sigmaS qr tr n : ℂ) -
          (B.q : ℂ) * (rhoS qr tr n : ℂ) := by
      have h2 : rhoS qr tr (n + 1) = kappaOne qr tr * etaS qr tr n + kappaTwo qr tr * sigmaS qr tr n -
          qr * rhoS qr tr n := by
        linarith [rhoS_rec qr tr n]
      rw [h2]
      simp only [kOne, kTwo]
      push_cast
      ring
    have hgam : ((gammaS qr tr (n + 1) : ℝ) : ℂ) =
        (kOne B : ℂ) * (gpS qr tr n : ℂ) + (kTwo B : ℂ) * (etaS qr tr n : ℂ) +
          2 * (-(B.q : ℂ)) ^ (n + 1) - (B.q : ℂ) * (gammaS qr tr n : ℂ) := by
      have h2 : gammaS qr tr (n + 1) = kappaOne qr tr * gpS qr tr n + kappaTwo qr tr * etaS qr tr n +
          2 * (-qr) ^ (n + 1) - qr * gammaS qr tr n := by
        linarith [gammaS_rec qr tr n]
      rw [h2]
      simp only [kOne, kTwo]
      push_cast
      ring
    have hT' : coreT B.q f (2 * (n + 1) + 1) =
        (1 / 2 : ℂ) * (rhoS qr tr (n + 1) : ℂ) * sOne B.q f +
          (1 / 2 : ℂ) * (gammaS qr tr (n + 1) : ℂ) * sTwo B.q f +
          convC (rhoS qr tr) (fun k => aS f (2 * k + 1)) (n + 1) := by
      have e1 : coreT B.q f (2 * (n + 1) + 1) = chebOp B.q (2 * n + 1 + 2) f .core := rfl
      rw [e1, chebOp_add_two, show 2 * n + 1 + 1 = 2 * n + 2 by ring, hcore, hW, hV, convC_succ]
      have c1 := convC_linear (x := fun j => rhoS qr tr (j + 1)) (y := rhoS qr tr) (z := etaS qr tr)
        (w := sigmaS qr tr) (A := -qr) (B' := kOne B) (C := kTwo B)
        (fun j => by
          have := rhoS_rec qr tr j
          simp only [kOne, kTwo]
          linarith) (fun k => aS f (2 * k + 1)) n
      have e0 : chebOp B.q (2 * n + 1) f .core = coreT B.q f (2 * n + 1) := rfl
      rw [c1, e0, hT, hrho, hgam]
      push_cast
      simp
      ring
    have eW : coreW B.q f (2 * (n + 1) + 1) =
        coreT B.q f (2 * (n + 1) + 1) + (B.q : ℂ) * coreW B.q f (2 * n + 1) := rfl
    have eV : coreV B.q f (2 * (n + 1) + 1) =
        coreT B.q f (2 * (n + 1) + 1) - (B.q : ℂ) * coreV B.q f (2 * n + 1) := rfl
    have c1 := convC_step (x := sigmaS qr tr) (y := rhoS qr tr) (c := qr) (by simp)
      (fun j => sigmaS_succ qr tr j) (fun k => aS f (2 * k + 1)) n
    have c2 := convC_step (x := etaS qr tr) (y := rhoS qr tr) (c := -qr) (by simp)
      (fun j => by rw [etaS_succ]; ring) (fun k => aS f (2 * k + 1)) n
    push_cast at c1 c2
    have rs : ((sigmaS qr tr (n + 1) : ℝ) : ℂ) = (rhoS qr tr (n + 1) : ℂ) + (B.q : ℂ) * (sigmaS qr tr n : ℂ) := by
      rw [sigmaS_succ]
      push_cast
      ring
    have re : ((etaS qr tr (n + 1) : ℝ) : ℂ) = (gammaS qr tr (n + 1) : ℂ) + (B.q : ℂ) * (etaS qr tr n : ℂ) := by
      rw [etaS_succ']
      push_cast
      ring
    have re2 : ((etaS qr tr (n + 1) : ℝ) : ℂ) = (rhoS qr tr (n + 1) : ℂ) - (B.q : ℂ) * (etaS qr tr n : ℂ) := by
      rw [etaS_succ]
      push_cast
      ring
    have rg : ((gpS qr tr (n + 1) : ℝ) : ℂ) = (gammaS qr tr (n + 1) : ℂ) - (B.q : ℂ) * (gpS qr tr n : ℂ) := by
      rw [gpS_succ]
      push_cast
      ring
    refine ⟨hT', ?_, ?_⟩
    · rw [eW, hT', hW, c1, rs, re]
      ring
    · rw [eV, hT', hV, c2, re2, rg]
      ring

end ClosedForms

/-! ### The rows of the propagator -/

/-- The row of a neck off the two-torsion. -/
theorem neck_row {P : G} (hP : ¬ 2 • P = 0) (d : ℕ) :
    chebOp B.q (d + 1) f (.neck (Branch.mk P)) =
      f (.ray P d) + f (.ray (-P) d) + ((B.q : ℂ) - 1) * coreW B.q f d := by
  have h := gap_formula B f d P
  unfold gapOp at h
  rw [dif_neg hP] at h
  exact mul_left_cancel₀ B.q_ne_zero h

theorem gapOp_zero_eq (q : ℕ) (g : Vertex G (DeadLabel G') → ℂ) :
    gapOp q g 0 = ((q : ℂ) - 1) * g (.neck (Branch.mk 0)) + g (.cap (capZero G)) := by
  unfold gapOp
  rw [dif_pos (by simp : 2 • (0 : G) = 0)]
  rfl

theorem deadTerm_zero_eq (q : ℕ) (g : Vertex G (DeadLabel G') → ℂ) :
    deadTerm q g (0 : G') = ((q : ℂ) + 1) * g (.neck (Branch.mk 0)) - g (.cap (capZero G)) := by
  unfold deadTerm deadTermB
  rw [dif_pos rfl]

/-- The pin is read from the two boundary terms at zero. -/
theorem pin_of_terms (q : ℕ) (hq : (q : ℂ) ≠ 0) (g : Vertex G (DeadLabel G') → ℂ) :
    g (.neck (Branch.mk 0)) = (gapOp q g 0 + deadTerm q g (0 : G')) / (2 * (q : ℂ)) := by
  rw [gapOp_zero_eq, deadTerm_zero_eq]
  field_simp
  ring

/-- The cap is read from the pin and the dead term at zero. -/
theorem cap_of_terms (q : ℕ) (g : Vertex G (DeadLabel G') → ℂ) :
    g (.cap (capZero G)) = ((q : ℂ) + 1) * g (.neck (Branch.mk 0)) - deadTerm q g (0 : G') := by
  rw [deadTerm_zero_eq]
  ring

/-- The row of a dead end at odd time. -/
theorem dead_row_odd (n : ℕ) {Q : G'} (h : Branch.mk Q ≠ Branch.mk 0) :
    chebOp B.q (2 * n + 1) f (.dead ⟨Branch.mk Q, h⟩) = ((B.q : ℂ) + 1) * coreV B.q f (2 * n) := by
  have e := deadTerm_odd B f n Q
  unfold deadTerm deadTermB at e
  rw [dif_neg h] at e
  exact mul_left_cancel₀ B.q_ne_zero e

/-- The row of a dead end at even time. -/
theorem dead_row_even (n : ℕ) {Q : G'} (h : Branch.mk Q ≠ Branch.mk 0) :
    chebOp B.q (2 * n + 2) f (.dead ⟨Branch.mk Q, h⟩) =
      ((B.q : ℂ) + 1) * coreV B.q f (2 * n + 1) +
        2 * (-(B.q : ℂ)) ^ (n + 1) * f (.dead ⟨Branch.mk Q, h⟩) := by
  have e := deadTerm_even B f n Q
  unfold deadTerm deadTermB at e
  rw [dif_neg h, dif_neg h] at e
  apply mul_left_cancel₀ B.q_ne_zero
  rw [e]
  ring

/-! ### Positivity -/

section Positivity

variable (hG : ∀ P : G, 2 • P = 0 → P = 0) (hG' : ∀ Q : G', 2 • Q = 0 → Q = 0)
  (hq : 7 ≤ B.q) {f} (hf : ∀ v, 0 ≤ f v)

local notation "qr" => (B.q : ℝ)
local notation "tr" => B.traceR

theorem ofReal_nonneg' {x : ℝ} (hx : 0 ≤ x) : (0 : ℂ) ≤ (x : ℂ) := Complex.zero_le_real.mpr hx

theorem half_nonneg_C : (0 : ℂ) ≤ 1 / 2 := by
  have h := ofReal_nonneg' (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rwa [show ((1 / 2 : ℝ) : ℂ) = 1 / 2 by push_cast; ring] at h

include hf in
theorem aS_nonneg (k : ℕ) : 0 ≤ aS f k := Finset.sum_nonneg fun _ _ => hf _

include hG hG' hq hf in
/-- **Reading the two sums.** A combination `α s₁ + β s₂ + (β₀ - β) g(0)`, with `s₁, s₂` the sums over the two groups and `g(0)` the
combination of the pin and the cap, is nonnegative as soon as `α, β ≥ 0`, `β₀ ≤ α` and `α(q-1) + β₀(q+1) ≥ 0`: those are its coefficients
on the cap and on the pin. An extra term `2e` at one dead end only asks `β + e ≥ 0`. -/
theorem pair_nonneg {α β β₀ e : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hB : β₀ ≤ α)
    (hA : 0 ≤ α * (qr - 1) + β₀ * (qr + 1)) (he : 0 ≤ β + e) (d₀ : DeadLabel G') :
    0 ≤ (α : ℂ) * sOne B.q f + (β : ℂ) * sTwo B.q f + ((β₀ - β : ℝ) : ℂ) * (deadTerm B.q f (0 : G') / B.q) +
      2 * (e : ℂ) * f (.dead d₀) := by
  have hq0 := B.q_ne_zero
  have hqr : (0 : ℝ) < qr := by
    have : (7 : ℝ) ≤ qr := by exact_mod_cast hq
    linarith
  have hgap : ∑ P : G, gapOp B.q f P =
      gapOp B.q f 0 + (B.q : ℂ) * ∑ P ∈ univ.erase (0 : G), f (.neck (Branch.mk P)) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : G)), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun P hP => ?_
    have hP0 : ¬ 2 • P = 0 := fun h => (Finset.mem_erase.mp hP).1 (hG P h)
    unfold gapOp
    rw [dif_neg hP0]
  have hdead := sum_deadTerm B.q f hG'
  have hsplit : ∑ d : DeadLabel G', f (.dead d) =
      f (.dead d₀) + ∑ d ∈ univ.erase d₀, f (.dead d) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ d₀)).symm
  have hN : 0 ≤ ∑ P ∈ univ.erase (0 : G), f (.neck (Branch.mk P)) :=
    Finset.sum_nonneg fun _ _ => hf _
  have hD : 0 ≤ ∑ d ∈ univ.erase d₀, f (.dead d) := Finset.sum_nonneg fun _ _ => hf _
  have key : (α : ℂ) * sOne B.q f + (β : ℂ) * sTwo B.q f +
        ((β₀ - β : ℝ) : ℂ) * (deadTerm B.q f (0 : G') / B.q) + 2 * (e : ℂ) * f (.dead d₀) =
      (((α * (qr - 1) + β₀ * (qr + 1)) / qr : ℝ) : ℂ) * f (.neck (Branch.mk 0)) +
        (((α - β₀) / qr : ℝ) : ℂ) * f (.cap (capZero G)) +
        (α : ℂ) * ∑ P ∈ univ.erase (0 : G), f (.neck (Branch.mk P)) +
        ((2 * β : ℝ) : ℂ) * ∑ d ∈ univ.erase d₀, f (.dead d) +
        ((2 * (β + e) : ℝ) : ℂ) * f (.dead d₀) := by
    unfold sOne sTwo
    rw [hgap, hdead, hsplit, gapOp_zero_eq, deadTerm_zero_eq]
    push_cast
    field_simp
    ring
  rw [key]
  have c1 : 0 ≤ (α * (qr - 1) + β₀ * (qr + 1)) / qr := div_nonneg hA hqr.le
  have c2 : 0 ≤ (α - β₀) / qr := div_nonneg (by linarith) hqr.le
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (ofReal_nonneg' c1) (hf _)) (mul_nonneg (ofReal_nonneg' c2) (hf _)))
    (mul_nonneg (ofReal_nonneg' hα) hN)) (mul_nonneg (ofReal_nonneg' (by linarith)) hD))
    (mul_nonneg (ofReal_nonneg' (by linarith)) (hf _))

include hG hG' hq hf in
/-- `pair_nonneg` without a dead end, when there may be no dead end. -/
theorem pair_nonneg' {α β β₀ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hB : β₀ ≤ α)
    (hA : 0 ≤ α * (qr - 1) + β₀ * (qr + 1)) :
    0 ≤ (α : ℂ) * sOne B.q f + (β : ℂ) * sTwo B.q f +
      ((β₀ - β : ℝ) : ℂ) * (deadTerm B.q f (0 : G') / B.q) := by
  have hqr : (0 : ℝ) < qr := by
    have : (7 : ℝ) ≤ qr := by exact_mod_cast hq
    linarith
  have hq0 := B.q_ne_zero
  have hgap : ∑ P : G, gapOp B.q f P =
      gapOp B.q f 0 + (B.q : ℂ) * ∑ P ∈ univ.erase (0 : G), f (.neck (Branch.mk P)) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : G)), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun P hP => ?_
    have hP0 : ¬ 2 • P = 0 := fun h => (Finset.mem_erase.mp hP).1 (hG P h)
    unfold gapOp
    rw [dif_neg hP0]
  have hdead := sum_deadTerm B.q f hG'
  have hN : 0 ≤ ∑ P ∈ univ.erase (0 : G), f (.neck (Branch.mk P)) :=
    Finset.sum_nonneg fun _ _ => hf _
  have hD : 0 ≤ ∑ d : DeadLabel G', f (.dead d) := Finset.sum_nonneg fun _ _ => hf _
  have key : (α : ℂ) * sOne B.q f + (β : ℂ) * sTwo B.q f +
        ((β₀ - β : ℝ) : ℂ) * (deadTerm B.q f (0 : G') / B.q) =
      (((α * (qr - 1) + β₀ * (qr + 1)) / qr : ℝ) : ℂ) * f (.neck (Branch.mk 0)) +
        (((α - β₀) / qr : ℝ) : ℂ) * f (.cap (capZero G)) +
        (α : ℂ) * ∑ P ∈ univ.erase (0 : G), f (.neck (Branch.mk P)) +
        ((2 * β : ℝ) : ℂ) * ∑ d : DeadLabel G', f (.dead d) := by
    unfold sOne sTwo
    rw [hgap, hdead, gapOp_zero_eq, deadTerm_zero_eq]
    push_cast
    field_simp
    ring
  rw [key]
  have c1 : 0 ≤ (α * (qr - 1) + β₀ * (qr + 1)) / qr := div_nonneg hA hqr.le
  have c2 : 0 ≤ (α - β₀) / qr := div_nonneg (by linarith) hqr.le
  exact add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (ofReal_nonneg' c1) (hf _)) (mul_nonneg (ofReal_nonneg' c2) (hf _)))
    (mul_nonneg (ofReal_nonneg' hα) hN)) (mul_nonneg (ofReal_nonneg' (by linarith)) hD)

include hq in
theorem qr_ge : (7 : ℝ) ≤ qr := by exact_mod_cast hq

theorem tr_le : |tr| ≤ qr := B.abs_traceR_le

include hG hG' hq hf in
/-- The sequence at the core is nonnegative. -/
theorem coreT_nonneg (d : ℕ) : 0 ≤ coreT B.q f d := by
  have h7 := qr_ge B hq
  have ht := tr_le B
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' d
  · rw [(even_closed B f hG hG' n).1]
    exact add_nonneg (mul_nonneg (ofReal_nonneg' (phiS_nonneg h7 ht n)) (hf _))
      (convC_nonneg (rhoS_nonneg h7 ht) (fun k => aS_nonneg hf _) n)
  · rw [(odd_closed B f hG hG' n).1]
    have h := pair_nonneg' B hG hG' hq hf (α := rhoS qr tr n / 2) (β := gammaS qr tr n / 2)
      (β₀ := gammaS qr tr n / 2) (div_nonneg (rhoS_nonneg h7 ht n) (by norm_num))
      (div_nonneg (gammaS_nonneg h7 ht n) (by norm_num))
      (by linarith [gammaS_le_rhoS h7 ht n])
      (by
        have := rhoS_nonneg h7 ht n
        have := gammaS_nonneg h7 ht n
        have h2 : 0 ≤ rhoS qr tr n / 2 * (qr - 1) := mul_nonneg (by linarith) (by linarith)
        have h3 : 0 ≤ gammaS qr tr n / 2 * (qr + 1) := mul_nonneg (by linarith) (by linarith)
        linarith)
    have e : (1 / 2 : ℂ) * (rhoS qr tr n : ℂ) * sOne B.q f + (1 / 2 : ℂ) * (gammaS qr tr n : ℂ) * sTwo B.q f =
        ((rhoS qr tr n / 2 : ℝ) : ℂ) * sOne B.q f + ((gammaS qr tr n / 2 : ℝ) : ℂ) * sTwo B.q f +
          ((gammaS qr tr n / 2 - gammaS qr tr n / 2 : ℝ) : ℂ) * (deadTerm B.q f (0 : G') / B.q) := by
      push_cast
      ring
    rw [e]
    exact add_nonneg h (convC_nonneg (rhoS_nonneg h7 ht) (fun k => aS_nonneg hf _) n)

include hG hG' hq hf in
/-- The geometric sum at the core is nonnegative. -/
theorem coreW_nonneg (d : ℕ) : 0 ≤ coreW B.q f d := by
  have h7 := qr_ge B hq
  have ht := tr_le B
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' d
  · rw [(even_closed B f hG hG' n).2.1]
    exact add_nonneg (mul_nonneg (ofReal_nonneg' (rhoS_nonneg h7 ht n)) (hf _))
      (convC_nonneg (sigmaS_nonneg h7 ht) (fun k => aS_nonneg hf _) n)
  · rw [(odd_closed B f hG hG' n).2.1]
    have h1 := sigmaS_nonneg h7 ht n
    have h2 := etaS_nonneg h7 ht n
    have h := pair_nonneg' B hG hG' hq hf (α := sigmaS qr tr n / 2) (β := etaS qr tr n / 2)
      (β₀ := etaS qr tr n / 2) (by linarith) (by linarith) (by linarith [etaS_le_sigmaS h7 ht n])
      (by
        have h2' : 0 ≤ sigmaS qr tr n / 2 * (qr - 1) := mul_nonneg (by linarith) (by linarith)
        have h3 : 0 ≤ etaS qr tr n / 2 * (qr + 1) := mul_nonneg (by linarith) (by linarith)
        linarith)
    have e : (1 / 2 : ℂ) * (sigmaS qr tr n : ℂ) * sOne B.q f + (1 / 2 : ℂ) * (etaS qr tr n : ℂ) * sTwo B.q f =
        ((sigmaS qr tr n / 2 : ℝ) : ℂ) * sOne B.q f + ((etaS qr tr n / 2 : ℝ) : ℂ) * sTwo B.q f +
          ((etaS qr tr n / 2 - etaS qr tr n / 2 : ℝ) : ℂ) * (deadTerm B.q f (0 : G') / B.q) := by
      push_cast
      ring
    rw [e]
    exact add_nonneg h (convC_nonneg (sigmaS_nonneg h7 ht) (fun k => aS_nonneg hf _) n)

include hG hG' hq hf in
/-- The alternating sum at even time is nonnegative. -/
theorem coreV_even_nonneg (n : ℕ) : 0 ≤ coreV B.q f (2 * n) := by
  have h7 := qr_ge B hq
  have ht := tr_le B
  rw [(even_closed B f hG hG' n).2.2]
  exact add_nonneg (mul_nonneg (ofReal_nonneg' (gammaS_nonneg h7 ht n)) (hf _))
    (convC_nonneg (etaS_nonneg h7 ht) (fun k => aS_nonneg hf _) n)

include hG hG' hq hf in
/-- At even time the geometric sum dominates the alternating sum. -/
theorem coreW_sub_coreV_even_nonneg (n : ℕ) : 0 ≤ coreW B.q f (2 * n) - coreV B.q f (2 * n) := by
  have h7 := qr_ge B hq
  have ht := tr_le B
  rw [(even_closed B f hG hG' n).2.1, (even_closed B f hG hG' n).2.2]
  have hc := convC_linear (x := fun j => sigmaS qr tr j - etaS qr tr j) (y := sigmaS qr tr) (z := etaS qr tr)
    (w := fun _ => 0) (A := 1) (B' := -1) (C := 0) (fun j => by ring) (fun k => aS f (2 * k)) n
  have e : (rhoS qr tr n : ℂ) * f .core + convC (sigmaS qr tr) (fun k => aS f (2 * k)) n -
      ((gammaS qr tr n : ℂ) * f .core + convC (etaS qr tr) (fun k => aS f (2 * k)) n) =
      ((rhoS qr tr n - gammaS qr tr n : ℝ) : ℂ) * f .core +
        convC (fun j => sigmaS qr tr j - etaS qr tr j) (fun k => aS f (2 * k)) n := by
    rw [hc]
    push_cast
    ring
  rw [e]
  exact add_nonneg
    (mul_nonneg (ofReal_nonneg' (by linarith [gammaS_le_rhoS h7 ht n])) (hf _))
    (convC_nonneg (fun j => by linarith [etaS_le_sigmaS h7 ht j]) (fun k => aS_nonneg hf _) n)

include hG hG' hq hf in
/-- Every entry of the wave on a ray is nonnegative: the echo is a geometric sum over the core. -/
theorem echoPart_nonneg (R : G) (k d : ℕ) : 0 ≤ echoPart B.q f R d k := by
  have hq0 : (0 : ℂ) ≤ (B.q : ℂ) := by simp
  have h7 := qr_ge B hq
  have hq1 : (0 : ℂ) ≤ (B.q : ℂ) - 1 := by
    have := ofReal_nonneg' (show (0 : ℝ) ≤ qr - 1 by linarith)
    simpa using this
  induction k generalizing d with
  | zero =>
    rcases d with _ | _ | d
    · rw [echoPart_zero]
      exact hf _
    · -- at the first tick the echo is the gap term
      have e : echoPart B.q f R (0 + 1) 0 = gapOp B.q f R := by
        unfold echoPart
        show waveOp B.q f (.ray R 0) - _ = _
        rw [waveOp_ray_zero]
        simp
      rw [e]
      unfold gapOp
      split_ifs
      · exact add_nonneg (mul_nonneg hq1 (hf _)) (hf _)
      · exact mul_nonneg hq0 (hf _)
    · have e : echoPart B.q f R (d + 1 + 1) 0 =
          (B.q : ℂ) * f (.ray (-R) d) + (B.q : ℂ) * ((B.q : ℂ) - 1) * coreW B.q f d := by
        unfold echoPart
        rw [show d + 1 + 1 = d + 2 from rfl, root_formula, show 0 + (d + 2) = d + 2 by ring]
        ring
      rw [e]
      exact add_nonneg (mul_nonneg hq0 (hf _))
        (mul_nonneg (mul_nonneg hq0 hq1) (coreW_nonneg B hG hG' hq hf d))
  | succ k ih =>
    rcases d with _ | d
    · rw [echoPart_zero]
      exact hf _
    · rw [echoPart_succ]
      exact mul_nonneg hq0 (ih d)

include hG hG' hq hf in
/-- **The wave propagator is a positive operator.** On a black hole with odd groups and `q ≥ 7`, all entries of `P_d(A)` are
nonnegative for every `d ≥ 3`, whatever the position of the resonances. -/
theorem chebOp_nonneg {d : ℕ} (hd : 3 ≤ d) (v : Vertex G (DeadLabel G')) : 0 ≤ chebOp B.q d f v := by
  have h7 := qr_ge B hq
  have ht := tr_le B
  have hq0 : (0 : ℂ) ≤ (B.q : ℂ) := by simp
  have hq1 : (0 : ℂ) ≤ (B.q : ℂ) - 1 := by
    have := ofReal_nonneg' (show (0 : ℝ) ≤ qr - 1 by linarith)
    simpa using this
  have hq2 : (0 : ℂ) ≤ (B.q : ℂ) + 1 := by
    have := ofReal_nonneg' (show (0 : ℝ) ≤ qr + 1 by linarith)
    simpa using this
  have hne := B.q_ne_zero
  have hW := coreW_nonneg B hG hG' hq hf
  -- write `d` as `e + 1`
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rcases v with _ | d₀ | x | L | ⟨P, k⟩
  · exact coreT_nonneg B hG hG' hq hf (e + 1)
  · obtain ⟨x, hx⟩ := d₀
    induction x using Quotient.inductionOn with
    | h Q =>
      change 0 ≤ chebOp B.q (e + 1) f (.dead ⟨Branch.mk Q, hx⟩)
      obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' e
      · rw [dead_row_odd B f n hx]
        exact mul_nonneg hq2 (coreV_even_nonneg B hG hG' hq hf n)
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [show 2 * (m + 1) + 1 + 1 = 2 * (m + 1) + 2 by ring, dead_row_even B f (m + 1) hx,
          (odd_closed B f hG hG' (m + 1)).2.2]
        have h1 := etaS_nonneg h7 ht (m + 1)
        have h2 := gpS_nonneg h7 ht (m + 1)
        have hdiag := dead_diag h7 ht m
        have hqr : 0 ≤ qr + 1 := by linarith
        have hle := gpS_le_etaS h7 ht (m + 1)
        have hα0 : 0 ≤ (qr + 1) * etaS qr tr (m + 1) / 2 :=
          div_nonneg (mul_nonneg hqr h1) (by norm_num)
        have hβ0 : 0 ≤ (qr + 1) * gpS qr tr (m + 1) / 2 :=
          div_nonneg (mul_nonneg hqr h2) (by norm_num)
        have h3 := pair_nonneg B hG hG' hq hf (α := (qr + 1) * etaS qr tr (m + 1) / 2)
          (β := (qr + 1) * gpS qr tr (m + 1) / 2) (β₀ := (qr + 1) * gpS qr tr (m + 1) / 2)
          (e := (-qr) ^ (m + 2)) hα0 hβ0
          (by
            have := mul_le_mul_of_nonneg_left hle hqr
            linarith)
          (add_nonneg (mul_nonneg hα0 (by linarith)) (mul_nonneg hβ0 hqr))
          (by linarith) ⟨Branch.mk Q, hx⟩
        have e1 : ((B.q : ℂ) + 1) * ((1 / 2 : ℂ) * (etaS qr tr (m + 1) : ℂ) * sOne B.q f +
              (1 / 2 : ℂ) * (gpS qr tr (m + 1) : ℂ) * sTwo B.q f +
              convC (etaS qr tr) (fun k => aS f (2 * k + 1)) (m + 1)) +
              2 * (-(B.q : ℂ)) ^ (m + 1 + 1) * f (.dead ⟨Branch.mk Q, hx⟩) =
            (((qr + 1) * etaS qr tr (m + 1) / 2 : ℝ) : ℂ) * sOne B.q f +
              (((qr + 1) * gpS qr tr (m + 1) / 2 : ℝ) : ℂ) * sTwo B.q f +
              (((qr + 1) * gpS qr tr (m + 1) / 2 - (qr + 1) * gpS qr tr (m + 1) / 2 : ℝ) : ℂ) *
                (deadTerm B.q f (0 : G') / B.q) +
              2 * (((-qr) ^ (m + 2) : ℝ) : ℂ) * f (.dead ⟨Branch.mk Q, hx⟩) +
              ((B.q : ℂ) + 1) * convC (etaS qr tr) (fun k => aS f (2 * k + 1)) (m + 1) := by
          push_cast
          ring
        rw [e1]
        exact add_nonneg h3 (mul_nonneg hq2
          (convC_nonneg (etaS_nonneg h7 ht) (fun k => aS_nonneg hf _) _))
  · induction x using Quotient.inductionOn with
    | h P =>
      change 0 ≤ chebOp B.q (e + 1) f (.neck (Branch.mk P))
      by_cases hP : P = 0
      · subst hP
        rw [pin_of_terms B.q hne (chebOp B.q (e + 1) f), gap_formula]
        obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' e
        · rw [deadTerm_odd]
          have e1 : ((B.q : ℂ) * (f (.ray 0 (2 * n)) + f (.ray (-0) (2 * n)) +
              ((B.q : ℂ) - 1) * coreW B.q f (2 * n)) +
              (B.q : ℂ) * (((B.q : ℂ) + 1) * coreV B.q f (2 * n))) / (2 * (B.q : ℂ)) =
              f (.ray 0 (2 * n)) + (1 / 2 : ℂ) * (((B.q : ℂ) - 1) * coreW B.q f (2 * n)) +
                (1 / 2 : ℂ) * (((B.q : ℂ) + 1) * coreV B.q f (2 * n)) := by
            rw [neg_zero]
            field_simp
            ring
          rw [e1]
          have h12 := half_nonneg_C
          exact add_nonneg (add_nonneg (hf _) (mul_nonneg h12 (mul_nonneg hq1 (hW _))))
            (mul_nonneg h12 (mul_nonneg hq2 (coreV_even_nonneg B hG hG' hq hf n)))
        · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          rw [show 2 * (m + 1) + 1 + 1 = 2 * (m + 1) + 2 by ring, deadTerm_even,
            (odd_closed B f hG hG' (m + 1)).2.1, (odd_closed B f hG hG' (m + 1)).2.2]
          set n := m + 1 with hn
          have h1 := sigmaS_nonneg h7 ht n
          have h2 := etaS_nonneg h7 ht n
          have h3 := gpS_nonneg h7 ht n
          have hB := pin_B h7 ht n
          have hA := pin_A h7 ht m
          rw [← hn, show m + 2 = n + 1 by omega] at hA
          set α : ℝ := (qr - 1) * sigmaS qr tr n / 4 + (qr + 1) * etaS qr tr n / 4 with hα
          set β : ℝ := (qr - 1) * etaS qr tr n / 4 + (qr + 1) * gpS qr tr n / 4 with hβ
          set θ : ℝ := (-qr) ^ (n + 1) with hθ
          have hα0 : 0 ≤ α := add_nonneg (div_nonneg (mul_nonneg (by linarith) h1) (by norm_num))
            (div_nonneg (mul_nonneg (by linarith) h2) (by norm_num))
          have hβ0 : 0 ≤ β := add_nonneg (div_nonneg (mul_nonneg (by linarith) h2) (by norm_num))
            (div_nonneg (mul_nonneg (by linarith) h3) (by norm_num))
          have hpair := pair_nonneg' B hG hG' hq hf (α := α) (β := β) (β₀ := β + θ) hα0 hβ0
            (by rw [hα, hβ]; linarith)
            (by
              rw [hα, hβ]
              have e2 : ((qr - 1) * sigmaS qr tr n / 4 + (qr + 1) * etaS qr tr n / 4) * (qr - 1) +
                  ((qr - 1) * etaS qr tr n / 4 + (qr + 1) * gpS qr tr n / 4 + θ) * (qr + 1) =
                  (qr - 1) ^ 2 * sigmaS qr tr n / 4 + (qr ^ 2 - 1) * etaS qr tr n / 2 +
                    (qr + 1) ^ 2 * gpS qr tr n / 4 + (qr + 1) * θ := by
                ring
              rw [e2]
              exact hA)
          have e1 : ((B.q : ℂ) * (f (.ray 0 (2 * n + 1)) + f (.ray (-0) (2 * n + 1)) +
              ((B.q : ℂ) - 1) * ((1 / 2 : ℂ) * (sigmaS qr tr n : ℂ) * sOne B.q f +
                (1 / 2 : ℂ) * (etaS qr tr n : ℂ) * sTwo B.q f +
                convC (sigmaS qr tr) (fun k => aS f (2 * k + 1)) n)) +
              ((B.q : ℂ) * (((B.q : ℂ) + 1) * ((1 / 2 : ℂ) * (etaS qr tr n : ℂ) * sOne B.q f +
                (1 / 2 : ℂ) * (gpS qr tr n : ℂ) * sTwo B.q f +
                convC (etaS qr tr) (fun k => aS f (2 * k + 1)) n)) +
              2 * (-(B.q : ℂ)) ^ (n + 1) * deadTerm B.q f (0 : G'))) / (2 * (B.q : ℂ)) =
              ((α : ℂ) * sOne B.q f + (β : ℂ) * sTwo B.q f +
                ((β + θ - β : ℝ) : ℂ) * (deadTerm B.q f (0 : G') / B.q)) +
              f (.ray 0 (2 * n + 1)) +
              (1 / 2 : ℂ) * (((B.q : ℂ) - 1) * convC (sigmaS qr tr) (fun k => aS f (2 * k + 1)) n) +
              (1 / 2 : ℂ) * (((B.q : ℂ) + 1) * convC (etaS qr tr) (fun k => aS f (2 * k + 1)) n) := by
            rw [neg_zero, hα, hβ, hθ]
            push_cast
            field_simp
            ring
          rw [e1]
          have h12 := half_nonneg_C
          exact add_nonneg (add_nonneg (add_nonneg hpair (hf _))
            (mul_nonneg h12 (mul_nonneg hq1
              (convC_nonneg (sigmaS_nonneg h7 ht) (fun k => aS_nonneg hf _) _))))
            (mul_nonneg h12 (mul_nonneg hq2
              (convC_nonneg (etaS_nonneg h7 ht) (fun k => aS_nonneg hf _) _)))
      · have hP' : ¬ 2 • P = 0 := fun h => hP (hG P h)
        rw [neck_row B f hP' e]
        exact add_nonneg (add_nonneg (hf _) (hf _)) (mul_nonneg hq1 (hW _))
  · -- the cap
    have hL : L = capZero G := Subtype.ext (hG L.1 L.2)
    subst hL
    rw [cap_of_terms B.q (chebOp B.q (e + 1) f), pin_of_terms B.q hne (chebOp B.q (e + 1) f),
      gap_formula]
    obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' e
    · rw [deadTerm_odd]
      have e1 : ((B.q : ℂ) + 1) * (((B.q : ℂ) * (f (.ray 0 (2 * n)) + f (.ray (-0) (2 * n)) +
          ((B.q : ℂ) - 1) * coreW B.q f (2 * n)) +
          (B.q : ℂ) * (((B.q : ℂ) + 1) * coreV B.q f (2 * n))) / (2 * (B.q : ℂ))) -
          (B.q : ℂ) * (((B.q : ℂ) + 1) * coreV B.q f (2 * n)) =
          ((B.q : ℂ) + 1) * f (.ray 0 (2 * n)) + (1 / 2 : ℂ) * (((B.q : ℂ) ^ 2 - 1) *
            (coreW B.q f (2 * n) - coreV B.q f (2 * n))) := by
        rw [neg_zero]
        field_simp
        ring
      rw [e1]
      have h12 := half_nonneg_C
      have hsq : (0 : ℂ) ≤ (B.q : ℂ) ^ 2 - 1 := by
        have := ofReal_nonneg' (show (0 : ℝ) ≤ qr ^ 2 - 1 by nlinarith)
        simpa using this
      exact add_nonneg (mul_nonneg hq2 (hf _)) (mul_nonneg h12 (mul_nonneg hsq
        (coreW_sub_coreV_even_nonneg B hG hG' hq hf n)))
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [show 2 * (m + 1) + 1 + 1 = 2 * (m + 1) + 2 by ring, deadTerm_even,
        (odd_closed B f hG hG' (m + 1)).2.1, (odd_closed B f hG hG' (m + 1)).2.2]
      set n := m + 1 with hn
      have h1 := etaS_le_sigmaS h7 ht n
      have h2 := gpS_le_etaS h7 ht n
      have hB := pin_B h7 ht n
      have hC := cap_B h7 ht m
      rw [← hn] at hC
      rw [show m + 2 = n + 1 by omega] at hC
      have hsq : 0 ≤ qr ^ 2 - 1 := by nlinarith
      set α : ℝ := (qr ^ 2 - 1) * (sigmaS qr tr n - etaS qr tr n) / 4 with hα
      set β : ℝ := (qr ^ 2 - 1) * (etaS qr tr n - gpS qr tr n) / 4 with hβ
      set θ : ℝ := (-qr) ^ (n + 1) with hθ
      have hα0 : 0 ≤ α := div_nonneg (mul_nonneg hsq (by linarith)) (by norm_num)
      have hβ0 : 0 ≤ β := div_nonneg (mul_nonneg hsq (by linarith)) (by norm_num)
      have hpair := pair_nonneg' B hG hG' hq hf (α := α) (β := β) (β₀ := β - (qr - 1) * θ) hα0 hβ0
        (by
          rw [hα, hβ]
          have e2 : (qr ^ 2 - 1) * (sigmaS qr tr n - etaS qr tr n) / 4 -
              ((qr ^ 2 - 1) * (etaS qr tr n - gpS qr tr n) / 4 - (qr - 1) * θ) =
              (qr ^ 2 - 1) * (sigmaS qr tr n - 2 * etaS qr tr n + gpS qr tr n) / 4 + (qr - 1) * θ := by
            ring
          linarith)
        (by
          rw [hα, hβ]
          have e2 : (qr ^ 2 - 1) * (sigmaS qr tr n - etaS qr tr n) / 4 * (qr - 1) +
              ((qr ^ 2 - 1) * (etaS qr tr n - gpS qr tr n) / 4 - (qr - 1) * θ) * (qr + 1) =
              (qr ^ 2 - 1) * ((qr - 1) * (sigmaS qr tr n - etaS qr tr n) / 4 +
                (qr + 1) * (etaS qr tr n - gpS qr tr n) / 4 - θ) := by
            ring
          rw [e2]
          exact mul_nonneg hsq (by linarith))
      have e1 : ((B.q : ℂ) + 1) * (((B.q : ℂ) * (f (.ray 0 (2 * n + 1)) + f (.ray (-0) (2 * n + 1)) +
          ((B.q : ℂ) - 1) * ((1 / 2 : ℂ) * (sigmaS qr tr n : ℂ) * sOne B.q f +
            (1 / 2 : ℂ) * (etaS qr tr n : ℂ) * sTwo B.q f +
            convC (sigmaS qr tr) (fun k => aS f (2 * k + 1)) n)) +
          ((B.q : ℂ) * (((B.q : ℂ) + 1) * ((1 / 2 : ℂ) * (etaS qr tr n : ℂ) * sOne B.q f +
            (1 / 2 : ℂ) * (gpS qr tr n : ℂ) * sTwo B.q f +
            convC (etaS qr tr) (fun k => aS f (2 * k + 1)) n)) +
          2 * (-(B.q : ℂ)) ^ (n + 1) * deadTerm B.q f (0 : G'))) / (2 * (B.q : ℂ))) -
          ((B.q : ℂ) * (((B.q : ℂ) + 1) * ((1 / 2 : ℂ) * (etaS qr tr n : ℂ) * sOne B.q f +
            (1 / 2 : ℂ) * (gpS qr tr n : ℂ) * sTwo B.q f +
            convC (etaS qr tr) (fun k => aS f (2 * k + 1)) n)) +
          2 * (-(B.q : ℂ)) ^ (n + 1) * deadTerm B.q f (0 : G')) =
          ((α : ℂ) * sOne B.q f + (β : ℂ) * sTwo B.q f +
            ((β - (qr - 1) * θ - β : ℝ) : ℂ) * (deadTerm B.q f (0 : G') / B.q)) +
          ((B.q : ℂ) + 1) * f (.ray 0 (2 * n + 1)) +
          (1 / 2 : ℂ) * (((B.q : ℂ) ^ 2 - 1) *
            (convC (sigmaS qr tr) (fun k => aS f (2 * k + 1)) n -
              convC (etaS qr tr) (fun k => aS f (2 * k + 1)) n)) := by
        rw [neg_zero, hα, hβ, hθ]
        push_cast
        field_simp
        ring
      rw [e1]
      have hc := convC_linear (x := fun j => sigmaS qr tr j - etaS qr tr j) (y := sigmaS qr tr)
        (z := etaS qr tr) (w := fun _ => 0) (A := 1) (B' := -1) (C := 0) (fun j => by ring)
        (fun k => aS f (2 * k + 1)) n
      have hdiff : 0 ≤ convC (sigmaS qr tr) (fun k => aS f (2 * k + 1)) n -
          convC (etaS qr tr) (fun k => aS f (2 * k + 1)) n := by
        have h0 := convC_nonneg (x := fun j => sigmaS qr tr j - etaS qr tr j)
          (fun j => by linarith [etaS_le_sigmaS h7 ht j]) (a := fun k => aS f (2 * k + 1))
          (fun k => aS_nonneg hf _) n
        rw [hc] at h0
        have e3 : ((1 : ℝ) : ℂ) * convC (sigmaS qr tr) (fun k => aS f (2 * k + 1)) n +
            ((-1 : ℝ) : ℂ) * convC (etaS qr tr) (fun k => aS f (2 * k + 1)) n +
            ((0 : ℝ) : ℂ) * convC (fun _ => 0) (fun k => aS f (2 * k + 1)) n =
            convC (sigmaS qr tr) (fun k => aS f (2 * k + 1)) n -
              convC (etaS qr tr) (fun k => aS f (2 * k + 1)) n := by
          push_cast
          ring
        rwa [e3] at h0
      have h12 := half_nonneg_C
      have hsqC : (0 : ℂ) ≤ (B.q : ℂ) ^ 2 - 1 := by
        have := ofReal_nonneg' hsq
        simpa using this
      exact add_nonneg (add_nonneg hpair (mul_nonneg hq2 (hf _)))
        (mul_nonneg h12 (mul_nonneg hsqC hdiff))
  · -- a ray
    have e1 : chebOp B.q (e + 1) f (.ray P k) = f (.ray P (k + (e + 1))) + echoPart B.q f P (e + 1) k := by
      unfold echoPart
      ring
    rw [e1]
    exact add_nonneg (hf _) (echoPart_nonneg B hG hG' hq hf P k _)

end Positivity

/-! ### Hecke at every degree -/

section EveryDegree

variable {D : Type*} [Fintype D]

/-- `P_d(T_Q)`: the operator of degree `d` and class `d Q`. It is `P_d(A)` conjugated by the translation of the cusps. -/
def heckeDeg (q : ℕ) (Q : G) (d : ℕ) (f : Vertex G D → ℂ) (v : Vertex G D) : ℂ :=
  chebOp q d (fun w => f (transl (-Q) w)) (transl Q v)

theorem heckeDeg_zero (q : ℕ) (Q : G) (f : Vertex G D → ℂ) (v : Vertex G D) :
    heckeDeg q Q 0 f v = 2 * f v := by
  unfold heckeDeg
  simp only [chebOp, transl_transl]

theorem heckeDeg_one (q : ℕ) (Q : G) (f : Vertex G D → ℂ) (v : Vertex G D) :
    heckeDeg q Q 1 f v = heckeOp q Q f v := (heckeOp_eq_conj q Q f v).symm

theorem heckeDeg_add_two (q : ℕ) (Q : G) (d : ℕ) (f : Vertex G D → ℂ) (v : Vertex G D) :
    heckeDeg q Q (d + 2) f v =
      heckeOp q Q (heckeDeg q Q (d + 1) f) v - (q : ℂ) * heckeDeg q Q d f v := by
  rw [heckeOp_eq_conj]
  have e : (fun w => heckeDeg q Q (d + 1) f (transl (-Q) w)) =
      chebOp q (d + 1) (fun w => f (transl (-Q) w)) := by
    funext w
    unfold heckeDeg
    rw [transl_neg_transl]
  rw [e]
  unfold heckeDeg
  rw [chebOp_add_two]

theorem heckeOp_sub_smul (q : ℕ) (Q : G) (g h : Vertex G D → ℂ) (a : ℂ) (v : Vertex G D) :
    heckeOp q Q (fun w => g w - a * h w) v = heckeOp q Q g v - a * heckeOp q Q h v := by
  have e : (fun w => g w - a * h w) = fun w => g w + (fun u => (-a) * h u) w := by
    funext w
    ring
  rw [e, heckeOp_add, heckeOp_smul]
  ring

theorem heckeDeg_sub_smul (q : ℕ) (Q : G) (d : ℕ) (g h : Vertex G D → ℂ) (a : ℂ) (v : Vertex G D) :
    heckeDeg q Q d (fun w => g w - a * h w) v = heckeDeg q Q d g v - a * heckeDeg q Q d h v := by
  induction d using Nat.twoStepInduction generalizing v with
  | zero =>
    simp only [heckeDeg_zero]
    ring
  | one =>
    simp only [heckeDeg_one]
    exact heckeOp_sub_smul q Q g h a v
  | more d h0 h1 =>
    simp only [heckeDeg_add_two]
    have e : heckeDeg q Q (d + 1) (fun w => g w - a * h w) =
        fun w => heckeDeg q Q (d + 1) g w - a * heckeDeg q Q (d + 1) h w := funext h1
    rw [e, heckeOp_sub_smul, h0]
    ring

theorem heckeDeg_smul (q : ℕ) (Q : G) (d : ℕ) (a : ℂ) (f : Vertex G D → ℂ) (v : Vertex G D) :
    heckeDeg q Q d (fun w => a * f w) v = a * heckeDeg q Q d f v := by
  have hzero : heckeDeg q Q d (fun _ => (0 : ℂ)) v = 0 := by
    have h := heckeDeg_sub_smul q Q d (fun _ => (0 : ℂ)) (fun _ => (0 : ℂ)) 1 v
    simp only [one_mul, sub_self] at h
    simpa using h
  have h := heckeDeg_sub_smul q Q d (fun _ => (0 : ℂ)) f (-a) v
  simp only [zero_sub, neg_mul, neg_neg] at h
  rw [h, hzero]
  ring

/-- **Hecke of degree `d` in the cusps**: the shift by `d`, moving the cusp by `±d Q`. -/
theorem heckeDeg_ray (q : ℕ) (Q : G) (d : ℕ) (f : Vertex G D → ℂ) (P : G) (j : ℕ) :
    heckeDeg q Q d f (.ray P (d + j)) =
      (q : ℂ) ^ d * f (.ray (P + d • Q) j) + f (.ray (P - d • Q) (2 * d + j)) := by
  unfold heckeDeg
  have e0 : transl Q (.ray P (d + j) : Vertex G D) = .ray (P + (d + j + 1) • Q) (d + j) := rfl
  rw [e0, chebOp_ray]
  have e1 : transl (-Q) (.ray (P + (d + j + 1) • Q) j : Vertex G D) = .ray (P + d • Q) j := by
    simp only [transl]
    congr 1
    have a : (d + j + 1) • Q = d • Q + (j + 1) • Q := by
      rw [← add_smul]
      rfl
    rw [smul_neg, a]
    abel
  have e2 : transl (-Q) (.ray (P + (d + j + 1) • Q) (2 * d + j) : Vertex G D) =
      .ray (P - d • Q) (2 * d + j) := by
    simp only [transl]
    congr 1
    have a : (2 * d + j + 1) • Q = d • Q + (d + j + 1) • Q := by
      rw [← add_smul]
      congr 1
      ring
    rw [smul_neg, a]
    abel
  rw [e1, e2]

variable (B : Channels G D)

/-- `P_d(T_Q)` commutes with the wave operator. -/
theorem heckeDeg_comm_waveOp (Q : G) (d : ℕ) (f : Vertex G D → ℂ) (v : Vertex G D) :
    waveOp B.q (heckeDeg B.q Q d f) v = heckeDeg B.q Q d (waveOp B.q f) v := by
  induction d using Nat.twoStepInduction generalizing f v with
  | zero =>
    have e : heckeDeg B.q Q 0 f = fun w => 2 * f w := funext (heckeDeg_zero B.q Q f)
    rw [e, waveOp_smul, heckeDeg_zero]
  | one =>
    have e : heckeDeg B.q Q 1 f = heckeOp B.q Q f := funext (heckeDeg_one B.q Q f)
    rw [e, heckeOp_comm_waveOp, heckeDeg_one]
  | more d h0 h1 =>
    have e : heckeDeg B.q Q (d + 2) f =
        fun w => heckeOp B.q Q (heckeDeg B.q Q (d + 1) f) w - (B.q : ℂ) * heckeDeg B.q Q d f w :=
      funext (heckeDeg_add_two B.q Q d f)
    rw [e, waveOp_sub_smul, heckeOp_comm_waveOp, heckeDeg_add_two, h0]
    have e1 : waveOp B.q (heckeDeg B.q Q (d + 1) f) = heckeDeg B.q Q (d + 1) (waveOp B.q f) :=
      funext (h1 f)
    rw [e1]

/-- `P_d(T_Q)` commutes with the rational places. -/
theorem heckeDeg_comm_heckeOp (Q R : G) (d : ℕ) (f : Vertex G D → ℂ) (v : Vertex G D) :
    heckeOp B.q R (heckeDeg B.q Q d f) v = heckeDeg B.q Q d (heckeOp B.q R f) v := by
  induction d using Nat.twoStepInduction generalizing f v with
  | zero =>
    have e : heckeDeg B.q Q 0 f = fun w => 2 * f w := funext (heckeDeg_zero B.q Q f)
    rw [e, heckeOp_smul, heckeDeg_zero]
  | one =>
    have e : heckeDeg B.q Q 1 f = heckeOp B.q Q f := funext (heckeDeg_one B.q Q f)
    rw [e, heckeOp_comm, heckeDeg_one]
  | more d h0 h1 =>
    have e : heckeDeg B.q Q (d + 2) f =
        fun w => heckeOp B.q Q (heckeDeg B.q Q (d + 1) f) w - (B.q : ℂ) * heckeDeg B.q Q d f w :=
      funext (heckeDeg_add_two B.q Q d f)
    rw [e, heckeOp_sub_smul, heckeOp_comm, heckeDeg_add_two, h0]
    have e1 : heckeOp B.q R (heckeDeg B.q Q (d + 1) f) = heckeDeg B.q Q (d + 1) (heckeOp B.q R f) :=
      funext (h1 f)
    rw [e1]

/-- **The operators of all degrees commute.** -/
theorem heckeDeg_comm (Q R : G) (d e : ℕ) (f : Vertex G D → ℂ) (v : Vertex G D) :
    heckeDeg B.q Q d (heckeDeg B.q R e f) v = heckeDeg B.q R e (heckeDeg B.q Q d f) v := by
  induction d using Nat.twoStepInduction generalizing f v with
  | zero =>
    have e1 : heckeDeg B.q Q 0 f = fun w => 2 * f w := funext (heckeDeg_zero B.q Q f)
    rw [heckeDeg_zero, e1, heckeDeg_smul]
  | one =>
    have e1 : heckeDeg B.q Q 1 f = heckeOp B.q Q f := funext (heckeDeg_one B.q Q f)
    rw [heckeDeg_one, e1, heckeDeg_comm_heckeOp]
  | more d h0 h1 =>
    have e1 : heckeDeg B.q Q (d + 2) f =
        fun w => heckeOp B.q Q (heckeDeg B.q Q (d + 1) f) w - (B.q : ℂ) * heckeDeg B.q Q d f w :=
      funext (heckeDeg_add_two B.q Q d f)
    have e2 : heckeDeg B.q Q (d + 1) (heckeDeg B.q R e f) =
        heckeDeg B.q R e (heckeDeg B.q Q (d + 1) f) := funext (h1 f)
    rw [heckeDeg_add_two, e1, heckeDeg_sub_smul, h0, e2, heckeDeg_comm_heckeOp B R Q e]

/-- `P_d(T_Q) 1 = (q^d + 1) 1`: the operator of degree `d` has `q^d + 1` edges. -/
theorem heckeDeg_one_const (Q : G) (d : ℕ) (v : Vertex G D) :
    heckeDeg B.q Q d (fun _ => (1 : ℂ)) v = (B.q : ℂ) ^ d + 1 := by
  unfold heckeDeg
  have h := chebOp_eigen (X := (B.q : ℂ)) (Y := 1) (q := B.q) (f := (fun _ => (1 : ℂ)) ) (by ring)
    (fun w => by rw [B.waveOp_one]; ring) d (transl Q v)
  rw [h]
  simp

/-- **`P_d(T_Q)` acts on every resonance by `X^d + Y^d`**, wherever the resonance is. -/
theorem heckeDeg_resonance (Q : G) (d : ℕ) {X Y : ℂ} (hXY : X * Y = B.q) (hne : X ≠ Y)
    (hlam : X + Y ≠ 0) {f : Vertex G D → ℂ} {c : G → ℂ} (hf : IsOutgoing B.q X Y f c)
    (v : Vertex G D) : heckeDeg B.q Q d f v = (X ^ d + Y ^ d) * f v :=
  hecke_rigidity B (heckeDeg B.q Q d) (heckeDeg_smul B.q Q d) (heckeDeg_comm_waveOp B Q d) d
    (fun P => P + d • Q) (fun P => P - d • Q) (heckeDeg_ray B.q Q d) hXY hne hlam hf v

/-- Hecke of every degree sends waves to waves. -/
theorem IsWave.heckeDeg {u : ℤ → Vertex G D → ℂ} (hu : IsWave B.q u) (Q : G) (d : ℕ) :
    IsWave B.q fun τ => GaloisForLFunctions.ArithmeticScatteringHolography.heckeDeg B.q Q d (u τ) := by
  intro τ v
  have e : (fun w => GaloisForLFunctions.ArithmeticScatteringHolography.heckeDeg B.q Q d (u (τ + 1)) w +
      (B.q : ℂ) * GaloisForLFunctions.ArithmeticScatteringHolography.heckeDeg B.q Q d (u (τ + (-1))) w) =
      GaloisForLFunctions.ArithmeticScatteringHolography.heckeDeg B.q Q d (waveOp B.q (u τ)) := by
    funext w
    have hfun : waveOp B.q (u τ) = fun x => u (τ + 1) x - (-(B.q : ℂ)) * u (τ + (-1)) x := by
      funext x
      rw [← hu τ x]
      ring
    rw [hfun, heckeDeg_sub_smul]
    ring
  have h := congrFun e v
  rw [heckeDeg_comm_waveOp]
  exact h

/-- **One conserved energy per place, at every degree.** -/
theorem heckeDeg_energy_balance {u : ℤ → Vertex G D → ℂ} (hu : IsWave B.q u) (Q : G) (d K : ℕ) (τ : ℤ) :
    energy B.q (K + 1) (fun τ => GaloisForLFunctions.ArithmeticScatteringHolography.heckeDeg B.q Q d (u τ)) u τ -
        energy B.q (K + 1)
          (fun τ => GaloisForLFunctions.ArithmeticScatteringHolography.heckeDeg B.q Q d (u τ)) u (τ + (-1)) =
      -((B.q : ℂ) ^ (-(τ + 1)) *
        ∑ P : G, rayFlux B.q (GaloisForLFunctions.ArithmeticScatteringHolography.heckeDeg B.q Q d (u (τ + 1)))
          (fun v => (starRingEnd ℂ) (u τ v)) P K) :=
  energy_balance B (IsWave.heckeDeg B hu Q d) hu K τ

end EveryDegree

section Positive

variable (B : Channels G (DeadLabel G')) (hG : ∀ P : G, 2 • P = 0 → P = 0)
  (hG' : ∀ Q : G', 2 • Q = 0 → Q = 0) (hq : 7 ≤ B.q)

include hG hG' hq in
/-- **Hecke at every degree `d ≥ 3` is a positive operator**, on a black hole with odd groups and `q ≥ 7`. -/
theorem heckeDeg_nonneg (Q : G) {d : ℕ} (hd : 3 ≤ d) {f : Vertex G (DeadLabel G') → ℂ}
    (hf : ∀ v, 0 ≤ f v) (v : Vertex G (DeadLabel G')) : 0 ≤ heckeDeg B.q Q d f v :=
  chebOp_nonneg B hG hG' hq (f := fun w => f (transl (-Q) w)) (fun _ => hf _) hd _

end Positive

/-- **Positivity of Hecke at all degrees does not exclude the fakes.** For `q ≥ 8`, the black hole with `N = 3`, `N' = 2q - 1` carries a
family of operators, one for each degree `d ≥ 3` and class `Q`, that commute with each other and with the wave operator, are
positive, have `q^d + 1` edges, act in the cusps by the shift by `d` and on a resonance by `X^d + Y^d`, and it has a resonance slower
than universal. Degrees one and two are `heckeOp` and `heckeTwo`. -/
theorem universal_damping_not_forced_at_every_degree {q : ℕ} (hq : 8 ≤ q) :
    let B := oddPairChannels q 3 (2 * (q - 1) + 1) (by decide) ⟨q - 1, rfl⟩ (by omega) (by omega)
    (∀ (Q : ZMod 3) (d : ℕ) (f : Vertex (ZMod 3) (DeadLabel (ZMod (2 * (q - 1) + 1))) → ℂ) (v),
        waveOp B.q (heckeDeg B.q Q d f) v = heckeDeg B.q Q d (waveOp B.q f) v) ∧
      (∀ (Q R : ZMod 3) (d e : ℕ) (f : Vertex (ZMod 3) (DeadLabel (ZMod (2 * (q - 1) + 1))) → ℂ) (v),
        heckeDeg B.q Q d (heckeDeg B.q R e f) v = heckeDeg B.q R e (heckeDeg B.q Q d f) v) ∧
      (∀ (Q : ZMod 3) (d : ℕ), 3 ≤ d →
        ∀ f : Vertex (ZMod 3) (DeadLabel (ZMod (2 * (q - 1) + 1))) → ℂ, (∀ v, 0 ≤ f v) → ∀ v,
          0 ≤ heckeDeg B.q Q d f v) ∧
      (∀ (Q : ZMod 3) (d : ℕ) (v : Vertex (ZMod 3) (DeadLabel (ZMod (2 * (q - 1) + 1)))),
        heckeDeg B.q Q d (fun _ => (1 : ℂ)) v = (B.q : ℂ) ^ d + 1) ∧
      ∃ (X Y : ℂ) (f : Vertex (ZMod 3) (DeadLabel (ZMod (2 * (q - 1) + 1))) → ℂ) (c : ZMod 3 → ℂ),
        f ≠ 0 ∧ IsOutgoing B.q X Y f c ∧ (B.q : ℝ) < Complex.normSq (X ^ 2) := by
  intro B
  have hG : ∀ P : ZMod 3, 2 • P = 0 → P = 0 := two_nsmul_eq_zero_zmod (by decide)
  have hG' : ∀ Q : ZMod (2 * (q - 1) + 1), 2 • Q = 0 → Q = 0 :=
    two_nsmul_eq_zero_zmod ⟨q - 1, rfl⟩
  have h7 : 7 ≤ B.q := by
    show 7 ≤ q
    omega
  refine ⟨fun Q d f v => heckeDeg_comm_waveOp B Q d f v, fun Q R d e f v => heckeDeg_comm B Q R d e f v,
    fun Q d hd f hf v => heckeDeg_nonneg B hG hG' h7 Q hd hf v,
    fun Q d v => heckeDeg_one_const B Q d v, ?_⟩
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
