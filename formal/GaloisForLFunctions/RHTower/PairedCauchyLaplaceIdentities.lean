import GaloisForLFunctions.HTGeometry.HalfLineExponentialPacketGram

/-!
# The universal paired transform: constant, Cauchy-atom and exponential-lag laws

For a value function `g` on a right half-plane the **paired transform** is

```text
P[g](w,u) = 2 Re( (g(w) + conj g(u))/(w + conj u) - (g(w) + g(u))/(w + u) ).
```

On a finite node packet `w₁,…,w_n` with `Re wⱼ > 0` and real coefficients `r₁,…,r_n`, put

```text
E(x) = ∑ⱼ rⱼ e^{-wⱼ x},   y = Im E,   A = ∫_0^∞ y²,
Z_a = Im ∑ⱼ rⱼ/(wⱼ+a),   y_a = Im ∑ⱼ rⱼ e^{-wⱼ x}/(wⱼ+a),   B_a = ∫_0^∞ y_a².
```

This module proves the three exact laws

```text
∑_{j,k} rⱼ r_k P[c](wⱼ,w_k)            = 8 c A,
∑_{j,k} rⱼ r_k P[w ↦ c/(w+a)](wⱼ,w_k)   = 4 c Z_a² + 8 a c B_a,
∑_{j,k} rⱼ r_k P[-d e^{-τ ·}](wⱼ,w_k)   = -8 d ∫_0^∞ y(x+τ) y(x) dx,
```

together with `ℝ`-linearity of the paired quadratic in `g` and the **contact-mass law**: two value
functions differing by a real constant have paired energies differing by exactly `8 c A`.  That is
why a real constant, invisible to the Herglotz imaginary part, still changes the paired form.

Everything is exact; the only analytic input is the half-line Gram algebra of
`HTGeometry.HalfLineExponentialPacketGram`.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry MeasureTheory Set Complex
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- The universal paired transform `(1)`. -/
def pairedTransform (g : ℂ → ℂ) (w u : ℂ) : ℝ :=
  2 * ((g w + (starRingEnd ℂ) (g u)) / (w + (starRingEnd ℂ) u)
        - (g w + g u) / (w + u)).re

/-- The paired quadratic form of a value function on a finite real-coefficient node packet. -/
def pairedQuadratic (w : Fin n → ℂ) (r : Fin n → ℝ) (g : ℂ → ℂ) : ℝ :=
  ∑ j, ∑ k, r j * r k * pairedTransform g (w j) (w k)

/-- The node packet as a half-line exponential packet, `E` of `(2)`. -/
def nodePacket (w : Fin n → ℂ) (r : Fin n → ℝ) : ℝ → ℂ :=
  halfLineExpPacket w (fun j => (r j : ℂ))

/-- The energy `A` of `(2)`. -/
def packetEnergy (w : Fin n → ℂ) (r : Fin n → ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), (nodePacket w r x).im ^ (2 : ℕ)

/-- The resolvent-weighted coefficients of `(3)`. -/
def resolventCoeff (w : Fin n → ℂ) (r : Fin n → ℝ) (a : ℝ) (j : Fin n) : ℂ :=
  (r j : ℂ) / (w j + (a : ℂ))

/-- `Z_a` of `(3)`. -/
def resolventValueIm (w : Fin n → ℂ) (r : Fin n → ℝ) (a : ℝ) : ℝ :=
  (∑ j, resolventCoeff w r a j).im

/-- `B_a` of `(3)`. -/
def resolventEnergy (w : Fin n → ℂ) (r : Fin n → ℝ) (a : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), (halfLineExpPacket w (resolventCoeff w r a) x).im ^ (2 : ℕ)

/-- The lag-translated coefficients. -/
def lagCoeff (w : Fin n → ℂ) (r : Fin n → ℝ) (tau : ℝ) (j : Fin n) : ℂ :=
  (r j : ℂ) * Complex.exp (-(w j) * (tau : ℂ))

/-- The lag autocorrelation `∫_0^∞ y(x) y(x+τ) dx`. -/
def packetAutocorrelation (w : Fin n → ℂ) (r : Fin n → ℝ) (tau : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), (nodePacket w r x).im * (halfLineExpPacket w (lagCoeff w r tau) x).im

theorem expPacket_lagCoeff (w : Fin n → ℂ) (r : Fin n → ℝ) (tau x : ℝ) :
    halfLineExpPacket w (lagCoeff w r tau) x = nodePacket w r (x + tau) := by
  unfold halfLineExpPacket nodePacket lagCoeff
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-! ## Elementary nonvanishing -/

theorem add_ne_zero_of_re_pos {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) : u + v ≠ 0 := by
  intro h
  have : (u + v).re = 0 := by rw [h]; simp
  rw [Complex.add_re] at this
  linarith

theorem add_conj_ne_zero_of_re_pos {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    u + (starRingEnd ℂ) v ≠ 0 := by
  refine add_ne_zero_of_re_pos hu ?_
  simpa using hv

/-! ## The `Re`-of-sum bridge and linearity -/

theorem pairedQuadratic_eq_re (w : Fin n → ℂ) (r : Fin n → ℝ) (g : ℂ → ℂ) :
    pairedQuadratic w r g
      = 2 * (∑ j, ∑ k, ((r j * r k : ℝ) : ℂ) *
          ((g (w j) + (starRingEnd ℂ) (g (w k))) / (w j + (starRingEnd ℂ) (w k))
            - (g (w j) + g (w k)) / (w j + w k))).re := by
  unfold pairedQuadratic pairedTransform
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem pairedTransform_add (g₁ g₂ : ℂ → ℂ) (w u : ℂ) :
    pairedTransform (fun z => g₁ z + g₂ z) w u
      = pairedTransform g₁ w u + pairedTransform g₂ w u := by
  unfold pairedTransform
  rw [← mul_add, ← Complex.add_re]
  congr 2
  rw [map_add]
  ring

theorem pairedQuadratic_add (w : Fin n → ℂ) (r : Fin n → ℝ) (g₁ g₂ : ℂ → ℂ) :
    pairedQuadratic w r (fun z => g₁ z + g₂ z)
      = pairedQuadratic w r g₁ + pairedQuadratic w r g₂ := by
  unfold pairedQuadratic
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pairedTransform_add]
  ring

/-! ## Sum swaps -/

theorem hermSum_swap (w : Fin n → ℂ) (c d : Fin n → ℂ) :
    ∑ j, ∑ k, c j * (starRingEnd ℂ) (d k) / (w j + (starRingEnd ℂ) (w k))
      = ∑ j, ∑ k, (starRingEnd ℂ) (d j) * c k / ((starRingEnd ℂ) (w j) + w k) := by
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [add_comm, mul_comm]

theorem bilSum_swap (w : Fin n → ℂ) (c d : Fin n → ℂ) :
    ∑ j, ∑ k, c j * d k / (w j + w k)
      = ∑ j, ∑ k, d j * c k / (w j + w k) := by
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [add_comm, mul_comm]

theorem ofReal_mul_re (t : ℝ) (z : ℂ) : (((t : ℝ) : ℂ) * z).re = t * z.re := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Splitting a double sum of sums. -/
theorem sum_sum_add (X Y : Fin n → Fin n → ℂ) :
    (∑ j, ∑ k, (X j k + Y j k)) = (∑ j, ∑ k, X j k) + ∑ j, ∑ k, Y j k := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_add_distrib

/-- Pulling a scalar out of a double sum. -/
theorem sum_sum_const_mul (t : ℂ) (Z : Fin n → Fin n → ℂ) :
    (∑ j, ∑ k, t * Z j k) = t * ∑ j, ∑ k, Z j k := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm

/-- A double sum of products of one-index families factors. -/
theorem sum_sum_mul_factor (c d : Fin n → ℂ) :
    (∑ j, ∑ k, c j * d k) = (∑ j, c j) * ∑ k, d k := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm

/-- Pulling a scalar out of a double sum of differences. -/
theorem sum_sum_const_mul_sub (t : ℂ) (X Y : Fin n → Fin n → ℂ) :
    (∑ j, ∑ k, t * (X j k - Y j k))
      = t * ((∑ j, ∑ k, X j k) - ∑ j, ∑ k, Y j k) := by
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ## `(4)`: the universal constant paired law -/

/-- **Equation (4).**  A real constant value function has paired quadratic `8 c A`. -/
theorem paired_const_law {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ) (c : ℝ) :
    pairedQuadratic w r (fun _ => (c : ℂ)) = 8 * c * packetEnergy w r := by
  classical
  set rc : Fin n → ℂ := fun j => (r j : ℂ) with hrc
  have hterm : ∀ j k : Fin n, ((r j * r k : ℝ) : ℂ) *
        (((c : ℂ) + (starRingEnd ℂ) ((c : ℂ))) / (w j + (starRingEnd ℂ) (w k))
          - ((c : ℂ) + (c : ℂ)) / (w j + w k))
      = ((2 * c : ℝ) : ℂ) *
        ((rc j * (starRingEnd ℂ) (rc k) / (w j + (starRingEnd ℂ) (w k)))
          - (rc j * rc k / (w j + w k))) := by
    intro j k
    rw [hrc]
    simp only [Complex.conj_ofReal]
    push_cast
    ring
  rw [pairedQuadratic_eq_re,
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hterm j k,
    sum_sum_const_mul_sub, hermSum_swap]
  have hgram := integral_im_sq_expPacket (w := w) (c := rc) hw
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re]
  have hA : (∑ j, ∑ k, (starRingEnd ℂ) (rc j) * rc k / ((starRingEnd ℂ) (w j) + w k)).re
      - (∑ j, ∑ k, rc j * rc k / (w j + w k)).re = 2 * packetEnergy w r := by
    rw [← hgram]
    rfl
  rw [hA]
  ring

/-! ## `(5)`: the universal real Cauchy-atom paired law -/

theorem cauchyAtom_split {u v b : ℂ} (hu : u + b ≠ 0) (hv : v + b ≠ 0) (huv : u + v ≠ 0) :
    (1 / (u + b) + 1 / (v + b)) / (u + v)
      = 1 / ((u + b) * (v + b)) + 2 * b / ((u + b) * (v + b) * (u + v)) := by
  field_simp
  ring

/-- **Equation (5).**  A real Cauchy atom `c/(w+a)` has paired quadratic
`4 c Z_a² + 8 a c B_a`. -/
theorem paired_cauchyAtom_law {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ)
    (c a : ℝ) (ha : ∀ j, w j + (a : ℂ) ≠ 0) :
    pairedQuadratic w r (fun z => (c : ℂ) / (z + (a : ℂ)))
      = 4 * c * (resolventValueIm w r a) ^ (2 : ℕ) + 8 * a * c * resolventEnergy w r a := by
  classical
  set cc : Fin n → ℂ := resolventCoeff w r a with hcc
  have haconj : ∀ k, (starRingEnd ℂ) (w k) + (a : ℂ) ≠ 0 := by
    intro k h
    apply ha k
    have : (starRingEnd ℂ) ((starRingEnd ℂ) (w k) + (a : ℂ)) = w k + (a : ℂ) := by
      simp [Complex.conj_ofReal]
    rw [← this, h, map_zero]
  have hconj_cc : ∀ k, (starRingEnd ℂ) (cc k) = (r k : ℂ) / ((starRingEnd ℂ) (w k) + (a : ℂ)) := by
    intro k
    rw [hcc, resolventCoeff, map_div₀, Complex.conj_ofReal, map_add, Complex.conj_ofReal]
  have hterm : ∀ j k : Fin n, ((r j * r k : ℝ) : ℂ) *
        (((c : ℂ) / (w j + (a : ℂ)) + (starRingEnd ℂ) ((c : ℂ) / (w k + (a : ℂ))))
            / (w j + (starRingEnd ℂ) (w k))
          - ((c : ℂ) / (w j + (a : ℂ)) + (c : ℂ) / (w k + (a : ℂ))) / (w j + w k))
      = (c : ℂ) * ((cc j * (starRingEnd ℂ) (cc k)
            + ((2 * a : ℝ) : ℂ) * (cc j * (starRingEnd ℂ) (cc k) / (w j + (starRingEnd ℂ) (w k))))
          - (cc j * cc k + ((2 * a : ℝ) : ℂ) * (cc j * cc k / (w j + w k)))) := by
    intro j k
    have hjc : (starRingEnd ℂ) ((c : ℂ) / (w k + (a : ℂ)))
        = (c : ℂ) / ((starRingEnd ℂ) (w k) + (a : ℂ)) := by
      rw [map_div₀, Complex.conj_ofReal, map_add, Complex.conj_ofReal]
    rw [hjc]
    have hs1 := cauchyAtom_split (u := w j) (v := (starRingEnd ℂ) (w k)) (b := (a : ℂ))
      (ha j) (haconj k) (add_conj_ne_zero_of_re_pos (hw j) (hw k))
    have hs2 := cauchyAtom_split (u := w j) (v := w k) (b := (a : ℂ))
      (ha j) (ha k) (add_ne_zero_of_re_pos (hw j) (hw k))
    have hcdiv : ∀ u : ℂ, (c : ℂ) / u = (c : ℂ) * (1 / u) := by
      intro u; rw [mul_one_div]
    rw [hcdiv (w j + (a : ℂ)), hcdiv ((starRingEnd ℂ) (w k) + (a : ℂ)), hcdiv (w k + (a : ℂ)),
      ← mul_add, ← mul_add, mul_div_assoc, mul_div_assoc, hs1, hs2]
    simp only [hcc, resolventCoeff, map_div₀, Complex.conj_ofReal, map_add]
    field_simp
    push_cast
    ring
  rw [pairedQuadratic_eq_re,
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hterm j k,
    sum_sum_const_mul_sub]
  -- split the two double sums
  have hsplit1 : (∑ j, ∑ k, (cc j * (starRingEnd ℂ) (cc k)
        + ((2 * a : ℝ) : ℂ) * (cc j * (starRingEnd ℂ) (cc k) / (w j + (starRingEnd ℂ) (w k)))))
      = (∑ j, cc j) * (starRingEnd ℂ) (∑ j, cc j)
        + ((2 * a : ℝ) : ℂ) * ∑ j, ∑ k, cc j * (starRingEnd ℂ) (cc k)
            / (w j + (starRingEnd ℂ) (w k)) := by
    rw [sum_sum_add, sum_sum_const_mul, sum_sum_mul_factor, map_sum]
  have hsplit2 : (∑ j, ∑ k, (cc j * cc k + ((2 * a : ℝ) : ℂ) * (cc j * cc k / (w j + w k))))
      = (∑ j, cc j) * (∑ j, cc j)
        + ((2 * a : ℝ) : ℂ) * ∑ j, ∑ k, cc j * cc k / (w j + w k) := by
    rw [sum_sum_add, sum_sum_const_mul, sum_sum_mul_factor]
  rw [hsplit1, hsplit2, hermSum_swap]
  set F : ℂ := ∑ j, cc j with hFdef
  set Hs : ℂ := ∑ j, ∑ k, (starRingEnd ℂ) (cc j) * cc k / ((starRingEnd ℂ) (w j) + w k) with hHs
  set Bs : ℂ := ∑ j, ∑ k, cc j * cc k / (w j + w k) with hBs
  have hgram : Hs.re - Bs.re = 2 * resolventEnergy w r a :=
    (integral_im_sq_expPacket (w := w) (c := cc) hw).symm
  have hFsq : (F * (starRingEnd ℂ) F).re - (F * F).re = 2 * F.im ^ (2 : ℕ) := by
    have h1 : (F * (starRingEnd ℂ) F).re = ‖F‖ ^ (2 : ℕ) := by
      rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_apply]
      ring
    have h2 : (F * F).re = (F ^ (2 : ℕ)).re := by rw [pow_two]
    rw [h1, h2]
    exact normSq_sub_re_sq F
  have hXre : ((F * (starRingEnd ℂ) F + ((2 * a : ℝ) : ℂ) * Hs)
        - (F * F + ((2 * a : ℝ) : ℂ) * Bs)).re
      = 2 * F.im ^ (2 : ℕ) + (2 * a) * (2 * resolventEnergy w r a) := by
    rw [Complex.sub_re, Complex.add_re, Complex.add_re, ofReal_mul_re, ofReal_mul_re]
    have hmul : 2 * a * Hs.re - 2 * a * Bs.re = 2 * a * (2 * resolventEnergy w r a) := by
      rw [← mul_sub, hgram]
    linarith [hFsq, hmul]
  rw [ofReal_mul_re, hXre]
  have hZ : resolventValueIm w r a = F.im := rfl
  rw [hZ]
  ring


/-! ## `(6)`: the universal exponential-lag autocorrelation law -/

/-- **Equation (6).**  A damped exponential lag term `-d e^{-τ w}` has paired quadratic
`-8 d ∫_0^∞ y(x+τ) y(x) dx`. -/
theorem paired_lag_law {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ) (d tau : ℝ) :
    pairedQuadratic w r (fun z => -(d : ℂ) * Complex.exp (-(tau : ℂ) * z))
      = -8 * d * packetAutocorrelation w r tau := by
  classical
  set L : Fin n → ℂ := lagCoeff w r tau with hLdef
  set rho : Fin n → ℂ := fun j => (r j : ℂ) with hrho
  have hLval : ∀ j, L j = (r j : ℂ) * Complex.exp (-(tau : ℂ) * w j) := by
    intro j
    rw [hLdef, lagCoeff]
    congr 2
    ring
  have hconjL : ∀ k, (starRingEnd ℂ) (L k)
      = (r k : ℂ) * Complex.exp (-(tau : ℂ) * (starRingEnd ℂ) (w k)) := by
    intro k
    rw [hLval, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, map_neg,
      Complex.conj_ofReal]
  have hterm : ∀ j k : Fin n, ((r j * r k : ℝ) : ℂ) *
        ((-(d : ℂ) * Complex.exp (-(tau : ℂ) * w j)
            + (starRingEnd ℂ) (-(d : ℂ) * Complex.exp (-(tau : ℂ) * w k)))
              / (w j + (starRingEnd ℂ) (w k))
          - (-(d : ℂ) * Complex.exp (-(tau : ℂ) * w j)
              + -(d : ℂ) * Complex.exp (-(tau : ℂ) * w k)) / (w j + w k))
      = -((d : ℝ) : ℂ) *
        ((L j * (starRingEnd ℂ) (rho k) / (w j + (starRingEnd ℂ) (w k))
            + rho j * (starRingEnd ℂ) (L k) / (w j + (starRingEnd ℂ) (w k)))
          - (L j * rho k / (w j + w k) + rho j * L k / (w j + w k))) := by
    intro j k
    rw [map_mul, map_neg, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, map_neg,
      Complex.conj_ofReal, hconjL k, hLval j, hLval k]
    simp only [hrho, Complex.conj_ofReal]
    push_cast
    ring
  rw [pairedQuadratic_eq_re,
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hterm j k,
    sum_sum_const_mul_sub, sum_sum_add, sum_sum_add,
    hermSum_swap w L rho, hermSum_swap w rho L, bilSum_swap w L rho]
  set Hs : ℂ := ∑ j, ∑ k, (starRingEnd ℂ) (rho j) * L k / ((starRingEnd ℂ) (w j) + w k) with hHs
  set Hs' : ℂ := ∑ j, ∑ k, (starRingEnd ℂ) (L j) * rho k / ((starRingEnd ℂ) (w j) + w k) with hHs'
  set Bs : ℂ := ∑ j, ∑ k, rho j * L k / (w j + w k) with hBs
  have hconjHs : Hs' = (starRingEnd ℂ) Hs := by
    have h1 : (starRingEnd ℂ) Hs
        = ∑ j, ∑ k, rho j * (starRingEnd ℂ) (L k) / (w j + (starRingEnd ℂ) (w k)) := by
      rw [hHs, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_div₀, map_mul, map_add, Complex.conj_conj, Complex.conj_conj]
    rw [h1, hermSum_swap w rho L, hHs']
  have hgram : Hs.re - Bs.re = 2 * packetAutocorrelation w r tau := by
    simp only [packetAutocorrelation, nodePacket]
    exact (integral_im_mul_im_expPacket (w := w) rho L hw).symm
  have hHsre : Hs'.re = Hs.re := by rw [hconjHs, Complex.conj_re]
  have hneg : (-(d : ℂ)) = (((-d : ℝ)) : ℂ) := by push_cast; ring
  rw [hneg, ofReal_mul_re, Complex.sub_re, Complex.add_re, Complex.add_re, hHsre]
  have hmul : -4 * d * (Hs.re - Bs.re) = -4 * d * (2 * packetAutocorrelation w r tau) := by
    rw [hgram]
  linarith [hmul]

/-! ## The contact-mass law -/

/-- **The contact-mass law.**  Two value functions differing by a real constant have paired
energies differing by exactly `8 c A`.  A real constant is invisible to the Herglotz imaginary
part, but it is *not* invisible to the paired form. -/
theorem pairedQuadratic_const_shift {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ)
    (g₁ g₂ : ℂ → ℂ) (c : ℝ) (h : ∀ z, g₁ z = g₂ z + (c : ℂ)) :
    pairedQuadratic w r g₁ - pairedQuadratic w r g₂ = 8 * c * packetEnergy w r := by
  have h1 : pairedQuadratic w r g₁ = pairedQuadratic w r (fun z => g₂ z + (c : ℂ)) := by
    congr 1
    funext z
    exact h z
  rw [h1, pairedQuadratic_add w r g₂ (fun _ => (c : ℂ)), paired_const_law hw r c]
  ring

end

end RHTower
