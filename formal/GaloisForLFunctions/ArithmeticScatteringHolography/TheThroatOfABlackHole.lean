import GaloisForLFunctions.ArithmeticScatteringHolography.TheKreinFluxLaw

/-!
# The throat of a black hole

**The rate `¼` is the functional equation, and the functional equation is not unitarity.** On the graph of an elliptic curve the denominator `1 - t w + q w²` has the top
coefficient `q` because the local count forces it, so its roots multiply to `q` whatever `t` is, and the rate `¼` is their isotropic value. Here is the simplest tree lattice
where this is not forced: a throat with one cusp, of edge indices

  `(A f)(0) = (q+1) f(1)`, `(A f)(1) = a f(2) + (q+1-a) f(0)`, `(A f)(2) = b f(3) + (q+1-b) f(1)`, `(A f)(k+3) = f(k+4) + q f(k+2)`,

for `1 ≤ a, b ≤ q`. It has `q + 1` edges at every vertex (`throatOp_one`) and an invariant measure with Green's identity and no boundary but the cusp (`throat_green`), so it has
flux and unitarity. A nonzero outgoing eigenfunction exists at every root `z = X²` of

  `z² - T z + (b - 1) q`,  `T = 1 + (b-1) q - a b`  (`throat_resonance`).

So the roots multiply to `(b - 1) q`, and the denominator `1 - T w + (b-1) q w²` obeys the functional equation `P(w) = q w² P(1/(q w))` exactly when `b = 2`
(`throat_functional_equation_iff`). At `b = 2` the throat is a black hole of genus one with `T = q + 1 - 2a`; for `b ≠ 2` the modes have an isotropic value different from `√q`,
with flux and unitarity as before. At `b = 1` a mode is `z = 1 - a`, alone: a denominator of degree one, which no curve has.

So higher degrees and the functional equation are separate data: the wave system does not know the partner law. Everywhere else in this programme `¼` is the midpoint of a reflection
(`TheKMSStripOfTheHorizon`); this module says that the reflection has to be supplied.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticScatteringHolography

/-- **The wave operator of a throat.** -/
def throatOp (q a b : ℕ) (f : ℕ → ℂ) : ℕ → ℂ
  | 0 => ((q : ℂ) + 1) * f 1
  | 1 => (a : ℂ) * f 2 + ((q : ℂ) + 1 - a) * f 0
  | 2 => (b : ℂ) * f 3 + ((q : ℂ) + 1 - b) * f 1
  | k + 3 => f (k + 4) + (q : ℂ) * f (k + 2)

/-- Every vertex has `q + 1` edges. -/
theorem throatOp_one (q a b k : ℕ) : throatOp q a b (fun _ => 1) k = (q : ℂ) + 1 := by
  rcases k with _ | _ | _ | k
  · simp [throatOp]
  · simp [throatOp]
  · simp [throatOp]
  · simp only [throatOp]
    ring

/-- The invariant measure: balanced across every edge. -/
def throatMass (q a b : ℕ) : ℕ → ℂ
  | 0 => 1
  | 1 => ((q : ℂ) + 1) / ((q : ℂ) + 1 - a)
  | 2 => ((q : ℂ) + 1) / ((q : ℂ) + 1 - a) * (a / ((q : ℂ) + 1 - b))
  | k + 3 => ((q : ℂ) + 1) / ((q : ℂ) + 1 - a) * (a / ((q : ℂ) + 1 - b)) * (b / (q : ℂ) ^ (k + 1))

/-- The flux across the edge between depths `K + 2` and `K + 3`. -/
def throatFlux (q a b : ℕ) (f g : ℕ → ℂ) (K : ℕ) : ℂ :=
  throatMass q a b (K + 3) * (q : ℂ) * (f (K + 3) * g (K + 2) - f (K + 2) * g (K + 3))

section Green

variable {q a b : ℕ} (hq : 1 ≤ q) (ha : a ≤ q) (hb : b ≤ q)

include ha in
theorem q_add_one_sub_a_ne_zero : (q : ℂ) + 1 - a ≠ 0 := by
  have h : ((q + 1 - a : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rwa [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one] at h

include hq in
theorem q_ne_zero_cast : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)

include hq ha hb in
/-- **Green's identity of a throat.** The only boundary is the cusp: this is the flux law, and it gives unitarity. -/
theorem throat_green (f g : ℕ → ℂ) (K : ℕ) :
    ∑ k ∈ Finset.range (K + 3), throatMass q a b k *
        (throatOp q a b f k * g k - f k * throatOp q a b g k) =
      throatFlux q a b f g K := by
  have hA := q_add_one_sub_a_ne_zero ha
  have hB := q_add_one_sub_a_ne_zero hb
  have hQ := q_ne_zero_cast hq
  induction K with
  | zero =>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    simp only [throatOp, throatMass, throatFlux]
    field_simp
    ring
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [throatOp, throatMass, throatFlux]
    field_simp
    ring

end Green

/-! ### The modes -/

/-- The value of the outgoing eigenfunction at depth one. -/
def throatOne (q b : ℕ) (X Y : ℂ) : ℂ := (X + (1 - (b : ℂ)) * Y) * Y ^ 2 / ((q : ℂ) + 1 - b)

/-- The value of the outgoing eigenfunction at the end of the throat. -/
def throatZero (q a b : ℕ) (X Y : ℂ) : ℂ :=
  ((X + Y) * throatOne q b X Y - a * Y ^ 2) / ((q : ℂ) + 1 - a)

/-- The outgoing eigenfunction. -/
def throatField (q a b : ℕ) (X Y : ℂ) : ℕ → ℂ
  | 0 => throatZero q a b X Y
  | 1 => throatOne q b X Y
  | k + 2 => Y ^ (k + 2)

/-- The trace of the modes of a throat. -/
def throatTrace (q a b : ℕ) : ℂ := 1 + ((b : ℂ) - 1) * q - a * b

/-- The polynomial of the modes. -/
def throatPoly (q a b : ℕ) (z : ℂ) : ℂ := z ^ 2 - throatTrace q a b * z + ((b : ℂ) - 1) * q

/-- The condition at the end of the throat, in the variable `z = X²`: the constant function and the polynomial of the modes. -/
theorem throat_condition {q a b : ℕ} (ha : a ≤ q) (hb : b ≤ q) {X Y : ℂ} (hX : X ≠ 0)
    (hXY : X * Y = q) :
    (X + Y) * throatZero q a b X Y - ((q : ℂ) + 1) * throatOne q b X Y =
      Y ^ 2 * (X ^ 2 - (q : ℂ) ^ 2) * throatPoly q a b (X ^ 2) /
        (((q : ℂ) + 1 - a) * ((q : ℂ) + 1 - b) * X ^ 3) := by
  have hA := q_add_one_sub_a_ne_zero ha
  have hB := q_add_one_sub_a_ne_zero hb
  have hY : Y = (q : ℂ) / X := by
    field_simp
    linear_combination hXY
  subst hY
  unfold throatZero throatOne throatPoly throatTrace
  field_simp
  ring

/-- **A root of the polynomial is a resonance.** At `z = X²`, a root of `z² - T z + (b-1) q`, the throat has a nonzero outgoing eigenfunction. -/
theorem throat_resonance {q a b : ℕ} (hq : 1 ≤ q) (ha : a ≤ q) (hb : b ≤ q) {X Y : ℂ} (hX : X ≠ 0)
    (hXY : X * Y = q) (hroot : throatPoly q a b (X ^ 2) = 0) :
    throatField q a b X Y ≠ 0 ∧
      (∀ k, 2 ≤ k → throatField q a b X Y k = Y ^ k) ∧
      ∀ k, throatOp q a b (throatField q a b X Y) k = (X + Y) * throatField q a b X Y k := by
  have hA := q_add_one_sub_a_ne_zero ha
  have hB := q_add_one_sub_a_ne_zero hb
  have hQ := q_ne_zero_cast (q := q) hq
  have hY0 : Y ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hXY
    exact hQ hXY.symm
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h2 := congrFun h 2
    simp only [throatField, Pi.zero_apply] at h2
    exact pow_ne_zero _ hY0 h2
  · intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rfl
  · intro k
    rcases k with _ | _ | _ | k
    · -- the end of the throat: the only place where the polynomial enters
      have h0 := throat_condition ha hb hX hXY
      rw [hroot, mul_zero, zero_div] at h0
      simp only [throatOp, throatField]
      linear_combination -h0
    · simp only [throatOp, throatField]
      unfold throatZero
      field_simp
      ring
    · have h1 : ((q : ℂ) + 1 - b) * throatOne q b X Y = (X + (1 - (b : ℂ)) * Y) * Y ^ 2 := by
        unfold throatOne
        field_simp
      simp only [throatOp, throatField]
      linear_combination h1
    · simp only [throatOp, throatField]
      rw [← hXY]
      ring

/-- **The partner law of a throat.** The modes multiply to `(b - 1) q`. -/
theorem throat_partner_law (q a b : ℕ) {z₁ z₂ : ℂ}
    (h : ∀ z, throatPoly q a b z = (z - z₁) * (z - z₂)) : z₁ * z₂ = ((b : ℂ) - 1) * q := by
  have h0 := h 0
  unfold throatPoly at h0
  linear_combination -h0

/-- The denominator in the causal variable. -/
def throatDenom (q a b : ℕ) (w : ℂ) : ℂ := 1 - throatTrace q a b * w + ((b : ℂ) - 1) * q * w ^ 2

/-- **The functional equation holds exactly at `b = 2`.** `P(w) = q w² P(1/(q w))` for all `w ≠ 0` iff `b = 2`: it is an extra condition on the throat, and flux and unitarity hold
for every `b`. -/
theorem throat_functional_equation_iff {q a b : ℕ} (hq : 1 ≤ q) :
    (∀ w : ℂ, w ≠ 0 → throatDenom q a b w = (q : ℂ) * w ^ 2 * throatDenom q a b (1 / ((q : ℂ) * w))) ↔
      b = 2 := by
  have hQ := q_ne_zero_cast (q := q) hq
  have hform (w : ℂ) (hw : w ≠ 0) :
      (q : ℂ) * w ^ 2 * throatDenom q a b (1 / ((q : ℂ) * w)) =
        (q : ℂ) * w ^ 2 - throatTrace q a b * w + ((b : ℂ) - 1) := by
    unfold throatDenom
    field_simp
  constructor
  · intro h
    have h1 := h 1 one_ne_zero
    rw [hform 1 one_ne_zero] at h1
    unfold throatDenom at h1
    have h2 : (((b : ℂ) - 2) * ((q : ℂ) - 1)) = 0 := by
      linear_combination h1
    have h3 := h 2 two_ne_zero
    rw [hform 2 two_ne_zero] at h3
    unfold throatDenom at h3
    have h4 : ((b : ℂ) - 2) * (4 * (q : ℂ) - 1) = 0 := by
      linear_combination h3
    have h5 : ((b : ℂ) - 2) * (3 * (q : ℂ)) = 0 := by
      linear_combination h4 - h2
    have hb2 : (b : ℂ) - 2 = 0 := by
      rcases mul_eq_zero.mp h5 with h6 | h6
      · exact h6
      · exfalso
        apply hQ
        simpa using h6
    have : (b : ℂ) = ((2 : ℕ) : ℂ) := by
      push_cast
      linear_combination hb2
    exact Nat.cast_injective this
  · rintro rfl w hw
    rw [hform w hw]
    unfold throatDenom
    push_cast
    ring

/-- At `b = 2` the throat is of genus one: `T = q + 1 - 2 a`, and the modes multiply to `q`. -/
theorem throat_genus_one (q a : ℕ) :
    throatTrace q a 2 = (q : ℂ) + 1 - 2 * a ∧ ((((2 : ℕ) : ℂ) - 1) * q) = (q : ℂ) := by
  unfold throatTrace
  push_cast
  constructor <;> ring

/-- At `b = 1` the only mode is `z = 1 - a`: a denominator of degree one, which no curve has. -/
theorem throat_degree_one (q a : ℕ) (z : ℂ) : throatPoly q a 1 z = z * (z - (1 - (a : ℂ))) := by
  unfold throatPoly throatTrace
  push_cast
  ring

/-- **The Krein law of a throat runs at its own rate.** The Krein square of the modes is multiplied by `(b - 1) q`, not by `q`, along the recurrence of the modes. -/
theorem throat_krein_step (q a b : ℕ) (x y : ℂ) :
    kreinSquare (((b : ℂ) - 1) * q) (throatTrace q a b) y (throatTrace q a b * y - ((b : ℂ) - 1) * q * x) =
      ((b : ℂ) - 1) * q * kreinSquare (((b : ℂ) - 1) * q) (throatTrace q a b) x y :=
  kreinSquare_step _ _ x y

end GaloisForLFunctions.ArithmeticScatteringHolography

end
