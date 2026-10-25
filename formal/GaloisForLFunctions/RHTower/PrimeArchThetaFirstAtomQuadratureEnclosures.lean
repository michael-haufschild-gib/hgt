import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomHighOrderQuadrature

/-!
# Rational enclosures for first-atom polynomial quadrature

Each arithmetic operation carries outward rational bounds. Polynomial list operations preserve
coefficientwise containment; integration and the rounded endpoint recurrence preserve it as well.
Integer numerators over a fixed denominator keep all polynomial operations in integer arithmetic.
-/

namespace RHTower.ThetaRationalQuadrature

def momentMass : QPoly → ℕ → ℚ → ℚ
  | [], _, _ => 0
  | a :: p, k, h =>
      a * h ^ (k + 1) / (k + 1 : ℚ) + momentMass p (k + 1) h

def integralMass (p : QPoly) (h : ℚ) : ℚ := momentMass p 0 h

def upperDelta (j : ℕ) : QPoly :=
  sub (mul (C ((3.14159265358979323847 : ℚ) * thirtySecondExpUpper ^ j))
      (sub expTwoTaylorUpper (C 1)))
    (mul (C (5 / 2)) X)

def lowerDelta (j : ℕ) : QPoly :=
  sub (mul (C ((3.14159265358979323846 : ℚ) * thirtySecondExpLower ^ j))
      (sub expTwoTaylor (C 1)))
    (mul (C (5 / 2)) X)

def localLower (j : ℕ) : QPoly := comp (expNeg 6) (upperDelta j)
def localUpper (j : ℕ) : QPoly := comp (expNeg 5) (lowerDelta j)

def sourceLower (j : ℕ) : QPoly :=
  sub (mul (C ((6.28318530717958647692 : ℚ) * thirtySecondExpLower ^ j))
    expTwoTaylor) (C 3)

def sourceUpper (j : ℕ) : QPoly :=
  sub (mul (C ((6.28318530717958647694 : ℚ) * thirtySecondExpUpper ^ j))
    expTwoTaylorUpper) (C 3)

def lowerPolynomial (r j : ℕ) : QPoly :=
  mul (mul (mul (C (12.5663706143591729538 : ℚ))
    (pow (add (C ((j : ℚ) / 64)) X) (2 * r))) (sourceLower j))
    (mul (C ((0.0432139182637 : ℚ) * endpointLower j)) (localLower j))

def upperPolynomial (r j : ℕ) : QPoly :=
  mul (mul (mul (C (12.5663706143591729539 : ℚ))
    (pow (add (C ((j : ℚ) / 64)) X) (2 * r))) (sourceUpper j))
    (mul (C ((0.0432139182638 : ℚ) * endpointUpper j)) (localUpper j))

def lowerMass (r j : ℕ) : ℚ := integralMass (lowerPolynomial r j) (1 / 64)
def upperMass (r j : ℕ) : ℚ := integralMass (upperPolynomial r j) (1 / 64)


namespace Enclosure

/-- Integer numerators of outward bounds with one common positive denominator. -/
structure Bounds where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq

/-- Common denominator for all coefficient and endpoint enclosures. -/
def precision : ℕ := 1000000000000000000000000000000

def lower (a : Bounds) : ℚ := a.lo / (precision : ℚ)
def upper (a : Bounds) : ℚ := a.hi / (precision : ℚ)
def Contains (a : Bounds) (x : ℚ) : Prop := lower a ≤ x ∧ x ≤ upper a

private theorem precision_pos : (0 : ℚ) < precision := by norm_num [precision]

def point (x : ℚ) : Bounds := ⟨⌊x * precision⌋, ⌈x * precision⌉⟩
def add (a b : Bounds) : Bounds := ⟨a.lo + b.lo, a.hi + b.hi⟩
def neg (a : Bounds) : Bounds := ⟨-a.hi, -a.lo⟩
def sub (a b : Bounds) : Bounds := add a (neg b)
def cornerLo (a b : Bounds) : ℤ :=
  min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi))
def cornerHi (a b : Bounds) : ℤ :=
  max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi))

def mul (a b : Bounds) : Bounds :=
  ⟨cornerLo a b / precision, -(-cornerHi a b / precision)⟩
def divNat (a : Bounds) (n : ℕ) : Bounds := ⟨a.lo / n, -(-a.hi / n)⟩
def pow (a : Bounds) : ℕ → Bounds
  | 0 => point 1
  | n + 1 => mul (pow a n) a

theorem contains_point (x : ℚ) : Contains (point x) x := by
  exact ⟨(div_le_iff₀ precision_pos).mpr (Int.floor_le _),
    (le_div_iff₀ precision_pos).mpr (Int.le_ceil _)⟩

theorem contains_add {a b : Bounds} {x y : ℚ}
    (hx : Contains a x) (hy : Contains b y) : Contains (add a b) (x + y) := by
  dsimp only [Contains, add, lower, upper] at *
  simp only [Int.cast_add, add_div]
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

theorem contains_neg {a : Bounds} {x : ℚ}
    (hx : Contains a x) : Contains (neg a) (-x) := by
  dsimp only [Contains, neg, lower, upper] at *
  simp only [Int.cast_neg, neg_div]
  exact ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩

theorem contains_sub {a b : Bounds} {x y : ℚ}
    (hx : Contains a x) (hy : Contains b y) : Contains (sub a b) (x - y) := by
  simpa only [sub, sub_eq_add_neg] using contains_add hx (contains_neg hy)

private theorem mul_le_max {l x u c : ℚ} (hl : l ≤ x) (hu : x ≤ u) :
    x * c ≤ max (l * c) (u * c) := by
  by_cases hc : 0 ≤ c
  · exact (mul_le_mul_of_nonneg_right hu hc).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_right hl (le_of_not_ge hc)).trans (le_max_left _ _)

private theorem min_le_mul {l x u c : ℚ} (hl : l ≤ x) (hu : x ≤ u) :
    min (l * c) (u * c) ≤ x * c := by
  by_cases hc : 0 ≤ c
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hl hc)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hu (le_of_not_ge hc))

private theorem scaled_bounds {a : Bounds} {x : ℚ} (hx : Contains a x) :
    (a.lo : ℚ) ≤ x * precision ∧ x * precision ≤ (a.hi : ℚ) :=
  ⟨(div_le_iff₀ precision_pos).mp hx.1, (le_div_iff₀ precision_pos).mp hx.2⟩

private theorem corner_bounds {a b : Bounds} {x y : ℚ}
    (hx : Contains a x) (hy : Contains b y) :
    (cornerLo a b : ℚ) ≤ (x * precision) * (y * precision) ∧
    (x * precision) * (y * precision) ≤ (cornerHi a b : ℚ) := by
  have ha := scaled_bounds hx
  have hb := scaled_bounds hy
  simp only [cornerLo, cornerHi, Int.cast_min, Int.cast_max, Int.cast_mul]
  constructor
  · apply le_trans _ (min_le_mul ha.1 ha.2)
    apply le_min
    · exact (min_le_left _ _).trans (by
        simpa only [mul_comm] using min_le_mul (c := (a.lo : ℚ)) hb.1 hb.2)
    · exact (min_le_right _ _).trans (by
        simpa only [mul_comm] using min_le_mul (c := (a.hi : ℚ)) hb.1 hb.2)
  · apply le_trans (mul_le_max ha.1 ha.2)
    apply max_le
    · calc
        (a.lo : ℚ) * (y * precision) ≤ max ((a.lo : ℚ) * b.lo) ((a.lo : ℚ) * b.hi) := by
          simpa only [mul_comm] using mul_le_max (c := (a.lo : ℚ)) hb.1 hb.2
        _ ≤ _ := le_max_left _ _
    · calc
        (a.hi : ℚ) * (y * precision) ≤ max ((a.hi : ℚ) * b.lo) ((a.hi : ℚ) * b.hi) := by
          simpa only [mul_comm] using mul_le_max (c := (a.hi : ℚ)) hb.1 hb.2
        _ ≤ _ := le_max_right _ _

/-- The product lies between its four corner products; integer division rounds outward. -/
theorem contains_mul {a b : Bounds} {x y : ℚ}
    (hx : Contains a x) (hy : Contains b y) : Contains (mul a b) (x * y) := by
  have hc := corner_bounds hx hy
  constructor
  · apply (div_le_iff₀ precision_pos).mpr
    change ((cornerLo a b / (precision : ℤ) : ℤ) : ℚ) ≤ (x * y) * precision
    rw [← Rat.floor_intCast_div_natCast]
    apply (Int.floor_le _).trans
    apply (div_le_iff₀ precision_pos).mpr
    calc
      (cornerLo a b : ℚ) ≤ (x * precision) * (y * precision) := hc.1
      _ = (x * y * precision) * precision := by ring
  · apply (le_div_iff₀ precision_pos).mpr
    change (x * y) * precision ≤ ((-(-cornerHi a b / (precision : ℤ)) : ℤ) : ℚ)
    rw [← Rat.ceil_intCast_div_natCast]
    apply le_trans _ (Int.le_ceil _)
    apply (le_div_iff₀ precision_pos).mpr
    calc
      (x * y * precision) * precision = (x * precision) * (y * precision) := by ring
      _ ≤ (cornerHi a b : ℚ) := hc.2

theorem contains_divNat {a : Bounds} {x : ℚ} (hx : Contains a x) (n : ℕ) :
    Contains (divNat a n) (x / n) := by
  have ha := scaled_bounds hx
  constructor
  · apply (div_le_iff₀ precision_pos).mpr
    change ((a.lo / (n : ℤ) : ℤ) : ℚ) ≤ (x / n) * precision
    rw [← Rat.floor_intCast_div_natCast]
    calc
      (⌊(a.lo : ℚ) / n⌋ : ℚ) ≤ (a.lo : ℚ) / n := Int.floor_le _
      _ ≤ (x * precision) / n := div_le_div_of_nonneg_right ha.1 (Nat.cast_nonneg _)
      _ = (x / n) * precision := by ring
  · apply (le_div_iff₀ precision_pos).mpr
    change (x / n) * precision ≤ ((-(-a.hi / (n : ℤ)) : ℤ) : ℚ)
    rw [← Rat.ceil_intCast_div_natCast]
    calc
      (x / n) * precision = (x * precision) / n := by ring
      _ ≤ (a.hi : ℚ) / n := div_le_div_of_nonneg_right ha.2 (Nat.cast_nonneg _)
      _ ≤ (⌈(a.hi : ℚ) / n⌉ : ℚ) := Int.le_ceil _

theorem contains_pow {a : Bounds} {x : ℚ} (hx : Contains a x) (n : ℕ) :
    Contains (pow a n) (x ^ n) := by
  induction n with
  | zero => simpa only [pow, pow_zero] using contains_point 1
  | succ n ih => simpa only [pow, pow_succ] using contains_mul ih hx


/-- Coefficientwise enclosure, with the same list shape on both sides. -/
def PolyContains (p : List Bounds) (q : QPoly) : Prop := List.Forall₂ Contains p q

def polyPoint (p : QPoly) : List Bounds := p.map point

def polyAdd : List Bounds → List Bounds → List Bounds
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => add a b :: polyAdd p q

def polyNeg (p : List Bounds) : List Bounds := p.map neg
def polySub (p q : List Bounds) : List Bounds := polyAdd p (polyNeg q)
def polyScale (a : Bounds) (p : List Bounds) : List Bounds := p.map (mul a)

def polyMul : List Bounds → List Bounds → List Bounds
  | [], _ => []
  | _ :: _, [] => []
  | a :: p, q => polyAdd (polyScale a q) (point 0 :: polyMul p q)

def polyPow (p : List Bounds) : ℕ → List Bounds
  | 0 => [point 1]
  | n + 1 => polyMul (polyPow p n) p

def polyComp (p q : List Bounds) : List Bounds :=
  p.foldr (fun a acc => polyAdd [a] (polyMul q acc)) []

def polyEval (p : List Bounds) (x : Bounds) : Bounds :=
  p.foldr (fun a acc => add a (mul x acc)) (point 0)

def mass : List Bounds → ℕ → Bounds → Bounds
  | [], _, _ => point 0
  | a :: p, k, h => add (divNat (mul a (pow h (k + 1))) (k + 1)) (mass p (k + 1) h)

theorem contains_polyPoint (p : QPoly) : PolyContains (polyPoint p) p := by
  induction p with
  | nil => exact .nil
  | cons a p ih => exact .cons (contains_point a) ih

theorem contains_polyAdd {p q : List Bounds} {s t : QPoly}
    (hp : PolyContains p s) (hq : PolyContains q t) :
    PolyContains (polyAdd p q) (ThetaRationalQuadrature.add s t) := by
  induction hp generalizing q t with
  | nil => exact hq
  | cons ha hp ih =>
      cases hq with
      | nil => exact .cons ha hp
      | cons hb hq => exact .cons (contains_add ha hb) (ih hq)

theorem contains_polyNeg {p : List Bounds} {s : QPoly} (hp : PolyContains p s) :
    PolyContains (polyNeg p) (ThetaRationalQuadrature.neg s) := by
  induction hp with
  | nil => exact .nil
  | cons ha hp ih => exact .cons (contains_neg ha) ih

theorem contains_polySub {p q : List Bounds} {s t : QPoly}
    (hp : PolyContains p s) (hq : PolyContains q t) :
    PolyContains (polySub p q) (ThetaRationalQuadrature.sub s t) :=
  contains_polyAdd hp (contains_polyNeg hq)

theorem contains_polyScale {a : Bounds} {x : ℚ} {p : List Bounds} {s : QPoly}
    (ha : Contains a x) (hp : PolyContains p s) :
    PolyContains (polyScale a p) (ThetaRationalQuadrature.scale x s) := by
  induction hp with
  | nil => exact .nil
  | cons hb hp ih => exact .cons (contains_mul ha hb) ih

theorem contains_polyMul {p q : List Bounds} {s t : QPoly}
    (hp : PolyContains p s) (hq : PolyContains q t) :
    PolyContains (polyMul p q) (ThetaRationalQuadrature.mul s t) := by
  induction hp generalizing q t with
  | nil => exact .nil
  | cons ha hp ih =>
      cases hq with
      | nil => exact .nil
      | cons hb hq =>
          exact contains_polyAdd (contains_polyScale ha (.cons hb hq))
            (.cons (contains_point 0) (ih (.cons hb hq)))

theorem contains_polyPow {p : List Bounds} {s : QPoly}
    (hp : PolyContains p s) (n : ℕ) :
    PolyContains (polyPow p n) (ThetaRationalQuadrature.pow s n) := by
  induction n with
  | zero => exact .cons (contains_point 1) .nil
  | succ n ih => exact contains_polyMul ih hp

theorem contains_polyComp {p q : List Bounds} {s t : QPoly}
    (hp : PolyContains p s) (hq : PolyContains q t) :
    PolyContains (polyComp p q) (ThetaRationalQuadrature.comp s t) := by
  induction hp with
  | nil => exact .nil
  | cons ha hp ih =>
      exact contains_polyAdd (.cons ha .nil) (contains_polyMul hq ih)

theorem contains_polyEval {p : List Bounds} {s : QPoly} {a : Bounds} {x : ℚ}
    (hp : PolyContains p s) (hx : Contains a x) :
    Contains (polyEval p a) (ThetaRationalQuadrature.eval s x) := by
  induction hp with
  | nil => exact contains_point 0
  | cons ha hp ih => exact contains_add ha (contains_mul hx ih)

theorem contains_mass {p : List Bounds} {s : QPoly} {a : Bounds} {x : ℚ}
    (hp : PolyContains p s) (hx : Contains a x) (k : ℕ) :
    Contains (mass p k a) (momentMass s k x) := by
  induction hp generalizing k with
  | nil => exact contains_point 0
  | cons ha hp ih =>
      simpa only [mass, momentMass, Nat.cast_add, Nat.cast_one] using
        contains_add (contains_divNat (contains_mul ha (contains_pow hx (k + 1))) (k + 1))
          (ih (k + 1))

/-- The endpoint rounding maps are monotone, including at their discontinuities. -/
private theorem monotone_roundDown : Monotone ThetaRationalQuadrature.roundDown := by
  intro x y h
  unfold ThetaRationalQuadrature.roundDown
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact_mod_cast Int.floor_mono (mul_le_mul_of_nonneg_right h (by norm_num : (0 : ℚ) ≤ 1000000000000))

private theorem monotone_roundUp : Monotone ThetaRationalQuadrature.roundUp := by
  intro x y h
  unfold ThetaRationalQuadrature.roundUp
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply (Int.cast_le (R := ℚ)).mpr
  exact Rat.ceil_le_iff.mpr ((mul_le_mul_of_nonneg_right h
    (by norm_num : (0 : ℚ) ≤ 1000000000000)).trans
      (Rat.le_ceil (x := y * 1000000000000)))

def down (a : Bounds) : Bounds :=
  ⟨(point (ThetaRationalQuadrature.roundDown (lower a))).lo,
    (point (ThetaRationalQuadrature.roundDown (upper a))).hi⟩
def up (a : Bounds) : Bounds :=
  ⟨(point (ThetaRationalQuadrature.roundUp (lower a))).lo,
    (point (ThetaRationalQuadrature.roundUp (upper a))).hi⟩

theorem contains_down {a : Bounds} {x : ℚ} (hx : Contains a x) :
    Contains (down a) (ThetaRationalQuadrature.roundDown x) :=
  ⟨(contains_point _).1.trans (monotone_roundDown hx.1),
    (monotone_roundDown hx.2).trans (contains_point _).2⟩

theorem contains_up {a : Bounds} {x : ℚ} (hx : Contains a x) :
    Contains (up a) (ThetaRationalQuadrature.roundUp x) :=
  ⟨(contains_point _).1.trans (monotone_roundUp hx.1),
    (monotone_roundUp hx.2).trans (contains_point _).2⟩

def expLo : Bounds := polyEval (polyPoint expTwoTaylor) (point (1 / 64))
def expHi : Bounds := polyEval (polyPoint expTwoTaylorUpper) (point (1 / 64))

theorem contains_expLo : Contains expLo thirtySecondExpLower :=
  contains_polyEval (contains_polyPoint _) (contains_point _)

theorem contains_expHi : Contains expHi thirtySecondExpUpper :=
  contains_polyEval (contains_polyPoint _) (contains_point _)

def incrementHi (j : ℕ) : Bounds :=
  sub (mul (mul (point 3.14159265358979323847) (pow expHi j))
    (sub expHi (point 1))) (point (5 / 128))
def incrementLo (j : ℕ) : Bounds :=
  sub (mul (mul (point 3.14159265358979323846) (pow expLo j))
    (sub expLo (point 1))) (point (5 / 128))

theorem contains_incrementHi (j : ℕ) : Contains (incrementHi j) (upperIncrement j) :=
  contains_sub (contains_mul (contains_mul (contains_point _) (contains_pow contains_expHi j))
    (contains_sub contains_expHi (contains_point _))) (contains_point _)

theorem contains_incrementLo (j : ℕ) : Contains (incrementLo j) (lowerIncrement j) :=
  contains_sub (contains_mul (contains_mul (contains_point _) (contains_pow contains_expLo j))
    (contains_sub contains_expLo (contains_point _))) (contains_point _)

def endpointLo : ℕ → Bounds
  | 0 => point 1
  | j + 1 => down (mul (endpointLo j) (polyEval (polyPoint (expNeg 10)) (incrementHi j)))
def endpointHi : ℕ → Bounds
  | 0 => point 1
  | j + 1 => up (mul (endpointHi j) (polyEval (polyPoint (expNeg 9)) (incrementLo j)))

theorem contains_endpointLo (j : ℕ) : Contains (endpointLo j) (endpointLower j) := by
  induction j with
  | zero => exact contains_point _
  | succ j ih => exact contains_down (contains_mul ih
      (contains_polyEval (contains_polyPoint _) (contains_incrementHi j)))

theorem contains_endpointHi (j : ℕ) : Contains (endpointHi j) (endpointUpper j) := by
  induction j with
  | zero => exact contains_point _
  | succ j ih => exact contains_up (contains_mul ih
      (contains_polyEval (contains_polyPoint _) (contains_incrementLo j)))

def deltaHi (j : ℕ) : List Bounds :=
  polySub (polyMul [mul (point 3.14159265358979323847) (pow expHi j)]
    (polySub (polyPoint expTwoTaylorUpper) [point 1]))
    (polyMul [point (5 / 2)] (polyPoint X))
def deltaLo (j : ℕ) : List Bounds :=
  polySub (polyMul [mul (point 3.14159265358979323846) (pow expLo j)]
    (polySub (polyPoint expTwoTaylor) [point 1]))
    (polyMul [point (5 / 2)] (polyPoint X))

theorem contains_C {a : Bounds} {x : ℚ} (hx : Contains a x) :
    PolyContains [a] (C x) := .cons hx .nil

theorem contains_deltaHi (j : ℕ) : PolyContains (deltaHi j) (upperDelta j) :=
  contains_polySub
    (contains_polyMul (contains_C (contains_mul (contains_point _) (contains_pow contains_expHi j)))
      (contains_polySub (contains_polyPoint _) (contains_C (contains_point _))))
    (contains_polyMul (contains_C (contains_point _)) (contains_polyPoint _))

theorem contains_deltaLo (j : ℕ) : PolyContains (deltaLo j) (lowerDelta j) :=
  contains_polySub
    (contains_polyMul (contains_C (contains_mul (contains_point _) (contains_pow contains_expLo j)))
      (contains_polySub (contains_polyPoint _) (contains_C (contains_point _))))
    (contains_polyMul (contains_C (contains_point _)) (contains_polyPoint _))

def localLo (j : ℕ) : List Bounds := polyComp (polyPoint (expNeg 6)) (deltaHi j)
def localHi (j : ℕ) : List Bounds := polyComp (polyPoint (expNeg 5)) (deltaLo j)

theorem contains_localLo (j : ℕ) : PolyContains (localLo j) (localLower j) :=
  contains_polyComp (contains_polyPoint _) (contains_deltaHi j)

theorem contains_localHi (j : ℕ) : PolyContains (localHi j) (localUpper j) :=
  contains_polyComp (contains_polyPoint _) (contains_deltaLo j)

def sourceLo (j : ℕ) : List Bounds :=
  polySub (polyMul [mul (point 6.28318530717958647692) (pow expLo j)]
    (polyPoint expTwoTaylor)) [point 3]
def sourceHi (j : ℕ) : List Bounds :=
  polySub (polyMul [mul (point 6.28318530717958647694) (pow expHi j)]
    (polyPoint expTwoTaylorUpper)) [point 3]

theorem contains_sourceLo (j : ℕ) : PolyContains (sourceLo j) (sourceLower j) :=
  contains_polySub
    (contains_polyMul (contains_C (contains_mul (contains_point _) (contains_pow contains_expLo j)))
      (contains_polyPoint _)) (contains_C (contains_point _))

theorem contains_sourceHi (j : ℕ) : PolyContains (sourceHi j) (sourceUpper j) :=
  contains_polySub
    (contains_polyMul (contains_C (contains_mul (contains_point _) (contains_pow contains_expHi j)))
      (contains_polyPoint _)) (contains_C (contains_point _))

def polynomialLo (r j : ℕ) : List Bounds :=
  polyMul (polyMul (polyMul [point 12.5663706143591729538]
    (polyPow (polyAdd [point ((j : ℚ) / 64)] (polyPoint X)) (2 * r))) (sourceLo j))
    (polyMul [mul (point 0.0432139182637) (endpointLo j)] (localLo j))
def polynomialHi (r j : ℕ) : List Bounds :=
  polyMul (polyMul (polyMul [point 12.5663706143591729539]
    (polyPow (polyAdd [point ((j : ℚ) / 64)] (polyPoint X)) (2 * r))) (sourceHi j))
    (polyMul [mul (point 0.0432139182638) (endpointHi j)] (localHi j))

theorem contains_polynomialLo (r j : ℕ) :
    PolyContains (polynomialLo r j) (lowerPolynomial r j) :=
  contains_polyMul
    (contains_polyMul
      (contains_polyMul (contains_C (contains_point _))
        (contains_polyPow (contains_polyAdd (contains_C (contains_point _))
          (contains_polyPoint _)) _)) (contains_sourceLo j))
    (contains_polyMul (contains_C (contains_mul (contains_point _) (contains_endpointLo j)))
      (contains_localLo j))

theorem contains_polynomialHi (r j : ℕ) :
    PolyContains (polynomialHi r j) (upperPolynomial r j) :=
  contains_polyMul
    (contains_polyMul
      (contains_polyMul (contains_C (contains_point _))
        (contains_polyPow (contains_polyAdd (contains_C (contains_point _))
          (contains_polyPoint _)) _)) (contains_sourceHi j))
    (contains_polyMul (contains_C (contains_mul (contains_point _) (contains_endpointHi j)))
      (contains_localHi j))

def massLo (r j : ℕ) : Bounds := mass (polynomialLo r j) 0 (point (1 / 64))
def massHi (r j : ℕ) : Bounds := mass (polynomialHi r j) 0 (point (1 / 64))

/-- Every rounded coefficient and endpoint is enclosed before integration. -/
theorem contains_massLo (r j : ℕ) : Contains (massLo r j) (lowerMass r j) :=
  contains_mass (contains_polynomialLo r j) (contains_point _) 0

theorem contains_massHi (r j : ℕ) : Contains (massHi r j) (upperMass r j) :=
  contains_mass (contains_polynomialHi r j) (contains_point _) 0

end Enclosure

end RHTower.ThetaRationalQuadrature
