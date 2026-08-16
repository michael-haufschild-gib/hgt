import GaloisForLFunctions.HTGeometry.SchemeEigenvolumeHorizon
import GaloisForLFunctions.HTGeometry.RamificationPoleFixedPoint

/-!
# Eigen-plurivolumes and their canonical log-crepant boundary

A rational section of the `k`-th tensor power of the canonical bundle which is an eigenvector of a
finite self-morphism determines a rational boundary `Δ = -(1/k) div Θ`.  The pluricanonical
pullback formula turns the eigen-condition into the weighted local law

`c + k = e (c' + k)`

on divisorial orders, equivalently `1 - d = e (1 - d')` on the normalized boundary coefficients.
This is the exact pointwise form of the two divisor statements of the theorem: the boundary
pullback identity `f* Δ = Δ + R_f`, and — combined with Riemann–Hurwitz for the canonical
coefficients — the log-crepant invariance `f*(K + Δ) = K + Δ`.

On a recurrent divisor whose cycle carries genuine expansion the weighted law has the single fixed
point `c = -k`, that is normalized boundary coefficient one, independently of the weight.
-/

namespace GaloisForLFunctions.HTGeometry

open AlgebraicGeometry Order

noncomputable section

/-! ## The abstract weighted law -/

section Abstract

variable {α : Type*} {F : α → α} {c : α → ℤ} {e : α → ℕ} {k : ℕ}

/-- The weighted shift is multiplied by the accumulated ramification along any orbit segment. -/
theorem pluriShift_eq_prod_iterate
    (hlaw : ∀ x, c x + (k : ℤ) = (e x : ℤ) * (c (F x) + (k : ℤ))) (x : α) (n : ℕ) :
    c x + (k : ℤ)
      = (∏ i ∈ Finset.range n, (e (F^[i] x) : ℤ)) * (c (F^[n] x) + (k : ℤ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ih, Finset.prod_range_succ, hlaw (F^[n] x), Function.iterate_succ_apply' F n x]
      ring

/-- **The weighted horizon fixed point.**  On a periodic divisor whose cycle carries genuine
expansion, the divisorial order of an eigen-`k`-plurivolume is exactly `-k`. -/
theorem pluriOrder_eq_neg_weight_of_periodic
    (hlaw : ∀ x, c x + (k : ℤ) = (e x : ℤ) * (c (F x) + (k : ℤ)))
    {x : α} {n : ℕ} (hper : F^[n] x = x)
    (hexp : 1 < ∏ i ∈ Finset.range n, (e (F^[i] x) : ℤ)) :
    c x = -(k : ℤ) := by
  have hfix := pluriShift_eq_prod_iterate hlaw x n
  rw [hper] at hfix
  set P : ℤ := ∏ i ∈ Finset.range n, (e (F^[i] x) : ℤ) with hP
  have hzero : (P - 1) * (c x + (k : ℤ)) = 0 := by
    have : P * (c x + (k : ℤ)) - (c x + (k : ℤ)) = 0 := by
      rw [← hfix]
      ring
    linarith [this]
  have hPne : P - 1 ≠ 0 := by omega
  have hck : c x + (k : ℤ) = 0 := (mul_eq_zero.mp hzero).resolve_left hPne
  omega

/-- The normalized boundary coefficient of an eigen-`k`-plurivolume. -/
def pluriBoundaryCoeff (k : ℕ) (c : α → ℤ) (x : α) : ℚ := -(c x : ℚ) / (k : ℚ)

/-- **Equation (7).**  The weighted order law is exactly the normalized boundary law. -/
theorem pluriBoundary_law (hk : k ≠ 0)
    (hlaw : ∀ x, c x + (k : ℤ) = (e x : ℤ) * (c (F x) + (k : ℤ))) (x : α) :
    1 - pluriBoundaryCoeff k c x = (e x : ℚ) * (1 - pluriBoundaryCoeff k c (F x)) := by
  have hkQ : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hcast : ((c x + (k : ℤ) : ℤ) : ℚ) = (((e x : ℤ) * (c (F x) + (k : ℤ)) : ℤ) : ℚ) := by
    rw [hlaw x]
  push_cast at hcast
  rw [pluriBoundaryCoeff, pluriBoundaryCoeff]
  field_simp
  linarith [hcast]

/-- **Equation (5).**  The pullback of the boundary is the boundary plus the ramification
divisor. -/
theorem pluriBoundary_pullback (hk : k ≠ 0)
    (hlaw : ∀ x, c x + (k : ℤ) = (e x : ℤ) * (c (F x) + (k : ℤ))) (x : α) :
    (e x : ℚ) * pluriBoundaryCoeff k c (F x)
      = pluriBoundaryCoeff k c x + ((e x : ℚ) - 1) := by
  have h := pluriBoundary_law (e := e) hk hlaw x
  linarith [h]

/-- **Equation (3).**  Writing the eigen-plurivolume as a rational multiple of the `k`-th power of
a chosen canonical section, the log pair is exactly the negative of the principal rational divisor
of that multiplier: `K + Δ` is `ℚ`-linearly trivial. -/
theorem pluriLogCrepant_principal (hk : k ≠ 0) (κ h : α → ℤ)
    (hΘ : ∀ x, c x = h x + (k : ℤ) * κ x) (x : α) :
    ((κ x : ℚ)) + pluriBoundaryCoeff k c x = -((h x : ℚ)) / (k : ℚ) := by
  have hkQ : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hcast : ((c x : ℤ) : ℚ) = ((h x : ℤ) : ℚ) + (k : ℚ) * ((κ x : ℤ) : ℚ) := by
    rw [hΘ x]
    push_cast
    ring
  rw [pluriBoundaryCoeff, hcast]
  field_simp
  ring

/-- **Equation (4).**  Given Riemann–Hurwitz for the coefficients of the canonical divisor, the
log-crepant pair is exactly pullback invariant. -/
theorem pluriLogCrepant_pullback (hk : k ≠ 0)
    (hlaw : ∀ x, c x + (k : ℤ) = (e x : ℤ) * (c (F x) + (k : ℤ)))
    (κ : α → ℚ) (hRH : ∀ x, κ x = (e x : ℚ) * κ (F x) + ((e x : ℚ) - 1)) (x : α) :
    (e x : ℚ) * (κ (F x) + pluriBoundaryCoeff k c (F x))
      = κ x + pluriBoundaryCoeff k c x := by
  have hb := pluriBoundary_pullback (e := e) hk hlaw x
  have hk' := hRH x
  linarith [hb, hk']

end Abstract

/-! ## The scheme instantiation -/

section Scheme

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

theorem scheme_ord_one (z : X) : Scheme.ord (1 : X.functionField) z = 0 := by
  have h := Scheme.ord_mul (x := z) (one_ne_zero (α := X.functionField)) one_ne_zero
  rw [one_mul] at h
  omega

theorem scheme_ord_pow {J : X.functionField} (hJ0 : J ≠ 0) (k : ℕ) (z : X) :
    Scheme.ord (J ^ k) z = (k : ℤ) * Scheme.ord J z := by
  induction k with
  | zero => rw [pow_zero, scheme_ord_one]; simp
  | succ n ih =>
      rw [pow_succ, Scheme.ord_mul (pow_ne_zero n hJ0) hJ0, ih]
      push_cast
      ring

variable (F : CodimOnePoint X → CodimOnePoint X) (e : CodimOnePoint X → ℕ) (k : ℕ)
variable {g J Pg : X.functionField} (hPg : Pg ≠ 0) (hJ0 : J ≠ 0)
variable (hpull : ∀ z : CodimOnePoint X, Scheme.ord Pg z.1 = (e z : ℤ) * Scheme.ord g (F z).1)
variable (hjac : ∀ z : CodimOnePoint X, Scheme.ord J z.1 = (e z : ℤ) - 1)
variable (heig : ∀ z : CodimOnePoint X, Scheme.ord (Pg * J ^ k) z.1 = Scheme.ord g z.1)

include hPg hJ0 hpull hjac heig in
/-- **Equation (6): the weighted shifted order law on a scheme.**  The pullback law, the weighted
order of the Jacobian factor and the eigen-plurivolume condition give the local law of the weighted
ramification system. -/
theorem schemeEigenPluriVolume_shiftLaw (z : CodimOnePoint X) :
    ordAt g z + (k : ℤ) = (e z : ℤ) * (ordAt g (F z) + (k : ℤ)) := by
  have hJk : (J ^ k : X.functionField) ≠ 0 := pow_ne_zero k hJ0
  have hmul := Scheme.ord_mul (x := z.1) hPg hJk
  have hpow : Scheme.ord (J ^ k) z.1 = (k : ℤ) * Scheme.ord J z.1 := scheme_ord_pow hJ0 k z.1
  rw [heig z, hpull z, hpow, hjac z] at hmul
  show Scheme.ord g z.1 + (k : ℤ) = (e z : ℤ) * (Scheme.ord g (F z).1 + (k : ℤ))
  rw [hmul]
  ring

include hPg hJ0 hpull hjac heig in
/-- **Equations (8) and (9).**  On a periodic divisor whose cycle carries expansion the
divisorial order of the eigen-plurivolume is `-k` and its normalized boundary coefficient is one. -/
theorem schemeEigenPluriVolume_periodic (hk : k ≠ 0) {z : CodimOnePoint X} {n : ℕ}
    (hper : F^[n] z = z)
    (hexp : 1 < ∏ i ∈ Finset.range n, (e (F^[i] z) : ℤ)) :
    ordAt g z = -(k : ℤ) ∧ pluriBoundaryCoeff k (ordAt g) z = 1 := by
  have horder := pluriOrder_eq_neg_weight_of_periodic
    (c := ordAt g) (e := e) (k := k)
    (schemeEigenPluriVolume_shiftLaw F e k hPg hJ0 hpull hjac heig) hper hexp
  refine ⟨horder, ?_⟩
  have hkQ : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  rw [pluriBoundaryCoeff, horder]
  push_cast
  field_simp

include hPg hJ0 hpull hjac heig in
/-- **The eigen-plurivolume log-crepant boundary law on a scheme.**  The normalized boundary
satisfies the exact ramification law, its pullback is the boundary plus the ramification divisor,
and against any Riemann–Hurwitz canonical coefficient system the log pair is pullback invariant. -/
theorem schemeEigenPluriVolume_logCrepant (hk : k ≠ 0) :
    (∀ z : CodimOnePoint X,
        1 - pluriBoundaryCoeff k (ordAt g) z
          = (e z : ℚ) * (1 - pluriBoundaryCoeff k (ordAt g) (F z))) ∧
      (∀ z : CodimOnePoint X,
        (e z : ℚ) * pluriBoundaryCoeff k (ordAt g) (F z)
          = pluriBoundaryCoeff k (ordAt g) z + ((e z : ℚ) - 1)) ∧
      (∀ κ : CodimOnePoint X → ℚ,
        (∀ z, κ z = (e z : ℚ) * κ (F z) + ((e z : ℚ) - 1)) →
          ∀ z : CodimOnePoint X,
            (e z : ℚ) * (κ (F z) + pluriBoundaryCoeff k (ordAt g) (F z))
              = κ z + pluriBoundaryCoeff k (ordAt g) z) := by
  have hlaw := schemeEigenPluriVolume_shiftLaw F e k hPg hJ0 hpull hjac heig
  exact ⟨fun z => pluriBoundary_law (e := e) hk hlaw z,
    fun z => pluriBoundary_pullback (e := e) hk hlaw z,
    fun κ hRH z => pluriLogCrepant_pullback (e := e) hk hlaw κ hRH z⟩

end Scheme

end

end GaloisForLFunctions.HTGeometry
