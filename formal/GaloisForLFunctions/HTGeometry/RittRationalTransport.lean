import GaloisForLFunctions.HTGeometry.RittRationalSubstitutionOrder
import GaloisForLFunctions.HTGeometry.RationalInvariantDifferential

/-!
# Pole transport for a rational map

With the substitution law for a rational map in hand the transport argument runs unchanged.  The
affine transport equation for a rational `P` reads

`a(P) · (P′)^k = b · a + c`,

and at a point `p` where `P` is regular, `P′` is a unit, `b` is a unit and `c` is regular, the left
side has order `ord_{P(p)} a` times the local multiplicity — a positive integer — so a pole of `a`
at the image forces the order of the right side negative, and the valuation inequality then forces a
pole of `a` at `p` itself.  A pole therefore travels backward along the map, exactly as in the
polynomial case, and an injective critical-free backward orbit turns one pole into infinitely many,
which a nonzero rational function cannot sustain.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- **The affine transport equation for a rational map.** -/
def IsRatAffineTransport (P : RatFunc K) (hP : ¬ ∃ c : K, P = RatFunc.C c)
    (k : ℤ) (b c a : RatFunc K) : Prop :=
  ratFuncSubstitutionAlgHom P hP a * (ratFuncDeriv P) ^ k = b * a + c

/-- **A pole travels backward along a rational map.** -/
theorem ratAffineTransport_pole_backward {P : RatFunc K} (hP : ¬ ∃ c : K, P = RatFunc.C c)
    {k : ℤ} {b c a : RatFunc K} (ha : a ≠ 0) (hb : b ≠ 0) (hderiv0 : ratFuncDeriv P ≠ 0)
    (heq : IsRatAffineTransport P hP k b c a) {p : K} (hden : P.denom.eval p ≠ 0)
    (hderiv : ratOrder (ratFuncDeriv P) p = 0) (hbp : ratOrder b p = 0)
    (hcp : 0 ≤ ratOrder c p) (hpole : ratOrder a (ratValue P p) < 0) :
    ratOrder a p < 0 := by
  classical
  have hsub0 : ratFuncSubstitutionAlgHom P hP a ≠ 0 := by
    intro h
    have hz : ratFuncSubstitutionAlgHom P hP a = ratFuncSubstitutionAlgHom P hP 0 := by
      rw [map_zero]; exact h
    exact ha ((ratFuncSubstitutionAlgHom P hP).toRingHom.injective hz)
  have hepos : 0 < ratOrder (P - RatFunc.C (ratValue P p)) p :=
    ratOrder_sub_ratValue_pos hP hden
  have hlhs : ratOrder (ratFuncSubstitutionAlgHom P hP a * (ratFuncDeriv P) ^ k) p
      = ratOrder a (ratValue P p) * ratOrder (P - RatFunc.C (ratValue P p)) p := by
    rw [ratOrder_mul hsub0 (zpow_ne_zero _ hderiv0), ratOrder_zpow hderiv0, hderiv,
      ratOrder_ratFuncSubstitution_ratFunc hP hden ha]
    ring
  have hneg : ratOrder (ratFuncSubstitutionAlgHom P hP a * (ratFuncDeriv P) ^ k) p < 0 := by
    rw [hlhs]
    exact mul_neg_of_neg_of_pos hpole hepos
  rw [IsRatAffineTransport] at heq
  rw [heq] at hneg
  have hba0 : b * a ≠ 0 := mul_ne_zero hb ha
  rcases eq_or_ne c 0 with hc0 | hc0
  · rw [hc0, add_zero, ratOrder_mul hb ha, hbp] at hneg
    omega
  · rcases eq_or_ne (b * a + c) 0 with hsum | hsum
    · rw [hsum, ratOrder_zero] at hneg
      omega
    · have hmin := min_le_ratOrder_add hba0 hc0 hsum p
      rw [ratOrder_mul hb ha, hbp] at hmin
      omega



/-- **A pole on an injective critical-free backward orbit is impossible, for a rational map.** -/
theorem no_pole_of_backward_orbit_ratAffineTransport {P : RatFunc K}
    (hP : ¬ ∃ c : K, P = RatFunc.C c) {k : ℤ} {b c a : RatFunc K}
    (ha : a ≠ 0) (hb : b ≠ 0) (hderiv0 : ratFuncDeriv P ≠ 0)
    (heq : IsRatAffineTransport P hP k b c a)
    {q : ℕ → K} (hstep : ∀ n, ratValue P (q (n + 1)) = q n)
    (hden : ∀ n, P.denom.eval (q (n + 1)) ≠ 0)
    (hderiv : ∀ n, ratOrder (ratFuncDeriv P) (q (n + 1)) = 0)
    (hbq : ∀ n, ratOrder b (q (n + 1)) = 0) (hcq : ∀ n, 0 ≤ ratOrder c (q (n + 1)))
    (hinj : Function.Injective q) (hpole : ratOrder a (q 0) < 0) : False := by
  have horbit : ∀ n : ℕ, ratOrder a (q n) < 0 := by
    intro n
    induction n with
    | zero => exact hpole
    | succ n ih =>
        exact ratAffineTransport_pole_backward hP ha hb hderiv0 heq (hden n) (hderiv n) (hbq n)
          (hcq n) (by rw [hstep n]; exact ih)
  have hsub : Set.range q ⊆ {z : K | ratOrder a z ≠ 0} := by
    rintro _ ⟨n, rfl⟩
    exact ne_of_lt (horbit n)
  exact (Set.infinite_range_of_injective hinj) ((finite_support_ratOrder ha).subset hsub)

end GaloisForLFunctions.HTGeometry
