import GaloisForLFunctions.KodairaParshinAbc.TheConductorOfAPrimitiveTriple
import GaloisForLFunctions.RHTower.HyperellipticDescent
import GaloisForLFunctions.RHTower.EllipticCurveHasseBound

/-!
# Weil bounds for the quintic curve and the Frey curves

Two curves carry the uniform `abc` inequality: the genus-two curve `C : y² + y = x⁵`, whose map
`y : C → P¹` of degree five is totally ramified over `0, -1, ∞`, and the Frey curves
`E_{a,b} : y² = x(x - a)(x + b)` of the triples `a + b = c`.  Over finite fields both satisfy the
Riemann hypothesis, through the hyperelliptic Weil bound
(`RHTower.Hyperelliptic.abs_card_points_sub_le_oddHyperelliptic`) and Hasse's theorem
(`RHTower.EllipticHasse.abs_natCard_point_sub_le`):

* for every finite field `E` with `char E ∉ {2, 5}`, `Y = 2y + 1` identifies the affine points of
  `C` with those of `Y² = 4x⁵ + 1`, a squarefree quintic, so
  `|#{y² + y = x⁵}(E) - |E|| ≤ 4 √|E|`;
* for coprime `a, b` and every prime `p ∤ 2ab(a+b)` — every prime outside the bad set of the
  Frey model, which is `2` together with the conductor primes of the triple — the reduction of
  `E_{a,b}` modulo `p` is elliptic and `|#E_{a,b}(F_p) - (p + 1)| ≤ 2 √p`.
-/

noncomputable section

open Polynomial Finset

namespace GaloisForLFunctions.KodairaParshinAbc

/-! ## The quintic curve `y² + y = x⁵` -/

section Quintic

variable {E : Type*} [Field E]

/-- The quintic `4x⁵ + 1` of the model `Y² = 4x⁵ + 1` of `y² + y = x⁵`. -/
def quinticModel : E[X] := C 4 * X ^ 5 + 1

theorem natDegree_quinticModel (h2 : (2 : E) ≠ 0) : (quinticModel : E[X]).natDegree = 5 := by
  have h4 : (4 : E) ≠ 0 := by
    rw [show (4 : E) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  unfold quinticModel
  rw [← C_1, natDegree_add_C, natDegree_C_mul_X_pow 5 4 h4]

/-- `4x⁵ + 1` is separable, hence squarefree, when `5 ≠ 0`:
`1 = (4x⁵ + 1) - (x/5) · 20x⁴`. -/
theorem squarefree_quinticModel (h5 : (5 : E) ≠ 0) : Squarefree (quinticModel : E[X]) := by
  apply Polynomial.Separable.squarefree
  rw [Polynomial.separable_def]
  refine ⟨1, -(C (5⁻¹ : E) * X), ?_⟩
  have h45 : (5⁻¹ : E) * (4 * 5) = 4 := by field_simp
  unfold quinticModel
  rw [derivative_add, derivative_one, derivative_C_mul_X_pow, add_zero,
    show (5 - 1 : ℕ) = 4 from rfl]
  have e1 : C (5⁻¹ : E) * X * (C (4 * ((5 : ℕ) : E)) * X ^ 4) =
      C ((5⁻¹ : E) * (4 * 5)) * X ^ 5 := by
    simp only [Nat.cast_ofNat, map_mul]
    ring
  rw [h45] at e1
  linear_combination -e1

/-- `Y = 2y + 1` identifies the affine points of `y² + y = x⁵` with those of `Y² = 4x⁵ + 1`. -/
theorem card_quintic_eq [Fintype E] [DecidableEq E] (h2 : (2 : E) ≠ 0) :
    (univ.filter fun q : E × E => q.2 ^ 2 + q.2 = q.1 ^ 5).card =
      (univ.filter fun q : E × E => q.2 ^ 2 = aeval q.1 (quinticModel : E[X])).card := by
  refine Finset.card_bij' (fun q _ => (q.1, 2 * q.2 + 1)) (fun q _ => (q.1, (q.2 - 1) / 2))
    ?_ ?_ ?_ ?_
  · intro q hq
    simp only [mem_filter, mem_univ, true_and] at hq ⊢
    simp only [quinticModel, map_add, map_mul, aeval_C, map_pow, aeval_X, map_one,
      Algebra.algebraMap_self, RingHom.id_apply]
    linear_combination 4 * hq
  · intro q hq
    simp only [mem_filter, mem_univ, true_and] at hq ⊢
    simp only [quinticModel, map_add, map_mul, aeval_C, map_pow, aeval_X, map_one,
      Algebra.algebraMap_self, RingHom.id_apply] at hq
    field_simp
    linear_combination hq
  · intro q _
    ext
    · rfl
    · simp only
      field_simp
      ring
  · intro q _
    ext
    · rfl
    · simp only
      field_simp
      ring

/-- **The Weil bound for `y² + y = x⁵`.**  Over every finite field `E` of characteristic
different from `2` and `5`, `|#{(x, y) ∈ E² : y² + y = x⁵} - |E|| ≤ 4 √|E|`. -/
theorem abs_card_quintic_sub_le [Fintype E] [DecidableEq E] (h2 : ringChar E ≠ 2)
    (h5 : (5 : E) ≠ 0) :
    |((univ.filter fun q : E × E => q.2 ^ 2 + q.2 = q.1 ^ 5).card : ℝ) - Fintype.card E| ≤
      4 * Real.sqrt (Fintype.card E) := by
  have h2' : (2 : E) ≠ 0 := Ring.two_ne_zero h2
  have hdeg := natDegree_quinticModel h2'
  rw [card_quintic_eq h2']
  have h := RHTower.Hyperelliptic.abs_card_points_sub_le_oddHyperelliptic h2
    (squarefree_quinticModel h5) (by rw [hdeg]; decide) E
  rw [hdeg] at h
  simpa using h

end Quintic

/-! ## The Frey curves modulo good primes -/

theorem freyCurve_map_Δ (a b : ℤ) (p : ℕ) :
    ((freyCurve a b).map (Int.castRingHom (ZMod p))).Δ =
      ((16 * (a * b * (a + b)) ^ 2 : ℤ) : ZMod p) := by
  rw [WeierstrassCurve.map_Δ, freyCurve_Δ]
  rfl

/-- **Good reduction away from `2` and the conductor.**  If `p` is an odd prime not dividing
`ab(a+b)`, the Frey curve is elliptic modulo `p`. -/
theorem freyCurve_map_isElliptic {a b : ℤ} {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (habc : ¬ (p : ℤ) ∣ a * b * (a + b)) :
    ((freyCurve a b).map (Int.castRingHom (ZMod p))).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, freyCurve_map_Δ]
  intro h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  rcases hpz.dvd_mul.mp h with h16 | hY
  · have h2 : (p : ℤ) ∣ 2 ^ 4 := by norm_num; exact h16
    have h2' : p ∣ 2 := Int.natCast_dvd_natCast.mp (hpz.dvd_of_dvd_pow h2)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h2')
  · exact habc (hpz.dvd_of_dvd_pow hY)

/-- **Hasse's bound for the Frey curves.**  For every odd prime `p ∤ ab(a+b)`,
`|#E_{a,b}(F_p) - (p + 1)| ≤ 2 √p`. -/
theorem abs_card_freyCurve_sub_le {a b : ℤ} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (habc : ¬ (p : ℤ) ∣ a * b * (a + b)) :
    |(Nat.card ((freyCurve a b).map (Int.castRingHom (ZMod p))).toAffine.Point : ℝ) - (p + 1)| ≤
      2 * Real.sqrt p := by
  haveI := freyCurve_map_isElliptic hp2 habc
  have h := RHTower.EllipticHasse.abs_natCard_point_sub_le
    ((freyCurve a b).map (Int.castRingHom (ZMod p))) (by rwa [ZMod.ringChar_zmod_n])
  simpa [ZMod.card] using h

end GaloisForLFunctions.KodairaParshinAbc
