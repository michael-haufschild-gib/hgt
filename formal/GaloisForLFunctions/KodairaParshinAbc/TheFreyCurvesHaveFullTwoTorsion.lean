import GaloisForLFunctions.KodairaParshinAbc.TheFreyCurvesCarryAMertensBudget

/-!
# The Frey curves have full two-torsion

The Frey curve `y² = x(x - a)(x + b)` of a triple `a + b = c` has its three roots `0, a, -b`
rational, so at every good prime `p` (odd, `p ∤ ab(a+b)`) its reduction has the full two-torsion
`{O, (0,0), (a,0), (-b,0)}`.  The two-torsion subgroup of a finite abelian group of exponent two has
order a power of `2`; containing four elements, it has order divisible by `4`, and Lagrange gives

  `4 ∣ #E_{a,b}(F_p)`,  i.e.  `a_p ≡ p + 1 (mod 4)`

for the Frobenius trace of the Frey curve (`frobeniusTrace`, as in the Mertens budget).
-/

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine

namespace GaloisForLFunctions.KodairaParshinAbc

/-! ## Groups of exponent two -/

/-- The two-torsion subgroup `{P | P + P = 0}` of an abelian group. -/
def twoTorsionSubgroup (G : Type*) [AddCommGroup G] : AddSubgroup G where
  carrier := {P | P + P = 0}
  add_mem' := by
    intro P Q hP hQ
    simp only [Set.mem_setOf_eq] at hP hQ ⊢
    calc P + Q + (P + Q) = (P + P) + (Q + Q) := by abel
      _ = 0 := by rw [hP, hQ, add_zero]
  zero_mem' := by simp
  neg_mem' := by
    intro P hP
    simp only [Set.mem_setOf_eq] at hP ⊢
    rw [← neg_add, hP, neg_zero]

/-- A finite group of exponent two has order a power of `2` (Cauchy). -/
theorem card_eq_two_pow_of_exponent_two {G : Type*} [AddGroup G] [Finite G]
    (h : ∀ x : G, x + x = 0) : ∃ k : ℕ, Nat.card G = 2 ^ k := by
  classical
  haveI := Fintype.ofFinite G
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := G)).ne' fun {d} hd hdvd => ?_⟩
  haveI := Fact.mk hd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card d (by rwa [← Nat.card_eq_fintype_card (α := G)])
  have h2 : addOrderOf x ∣ 2 := addOrderOf_dvd_of_nsmul_eq_zero (by rw [two_nsmul]; exact h x)
  rw [hx] at h2
  exact (Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp h2

/-- A finite group of exponent two with at least four elements has order divisible by `4`. -/
theorem four_dvd_card_of_exponent_two {G : Type*} [AddGroup G] [Finite G]
    (h : ∀ x : G, x + x = 0) (h4 : 4 ≤ Nat.card G) : 4 ∣ Nat.card G := by
  obtain ⟨k, hk⟩ := card_eq_two_pow_of_exponent_two h
  rw [hk] at h4 ⊢
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    interval_cases k <;> simp at h4
  exact (pow_dvd_pow 2 hk2 : 2 ^ 2 ∣ 2 ^ k)

/-! ## The Frey curve modulo a good prime -/

variable {p : ℕ} [hp : Fact p.Prime]

/-- The reduction of the Frey curve modulo `p`. -/
def freyModP (a b : ℤ) (p : ℕ) : WeierstrassCurve (ZMod p) :=
  (freyCurve a b).map (Int.castRingHom (ZMod p))

theorem freyModP_equation_root (a b : ℤ) {x : ZMod p}
    (hx : x = 0 ∨ x = (a : ZMod p) ∨ x = -(b : ZMod p)) :
    (freyModP a b p).toAffine.Equation x 0 := by
  rw [equation_iff]
  simp only [freyModP, freyCurve, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, eq_intCast,
    Int.cast_sub, Int.cast_neg, Int.cast_mul, Int.cast_zero]
  rcases hx with rfl | rfl | rfl <;> ring

theorem freyModP_Δ_ne_zero {a b : ℤ} (hp2 : p ≠ 2) (habc : ¬ (p : ℤ) ∣ a * b * (a + b)) :
    (freyModP a b p).Δ ≠ 0 := by
  haveI : (freyModP a b p).IsElliptic := freyCurve_map_isElliptic hp2 habc
  exact (WeierstrassCurve.isUnit_Δ (W := freyModP a b p)).ne_zero

theorem freyModP_point_finite {a b : ℤ} (hp2 : p ≠ 2) (habc : ¬ (p : ℤ) ∣ a * b * (a + b)) :
    Finite (freyModP a b p).toAffine.Point := by
  haveI : (freyModP a b p).IsElliptic := freyCurve_map_isElliptic hp2 habc
  haveI : Finite (WithZero {xy : ZMod p × ZMod p //
      (freyModP a b p).toAffine.Equation xy.1 xy.2}) := inferInstanceAs (Finite (Option _))
  exact Finite.of_equiv _ (pointEquiv (freyModP a b p).toAffine).symm

/-- **Full two-torsion at a good prime**: `4 ∣ #E_{a,b}(F_p)` for every odd `p ∤ ab(a+b)`. -/
theorem four_dvd_card_freyModP {a b : ℤ} (hp2 : p ≠ 2) (habc : ¬ (p : ℤ) ∣ a * b * (a + b)) :
    4 ∣ Nat.card (freyModP a b p).toAffine.Point := by
  classical
  haveI := freyModP_point_finite hp2 habc
  have hΔ := freyModP_Δ_ne_zero hp2 habc
  have hns : ∀ {x : ZMod p}, (x = 0 ∨ x = (a : ZMod p) ∨ x = -(b : ZMod p)) →
      (freyModP a b p).toAffine.Nonsingular x 0 := fun hx =>
    (equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp (freyModP_equation_root a b hx)
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have ha : (a : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun h => habc (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _)
  have hb : (b : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun h => habc (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _)
  have hc : (a : ZMod p) + b ≠ 0 := by
    rw [← Int.cast_add, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun h => habc (dvd_mul_of_dvd_right h _)
  set T₀ : (freyModP a b p).toAffine.Point := Point.some 0 0 (hns (Or.inl rfl))
  set Tₐ : (freyModP a b p).toAffine.Point := Point.some (a : ZMod p) 0 (hns (Or.inr (Or.inl rfl)))
  set T_b : (freyModP a b p).toAffine.Point := Point.some (-(b : ZMod p)) 0 (hns (Or.inr (Or.inr rfl)))
  have hneg : ∀ x : ZMod p, (0 : ZMod p) = (freyModP a b p).toAffine.negY x 0 := by
    intro x
    simp [negY, freyModP, freyCurve]
  have htor : ∀ P ∈ ({0, T₀, Tₐ, T_b} : Finset (freyModP a b p).toAffine.Point),
      P ∈ twoTorsionSubgroup (freyModP a b p).toAffine.Point := by
    intro P hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    show P + P = 0
    rcases hP with rfl | rfl | rfl | rfl
    · exact add_zero 0
    · exact Point.add_self_of_Y_eq (hneg 0)
    · exact Point.add_self_of_Y_eq (hneg _)
    · exact Point.add_self_of_Y_eq (hneg _)
  have hne : ∀ {x y : ZMod p} {hx : (freyModP a b p).toAffine.Nonsingular x 0}
      {hy : (freyModP a b p).toAffine.Nonsingular y 0}, x ≠ y → Point.some x 0 hx ≠ Point.some y 0 hy :=
    fun hxy h => hxy (Point.some.inj h).1
  have hcard4 : ({0, T₀, Tₐ, T_b} : Finset (freyModP a b p).toAffine.Point).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
    · exact hne (fun h => hc (by linear_combination h))
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hne (Ne.symm ha), hne (fun h => hb (by linear_combination h))⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(Point.some_ne_zero _).symm, (Point.some_ne_zero _).symm,
        (Point.some_ne_zero _).symm⟩
  set H := twoTorsionSubgroup (freyModP a b p).toAffine.Point
  have hH4 : 4 ≤ Nat.card H := by
    rw [← hcard4]
    have hsub : (({0, T₀, Tₐ, T_b} : Finset _) : Set (freyModP a b p).toAffine.Point) ⊆ H :=
      fun P hP => htor P hP
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at this
  have hHexp : ∀ x : H, x + x = 0 := fun x => Subtype.ext x.2
  exact (four_dvd_card_of_exponent_two hHexp hH4).trans (AddSubgroup.card_addSubgroup_dvd_card H)

/-- **`a_p ≡ p + 1 (mod 4)`** for the Frey curve at every good odd prime. -/
theorem freyModP_trace_mod_four {a b : ℤ} (hp2 : p ≠ 2) (habc : ¬ (p : ℤ) ∣ a * b * (a + b)) :
    (4 : ℤ) ∣ (p : ℤ) + 1 - frobeniusTrace (freyModP a b p) := by
  have h := four_dvd_card_freyModP hp2 habc
  rw [frobeniusTrace, show (p : ℤ) + 1 - ((p : ℤ) + 1 - Nat.card (freyModP a b p).toAffine.Point) =
    Nat.card (freyModP a b p).toAffine.Point by ring]
  exact_mod_cast h

end GaloisForLFunctions.KodairaParshinAbc
