import GaloisForLFunctions.RHTower.EisensteinHeckeFactorizationAtI

/-!
# Primitive coordinates for scalar charges on a square two-torus

The zero-spin condition is integer orthogonality. Nonzero winding fixes a
unique primitive direction and a positive winding scale; momentum lies on
that direction. The squared energy consequently factors into two sums of squares.
-/

open RHTower RHTower.HeckeFactorization

namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Zero-spin integer charges with nonzero winding. -/
abbrev ScalarCharge := {q : (ℤ × ℤ) × (ℤ × ℤ) //
  q.1.1 * q.2.1 + q.1.2 * q.2.2 = 0 ∧ q.2 ≠ (0, 0)}

private theorem primitive_parallel (a : D4BMPrimitiveIntegerPair) (m n : ℤ)
    (h : m * a.pair.2 - n * a.pair.1 = 0) :
    ∃! d : ℤ, m = d * a.pair.1 ∧ n = d * a.pair.2 := by
  have hb := Int.gcd_eq_gcd_ab a.pair.1 a.pair.2
  rw [a.primitive] at hb
  norm_cast at hb
  let A := Int.gcdA a.pair.1 a.pair.2
  let B := Int.gcdB a.pair.1 a.pair.2
  have hbez : a.pair.1 * A + a.pair.2 * B = 1 := hb.symm
  refine ⟨m * A + n * B, ⟨?_, ?_⟩, ?_⟩
  · linear_combination -m * hbez + B * h
  · linear_combination -n * hbez - A * h
  · intro d hd
    linear_combination -A * hd.1 - B * hd.2 - d * hbez

/-- A primitive direction, positive winding scale and integer momentum scale. -/
def scalarParameters (k : ℕ) (a : D4BMPrimitiveIntegerPair) (d : ℤ) :
    (ℤ × ℤ) × (ℤ × ℤ) :=
  ((d * a.pair.1, d * a.pair.2),
    (-((k : ℤ) + 1) * a.pair.2, ((k : ℤ) + 1) * a.pair.1))

theorem scalarParameters_mem (k : ℕ) (a : D4BMPrimitiveIntegerPair) (d : ℤ) :
    let q := scalarParameters k a d
    q.1.1 * q.2.1 + q.1.2 * q.2.2 = 0 ∧ q.2 ≠ (0, 0) := by
  refine ⟨by dsimp only [scalarParameters]; ring, ?_⟩
  intro h
  apply (gcdEquiv (k, a)).property
  apply Prod.ext
  · exact congrArg Prod.snd h
  · have hh := congrArg Prod.fst h
    change -((k : ℤ) + 1) * a.pair.2 = 0 at hh
    change ((k : ℤ) + 1) * a.pair.2 = 0
    linear_combination -hh

/-- Nonzero winding scalar charges have unique primitive coordinates. -/
theorem scalar_charge_parameters (q : ScalarCharge) :
    ∃! t : (ℕ × D4BMPrimitiveIntegerPair) × ℤ,
      q.val = scalarParameters t.1.1 t.1.2 t.2 := by
  let v : {p : ℤ × ℤ // p ≠ (0, 0)} :=
    ⟨(q.val.2.2, -q.val.2.1), by
      intro h
      apply q.property.2
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      exact Prod.ext (by simpa using h₂) h₁⟩
  rcases hka : gcdEquiv.symm v with ⟨k, a⟩
  have hg : gcdEquiv (k, a) = v := by
    rw [← hka]
    exact gcdEquiv.apply_symm_apply v
  have hw₁ : q.val.2.1 = -((k : ℤ) + 1) * a.pair.2 := by
    have hh := congrArg (fun p => p.val.2) hg
    change ((k : ℤ) + 1) * a.pair.2 = -q.val.2.1 at hh
    linear_combination hh
  have hw₂ : q.val.2.2 = ((k : ℤ) + 1) * a.pair.1 :=
    (congrArg (fun p => p.val.1) hg).symm
  have horth := q.property.1
  rw [hw₁, hw₂] at horth
  have hdet : q.val.1.1 * a.pair.2 - q.val.1.2 * a.pair.1 = 0 := by
    have hm : ((k : ℤ) + 1) *
        (q.val.1.1 * a.pair.2 - q.val.1.2 * a.pair.1) = 0 := by
      linear_combination -horth
    exact (mul_eq_zero.mp hm).resolve_left (by positivity)
  obtain ⟨d, hd, hdu⟩ := primitive_parallel a q.val.1.1 q.val.1.2 hdet
  have hq : q.val = scalarParameters k a d :=
    Prod.ext (Prod.ext hd.1 hd.2) (Prod.ext hw₁ hw₂)
  refine ⟨((k, a), d), hq, ?_⟩
  rintro ⟨b, e⟩ he
  have hbe : gcdEquiv b = gcdEquiv (k, a) := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun q => q.2.2) (he.symm.trans hq)
    · have hh := congrArg (fun q => q.2.1) (he.symm.trans hq)
      change -((b.1 : ℤ) + 1) * b.2.pair.2 = -((k : ℤ) + 1) * a.pair.2 at hh
      change ((b.1 : ℤ) + 1) * b.2.pair.2 = ((k : ℤ) + 1) * a.pair.2
      linear_combination -hh
  have hb := gcdEquiv.injective hbe
  subst b
  exact congrArg (fun z : ℤ => ((k, a), z))
    (hdu e ⟨congrArg (fun q => q.1.1) he, congrArg (fun q => q.1.2) he⟩)

/-- Exact reindexing of nonzero-winding scalar charges by primitive coordinates. -/
noncomputable def scalarChargeEquiv :
    ((ℕ × D4BMPrimitiveIntegerPair) × ℤ) ≃ ScalarCharge := by
  let f : ((ℕ × D4BMPrimitiveIntegerPair) × ℤ) → ScalarCharge := fun t =>
    ⟨scalarParameters t.1.1 t.1.2 t.2, scalarParameters_mem t.1.1 t.1.2 t.2⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    obtain ⟨t, _, ht⟩ := scalar_charge_parameters (f a)
    exact (ht a rfl).trans (ht b (congrArg Subtype.val hab)).symm
  · intro q
    obtain ⟨t, ht, _⟩ := scalar_charge_parameters q
    exact ⟨t, Subtype.ext ht.symm⟩

/-- The scalar energy separates into winding-momentum and primitive factors. -/
theorem scalarParameters_energy (k : ℕ) (a : D4BMPrimitiveIntegerPair) (d : ℤ) :
    let q := scalarParameters k a d
    q.1.1 ^ 2 + q.1.2 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 =
      (((k : ℤ) + 1) ^ 2 + d ^ 2) * (a.pair.1 ^ 2 + a.pair.2 ^ 2) := by
  dsimp only [scalarParameters]
  ring

end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.scalar_charge_parameters
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.scalarParameters_energy
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.scalarChargeEquiv
