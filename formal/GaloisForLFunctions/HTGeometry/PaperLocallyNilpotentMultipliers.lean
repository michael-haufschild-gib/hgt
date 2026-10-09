import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.FactorialClosure

/-!
# Invariant multipliers of locally nilpotent derivations

The source's highest-nonzero-iterate product formula excludes nonconstant
semi-invariants. It gives the exact criterion for
multiplying a terminating derivation by an arbitrary ring element.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- The source top-iterate product formula forces every divisible derivative to vanish. -/
theorem paperLND_fixed_of_dvd_apply [IsDomain A] [CharZero A]
    (D : Derivation k A A) (hD : IsLocallyNilpotent D) (a : A)
    (ha : a ∣ D a) : D a = 0 := by
  by_cases hzero : a = 0
  · simp [hzero]
  obtain ⟨b, hb⟩ := ha
  by_cases hbzero : b = 0
  · simpa [hbzero] using hb
  obtain ⟨m, hm, hm'⟩ := exists_last_nonzero_iterate D hzero (hD a)
  obtain ⟨n, hn, hn'⟩ := exists_last_nonzero_iterate D hbzero (hD b)
  have hz : (D : A → A)^[m + n] (D a) = 0 := by
    rw [← Function.iterate_succ_apply]
    exact derivation_iterate_eq_zero_of_le D hm' (by omega)
  rw [hb, derivation_iterate_top_mul D a b m n hm' hn', nsmul_eq_mul] at hz
  have hchoose : ((m + n).choose m : A) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : m ≤ m + n)).ne'
  exact False.elim ((mul_ne_zero hchoose (mul_ne_zero hm hn)) hz)

/-- An invariant coefficient factors out of every iterate, with the expected power. -/
theorem paperLND_invariant_smul_iterate
    (D : Derivation k A A) (q : A) (hq : D q = 0) (m : ℕ) (a : A) :
    ((q • D : Derivation k A A) : A → A)^[m] a = q ^ m * (D : A → A)^[m] a := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, Derivation.smul_apply, smul_eq_mul,
      Derivation.leibniz, Derivation.leibniz_pow, hq]
    simp only [smul_zero, smul_eq_mul, mul_zero, add_zero]
    rw [Function.iterate_succ_apply', pow_succ]
    ring

/-- Every invariant multiple of a locally nilpotent derivation is locally nilpotent. -/
theorem paperLND_invariant_smul (D : Derivation k A A) (hD : IsLocallyNilpotent D)
    (q : A) (hq : D q = 0) : IsLocallyNilpotent (q • D) := by
  intro a
  obtain ⟨m, hm⟩ := hD a
  refine ⟨m, ?_⟩
  rw [paperLND_invariant_smul_iterate D q hq, hm, mul_zero]

/-- The invariant-coefficient condition is both necessary and sufficient. -/
theorem paperLND_smul_iff [IsDomain A] [CharZero A]
    (D : Derivation k A A) (hD : IsLocallyNilpotent D) (q : A) :
    IsLocallyNilpotent (q • D) ↔ D q = 0 := by
  constructor
  · intro h
    have hq : (q • D : Derivation k A A) q = 0 :=
      paperLND_fixed_of_dvd_apply (q • D) h q ⟨D q, rfl⟩
    change q * D q = 0 at hq
    rcases mul_eq_zero.mp hq with hq | hq
    · simp [hq]
    · exact hq
  · exact paperLND_invariant_smul D hD q

end GaloisForLFunctions.HTGeometry
