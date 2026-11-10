import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheFrobeniusGraphsMeetInThePrimes
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheArchimedeanFibreOfTheSquare
import GaloisForLFunctions.SurfaceOfSpecZ.ThePointCountOfSpecZ
import GaloisForLFunctions.SurfaceOfSpecZ.TheArchimedeanPlaceIsNotToric

/-!
# Weil's off-diagonal is contacts plus jets

`SurfaceOfSpecZ` defines the intersection number of two Frobenius graphs of `Spec ℤ` from Weil's
form, `Γ_m · Γ_n = (m + n) − √(mn) W(m, n)`, and computes it as an archimedean term plus a gcd-twisted
intersection of torsion orbits on `ℙ¹_ℤ`. This file identifies both terms inside the sequence ring
of the arithmetic square. Write `m = g a`, `n = g b` with `a < b` coprime.

* **The prime part is the contact of the reduced graphs** (`gcdTwist_mul_orbitIntersection_reduced`):

    `G(m, n) · I(m, n) = g · log #(ℤ/J(a, b))`.

  The factor `g` is the degree of the common Frobenius (`F_g V_g = g`); the reduced graphs meet in
  `Spec 𝔽_p` if `a = 1` and `b` is a power of `p`, and nowhere otherwise
  (`graphIdeal_eq_top_of_coprime`).
* **The archimedean part is the trace of `V_m F_n` on the jets**
  (`frobeniusIntersection_eq_tsum_jets_add_contacts`):

    `Γ_m · Γ_n = Σ_{j ≥ 0} m^{1+2j} n^{−2j} + g · log #(ℤ/J(a, b))`.

* **On divisible pairs the intersection is the Verschiebung of the point count**
  (`frobeniusIntersection_mul_eq_mul_pointCount`): `Γ_m · Γ_{mk} = m · N(k)`.
* **No Witt Verschiebung carries Weil's numbers**
  (`not_exists_projection_verschiebung_frobeniusIntersection`): a family of maps with the projection
  formula vanishes at the pair `(2, 3)`, where `Γ_2 · Γ_3 = 18/5`. The contacts are supported on the
  divisibility order of the degrees; the jets are not. The two fibres of the square share the
  Frobenius and not the Verschiebung.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open GaloisForLFunctions.SurfaceOfSpecZ GaloisForLFunctions.ArithmeticEffectivityTheory

/-- Reduced graphs of coprime degrees `a, b ≥ 2` are disjoint. -/
theorem graphIdeal_eq_top_of_coprime {a b : ℕ+} (h : Nat.Coprime a b) (ha : 1 < a) (hb : 1 < b) :
    graphIdeal a b = ⊤ := by
  have ha1 : (a : ℕ) ≠ 1 := fun h1 => ha.ne' (PNat.eq (by simpa using h1))
  have hb1 : (b : ℕ) ≠ 1 := fun h1 => hb.ne' (PNat.eq (by simpa using h1))
  obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd ha1
  obtain ⟨q, hq, hqb⟩ := Nat.exists_prime_and_dvd hb1
  have hpb : ¬ p ∣ (b : ℕ) := fun hpb => by
    have := Nat.dvd_gcd hpa hpb
    rw [h.gcd_eq_one] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hqa : ¬ q ∣ (a : ℕ) := fun hqa => by
    have := Nat.dvd_gcd hqa hqb
    rw [h.gcd_eq_one] at this
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  have hpq : p ≠ q := fun e => hpb (e ▸ hqb)
  refine graphIdeal_eq_top_of_two_primes hp hq hpq ?_ ?_
  · rw [Nat.factorization_eq_zero_of_not_dvd hpb]
    exact (hp.factorization_pos_of_dvd a.ne_zero hpa).ne'
  · rw [Nat.factorization_eq_zero_of_not_dvd hqa]
    exact (hq.factorization_pos_of_dvd b.ne_zero hqb).ne

/-- The order of an empty intersection is `1`. -/
theorem log_card_quotient_eq_zero_of_eq_top {I : Ideal ℤ} (h : I = ⊤) :
    Real.log (Nat.card (ℤ ⧸ I)) = 0 := by
  haveI : Subsingleton (ℤ ⧸ I) := Ideal.Quotient.subsingleton_iff.mpr h
  rw [Nat.card_of_subsingleton (0 : ℤ ⧸ I), Nat.cast_one, Real.log_one]

/-- **The prime part of Weil's off-diagonal is the contact of the reduced graphs**, with the
degree `g` of the common Frobenius as multiplicity. -/
theorem gcdTwist_mul_orbitIntersection_reduced (g : ℕ+) {a b : ℕ+} (h : Nat.Coprime a b)
    (hab : a < b) :
    gcdTwist ((g : ℕ) * a) ((g : ℕ) * b) * orbitIntersection ((g : ℕ) * a) ((g : ℕ) * b) =
      ((g : ℕ) : ℝ) * Real.log (Nat.card (ℤ ⧸ graphIdeal a b)) := by
  have hab' : (a : ℕ) < (b : ℕ) := hab
  have hne : (g : ℕ) * a ≠ (g : ℕ) * b := (Nat.mul_lt_mul_of_pos_left hab' g.pos).ne
  have h1 : ¬ (g : ℕ) * b ∣ (g : ℕ) * a := fun hd =>
    absurd (Nat.le_of_dvd a.pos (Nat.dvd_of_mul_dvd_mul_left g.pos hd)) (not_le.mpr hab')
  rw [orbitIntersection_eq (Nat.mul_pos g.pos a.pos) (Nat.mul_pos g.pos b.pos) hne, if_neg h1]
  by_cases ha : a = 1
  · subst ha
    have hb : (1 : ℕ+) < b := hab
    have hφ : (0 : ℝ) < Nat.totient (g : ℕ) := by exact_mod_cast Nat.totient_pos.mpr g.pos
    rw [PNat.one_coe, mul_one, if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ g.pos,
      gcdTwist_eq, Nat.gcd_eq_left (dvd_mul_right _ _), log_card_quotient_graphIdeal_one hb]
    field_simp
  · have ha1 : 1 < a := by
      have hpos := a.pos
      have hne : (a : ℕ) ≠ 1 := fun h1 => ha (PNat.eq (by simpa using h1))
      have : (1 : ℕ) < (a : ℕ) := by omega
      exact this
    have h2 : ¬ (g : ℕ) * a ∣ (g : ℕ) * b := fun hd => by
      have hd' : (a : ℕ) ∣ (b : ℕ) := Nat.dvd_of_mul_dvd_mul_left g.pos hd
      have := Nat.dvd_gcd dvd_rfl hd'
      rw [h.gcd_eq_one, Nat.dvd_one] at this
      exact ha (PNat.eq (by simpa using this))
    rw [if_neg h2, mul_zero,
      log_card_quotient_eq_zero_of_eq_top (graphIdeal_eq_top_of_coprime h ha1 (ha1.trans hab)),
      mul_zero]

/-- **Weil's off-diagonal on a reduced pair**: the jets of the archimedean fibre plus `g` times the
contact of the reduced graphs in the arithmetic square. -/
theorem frobeniusIntersection_reduced (g : ℕ+) {a b : ℕ+} (h : Nat.Coprime a b) (hab : a < b) :
    frobeniusIntersection ((g : ℕ) * a) ((g : ℕ) * b) =
      ((g : ℕ) : ℝ) * (a : ℕ) / (1 - (((a : ℕ) : ℝ) / (b : ℕ)) ^ 2) +
        ((g : ℕ) : ℝ) * Real.log (Nat.card (ℤ ⧸ graphIdeal a b)) := by
  have hG : (0 : ℝ) < ((g : ℕ) : ℝ) := by exact_mod_cast g.pos
  have hA : (0 : ℝ) < ((a : ℕ) : ℝ) := by exact_mod_cast a.pos
  have hAB : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  have hlt : (g : ℕ) * a < (g : ℕ) * b := Nat.mul_lt_mul_of_pos_left hab g.pos
  have hle : ((g : ℕ) : ℝ) * (a : ℕ) ≤ ((g : ℕ) : ℝ) * (b : ℕ) := by nlinarith
  have hmin : min ((((g : ℕ) * (a : ℕ) : ℕ)) : ℝ) ((((g : ℕ) * (b : ℕ) : ℕ)) : ℝ) =
      ((g : ℕ) : ℝ) * (a : ℕ) := by push_cast; exact min_eq_left hle
  have hmax : max ((((g : ℕ) * (a : ℕ) : ℕ)) : ℝ) ((((g : ℕ) * (b : ℕ) : ℕ)) : ℝ) =
      ((g : ℕ) : ℝ) * (b : ℕ) := by push_cast; exact max_eq_right hle
  rw [frobeniusIntersection_eq (Nat.mul_pos g.pos a.pos) (Nat.mul_pos g.pos b.pos) hlt.ne,
    gcdTwist_mul_orbitIntersection_reduced g h hab, hmin, hmax, mul_div_mul_left _ _ hG.ne']

/-- **Contacts plus jets.** For `m = g a < n = g b`, `a, b` coprime:
`Γ_m · Γ_n = Σ_j m^{1+2j} n^{−2j} + g · log #(ℤ/J(a, b))`, the trace of `V_m F_n` on the jets plus
the contact of the reduced graphs. -/
theorem frobeniusIntersection_eq_tsum_jets_add_contacts (g : ℕ+) {a b : ℕ+} (h : Nat.Coprime a b)
    (hab : a < b) :
    frobeniusIntersection ((g : ℕ) * a) ((g : ℕ) * b) =
      ∑' j : ℕ, ((((g * a : ℕ+) : ℕ) : ℝ) * ((((g * a : ℕ+) : ℕ) : ℝ) ^ 2) ^ j) *
          (((((g * b : ℕ+) : ℕ) : ℝ)) ^ 2)⁻¹ ^ j +
        ((g : ℕ) : ℝ) * Real.log (Nat.card (ℤ ⧸ graphIdeal a b)) := by
  have hG : (0 : ℝ) < ((g : ℕ) : ℝ) := by exact_mod_cast g.pos
  have hlt : g * a < g * b := by
    have : ((g * a : ℕ+) : ℕ) < ((g * b : ℕ+) : ℕ) := by
      rw [PNat.mul_coe, PNat.mul_coe]
      exact Nat.mul_lt_mul_of_pos_left hab g.pos
    exact this
  rw [frobeniusIntersection_reduced g h hab, (hasSum_trace_verschiebung_shift_jets hlt).tsum_eq,
    PNat.mul_coe, PNat.mul_coe, Nat.cast_mul, Nat.cast_mul, mul_div_mul_left _ _ hG.ne']

/-- **On divisible pairs Weil's intersection is the Verschiebung of the point count**:
`Γ_m · Γ_{mk} = m · N(k)`. -/
theorem frobeniusIntersection_mul_eq_mul_pointCount {m k : ℕ} (hm : 0 < m) (hk : 2 ≤ k) :
    frobeniusIntersection m (m * k) = (m : ℝ) * pointCount k := by
  obtain ⟨G, rfl⟩ : ∃ G : ℕ+, (G : ℕ) = m := ⟨⟨m, hm⟩, rfl⟩
  obtain ⟨K, rfl⟩ : ∃ K : ℕ+, (K : ℕ) = k := ⟨⟨k, by omega⟩, rfl⟩
  have hK : (1 : ℕ+) < K := by
    have : (1 : ℕ) < (K : ℕ) := by omega
    exact this
  have hK2 : (2 : ℝ) ≤ ((K : ℕ) : ℝ) := by exact_mod_cast hk
  have h := frobeniusIntersection_reduced G (a := 1) (b := K) (Nat.coprime_one_left _) hK
  rw [PNat.one_coe, mul_one, Nat.cast_one, mul_one, log_card_quotient_graphIdeal_one hK] at h
  rw [h, pointCount_eq hk]
  have h1 : ((K : ℕ) : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have h2 : ((K : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- **No Witt Verschiebung carries Weil's off-diagonal.** A family of maps with the projection
formula vanishes at the degrees `(2, 3)`, where Weil's intersection number is `18/5`. -/
theorem not_exists_projection_verschiebung_frobeniusIntersection :
    ¬ ∃ (V : ℕ+ → (ℕ+ → ℝ) → (ℕ+ → ℝ)) (c : ℕ+ → ℝ),
      (∀ (k : ℕ+) (y : ℕ+ → ℝ), V k ((((k : ℕ) : ℝ)) • y) = (((k : ℕ) : ℝ)) • V k y) ∧
      (∀ (k : ℕ+) (y : ℕ+ → ℝ), V k (y * shift k (orbitSeq k)) = V k y * orbitSeq k) ∧
      ∀ m n : ℕ+, m < n → V m c n = frobeniusIntersection m n := by
  rintro ⟨V, c, hsmul, hproj, hW⟩
  have h0 : V 2 c 3 = 0 :=
    eq_zero_of_projection_formula 2 (V 2) c (hsmul 2 c) (hproj 2 c) (by decide)
  have h1 := hW 2 3 (by decide)
  rw [h0] at h1
  have h2 : frobeniusIntersection ((2 : ℕ+) : ℕ) ((3 : ℕ+) : ℕ) = 18 / 5 :=
    frobeniusIntersection_two_three
  rw [h2] at h1
  norm_num at h1

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
