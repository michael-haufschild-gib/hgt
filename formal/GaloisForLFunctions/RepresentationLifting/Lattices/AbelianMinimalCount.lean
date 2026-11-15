import GaloisForLFunctions.RepresentationLifting.Lattices.AbelianMinimalVectors
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Exact minimum-vector counts for abelian augmentation squares

Ordered parallelograms correspond to distinct triples except when the fourth
label repeats the third. The exceptional triples are parametrized by a group
label and an element whose square is not one. This gives the exact norm-four
count `4m + 4N² = N³ + 2N + N|G[2]|`. For `N ≥ 4`, norm four is the minimum.
Thus equal-order groups have equal minimum-vector counts exactly when their
two-torsion subgroups have equal order.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
variable (G : Type) [CommGroup G] [Fintype G]

/-- Ordered triples of distinct group labels. -/
abbrev AbelianDistinctTriple := {t : G × G × G //
  t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}

private def distinctTripleEmbeddingEquiv : AbelianDistinctTriple G ≃ (Fin 3 ↪ G) where
  toFun t := ⟨![t.val.1, t.val.2.1, t.val.2.2], by
    intro i j h
    have ht := t.property
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩
  invFun e := ⟨(e 0, e 1, e 2),
    e.injective.ne (by decide), e.injective.ne (by decide), e.injective.ne (by decide)⟩
  left_inv t := rfl
  right_inv e := by ext i; fin_cases i <;> rfl

omit [CommGroup G] in
theorem abelianDistinctTriple_card : Nat.card (AbelianDistinctTriple G) =
    (Fintype.card G).descFactorial 3 := by
  rw [Nat.card_congr (distinctTripleEmbeddingEquiv G), Nat.card_eq_fintype_card,
    Fintype.card_embedding_eq, Fintype.card_fin]

/-- The triples for which the fourth parallelogram label repeats the third. -/
abbrev AbelianBadTriple := {t : AbelianDistinctTriple G //
  t.val.2.2 * t.val.2.2 = t.val.1 * t.val.2.1}

omit [Fintype G] in
private theorem badTriple_ratio_ne_one (t : AbelianBadTriple G) :
    (t.val.val.1 / t.val.val.2.2) * (t.val.val.1 / t.val.val.2.2) ≠ 1 := by
  intro h
  apply t.val.property.1
  have hh : t.val.val.1 * t.val.val.1 = t.val.val.2.2 * t.val.val.2.2 := by
    calc
      _ = ((t.val.val.1 / t.val.val.2.2) * (t.val.val.1 / t.val.val.2.2)) *
          (t.val.val.2.2 * t.val.val.2.2) := by
        simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = _ := by rw [h, one_mul]
  exact mul_left_cancel (hh.trans t.property)

private def badTripleEquiv : AbelianBadTriple G ≃
    G × {r : G // r*r ≠ 1} where
  toFun t := (t.val.val.2.2, ⟨t.val.val.1 / t.val.val.2.2, badTriple_ratio_ne_one G t⟩)
  invFun x := ⟨⟨(x.1*x.2.val, x.1/x.2.val, x.1), by
    have hne : x.2.val ≠ 1 := by intro h; exact x.2.property (by rw [h, one_mul])
    refine ⟨?_, ?_, ?_⟩
    · intro h
      apply x.2.property
      have hh : x.2.val = x.2.val⁻¹ := by
        change x.1 * x.2.val = x.1 / x.2.val at h
        rw [div_eq_mul_inv] at h
        exact mul_left_cancel h
      calc
        x.2.val * x.2.val = x.2.val * x.2.val⁻¹ := congrArg (x.2.val * ·) hh
        _ = 1 := mul_inv_cancel _
    · simpa using hne
    · simpa [div_eq_mul_inv] using hne⟩, by
      dsimp
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm]⟩
  left_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · simp
    · apply Prod.ext
      · apply (mul_left_cancel (a := t.val.val.1))
        change t.val.val.1 * (t.val.val.2.2 / (t.val.val.1 / t.val.val.2.2)) =
          t.val.val.1 * t.val.val.2.1
        rw [← t.property]
        simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
        calc
          _ = (t.val.val.1 * t.val.val.1⁻¹) * (t.val.val.2.2 * t.val.val.2.2) := by ac_rfl
          _ = _ := by rw [mul_inv_cancel, one_mul]
      · rfl
  right_inv x := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp


/-- Triples whose fourth parallelogram label is distinct from all three. -/
abbrev AbelianGoodTriple := {t : AbelianDistinctTriple G //
  t.val.2.2 * t.val.2.2 ≠ t.val.1 * t.val.2.1}

private def goodTripleParallelogramEquiv : AbelianGoodTriple G ≃ AbelianParallelogram G where
  toFun t := {
    a := t.val.val.1
    b := t.val.val.2.1
    c := t.val.val.2.2
    d := t.val.val.1 * t.val.val.2.1 / t.val.val.2.2
    hab := t.val.property.1
    hac := t.val.property.2.1
    had := by
      intro h
      have hh := congrArg (· * t.val.val.2.2) h
      rw [div_mul_cancel] at hh
      exact t.val.property.2.2 (mul_left_cancel hh).symm
    hbc := t.val.property.2.2
    hbd := by
      intro h
      have hh := congrArg (· * t.val.val.2.2) h
      rw [div_mul_cancel, mul_comm t.val.val.1 t.val.val.2.1] at hh
      exact t.val.property.2.1 (mul_left_cancel hh).symm
    hcd := by
      intro h
      apply t.property
      have hh := congrArg (· * t.val.val.2.2) h
      simpa only [div_mul_cancel] using hh
    product_eq := by simp [div_eq_mul_inv, mul_assoc, mul_left_comm] }
  invFun q := ⟨⟨(q.a, q.b, q.c), q.hab, q.hac, q.hbc⟩, by
    intro h
    exact q.hcd (mul_left_cancel (h.trans q.product_eq))⟩
  left_inv t := rfl
  right_inv q := by
    apply AbelianParallelogram.ext <;> try rfl
    change q.a * q.b / q.c = q.d
    rw [q.product_eq]
    simp [div_eq_mul_inv, mul_assoc]

/-- Two-torsion cardinality, including the identity. -/
def abelianTwoTorsionCard : ℕ := Nat.card {r : G // r*r = 1}

private theorem abelianBadTriple_card : Nat.card (AbelianBadTriple G) =
    Fintype.card G * (Fintype.card G - abelianTwoTorsionCard G) := by
  classical
  rw [Nat.card_congr (badTripleEquiv G), Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_subtype_compl]
  rw [abelianTwoTorsionCard, Nat.card_eq_fintype_card]

private theorem abelianTriple_partition :
    Nat.card (AbelianParallelogram G) + Nat.card (AbelianBadTriple G) =
      Nat.card (AbelianDistinctTriple G) := by
  classical
  letI := Fintype.ofFinite (AbelianParallelogram G)
  have h := Fintype.card_congr
    (Equiv.sumCompl (fun t : AbelianDistinctTriple G => t.val.2.2 * t.val.2.2 =
      t.val.1 * t.val.2.1))
  rw [Fintype.card_sum] at h
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card] at h
  have hg : Nat.card (AbelianGoodTriple G) = Nat.card (AbelianParallelogram G) :=
    Nat.card_congr (goodTripleParallelogramEquiv G)
  change Nat.card (AbelianBadTriple G) + Nat.card (AbelianGoodTriple G) = _ at h
  rw [hg] at h
  omega

/-- Counting framed minima separates the repeated-label triples exactly. -/
theorem abelianMinimalVector_count :
    4 * Nat.card (AbelianMinimalVector G) +
      Fintype.card G * (Fintype.card G - abelianTwoTorsionCard G) =
      (Fintype.card G).descFactorial 3 := by
  have h := abelianTriple_partition G
  rw [abelianParallelogram_card, abelianBadTriple_card, abelianDistinctTriple_card] at h
  exact h

private theorem descFactorial_three_cast (n : ℕ) :
    (n.descFactorial 3 : ℤ) = (n : ℤ) * ((n : ℤ)-1) * ((n : ℤ)-2) := by
  cases n with
  | zero => simp [Nat.descFactorial_succ]
  | succ n =>
    cases n with
    | zero => simp [Nat.descFactorial_succ]
    | succ n =>
      simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero,
        Nat.succ_sub_succ_eq_sub, mul_one,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring

/-- The exact norm-four count; these are the minimum vectors for group order
at least four. At fixed order, only two-torsion changes their number. -/
theorem abelianMinimalVector_count_polynomial :
    (4 : ℤ) * Nat.card (AbelianMinimalVector G) + 4 * (Fintype.card G : ℤ)^2 =
      (Fintype.card G : ℤ)^3 + 2 * Fintype.card G +
        Fintype.card G * abelianTwoTorsionCard G := by
  have ht : abelianTwoTorsionCard G ≤ Fintype.card G := by
    classical
    rw [abelianTwoTorsionCard, Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_le (fun r : G => r*r = 1)
  have h := congrArg (fun n : ℕ => (n : ℤ)) (abelianMinimalVector_count G)
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub ht,
    Nat.cast_ofNat, descFactorial_three_cast] at h
  nlinarith only [h]


/-- A subtraction-free natural-number form of the exact count. -/
theorem abelianMinimalVector_count_nat :
    4 * Nat.card (AbelianMinimalVector G) + 4 * (Fintype.card G)^2 =
      (Fintype.card G)^3 + 2 * Fintype.card G +
        Fintype.card G * abelianTwoTorsionCard G := by
  exact_mod_cast abelianMinimalVector_count_polynomial G

/-- At a fixed group order, the minimum-vector count determines and is determined
by the two-torsion count. -/
theorem abelianMinimalVector_card_eq_iff_twoTorsionCard_eq
    (H : Type) [CommGroup H] [Fintype H] (hcard : Fintype.card G = Fintype.card H) :
    Nat.card (AbelianMinimalVector G) = Nat.card (AbelianMinimalVector H) ↔
      abelianTwoTorsionCard G = abelianTwoTorsionCard H := by
  have hG := abelianMinimalVector_count_polynomial G
  have hH := abelianMinimalVector_count_polynomial H
  rw [hcard] at hG
  have hn : (Fintype.card H : ℤ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card H).ne'
  constructor
  · intro hm
    rw [hm] at hG
    have he : (Fintype.card H : ℤ) * abelianTwoTorsionCard G =
        (Fintype.card H : ℤ) * abelianTwoTorsionCard H := by linarith only [hG, hH]
    exact_mod_cast (mul_left_cancel₀ hn he)
  · intro ht
    rw [ht] at hG
    have he : (Nat.card (AbelianMinimalVector G) : ℤ) =
        Nat.card (AbelianMinimalVector H) := by linarith only [hG, hH]
    exact_mod_cast he

#print axioms abelianMinimalVector_count
#print axioms abelianMinimalVector_count_polynomial
#print axioms abelianMinimalVector_card_eq_iff_twoTorsionCard_eq

end GaloisForLFunctions.RepresentationLifting
