import GaloisForLFunctions.HTGeometry.MonomialTailFibreCount
import GaloisForLFunctions.HTGeometry.HorizonTruncationCancel

/-!
# The fibre over an observation with arbitrary critical tails

The fibre count over a monomial observation extends to every observation whose two tails have
exactly the critical degrees, with arbitrary coefficients: the target of the factorization is
`1 + U V`, a polynomial of degree `m + n` with nonzero constant term, and once it is separable its
monic divisors of degree `m` number the critical binomial multiplicity.

Separability is the only thing the coefficients of the tails enter through.  It holds for the
monomial tails of the previous module, so the family of observations with the critical count is at
least as large as the whole open set where `1 + U V` is squarefree, rather than the two-parameter
family of monomials.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-! ## The target of the factorization -/

omit [CharZero K] [IsAlgClosed K] in
theorem natDegree_one_add_mul_of_coeff_ne_zero {m n : ℕ} (hL : 0 < m + n) {U V : K[X]}
    (hU : U.natDegree ≤ m) (hV : V.natDegree ≤ n) (hUm : U.coeff m ≠ 0)
    (hVn : V.coeff n ≠ 0) : (1 + U * V).natDegree = m + n := by
  have hUdeg : U.natDegree = m := natDegree_eq_of_le_of_coeff_ne_zero hU hUm
  have hVdeg : V.natDegree = n := natDegree_eq_of_le_of_coeff_ne_zero hV hVn
  have hU0 : U ≠ 0 := fun h => hUm (by rw [h]; simp)
  have hV0 : V ≠ 0 := fun h => hVn (by rw [h]; simp)
  have hlead : (U * V).leadingCoeff ≠ 0 := by
    rw [leadingCoeff_mul]
    exact mul_ne_zero (leadingCoeff_ne_zero.2 hU0) (leadingCoeff_ne_zero.2 hV0)
  have hmul : (U * V).natDegree = m + n := by
    rw [natDegree_mul hU0 hV0, hUdeg, hVdeg]
  have hone : (1 : K[X]).natDegree < (U * V).natDegree := by
    rw [natDegree_one, hmul]
    exact hL
  rw [natDegree_add_eq_right_of_natDegree_lt hone, hmul]

/-! ## The fibre -/

omit [CharZero K] in
/-- **The fibre over an observation with arbitrary tails of the critical degrees.**  Whenever the
target `1 + U V` is separable, its monic divisors of degree `m` number the critical binomial
multiplicity, exactly as for the monomial tails. -/
theorem nat_card_monic_divisors_criticalTails {m n : ℕ} (hL : 0 < m + n) {U V : K[X]}
    (hU : U.natDegree ≤ m) (hV : V.natDegree ≤ n) (hUm : U.coeff m ≠ 0)
    (hVn : V.coeff n ≠ 0) (hsep : (1 + U * V).Separable) :
    Nat.card {A : K[X] // A.Monic ∧ A ∣ (1 + U * V) ∧ A.natDegree = m}
      = criticalHorizonMultiplicity m n := by
  classical
  have hdeg : (1 + U * V).natDegree = m + n :=
    natDegree_one_add_mul_of_coeff_ne_zero hL hU hV hUm hVn
  have hne : (1 + U * V) ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    exact absurd hdeg.symm (Nat.ne_of_gt hL)
  set c : K := (1 + U * V).leadingCoeff with hc
  have hc0 : c ≠ 0 := leadingCoeff_ne_zero.2 hne
  set M : K[X] := (1 + U * V) * C c⁻¹ with hM
  have hMmonic : M.Monic := monic_mul_leadingCoeff_inv hne
  have hMdeg : M.natDegree = m + n := by
    rw [hM, natDegree_mul_C (inv_ne_zero hc0), hdeg]
  have hcc : (C c : K[X]) * C c⁻¹ = 1 := by
    rw [← C_mul, mul_inv_cancel₀ hc0, map_one]
  have hMsep : M.Separable := by
    obtain ⟨a, b, hab⟩ := hsep
    refine ⟨a * C c, b * C c, ?_⟩
    have hder : derivative M = derivative (1 + U * V) * C c⁻¹ := by
      rw [hM, derivative_mul, derivative_C, mul_zero, add_zero]
    rw [hM, hder]
    calc a * C c * ((1 + U * V) * C c⁻¹) + b * C c * (derivative (1 + U * V) * C c⁻¹)
        = (a * (1 + U * V) + b * derivative (1 + U * V)) * (C c * C c⁻¹) := by ring
      _ = 1 := by rw [hcc, mul_one]; exact hab
  have hdvd : ∀ A : K[X], A ∣ (1 + U * V) ↔ A ∣ M := by
    intro A
    rw [hM]
    exact ((isUnit_C.2 (inv_ne_zero hc0).isUnit).dvd_mul_right).symm
  have hcongr : Nat.card {A : K[X] // A.Monic ∧ A ∣ (1 + U * V) ∧ A.natDegree = m}
      = Nat.card {A : K[X] // A.Monic ∧ A ∣ M ∧ A.natDegree = m} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun A => ?_)
    rw [hdvd A]
  rw [hcongr, nat_card_monic_divisors hMmonic hMsep (IsAlgClosed.splits _) m, hMdeg,
    criticalHorizonMultiplicity]


/-! ## Long tails see only the first `L` coefficients -/

section Truncation

variable {R : Type*} [CommRing R]

/-- The low product changes by the observed difference of the tails. -/
theorem criticalLowProduct_sub (U U' V V' A B : R[X]) :
    criticalLowProduct U V A B - criticalLowProduct U' V' A B
      = A * (V - V') + (U - U') * B := by
  simp only [criticalLowProduct]
  ring

/-- **The truncated compatibility equation depends on the tails only modulo `X ^ L`.**  An
observation with a long tail imposes the same condition as its truncation, so the fibre of a tail
of any length is the fibre of a tail of degree below the horizon. -/
theorem dvd_criticalLowProduct_sub_one_congr {L : ℕ} {U U' V V' A B : R[X]}
    (hU : (X : R[X]) ^ L ∣ (U - U')) (hV : (X : R[X]) ^ L ∣ (V - V')) :
    (X : R[X]) ^ L ∣ (criticalLowProduct U V A B - 1)
      ↔ (X : R[X]) ^ L ∣ (criticalLowProduct U' V' A B - 1) := by
  have hdiff : (X : R[X]) ^ L ∣ (criticalLowProduct U V A B - criticalLowProduct U' V' A B) := by
    rw [criticalLowProduct_sub]
    exact dvd_add (Dvd.dvd.mul_left hV A) (Dvd.dvd.mul_right hU B)
  constructor
  · intro h
    have := dvd_sub h hdiff
    simpa using this
  · intro h
    have := dvd_add h hdiff
    simpa using this

/-- **The fibre over an observation is the fibre over its truncation.** -/
theorem fibre_eq_of_dvd_sub {L : ℕ} {U U' V V' : R[X]}
    (hU : (X : R[X]) ^ L ∣ (U - U')) (hV : (X : R[X]) ^ L ∣ (V - V')) (m n : ℕ) :
    {AB : R[X] × R[X] | AB.1.degree < (m : WithBot ℕ) ∧ AB.2.degree < (n : WithBot ℕ) ∧
        (X : R[X]) ^ L ∣ (criticalLowProduct U V AB.1 AB.2 - 1)}
      = {AB : R[X] × R[X] | AB.1.degree < (m : WithBot ℕ) ∧ AB.2.degree < (n : WithBot ℕ) ∧
        (X : R[X]) ^ L ∣ (criticalLowProduct U' V' AB.1 AB.2 - 1)} := by
  ext ⟨A, B⟩
  simp only [Set.mem_setOf_eq, and_congr_right_iff]
  intro _ _
  exact dvd_criticalLowProduct_sub_one_congr hU hV

end Truncation


/-! ## The second component is determined by the first -/

section Elimination

variable {F : Type*} [Field F]

/-- The compatibility equation is affine-linear in the second unknown once the first is fixed. -/
theorem criticalLowProduct_eq_affine (U V A B : F[X]) :
    criticalLowProduct U V A B - 1 = (U + A) * B + (A * V - 1) := by
  simp only [criticalLowProduct]
  ring

/-- **For a fixed first component the second is unique.**  The equation is affine-linear in `B`
with leading factor `U + A`, which is invertible at the origin, so two solutions differ by a
polynomial divisible by `X ^ L` and of degree below the horizon — hence by nothing.

This is the elimination step: the fibre injects into the space of first components, cutting the
count down from `L` unknowns to `m`. -/
theorem fibre_snd_unique {L n : ℕ} (hn : n ≤ L) {U V A B B' : F[X]}
    (hUA : (U + A).coeff 0 ≠ 0)
    (hB : (X : F[X]) ^ L ∣ (criticalLowProduct U V A B - 1))
    (hB' : (X : F[X]) ^ L ∣ (criticalLowProduct U V A B' - 1))
    (hdB : B.degree < (n : WithBot ℕ)) (hdB' : B'.degree < (n : WithBot ℕ)) :
    B = B' := by
  have hsub : (X : F[X]) ^ L ∣ (U + A) * (B - B') := by
    have h := dvd_sub hB hB'
    rwa [criticalLowProduct_eq_affine, criticalLowProduct_eq_affine,
      show (U + A) * B + (A * V - 1) - ((U + A) * B' + (A * V - 1))
        = (U + A) * (B - B') from by ring] at h
  have hdvd : (X : F[X]) ^ L ∣ (B - B') := dvd_of_mul_dvd_of_coeff_zero_ne_zero hUA hsub
  by_contra hne
  have hBB : B - B' ≠ 0 := sub_ne_zero.2 hne
  have hdeg : ((X : F[X]) ^ L).degree ≤ (B - B').degree := Polynomial.degree_le_of_dvd hdvd hBB
  rw [Polynomial.degree_X_pow] at hdeg
  have hlt : (B - B').degree < (L : WithBot ℕ) :=
    lt_of_lt_of_le (lt_of_le_of_lt (Polynomial.degree_sub_le B B')
      (max_lt hdB hdB')) (by exact_mod_cast hn)
  exact absurd (lt_of_le_of_lt hdeg hlt) (lt_irrefl _)

end Elimination


/-! ## The fibre, and its injection into the first components -/

section Fibre

variable {F : Type*} [Field F]

/-- The fibre of the truncated compatibility equation over an observation. -/
def criticalFibre (U V : F[X]) (m n L : ℕ) : Set (F[X] × F[X]) :=
  {AB | AB.1.degree < (m : WithBot ℕ) ∧ AB.2.degree < (n : WithBot ℕ) ∧
    (X : F[X]) ^ L ∣ (criticalLowProduct U V AB.1 AB.2 - 1)}

/-- **On the fibre the first component is automatically invertible at the origin**, as soon as the
target is.  If it were not, the constant term of the equation would force `1 + U V` to vanish at
the origin. -/
theorem coeff_zero_ne_zero_of_mem_criticalFibre {U V A B : F[X]} {L : ℕ} (hL : 0 < L)
    (hT : (1 + U * V).coeff 0 ≠ 0)
    (h : (X : F[X]) ^ L ∣ (criticalLowProduct U V A B - 1)) : (U + A).coeff 0 ≠ 0 := by
  intro hUA
  have hX : (X : F[X]) ∣ (criticalLowProduct U V A B - 1) :=
    dvd_trans (dvd_pow_self (X : F[X]) (Nat.ne_of_gt hL)) h
  have hc : (criticalLowProduct U V A B - 1).coeff 0 = 0 := by
    have := Polynomial.X_dvd_iff.1 hX
    exact this
  rw [criticalLowProduct_eq_affine] at hc
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.mul_coeff_zero,
    Polynomial.coeff_one_zero, hUA, zero_mul, zero_add] at hc
  apply hT
  have hA : A.coeff 0 = -(U.coeff 0) := by
    have : (U + A).coeff 0 = U.coeff 0 + A.coeff 0 := Polynomial.coeff_add _ _ _
    rw [hUA] at this
    linear_combination -this
  simp only [Polynomial.coeff_add, Polynomial.mul_coeff_zero, Polynomial.coeff_one_zero]
  rw [hA] at hc
  linear_combination -hc

/-- **The fibre injects into the space of first components.**  Combining the uniqueness of the
second component with the automatic invertibility above: a point of the fibre is determined by its
first component alone, so the count is a count in `m` unknowns rather than `L`. -/
theorem criticalFibre_fst_injOn {U V : F[X]} {m n L : ℕ} (hL : 0 < L) (hn : n ≤ L)
    (hT : (1 + U * V).coeff 0 ≠ 0) :
    Set.InjOn Prod.fst (criticalFibre U V m n L) := by
  rintro ⟨A, B⟩ ⟨-, hB, hAB⟩ ⟨A', B'⟩ ⟨-, hB', hAB'⟩ hfst
  simp only at hfst
  subst hfst
  have hUA : (U + A).coeff 0 ≠ 0 := coeff_zero_ne_zero_of_mem_criticalFibre hL hT hAB
  exact Prod.ext rfl (fibre_snd_unique hn hUA hAB hAB' hB hB')

end Fibre


/-! ## The condition on a first component is a linear solvability -/

section Solvability

variable {F : Type*} [Field F]

/-- **A first component extends to a fibre point exactly when a linear congruence is solvable.**
The unknown second component enters the equation only through multiplication by `U + A`, so
extending `A` means writing the target `1 - A V` as a multiple of `U + A` modulo `X ^ L` by a
polynomial of degree below `n`. -/
theorem exists_snd_iff_linear_solvable {U V A : F[X]} {n L : ℕ} :
    (∃ B : F[X], B.degree < (n : WithBot ℕ) ∧
        (X : F[X]) ^ L ∣ (criticalLowProduct U V A B - 1))
      ↔ ∃ B : F[X], B.degree < (n : WithBot ℕ) ∧
        (X : F[X]) ^ L ∣ ((U + A) * B - (1 - A * V)) := by
  constructor
  · rintro ⟨B, hB, hdvd⟩
    refine ⟨B, hB, ?_⟩
    rwa [criticalLowProduct_eq_affine,
      show (U + A) * B + (A * V - 1) = (U + A) * B - (1 - A * V) from by ring] at hdvd
  · rintro ⟨B, hB, hdvd⟩
    refine ⟨B, hB, ?_⟩
    rwa [criticalLowProduct_eq_affine,
      show (U + A) * B + (A * V - 1) = (U + A) * B - (1 - A * V) from by ring]

/-- **The fibre is the graph of the extension over the solvable first components.** -/
theorem criticalFibre_fst_image {U V : F[X]} {m n L : ℕ} :
    Prod.fst '' (criticalFibre U V m n L)
      = {A : F[X] | A.degree < (m : WithBot ℕ) ∧
          ∃ B : F[X], B.degree < (n : WithBot ℕ) ∧
            (X : F[X]) ^ L ∣ ((U + A) * B - (1 - A * V))} := by
  ext A
  constructor
  · rintro ⟨⟨A', B⟩, ⟨hA, hB, hdvd⟩, rfl⟩
    exact ⟨hA, (exists_snd_iff_linear_solvable).1 ⟨B, hB, hdvd⟩⟩
  · rintro ⟨hA, hsol⟩
    obtain ⟨B, hB, hdvd⟩ := (exists_snd_iff_linear_solvable (U := U) (V := V) (A := A)).2 hsol
    exact ⟨⟨A, B⟩, ⟨hA, hB, hdvd⟩, rfl⟩

end Solvability


/-! ## The solvability is a linear range membership -/

section RangeCriterion

variable {F : Type*} [Field F]

/-- Multiplication by a polynomial, followed by truncation below the horizon, as an `F`-linear
map into the truncated ring. -/
noncomputable def mulTruncMap (G : F[X]) (L : ℕ) :
    F[X] →ₗ[F] (F[X] ⧸ Ideal.span {(X : F[X]) ^ L}) :=
  (Ideal.Quotient.mkₐ F (Ideal.span {(X : F[X]) ^ L})).toLinearMap ∘ₗ LinearMap.mulLeft F G

@[simp]
theorem mulTruncMap_apply (G : F[X]) (L : ℕ) (B : F[X]) :
    mulTruncMap G L B = Ideal.Quotient.mk (Ideal.span {(X : F[X]) ^ L}) (G * B) := rfl

/-- Divisibility by the horizon power is vanishing in the truncated ring. -/
theorem quot_eq_iff_dvd {L : ℕ} (p q : F[X]) :
    Ideal.Quotient.mk (Ideal.span {(X : F[X]) ^ L}) p
        = Ideal.Quotient.mk (Ideal.span {(X : F[X]) ^ L}) q
      ↔ (X : F[X]) ^ L ∣ (p - q) := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]

/-- **The first components that extend are exactly those whose target lies in the image of
multiplication by `U + A`.**  This is the elimination in linear-algebra form: the second component
ranges over an `n`-dimensional space, the residues form an `L`-dimensional space, and a first
component extends precisely when the target is in the range. -/
theorem exists_snd_iff_mem_range {U V A : F[X]} {n L : ℕ} :
    (∃ B : F[X], B.degree < (n : WithBot ℕ) ∧
        (X : F[X]) ^ L ∣ ((U + A) * B - (1 - A * V)))
      ↔ Ideal.Quotient.mk (Ideal.span {(X : F[X]) ^ L}) (1 - A * V)
          ∈ Submodule.map (mulTruncMap (U + A) L) (Polynomial.degreeLT F n) := by
  constructor
  · rintro ⟨B, hB, hdvd⟩
    refine ⟨B, Polynomial.mem_degreeLT.2 hB, ?_⟩
    rw [mulTruncMap_apply]
    exact (quot_eq_iff_dvd _ _).2 hdvd
  · rintro ⟨B, hB, hmap⟩
    refine ⟨B, Polynomial.mem_degreeLT.1 hB, ?_⟩
    rw [mulTruncMap_apply] at hmap
    exact (quot_eq_iff_dvd _ _).1 hmap

end RangeCriterion


/-! ## The elimination map has full column rank -/

section FullRank

variable {F : Type*} [Field F]

theorem mulTruncMap_eq_zero_iff {G : F[X]} {L : ℕ} (B : F[X]) :
    mulTruncMap G L B = 0 ↔ (X : F[X]) ^ L ∣ (G * B) := by
  rw [mulTruncMap_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

/-- **Multiplication by a polynomial invertible at the origin is injective below the horizon.**
So the elimination matrix has full column rank: its kernel meets the space of second components
only in zero, and the rank-drop locus therefore has the expected codimension. -/
theorem eq_zero_of_mulTruncMap_eq_zero {G B : F[X]} {n L : ℕ} (hn : n ≤ L)
    (hG : G.coeff 0 ≠ 0) (hB : B.degree < (n : WithBot ℕ)) (h : mulTruncMap G L B = 0) :
    B = 0 := by
  have hdvd : (X : F[X]) ^ L ∣ B :=
    dvd_of_mul_dvd_of_coeff_zero_ne_zero hG ((mulTruncMap_eq_zero_iff B).1 h)
  by_contra hne
  have hdeg : ((X : F[X]) ^ L).degree ≤ B.degree := Polynomial.degree_le_of_dvd hdvd hne
  rw [Polynomial.degree_X_pow] at hdeg
  exact absurd (lt_of_le_of_lt hdeg
    (lt_of_lt_of_le hB (by exact_mod_cast hn))) (lt_irrefl _)

/-- The same, as the statement that the kernel misses the second components. -/
theorem disjoint_ker_degreeLT {G : F[X]} {n L : ℕ} (hn : n ≤ L) (hG : G.coeff 0 ≠ 0) :
    Disjoint (LinearMap.ker (mulTruncMap G L)) (Polynomial.degreeLT F n) := by
  rw [Submodule.disjoint_def]
  intro B hker hdeg
  exact eq_zero_of_mulTruncMap_eq_zero hn hG (Polynomial.mem_degreeLT.1 hdeg)
    (LinearMap.mem_ker.1 hker)

end FullRank


/-! ## Range membership is degeneracy of the augmented system -/

section Augmented

variable {F : Type*} [Field F]

/-- **For an injective map, a vector lies in the range exactly when the augmented system is
degenerate.**  This is the bridge from the elimination to a determinantal condition: adjoining the
target as one more column, the enlarged system has a nontrivial relation precisely on the locus
where the target is hit. -/
theorem mem_range_iff_exists_nontrivial {W Z : Type*} [AddCommGroup W] [Module F W]
    [AddCommGroup Z] [Module F Z] {Λ : W →ₗ[F] Z} (hinj : Function.Injective Λ) (t : Z) :
    t ∈ LinearMap.range Λ ↔ ∃ (B : W) (c : F), ¬(B = 0 ∧ c = 0) ∧ Λ B = c • t := by
  constructor
  · rintro ⟨B, rfl⟩
    refine ⟨B, 1, ?_, by rw [one_smul]⟩
    rintro ⟨-, hc⟩
    exact one_ne_zero hc
  · rintro ⟨B, c, hne, heq⟩
    rcases eq_or_ne c 0 with rfl | hc
    · refine absurd ⟨?_, rfl⟩ hne
      have hzero : Λ B = 0 := by rw [heq, zero_smul]
      have := hinj (by rw [hzero, map_zero] : Λ B = Λ 0)
      exact this
    · refine ⟨c⁻¹ • B, ?_⟩
      rw [map_smul, heq, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- **The first components of the fibre are exactly the degenerate parameters.**  Combining the
range criterion with the injectivity of the elimination map: an `A` extends to a fibre point
exactly when the augmented system in `n + 1` unknowns has a nontrivial relation. -/
theorem exists_snd_iff_augmented_degenerate {U V A : F[X]} {n L : ℕ} (hn : n ≤ L)
    (hUA : (U + A).coeff 0 ≠ 0) :
    (∃ B : F[X], B.degree < (n : WithBot ℕ) ∧
        (X : F[X]) ^ L ∣ ((U + A) * B - (1 - A * V)))
      ↔ ∃ (B : Polynomial.degreeLT F n) (c : F), ¬((B : F[X]) = 0 ∧ c = 0) ∧
          mulTruncMap (U + A) L (B : F[X])
            = c • Ideal.Quotient.mk (Ideal.span {(X : F[X]) ^ L}) (1 - A * V) := by
  have hinj : Function.Injective
      ((mulTruncMap (U + A) L).comp (Polynomial.degreeLT F n).subtype) := by
    intro B B' hBB
    refine Subtype.ext ?_
    have hsub : mulTruncMap (U + A) L ((B : F[X]) - (B' : F[X])) = 0 := by
      simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hBB
      rw [map_sub, hBB, sub_self]
    have hdeg : ((B : F[X]) - (B' : F[X])).degree < (n : WithBot ℕ) :=
      lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
        (max_lt (Polynomial.mem_degreeLT.1 B.2) (Polynomial.mem_degreeLT.1 B'.2))
    have := eq_zero_of_mulTruncMap_eq_zero hn hUA hdeg hsub
    linarith [0] <;> skip
  sorry

end Augmented

end GaloisForLFunctions.HTGeometry
