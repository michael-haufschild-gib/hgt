import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerNormalization
import GaloisForLFunctions.HTGeometry.RamificationIndexLowerBound
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# The totally ramified origin of a Kummer cover

In the normalization of `z^(Q+1)=c y(1-y^(b+1))^R`, the origin has exactly
one prime above it, with ramification index `Q+1` and residue degree one.
Modulo a prime power, nilpotence of `y` makes `1-y^(b+1)` invertible.
The defining equation then gives the lower ramification bound; the
fundamental degree identity forces equality, uniqueness, and residue degree.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial

/-- A simple Kummer zero lies in the full root-order power of every prime above it. -/
theorem mem_prime_pow_of_kummer_equation {A : Type*} [CommRing A]
    {P : Ideal A} (hP : P.IsPrime) {x z c : A} (hc : IsUnit c)
    (b R N : ℕ) (hx : x ∈ P) (heq : z ^ N = c * x * (1 - x ^ (b + 1)) ^ R) :
    x ∈ P ^ N := by
  have hz : z ∈ P := hP.mem_of_pow_mem N (by
    rw [heq]
    exact P.mul_mem_right _ (P.mul_mem_left _ hx))
  let f := Ideal.Quotient.mk (P ^ N)
  have hxN : f x ^ N = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hx N)
  have hzN : f z ^ N = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hz N)
  have hnil : IsNilpotent (f x ^ (b + 1)) := ⟨N, by
    rw [← pow_mul, Nat.mul_comm (b + 1) N, pow_mul, hxN, zero_pow (Nat.succ_ne_zero b)]⟩
  have hunit := hnil.isUnit_one_sub.pow R
  have he : f c * f x * (1 - f x ^ (b + 1)) ^ R = 0 := by
    have h := congrArg f heq
    simp only [map_pow, map_mul, map_sub, map_one] at h
    exact h.symm.trans hzN
  exact Ideal.Quotient.eq_zero_iff_mem.mp
    ((hc.map f).mul_right_eq_zero.mp (hunit.mul_left_eq_zero.mp he))


variable {K : Type*} [Field K]
private theorem origin_ne_bot : (Ideal.span {(X : K[X])}) ≠ ⊥ :=
  mt Ideal.span_singleton_eq_bot.mp X_ne_zero

private theorem origin_maximal : (Ideal.span {(X : K[X])}).IsMaximal :=
  ((Ideal.span_singleton_prime X_ne_zero).mpr prime_X).isMaximal origin_ne_bot

variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

private theorem baseMap_injective : Function.Injective
    (algebraMap (SquareConstantField p s)[X] (SquareKummerNormalization p s c b R)) :=
  Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance

/-- The extended origin ideal lies in the full covering-degree power of every prime above it. -/
theorem squareKummer_origin_map_le_pow
    (P : Ideal (SquareKummerNormalization p s c b R)) [hP : P.IsPrime]
    [P.LiesOver (Ideal.span {(X : (SquareConstantField p s)[X])})] :
    (Ideal.span {(X : (SquareConstantField p s)[X])}).map
      (algebraMap _ (SquareKummerNormalization p s c b R)) ≤ P ^ (p ^ (s + 1) + 1) := by
  let f := algebraMap (SquareConstantField p s)[X] (SquareKummerNormalization p s c b R)
  apply Ideal.map_le_iff_le_comap.mpr
  rw [Ideal.span_le, Set.singleton_subset_iff]
  change f X ∈ P ^ (p ^ (s + 1) + 1)
  have hx : f X ∈ P := (Ideal.mem_of_liesOver P _ X).mp (Ideal.mem_span_singleton_self _)
  apply mem_prime_pow_of_kummer_equation hP
    (((Units.isUnit c).map C).map f) b R (p ^ (s + 1) + 1) hx
    (z := squareKummerIntegralRoot p s c b R)
  simpa only [kummerBranch, map_mul, map_pow, map_sub, map_one] using
    squareKummerIntegralRoot_pow p s c b R

/-- Every prime above the origin is totally ramified. -/
theorem squareKummer_origin_ramification
    (P : Ideal (SquareKummerNormalization p s c b R)) [hP : P.IsPrime]
    [P.LiesOver (Ideal.span {(X : (SquareConstantField p s)[X])})] :
    (Ideal.span {(X : (SquareConstantField p s)[X])}).ramificationIdx' P =
      p ^ (s + 1) + 1 := by
  letI : (Ideal.span {(X : (SquareConstantField p s)[X])}).IsMaximal := origin_maximal
  let f := algebraMap (SquareConstantField p s)[X] (SquareKummerNormalization p s c b R)
  have hf := baseMap_injective p s c b R
  have hx : f X ∈ P := (Ideal.mem_of_liesOver P _ X).mp (Ideal.mem_span_singleton_self _)
  have hxn : f X ≠ 0 := (map_ne_zero_iff f hf).mpr X_ne_zero
  have hP0 : P ≠ ⊥ := by intro h; exact hxn (by simpa only [h, Ideal.mem_bot] using hx)
  have hp0 : (Ideal.span {(X : (SquareConstantField p s)[X])}).map f ≠ ⊥ := by
    rw [ne_eq, Ideal.map_eq_bot_iff_le_ker,
      (RingHom.injective_iff_ker_eq_bot f).mp hf, le_bot_iff]
    exact origin_ne_bot
  apply le_antisymm
  · have h := Ideal.sum_ramification_inertia (SquareKummerNormalization p s c b R)
      (FractionRing (SquareConstantField p s)[X]) (SquareKummerField p s c b R)
      (origin_ne_bot (K := SquareConstantField p s))
    have hm : P ∈ IsDedekindDomain.primesOverFinset
        (Ideal.span {(X : (SquareConstantField p s)[X])}) (SquareKummerNormalization p s c b R) :=
      (IsDedekindDomain.mem_primesOverFinset_iff origin_ne_bot _).mpr ⟨hP, inferInstance⟩
    have hi := Ideal.inertiaDeg'_ne_zero (Ideal.span {(X : (SquareConstantField p s)[X])}) P
    have hle := Finset.single_le_sum (fun Q _ => Nat.zero_le
      ((Ideal.span {(X : (SquareConstantField p s)[X])}).ramificationIdx' Q *
        (Ideal.span {(X : (SquareConstantField p s)[X])}).inertiaDeg' Q)) hm
    rw [h, kummerBranchField_finrank] at hle
    exact (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hi)).trans hle
  · exact GaloisForLFunctions.HTGeometry.le_ramificationIdx'_of_map_le_pow hP hP0 hp0
      (squareKummer_origin_map_le_pow p s c b R P)


/-- The fundamental degree identity leaves one prime of residue degree one. -/
private theorem squareKummer_origin_singleton :
    ∃ P : Ideal (SquareKummerNormalization p s c b R),
      IsDedekindDomain.primesOverFinset (Ideal.span {(X : (SquareConstantField p s)[X])})
        (SquareKummerNormalization p s c b R) = {P} ∧
      (Ideal.span {(X : (SquareConstantField p s)[X])}).inertiaDeg' P = 1 := by
  classical
  letI : (Ideal.span {(X : (SquareConstantField p s)[X])}).IsMaximal := origin_maximal
  let T := IsDedekindDomain.primesOverFinset (Ideal.span {(X : (SquareConstantField p s)[X])})
    (SquareKummerNormalization p s c b R)
  let f : Ideal (SquareKummerNormalization p s c b R) → ℕ :=
    (Ideal.span {(X : (SquareConstantField p s)[X])}).inertiaDeg'
  have hsum : (p ^ (s + 1) + 1) * ∑ P ∈ T, f P = p ^ (s + 1) + 1 := by
    rw [Finset.mul_sum]
    have h := Ideal.sum_ramification_inertia (SquareKummerNormalization p s c b R)
      (FractionRing (SquareConstantField p s)[X]) (SquareKummerField p s c b R)
      (origin_ne_bot (K := SquareConstantField p s))
    rw [kummerBranchField_finrank] at h
    refine (Finset.sum_congr rfl fun P hP => ?_).trans h
    obtain ⟨hprime, hover⟩ := (IsDedekindDomain.mem_primesOverFinset_iff origin_ne_bot _).mp hP
    letI := hprime
    letI := hover
    rw [squareKummer_origin_ramification p s c b R P]
  have hsum1 : ∑ P ∈ T, f P = 1 := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos (p ^ (s + 1)))
    simpa only [mul_one] using hsum
  have hcard : T.card ≤ 1 := by
    suffices T.card ≤ ∑ P ∈ T, f P by exact this.trans_eq hsum1
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro P hP
    obtain ⟨hprime, hover⟩ := (IsDedekindDomain.mem_primesOverFinset_iff origin_ne_bot _).mp hP
    letI := hover
    exact Nat.pos_of_ne_zero (Ideal.inertiaDeg'_ne_zero _ P)
  have hnonempty : T.Nonempty := by
    by_contra hn
    have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Finset.sum_empty] at hsum1
    omega
  have hc : T.card = 1 := Nat.le_antisymm hcard (Finset.card_pos.mpr hnonempty)
  obtain ⟨P, hP⟩ := Finset.card_eq_one.mp hc
  exact ⟨P, hP, by simpa only [hP, Finset.sum_singleton] using hsum1⟩

/-- There is exactly one prime of the normalization above the origin. -/
theorem squareKummer_origin_unique :
    ∃! P : Ideal (SquareKummerNormalization p s c b R),
      P.IsPrime ∧ P.LiesOver (Ideal.span {(X : (SquareConstantField p s)[X])}) := by
  classical
  letI : (Ideal.span {(X : (SquareConstantField p s)[X])}).IsMaximal := origin_maximal
  obtain ⟨P, hP, _⟩ := squareKummer_origin_singleton p s c b R
  have hm : P ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span {(X : (SquareConstantField p s)[X])}) (SquareKummerNormalization p s c b R) := by
    rw [hP]; exact Finset.mem_singleton_self _
  refine ⟨P, (IsDedekindDomain.mem_primesOverFinset_iff origin_ne_bot _).mp hm, ?_⟩
  intro Q hQ
  have hQm := (IsDedekindDomain.mem_primesOverFinset_iff origin_ne_bot _).mpr hQ
  rw [hP, Finset.mem_singleton] at hQm
  exact hQm

/-- The residue field above the origin has degree one over the base residue field. -/
theorem squareKummer_origin_inertia
    (P : Ideal (SquareKummerNormalization p s c b R)) [hP : P.IsPrime]
    [P.LiesOver (Ideal.span {(X : (SquareConstantField p s)[X])})] :
    (Ideal.span {(X : (SquareConstantField p s)[X])}).inertiaDeg' P = 1 := by
  classical
  letI : (Ideal.span {(X : (SquareConstantField p s)[X])}).IsMaximal := origin_maximal
  obtain ⟨Q, hQ, hf⟩ := squareKummer_origin_singleton p s c b R
  have hm := (IsDedekindDomain.mem_primesOverFinset_iff
    (origin_ne_bot (K := SquareConstantField p s))
    (SquareKummerNormalization p s c b R)).mpr ⟨hP, inferInstance⟩
  rw [hQ, Finset.mem_singleton] at hm
  exact hm.symm ▸ hf

/-- The unique actual prime of the normalization above the origin. -/
def squareKummerOriginIdeal : Ideal (SquareKummerNormalization p s c b R) :=
  (squareKummer_origin_unique p s c b R).choose

/-- The chosen origin ideal is prime. -/
instance squareKummerOriginIdeal_prime : (squareKummerOriginIdeal p s c b R).IsPrime :=
  (squareKummer_origin_unique p s c b R).choose_spec.1.1

/-- The chosen origin ideal contracts to the origin of the polynomial line. -/
instance squareKummerOriginIdeal_liesOver :
    (squareKummerOriginIdeal p s c b R).LiesOver
      (Ideal.span {(X : (SquareConstantField p s)[X])}) :=
  (squareKummer_origin_unique p s c b R).choose_spec.1.2

/-- The origin prime is nonzero, since it contains the nonzero base coordinate. -/
theorem squareKummerOriginIdeal_ne_bot : squareKummerOriginIdeal p s c b R ≠ ⊥ := by
  intro h
  have hx := (Ideal.mem_of_liesOver (squareKummerOriginIdeal p s c b R)
    (Ideal.span {(X : (SquareConstantField p s)[X])}) X).mp (Ideal.mem_span_singleton_self _)
  have hzero : algebraMap (SquareConstantField p s)[X] (SquareKummerNormalization p s c b R)
      X = 0 := by simpa only [h, Ideal.mem_bot] using hx
  exact X_ne_zero ((baseMap_injective p s c b R) (hzero.trans (map_zero _).symm))

/-- The origin prime is maximal in the Dedekind normalization. -/
instance squareKummerOriginIdeal_maximal : (squareKummerOriginIdeal p s c b R).IsMaximal :=
  (squareKummerOriginIdeal_prime p s c b R).isMaximal (squareKummerOriginIdeal_ne_bot p s c b R)

/-- The canonical origin prime has ramification index equal to the covering degree. -/
theorem squareKummerOriginIdeal_ramification :
    (Ideal.span {(X : (SquareConstantField p s)[X])}).ramificationIdx'
      (squareKummerOriginIdeal p s c b R) = p ^ (s + 1) + 1 :=
  squareKummer_origin_ramification p s c b R _

/-- The canonical origin prime has residue degree one. -/
theorem squareKummerOriginIdeal_inertia :
    (Ideal.span {(X : (SquareConstantField p s)[X])}).inertiaDeg'
      (squareKummerOriginIdeal p s c b R) = 1 :=
  squareKummer_origin_inertia p s c b R _

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
