import GaloisForLFunctions.HTGeometry.PureFibreTangentIso
import GaloisForLFunctions.HTGeometry.CriticalTargetGenericSeparable

/-!
# A transverse channel adds no ambiguity

A source of projective dimension larger than one carries, besides the longitudinal coordinate whose
two horizon tails are counted by the critical multiplicity, a transverse coordinate `u` observed at
the first horizon and `u / p` observed at the second, where `p` is the longitudinal jet.  The
compatibility between the two transverse observations is `u = p (u/p)`, which is *linear* in the
unknown low parts: it is a square convolution system of size `m + n`.

When that system is nonsingular the transverse lift of a longitudinal solution is unique, so a
transverse channel multiplies the count by one.  Nonsingularity is not automatic — for `p = 1` the
system is degenerate — but it holds for an explicit unipotent jet, so the nonsingular locus is not
empty and the critical count is stable under adding projective dimensions.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] {m n : ℕ}

/-! ## The transverse convolution system -/

/-- **The transverse compatibility map.**  The low parts of the transverse coordinate and of its
quotient by the longitudinal jet enter linearly, coupled by the convolution with that jet. -/
noncomputable def transverseDifferential (p : K[X]) (m n L : ℕ) :
    fibreTangentSpace K m n →ₗ[K] degreeLT K L where
  toFun q := ⟨((q.1 : K[X]) - p * (q.2 : K[X])) %ₘ X ^ L, by
    rw [mem_degreeLT]
    have hlt := degree_modByMonic_lt ((q.1 : K[X]) - p * (q.2 : K[X])) (monic_X_pow (R := K) L)
    rwa [degree_X_pow] at hlt⟩
  map_add' q r := by
    refine Subtype.ext ?_
    show (((q.1 : K[X]) + (r.1 : K[X])) - p * ((q.2 : K[X]) + (r.2 : K[X]))) %ₘ X ^ L = _
    rw [show ((q.1 : K[X]) + (r.1 : K[X])) - p * ((q.2 : K[X]) + (r.2 : K[X]))
        = ((q.1 : K[X]) - p * (q.2 : K[X])) + ((r.1 : K[X]) - p * (r.2 : K[X])) by ring,
      Polynomial.add_modByMonic]
    rfl
  map_smul' c q := by
    refine Subtype.ext ?_
    show ((c • (q.1 : K[X])) - p * (c • (q.2 : K[X]))) %ₘ X ^ L = _
    rw [show (c • (q.1 : K[X])) - p * (c • (q.2 : K[X]))
        = c • ((q.1 : K[X]) - p * (q.2 : K[X])) by
          simp only [Polynomial.smul_eq_C_mul]; ring,
      Polynomial.smul_modByMonic]
    rfl

theorem transverseDifferential_eq_zero_iff {p : K[X]} {L : ℕ} {q : fibreTangentSpace K m n} :
    transverseDifferential p m n L q = 0 ↔
      (X : K[X]) ^ L ∣ (q.1 : K[X]) - p * (q.2 : K[X]) := by
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd (monic_X_pow (R := K) L)]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-! ## An explicit nonsingular longitudinal jet -/

/-- **The transverse system of a unipotent jet is nonsingular.**  The compatibility of the two
transverse observations forces the exact identity `a = (1 + t^m) b` below the horizon, and the
degree of the right side exceeds the depth of the left unless both sides vanish. -/
theorem injective_transverseDifferential (hm : 0 < m) :
    Function.Injective (transverseDifferential (1 + X ^ m : K[X]) m n (m + n)) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro q hq
  have hdvd : (X : K[X]) ^ (m + n) ∣ (q.1 : K[X]) - (1 + X ^ m) * (q.2 : K[X]) :=
    transverseDifferential_eq_zero_iff.1 hq
  have h1 : ((q.1 : K[X])).degree < (m : ℕ) := mem_degreeLT.1 q.1.2
  have h2 : ((q.2 : K[X])).degree < (n : ℕ) := mem_degreeLT.1 q.2.2
  have hp : (1 + X ^ m : K[X]).degree = (m : ℕ) := by
    rw [Polynomial.degree_add_eq_right_of_degree_lt, Polynomial.degree_X_pow]
    rw [Polynomial.degree_one, Polynomial.degree_X_pow]
    exact_mod_cast hm
  have hp0 : (1 + X ^ m : K[X]) ≠ 0 := by
    intro h
    rw [h, Polynomial.degree_zero] at hp
    simp at hp
  have hlt : ((q.1 : K[X]) - (1 + X ^ m) * (q.2 : K[X])).degree < ((m + n : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
    · exact lt_of_lt_of_le h1 (by exact_mod_cast Nat.le_add_right m n)
    · refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
      rw [hp]
      calc ((m : ℕ) : WithBot ℕ) + ((q.2 : K[X])).degree
          < ((m : ℕ) : WithBot ℕ) + ((n : ℕ) : WithBot ℕ) :=
            WithBot.add_lt_add_left (by simp) h2
        _ = ((m + n : ℕ) : WithBot ℕ) := by rw [Nat.cast_add]
  have hzero : (q.1 : K[X]) - (1 + X ^ m) * (q.2 : K[X]) = 0 :=
    eq_zero_of_dvd_of_degree_lt hdvd hlt
  have heq : (q.1 : K[X]) = (1 + X ^ m) * (q.2 : K[X]) := by
    rw [← sub_eq_zero]; exact hzero
  have h20 : (q.2 : K[X]) = 0 := by
    by_contra h0
    have hq10 : (q.1 : K[X]) ≠ 0 := by rw [heq]; exact mul_ne_zero hp0 h0
    have hnat1 : ((q.1 : K[X])).natDegree < m :=
      (Polynomial.natDegree_lt_iff_degree_lt hq10).2 h1
    have hnatp : (1 + X ^ m : K[X]).natDegree = m :=
      Polynomial.natDegree_eq_of_degree_eq_some hp
    have hsum : ((q.1 : K[X])).natDegree = m + ((q.2 : K[X])).natDegree := by
      rw [heq, Polynomial.natDegree_mul hp0 h0, hnatp]
    omega
  have h10 : (q.1 : K[X]) = 0 := by rw [heq, h20, mul_zero]
  exact Prod.ext (Subtype.ext h10) (Subtype.ext h20)

/-- **And therefore bijective**: the two transverse coordinate spaces together have the dimension of
the space of compatibility errors below the horizon. -/
theorem bijective_transverseDifferential (hm : 0 < m) :
    Function.Bijective (transverseDifferential (1 + X ^ m : K[X]) m n (m + n)) := by
  have hdim : Module.finrank K (fibreTangentSpace K m n)
      = Module.finrank K (degreeLT K (m + n)) := by
    rw [Module.finrank_prod, finrank_degreeLT, finrank_degreeLT, finrank_degreeLT]
  have hinj := injective_transverseDifferential (K := K) (m := m) (n := n) hm
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩

/-! ## The unique transverse lift -/

/-- The transverse fibre of an observation: the low parts of the transverse coordinate and of its
quotient by the longitudinal jet, each below its own depth, compatible below the horizon. -/
def transverseFibre (K : Type*) [Field K] (m n : ℕ) (p U V : K[X]) : Type _ :=
  {q : K[X] × K[X] // q.1.degree < (m : ℕ) ∧ q.2.degree < (n : ℕ) ∧
    (X : K[X]) ^ (m + n) ∣ ((q.1 + U) - p * (q.2 + V))}

/-- **Every transverse observation has exactly one lift.**  The compatibility is an affine equation
for a bijective linear map, so it has a unique solution for every pair of observed transverse
tails. -/
theorem exists_unique_transverse (hm : 0 < m) (U V : K[X]) :
    ∃! q : K[X] × K[X], (q.1.degree < (m : ℕ) ∧ q.2.degree < (n : ℕ)) ∧
      (X : K[X]) ^ (m + n) ∣ ((q.1 + U) - (1 + X ^ m) * (q.2 + V)) := by
  set p : K[X] := 1 + X ^ m with hpdef
  set L : ℕ := m + n with hLdef
  have hkey : ∀ q : fibreTangentSpace K m n,
      (transverseDifferential p m n L q
          = -(⟨(U - p * V) %ₘ X ^ L, by
              rw [mem_degreeLT]
              have hlt := degree_modByMonic_lt (U - p * V) (monic_X_pow (R := K) L)
              rwa [degree_X_pow] at hlt⟩ : degreeLT K L))
        ↔ (X : K[X]) ^ L ∣ (((q.1 : K[X]) + U) - p * ((q.2 : K[X]) + V)) := by
    intro q
    rw [← Polynomial.modByMonic_eq_zero_iff_dvd (monic_X_pow (R := K) L)]
    rw [show ((q.1 : K[X]) + U) - p * ((q.2 : K[X]) + V)
        = ((q.1 : K[X]) - p * (q.2 : K[X])) + (U - p * V) by ring,
      Polynomial.add_modByMonic, add_eq_zero_iff_eq_neg]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  obtain ⟨hinj, hsurj⟩ := bijective_transverseDifferential (K := K) (m := m) (n := n) hm
  obtain ⟨q, hq⟩ := hsurj _
  refine ⟨((q.1 : K[X]), (q.2 : K[X])), ⟨⟨mem_degreeLT.1 q.1.2, mem_degreeLT.1 q.2.2⟩,
    (hkey q).1 hq⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨⟨ha, hb⟩, hdvd⟩
  have hq' : transverseDifferential p m n L (⟨a, mem_degreeLT.2 ha⟩, ⟨b, mem_degreeLT.2 hb⟩) = _ :=
    (hkey (⟨a, mem_degreeLT.2 ha⟩, ⟨b, mem_degreeLT.2 hb⟩)).2 hdvd
  have := hinj (hq'.trans hq.symm)
  exact Prod.ext (congrArg Subtype.val (congrArg Prod.fst this))
    (congrArg Subtype.val (congrArg Prod.snd this))

/-- **A transverse channel contributes exactly one point.** -/
theorem nat_card_transverseFibre (hm : 0 < m) (U V : K[X]) :
    Nat.card (transverseFibre K m n (1 + X ^ m) U V) = 1 := by
  obtain ⟨q, hq, huniq⟩ := exists_unique_transverse (K := K) (m := m) (n := n) hm U V
  refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => ?_⟩, ⟨⟨q, hq.1.1, hq.1.2, hq.2⟩⟩⟩
  exact Subtype.ext ((huniq a.1 ⟨⟨a.2.1, a.2.2.1⟩, a.2.2.2⟩).trans
    (huniq b.1 ⟨⟨b.2.1, b.2.2.1⟩, b.2.2.2⟩).symm)

/-! ## Projective dimension does not change the critical count -/

section Count

variable [IsAlgClosed K]

/-- **The critical multiplicity is stable under adding a transverse channel.**  The longitudinal
count is the critical binomial multiplicity and the transverse channel is uniquely solvable, so the
pair is counted by the same number. -/
theorem nat_card_criticalFibre_prod_transverse (hm : 0 < m) (hn : 0 < n) {U V U' V' : K[X]}
    (hU : U.degree ≤ (m : ℕ)) (hV : V.degree ≤ (n : ℕ)) (hUm : U.coeff m ≠ 0)
    (hVn : V.coeff n ≠ 0) (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0)
    (hsep : (1 + U * V).Separable) :
    Nat.card (criticalFibre K m n U V × transverseFibre K m n (1 + X ^ m) U' V')
      = criticalHorizonMultiplicity m n := by
  rw [Nat.card_prod, nat_card_transverseFibre hm U' V', mul_one,
    nat_card_criticalFibre_criticalTails hm hn hU hV hUm hVn hU0 hV0 hsep]

end Count


section AllRank

variable {K : Type*} [Field K] [IsAlgClosed K] {m n : ℕ}

/-- **The critical multiplicity is stable under any number of transverse channels.**  A source of
projective dimension `d + 1` observed at the two horizons has one longitudinal channel, counted by
the critical binomial multiplicity, and `d` transverse channels, each uniquely solvable.  So the
count of compatible sources is the same integer for every projective dimension. -/
theorem nat_card_criticalFibre_prod_transverse_channels {d : ℕ} (hm : 0 < m) (hn : 0 < n)
    {U V : K[X]} (hU : U.degree ≤ (m : ℕ)) (hV : V.degree ≤ (n : ℕ)) (hUm : U.coeff m ≠ 0)
    (hVn : V.coeff n ≠ 0) (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0)
    (hsep : (1 + U * V).Separable) (U' V' : Fin d → K[X]) :
    Nat.card (criticalFibre K m n U V ×
        ∀ i : Fin d, transverseFibre K m n (1 + X ^ m) (U' i) (V' i))
      = criticalHorizonMultiplicity m n := by
  rw [Nat.card_prod, Nat.card_pi,
    Finset.prod_congr rfl (fun i _ => nat_card_transverseFibre hm (U' i) (V' i)),
    Finset.prod_const_one, mul_one,
    nat_card_criticalFibre_criticalTails hm hn hU hV hUm hVn hU0 hV0 hsep]

end AllRank

end GaloisForLFunctions.HTGeometry
