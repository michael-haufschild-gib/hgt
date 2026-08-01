import GaloisForLFunctions.HTGeometry.TruncatedCompatibilityFibre
import GaloisForLFunctions.HTGeometry.InverseJetNumerator
import GaloisForLFunctions.HTGeometry.SeparableSplitDivisorCount

/-!
# The fibre of a one-deep observation

At depth one in the jet the unknown is a single scalar, and the compatibility equation eliminates to
a polynomial equation in it whose degree is the horizon length.  So the fibre of any such
observation — with no condition on the length of the observed tail — has at most that many points.

This is the first count at an observation whose tail need not be a monomial, where the truncation is
not vacuous and the exact factorization is unavailable.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K]

/-- The polynomial whose roots carry the fibre of a one-deep observation: the observed reciprocal
tail coefficient against the numerator of the last inverse coefficient. -/
noncomputable def oneDeepEquation (U : K[X]) (d : K) (n : ℕ) : K[X] :=
  C d * X ^ (1 + n) - invNumerator (fun i => U.coeff i) n

theorem natDegree_invNumerator_lt_oneDeep (U : K[X]) (n : ℕ) :
    (invNumerator (fun i => U.coeff i) n).natDegree < 1 + n :=
  lt_of_le_of_lt (natDegree_invNumerator_le _ n) (by omega)

/-- **The elimination polynomial has degree the horizon length.** -/
theorem degree_oneDeepEquation {U : K[X]} {d : K} (hd : d ≠ 0) (n : ℕ) :
    (oneDeepEquation U d n).degree = ((1 + n : ℕ) : WithBot ℕ) := by
  have hlead : (C d * X ^ (1 + n) : K[X]).degree = ((1 + n : ℕ) : WithBot ℕ) :=
    degree_C_mul_X_pow _ hd
  have hsmall : (-invNumerator (fun i => U.coeff i) n : K[X]).degree
      < (C d * X ^ (1 + n) : K[X]).degree := by
    rw [hlead, Polynomial.degree_neg]
    refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
    exact_mod_cast natDegree_invNumerator_lt_oneDeep U n
  rw [oneDeepEquation, sub_eq_add_neg, Polynomial.degree_add_eq_left_of_degree_lt hsmall, hlead]

theorem natDegree_oneDeepEquation {U : K[X]} {d : K} (hd : d ≠ 0) (n : ℕ) :
    (oneDeepEquation U d n).natDegree = 1 + n :=
  Polynomial.natDegree_eq_of_degree_eq_some (degree_oneDeepEquation hd n)

/-- **The elimination polynomial is nonzero.** -/
theorem oneDeepEquation_ne_zero {U : K[X]} {d : K} (hd : d ≠ 0) (n : ℕ) :
    oneDeepEquation U d n ≠ 0 := by
  intro h
  have := natDegree_oneDeepEquation hd (U := U) n
  rw [h, Polynomial.natDegree_zero] at this
  omega

/-! ## The fibre points are roots -/

/-- **A fibre point's jet coefficient is a root of the elimination polynomial.** -/
theorem isRoot_oneDeepEquation {n : ℕ} (hn : 0 < n) {U : K[X]} (hU : U.coeff 0 = 0) {d : K}
    (p : criticalFibre K 1 n U (C d * X ^ n)) :
    (oneDeepEquation U d n).IsRoot (p.1.1.coeff 0) := by
  obtain ⟨⟨A, B⟩, hA, hB, hdvd⟩ := p
  have hUdvd : (X : K[X]) ^ 1 ∣ U := by
    rw [pow_one, Polynomial.X_dvd_iff]
    exact hU
  have hVdvd : (X : K[X]) ^ n ∣ C d * X ^ n := ⟨C d, by ring⟩
  rw [dvd_criticalLowProduct_sub_one_iff_mul_sub_one hUdvd hVdvd] at hdvd
  obtain ⟨h0, hrec⟩ := coeff_recursion_of_dvd hdvd
  have hA0 : (A + U).coeff 0 = A.coeff 0 := by
    rw [Polynomial.coeff_add, hU, add_zero]
  have hAsucc : ∀ i : ℕ, (A + U).coeff (i + 1) = U.coeff (i + 1) := by
    intro i
    rw [Polynomial.coeff_add, Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le hA (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by omega))), zero_add]
  have hGn : (B + C d * X ^ n).coeff n = d := by
    rw [Polynomial.coeff_add, Polynomial.coeff_eq_zero_of_degree_lt hB, zero_add,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  have hkey := pow_mul_eq_invNumerator_eval_of_lt (fun i => U.coeff i)
    (fun k => (B + C d * X ^ n).coeff k) (A.coeff 0) (L := 1 + n)
    (by rw [← hA0]; exact h0 (by omega))
    (fun k hk => by
      rw [← hA0]
      have := hrec k hk
      rw [Finset.sum_congr rfl (fun i _ => by rw [hAsucc i])] at this
      exact this)
    n (by omega)
  rw [hGn] at hkey
  show (oneDeepEquation U d n).eval (A.coeff 0) = 0
  rw [oneDeepEquation, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, ← hkey]
  ring

/-- **The fibre of a one-deep observation has at most the horizon length many points**, for any
observed tail whatever. -/
theorem nat_card_criticalFibre_one_le {n : ℕ} (hn : 0 < n) {U : K[X]} (hU : U.coeff 0 = 0) {d : K}
    (hd : d ≠ 0) :
    Nat.card (criticalFibre K 1 n U (C d * X ^ n)) ≤ 1 + n := by
  classical
  have hV0 : (C d * X ^ n : K[X]).coeff 0 = 0 := by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega : ¬ (0 : ℕ) = n), mul_zero]
  have hne := oneDeepEquation_ne_zero (U := U) hd n
  have hmem : ∀ p : criticalFibre K 1 n U (C d * X ^ n),
      p.1.1.coeff 0 ∈ (oneDeepEquation U d n).roots.toFinset := by
    intro p
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
    exact isRoot_oneDeepEquation hn hU p
  have hinj : Function.Injective (fun p : criticalFibre K 1 n U (C d * X ^ n) =>
      (⟨p.1.1.coeff 0, hmem p⟩ : {x : K // x ∈ (oneDeepEquation U d n).roots.toFinset})) := by
    intro p q h
    have hcoeff : p.1.1.coeff 0 = q.1.1.coeff 0 := congrArg Subtype.val h
    have hpq : p.1.1 = q.1.1 := by
      refine Polynomial.ext fun k => ?_
      match k with
      | 0 => exact hcoeff
      | (j + 1) =>
          have hle : ((1 : ℕ) : WithBot ℕ) ≤ ((j + 1 : ℕ) : WithBot ℕ) := by
            exact_mod_cast (by omega : (1 : ℕ) ≤ j + 1)
          rw [Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le p.2.1 hle),
            Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le q.2.1 hle)]
    exact criticalFibre_fst_injective (by omega) hn hU hV0 hpq
  calc Nat.card (criticalFibre K 1 n U (C d * X ^ n))
      ≤ Nat.card {x : K // x ∈ (oneDeepEquation U d n).roots.toFinset} :=
        Nat.card_le_card_of_injective _ hinj
    _ = ((oneDeepEquation U d n).roots.toFinset).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ Multiset.card (oneDeepEquation U d n).roots := Multiset.toFinset_card_le _
    _ ≤ (oneDeepEquation U d n).natDegree := Polynomial.card_roots' _
    _ = 1 + n := natDegree_oneDeepEquation hd n

/-! ## Every nonzero root comes from a fibre point -/

/-- The inverse coefficients built from a nonzero constant term by the recursion. -/
noncomputable def invCoeff (u : ℕ → K) (a : K) : ℕ → K
  | 0 => a⁻¹
  | (k + 1) => -a⁻¹ * ∑ j ∈ Finset.range (k + 1), u (j + 1) * invCoeff u a (k - j)

theorem invCoeff_zero (u : ℕ → K) (a : K) : invCoeff u a 0 = a⁻¹ := by
  rw [invCoeff]

theorem invCoeff_succ (u : ℕ → K) (a : K) (k : ℕ) :
    invCoeff u a (k + 1) = -a⁻¹ * ∑ j ∈ Finset.range (k + 1), u (j + 1) * invCoeff u a (k - j) := by
  rw [invCoeff]

theorem mul_invCoeff_zero {u : ℕ → K} {a : K} (ha : a ≠ 0) : a * invCoeff u a 0 = 1 := by
  rw [invCoeff_zero, mul_inv_cancel₀ ha]

theorem mul_invCoeff_succ {u : ℕ → K} {a : K} (ha : a ≠ 0) (k : ℕ) :
    a * invCoeff u a (k + 1) = -∑ j ∈ Finset.range (k + 1), u (j + 1) * invCoeff u a (k - j) := by
  rw [invCoeff_succ]
  field_simp

/-- **The recursion reproduces the numerators.** -/
theorem pow_mul_invCoeff_eq (u : ℕ → K) {a : K} (ha : a ≠ 0) (k : ℕ) :
    a ^ (k + 1) * invCoeff u a k = (invNumerator u k).eval a :=
  pow_mul_eq_invNumerator_eval u (invCoeff u a) a (mul_invCoeff_zero ha)
    (fun k => mul_invCoeff_succ ha k) k

/-- **At a nonzero root the last inverse coefficient is the observed one.** -/
theorem invCoeff_eq_of_isRoot {U : K[X]} {d a : K} (ha : a ≠ 0) {n : ℕ}
    (hroot : (oneDeepEquation U d n).IsRoot a) :
    invCoeff (fun i => U.coeff i) a n = d := by
  have hnum := pow_mul_invCoeff_eq (fun i => U.coeff i) ha n
  have hval : (invNumerator (fun i => U.coeff i) n).eval a = d * a ^ (1 + n) := by
    have := hroot
    rw [Polynomial.IsRoot, oneDeepEquation, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero] at this
    exact this.symm
  rw [hval] at hnum
  have hpow : a ^ (1 + n) = a ^ (n + 1) := by rw [Nat.add_comm]
  rw [hpow] at hnum
  have hane : a ^ (n + 1) ≠ 0 := pow_ne_zero _ ha
  refine mul_left_cancel₀ hane ?_
  rw [hnum]
  ring

/-- The reciprocal jet reconstructed from a nonzero root. -/
noncomputable def invPoly (u : ℕ → K) (a : K) (n : ℕ) : K[X] :=
  ∑ k ∈ Finset.range (n + 1), C (invCoeff u a k) * X ^ k

theorem coeff_invPoly (u : ℕ → K) (a : K) (n : ℕ) {k : ℕ} (hk : k ≤ n) :
    (invPoly u a n).coeff k = invCoeff u a k := by
  classical
  rw [invPoly, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single k]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro j _ hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (fun hcon => hj hcon.symm), mul_zero]
  · intro hcon
    exact absurd (Finset.mem_range.2 (by omega)) hcon

/-- **The reconstructed pair satisfies the truncated compatibility.**  So a nonzero root of the
elimination polynomial does come from a solution of the observation's equation. -/
theorem dvd_invPoly_compat {U : K[X]} (hU : U.coeff 0 = 0) {a : K} (ha : a ≠ 0) (n : ℕ) :
    (X : K[X]) ^ (n + 1) ∣ (C a + U) * invPoly (fun i => U.coeff i) a n - 1 := by
  classical
  set u : ℕ → K := fun i => U.coeff i with hu
  set G : K[X] := invPoly u a n with hG
  have hF0 : (C a + U).coeff 0 = a := by
    rw [Polynomial.coeff_add, Polynomial.coeff_C_zero, hU, add_zero]
  have hFsucc : ∀ i : ℕ, (C a + U).coeff (i + 1) = u (i + 1) := by
    intro i
    rw [Polynomial.coeff_add, Polynomial.coeff_C, if_neg (by omega), zero_add, hu]
  have hsum : ∀ k : ℕ, ((C a + U) * G).coeff k
      = (∑ i ∈ Finset.range k, u (i + 1) * G.coeff (k - (i + 1))) + a * G.coeff k := by
    intro k
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (C a + U).coeff i * G.coeff j), Finset.sum_range_succ']
    simp only [hFsucc, hF0, Nat.sub_zero]
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  rw [Polynomial.coeff_sub, hsum k]
  match k with
  | 0 =>
      rw [Finset.range_zero, Finset.sum_empty, zero_add, coeff_invPoly u a n (by omega),
        mul_invCoeff_zero ha, Polynomial.coeff_one_zero, sub_self]
  | (j + 1) =>
      have hcoeffs : ∀ i ∈ Finset.range (j + 1),
          u (i + 1) * G.coeff (j + 1 - (i + 1)) = u (i + 1) * invCoeff u a (j - i) := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [show j + 1 - (i + 1) = j - i from by omega, coeff_invPoly u a n (by omega)]
      rw [Finset.sum_congr rfl hcoeffs, coeff_invPoly u a n (by omega),
        mul_invCoeff_succ ha j, Polynomial.coeff_one, if_neg (by omega)]
      ring

/-- The reconstructed reciprocal jet has degree at most the second depth. -/
theorem degree_invPoly_le (u : ℕ → K) (a : K) (n : ℕ) :
    (invPoly u a n).degree ≤ (n : ℕ) := by
  refine le_trans (Polynomial.degree_sum_le _ _) ?_
  refine Finset.sup_le fun k hk => ?_
  rw [Finset.mem_range] at hk
  refine le_trans (Polynomial.degree_C_mul_X_pow_le _ _) ?_
  exact_mod_cast (by omega : k ≤ n)

/-- **A nonzero root gives a point of the fibre.** -/
noncomputable def fibreOfRoot {n : ℕ} {U : K[X]} (hU : U.coeff 0 = 0) {d : K}
    (hd : d ≠ 0) {a : K} (ha : a ≠ 0) (hroot : (oneDeepEquation U d n).IsRoot a) :
    criticalFibre K 1 n U (C d * X ^ n) := by
  classical
  refine ⟨(C a, invPoly (fun i => U.coeff i) a n - C d * X ^ n), ?_, ?_, ?_⟩
  · refine lt_of_le_of_lt Polynomial.degree_C_le ?_
    exact_mod_cast (by omega : (0 : ℕ) < 1)
  · have hcoeff : (invPoly (fun i => U.coeff i) a n).coeff n = d := by
      rw [coeff_invPoly _ a n le_rfl]
      exact invCoeff_eq_of_isRoot ha hroot
    have hVdeg : (C d * X ^ n : K[X]).degree = (n : ℕ) := degree_C_mul_X_pow n hd
    have hGdeg : (invPoly (fun i => U.coeff i) a n).degree = (n : ℕ) := by
      refine le_antisymm (degree_invPoly_le _ a n) ?_
      refine Polynomial.le_degree_of_ne_zero ?_
      rw [hcoeff]
      exact hd
    refine lt_of_lt_of_le (Polynomial.degree_sub_lt (by rw [hGdeg, hVdeg]) ?_ ?_) (le_of_eq hGdeg)
    · intro hcon
      rw [hcon, Polynomial.coeff_zero] at hcoeff
      exact hd hcoeff.symm
    · rw [Polynomial.leadingCoeff, Polynomial.natDegree, hGdeg, Polynomial.leadingCoeff_C_mul_X_pow]
      exact hcoeff
  · have hUdvd : (X : K[X]) ^ 1 ∣ U := by
      rw [pow_one, Polynomial.X_dvd_iff]
      exact hU
    have hVdvd : (X : K[X]) ^ n ∣ C d * X ^ n := ⟨C d, by ring⟩
    rw [dvd_criticalLowProduct_sub_one_iff_mul_sub_one hUdvd hVdvd]
    simp only
    rw [show (invPoly (fun i => U.coeff i) a n - C d * X ^ n) + C d * X ^ n
        = invPoly (fun i => U.coeff i) a n from by ring]
    rw [show 1 + n = n + 1 from Nat.add_comm 1 n]
    exact dvd_invPoly_compat hU ha n

/-! ## The fibre is exactly the nonzero roots -/

/-- **A fibre point has invertible jet coefficient.** -/
theorem coeff_zero_ne_zero_of_fibre {n : ℕ} (hn : 0 < n) {U : K[X]} (hU : U.coeff 0 = 0) {d : K}
    (p : criticalFibre K 1 n U (C d * X ^ n)) : p.1.1.coeff 0 ≠ 0 := by
  have hV0 : (C d * X ^ n : K[X]).coeff 0 = 0 := by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega : ¬ (0 : ℕ) = n), mul_zero]
  have h := coeff_zero_add_ne_zero_of_dvd (by omega : 0 < 1 + n) hU hV0 p.2.2.2
  rw [Polynomial.coeff_add, hU, add_zero] at h
  exact h

/-- **The jet coefficients of the fibre are exactly the nonzero roots of the elimination
polynomial.** -/
theorem range_fibre_coeff {n : ℕ} (hn : 0 < n) {U : K[X]} (hU : U.coeff 0 = 0) {d : K}
    (hd : d ≠ 0) :
    Set.range (fun p : criticalFibre K 1 n U (C d * X ^ n) => p.1.1.coeff 0)
      = {a : K | a ≠ 0 ∧ (oneDeepEquation U d n).IsRoot a} := by
  ext a
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨coeff_zero_ne_zero_of_fibre hn hU p, isRoot_oneDeepEquation hn hU p⟩
  · rintro ⟨ha, hroot⟩
    refine ⟨fibreOfRoot hU hd ha hroot, ?_⟩
    show (C a : K[X]).coeff 0 = a
    exact Polynomial.coeff_C_zero

/-- **So the fibre of a one-deep observation is counted by the nonzero roots of a single polynomial
of degree the horizon length.** -/
theorem nat_card_criticalFibre_one_eq {n : ℕ} (hn : 0 < n) {U : K[X]} (hU : U.coeff 0 = 0) {d : K}
    (hd : d ≠ 0) :
    Nat.card (criticalFibre K 1 n U (C d * X ^ n))
      = Nat.card {a : K // a ≠ 0 ∧ (oneDeepEquation U d n).IsRoot a} := by
  classical
  have hV0 : (C d * X ^ n : K[X]).coeff 0 = 0 := by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega : ¬ (0 : ℕ) = n), mul_zero]
  have hinj : Function.Injective
      (fun p : criticalFibre K 1 n U (C d * X ^ n) => p.1.1.coeff 0) := by
    intro p q hcoeff
    have hpq : p.1.1 = q.1.1 := by
      refine Polynomial.ext fun k => ?_
      match k with
      | 0 => exact hcoeff
      | (j + 1) =>
          have hle : ((1 : ℕ) : WithBot ℕ) ≤ ((j + 1 : ℕ) : WithBot ℕ) := by
            exact_mod_cast (by omega : (1 : ℕ) ≤ j + 1)
          rw [Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le p.2.1 hle),
            Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le q.2.1 hle)]
    exact criticalFibre_fst_injective (by omega) hn hU hV0 hpq
  refine Nat.card_congr (Equiv.ofBijective
    (fun p : criticalFibre K 1 n U (C d * X ^ n) =>
      (⟨p.1.1.coeff 0, coeff_zero_ne_zero_of_fibre hn hU p, isRoot_oneDeepEquation hn hU p⟩ :
        {a : K // a ≠ 0 ∧ (oneDeepEquation U d n).IsRoot a})) ⟨?_, ?_⟩)
  · intro p q h
    exact hinj (congrArg Subtype.val h)
  · rintro ⟨a, ha, hroot⟩
    exact ⟨fibreOfRoot hU hd ha hroot, Subtype.ext Polynomial.coeff_C_zero⟩

/-! ## The dual case, by the depth symmetry -/

/-- **The same count when it is the reciprocal depth that is one.**  The depth symmetry of the fibre
exchanges the two roles, so an observation whose **jet** tail is a monomial and whose reciprocal tail
is arbitrary is counted by the same root set. -/
theorem nat_card_criticalFibre_snd_one_eq {m : ℕ} (hm : 0 < m) {V : K[X]} (hV : V.coeff 0 = 0)
    {d : K} (hd : d ≠ 0) :
    Nat.card (criticalFibre K m 1 (C d * X ^ m) V)
      = Nat.card {a : K // a ≠ 0 ∧ (oneDeepEquation V d m).IsRoot a} := by
  rw [Nat.card_congr (criticalFibreSwap m 1 (C d * X ^ m) V)]
  exact nat_card_criticalFibre_one_eq hm hV hd

/-! ## Exactness -/

/-- **The depth-one fibre has exactly the horizon length many points** when the elimination
polynomial is separable and does not vanish at the origin.  Both conditions are the generic ones:
separability is the discriminant not vanishing, and a root at the origin would be a jet that is not
invertible there, which compatibility already excludes. -/
theorem nat_card_criticalFibre_one_eq_horizon [IsAlgClosed K] {n : ℕ} (hn : 0 < n) {U : K[X]}
    (hU : U.coeff 0 = 0) {d : K} (hd : d ≠ 0)
    (hsep : (oneDeepEquation U d n).Separable)
    (hzero : ¬ (oneDeepEquation U d n).IsRoot 0) :
    Nat.card (criticalFibre K 1 n U (C d * X ^ n)) = 1 + n := by
  classical
  rw [nat_card_criticalFibre_one_eq hn hU hd]
  have hequiv : {a : K // a ≠ 0 ∧ (oneDeepEquation U d n).IsRoot a}
      ≃ {a : K // a ∈ (oneDeepEquation U d n).roots.toFinset} := by
    refine Equiv.subtypeEquivRight fun a => ?_
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (oneDeepEquation_ne_zero hd n)]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨fun hcon => hzero ?_, h⟩
      rwa [hcon] at h
  rw [Nat.card_congr hequiv, Nat.card_eq_fintype_card, Fintype.card_coe,
    card_roots_toFinset hsep (IsAlgClosed.splits _), natDegree_oneDeepEquation hd]

/-- **`(2)` at depth one, in the card's own notation.**  The fibre of a one-deep observation has
exactly the critical binomial multiplicity of points. -/
theorem nat_card_criticalFibre_one_eq_multiplicity [IsAlgClosed K] {n : ℕ} (hn : 0 < n)
    {U : K[X]} (hU : U.coeff 0 = 0) {d : K} (hd : d ≠ 0)
    (hsep : (oneDeepEquation U d n).Separable)
    (hzero : ¬ (oneDeepEquation U d n).IsRoot 0) :
    Nat.card (criticalFibre K 1 n U (C d * X ^ n)) = criticalHorizonMultiplicity 1 n := by
  rw [nat_card_criticalFibre_one_eq_horizon hn hU hd hsep hzero, criticalHorizonMultiplicity,
    Nat.choose_one_right]

/-- **And dually at reciprocal depth one.** -/
theorem nat_card_criticalFibre_snd_one_eq_multiplicity [IsAlgClosed K] {m : ℕ} (hm : 0 < m)
    {V : K[X]} (hV : V.coeff 0 = 0) {d : K} (hd : d ≠ 0)
    (hsep : (oneDeepEquation V d m).Separable)
    (hzero : ¬ (oneDeepEquation V d m).IsRoot 0) :
    Nat.card (criticalFibre K m 1 (C d * X ^ m) V) = criticalHorizonMultiplicity m 1 := by
  rw [Nat.card_congr (criticalFibreSwap m 1 (C d * X ^ m) V),
    nat_card_criticalFibre_one_eq_horizon hm hV hd hsep hzero, criticalHorizonMultiplicity,
    Nat.add_comm m 1]
  have h1 : (1 + m) - 1 = m := by omega
  have h2 := Nat.choose_symm (n := 1 + m) (k := 1) (by omega)
  rw [h1, Nat.choose_one_right] at h2
  omega

/-! ## The fibre equations at arbitrary depths -/

/-- **The fibre equations of an arbitrary observation.**  Every coefficient of the reciprocal jet,
cleared of its denominator, is the corresponding numerator evaluated at the jet's constant term — for
**any** pair of depths, not only depth one.  The observed reciprocal tail then turns the equations of
index `n` and above into the fibre's defining system. -/
theorem fibre_eval_invNumerator {m n : ℕ} (hm : 0 < m) {U V : K[X]}
    (hU : (X : K[X]) ^ m ∣ U) (hV : (X : K[X]) ^ n ∣ V)
    (p : criticalFibre K m n U V) {k : ℕ} (hk : k < m + n) :
    (p.1.1 + U).coeff 0 ^ (k + 1) * (p.1.2 + V).coeff k
      = (invNumerator (fun i => (p.1.1 + U).coeff i) k).eval ((p.1.1 + U).coeff 0) := by
  obtain ⟨⟨A, B⟩, hA, hB, hdvd⟩ := p
  rw [dvd_criticalLowProduct_sub_one_iff_mul_sub_one hU hV] at hdvd
  obtain ⟨h0, hrec⟩ := coeff_recursion_of_dvd hdvd
  exact pow_mul_eq_invNumerator_eval_of_lt (fun i => (A + U).coeff i)
    (fun j => (B + V).coeff j) ((A + U).coeff 0) (h0 (by omega)) hrec k hk

/-- **The fibre's defining system, in terms of the observation alone.**  Above the reciprocal depth
the unknown low part contributes nothing, so the `m` equations of index `n` and above read entirely
in the observed data. -/
theorem fibre_system {m n : ℕ} (hm : 0 < m) {U V : K[X]}
    (hU : (X : K[X]) ^ m ∣ U) (hV : (X : K[X]) ^ n ∣ V)
    (p : criticalFibre K m n U V) {k : ℕ} (hk1 : n ≤ k) (hk2 : k < m + n) :
    (p.1.1 + U).coeff 0 ^ (k + 1) * V.coeff k
      = (invNumerator (fun i => (p.1.1 + U).coeff i) k).eval ((p.1.1 + U).coeff 0) := by
  have hBk : p.1.2.coeff k = 0 := by
    refine Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le p.2.2.1 ?_)
    exact_mod_cast hk1
  have hcoeff : (p.1.2 + V).coeff k = V.coeff k := by
    rw [Polynomial.coeff_add, hBk, zero_add]
  have h := fibre_eval_invNumerator hm hU hV p hk2
  rwa [hcoeff] at h

end GaloisForLFunctions.HTGeometry
