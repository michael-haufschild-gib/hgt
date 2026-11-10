import GaloisForLFunctions.HyperbolicArakelovTheory.TheMinimalBranchOfTheAdelicGreenKernel
import GaloisForLFunctions.HyperbolicArakelovTheory.TheCoupledLocalProductObstructsOffDiagonalAndTorusInvariance
import GaloisForLFunctions.ArithmeticIntersectionTheory.ThePrimeKernelIsASumOfTransverseTowers

/-!
# Arithmetic contact from the prime fibres of the adelic vertex space

Extend the critical Green kernel by zero between different fibres of all other
coordinates. Each extension is the minimal nonnegative point-source solution
for its prime adjacency. Removing its constant diagonal and summing over primes
recovers the arithmetic prime kernel on the actual degree configuration.
These kernels have simultaneous adelic invariance; no separate quotient descent
or torus periodization is asserted.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators

namespace GaloisForLFunctions.HyperbolicArakelovTheory.PrimeFibres
open FullAdelic AdelicAdjacency AdelicRadial AdelicGreen CoupledProductObstruction
open ArithmeticIntersectionTheory ArithmeticEffectivityTheory

abbrev Prime := {p : ℕ // p.Prime}
local instance (p : Prime) : Fact p.1.Prime := ⟨p.2⟩

/-- Agreement at every finite place except the indicated prime. -/
def SameFibre (p : Prime) (v w : FiniteVertices) : Prop :=
  ∀ q : Prime, q ≠ p → v.1 q = w.1 q

theorem sameFibre_smul (p : Prime) (a : FiniteAdelicGroup) (v w : FiniteVertices) :
    SameFibre p (a • v) (a • w) ↔ SameFibre p v w := by
  constructor <;> intro h q hq
  · exact (MulAction.injective (a q)) (h q hq)
  · exact congrArg (fun z => a q • z) (h q hq)

theorem sameFibre_replace (p : Prime) (v w : FiniteVertices) (z : LocalVertex p) :
    SameFibre p v (replaceVertex p w z) ↔ SameFibre p v w := by
  constructor <;> intro h q hq
  · simpa only [replaceVertex_away p w z q hq] using h q hq
  · rw [replaceVertex_away p w z q hq]
    exact h q hq

theorem eq_replace_of_sameFibre (p : Prime) {v w : FiniteVertices}
    (h : SameFibre p v w) : replaceVertex p v (w.1 p) = w := by
  apply Subtype.ext
  funext q
  by_cases hq : q = p
  · subst q
    exact replaceVertex_at p v _
  · rw [replaceVertex_away p v _ q hq]
    exact h q hq

/-- Distinct vertices share at most one prime fibre. -/
theorem eq_of_two_fibres {p q : Prime} (hpq : p ≠ q) {v w : FiniteVertices}
    (hp : SameFibre p v w) (hq : SameFibre q v w) : v = w := by
  apply Subtype.ext
  funext r
  by_cases hr : r = p
  · subst r
    exact hq p hpq
  · exact hp r hr

/-- The critical point-source kernel for a prime acting on the full finite product. -/
def fibreGreen (p : Prime) (v w : FiniteVertices) : ℝ :=
  if SameFibre p v w then localGreen p (1 / 2) (v.1 p) (w.1 p) else 0

theorem fibreGreen_nonneg (p : Prime) (v w : FiniteVertices) :
    0 ≤ fibreGreen p v w := by
  unfold fibreGreen
  split_ifs
  · exact (localGreen_pos p (by norm_num) _ _).le
  · exact le_rfl

theorem fibreGreen_smul (p : Prime) (a : FiniteAdelicGroup) (v w : FiniteVertices) :
    fibreGreen p (a • v) (a • w) = fibreGreen p v w := by
  simp only [fibreGreen, sameFibre_smul]
  split_ifs
  · exact localGreen_smul p (1 / 2) (a p) _ _
  · rfl

/-- Its source is the single finite vertex. -/
theorem fibreGreen_source (p : Prime) (v w : FiniteVertices) :
    (2 * Real.sqrt p.1) * fibreGreen p v w -
      (∑ z ∈ neighbors p (w.1 p), fibreGreen p v (replaceVertex p w z)) =
        if v = w then 1 else 0 := by
  by_cases h : SameFibre p v w
  · have he : v = w ↔ v.1 p = w.1 p := by
      constructor
      · intro hvw; rw [hvw]
      · intro hp
        apply Subtype.ext
        funext q
        by_cases hq : q = p
        · subst q; exact hp
        · exact h q hq
    simp only [fibreGreen, sameFibre_replace, if_pos h, replaceVertex_at, he]
    exact localGreen_tempered_resolvent p _ _
  · have hne : v ≠ w := by rintro rfl; exact h (fun _ _ => rfl)
    simp only [fibreGreen, sameFibre_replace, if_neg h, if_neg hne,
      mul_zero, Finset.sum_const_zero, sub_zero]

/-- Extension by zero selects the least supersolution on all disconnected prime fibres. -/
theorem fibreGreen_isLeast (p : Prime) (v : FiniteVertices) :
    IsLeast {u : FiniteVertices → ℝ | (∀ w, 0 ≤ u w) ∧ ∀ w,
      (if v = w then 1 else 0) ≤ (2 * Real.sqrt p.1) * u w -
        ∑ z ∈ neighbors p (w.1 p), u (replaceVertex p w z)} (fibreGreen p v) := by
  refine ⟨⟨fibreGreen_nonneg p v, fun w => (fibreGreen_source p v w).ge⟩, ?_⟩
  intro u hu w
  by_cases hw : SameFibre p v w
  · have hlocal : (fun z => u (replaceVertex p v z)) ∈
        MinimalGreen.supersolutions p (treeEigen p.1 (1 / 2)) (v.1 p) := by
      refine ⟨fun z => hu.1 _, fun z => ?_⟩
      have hsource := hu.2 (replaceVertex p v z)
      have he : v = replaceVertex p v z ↔ v.1 p = z := by
        constructor
        · intro hh
          have hh' := congrArg (fun x : FiniteVertices => x.1 p) hh
          simpa only [replaceVertex_at] using hh'
        · intro hh
          rw [← hh]
          exact (eq_replace_of_sameFibre p (v := v) (w := v) (fun _ _ => rfl)).symm
      have hr (t : LocalVertex p) :
          replaceVertex p (replaceVertex p v z) t = replaceVertex p v t := by
        apply Subtype.ext
        funext q
        by_cases hq : q = p
        · subst q; simp only [replaceVertex_at]
        · simp only [replaceVertex_away p _ _ q hq]
      have hp1 : (1 : ℝ) < p.1 := by exact_mod_cast p.2.one_lt
      rw [(treeEigen_eq_iff hp1 (1 / 2)).mpr rfl]
      simpa only [PrimeWalk.pointMass, he, replaceVertex_at, hr] using hsource
    have hmin := (MinimalGreen.localGreen_isLeast_of_half_le p
      (s := (1 / 2 : ℝ)) le_rfl (v.1 p)).2 hlocal (w.1 p)
    simpa only [fibreGreen, if_pos hw, eq_replace_of_sameFibre p hw] using hmin
  · simpa only [fibreGreen, if_neg hw] using hu.1 w

private theorem factor_eq_sqrt_ratio (p : Prime) (v w : LocalVertex p) :
    localFactor p v w = Real.sqrt (localRatio p v w) := by
  induction v using Quotient.inductionOn with
  | h g =>
    induction w using Quotient.inductionOn with
    | h h =>
      rw [localFactor_mk, localRatio_mk]
      generalize g⁻¹ * h = a
      induction a using Quotient.inductionOn with
      | h A =>
        change glFactor p A = Real.sqrt (matrixRatio p A)
        change Real.sqrt ‖A.val.det‖ / entrySize p A.val =
          Real.sqrt (‖A.val.det‖ / entrySize p A.val ^ 2)
        rw [Real.sqrt_div (norm_nonneg _), Real.sqrt_sq (entrySize_pos p A).le]

/-- The normalized minimal Green kernel agrees with the invariant local matrix factor. -/
theorem normalized_localGreen (p : Prime) (v w : LocalVertex p) :
    (((p.1 : ℝ) - 1) / Real.sqrt p.1) * localGreen p (1 / 2) v w =
      localFactor p v w := by
  have hp1 : (1 : ℝ) < p.1 := by exact_mod_cast p.2.one_lt
  have hs : Real.sqrt p.1 ≠ 0 := (Real.sqrt_pos.mpr (by linarith only [hp1])).ne'
  have hd : (p.1 : ℝ) - 1 ≠ 0 := by linarith only [hp1]
  rw [localGreen, ← localGreen_self p (1 / 2) v, localGreen_tempered_self,
    ← Real.sqrt_eq_rpow, factor_eq_sqrt_ratio]
  field_simp [hs, hd]

private theorem localFactor_eq_one_iff (p : Prime) (v w : LocalVertex p) :
    localFactor p v w = 1 ↔ v = w := by
  rw [factor_eq_sqrt_ratio, ← localRatio_eq_one_iff p v w]
  constructor
  · intro h
    have hh := Real.sq_sqrt (localRatio_pos p v w).le
    rw [h, one_pow] at hh
    exact hh.symm
  · intro h; rw [h, Real.sqrt_one]

/-- Local prime normalization, with its constant diagonal removed. -/
def primeTerm (p : Prime) (v w : FiniteVertices) : ℝ :=
  Real.log p.1 * (((p.1 : ℝ) - 1) / Real.sqrt p.1) * fibreGreen p v w -
    if v = w then Real.log p.1 else 0

theorem primeTerm_eq (p : Prime) (v w : FiniteVertices) :
    primeTerm p v w = if v ≠ w ∧ SameFibre p v w then
      Real.log p.1 * localFactor p (v.1 p) (w.1 p) else 0 := by
  by_cases he : v = w
  · subst w
    simp only [primeTerm, fibreGreen, SameFibre, implies_true, if_true,
      mul_assoc, normalized_localGreen, localFactor_self, mul_one, sub_self,
      ne_eq, not_true_eq_false, false_and, if_false]
  · by_cases hf : SameFibre p v w
    · rw [primeTerm, fibreGreen, if_pos hf, if_neg he, sub_zero,
        if_pos ⟨he, hf⟩, mul_assoc,
        normalized_localGreen]
    · rw [primeTerm, fibreGreen, if_neg hf, if_neg he, mul_zero,
        sub_zero, if_neg (fun h => hf h.2)]

@[simp] theorem primeTerm_self (p : Prime) (v : FiniteVertices) : primeTerm p v v = 0 := by
  simp only [primeTerm_eq, ne_eq, not_true_eq_false, false_and, if_false]

/-- Natural indexing permits finite sums over the prime factors of degrees. -/
def primeTermNat (v w : FiniteVertices) (p : ℕ) : ℝ :=
  if hp : p.Prime then primeTerm ⟨p, hp⟩ v w else 0

/-- Off the diagonal only one place can contribute, regardless of support size. -/
theorem primeTermNat_finite_support (v w : FiniteVertices) :
    (Function.support (primeTermNat v w)).Finite := by
  by_cases he : v = w
  · subst w
    have hz : primeTermNat v v = 0 := by
      funext p
      simp only [primeTermNat, primeTerm_self, dite_eq_ite, ite_self, Pi.zero_apply]
    rw [hz, Function.support_zero]
    exact Set.finite_empty
  · obtain ⟨q, hq⟩ : ∃ q : Prime, v.1 q ≠ w.1 q := by
      by_contra h
      push Not at h
      exact he (Subtype.ext (funext h))
    apply (Set.finite_singleton q.1).subset
    intro p hp
    by_cases hprime : p.Prime
    · have hf : SameFibre ⟨p, hprime⟩ v w := by
        by_contra hf
        exact hp (by simp only [primeTermNat, dif_pos hprime, primeTerm_eq,
          and_false, if_false, hf])
      have hqp : q = (⟨p, hprime⟩ : Prime) := by
        by_contra hh
        exact hq (hf q hh)
      exact (congrArg Subtype.val hqp).symm
    · exact (hp (by simp only [primeTermNat, dif_neg hprime])).elim

/-- Finite, intrinsic prime channel on pairs of adelic finite vertices. -/
def primeGreen (v w : FiniteVertices) : ℝ := ∑ᶠ p, primeTermNat v w p

theorem primeGreen_smul (a : FiniteAdelicGroup) (v w : FiniteVertices) :
    primeGreen (a • v) (a • w) = primeGreen v w := by
  apply finsum_congr
  intro p
  by_cases hp : p.Prime
  · simp only [primeTermNat, dif_pos hp, primeTerm, fibreGreen_smul,
      (MulAction.injective a).eq_iff]
  · simp only [primeTermNat, dif_neg hp]

private theorem factor_degree (p : Prime) (m n : ℕ+) :
    localFactor p (principalVertex (upperDegree m) p) (principalVertex (upperDegree n) p) =
      kmsEntry (1 / Real.sqrt p.1) ((m : ℕ).factorization p.1) ((n : ℕ).factorization p.1) := by
  have hp0 : (0 : ℝ) < p.1 := by exact_mod_cast p.2.pos
  have hq : (p.1 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt p.1 := by
    rw [Real.rpow_neg hp0.le, ← Real.sqrt_eq_rpow, one_div]
  have ht (k : ℕ) : treeGreen p.1 (1 / 2) k =
      treeGreen p.1 (1 / 2) 0 * (1 / Real.sqrt p.1) ^ k := by
    simp only [treeGreen, pow_zero, mul_one, hq]
  have hc : treeGreen p.1 (1 / 2) 0 ≠ 0 := by
    rw [← localGreen_self p (1 / 2) (baseVertex p)]
    exact (localGreen_pos p (by norm_num) _ _).ne'
  rw [localFactor_upperDegree_eq_treeGreen, ht, mul_div_cancel_left₀ _ hc, kmsEntry]
  congr 1
  omega

/-- Equality of actual local degree vertices is exactly equality of prime exponents. -/
theorem degree_vertex_eq_iff (p : Prime) (m n : ℕ+) :
    principalVertex (upperDegree m) p = principalVertex (upperDegree n) p ↔
      (m : ℕ).factorization p.1 = (n : ℕ).factorization p.1 := by
  rw [← localFactor_eq_one_iff, factor_degree]
  constructor
  · intro h
    by_contra he
    have hk : max ((m : ℕ).factorization p.1) ((n : ℕ).factorization p.1) -
        min ((m : ℕ).factorization p.1) ((n : ℕ).factorization p.1) ≠ 0 := by omega
    exact (pow_lt_one₀ (inv_sqrt_prime_nonneg p.1) (inv_sqrt_prime_lt_one p.2) hk).ne h
  · intro h
    rw [h, kmsEntry_self]

private theorem degree_vertices_injective :
    Function.Injective (fun n : ℕ+ => finitePoint (upperDegree n)) := by
  intro m n h
  apply Subtype.ext
  apply Nat.eq_of_factorization_eq m.ne_zero n.ne_zero
  intro q
  by_cases hq : q.Prime
  · exact (degree_vertex_eq_iff ⟨q, hq⟩ m n).mp
      (congrArg (fun v : FiniteVertices => v.1 ⟨q, hq⟩) h)
  · rw [Nat.factorization_eq_zero_of_not_prime _ hq,
      Nat.factorization_eq_zero_of_not_prime _ hq]

/-- The geometric prime fibres restrict to the arithmetic ladders. -/
theorem sameFibre_degree (p : Prime) (m n : ℕ+) :
    SameFibre p (finitePoint (upperDegree m)) (finitePoint (upperDegree n)) ↔
      ordCompl[p.1] (m : ℕ) = ordCompl[p.1] (n : ℕ) := by
  constructor
  · intro h
    apply Nat.eq_of_factorization_eq (Nat.ordCompl_pos p.1 m.ne_zero).ne'
      (Nat.ordCompl_pos p.1 n.ne_zero).ne'
    intro q
    rw [Nat.factorization_ordCompl, Nat.factorization_ordCompl]
    by_cases hqp : q = p.1
    · subst q; simp only [Finsupp.erase_same]
    · rw [Finsupp.erase_ne hqp, Finsupp.erase_ne hqp]
      by_cases hq : q.Prime
      · exact (degree_vertex_eq_iff ⟨q, hq⟩ m n).mp
          (h ⟨q, hq⟩ (fun he => hqp (congrArg Subtype.val he)))
      · rw [Nat.factorization_eq_zero_of_not_prime _ hq,
          Nat.factorization_eq_zero_of_not_prime _ hq]
  · intro h q hq
    apply (degree_vertex_eq_iff q m n).mpr
    have hqp : q.1 ≠ p.1 := fun he => hq (Subtype.ext he)
    have he := congrArg (fun k : ℕ => k.factorization q.1) h
    simpa only [Nat.factorization_ordCompl, Finsupp.erase_ne hqp] using he

/-- Diagonal-subtracted geometric prime sources are precisely the arithmetic ladder kernels. -/
theorem primeTerm_degree (p : Prime) (m n : ℕ+) :
    primeTerm p (finitePoint (upperDegree m)) (finitePoint (upperDegree n)) =
      ladderKernel p.1 m n := by
  have he : finitePoint (upperDegree m) = finitePoint (upperDegree n) ↔ (m : ℕ) = n := by
    constructor
    · intro h; exact congrArg Subtype.val (degree_vertices_injective h)
    · intro h; rw [show m = n from Subtype.ext h]
  simp only [primeTerm_eq, ne_eq, he, sameFibre_degree]
  change (if (m : ℕ) ≠ n ∧ ordCompl[p.1] (m : ℕ) = ordCompl[p.1] (n : ℕ) then
    Real.log p.1 * localFactor p (principalVertex (upperDegree m) p)
      (principalVertex (upperDegree n) p) else 0) = _
  rw [factor_degree]
  rfl

/-- The finite adelic prime Green sum recovers every arithmetic prime entry. -/
theorem primeGreen_degree (m n : ℕ+) :
    primeGreen (finitePoint (upperDegree m)) (finitePoint (upperDegree n)) =
      weilPrimeKernel m n := by
  have hs : Function.support
      (primeTermNat (finitePoint (upperDegree m)) (finitePoint (upperDegree n))) ⊆
        (((m : ℕ) * n).primeFactors : Set ℕ) := by
    intro p hp
    by_contra hnot
    by_cases hprime : p.Prime
    · exact hp (by rw [primeTermNat, dif_pos hprime, primeTerm_degree,
        ladderKernel_eq_zero_of_not_mem m.ne_zero n.ne_zero hnot])
    · exact hp (by rw [primeTermNat, dif_neg hprime])
  rw [primeGreen, finsum_eq_sum_of_support_subset _ hs,
    weilPrimeKernel_eq_sum_ladderKernel m.ne_zero n.ne_zero]
  apply Finset.sum_congr rfl
  intro p hp
  rw [primeTermNat, dif_pos (Nat.prime_of_mem_primeFactors hp), primeTerm_degree]

/-- A prime cutoff has exactly the prime-logarithm diagonal before subtraction. -/
theorem cutoff_diagonal (S : Finset Prime) (v : FiniteVertices) :
    (∑ p ∈ S, Real.log p.1 * (((p.1 : ℝ) - 1) / Real.sqrt p.1) * fibreGreen p v v) =
      ∑ p ∈ S, Real.log p.1 := by
  apply Finset.sum_congr rfl
  intro p hp
  have h := primeTerm_self p v
  simpa only [primeTerm, if_true, sub_eq_zero] using h

/-- Finite sum of the actual normalized prime point-source kernels. -/
def rawCutoff (N : ℕ) (v w : FiniteVertices) : ℝ :=
  ∑ p ∈ Finset.range N, if hp : p.Prime then
    Real.log p * (((p : ℝ) - 1) / Real.sqrt p) * fibreGreen ⟨p, hp⟩ v w else 0

def diagonalCutoff (N : ℕ) : ℝ :=
  ∑ p ∈ Finset.range N, if p.Prime then Real.log p else 0

theorem cutoff_sub_diagonal (N : ℕ) (v w : FiniteVertices) :
    rawCutoff N v w - (if v = w then diagonalCutoff N else 0) =
      ∑ p ∈ Finset.range N, primeTermNat v w p := by
  by_cases he : v = w
  · rw [if_pos he, rawCutoff, diagonalCutoff, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hprime : p.Prime
    · simp only [primeTermNat, dif_pos hprime, if_pos hprime, primeTerm, if_pos he]
    · simp only [primeTermNat, dif_neg hprime, if_neg hprime, sub_self]
  · rw [if_neg he, sub_zero]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hprime : p.Prime
    · simp only [primeTermNat, dif_pos hprime, primeTerm, if_neg he, sub_zero]
    · simp only [primeTermNat, dif_neg hprime]

/-- After its universal diagonal is removed, the cutoff is eventually exactly constant. -/
theorem cutoff_stabilizes (v w : FiniteVertices) :
    ∃ N : ℕ, ∀ M ≥ N,
      rawCutoff M v w - (if v = w then diagonalCutoff M else 0) = primeGreen v w := by
  let S := (primeTermNat_finite_support v w).toFinset
  refine ⟨S.sup id + 1, fun M hM => ?_⟩
  rw [cutoff_sub_diagonal, primeGreen]
  symm
  apply finsum_eq_sum_of_support_subset
  intro p hp
  apply Finset.mem_range.mpr
  have hpS : p ∈ S := (Set.Finite.mem_toFinset _).mpr hp
  exact lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) hpS)) hM

#print axioms fibreGreen_source
#print axioms fibreGreen_isLeast
#print axioms primeTermNat_finite_support
#print axioms primeGreen_smul
#print axioms primeTerm_degree
#print axioms primeGreen_degree
#print axioms cutoff_diagonal
#print axioms cutoff_stabilizes

end GaloisForLFunctions.HyperbolicArakelovTheory.PrimeFibres
