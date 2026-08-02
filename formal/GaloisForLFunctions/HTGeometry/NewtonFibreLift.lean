import GaloisForLFunctions.HTGeometry.NewtonFibreInvariant
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Lifting a fibre point along a deformation

Over a base that is complete for an ideal `I`, a factorisation over the horizon deforms with its
coefficients: adding to the two factors any polynomials with coefficients in `I` can be corrected,
below the two critical orders and by coefficients in `I`, so that the corrected pair again inverts
over the horizon.

The proof is the Newton iteration.  Each step solves the linearised equation exactly — which
`existsUnique_coprimeSplit` does over any ring — and `newton_step_contracts` shows the error drops one
power of `I` per step while the correction is itself that small.  Completeness turns the resulting
Cauchy sequence of coefficients into a limit, and the Hausdorff property kills what is left.

This is the step that converts a point of the special fibre into a point of the deformed fibre, and
it is what a count at the special fibre alone can never give.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {S : Type*} [CommRing S]

theorem smodEq_iff_sub_mem {J : Ideal S} {x y : S} :
    x ≡ y [SMOD J • (⊤ : Submodule S S)] ↔ x - y ∈ J := by
  rw [SModEq.sub_mem]
  simp

/-- The invariant carried by the Newton iteration: a state below the critical orders, small, with a
small truncated error. -/
def NewtonGood (I : Ideal S) (m n : ℕ) (A B Γ Γ' : S[X]) (k : ℕ)
    (s : S[X] × S[X] × S[X]) : Prop :=
  s.1.natDegree < m ∧ s.2.1.natDegree < n ∧ CoeffMem I s.1 ∧ CoeffMem I s.2.1 ∧
    s.2.2.natDegree < m + n ∧ CoeffMem (I ^ (k + 1)) s.2.2 ∧
    (X : S[X]) ^ (m + n) ∣ inversionError (A + Γ + s.1) (B + Γ' + s.2.1) - s.2.2

/-- **The iteration can always be advanced.** -/
theorem exists_newtonGood_succ [Nontrivial S] {I : Ideal S} {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {A B : S[X]} (hA : A.Monic) (hAdeg : A.natDegree = m) (hBdeg : B.natDegree ≤ n)
    (hcop : IsCoprime A B) {Γ Γ' : S[X]} (hΓ : CoeffMem I Γ) (hΓ' : CoeffMem I Γ')
    (k : ℕ) (s : S[X] × S[X] × S[X]) (hs : NewtonGood I m n A B Γ Γ' k s) :
    ∃ s' : S[X] × S[X] × S[X], NewtonGood I m n A B Γ Γ' (k + 1) s' ∧
      CoeffMem (I ^ (k + 1)) (s'.1 - s.1) ∧ CoeffMem (I ^ (k + 1)) (s'.2.1 - s.2.1) := by
  obtain ⟨hP, hQ, hPmem, hQmem, hEdeg, hEmem, hErr⟩ := hs
  have hZ : CoeffMem I (A + Γ + s.1 - A) := by
    have : A + Γ + s.1 - A = Γ + s.1 := by ring
    rw [this]
    exact hΓ.add hPmem
  have hW : CoeffMem I (B + Γ' + s.2.1 - B) := by
    have : B + Γ' + s.2.1 - B = Γ' + s.2.1 := by ring
    rw [this]
    exact hΓ'.add hQmem
  obtain ⟨dP, dQ, E', hdP, hdQ, hdPmem, hdQmem, hE'deg, hE'mem, hE'err⟩ :=
    newton_step_contracts hA hAdeg hBdeg hm hn hcop hZ hW hEdeg hEmem hErr
  have hIle : I ^ (k + 1) ≤ I := Ideal.pow_le_self (by omega)
  refine ⟨(s.1 + dP, s.2.1 + dQ, E'), ⟨?_, ?_, ?_, ?_, hE'deg, hE'mem, ?_⟩, ?_, ?_⟩
  · exact lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt hP hdP)
  · exact lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt hQ hdQ)
  · exact hPmem.add (hdPmem.mono hIle)
  · exact hQmem.add (hdQmem.mono hIle)
  · have h1 : A + Γ + (s.1 + dP) = A + Γ + s.1 + dP := by ring
    have h2 : B + Γ' + (s.2.1 + dQ) = B + Γ' + s.2.1 + dQ := by ring
    rw [h1, h2]
    exact hE'err
  · have : s.1 + dP - s.1 = dP := by ring
    rw [this]
    exact hdPmem
  · have : s.2.1 + dQ - s.2.1 = dQ := by ring
    rw [this]
    exact hdQmem

/-- **A deformation of a factorisation over the horizon can be corrected.**  Over a base complete
for `I`, adding coefficients in `I` to the two factors of a factorisation over the horizon can be
compensated below the two critical orders, again by coefficients in `I`. -/
theorem exists_deformed_factorisation [Nontrivial S] (I : Ideal S) [IsAdicComplete I S]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {A B : S[X]} (hA : A.Monic) (hAdeg : A.natDegree = m)
    (hBdeg : B.natDegree ≤ n) (hcop : IsCoprime A B)
    {Γ Γ' : S[X]} (hΓ : CoeffMem I Γ) (hΓ' : CoeffMem I Γ')
    (hAB : (X : S[X]) ^ (m + n) ∣ inversionError A B) :
    ∃ P Q : S[X], P.natDegree < m ∧ Q.natDegree < n ∧ CoeffMem I P ∧ CoeffMem I Q ∧
      (X : S[X]) ^ (m + n) ∣ inversionError (A + Γ + P) (B + Γ' + Q) := by
  classical
  -- the initial state
  have hinit : NewtonGood I m n A B Γ Γ' 0
      (0, 0, (Γ * B + A * Γ' + Γ * Γ') %ₘ X ^ (m + n)) := by
    refine ⟨by rw [Polynomial.natDegree_zero]; omega, by rw [Polynomial.natDegree_zero]; omega,
      fun i => by rw [Polynomial.coeff_zero]; exact I.zero_mem,
      fun i => by rw [Polynomial.coeff_zero]; exact I.zero_mem, ?_, ?_, ?_⟩
    · have hne : (X : S[X]) ^ (m + n) ≠ 1 := by
        intro hcon
        have hdeg := congrArg Polynomial.natDegree hcon
        rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_one] at hdeg
        omega
      have hlt := Polynomial.natDegree_modByMonic_lt (Γ * B + A * Γ' + Γ * Γ')
        (monic_X_pow (R := S) (m + n)) hne
      rwa [Polynomial.natDegree_X_pow] at hlt
    · rw [pow_one]
      refine CoeffMem.modByMonic_X_pow ?_ _
      refine ((CoeffMem.mul hΓ (fun i => Submodule.mem_top)).mono ?_).add ?_ |>.add ?_
      · exact le_of_eq (by rw [Ideal.mul_top])
      · exact (CoeffMem.mul (fun i => Submodule.mem_top) hΓ').mono (le_of_eq (by rw [Ideal.top_mul]))
      · exact (CoeffMem.mul hΓ (fun i => Submodule.mem_top)).mono (le_of_eq (by rw [Ideal.mul_top]))
    · have hdef := inversionError_deformation A B Γ Γ' hAB
      have hsub : inversionError (A + Γ + 0) (B + Γ' + 0)
          - (Γ * B + A * Γ' + Γ * Γ') %ₘ X ^ (m + n)
          = (inversionError (A + Γ) (B + Γ') - (Γ * B + A * Γ' + Γ * Γ'))
            + ((Γ * B + A * Γ' + Γ * Γ') - (Γ * B + A * Γ' + Γ * Γ') %ₘ X ^ (m + n)) := by
        simp only [add_zero]
        ring
      rw [hsub]
      exact dvd_add hdef (X_pow_dvd_sub_modByMonic _ (m + n))
  -- a total step function
  have hchoice : ∀ (k : ℕ) (s : S[X] × S[X] × S[X]), ∃ s' : S[X] × S[X] × S[X],
      NewtonGood I m n A B Γ Γ' k s →
        NewtonGood I m n A B Γ Γ' (k + 1) s' ∧
          CoeffMem (I ^ (k + 1)) (s'.1 - s.1) ∧ CoeffMem (I ^ (k + 1)) (s'.2.1 - s.2.1) := by
    intro k s
    by_cases hs : NewtonGood I m n A B Γ Γ' k s
    · obtain ⟨s', h1, h2, h3⟩ :=
        exists_newtonGood_succ hm hn hA hAdeg hBdeg hcop hΓ hΓ' k s hs
      exact ⟨s', fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨s, fun hc => absurd hc hs⟩
  choose F hF using hchoice
  set seq : ℕ → S[X] × S[X] × S[X] := fun k =>
    Nat.rec (0, 0, (Γ * B + A * Γ' + Γ * Γ') %ₘ X ^ (m + n)) (fun j s => F j s) k with hseq
  have hgood : ∀ k, NewtonGood I m n A B Γ Γ' k (seq k) := by
    intro k
    induction k with
    | zero => exact hinit
    | succ k ih => exact (hF k (seq k) ih).1
  have hdiffP : ∀ k, CoeffMem (I ^ (k + 1)) ((seq (k + 1)).1 - (seq k).1) :=
    fun k => (hF k (seq k) (hgood k)).2.1
  have hdiffQ : ∀ k, CoeffMem (I ^ (k + 1)) ((seq (k + 1)).2.1 - (seq k).2.1) :=
    fun k => (hF k (seq k) (hgood k)).2.2
  -- the sequences of coefficients are Cauchy
  have hcauchy : ∀ (g : ℕ → S[X]) (hg : ∀ k, CoeffMem (I ^ (k + 1)) (g (k + 1) - g k))
      (i j k : ℕ), j ≤ k → (g j).coeff i - (g k).coeff i ∈ I ^ j := by
    intro g hg i j k hjk
    induction k with
    | zero =>
        have : j = 0 := by omega
        subst this
        rw [sub_self]
        exact Submodule.zero_mem _
    | succ k ih =>
        rcases Nat.lt_or_ge j (k + 1) with h | h
        · have hstep : (g k).coeff i - (g (k + 1)).coeff i ∈ I ^ j := by
            have hmem := hg k i
            rw [Polynomial.coeff_sub] at hmem
            have hle : I ^ (k + 1) ≤ I ^ j := Ideal.pow_le_pow_right (by omega)
            rw [← neg_sub]
            exact neg_mem (hle hmem)
          have := ih (by omega)
          have hsum := Submodule.add_mem _ this hstep
          have hrw : (g j).coeff i - (g k).coeff i + ((g k).coeff i - (g (k + 1)).coeff i)
              = (g j).coeff i - (g (k + 1)).coeff i := by ring
          rwa [hrw] at hsum
        · have : j = k + 1 := by omega
          subst this
          rw [sub_self]
          exact Submodule.zero_mem _
  -- limits of the coefficients
  have hlimP : ∀ i : ℕ, ∃ p : S, ∀ k, ((seq k).1.coeff i - p) ∈ I ^ k := by
    intro i
    obtain ⟨p, hp⟩ := IsPrecomplete.prec' (I := I) (M := S) (fun k => (seq k).1.coeff i)
      (fun {j k} hjk => smodEq_iff_sub_mem.2 (hcauchy (fun k => (seq k).1) hdiffP i j k hjk))
    exact ⟨p, fun k => smodEq_iff_sub_mem.1 (hp k)⟩
  have hlimQ : ∀ i : ℕ, ∃ q : S, ∀ k, ((seq k).2.1.coeff i - q) ∈ I ^ k := by
    intro i
    obtain ⟨q, hq⟩ := IsPrecomplete.prec' (I := I) (M := S) (fun k => (seq k).2.1.coeff i)
      (fun {j k} hjk => smodEq_iff_sub_mem.2 (hcauchy (fun k => (seq k).2.1) hdiffQ i j k hjk))
    exact ⟨q, fun k => smodEq_iff_sub_mem.1 (hq k)⟩
  choose p hp using hlimP
  choose q hq using hlimQ
  -- assemble the limits
  have hpzero : ∀ i, m ≤ i → p i = 0 := by
    intro i hi
    refine IsHausdorff.haus' (I := I) (M := S) (p i) (fun k => ?_)
    refine smodEq_iff_sub_mem.2 ?_
    rw [sub_zero]
    have h0 : (seq k).1.coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hgood k).1 hi)
    have := hp i k
    rwa [h0, zero_sub, neg_mem_iff] at this
  have hqzero : ∀ i, n ≤ i → q i = 0 := by
    intro i hi
    refine IsHausdorff.haus' (I := I) (M := S) (q i) (fun k => ?_)
    refine smodEq_iff_sub_mem.2 ?_
    rw [sub_zero]
    have h0 : (seq k).2.1.coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hgood k).2.1 hi)
    have := hq i k
    rwa [h0, zero_sub, neg_mem_iff] at this
  set P : S[X] := ∑ i ∈ Finset.range m, Polynomial.C (p i) * X ^ i with hP
  set Q : S[X] := ∑ i ∈ Finset.range n, Polynomial.C (q i) * X ^ i with hQ
  have hPcoeff : ∀ i, P.coeff i = p i := by
    intro i
    rw [hP, Polynomial.finsetSum_coeff]
    by_cases hi : i < m
    · rw [Finset.sum_eq_single i]
      · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
      · intro b _ hb
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm hb), mul_zero]
      · intro hc
        exact absurd (Finset.mem_range.2 hi) hc
    · have hz : ∀ b ∈ Finset.range m, (Polynomial.C (p b) * X ^ b).coeff i = 0 := by
        intro b hb
        have hbm : b < m := Finset.mem_range.1 hb
        have hne : i ≠ b := by omega
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne, mul_zero]
      rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]
      exact (hpzero i (by omega)).symm
  have hQcoeff : ∀ i, Q.coeff i = q i := by
    intro i
    rw [hQ, Polynomial.finsetSum_coeff]
    by_cases hi : i < n
    · rw [Finset.sum_eq_single i]
      · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
      · intro b _ hb
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm hb), mul_zero]
      · intro hc
        exact absurd (Finset.mem_range.2 hi) hc
    · have hz : ∀ b ∈ Finset.range n, (Polynomial.C (q b) * X ^ b).coeff i = 0 := by
        intro b hb
        have hbn : b < n := Finset.mem_range.1 hb
        have hne : i ≠ b := by omega
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne, mul_zero]
      rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]
      exact (hqzero i (by omega)).symm
  have hPdeg : P.natDegree < m := by
    refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i hi => ?_))
      (by omega : m - 1 < m)
    exact le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _)
      (by have := Finset.mem_range.1 hi; omega)
  have hQdeg : Q.natDegree < n := by
    refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i hi => ?_))
      (by omega : n - 1 < n)
    exact le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _)
      (by have := Finset.mem_range.1 hi; omega)
  have hPmem : CoeffMem I P := by
    intro i
    rw [hPcoeff]
    have h1 := hp i 1
    rw [pow_one] at h1
    have h2 : (seq 1).1.coeff i ∈ I := (hgood 1).2.2.1 i
    have h3 := Submodule.sub_mem I h2 h1
    have hEq : (seq 1).1.coeff i - ((seq 1).1.coeff i - p i) = p i := by ring
    rwa [hEq] at h3
  have hQmem : CoeffMem I Q := by
    intro i
    rw [hQcoeff]
    have h1 := hq i 1
    rw [pow_one] at h1
    have h2 : (seq 1).2.1.coeff i ∈ I := (hgood 1).2.2.2.1 i
    have h3 := Submodule.sub_mem I h2 h1
    have hEq : (seq 1).2.1.coeff i - ((seq 1).2.1.coeff i - q i) = q i := by ring
    rwa [hEq] at h3
  -- the limit inverts over the horizon
  refine ⟨P, Q, hPdeg, hQdeg, hPmem, hQmem, ?_⟩
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd (monic_X_pow (R := S) (m + n))]
  refine Polynomial.ext (fun i => ?_)
  rw [Polynomial.coeff_zero]
  refine IsHausdorff.haus' (I := I) (M := S) _ (fun k => ?_)
  refine smodEq_iff_sub_mem.2 ?_
  rw [sub_zero]
  -- compare with the k-th approximation
  have hPk : CoeffMem (I ^ k) (P - (seq k).1) := by
    intro j
    rw [Polynomial.coeff_sub, hPcoeff]
    rw [← neg_sub]
    exact neg_mem (hp j k)
  have hQk : CoeffMem (I ^ k) (Q - (seq k).2.1) := by
    intro j
    rw [Polynomial.coeff_sub, hQcoeff]
    rw [← neg_sub]
    exact neg_mem (hq j k)
  have hdiff : inversionError (A + Γ + P) (B + Γ' + Q)
      - inversionError (A + Γ + (seq k).1) (B + Γ' + (seq k).2.1)
      = (P - (seq k).1) * (B + Γ' + Q) + (A + Γ + (seq k).1) * (Q - (seq k).2.1) := by
    simp only [inversionError]
    ring
  have hdiffmem : CoeffMem (I ^ k)
      (inversionError (A + Γ + P) (B + Γ' + Q)
        - inversionError (A + Γ + (seq k).1) (B + Γ' + (seq k).2.1)) := by
    rw [hdiff]
    refine CoeffMem.add ?_ ?_
    · exact (CoeffMem.mul hPk (fun _ => Submodule.mem_top)).mono (le_of_eq (by rw [Ideal.mul_top]))
    · exact (CoeffMem.mul (fun _ => Submodule.mem_top) hQk).mono
        (le_of_eq (by rw [Ideal.top_mul]))
  set target : S[X] :=
    (inversionError (A + Γ + P) (B + Γ' + Q)
      - inversionError (A + Γ + (seq k).1) (B + Γ' + (seq k).2.1)) + (seq k).2.2 with htarget
  have htargetmem : CoeffMem (I ^ k) target := by
    refine hdiffmem.add ?_
    exact ((hgood k).2.2.2.2.2.1).mono (Ideal.pow_le_pow_right (by omega))
  have hdvdsub : (X : S[X]) ^ (m + n) ∣ inversionError (A + Γ + P) (B + Γ' + Q) - target := by
    have hrw : inversionError (A + Γ + P) (B + Γ' + Q) - target
        = inversionError (A + Γ + (seq k).1) (B + Γ' + (seq k).2.1) - (seq k).2.2 := by
      rw [htarget]
      ring
    rw [hrw]
    exact (hgood k).2.2.2.2.2.2
  have hmodeq : inversionError (A + Γ + P) (B + Γ' + Q) %ₘ X ^ (m + n)
      = target %ₘ X ^ (m + n) := by
    have hzero : (inversionError (A + Γ + P) (B + Γ' + Q) - target) %ₘ X ^ (m + n) = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd (monic_X_pow (R := S) (m + n))).2 hdvdsub
    have hneg : (-target) %ₘ X ^ (m + n) = -(target %ₘ X ^ (m + n)) := by
      have h0 : target %ₘ X ^ (m + n) + (-target) %ₘ X ^ (m + n) = 0 := by
        rw [← Polynomial.add_modByMonic, add_neg_cancel]
        simp
      linear_combination h0
    have hsplit : (inversionError (A + Γ + P) (B + Γ' + Q) - target) %ₘ X ^ (m + n)
        = inversionError (A + Γ + P) (B + Γ' + Q) %ₘ X ^ (m + n) - target %ₘ X ^ (m + n) := by
      rw [sub_eq_add_neg, Polynomial.add_modByMonic, hneg, ← sub_eq_add_neg]
    rw [hsplit] at hzero
    exact sub_eq_zero.1 hzero
  rw [hmodeq]
  exact (htargetmem.modByMonic_X_pow (m + n)) i

end GaloisForLFunctions.HTGeometry
