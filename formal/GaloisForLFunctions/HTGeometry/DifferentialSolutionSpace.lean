import Mathlib
import GaloisForLFunctions.HTGeometry.DifferentialIndependence

/-!
# Solutions of a linear differential system are constrained by the constants

For a differential field, the solutions of a first-order linear system `v′ = A v` span a space
measured by the constants, not by the field: every linear relation among solutions can be replaced
by a relation with *constant* coefficients supported inside the original support.

The mechanism is the minimal-support argument.  Normalize one coefficient of a relation to one and
differentiate; the terms `c_j v_j′` reassemble into `A` applied to the relation, hence vanish, so
the derivatives of the coefficients again give a relation — one whose support misses the normalized
index.  Minimality forces every coefficient to be a constant.

Consequences: the solution space of a rank-`n` system has dimension at most `n` over the constants;
for a monic scalar equation of order `n` the same bound holds through the companion system; and if
all the powers of one element solve such an equation, that element satisfies a nonzero polynomial
relation with constant coefficients.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

variable {K : Type*} [Field K] [Differential K]

/-- A solution of the first-order linear differential system with matrix `A`. -/
def IsDifferentialSystemSolution {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : Prop :=
  ∀ i, (v i)′ = A.mulVec v i

/-- **The minimal-support argument.**  A nontrivial linear relation among solutions of a
first-order linear differential system can be replaced by a nontrivial relation with constant
coefficients supported inside the original support. -/
theorem exists_differentialConstants_relation {n : ℕ} {A : Matrix (Fin n) (Fin n) K}
    {ι : Type*} [DecidableEq ι] {v : ι → Fin n → K}
    (hv : ∀ j, IsDifferentialSystemSolution A (v j)) :
    ∀ (s : Finset ι) (c : ι → K), s.Nonempty → (∀ j ∈ s, c j ≠ 0) →
      (∀ i, ∑ j ∈ s, c j * v j i = 0) →
      ∃ (t : Finset ι) (d : ι → K), t.Nonempty ∧ t ⊆ s ∧ (∀ j ∈ t, (d j)′ = 0) ∧
        (∀ j ∈ t, d j ≠ 0) ∧ ∀ i, ∑ j ∈ t, d j * v j i = 0 := by
  classical
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
      intro c hne hsupp hrel
      obtain ⟨j₀, hj₀⟩ := hne
      have hc0 : c j₀ ≠ 0 := hsupp j₀ hj₀
      set c' : ι → K := fun j => c j / c j₀ with hc'
      have hc'j₀ : c' j₀ = 1 := by rw [hc']; exact div_self hc0
      have hc'ne : ∀ j ∈ s, c' j ≠ 0 := by
        intro j hj
        rw [hc']
        exact div_ne_zero (hsupp j hj) hc0
      have hrel' : ∀ i, ∑ j ∈ s, c' j * v j i = 0 := by
        intro i
        have hdiv : ∑ j ∈ s, c' j * v j i = (∑ j ∈ s, c j * v j i) / c j₀ := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun j _ => by rw [hc']; ring
        rw [hdiv, hrel i, zero_div]
      -- differentiating the relation gives a relation among the derivatives of the coefficients
      set d : ι → K := fun j => (c' j)′ with hd
      have hdrel : ∀ i, ∑ j ∈ s, d j * v j i = 0 := by
        intro i
        have hzero : (∑ j ∈ s, c' j * v j i)′ = 0 := by rw [hrel' i, map_zero]
        rw [map_sum] at hzero
        have hleib : ∀ j, (c' j * v j i)′ = c' j * (v j i)′ + v j i * (c' j)′ := by
          intro j
          rw [Derivation.leibniz]
          simp [smul_eq_mul]
        rw [Finset.sum_congr rfl (fun j _ => hleib j)] at hzero
        rw [Finset.sum_add_distrib] at hzero
        have hsys : ∑ j ∈ s, c' j * (v j i)′ = 0 := by
          have hmv : ∀ u : Fin n → K, A.mulVec u i = ∑ k, A i k * u k := by
            intro u
            simp [Matrix.mulVec, dotProduct]
          calc ∑ j ∈ s, c' j * (v j i)′
              = ∑ j ∈ s, c' j * A.mulVec (v j) i := by
                exact Finset.sum_congr rfl fun j _ => by rw [hv j i]
            _ = ∑ j ∈ s, ∑ k, c' j * (A i k * v j k) := by
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [hmv, Finset.mul_sum]
            _ = ∑ k, ∑ j ∈ s, A i k * (c' j * v j k) := by
                rw [Finset.sum_comm]
                exact Finset.sum_congr rfl fun k _ =>
                  Finset.sum_congr rfl fun j _ => by ring
            _ = ∑ k, A i k * ∑ j ∈ s, c' j * v j k := by
                exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
            _ = 0 := by
                refine Finset.sum_eq_zero fun k _ => ?_
                rw [hrel' k, mul_zero]
        rw [hsys, zero_add] at hzero
        rw [← hzero]
        exact Finset.sum_congr rfl fun j _ => by rw [hd]; ring
      have hdj₀ : d j₀ = 0 := by
        show (c' j₀)′ = 0
        rw [hc'j₀]
        simp
      by_cases hall : ∀ j ∈ s, d j = 0
      · refine ⟨s, c', ⟨j₀, hj₀⟩, le_rfl, ?_, hc'ne, hrel'⟩
        intro j hj
        exact hall j hj
      · obtain ⟨j₁, hj₁s, hj₁⟩ : ∃ j ∈ s, d j ≠ 0 := by
          by_contra hcon
          refine hall fun j hj => ?_
          by_contra hne
          exact hcon ⟨j, hj, hne⟩
        set t := s.filter (fun j => d j ≠ 0) with ht
        have htsub : t ⊆ s := Finset.filter_subset _ _
        have htne : t.Nonempty := ⟨j₁, by rw [ht]; exact Finset.mem_filter.2 ⟨hj₁s, hj₁⟩⟩
        have htlt : t ⊂ s := by
          refine ⟨htsub, ?_⟩
          intro hcon
          have hmem : j₀ ∈ t := hcon hj₀
          rw [ht, Finset.mem_filter] at hmem
          exact hmem.2 hdj₀
        have htrel : ∀ i, ∑ j ∈ t, d j * v j i = 0 := by
          intro i
          have hsum : ∑ j ∈ t, d j * v j i = ∑ j ∈ s, d j * v j i := by
            refine Finset.sum_subset (f := fun j => d j * v j i) htsub ?_
            intro j hjs hjt
            rw [ht, Finset.mem_filter] at hjt
            have hdj : d j = 0 := by
              by_contra hne
              exact hjt ⟨hjs, hne⟩
            rw [hdj, zero_mul]
          rw [hsum, hdrel i]
        obtain ⟨t', d', ht'ne, ht'sub, ht'const, ht'nz, ht'rel⟩ :=
          ih t htlt d htne (fun j hj => by
            rw [ht, Finset.mem_filter] at hj; exact hj.2) htrel
        exact ⟨t', d', ht'ne, ht'sub.trans htsub, ht'const, ht'nz, ht'rel⟩

/-- The same statement for a relation whose coefficients may vanish, provided one of them does
not. -/
theorem exists_differentialConstants_relation_of_ne_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) K}
    {ι : Type*} [DecidableEq ι] {v : ι → Fin n → K}
    (hv : ∀ j, IsDifferentialSystemSolution A (v j))
    (s : Finset ι) (c : ι → K) {j₀ : ι} (hj₀ : j₀ ∈ s) (hcj₀ : c j₀ ≠ 0)
    (hrel : ∀ i, ∑ j ∈ s, c j * v j i = 0) :
    ∃ (t : Finset ι) (d : ι → K), t.Nonempty ∧ (∀ j ∈ t, (d j)′ = 0) ∧
      (∀ j ∈ t, d j ≠ 0) ∧ ∀ i, ∑ j ∈ t, d j * v j i = 0 := by
  classical
  set s' := s.filter (fun j => c j ≠ 0) with hs'
  have hs'sub : s' ⊆ s := Finset.filter_subset _ _
  have hj₀' : j₀ ∈ s' := by rw [hs']; exact Finset.mem_filter.2 ⟨hj₀, hcj₀⟩
  have hrel' : ∀ i, ∑ j ∈ s', c j * v j i = 0 := by
    intro i
    have hsum : ∑ j ∈ s', c j * v j i = ∑ j ∈ s, c j * v j i := by
      refine Finset.sum_subset (f := fun j => c j * v j i) hs'sub ?_
      intro j hjs hjs'
      rw [hs', Finset.mem_filter] at hjs'
      have hcj : c j = 0 := by
        by_contra hne
        exact hjs' ⟨hjs, hne⟩
      rw [hcj, zero_mul]
    rw [hsum, hrel i]
  obtain ⟨t, d, htne, -, hconst, hnz, hdrel⟩ :=
    exists_differentialConstants_relation hv s' c ⟨j₀, hj₀'⟩
      (fun j hj => by rw [hs', Finset.mem_filter] at hj; exact hj.2) hrel'
  exact ⟨t, d, htne, hconst, hnz, hdrel⟩

/-- **The solution space of a rank-`n` differential system has dimension at most `n` over the
constants.** -/
theorem card_le_of_no_differentialConstants_relation {n : ℕ} {A : Matrix (Fin n) (Fin n) K}
    {ι : Type*} [DecidableEq ι] [Fintype ι] {v : ι → Fin n → K}
    (hv : ∀ j, IsDifferentialSystemSolution A (v j))
    (hindep : ∀ (t : Finset ι) (d : ι → K), t.Nonempty → (∀ j ∈ t, (d j)′ = 0) →
      (∀ j ∈ t, d j ≠ 0) → ∃ i, ∑ j ∈ t, d j * v j i ≠ 0) :
    Fintype.card ι ≤ n := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  have hnli : ¬ LinearIndependent K v := by
    intro hli
    have hle := hli.fintype_card_le_finrank
    rw [Module.finrank_fin_fun K] at hle
    omega
  obtain ⟨g, hg, j₀, hj₀⟩ := Fintype.not_linearIndependent_iff.1 hnli
  have hrel : ∀ i, ∑ j ∈ Finset.univ, g j * v j i = 0 := by
    intro i
    have hfun := congrFun hg i
    simpa [Finset.sum_apply] using hfun
  obtain ⟨t, d, htne, hconst, hnz, hdrel⟩ :=
    exists_differentialConstants_relation_of_ne_zero hv Finset.univ g
      (Finset.mem_univ j₀) hj₀ hrel
  obtain ⟨i, hi⟩ := hindep t d htne hconst hnz
  exact hi (hdrel i)

/-! ### Scalar equations -/

open GaloisForLFunctions

/-- The companion matrix of the monic scalar operator `y⁽ⁿ⁾ = ∑ a i y⁽ⁱ⁾`. -/
def scalarCompanion {n : ℕ} (a : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => if (i : ℕ) + 1 = n then a j else if (j : ℕ) = (i : ℕ) + 1 then 1 else 0

/-- The jet vector of a solution of a monic scalar equation solves the companion system. -/
theorem isDifferentialSystemSolution_jetVec {n : ℕ} (a : Fin n → K) {x : K}
    (hx : differentialJet n x = ∑ j, a j * differentialJet (j : ℕ) x) :
    IsDifferentialSystemSolution (scalarCompanion a)
      (fun i : Fin n => differentialJet (i : ℕ) x) := by
  classical
  intro i
  have hmv : ∀ u : Fin n → K, (scalarCompanion a).mulVec u i = ∑ k, scalarCompanion a i k * u k := by
    intro u
    simp [Matrix.mulVec, dotProduct]
  by_cases hi : (i : ℕ) + 1 = n
  · have hlhs : (differentialJet (i : ℕ) x)′ = differentialJet n x := by
      have h1 : differentialJet ((i : ℕ) + 1) x = differentialJet n x := by rw [hi]
      rw [← h1, differentialJet_succ]
    rw [hlhs, hmv, hx]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [scalarCompanion, hi]
  · have hilt : (i : ℕ) + 1 < n := lt_of_le_of_ne i.2 hi
    set i' : Fin n := ⟨(i : ℕ) + 1, hilt⟩ with hi'
    have hlhs : (differentialJet (i : ℕ) x)′ = differentialJet ((i : ℕ) + 1) x := by
      rw [differentialJet_succ]
    rw [hlhs, hmv]
    rw [Finset.sum_eq_single i']
    · simp [scalarCompanion, hi, hi']
    · intro k _ hk
      have hkne : (k : ℕ) ≠ (i : ℕ) + 1 := by
        intro hcon
        exact hk (Fin.ext hcon)
      simp [scalarCompanion, hi, hkne]
    · intro hcon
      exact absurd (Finset.mem_univ i') hcon

/-- **At most `n` solutions of a monic scalar equation of order `n` are independent over the
constants.** -/
theorem card_le_of_no_constantRelation_scalar {n : ℕ} (a : Fin n → K)
    {ι : Type*} [DecidableEq ι] [Fintype ι] {x : ι → K}
    (hx : ∀ j, differentialJet n (x j) = ∑ i, a i * differentialJet (i : ℕ) (x j))
    (hindep : ∀ (t : Finset ι) (d : ι → K), t.Nonempty → (∀ j ∈ t, (d j)′ = 0) →
      (∀ j ∈ t, d j ≠ 0) → ∑ j ∈ t, d j * x j ≠ 0) :
    Fintype.card ι ≤ n := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hzero : ∀ j : ι, x j = 0 := by
      intro j
      have h := hx j
      simpa using h
    have hempty : IsEmpty ι := by
      refine ⟨fun j => ?_⟩
      refine hindep {j} (fun _ => 1) ⟨j, Finset.mem_singleton_self j⟩ (fun _ _ => by simp)
        (fun _ _ => one_ne_zero) ?_
      rw [Finset.sum_singleton, hzero j, mul_zero]
    exact le_of_eq (Fintype.card_eq_zero_iff.mpr hempty)
  · refine card_le_of_no_differentialConstants_relation
      (A := scalarCompanion a) (v := fun j => fun i : Fin n => differentialJet (i : ℕ) (x j))
      (fun j => isDifferentialSystemSolution_jetVec a (hx j)) ?_
    intro t d htne hconst hnz
    refine ⟨⟨0, hn⟩, ?_⟩
    have hval : ∀ j : ι, differentialJet ((⟨0, hn⟩ : Fin n) : ℕ) (x j) = x j := by
      intro j
      simp
    rw [Finset.sum_congr rfl (fun j _ => by rw [hval j])]
    exact hindep t d htne hconst hnz

/-- **A power family of solutions is algebraically dependent over the constants.**  If every power
`x ^ i` with `i ≤ n` solves a monic scalar equation of order `n`, then `x` is a root of a nonzero
polynomial relation with constant coefficients. -/
theorem exists_constantCoeff_relation_of_powers {n : ℕ} (a : Fin n → K) {x : K}
    (hx : ∀ m : Fin (n + 1), differentialJet n (x ^ (m : ℕ))
      = ∑ i, a i * differentialJet (i : ℕ) (x ^ (m : ℕ))) :
    ∃ d : Fin (n + 1) → K, (∀ m, (d m)′ = 0) ∧ (∃ m, d m ≠ 0) ∧
      ∑ m, d m * x ^ (m : ℕ) = 0 := by
  classical
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hindep : ∀ (t : Finset (Fin (n + 1))) (d : Fin (n + 1) → K), t.Nonempty →
      (∀ j ∈ t, (d j)′ = 0) → (∀ j ∈ t, d j ≠ 0) →
      ∑ j ∈ t, d j * x ^ (j : ℕ) ≠ 0 := by
    intro t d htne hconst hnz hrel
    set d' : Fin (n + 1) → K := fun j => if j ∈ t then d j else 0 with hd'
    have hd'const : ∀ m, (d' m)′ = 0 := by
      intro m
      by_cases hm : m ∈ t
      · simp only [hd', if_pos hm]
        exact hconst m hm
      · simp only [hd', if_neg hm]
        simp
    have hd'ne : ∃ m, d' m ≠ 0 := by
      obtain ⟨j, hj⟩ := htne
      exact ⟨j, by simp only [hd', if_pos hj]; exact hnz j hj⟩
    have hd'rel : ∑ m, d' m * x ^ (m : ℕ) = 0 := by
      have hsum : ∑ m, d' m * x ^ (m : ℕ) = ∑ j ∈ t, d j * x ^ (j : ℕ) := by
        rw [← Finset.sum_subset (Finset.subset_univ t)]
        · exact Finset.sum_congr rfl fun j hj => by simp only [hd', if_pos hj]
        · intro j _ hj
          simp only [hd', if_neg hj, zero_mul]
      rw [hsum, hrel]
    obtain ⟨m, hm⟩ := hd'ne
    exact hcon d' hd'const ⟨m, hm⟩ hd'rel
  have hcard := card_le_of_no_constantRelation_scalar a (x := fun m : Fin (n + 1) => x ^ (m : ℕ))
    hx hindep
  simp at hcard

end

end GaloisForLFunctions.HTGeometry
