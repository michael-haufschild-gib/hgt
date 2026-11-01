import GaloisForLFunctions.RHTower.ZetaJetExtraction

/-!
# Prime-frequency separation of positive dilation jets

The incidence matrix of positive integer multiples is triangular when dilations
are ordered. Polynomial uniqueness at cofinite prime logarithms then makes the
normalized jet rows span every finite packet of distinct positive real dilations.
Currying extends this separation to multilinear tests on distinct primes.
-/

set_option autoImplicit false
open Finset
open scoped Classical
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.DilationPrimeJets

noncomputable section
variable {ι : Type*} [Fintype ι]

/-- Incidence of positive integer multiples among a finite dilation packet. -/
def incidence (r : ι → ℝ) (j i : ι) : ℂ :=
  if ∃ n : ℕ, 0 < n ∧ r j = n * r i then (r i : ℂ) else 0

/-- Prime-frequency jet coefficient after removing the common logarithm and decay. -/
def primeJet (r : ι → ℝ) (j : ι) (p : ℕ) (i : ι) (k : ℕ) : ℂ :=
  incidence r j i * (-(r j : ℂ)) ^ k * (Real.log p : ℂ) ^ k

omit [Fintype ι] in
theorem incidence_self (r : ι → ℝ) (j : ι) : incidence r j j = (r j : ℂ) := by
  classical
  exact if_pos ⟨1, Nat.zero_lt_one, by simp⟩

omit [Fintype ι] in
private theorem incidence_le (r : ι → ℝ) (hr : ∀ i, 0 < r i) (j i : ι)
    (h : incidence r j i ≠ 0) : r i ≤ r j := by
  classical
  have hm : ∃ n : ℕ, 0 < n ∧ r j = n * r i := by
    by_contra hm
    exact h (if_neg hm)
  obtain ⟨n, hn, he⟩ := hm
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [he]
  nlinarith only [hr i, hn']

/-- Ordering a nonzero coefficient's dilation first makes the incidence system triangular. -/
theorem incidence_kernel_eq_zero (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hinj : Function.Injective r) (c : ι → ℂ)
    (h : ∀ j, ∑ i, c i * incidence r j i = 0) : ∀ i, c i = 0 := by
  classical
  intro i
  by_contra hi
  let S : Finset ι := univ.filter (fun i => c i ≠ 0)
  have hS : S.Nonempty := ⟨i, by simp [S, hi]⟩
  obtain ⟨j, hj, hmin⟩ := S.exists_min_image r hS
  have hcj : c j ≠ 0 := (mem_filter.mp hj).2
  have hrow : (∑ i, c i * incidence r j i) = c j * incidence r j j := by
    apply sum_eq_single j
    · intro b _ hbj
      by_cases hb : c b = 0
      · simp only [hb, zero_mul]
      · have hbj' : r j ≤ r b := hmin b (by simp [S, hb])
        have hz : incidence r j b = 0 := by
          by_contra hz
          have he : r b = r j := le_antisymm (incidence_le r hr j b hz) hbj'
          exact hbj (hinj he)
        simp only [hz, mul_zero]
    · simp
  have hc := h j
  rw [hrow, incidence_self] at hc
  have hrj : (r j : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hr j))
  exact mul_ne_zero hcj hrj hc

/-- Cofinitely many prime rows detect every jet coefficient, even for irrational dilations. -/
theorem primeJet_tail_independent (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hinj : Function.Injective r) (J : ℕ) (c : ι → ℕ → ℂ) (S : Finset ℕ)
    (h : ∀ j p, p.Prime → p ∉ S →
      ∑ i, ∑ k ∈ range (J+1), c i k * primeJet r j p i k = 0) :
    ∀ i k, k ≤ J → c i k = 0 := by
  classical
  have hrow : ∀ j k, k ≤ J → ∑ i, c i k * incidence r j i = 0 := by
    intro j k hk
    let a : ℕ → ℂ := fun k => (∑ i, c i k * incidence r j i) * (-(r j : ℂ))^k
    have ha : ∀ p : ℕ, p.Prime → p ∉ S →
        ∑ k ∈ range (J+1), a k * (Real.log p : ℂ)^k = 0 := by
      intro p hp hpS
      calc
        _ = ∑ i, ∑ k ∈ range (J+1), c i k * primeJet r j p i k := by
          simp only [a, sum_mul]
          rw [sum_comm]
          apply sum_congr rfl
          intro i _
          apply sum_congr rfl
          intro k _
          simp only [primeJet]
          ring
        _ = 0 := h j p hp hpS
    have hak := coeff_eq_zero_of_forall_prime_root a S ha k hk
    have hrj : -(r j : ℂ) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast (ne_of_gt (hr j)))
    exact (mul_eq_zero.mp hak).resolve_right (pow_ne_zero _ hrj)
  intro i k hk
  exact incidence_kernel_eq_zero r hr hinj (fun i => c i k) (fun j => hrow j k hk) i

/-- The finite-coordinate form of cofinite prime-jet independence. -/
theorem primeJet_tail_independent_fin (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hinj : Function.Injective r) (J : ℕ) (c : ι → Fin (J+1) → ℂ) (S : Finset ℕ)
    (h : ∀ j p, p.Prime → p ∉ S →
      ∑ i, ∑ k : Fin (J+1), c i k * primeJet r j p i k = 0) : ∀ i k, c i k = 0 := by
  classical
  let a : ι → ℕ → ℂ := fun i k => if hk : k < J+1 then c i ⟨k,hk⟩ else 0
  have hz := primeJet_tail_independent r hr hinj J a S (by
    intro j p hp hpS
    convert h j p hp hpS using 1
    apply sum_congr rfl
    intro i _
    apply sum_bij (fun k hk => (⟨k,mem_range.mp hk⟩ : Fin (J+1)))
    · intro k hk; exact mem_univ _
    · intro k hk l hl he; exact congrArg Fin.val he
    · intro k _; exact ⟨k,mem_range.mpr k.isLt,rfl⟩
    · intro k hk
      simp only [a, dif_pos (mem_range.mp hk)])
  intro i k
  have hk := hz i k (by omega)
  simpa only [a, dif_pos k.isLt] using hk

/-- The finite packet of jet coordinates at one target prime frequency. -/
def primeJetVector (r : ι → ℝ) (J : ℕ) (j : ι) (p : ℕ) : (ι × Fin (J+1)) → ℂ :=
  fun ik => primeJet r j p ik.1 ik.2

private def coordinateVector {κ : Type*} (i : κ) : κ → ℂ :=
  fun j => if j = i then 1 else 0

private theorem linearMap_coordinates {κ : Type*} [Fintype κ]
    (L : (κ → ℂ) →ₗ[ℂ] ℂ) (v : κ → ℂ) :
    L v = ∑ i, v i * L (coordinateVector i) := by
  classical
  have hv : v = ∑ i, v i • (coordinateVector i : κ → ℂ) := by
    funext k
    rw [Finset.sum_apply, sum_eq_single k]
    · simp [coordinateVector]
    · intro i _ hik
      simp only [Pi.smul_apply, coordinateVector, if_neg (Ne.symm hik), smul_zero]
    · simp
  calc
    L v = L (∑ i, v i • (coordinateVector i : κ → ℂ)) := congrArg L hv
    _ = ∑ i, v i * L (coordinateVector i) := by
      rw [map_sum]
      apply sum_congr rfl
      intro i _
      rw [map_smul, smul_eq_mul]

/-- A linear functional vanishing on the cofinite prime rows is zero. -/
theorem linearMap_eq_zero_of_primeJet (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hinj : Function.Injective r) (J : ℕ) (S : Finset ℕ)
    (L : ((ι × Fin (J+1)) → ℂ) →ₗ[ℂ] ℂ)
    (h : ∀ j p, p.Prime → p ∉ S → L (primeJetVector r J j p) = 0) : L = 0 := by
  classical
  have hc := primeJet_tail_independent_fin r hr hinj J
    (fun i k => L (coordinateVector (i,k))) S (by
      intro j p hp hpS
      have hh := h j p hp hpS
      rw [linearMap_coordinates, Fintype.sum_prod_type] at hh
      simpa only [primeJetVector, mul_comm] using hh)
  apply DFunLike.ext
  intro v
  change L v = 0
  rw [linearMap_coordinates]
  apply sum_eq_zero
  intro ik _
  rw [hc ik.1 ik.2, mul_zero]

/-- Distinct-prime testing detects every multilinear form on a finite dilation-jet packet. -/
theorem multilinearMap_eq_zero_of_distinct_primeJets (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hinj : Function.Injective r) (J : ℕ) : ∀ D : ℕ,
    ∀ M : MultilinearMap ℂ (fun _ : Fin D => (ι × Fin (J+1)) → ℂ) ℂ,
    ∀ S : Finset ℕ,
    (∀ (j : Fin D → ι) (p : Fin D → ℕ), (∀ k, (p k).Prime) →
      Function.Injective p → (∀ k, p k ∉ S) →
      M (fun k => primeJetVector r J (j k) (p k)) = 0) → M = 0 := by
  classical
  intro D
  induction D with
  | zero =>
    intro M S h
    apply DFunLike.ext
    intro v
    change M v = 0
    have hz := h Fin.elim0 Fin.elim0 (fun k => Fin.elim0 k)
      (fun k => Fin.elim0 k) (fun k => Fin.elim0 k)
    have hv : (fun k => primeJetVector r J (Fin.elim0 k) (Fin.elim0 k)) = v :=
      funext fun k => Fin.elim0 k
    simpa only [hv] using hz
  | succ D ih =>
    intro M S h
    have hhead : ∀ (j0 : ι) (p0 : ℕ), p0.Prime → p0 ∉ S →
        M.curryLeft (primeJetVector r J j0 p0) = 0 := by
      intro j0 p0 hp0 hp0S
      apply ih _ (insert p0 S)
      intro j p hp hpinj hpS
      have hpneq : ∀ k, p k ≠ p0 := fun k he =>
        hpS k (mem_insert.mpr (Or.inl he))
      have hpout : ∀ k, p k ∉ S := fun k hk => hpS k (mem_insert_of_mem hk)
      have hpcons : ∀ k : Fin (D+1), Nat.Prime ((Fin.cons p0 p : Fin (D+1) → ℕ) k) := by
        intro k
        exact Fin.cases (motive := fun k => Nat.Prime ((Fin.cons p0 p : Fin (D+1) → ℕ) k)) hp0 hp k
      have hconsinj : Function.Injective (Fin.cons p0 p : Fin (D+1) → ℕ) := by
        intro a b hab
        revert hab
        refine Fin.cases ?_ (fun a => ?_) a
        · refine Fin.cases ?_ (fun b => ?_) b
          · intro _; rfl
          · intro hab
            exact False.elim (hpneq b hab.symm)
        · refine Fin.cases ?_ (fun b => ?_) b
          · intro hab
            exact False.elim (hpneq a hab)
          · intro hab
            exact congrArg Fin.succ (hpinj hab)
      have hpconsS : ∀ k, (Fin.cons p0 p : Fin (D+1) → ℕ) k ∉ S :=
        Fin.cases hp0S hpout
      have hz := h (Fin.cons j0 j : Fin (D+1) → ι) (Fin.cons p0 p : Fin (D+1) → ℕ) hpcons hconsinj hpconsS
      change M (Fin.cons (primeJetVector r J j0 p0)
        (fun k => primeJetVector r J (j k) (p k))) = 0
      have he : (fun k : Fin (D+1) => primeJetVector r J
          ((Fin.cons j0 j : Fin (D+1) → ι) k) ((Fin.cons p0 p : Fin (D+1) → ℕ) k)) =
          Fin.cons (primeJetVector r J j0 p0)
            (fun k => primeJetVector r J (j k) (p k)) := by
        funext k
        exact Fin.cases rfl (fun _ => rfl) k
      rwa [he] at hz
    apply DFunLike.ext
    intro v
    change M v = 0
    let L : ((ι × Fin (J+1)) → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun x => M.curryLeft x (Fin.tail v)
        map_add' := by
          intro x y
          rw [map_add]
          rfl
        map_smul' := by
          intro c x
          rw [map_smul]
          rfl }
    have hL : L = 0 := linearMap_eq_zero_of_primeJet r hr hinj J S L (by
      intro j p hp hpS
      change M.curryLeft (primeJetVector r J j p) (Fin.tail v) = 0
      rw [hhead j p hp hpS]
      rfl)
    have hv := congrArg (fun f : ((ι × Fin (J+1)) → ℂ) →ₗ[ℂ] ℂ => f (v 0)) hL
    change M (Fin.cons (v 0) (Fin.tail v)) = 0 at hv
    have he : Fin.cons (v 0) (Fin.tail v) = v := by
      funext k
      exact Fin.cases rfl (fun _ => rfl) k
    simpa only [he] using hv

#print axioms incidence_kernel_eq_zero
#print axioms primeJet_tail_independent
#print axioms primeJet_tail_independent_fin
#print axioms linearMap_eq_zero_of_primeJet
#print axioms multilinearMap_eq_zero_of_distinct_primeJets
end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.DilationPrimeJets
