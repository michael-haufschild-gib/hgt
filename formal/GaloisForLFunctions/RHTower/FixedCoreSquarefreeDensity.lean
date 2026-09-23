import GaloisForLFunctions.RHTower.PrimeSquareMobiusDensityFracture
import GaloisForLFunctions.RHTower.Sieve.CoprimeLogMoebiusLimit

/-!
# Squarefree density outside a fixed finite prime core

The complete count obeys an exact prime-divisibility recurrence. Two steps
turn its normalized form into the corpus's divided-argument contraction,
proving the factor p/(p+1) for every excluded prime. No density hypothesis
or numerical input is assumed in the finite-core conclusions.
-/

noncomputable section
open Filter Topology
open Finset
namespace RHTower

/-- Squarefree source integers through N whose prime factors avoid P. -/
def fixedCoreSquarefreeIndices (P : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun n => Squarefree n ∧ Disjoint n.primeFactors P)

/-- Count of the complete squarefree source with a fixed processed core excluded. -/
def fixedCoreSquarefreeCount (P : Finset ℕ) (N : ℕ) : ℕ :=
  (fixedCoreSquarefreeIndices P N).card

private lemma mem_insert_core {p n N : ℕ} (hp : p.Prime) (P : Finset ℕ) :
    n ∈ fixedCoreSquarefreeIndices (insert p P) N ↔
      n ∈ fixedCoreSquarefreeIndices P N ∧ ¬p ∣ n := by
  simp only [fixedCoreSquarefreeIndices, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hn, hs, hd⟩
    refine ⟨⟨hn, hs, hd.mono_right (subset_insert _ _)⟩, ?_⟩
    intro hpn
    exact disjoint_left.mp hd (Nat.mem_primeFactors.mpr ⟨hp,hpn,by omega⟩)
      (mem_insert_self _ _)
  · rintro ⟨⟨hn, hs, hd⟩, hpn⟩
    refine ⟨hn, hs, disjoint_left.mpr ?_⟩
    intro q hqn hqp
    rcases mem_insert.mp hqp with he | hqP
    · subst q
      exact hpn (Nat.mem_primeFactors.mp hqn).2.1
    · exact disjoint_left.mp hd hqn hqP

private lemma mem_mul_core {p n : ℕ} (hp : p.Prime) (P : Finset ℕ)
    (hpP : p ∉ P) (hn : 0 < n) :
    Squarefree (p*n) ∧ Disjoint (p*n).primeFactors P ↔
      Squarefree n ∧ Disjoint n.primeFactors (insert p P) := by
  rw [Nat.squarefree_mul_iff, Nat.primeFactors_mul hp.ne_zero hn.ne', hp.primeFactors]
  constructor
  · rintro ⟨⟨hc, _, hs⟩, hd⟩
    refine ⟨hs, disjoint_left.mpr ?_⟩
    intro q hqn hqP
    rcases mem_insert.mp hqP with he | hqP
    · subst q
      exact (hp.coprime_iff_not_dvd.mp hc) (Nat.mem_primeFactors.mp hqn).2.1
    · exact disjoint_left.mp hd (mem_union_right _ hqn) hqP
  · rintro ⟨hs, hd⟩
    refine ⟨⟨hp.coprime_iff_not_dvd.mpr ?_, hp.squarefree, hs⟩,
      disjoint_left.mpr ?_⟩
    · intro hpn
      exact disjoint_left.mp hd (Nat.mem_primeFactors.mpr ⟨hp,hpn,hn.ne'⟩)
        (mem_insert_self _ _)
    · intro q hq hqP
      rcases mem_union.mp hq with hq | hq
      · have he := mem_singleton.mp hq
        subst q
        exact hpP hqP
      · exact disjoint_left.mp hd hq (mem_insert_of_mem hqP)

/-- Exact prime-exclusion count recurrence, including all endpoint cases. -/
theorem fixedCoreSquarefreeCount_insert {p : ℕ} (hp : p.Prime)
    (P : Finset ℕ) (hpP : p ∉ P) (N : ℕ) :
    fixedCoreSquarefreeCount P N = fixedCoreSquarefreeCount (insert p P) N +
      fixedCoreSquarefreeCount (insert p P) (N/p) := by
  let S := fixedCoreSquarefreeIndices P N
  have hfree : S.filter (fun n => ¬p ∣ n) = fixedCoreSquarefreeIndices (insert p P) N := by
    ext n
    exact (mem_filter.trans (mem_insert_core hp P).symm)
  have hdiv : (S.filter (fun n => p ∣ n)).card =
      (fixedCoreSquarefreeIndices (insert p P) (N/p)).card := by
    symm
    apply card_nbij' (fun n => p*n) (fun n => n/p)
    · intro n hn
      have hn' := mem_filter.mp hn
      have hnN := mem_Icc.mp hn'.1
      apply mem_filter.mpr
      refine ⟨?_, dvd_mul_right p n⟩
      apply mem_filter.mpr
      refine ⟨mem_Icc.mpr ⟨by nlinarith [hp.pos], ?_⟩,
        (mem_mul_core hp P hpP (by omega)).mpr hn'.2⟩
      simpa [mul_comm] using (Nat.le_div_iff_mul_le hp.pos).mp hnN.2
    · intro n hn
      obtain ⟨hnS, hpn⟩ := mem_filter.mp hn
      obtain ⟨hnN, hs, hd⟩ := mem_filter.mp hnS
      have hnN' := mem_Icc.mp hnN
      have he : p*(n/p) = n := Nat.mul_div_cancel' hpn
      have hnq : 0 < n/p := by nlinarith
      change n/p ∈ fixedCoreSquarefreeIndices (insert p P) (N/p)
      apply mem_filter.mpr
      refine ⟨mem_Icc.mpr ⟨hnq, Nat.div_le_div_right hnN'.2⟩, ?_⟩
      apply (mem_mul_core hp P hpP hnq).mp
      rw [he]
      exact ⟨hs, hd⟩
    · intro n hn
      exact Nat.mul_div_cancel_left n hp.pos
    · intro n hn
      exact Nat.mul_div_cancel' (mem_filter.mp hn).2
  have hsplit := card_filter_add_card_filter_not (s := S) (fun n => p ∣ n)
  rw [hfree, hdiv] at hsplit
  exact hsplit.symm.trans (Nat.add_comm _ _)

/-- Literal normalized squarefree count at a real cutoff. -/
def fixedCoreSquarefreeRatio (P : Finset ℕ) (Y : ℝ) : ℝ :=
  (fixedCoreSquarefreeCount P ⌊Y⌋₊ : ℝ) / Y

private lemma ratio_bound (P : Finset ℕ) (Y : ℝ) :
    |fixedCoreSquarefreeRatio P Y| ≤ 1 := by
  by_cases hY : 0 < Y
  · have hc : fixedCoreSquarefreeCount P ⌊Y⌋₊ ≤ ⌊Y⌋₊ := by
      simpa [fixedCoreSquarefreeCount, fixedCoreSquarefreeIndices] using
        (card_filter_le (s := Icc 1 ⌊Y⌋₊)
          (fun n => Squarefree n ∧ Disjoint n.primeFactors P))
    unfold fixedCoreSquarefreeRatio
    rw [abs_of_nonneg (by positivity)]
    apply (div_le_one hY).mpr
    exact (show (fixedCoreSquarefreeCount P ⌊Y⌋₊ : ℝ) ≤ (⌊Y⌋₊ : ℝ) by exact_mod_cast hc).trans
      (Nat.floor_le hY.le)
  · simp [fixedCoreSquarefreeRatio, Nat.floor_of_nonpos (le_of_not_gt hY),
      fixedCoreSquarefreeCount, fixedCoreSquarefreeIndices]

private lemma ratio_insert {p : ℕ} (hp : p.Prime) (P : Finset ℕ)
    (hpP : p ∉ P) (Y : ℝ) :
    fixedCoreSquarefreeRatio P Y = fixedCoreSquarefreeRatio (insert p P) Y +
      (1/(p : ℝ))*fixedCoreSquarefreeRatio (insert p P) (Y/p) := by
  unfold fixedCoreSquarefreeRatio
  rw [fixedCoreSquarefreeCount_insert hp P hpP, Nat.floor_div_natCast]
  push_cast
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp

private lemma ratio_prime_step {p : ℕ} (hp : p.Prime) (P : Finset ℕ)
    (hpP : p ∉ P) (L : ℝ)
    (hlim : Tendsto (fixedCoreSquarefreeRatio P) atTop (𝓝 L)) :
    Tendsto (fixedCoreSquarefreeRatio (insert p P)) atTop (𝓝 ((p : ℝ)/(p+1)*L)) := by
  let f := fixedCoreSquarefreeRatio (insert p P)
  let g := fixedCoreSquarefreeRatio P
  let h : ℝ → ℝ := fun Y => g Y - (1/(p : ℝ))*g (Y/p)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hscale : Tendsto (fun Y : ℝ => Y/(p : ℝ)) atTop atTop := by
    simpa [div_eq_mul_inv] using
      (tendsto_mul_const_atTop_of_pos (show 0 < (p : ℝ)⁻¹ by positivity)).mpr
        (tendsto_id : Tendsto id atTop atTop)
  have hh : Tendsto h atTop (𝓝 (L-(1/(p : ℝ))*L)) :=
    hlim.sub ((hlim.comp hscale).const_mul (1/(p : ℝ)))
  have hrec (Y : ℝ) : h Y = f Y - (1/(p : ℝ)^(2 : ℕ))*f (Y/(p : ℝ)^(2 : ℕ)) := by
    dsimp only [h, g]
    rw [ratio_insert hp P hpP Y, ratio_insert hp P hpP (Y/p)]
    change f Y + (1/(p : ℝ))*f (Y/p) -
      (1/(p : ℝ))*(f (Y/p)+(1/(p : ℝ))*f (Y/(p : ℝ)/(p : ℝ))) = _
    rw [div_div, ← pow_two]
    ring
  have hf := Sieve.tendsto_of_div_contraction ((p : ℝ)^(2 : ℕ)) (by nlinarith) f h
    (L-(1/(p : ℝ))*L) 1 (by norm_num) (ratio_bound (insert p P)) hh hrec
  convert hf using 1
  congr 1
  have hm : (p : ℝ)-1 ≠ 0 := by linarith
  have hs : (p : ℝ)^(2 : ℕ)-1 ≠ 0 := by nlinarith
  field_simp
  ring

private lemma count_empty_eq (N : ℕ) :
    (fixedCoreSquarefreeCount ∅ N : ℝ) =
      ∑ n ∈ Icc 1 N, ((ArithmeticFunction.moebius n : ℤ) : ℝ)^(2 : ℕ) := by
  calc
    _ = ∑ n ∈ fixedCoreSquarefreeIndices ∅ N, (1 : ℝ) := by
      simp [fixedCoreSquarefreeCount]
    _ = _ := by
      rw [fixedCoreSquarefreeIndices, sum_filter]
      apply sum_congr rfl
      intro n hn
      by_cases hs : Squarefree n
      · have hm : (1 : ℝ) = ((ArithmeticFunction.moebius n : ℤ) : ℝ)^(2 : ℕ) := by
          exact_mod_cast (ArithmeticFunction.moebius_sq_eq_one_of_squarefree hs).symm
        simpa [hs] using hm
      · simp [hs, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]

private lemma ratio_empty_limit :
    Tendsto (fixedCoreSquarefreeRatio ∅) atTop (𝓝 Sieve.squarefreeDensity) := by
  have h := (tendsto_squarefree_density.comp tendsto_nat_floor_atTop).mul
    (tendsto_nat_floor_div_atTop (R := ℝ))
  rw [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
  have hN : 0 < (⌊Y⌋₊ : ℝ) := by
    have hN := (Nat.one_le_floor_iff Y).mpr hY
    exact_mod_cast (show 0 < ⌊Y⌋₊ by omega)
  rw [fixedCoreSquarefreeRatio, count_empty_eq]
  dsimp only [Function.comp_def]
  field_simp

/-- Exact squarefree density after excluding any fixed finite prime core. -/
theorem tendsto_fixedCoreSquarefreeRatio
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Tendsto (fixedCoreSquarefreeRatio P) atTop
      (𝓝 (Sieve.squarefreeDensity * ∏ p ∈ P, (p : ℝ)/(p+1))) := by
  induction P using Finset.induction_on with
  | empty => simpa using ratio_empty_limit
  | @insert p P hpP ih =>
    have hp := hP p (mem_insert_self p P)
    have hrest := ih (fun q hq => hP q (mem_insert_of_mem hq))
    have hstep := ratio_prime_step hp P hpP _ hrest
    rw [prod_insert hpP]
    convert hstep using 1
    congr 1
    ring

/-- The same density holds for the exact integer-cutoff count. -/
theorem tendsto_fixedCoreSquarefreeCount_div
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Tendsto (fun N : ℕ => (fixedCoreSquarefreeCount P N : ℝ)/(N : ℝ)) atTop
      (𝓝 (Sieve.squarefreeDensity * ∏ p ∈ P, (p : ℝ)/(p+1))) := by
  simpa [Function.comp_def, fixedCoreSquarefreeRatio] using
    (tendsto_fixedCoreSquarefreeRatio P hP).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

end RHTower
