import Mathlib.RingTheory.RootsOfUnity.Complex
import GaloisForLFunctions.BezoutValuationIncidence.CyclotomicIncidenceRecurrenceAndArbitraryPhaseObservability

/-!
# Exact recurrence complexity of a response is the totient mass of its Selberg support

Character orthogonality `Σ_{ζ^d = 1} ζ^k = d [d ∣ k]` turns a level-`N` response into a finite
exponential sum over roots of unity graded by order:

`s(k) = Σ_{ζ ∈ T_N} Y(ord ζ) ζ^k`,  `T_N = {ζ : ζ^d = 1 for some d ≤ N}`,

with `Y(q) = Σ_{q ∣ d ≤ N} c(d)/d` the Selberg coordinate. So `P(E) s(n) = Σ_ζ Y(ord ζ) P(ζ) ζ^n`.
The characters `n ↦ ζ^n` are linearly independent (Dedekind), hence:

* `P(E)` kills the response exactly when `P` vanishes at every primitive `q`-th root with
  `Y(q) ≠ 0`, i.e. exactly when `∏_{Y(q) ≠ 0} Φ_q ∣ P`;
* the shortest recurrence of the response is `∏_{Y(q) ≠ 0} Φ_q`, of order
  `Σ_{Y(q) ≠ 0} φ(q)`: the recurrence complexity of a row is the totient mass of its Selberg
  support.

For a class of rows whose Selberg coordinates vanish off a set `S`, every phase window of
`Σ_{q ∈ S} φ(q)` consecutive response values determines the row on `[1, N]`. With `S = [1, N]`
this is the universal cyclotomic horizon; a row with a single Selberg mode `q` needs only `φ(q)`.
-/

open Finset Polynomial GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-! ## §1. The roots-of-unity spectrum of a response -/

/-- Character orthogonality: `Σ_{ζ^d = 1} ζ^k = d [d ∣ k]`. -/
theorem sum_nthRootsFinset_pow {d : ℕ} (hd : 0 < d) (k : ℕ) :
    ∑ ζ ∈ nthRootsFinset d (1 : ℂ), ζ ^ k = if d ∣ k then (d : ℂ) else 0 := by
  have hω := Complex.isPrimitiveRoot_exp d hd.ne'
  set ω := Complex.exp (2 * ↑Real.pi * Complex.I / ↑d)
  split_ifs with hdk
  · rw [sum_congr rfl fun ζ hζ => ?_, sum_const, hω.card_nthRootsFinset, nsmul_eq_mul, mul_one]
    obtain ⟨t, rfl⟩ := hdk
    rw [pow_mul, (mem_nthRootsFinset hd 1).mp hζ, one_pow]
  · have hωk : ω ^ k ≠ 1 := fun h => hdk ((hω.pow_eq_one_iff_dvd k).mp h)
    have hωd : ω ^ (d - 1) * ω = 1 := by rw [← pow_succ, Nat.sub_add_cancel hd, hω.pow_eq_one]
    -- rotating by `ω` permutes the `d`-th roots of unity
    have hrot : ∑ ζ ∈ nthRootsFinset d (1 : ℂ), ζ ^ k =
        ∑ ζ ∈ nthRootsFinset d (1 : ℂ), ω ^ k * ζ ^ k := by
      refine sum_nbij' (fun ζ => ω ^ (d - 1) * ζ) (fun ζ => ω * ζ) ?_ ?_ ?_ ?_ ?_
      · intro ζ hζ
        rw [mem_nthRootsFinset hd] at hζ ⊢
        rw [mul_pow, ← pow_mul, mul_comm (d - 1), pow_mul, hω.pow_eq_one, one_pow, one_mul, hζ]
      · intro ζ hζ
        rw [mem_nthRootsFinset hd] at hζ ⊢
        rw [mul_pow, hω.pow_eq_one, hζ, one_mul]
      · intro ζ _
        rw [← mul_assoc, mul_comm ω, hωd, one_mul]
      · intro ζ _
        rw [← mul_assoc, hωd, one_mul]
      · intro ζ _
        rw [mul_pow, ← mul_assoc, ← mul_pow, mul_comm ω, hωd, one_pow, one_mul]
    rw [← mul_sum] at hrot
    have h0 : (1 - ω ^ k) * ∑ ζ ∈ nthRootsFinset d (1 : ℂ), ζ ^ k = 0 := by
      rw [sub_mul, one_mul, ← hrot, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hωk.symm)

/-- The roots of unity of order at most `N`. -/
def responseRoots (N : ℕ) : Finset ℂ :=
  (Icc 1 N).biUnion fun d => nthRootsFinset d (1 : ℂ)

theorem orderOf_mem_Icc_of_mem_responseRoots {N : ℕ} {ζ : ℂ} (hζ : ζ ∈ responseRoots N) :
    orderOf ζ ∈ Icc 1 N := by
  obtain ⟨d, hd, hζd⟩ := mem_biUnion.mp hζ
  have hd0 := (mem_Icc.mp hd).1
  have hpow := (mem_nthRootsFinset hd0 1).mp hζd
  have hpos : 0 < orderOf ζ := orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨d, hd0, hpow⟩)
  exact mem_Icc.mpr ⟨hpos, (Nat.le_of_dvd hd0 (orderOf_dvd_iff_pow_eq_one.mpr hpow)).trans
    (mem_Icc.mp hd).2⟩

theorem primitiveRoot_mem_responseRoots {N q : ℕ} (hq : q ∈ Icc 1 N) {μ : ℂ}
    (hμ : IsPrimitiveRoot μ q) : μ ∈ responseRoots N :=
  mem_biUnion.mpr ⟨q, hq, (mem_nthRootsFinset (mem_Icc.mp hq).1 1).mpr hμ.pow_eq_one⟩

/-- **Spectral form of a response.** `s(k) = Σ_{ζ ∈ T_N} Y(ord ζ) ζ^k`. -/
theorem sieveSeq_eq_sum_responseRoots (N : ℕ) (c : ℕ → ℝ) (k : ℕ) :
    (sieveSeq N c k : ℂ) =
      ∑ ζ ∈ responseRoots N, (selbergMultiplesCoord N c (orderOf ζ) : ℂ) * ζ ^ k := by
  have h1 : (sieveSeq N c k : ℂ) = ∑ d ∈ Icc 1 N,
      ∑ ζ ∈ nthRootsFinset d (1 : ℂ), ((c d / d : ℝ) : ℂ) * ζ ^ k := by
    rw [sieveSeq, sum_filter, Complex.ofReal_sum]
    refine sum_congr rfl fun d hd => ?_
    have hd0 := (mem_Icc.mp hd).1
    have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    rw [← mul_sum, sum_nthRootsFinset_pow hd0]
    split_ifs
    · push_cast
      field_simp
    · simp
  rw [h1, sum_comm' (t' := responseRoots N)
    (s' := fun ζ => (Icc 1 N).filter fun d => orderOf ζ ∣ d)]
  · refine sum_congr rfl fun ζ _ => ?_
    rw [← sum_mul, selbergMultiplesCoord, Complex.ofReal_sum]
  · intro d ζ
    simp only [responseRoots, mem_filter, mem_biUnion]
    constructor
    · rintro ⟨hd, hζ⟩
      exact ⟨⟨hd, orderOf_dvd_iff_pow_eq_one.mpr ((mem_nthRootsFinset (mem_Icc.mp hd).1 1).mp hζ)⟩,
        d, hd, hζ⟩
    · rintro ⟨⟨hd, hdvd⟩, -⟩
      exact ⟨hd, (mem_nthRootsFinset (mem_Icc.mp hd).1 1).mpr (orderOf_dvd_iff_pow_eq_one.mp hdvd)⟩

/-- `P(E)` acts on the spectrum by multiplication with `P(ζ)`. -/
theorem aeval_sieveSeq_eq_sum_responseRoots (P : ℝ[X]) (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    ((aeval sequenceUnitShift P (sieveSeq N c) n : ℝ) : ℂ) =
      ∑ ζ ∈ responseRoots N,
        (selbergMultiplesCoord N c (orderOf ζ) : ℂ) * aeval ζ P * ζ ^ n := by
  rw [aeval_sequenceUnitShift_apply, Complex.ofReal_sum]
  simp_rw [Complex.ofReal_mul, sieveSeq_eq_sum_responseRoots, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun ζ _ => ?_
  rw [aeval_eq_sum_range, mul_sum, sum_mul]
  refine sum_congr rfl fun i _ => ?_
  rw [Complex.real_smul, pow_add]
  ring

/-! ## §2. Upper and lower recurrence laws -/

theorem aeval_cyclotomic_primitiveRoot {q : ℕ} (hq : 0 < q) {μ : ℂ} (hμ : IsPrimitiveRoot μ q) :
    aeval μ (cyclotomic q ℝ) = 0 := by
  rw [aeval_def, ← eval_map, map_cyclotomic]
  exact hμ.isRoot_cyclotomic hq

/-- **Upper law.** If the Selberg coordinates vanish off `S`, then `∏_{q ∈ S} Φ_q(E)` kills the
response. -/
theorem aeval_prod_cyclotomic_sieveSeq_of_support {N : ℕ} {c : ℕ → ℝ} {S : Finset ℕ}
    (hS : ∀ q ∈ Icc 1 N, q ∉ S → selbergMultiplesCoord N c q = 0) :
    aeval sequenceUnitShift (∏ q ∈ S, cyclotomic q ℝ) (sieveSeq N c) = 0 := by
  funext n
  rw [Pi.zero_apply, ← Complex.ofReal_eq_zero, aeval_sieveSeq_eq_sum_responseRoots]
  refine sum_eq_zero fun ζ hζ => ?_
  have hord := orderOf_mem_Icc_of_mem_responseRoots hζ
  by_cases hmem : orderOf ζ ∈ S
  · rw [map_prod, prod_eq_zero hmem (aeval_cyclotomic_primitiveRoot (mem_Icc.mp hord).1
      (IsPrimitiveRoot.orderOf ζ)), mul_zero, zero_mul]
  · rw [hS _ hord hmem, Complex.ofReal_zero, zero_mul, zero_mul]

/-- Distinct characters `n ↦ ζ^n` are linearly independent. -/
theorem eq_zero_of_sum_mul_pow_eq_zero (T : Finset ℂ) (a : ℂ → ℂ)
    (h : ∀ n : ℕ, ∑ ζ ∈ T, a ζ * ζ ^ n = 0) : ∀ ζ ∈ T, a ζ = 0 := by
  have hli : LinearIndependent ℂ fun ζ : ℂ => (⇑(powersHom ℂ ζ) : Multiplicative ℕ → ℂ) :=
    (linearIndependent_monoidHom (Multiplicative ℕ) ℂ).comp (fun ζ => powersHom ℂ ζ)
      (powersHom ℂ).injective
  refine linearIndependent_iff'.mp hli T a ?_
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, powersHom_apply]
  exact h (Multiplicative.toAdd x)

/-- A real polynomial vanishing at every primitive `q`-th root of unity is a multiple of `Φ_q`. -/
theorem cyclotomic_dvd_of_aeval_primitiveRoots {q : ℕ} (hq : 0 < q) {P : ℝ[X]}
    (h : ∀ μ : ℂ, IsPrimitiveRoot μ q → aeval μ P = 0) : cyclotomic q ℝ ∣ P := by
  have hmap : cyclotomic q ℂ ∣ P.map (algebraMap ℝ ℂ) := by
    rw [cyclotomic_eq_prod_X_sub_primitiveRoots (Complex.isPrimitiveRoot_exp q hq.ne')]
    refine prod_dvd_of_coprime
      ((pairwise_coprime_X_sub_C (s := fun μ : ℂ => μ) fun _ _ h => h).set_pairwise _)
      fun μ hμ => ?_
    rw [dvd_iff_isRoot, IsRoot.def, eval_map, ← aeval_def]
    exact h μ ((mem_primitiveRoots hq).mp hμ)
  rwa [← map_cyclotomic q (algebraMap ℝ ℂ),
    map_dvd_map _ (algebraMap ℝ ℂ).injective (cyclotomic.monic q ℝ)] at hmap

/-- **Lower law.** A recurrence of the response vanishes at every primitive root whose order
carries a nonzero Selberg coordinate, so it is a multiple of that `Φ_q`. -/
theorem cyclotomic_dvd_of_aeval_sieveSeq {N : ℕ} {c : ℕ → ℝ} {P : ℝ[X]}
    (hP : aeval sequenceUnitShift P (sieveSeq N c) = 0) {q : ℕ} (hq : q ∈ Icc 1 N)
    (hY : selbergMultiplesCoord N c q ≠ 0) : cyclotomic q ℝ ∣ P := by
  have hzero := eq_zero_of_sum_mul_pow_eq_zero (responseRoots N)
    (fun ζ => (selbergMultiplesCoord N c (orderOf ζ) : ℂ) * aeval ζ P) fun n => by
      rw [← aeval_sieveSeq_eq_sum_responseRoots, hP, Pi.zero_apply, Complex.ofReal_zero]
  refine cyclotomic_dvd_of_aeval_primitiveRoots (mem_Icc.mp hq).1 fun μ hμ => ?_
  have h := hzero μ (primitiveRoot_mem_responseRoots hq hμ)
  rw [← hμ.eq_orderOf] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hY)

/-! ## §3. The exact complexity -/

/-- The Selberg support `{q ≤ N : Y(q) ≠ 0}` of a row. -/
def selbergSpectralSupport (N : ℕ) (c : ℕ → ℝ) : Finset ℕ :=
  (Icc 1 N).filter fun q => selbergMultiplesCoord N c q ≠ 0

/-- The minimal recurrence `∏_{Y(q) ≠ 0} Φ_q` of the response. -/
def selbergSpectralPolynomial (N : ℕ) (c : ℕ → ℝ) : ℝ[X] :=
  ∏ q ∈ selbergSpectralSupport N c, cyclotomic q ℝ

/-- The recurrence complexity `Σ_{Y(q) ≠ 0} φ(q)` of a row. -/
def selbergRecurrenceComplexity (N : ℕ) (c : ℕ → ℝ) : ℕ :=
  ∑ q ∈ selbergSpectralSupport N c, q.totient

theorem selbergSpectralPolynomial_monic (N : ℕ) (c : ℕ → ℝ) :
    (selbergSpectralPolynomial N c).Monic :=
  monic_prod_of_monic _ _ fun q _ => cyclotomic.monic q ℝ

theorem natDegree_selbergSpectralPolynomial (N : ℕ) (c : ℕ → ℝ) :
    (selbergSpectralPolynomial N c).natDegree = selbergRecurrenceComplexity N c := by
  rw [selbergSpectralPolynomial, natDegree_prod_of_monic _ _ fun q _ => cyclotomic.monic q ℝ]
  exact sum_congr rfl fun q _ => natDegree_cyclotomic q ℝ

theorem aeval_selbergSpectralPolynomial_sieveSeq (N : ℕ) (c : ℕ → ℝ) :
    aeval sequenceUnitShift (selbergSpectralPolynomial N c) (sieveSeq N c) = 0 :=
  aeval_prod_cyclotomic_sieveSeq_of_support fun q hq hqS => by
    by_contra hY
    exact hqS (mem_filter.mpr ⟨hq, hY⟩)

/-- **Minimality.** Every recurrence of the response is a multiple of the spectral polynomial. -/
theorem selbergSpectralPolynomial_dvd_of_aeval {N : ℕ} {c : ℕ → ℝ} {P : ℝ[X]}
    (hP : aeval sequenceUnitShift P (sieveSeq N c) = 0) :
    selbergSpectralPolynomial N c ∣ P :=
  prod_dvd_of_coprime (fun _ _ _ _ hqq' => isCoprime_cyclotomic_real hqq') fun _ hq =>
    cyclotomic_dvd_of_aeval_sieveSeq hP (mem_filter.mp hq).1 (mem_filter.mp hq).2

/-- **Exact complexity.** A nonzero recurrence of the response has order at least the totient mass
of the Selberg support, and the spectral polynomial attains it. -/
theorem selbergRecurrenceComplexity_le_natDegree {N : ℕ} {c : ℕ → ℝ} {P : ℝ[X]} (hP0 : P ≠ 0)
    (hP : aeval sequenceUnitShift P (sieveSeq N c) = 0) :
    selbergRecurrenceComplexity N c ≤ P.natDegree := by
  rw [← natDegree_selbergSpectralPolynomial]
  exact natDegree_le_of_dvd (selbergSpectralPolynomial_dvd_of_aeval hP) hP0

/-! ## §4. Observability inside a support class -/

theorem sieveSeq_sub_rows (N : ℕ) (c b : ℕ → ℝ) (k : ℕ) :
    sieveSeq N (fun d => c d - b d) k = sieveSeq N c k - sieveSeq N b k := by
  simp only [sieveSeq, sum_sub_distrib]

/-- **Support-class observability at every phase.** Two rows whose Selberg coordinates vanish off
`S` and whose responses agree on `Σ_{q ∈ S} φ(q)` consecutive integers agree on `[1, N]`. -/
theorem eq_of_sieveSeq_window_of_support {N A : ℕ} {S : Finset ℕ} {c b : ℕ → ℝ}
    (hc : ∀ q ∈ Icc 1 N, q ∉ S → selbergMultiplesCoord N c q = 0)
    (hb : ∀ q ∈ Icc 1 N, q ∉ S → selbergMultiplesCoord N b q = 0)
    (hwin : ∀ k ∈ Ico A (A + ∑ q ∈ S, q.totient), sieveSeq N c k = sieveSeq N b k) :
    ∀ d ∈ Icc 1 N, c d = b d := by
  set r : ℕ → ℝ := fun d => c d - b d
  have hr : ∀ q ∈ Icc 1 N, q ∉ S → selbergMultiplesCoord N r q = 0 := fun q hq hqS => by
    rw [selbergMultiplesCoord_sub, hc q hq hqS, hb q hq hqS, sub_zero]
  have hmon : (∏ q ∈ S, cyclotomic q ℝ).Monic := monic_prod_of_monic _ _ fun q _ =>
    cyclotomic.monic q ℝ
  have hdeg : (∏ q ∈ S, cyclotomic q ℝ).natDegree = ∑ q ∈ S, q.totient := by
    rw [natDegree_prod_of_monic _ _ fun q _ => cyclotomic.monic q ℝ]
    exact sum_congr rfl fun q _ => natDegree_cyclotomic q ℝ
  have hprop := eq_zero_of_aeval_monic hmon (aeval_prod_cyclotomic_sieveSeq_of_support hr)
    (by
      rw [hdeg]
      intro k hk
      rw [sieveSeq_sub_rows, hwin k hk, sub_self])
  have hzero := eq_zero_of_sieveSeq_initial (N := N) (c := r) fun k _ => by
    rw [← sieveSeq_add_mul_factorial N r k A]
    exact hprop _ (le_add_left (Nat.le_mul_of_pos_right A (Nat.factorial_pos N)))
  exact fun d hd => sub_eq_zero.mp (hzero d hd)

end

end GaloisForLFunctions.BezoutValuationIncidence
