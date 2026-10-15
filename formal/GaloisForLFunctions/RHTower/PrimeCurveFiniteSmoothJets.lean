import GaloisForLFunctions.RHTower.PrimeCurveFiniteSmoothModels
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Data.Nat.PrimeFin

/-!
# Derivatives of finite-smoothness prime-curve models

The model `finiteSmoothModel k` has derivative at zero equal to the coordinate
reader over primes at most `2^k`. Its Riesz representative is the finite prime
indicator vector, and its norm is exactly the square root of the prime count.

`exists_finiteSmoothGerm_with_derivative` closes the finite-order construction,
including its exact first derivative and norm. `no_bounded_all_prime_reader`
records the Hilbert-space contradiction needed after proving actual-curve
Taylor rigidity. This file does not prove that rigidity, construct Kummer
continuation, or certify a zero-free half-strip.
-/

open Filter Set Topology

namespace RHTower.PrimeCurveModel

noncomputable def cutoffReader (N : ℕ) : PrimeHilbert →L[ℝ] ℝ :=
  ∑ n ∈ Finset.range (N + 1), if hn : Nat.Prime n then
    lp.evalCLM ℝ (fun _ : Nat.Primes => ℝ) 2 ⟨n, hn⟩ else 0

noncomputable def cutoffVector (N : ℕ) : PrimeHilbert :=
  ∑ n ∈ Finset.range (N + 1), if hn : Nat.Prime n then
    lp.single 2 ⟨n, hn⟩ (1 : ℝ) else 0

theorem cutoffReader_apply (N : ℕ) (x : PrimeHilbert) :
    cutoffReader N x = ∑ n ∈ Finset.range (N + 1),
      if hn : Nat.Prime n then x ⟨n, hn⟩ else 0 := by
  simp only [cutoffReader, sum_apply]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> rfl

theorem cutoffReader_eq_toDualMap (N : ℕ) :
    cutoffReader N = InnerProductSpace.toDualMap ℝ PrimeHilbert (cutoffVector N) := by
  ext x
  rw [cutoffReader_apply, InnerProductSpace.toDualMap_apply_apply, cutoffVector, sum_inner]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs with hn
  · simp only [lp.inner_single_left, Real.inner_apply, one_mul]
  · simp

theorem cutoffVector_apply (N : ℕ) (p : Nat.Primes) :
    cutoffVector N p = if p.val ≤ N then 1 else 0 := by
  classical
  rw [cutoffVector, lp.coeFn_sum, Finset.sum_apply]
  have hterm (n : ℕ) :
      (if hn : Nat.Prime n then lp.single 2 ⟨n, hn⟩ (1 : ℝ) else (0 : PrimeHilbert)) p =
        if n = p.val then 1 else 0 := by
    by_cases hn : Nat.Prime n
    · by_cases heq : n = p.val
      · subst n
        simp [hn, lp.single_apply]
      · have hp : p ≠ (⟨n, hn⟩ : Nat.Primes) := by
          intro h
          exact heq (congrArg Subtype.val h).symm
        simp [hn, heq, lp.single_apply, hp]
    · have heq : n ≠ p.val := fun h => hn (h ▸ p.property)
      simp [hn, heq]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_iff]

theorem hasFDerivAt_lowPrimeLog (k : ℕ) :
    HasFDerivAt (lowPrimeLog k) (cutoffReader (2 ^ k)) 0 := by
  unfold lowPrimeLog cutoffReader
  apply HasFDerivAt.fun_sum
  intro n _
  by_cases hn : Nat.Prime n
  · simp only [dif_pos hn]
    have h := (((hasFDerivAt_const (1 : ℝ) (0 : PrimeHilbert)).sub
      (lp.evalCLM ℝ (fun _ : Nat.Primes => ℝ) 2 ⟨n, hn⟩).hasFDerivAt).log (by
        change (1 : ℝ) - 0 ≠ 0
        norm_num)).neg
    simpa using! h
  · simp only [dif_neg hn]
    exact hasFDerivAt_const 0 0

theorem hasFDerivAt_finiteSmoothModel {k : ℕ} (hk : 1 ≤ k) :
    HasFDerivAt (finiteSmoothModel k) (cutoffReader (2 ^ k)) 0 := by
  have ht : ContDiffAt ℝ k (primeTail k) 0 :=
    (contDiffOn_primeTail k).contDiffAt (isOpen_Ioo.mem_nhds
      ⟨neg_neg_of_pos (Real.exp_pos _), Real.exp_pos _⟩)
  have hd : HasDerivAt (primeTail k) 0 0 := by
    have h := (ht.differentiableAt (by exact_mod_cast (Nat.ne_of_gt hk))).hasDerivAt
    have hz := iteratedDeriv_primeTail_zero k hk
    rw [iteratedDeriv_one] at hz
    simpa only [hz] using h
  have htail := hd.comp_hasFDerivAt (0 : PrimeHilbert)
    (lp.evalCLM ℝ (fun _ : Nat.Primes => ℝ) 2 ⟨2, Nat.prime_two⟩).hasFDerivAt
  have h := (hasFDerivAt_lowPrimeLog k).add htail
  simpa only [finiteSmoothModel, zero_smul, add_zero, Function.comp_def, Pi.add_apply] using! h

theorem cutoffReader_vector (N : ℕ) :
    cutoffReader N (cutoffVector N) =
      (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ) := by
  rw [cutoffReader_apply]
  calc
    (∑ n ∈ Finset.range (N + 1), if hn : Nat.Prime n then cutoffVector N ⟨n, hn⟩ else 0)
        = ∑ n ∈ Finset.range (N + 1), if Nat.Prime n then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      split_ifs <;> simp [cutoffVector_apply, hnN]
    _ = _ := by rw [← Finset.sum_filter]; simp

theorem norm_cutoffReader_sq (N : ℕ) :
    ‖cutoffReader N‖ ^ 2 = (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ) := by
  calc
    ‖cutoffReader N‖ ^ 2 = ‖cutoffVector N‖ ^ 2 := by
      rw [cutoffReader_eq_toDualMap, (InnerProductSpace.toDualMap ℝ PrimeHilbert).norm_map]
    _ = inner ℝ (cutoffVector N) (cutoffVector N) := (real_inner_self_eq_norm_sq _).symm
    _ = cutoffReader N (cutoffVector N) := by rw [cutoffReader_eq_toDualMap]; rfl
    _ = _ := cutoffReader_vector N

theorem norm_cutoffReader (N : ℕ) :
    ‖cutoffReader N‖ = Real.sqrt (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ) := by
  simpa only [Real.sqrt_sq (norm_nonneg _)] using congrArg Real.sqrt (norm_cutoffReader_sq N)

theorem norm_cutoffVector (N : ℕ) :
    ‖cutoffVector N‖ = Real.sqrt (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ) := by
  rw [← norm_cutoffReader]
  rw [cutoffReader_eq_toDualMap, (InnerProductSpace.toDualMap ℝ PrimeHilbert).norm_map]

theorem fderiv_finiteSmoothModel {k : ℕ} (hk : 1 ≤ k) :
    fderiv ℝ (finiteSmoothModel k) 0 = cutoffReader (2 ^ k) :=
  (hasFDerivAt_finiteSmoothModel hk).fderiv

theorem norm_fderiv_finiteSmoothModel {k : ℕ} (hk : 1 ≤ k) :
    ‖fderiv ℝ (finiteSmoothModel k) 0‖ =
      Real.sqrt (((Finset.range (2 ^ k + 1)).filter Nat.Prime).card : ℝ) := by
  rw [fderiv_finiteSmoothModel hk, norm_cutoffReader]

theorem cutoffReader_single (N : ℕ) (p : Nat.Primes) :
    cutoffReader N (lp.single 2 p (1 : ℝ)) = if p.val ≤ N then 1 else 0 := by
  rw [cutoffReader_eq_toDualMap, InnerProductSpace.toDualMap_apply_apply, lp.inner_single_right,
    Real.inner_apply, mul_one, cutoffVector_apply]

theorem norm_lowerBound_of_prime_coordinates (N : ℕ) (T : PrimeHilbert →L[ℝ] ℝ)
    (hT : ∀ p : Nat.Primes, p.val ≤ N → T (lp.single 2 p (1 : ℝ)) = 1) :
    Real.sqrt (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ) ≤ ‖T‖ := by
  have hvalue : T (cutoffVector N) = (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ) := by
    rw [cutoffVector, map_sum]
    calc
      (∑ n ∈ Finset.range (N + 1), T (if hn : Nat.Prime n then
          lp.single 2 ⟨n, hn⟩ (1 : ℝ) else 0))
          = ∑ n ∈ Finset.range (N + 1), if Nat.Prime n then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
        split_ifs with hp
        · exact hT ⟨n, hp⟩ hnN
        · exact map_zero T
      _ = _ := by rw [← Finset.sum_filter]; simp
  have hbound := T.le_opNorm (cutoffVector N)
  rw [hvalue, Real.norm_of_nonneg (Nat.cast_nonneg _), norm_cutoffVector] at hbound
  have hnonneg := Real.sqrt_nonneg (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg ((Finset.range (N + 1)).filter Nat.Prime).card)
  by_cases hz : Real.sqrt (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ) = 0
  · rw [hz]
    exact norm_nonneg T
  · have hpos : 0 < Real.sqrt (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ) :=
      lt_of_le_of_ne hnonneg (Ne.symm hz)
    nlinarith

theorem no_bounded_all_prime_reader :
    ¬ ∃ T : PrimeHilbert →L[ℝ] ℝ, ∀ p : Nat.Primes, T (lp.single 2 p (1 : ℝ)) = 1 := by
  rintro ⟨T, hT⟩
  let v : PrimeHilbert := (InnerProductSpace.toDual ℝ PrimeHilbert).symm T
  have hv (p : Nat.Primes) : v p = 1 := by
    have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := PrimeHilbert)
      (x := lp.single 2 p (1 : ℝ)) (y := T)
    simpa only [v, lp.inner_single_right, Real.inner_apply, mul_one, hT p] using h
  have hs : Summable (fun _ : Nat.Primes => (1 : ℝ)) := by
    have h := (lp.memℓp v).summable (by norm_num)
    simpa only [hv, norm_one, Real.one_rpow] using h
  have h := (summable_const_iff (1 : ℝ)).mp hs
  norm_num at h

theorem exists_finiteSmoothGerm_with_derivative (k : ℕ) :
    ∃ G : PrimeHilbert → ℝ, ∃ ε : ℝ, 0 < ε ∧
      ContDiffOn ℝ (k + 1) G (Metric.ball 0 ε) ∧
      (∀ σ : ℝ, ∀ hσ : 1 < σ,
        G (primeCurve σ (by linarith)) = Real.log ‖riemannZeta (σ : ℂ)‖) ∧
      fderiv ℝ G 0 = cutoffReader (2 ^ (k + 1)) ∧
      ‖fderiv ℝ G 0‖ = Real.sqrt
        (((Finset.range (2 ^ (k + 1) + 1)).filter Nat.Prime).card : ℝ) :=
  ⟨finiteSmoothModel (k + 1), modelRadius, modelRadius_pos, contDiffOn_finiteSmoothModel (k + 1),
    fun _ hσ => finiteSmoothModel_eq_log_norm_zeta (k + 1) hσ,
    fderiv_finiteSmoothModel (Nat.succ_le_succ (Nat.zero_le k)),
    norm_fderiv_finiteSmoothModel (Nat.succ_le_succ (Nat.zero_le k))⟩

end RHTower.PrimeCurveModel
