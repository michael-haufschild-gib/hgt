import GaloisForLFunctions.HTGeometry.FiniteAtomicCubature
import GaloisForLFunctions.RHTower.PrimeArchFiniteKMSLocalMomentClosure

/-!
# The exact finite positive-atomic block law for RH

`RHTower/PrimeArchFiniteKMSLocalMomentClosure.lean` proves that RH is equivalent to
*approximating* every finite initial block of the normalized prime--Gamma moment sequence by
finitely many nonnegative masses at nonnegative nodes.  This module removes the approximation
tolerance: RH is equivalent to **exact** representability of every finite block, with at most
`N + 1` atoms for an `N`-coordinate block
(`primeArchExactFiniteAtomicBlock_iff_riemannHypothesis`).

The forward direction is immediate — an exact witness has zero error.  The converse is the
cubature step.  Under RH the Xi thermal nodes satisfy `∑_j λ_j^{n+1} = m_n` with all `λ_j > 0`, so
with `M = m_0 = ∑_j λ_j` every `λ_j` lies in `[0, M]` and the truncations

`b_J = ∑_{j<J} (λ_j/M) · v(λ_j) + (1 - ∑_{j<J} λ_j/M) · v(0)`,   `v(x) = (1, x, …, x^{N-1})`,

are genuine convex combinations of points of the compact moment arc `momentArc N M`, converging
coordinatewise to `(m_n/M)_{n<N}`.  `HTGeometry/FiniteAtomicCubature.lean` then converts that limit
into an exact convex combination of at most `N + 1` points of the arc, and rescaling by `M`
produces the masses.

The unspent mass is parked at the node `0`, which contributes to the zeroth coordinate only; that
is what makes the truncations convex combinations rather than sub-probability combinations.
-/

noncomputable section

open Set Filter Topology

namespace RHTower


open GaloisForLFunctions.HTGeometry

/-- The moment curve `x ↦ (1, x, …, x^{N-1})`. -/
def momentCurve (N : ℕ) (x : ℝ) : Fin N → ℝ := fun n => x ^ (n : ℕ)

theorem continuous_momentCurve (N : ℕ) : Continuous (momentCurve N) := by
  refine continuous_pi (fun n => ?_)
  exact continuous_pow _

/-- The compact moment arc over `[0, M]`. -/
def momentArc (N : ℕ) (M : ℝ) : Set (Fin N → ℝ) := momentCurve N '' Set.Icc 0 M

theorem isCompact_momentArc (N : ℕ) (M : ℝ) : IsCompact (momentArc N M) :=
  (isCompact_Icc).image (continuous_momentCurve N)

theorem momentArc_nonempty (N : ℕ) {M : ℝ} (hM : 0 ≤ M) : (momentArc N M).Nonempty :=
  ⟨momentCurve N 0, ⟨0, ⟨le_rfl, hM⟩, rfl⟩⟩

/-- Exact finite positive-atomic representability of every finite initial block, with at most
`N + 1` atoms. -/
def FinitePositiveAtomicExactBlock (target : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, ∃ mass node : Fin (N + 1) → ℝ,
    (∀ i, 0 ≤ mass i) ∧ (∀ i, 0 ≤ node i) ∧
      ∀ n : ℕ, n < N → target n = ∑ i, mass i * node i ^ n

theorem finitePositiveAtomicLocalMomentClosure_of_exactBlock {target : ℕ → ℝ}
    (h : FinitePositiveAtomicExactBlock target) :
    FinitePositiveAtomicLocalMomentClosure target := by
  intro N ε hε
  obtain ⟨mass, node, hm, hn, hblock⟩ := h N
  refine ⟨fun n => ∑ i, mass i * node i ^ n, ⟨N + 1, mass, node, hm, hn, rfl⟩, ?_⟩
  intro n hnN
  show dist (∑ i, mass i * node i ^ n) (target n) < ε
  rw [← hblock n hnN, dist_self]
  exact hε


/-! ## RH gives exact finite atomic blocks -/

theorem primeArchExactFiniteAtomicBlock_of_riemannHypothesis (hRH : RiemannHypothesis) :
    FinitePositiveAtomicExactBlock normalizedPrimeArchMoment := by
  classical
  intro N
  set lam : ℕ → ℝ := fun j => xiThermalNode (xiThermalEnumeration j) with hlamdef
  have hlampos : ∀ j, 0 < lam j := fun j => xiThermalNode_pos _
  have hM : HasSum lam (normalizedPrimeArchMoment 0) := by
    have h := hasSum_xiThermalEnumeration_pow_of_rh hRH 0
    simpa [hlamdef] using h
  set M : ℝ := normalizedPrimeArchMoment 0 with hMdef
  have hsum : Summable lam := hM.summable
  have htsum : ∑' j, lam j = M := hM.tsum_eq
  have hMle : ∀ j, lam j ≤ M := by
    intro j
    have h := hsum.le_tsum j (fun i _ => (hlampos i).le)
    rwa [htsum] at h
  have hMpos : 0 < M := lt_of_lt_of_le (hlampos 0) (hMle 0)
  have hpartial : ∀ J : ℕ, ∑ j ∈ Finset.range J, lam j ≤ M := by
    intro J
    have h := hsum.sum_le_tsum (Finset.range J) (fun i _ => (hlampos i).le)
    rwa [htsum] at h
  -- the convex combinations
  set w : ℕ → ℕ → ℝ := fun J j =>
    if j < J then lam j / M else 1 - (∑ i ∈ Finset.range J, lam i) / M with hwdef
  set z : ℕ → ℕ → ℝ := fun J j => if j < J then lam j else 0 with hzdef
  set b : ℕ → (Fin N → ℝ) :=
    fun J => ∑ j ∈ Finset.range (J + 1), w J j • momentCurve N (z J j) with hbdef
  have hwnn : ∀ J j, 0 ≤ w J j := by
    intro J j
    rw [hwdef]
    by_cases hj : j < J
    · simp only [hj, if_true]
      exact div_nonneg (hlampos j).le hMpos.le
    · simp only [hj, if_false]
      have hp := hpartial J
      rw [sub_nonneg, div_le_one hMpos]
      exact hp
  have hwsum : ∀ J, ∑ j ∈ Finset.range (J + 1), w J j = 1 := by
    intro J
    rw [Finset.sum_range_succ]
    have h1 : ∑ j ∈ Finset.range J, w J j = (∑ j ∈ Finset.range J, lam j) / M := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [hwdef]
      simp only [Finset.mem_range.mp hj, if_true]
    have h2 : w J J = 1 - (∑ i ∈ Finset.range J, lam i) / M := by
      rw [hwdef]
      simp
    rw [h1, h2]
    ring
  have hznn : ∀ J j, 0 ≤ z J j := by
    intro J j
    rw [hzdef]
    by_cases hj : j < J
    · simp only [hj, if_true]
      exact (hlampos j).le
    · simp only [hj, if_false]
      exact le_rfl
  have hzle : ∀ J j, z J j ≤ M := by
    intro J j
    rw [hzdef]
    by_cases hj : j < J
    · simp only [hj, if_true]
      exact hMle j
    · simp only [hj, if_false]
      exact hMpos.le
  have hbmem : ∀ J, b J ∈ convexHull ℝ (momentArc N M) := by
    intro J
    refine (convex_convexHull ℝ _).sum_mem (fun j _ => hwnn J j) (hwsum J) (fun j _ => ?_)
    exact subset_convexHull ℝ _ ⟨z J j, ⟨hznn J j, hzle J j⟩, rfl⟩
  -- the limit
  have hlim : Filter.Tendsto b atTop (nhds (fun n : Fin N => normalizedPrimeArchMoment n / M)) := by
    refine tendsto_pi_nhds.mpr (fun n => ?_)
    have hcoord : ∀ J, b J n
        = ∑ j ∈ Finset.range (J + 1), w J j * (z J j) ^ (n : ℕ) := by
      intro J
      rw [hbdef]
      simp [momentCurve, Finset.sum_apply]
    rcases Nat.eq_zero_or_pos (n : ℕ) with hn0 | hn1
    · have hconst : ∀ J, b J n = 1 := by
        intro J
        rw [hcoord J, hn0]
        simpa using hwsum J
      have htarget : normalizedPrimeArchMoment (n : ℕ) / M = 1 := by
        rw [hn0, ← hMdef, div_self hMpos.ne']
      rw [htarget]
      have hfun : (fun J => b J n) = fun _ : ℕ => (1 : ℝ) := funext hconst
      rw [hfun]
      exact tendsto_const_nhds
    · obtain ⟨k, hk⟩ : ∃ k, (n : ℕ) = k + 1 := ⟨(n : ℕ) - 1, by omega⟩
      have hcoord' : ∀ J, b J n = (∑ j ∈ Finset.range J, lam j ^ ((n : ℕ) + 1)) / M := by
        intro J
        rw [hcoord J, Finset.sum_range_succ]
        have hlast : w J J * (z J J) ^ (n : ℕ) = 0 := by
          rw [hzdef]
          simp only [lt_irrefl, if_false]
          rw [zero_pow (by omega), mul_zero]
        rw [hlast, add_zero, Finset.sum_div]
        refine Finset.sum_congr rfl (fun j hj => ?_)
        have hjJ : j < J := Finset.mem_range.mp hj
        rw [hwdef, hzdef]
        simp only [hjJ, if_true]
        rw [div_mul_eq_mul_div, pow_succ']
      have hser := hasSum_xiThermalEnumeration_pow_of_rh hRH (n : ℕ)
      have hpart : Filter.Tendsto
          (fun J => ∑ j ∈ Finset.range J, lam j ^ ((n : ℕ) + 1)) atTop
          (nhds (normalizedPrimeArchMoment (n : ℕ))) := by
        simpa [hlamdef] using hser.tendsto_sum_nat
      have hdiv := hpart.div_const M
      refine hdiv.congr (fun J => (hcoord' J).symm)
  have hmem : (fun n : Fin N => normalizedPrimeArchMoment n / M)
      ∈ closure (convexHull ℝ (momentArc N M)) :=
    mem_closure_of_tendsto hlim (Filter.Eventually.of_forall hbmem)
  obtain ⟨a, Z, hann, hasum, hZmem, hZsum⟩ :=
    exists_atomic_of_mem_closure_convexHull (isCompact_momentArc N M)
      (momentArc_nonempty N hMpos.le) hmem
  choose x hxmem hxeq using hZmem
  refine ⟨fun i => M * a i, x, fun i => mul_nonneg hMpos.le (hann i), fun i => (hxmem i).1, ?_⟩
  intro n hnN
  have hcomp := congrFun hZsum ⟨n, hnN⟩
  have hval : ∑ i, a i * (x i) ^ n = normalizedPrimeArchMoment n / M := by
    rw [← hcomp]
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hxeq i]
    simp [momentCurve]
  have : normalizedPrimeArchMoment n = M * ∑ i, a i * (x i) ^ n := by
    rw [hval]
    field_simp
  rw [this, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => by ring)


/-! ## The exact block law -/

/-- The normalized prime--Gamma source has exact finite positive-atomic blocks. -/
def PrimeArchExactFiniteAtomicBlock : Prop :=
  FinitePositiveAtomicExactBlock normalizedPrimeArchMoment

/-- **Exact finite positive-atomic block law for RH.**  RH is equivalent to *exact* finite
positive-atomic representability of every finite initial prime--Gamma moment block, with at most
`N + 1` atoms for an `N`-coordinate block.  No approximation tolerance is needed. -/
theorem primeArchExactFiniteAtomicBlock_iff_riemannHypothesis :
    PrimeArchExactFiniteAtomicBlock ↔ RiemannHypothesis :=
  ⟨fun h => riemannHypothesis_of_primeArchFinitePositiveAtomicLocalMomentClosure
      (finitePositiveAtomicLocalMomentClosure_of_exactBlock h),
   primeArchExactFiniteAtomicBlock_of_riemannHypothesis⟩

/-- The exact block law and the approximate local closure law agree at the prime--Gamma source. -/
theorem primeArchExactFiniteAtomicBlock_iff_localMomentClosure :
    PrimeArchExactFiniteAtomicBlock ↔ PrimeArchFinitePositiveAtomicLocalMomentClosure :=
  primeArchExactFiniteAtomicBlock_iff_riemannHypothesis.trans
    primeArchFinitePositiveAtomicLocalMomentClosure_iff_riemannHypothesis.symm


end RHTower

end
