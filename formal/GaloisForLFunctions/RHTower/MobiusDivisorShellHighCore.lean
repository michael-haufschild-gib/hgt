import GaloisForLFunctions.RHTower.MobiusDivisorShellAnchorComplexity

noncomputable section
open Finset Set Filter Topology MeasureTheory
namespace RHTower

/-- Pair-inactive processed primes can only lower the physical head. -/
theorem head_le_unit_of_pair_inactive (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime) {x : ℝ}
    (hpair : ∀ q ∈ Q, ∀ r ∈ Q, x ≤ (q : ℝ) * r) :
    mobiusDivisorContinuousHead Q x ≤ divisorContinuousUnitHead x := by
  have heq := head_shell_over_base ∅ Q (by simp) hQ (by simp) hpair
  simp only [Finset.empty_union] at heq
  have hs : 0 ≤ ∑ q ∈ Q, Real.sqrt q * divisorContinuousUnitHead (x/q) := by
    apply sum_nonneg
    intro q hq
    exact mul_nonneg (Real.sqrt_nonneg _) (divisorContinuousUnitHead_nonneg _)
  have hs' : 0 ≤ ∑ q ∈ Q,
      Real.sqrt q * mobiusDivisorContinuousHead ∅ (x/q) := by
    simpa [mobiusDivisorContinuousHead] using hs
  simpa [mobiusDivisorContinuousHead] using
    (show mobiusDivisorContinuousHead Q x ≤ mobiusDivisorContinuousHead ∅ x by
      rw [heq]
      linarith only [hs'])

/-- Even an arbitrarily dense old core above `N` cannot compensate the fresh
    `(2N,3N]` shell near `7N/2`: all two-prime products are inactive. -/
theorem shell_head_high_core_bound (Q : Finset ℕ) (N : ℕ)
    (hN : 4 ≤ N) (hQ : ∀ q ∈ Q, q.Prime ∧ N < q)
    (hdis : Disjoint Q (GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)))
    {x : ℝ} (hxl : (7/2:ℝ)*N ≤ x) (hxu : x ≤ (15/4:ℝ)*N) :
    mobiusDivisorContinuousHead
      (Q ∪ GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) x ≤
    (2 - ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)/200) *
      Real.sqrt N := by
  let P := GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)
  have hprime : ∀ p ∈ P, p.Prime := fun p hp =>
    (GaloisForLFunctions.HTGeometry.mem_primesInIoc hp).1
  have hQprime : ∀ q ∈ Q, q.Prime := fun q hq => (hQ q hq).1
  have hNreal : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hlow : ∀ q ∈ Q ∪ P, (N:ℝ) ≤ q := by
    intro q hq
    rcases mem_union.mp hq with hq | hq
    · exact_mod_cast (hQ q hq).2.le
    · have h := (GaloisForLFunctions.HTGeometry.mem_primesInIoc hq).2.1
      exact_mod_cast (show N ≤ q by omega)
  have hpair : ∀ q ∈ Q ∪ P, ∀ r ∈ Q ∪ P, x ≤ (q:ℝ)*r := by
    intro q hq r hr
    have hmul : (N:ℝ)*N ≤ (q:ℝ)*r := by
      calc
        (N:ℝ)*N ≤ q*N := mul_le_mul_of_nonneg_right (hlow q hq) (by positivity)
        _ ≤ q*r := mul_le_mul_of_nonneg_left (hlow r hr) (by positivity)
    have hNbound : (15/4:ℝ)*N ≤ (N:ℝ)*N := by
      nlinarith [mul_nonneg (show (0:ℝ) ≤ (N:ℝ)-4 by linarith)
        (show (0:ℝ) ≤ (N:ℝ) by positivity)]
    exact hxu.trans (hNbound.trans hmul)
  have hsum : (P.card:ℝ)*Real.sqrt N/200 ≤
      ∑ p ∈ P, Real.sqrt p * divisorContinuousUnitHead (x/p) := by
    calc
      _ = ∑ _p ∈ P, Real.sqrt N/200 := by
        simp only [sum_const,nsmul_eq_mul]
        ring
      _ ≤ _ := sum_le_sum (fun p hp => by
        exact anchor_shell_term_floor (by omega) hp hxl hxu)
  have hx0 : 0 ≤ x := by
    have hN0 : (0:ℝ) < N := by positivity
    linarith
  have hroot : Real.sqrt x ≤ 2*Real.sqrt N := by
    have hxSq := Real.sq_sqrt hx0
    have hNSq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg (N:ℝ)]
  have hAll : ∀ p ∈ Q ∪ P, p.Prime := by
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · exact hQprime p hp
    · exact hprime p hp
  have heq := head_shell_over_base ∅ (Q ∪ P) (by simp) hAll (by simp) hpair
  simp only [Finset.empty_union] at heq
  rw [sum_union hdis] at heq
  have hQsum : 0 ≤ ∑ q ∈ Q, Real.sqrt q * mobiusDivisorContinuousHead ∅ (x/q) := by
    apply sum_nonneg
    intro q hq
    exact mul_nonneg (Real.sqrt_nonneg _) (by
      simpa [mobiusDivisorContinuousHead] using divisorContinuousUnitHead_nonneg (x/q))
  have hsum' : (P.card:ℝ)*Real.sqrt N/200 ≤
      ∑ p ∈ P, Real.sqrt p * mobiusDivisorContinuousHead ∅ (x/p) := by
    simpa [mobiusDivisorContinuousHead] using hsum
  have hbase : mobiusDivisorContinuousHead ∅ x ≤ Real.sqrt x := by
    calc
      mobiusDivisorContinuousHead ∅ x = divisorContinuousUnitHead x := by
        simp [mobiusDivisorContinuousHead]
      _ ≤ (3/5:ℝ)*Real.sqrt x := divisorContinuousUnitHead_le_sqrt x
      _ ≤ Real.sqrt x := by nlinarith [Real.sqrt_nonneg x]
  rw [heq]
  nlinarith only [hQsum, hsum', hbase, hroot]

/-- A dense high-prime old core incurs the same quantitative shell mean debt
    as the empty core, regardless of its cardinality. -/
theorem shell_dilationMean_high_core_barrier (Q : Finset ℕ) (N : ℕ)
    (hN : 4 ≤ N) (hQ : ∀ q ∈ Q, q.Prime ∧ N < q)
    (hdis : Disjoint Q (GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)))
    (hcard : (800:ℝ) ≤
      ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)) :
    ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)^2 /
      (40960000*(N:ℝ)) ≤
    mobiusDivisorDilationMean
      (Q ∪ GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) 1 := by
  apply anchor_shell_mean_lower_of_head Q N (by omega)
  intro x hxl hxu
  have h := shell_head_high_core_bound Q N hN hQ hdis hxl hxu
  have hs : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  nlinarith only [h, hcard, hs,
    mul_nonneg (show (0:ℝ) ≤
      ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)-800 by
        linarith) hs]

/-- Processing *all* primes in `(N,2N]` before the next dense shell still
    leaves divergent physical mean. High-prime density cannot be payment. -/
theorem tendsto_shell_dilationMean_over_dense_high_core_atTop :
    Tendsto (fun N : ℕ => mobiusDivisorDilationMean
      (GaloisForLFunctions.HTGeometry.primesInIoc N (2*N) ∪
        GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) 1)
      atTop atTop := by
  let k : ℕ → ℝ := fun N =>
    ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)
  have hcardTop : Tendsto (fun N : ℕ => k N/Real.sqrt N) atTop atTop :=
    tendsto_shell_card_div_sqrt
  have hpow : Tendsto (fun x : ℝ => x^2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)
  have hscaled : Tendsto (fun N : ℕ => (k N/Real.sqrt N)^2/40960000)
      atTop atTop :=
    (hpow.comp hcardTop).atTop_div_const (by norm_num : (0:ℝ)<40960000)
  have hbound : ∀ᶠ N : ℕ in atTop,
      (k N/Real.sqrt N)^2/40960000 ≤
        mobiusDivisorDilationMean
          (GaloisForLFunctions.HTGeometry.primesInIoc N (2*N) ∪
            GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) 1 := by
    filter_upwards [hcardTop.eventually_ge_atTop 800,
      eventually_ge_atTop 4] with N hk hN
    have hNr : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
    have hroot : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
    have hroot1 : 1 ≤ Real.sqrt N := by
      have hN1R : (1:ℝ) ≤ N := by exact_mod_cast (show 1≤N by omega)
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N),
        Real.sqrt_nonneg (N:ℝ)]
    have hk' : (800:ℝ) ≤ k N := by
      have hmul := (le_div_iff₀ hroot).mp hk
      nlinarith only [hmul, hroot1]
    have hQ : ∀ q ∈ GaloisForLFunctions.HTGeometry.primesInIoc N (2*N),
        q.Prime ∧ N < q := by
      intro q hq
      obtain ⟨hp,hl,_⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hq
      exact ⟨hp,hl⟩
    have hdis : Disjoint
        (GaloisForLFunctions.HTGeometry.primesInIoc N (2*N))
        (GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) := by
      apply Finset.disjoint_left.mpr
      intro p hpQ hpP
      have hqu := (GaloisForLFunctions.HTGeometry.mem_primesInIoc hpQ).2.2
      have hpl := (GaloisForLFunctions.HTGeometry.mem_primesInIoc hpP).2.1
      omega
    have hlower := shell_dilationMean_high_core_barrier
      (GaloisForLFunctions.HTGeometry.primesInIoc N (2*N)) N hN hQ hdis hk'
    have hN0 : (N:ℝ) ≠ 0 := hNr.ne'
    have heq : (k N/Real.sqrt N)^2/40960000 =
        (k N)^2/(40960000*(N:ℝ)) := by
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)]
      field_simp [hN0]
    rw [heq]
    exact hlower
  exact tendsto_atTop_mono' _ hbound hscaled

end RHTower
