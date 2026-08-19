import GaloisForLFunctions.HTGeometry.HilbertSchmidtTruncation
import GaloisForLFunctions.HTGeometry.FredholmDeterminantExamples

/-!
# Finite-rank approximation with a prescribed trace

The Hilbert--Carleman determinant `det₂` forgets exactly one coordinate of a Hilbert--Schmidt
kernel: its trace.  The determinant-completion law says that coordinate is completely free in the
limit, and this module proves the `p = 2` half of that freedom directly: every Hilbert--Schmidt
kernel is approximated, in Hilbert--Schmidt norm and to any accuracy, by finitely supported
kernels of **any** prescribed diagonal trace.

The mechanism is the degree-one vanishing micro-spectrum: spread the required trace over `M` equal
diagonal entries placed beyond the truncation block.  The trace is `M · t = ` the target while the
Hilbert--Schmidt energy is `M‖t‖² = |target|²/M`, which vanishes as `M` grows.  This is the `k = 1`,
`p = 2` case of the general cost law `(kN)^{1−p/k}|c|^{p/k}`, with no fractional exponent in sight.
-/

open Filter

namespace HilbertSchmidt

noncomputable section

/-- `M` equal diagonal entries `t`, placed at the indices `N, …, N + M − 1`. -/
def diagBlock (N M : ℕ) (t : ℂ) : ℕ × ℕ → ℂ :=
  fun p => if p.1 = p.2 ∧ N ≤ p.1 ∧ p.1 < N + M then t else 0

theorem diagBlock_eq_zero_of_notMem {N M : ℕ} (t : ℂ) {p : ℕ × ℕ}
    (hp : p ∉ (Finset.range (N + M)) ×ˢ (Finset.range (N + M))) : diagBlock N M t p = 0 := by
  rw [diagBlock]
  by_cases h : p.1 = p.2 ∧ N ≤ p.1 ∧ p.1 < N + M
  · exfalso
    refine hp (Finset.mem_product.mpr ⟨Finset.mem_range.mpr h.2.2, ?_⟩)
    rw [← h.1]
    exact Finset.mem_range.mpr h.2.2
  · rw [if_neg h]

theorem sum_diagBlock_normSq (N M : ℕ) (t : ℂ) :
    ∑ p ∈ (Finset.range (N + M)) ×ˢ (Finset.range (N + M)), ‖diagBlock N M t p‖ ^ 2
      = (M : ℝ) * ‖t‖ ^ 2 := by
  classical
  rw [Finset.sum_product]
  have hinner : ∀ i ∈ Finset.range (N + M),
      (∑ j ∈ Finset.range (N + M), ‖diagBlock N M t (i, j)‖ ^ 2)
        = if N ≤ i ∧ i < N + M then ‖t‖ ^ 2 else 0 := by
    intro i hi
    by_cases hrange : N ≤ i ∧ i < N + M
    · rw [if_pos hrange, Finset.sum_eq_single i]
      · rw [diagBlock, if_pos ⟨rfl, hrange⟩]
      · intro j _ hj
        rw [diagBlock, if_neg (by simp [Ne.symm hj]), norm_zero]
        simp
      · intro hcon
        exact absurd hi hcon
    · rw [if_neg hrange, Finset.sum_eq_zero]
      intro j _
      rw [diagBlock, if_neg (by tauto), norm_zero]
      simp
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  have hcard : (Finset.range (N + M)).filter (fun i => N ≤ i ∧ i < N + M) = Finset.Ico N (N + M) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2⟩
  rw [hcard, Nat.card_Ico]
  simp

theorem isHS_diagBlock (N M : ℕ) (t : ℂ) : IsHS (diagBlock N M t) := by
  classical
  refine summable_of_ne_finset_zero
    (s := (Finset.range (N + M)) ×ˢ (Finset.range (N + M))) fun p hp => ?_
  rw [diagBlock_eq_zero_of_notMem t hp, norm_zero]
  simp

theorem hsNormSq_diagBlock (N M : ℕ) (t : ℂ) :
    hsNormSq (diagBlock N M t) = (M : ℝ) * ‖t‖ ^ 2 := by
  classical
  rw [hsNormSq, tsum_eq_sum (s := (Finset.range (N + M)) ×ˢ (Finset.range (N + M)))
    (fun p hp => by rw [diagBlock_eq_zero_of_notMem t hp, norm_zero]; simp),
    sum_diagBlock_normSq]

theorem hsTraceDiag_diagBlock (N M : ℕ) (t : ℂ) :
    hsTraceDiag (diagBlock N M t) = (M : ℂ) * t := by
  classical
  rw [hsTraceDiag, tsum_eq_sum (s := Finset.range (N + M))
    (fun i hi => by
      rw [diagBlock, if_neg]
      rintro ⟨-, -, hlt⟩
      exact hi (Finset.mem_range.mpr hlt))]
  have hterm : ∀ i ∈ Finset.range (N + M),
      diagBlock N M t (i, i) = if N ≤ i ∧ i < N + M then t else 0 := by
    intro i _
    rw [diagBlock]
    by_cases h : N ≤ i ∧ i < N + M
    · rw [if_pos ⟨rfl, h⟩, if_pos h]
    · rw [if_neg (by tauto), if_neg h]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  have hcard : (Finset.range (N + M)).filter (fun i => N ≤ i ∧ i < N + M) = Finset.Ico N (N + M) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2⟩
  rw [hcard, Nat.card_Ico]
  simp

theorem summable_diag_of_support {K : ℕ × ℕ → ℂ} {s : Finset ℕ}
    (h : ∀ i, i ∉ s → K (i, i) = 0) : Summable fun i => K (i, i) :=
  summable_of_ne_finset_zero (s := s) h

/-- **Finite-rank approximation with a prescribed trace.**  Every Hilbert--Schmidt kernel is
approximated in Hilbert--Schmidt norm, to any accuracy, by finitely supported kernels of any
prescribed diagonal trace.  The trace -- the one coordinate the Hilbert--Carleman determinant
forgets -- is therefore completely free in the limit. -/
theorem exists_finiteSupport_hsNorm_sub_lt_and_hsTraceDiag_eq
    {K : ℕ × ℕ → ℂ} (hK : IsHS K) (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (K' : ℕ × ℕ → ℂ),
      (∀ p : ℕ × ℕ, p ∉ (Finset.range n) ×ˢ (Finset.range n) → K' p = 0) ∧
        IsHS K' ∧ hsNorm (K' - K) < ε ∧ hsTraceDiag K' = c := by
  classical
  have hhalf : (0 : ℝ) < ε / 2 := by linarith
  have hlim : Filter.Tendsto (fun N : ℕ => hsNorm (K - truncKernel K (Finset.range N)))
      Filter.atTop (nhds 0) :=
    (tendsto_hsNorm_sub_truncKernel hK).comp tendsto_finset_range
  obtain ⟨N, hN⟩ := (hlim.eventually (eventually_lt_nhds hhalf)).exists
  obtain ⟨T, hTdef⟩ : ∃ T, T = truncKernel K (Finset.range N) := ⟨_, rfl⟩
  have hTsupp : ∀ p : ℕ × ℕ, p ∉ (Finset.range N) ×ˢ (Finset.range N) → T p = 0 := by
    intro p hp
    rw [hTdef, truncKernel]
    by_cases h : p.1 ∈ Finset.range N ∧ p.2 ∈ Finset.range N
    · exact absurd (Finset.mem_product.mpr h) hp
    · rw [if_neg h]
  have hTHS : IsHS T := by rw [hTdef]; exact isHS_truncKernel hK _
  obtain ⟨R, hRdef⟩ : ∃ R : ℂ, R = c - hsTraceDiag T := ⟨_, rfl⟩
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt (‖R‖ ^ 2 / (ε / 2) ^ 2)
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = M₀ + 1 := ⟨_, rfl⟩
  have hMpos : 0 < M := by omega
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
  have hMbig : ‖R‖ ^ 2 / (ε / 2) ^ 2 < (M : ℝ) := by
    have : (M₀ : ℝ) ≤ (M : ℝ) := by
      have : M₀ ≤ M := by omega
      exact_mod_cast this
    linarith
  obtain ⟨t, htdef⟩ : ∃ t : ℂ, t = R / (M : ℂ) := ⟨_, rfl⟩
  have hMC : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hMpos.ne'
  have hnormt : ‖t‖ = ‖R‖ / (M : ℝ) := by
    rw [htdef, norm_div]
    simp
  refine ⟨N + M, T + diagBlock N M t, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hpN : p ∉ (Finset.range N) ×ˢ (Finset.range N) := by
      intro hcon
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hcon
      exact hp (Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp h1) (by omega)),
          Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp h2) (by omega))⟩)
    show T p + diagBlock N M t p = 0
    rw [hTsupp p hpN, diagBlock_eq_zero_of_notMem t hp, add_zero]
  · exact isHS_add hTHS (isHS_diagBlock N M t)
  · have hsplit : (T + diagBlock N M t) - K = (T - K) + diagBlock N M t := by ring
    rw [hsplit]
    have hTK : hsNorm (T - K) < ε / 2 := by
      have hneg : T - K = -(K - T) := by ring
      rw [hneg, hsNorm_neg, hTdef]
      exact hN
    have hB : hsNorm (diagBlock N M t) < ε / 2 := by
      rw [hsNorm, hsNormSq_diagBlock, hnormt]
      have hval : (M : ℝ) * (‖R‖ / (M : ℝ)) ^ 2 = ‖R‖ ^ 2 / (M : ℝ) := by
        field_simp
      rw [hval]
      refine (Real.sqrt_lt' hhalf).mpr ?_
      rw [div_lt_iff₀ hMR]
      have hpos : (0 : ℝ) < (ε / 2) ^ 2 := by positivity
      rw [div_lt_iff₀ hpos] at hMbig
      nlinarith [hMbig]
    have := hsNorm_add_le (isHS_sub hTHS hK) (isHS_diagBlock N M t)
    linarith
  · have hsum1 : Summable fun i : ℕ => T (i, i) :=
      summable_diag_of_support (s := Finset.range N) fun i hi =>
        hTsupp (i, i) (fun hcon => hi (Finset.mem_product.mp hcon).1)
    have hsum2 : Summable fun i : ℕ => diagBlock N M t (i, i) :=
      summable_diag_of_support (s := Finset.range (N + M)) fun i hi =>
        diagBlock_eq_zero_of_notMem t (fun hcon => hi (Finset.mem_product.mp hcon).1)
    have hadd : hsTraceDiag (T + diagBlock N M t)
        = hsTraceDiag T + hsTraceDiag (diagBlock N M t) := by
      rw [hsTraceDiag, hsTraceDiag, hsTraceDiag, ← Summable.tsum_add hsum1 hsum2]
      rfl
    rw [hadd, hsTraceDiag_diagBlock, htdef]
    field_simp
    rw [hRdef]
    ring


end

end HilbertSchmidt
