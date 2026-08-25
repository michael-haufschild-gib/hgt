import GaloisForLFunctions.HTGeometry.FiniteRankTracePrescription

/-!
# Prescribed-trace finite-rank approximation on infinite index types

The trace-spreading correction does not depend on a preferred enumeration.  On any infinite index
type, place equal diagonal entries on a finite set of prescribed cardinality.  This extends the
natural-number construction to source-defined Hilbert bases whose index is merely countable and
infinite.
-/

open Filter

namespace HilbertSchmidt

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- Equal diagonal entries on a finite source-defined block. -/
def diagFinsetBlock (s : Finset ι) (t : ℂ) : ι × ι → ℂ :=
  fun p => if p.1 = p.2 ∧ p.1 ∈ s then t else 0

theorem diagFinsetBlock_eq_zero_of_notMem (s : Finset ι) (t : ℂ) {p : ι × ι}
    (hp : p ∉ s ×ˢ s) : diagFinsetBlock s t p = 0 := by
  rw [diagFinsetBlock]
  apply if_neg
  rintro ⟨hdiag, hmem⟩
  exact hp (Finset.mem_product.mpr ⟨hmem, hdiag ▸ hmem⟩)

theorem sum_diagFinsetBlock_normSq (s : Finset ι) (t : ℂ) :
    ∑ p ∈ s ×ˢ s, ‖diagFinsetBlock s t p‖ ^ 2 = (s.card : ℝ) * ‖t‖ ^ 2 := by
  classical
  rw [Finset.sum_product]
  have hinner : ∀ i ∈ s,
      (∑ j ∈ s, ‖diagFinsetBlock s t (i, j)‖ ^ 2) = ‖t‖ ^ 2 := by
    intro i hi
    rw [Finset.sum_eq_single i]
    · simp [diagFinsetBlock, hi]
    · intro j hj hji
      simp [diagFinsetBlock, Ne.symm hji]
    · exact fun h => absurd hi h
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]

theorem isHS_diagFinsetBlock (s : Finset ι) (t : ℂ) : IsHS (diagFinsetBlock s t) := by
  classical
  refine summable_of_ne_finset_zero (s := s ×ˢ s) fun p hp => ?_
  rw [diagFinsetBlock_eq_zero_of_notMem s t hp, norm_zero]
  simp

theorem hsNormSq_diagFinsetBlock (s : Finset ι) (t : ℂ) :
    hsNormSq (diagFinsetBlock s t) = (s.card : ℝ) * ‖t‖ ^ 2 := by
  classical
  rw [hsNormSq, tsum_eq_sum (s := s ×ˢ s)
    (fun p hp => by rw [diagFinsetBlock_eq_zero_of_notMem s t hp, norm_zero]; simp),
    sum_diagFinsetBlock_normSq]

theorem hsTraceDiag_diagFinsetBlock (s : Finset ι) (t : ℂ) :
    hsTraceDiag (diagFinsetBlock s t) = (s.card : ℂ) * t := by
  classical
  rw [hsTraceDiag, tsum_eq_sum (s := s) (fun i hi => by
    rw [diagFinsetBlock, if_neg]
    exact fun h => hi h.2)]
  have hterm : ∀ i ∈ s, diagFinsetBlock s t (i, i) = t := by
    intro i hi
    simp [diagFinsetBlock, hi]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]

omit [DecidableEq ι] in
theorem summable_diag_of_finset_support {K : ι × ι → ℂ} {s : Finset ι}
    (h : ∀ i, i ∉ s → K (i, i) = 0) : Summable fun i => K (i, i) :=
  summable_of_ne_finset_zero (s := s) h

/-- Every Hilbert--Schmidt kernel on an infinite index type admits arbitrarily close finite-support
approximants with any prescribed diagonal trace. -/
theorem exists_finiteSupport_hsNorm_sub_lt_and_hsTraceDiag_eq_of_infinite
    [Infinite ι] {K : ι × ι → ℂ} (hK : IsHS K) (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset ι) (K' : ι × ι → ℂ),
      (∀ p : ι × ι, p ∉ s ×ˢ s → K' p = 0) ∧
        IsHS K' ∧ hsNorm (K' - K) < ε ∧ hsTraceDiag K' = c := by
  classical
  have hhalf : (0 : ℝ) < ε / 2 := by linarith
  have hlim := tendsto_hsNorm_sub_truncKernel hK
  obtain ⟨s, hs⟩ := (hlim.eventually (eventually_lt_nhds hhalf)).exists
  let T : ι × ι → ℂ := truncKernel K s
  have hTsupp : ∀ p : ι × ι, p ∉ s ×ˢ s → T p = 0 := by
    intro p hp
    simp only [T, truncKernel]
    by_cases h : p.1 ∈ s ∧ p.2 ∈ s
    · exact absurd (Finset.mem_product.mpr h) hp
    · rw [if_neg h]
  have hTHS : IsHS T := isHS_truncKernel hK s
  let R : ℂ := c - hsTraceDiag T
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt (‖R‖ ^ 2 / (ε / 2) ^ 2)
  let M : ℕ := M₀ + 1
  have hMpos : 0 < M := by simp [M]
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
  have hMbig : ‖R‖ ^ 2 / (ε / 2) ^ 2 < (M : ℝ) := by
    have hle : (M₀ : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast (show M₀ ≤ M by simp [M])
    linarith
  obtain ⟨u, hu⟩ := Infinite.exists_subset_card_eq ι M
  let t : ℂ := R / (M : ℂ)
  have hMC : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hMpos.ne'
  have hnormt : ‖t‖ = ‖R‖ / (M : ℝ) := by
    simp only [t, norm_div]
    simp
  refine ⟨s ∪ u, T + diagFinsetBlock u t, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hps : p ∉ s ×ˢ s := by
      intro hcon
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hcon
      exact hp (Finset.mem_product.mpr
        ⟨Finset.mem_union_left u h1, Finset.mem_union_left u h2⟩)
    have hpu : p ∉ u ×ˢ u := by
      intro hcon
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hcon
      exact hp (Finset.mem_product.mpr
        ⟨Finset.mem_union_right s h1, Finset.mem_union_right s h2⟩)
    change T p + diagFinsetBlock u t p = 0
    rw [hTsupp p hps, diagFinsetBlock_eq_zero_of_notMem u t hpu, add_zero]
  · exact isHS_add hTHS (isHS_diagFinsetBlock u t)
  · have hsplit : (T + diagFinsetBlock u t) - K = (T - K) + diagFinsetBlock u t := by ring
    rw [hsplit]
    have hTK : hsNorm (T - K) < ε / 2 := by
      have hneg : T - K = -(K - T) := by ring
      rw [hneg, hsNorm_neg]
      change hsNorm (K - truncKernel K s) < ε / 2
      exact hs
    have hB : hsNorm (diagFinsetBlock u t) < ε / 2 := by
      rw [hsNorm, hsNormSq_diagFinsetBlock, hu, hnormt]
      have hval : (M : ℝ) * (‖R‖ / (M : ℝ)) ^ 2 = ‖R‖ ^ 2 / (M : ℝ) := by
        field_simp
      rw [hval]
      refine (Real.sqrt_lt' hhalf).mpr ?_
      rw [div_lt_iff₀ hMR]
      have hpos : (0 : ℝ) < (ε / 2) ^ 2 := by positivity
      rw [div_lt_iff₀ hpos] at hMbig
      nlinarith [hMbig]
    have hadd := hsNorm_add_le (isHS_sub hTHS hK) (isHS_diagFinsetBlock u t)
    linarith
  · have hsum1 : Summable fun i : ι => T (i, i) :=
      summable_diag_of_finset_support (s := s) fun i hi =>
        hTsupp (i, i) (fun hcon => hi (Finset.mem_product.mp hcon).1)
    have hsum2 : Summable fun i : ι => diagFinsetBlock u t (i, i) :=
      summable_diag_of_finset_support (s := u) fun i hi => by
        rw [diagFinsetBlock, if_neg]
        exact fun h => hi h.2
    have hadd : hsTraceDiag (T + diagFinsetBlock u t) =
        hsTraceDiag T + hsTraceDiag (diagFinsetBlock u t) := by
      rw [hsTraceDiag, hsTraceDiag, hsTraceDiag, ← Summable.tsum_add hsum1 hsum2]
      rfl
    rw [hadd, hsTraceDiag_diagFinsetBlock, hu]
    simp only [t]
    field_simp
    simp only [R]
    ring

end

end HilbertSchmidt
