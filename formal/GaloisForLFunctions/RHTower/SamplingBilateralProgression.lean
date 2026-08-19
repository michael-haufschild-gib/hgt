import GaloisForLFunctions.RHTower.SamplingProgressionCriterion

/-!
# Aperiodicity from bounded two-sided progression blocks

`SamplingProgressionCriterion` reduces the collapse to the absence of an infinite *one-sided*
arithmetic progression inside the sample set.  For a **symmetric** sample set the reduction can be
sharpened: a finite shift failure at step `h` bounds the backward failure as well, because the
backward failure is the reflection of the forward one.  Hence above a single threshold the sample
set is closed under both `+h` and `-h`, and a sample chosen high enough carries a two-sided block

`{ b + n h : |n| ≤ M }`

of any prescribed length `M`.  The criterion therefore becomes a **length bound**: it suffices that
for each step there is a length no two-sided block of which lies in the sample set.  That is the
shape in which the corresponding zero-free statement for `Xi` is available in the literature.
-/

open Set

namespace RHTower

/-- A finite shift failure at step `h` on a symmetric set bounds the backward failure too: above a
single threshold the set is closed under both shifts. -/
theorem exists_bilateral_threshold_of_finite_shiftFailure {S : Set ℝ} {h : ℝ}
    (hsym : ∀ x, x ∈ S → -x ∈ S) (hfin : (shiftFailure S h).Finite) :
    ∃ T : ℝ, ∀ x ∈ S, T < x → x + h ∈ S ∧ x - h ∈ S := by
  obtain ⟨T₀, hT₀⟩ := hfin.bddAbove
  obtain ⟨m, hm⟩ := hfin.bddBelow
  refine ⟨max T₀ (-m), fun x hxS hx => ⟨?_, ?_⟩⟩
  · by_contra hcon
    have hmem : x ∈ shiftFailure S h := ⟨hxS, hcon⟩
    exact absurd (hT₀ hmem) (not_le.mpr (lt_of_le_of_lt (le_max_left _ _) hx))
  · by_contra hcon
    have hmem : x ∈ Neg.neg '' shiftFailure S h :=
      backwardFailure_subset_neg_shiftFailure hsym h ⟨hxS, hcon⟩
    obtain ⟨y, hy, hyx⟩ := hmem
    have hylow : m ≤ y := hm hy
    have : x = -y := hyx.symm
    have hxle : x ≤ -m := by
      rw [this]
      linarith
    exact absurd hxle (not_le.mpr (lt_of_le_of_lt (le_max_right _ _) hx))

/-- **Arbitrarily long two-sided blocks.**  If the shift failure at a positive step is finite, the
symmetric sample set carries a two-sided arithmetic-progression block of every prescribed length. -/
theorem exists_bilateral_block_of_finite_shiftFailure {S : Set ℝ} {h : ℝ} (hh : 0 < h)
    (hsym : ∀ x, x ∈ S → -x ∈ S) (hfin : (shiftFailure S h).Finite)
    (hunb : ∀ T : ℝ, ∃ γ, γ ∈ S ∧ T < γ) (M : ℕ) :
    ∃ b : ℝ, ∀ n : ℤ, n.natAbs ≤ M → b + (n : ℝ) * h ∈ S := by
  obtain ⟨T, hT⟩ := exists_bilateral_threshold_of_finite_shiftFailure hsym hfin
  obtain ⟨γ, hγS, hγ⟩ := hunb (T + (M : ℝ) * h)
  refine ⟨γ, ?_⟩
  have hdown : ∀ k : ℕ, k ≤ M → γ - (k : ℝ) * h ∈ S ∧ T < γ - (k : ℝ) * h := by
    intro k
    induction k with
    | zero =>
        intro _
        refine ⟨by simpa using hγS, ?_⟩
        have : (0 : ℝ) ≤ (M : ℝ) * h := by positivity
        simp only [Nat.cast_zero, zero_mul, sub_zero]
        linarith
    | succ k ih =>
        intro hk
        obtain ⟨hmem, hgt⟩ := ih (by omega)
        refine ⟨?_, ?_⟩
        · have := (hT _ hmem hgt).2
          have hcast : γ - (k : ℝ) * h - h = γ - ((k + 1 : ℕ) : ℝ) * h := by
            push_cast
            ring
          rwa [hcast] at this
        · have hkM : ((k : ℝ) + 1) * h ≤ (M : ℝ) * h := by
            have : ((k : ℝ) + 1) ≤ (M : ℝ) := by exact_mod_cast hk
            nlinarith [hh.le]
          have hcast : ((k + 1 : ℕ) : ℝ) * h = ((k : ℝ) + 1) * h := by push_cast; ring
          rw [hcast]
          linarith
  have hup : ∀ k : ℕ, γ + (k : ℝ) * h ∈ S := by
    intro k
    induction k with
    | zero => simpa using hγS
    | succ k ih =>
        have hgt : T < γ + (k : ℝ) * h := by
          have h1 : (0 : ℝ) ≤ (k : ℝ) * h := by positivity
          have h2 : (0 : ℝ) ≤ (M : ℝ) * h := by positivity
          linarith
        have := (hT _ ih hgt).1
        have hcast : γ + (k : ℝ) * h + h = γ + ((k + 1 : ℕ) : ℝ) * h := by
          push_cast
          ring
        rwa [hcast] at this
  intro n hn
  rcases lt_or_ge n 0 with hneg | hpos
  · have hnn : 0 ≤ -n := by omega
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hnn
    have hkM : k ≤ M := by
      have : n.natAbs = k := by omega
      omega
    have hmem := (hdown k hkM).1
    have hcast : γ - (k : ℝ) * h = γ + (n : ℝ) * h := by
      have : (n : ℝ) = -(k : ℝ) := by
        have : (-n : ℤ) = (k : ℤ) := hk
        have hcast2 : ((-n : ℤ) : ℝ) = ((k : ℤ) : ℝ) := by exact_mod_cast this
        push_cast at hcast2
        linarith
      rw [this]
      ring
    rwa [hcast] at hmem
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hpos
    have := hup k
    simpa using this

/-- **Aperiodicity from a length bound.**  A symmetric, unbounded sample set in which, for every
step, some two-sided block of a fixed length fails to be contained, has infinite shift failure at
every nonzero step. -/
theorem infinite_shiftFailure_of_no_long_block {S : Set ℝ}
    (hsym : ∀ x, x ∈ S → -x ∈ S)
    (hunb : ∀ T : ℝ, ∃ γ, γ ∈ S ∧ T < γ)
    (hnoBlock : ∀ k : ℝ, 0 < k → ∃ M : ℕ, ∀ b : ℝ, ∃ n : ℤ, n.natAbs ≤ M ∧ b + (n : ℝ) * k ∉ S)
    {h : ℝ} (hh : h ≠ 0) : (shiftFailure S h).Infinite := by
  have hpos : ∀ k : ℝ, 0 < k → (shiftFailure S k).Infinite := by
    intro k hk
    rw [Set.Infinite]
    intro hfin
    obtain ⟨M, hM⟩ := hnoBlock k hk
    obtain ⟨b, hb⟩ := exists_bilateral_block_of_finite_shiftFailure hk hsym hfin hunb M
    obtain ⟨n, hn, hnot⟩ := hM b
    exact hnot (hb n hn)
  rcases lt_or_gt_of_ne hh with hneg | hposh
  · have hkey := hpos (-h) (by linarith)
    rw [shiftFailure_neg_eq hsym h]
    exact hkey.image (fun x _ y _ hxy => by simpa using neg_injective hxy)
  · exact hpos h hposh

/-- **`(23)` from a length bound on progressions of real `Xi` zeros.** -/
theorem xiSamplingIdealizer_collapse_of_no_long_block {m : ℕ} {F : Finset ℝ}
    {a : ℝ → ℕ → Polynomial ℂ}
    (hnoBlock : ∀ k : ℝ, 0 < k → ∃ M : ℕ, ∀ b : ℝ,
      ∃ n : ℤ, n.natAbs ≤ M ∧ b + (n : ℝ) * k ∉ xiRealDivisor)
    (h0 : (0 : ℝ) ∈ F) (hpres : PreservesSamplingIdeal m xiRealDivisor F a) :
    ∀ h ∈ F, ∀ j ≤ m, (h ≠ 0 ∨ j ≠ 0) → a h j = 0 := by
  have hinf : xiRealDivisor.Infinite := by
    refine Set.infinite_of_not_bddAbove ?_
    rintro ⟨T, hT⟩
    obtain ⟨γ, hγS, hγ⟩ := unbounded_xiRealDivisor T
    exact absurd (hT hγS) (not_le.mpr hγ)
  intro h hhF j hj hcase
  rcases eq_or_ne h 0 with rfl | hh
  · have hj0 : j ≠ 0 := hcase.resolve_left (by simp)
    exact derivCoeff_eq_zero_of_infinite_samples locallyFiniteSamples_xiRealDivisor hpres h0 hinf
      hj hj0
  · exact shiftCoeff_eq_zero_of_infinite_failure locallyFiniteSamples_xiRealDivisor hpres hhF
      (infinite_shiftFailure_of_no_long_block symmetric_xiRealDivisor unbounded_xiRealDivisor
        hnoBlock hh) hj

end RHTower
