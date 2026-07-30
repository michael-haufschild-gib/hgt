import GaloisForLFunctions.HTGeometry.PrimeWalshEntropy

/-!
# Shift-invariant Prime-Walsh entropy

This file closes the shift-invariant clause of the Prime-Walsh Stone law.  A prefix pattern of
length `m + n` splits injectively into a length-`m` pattern and a length-`n` pattern.  The second
piece is again recurring because the full compact prime-tail constraint is shift invariant.  The
resulting prefix-complexity submultiplicativity makes the logarithmic complexity subadditive, so
Fekete's lemma gives the entropy limit and the identical differential-rank limit.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set Topology

noncomputable section

/-- Restriction of a countable Boolean orientation to its first `n` coordinates. -/
def primePrefixRestriction (n : ℕ) (x : ℕ → Bool) : Fin n → Bool :=
  fun i => x i.1

theorem continuous_primePrefixRestriction (n : ℕ) :
    Continuous (primePrefixRestriction n) := by
  apply continuous_pi
  intro i
  exact (continuous_apply (i : ℕ) : Continuous (fun x : ℕ → Bool => x i))

/-- The full-cube cylinder determined by one prefix pattern. -/
def primePrefixCylinder (n : ℕ) (b : Fin n → Bool) : Set (ℕ → Bool) :=
  primePrefixRestriction n ⁻¹' {b}

theorem isClopen_primePrefixCylinder (n : ℕ) (b : Fin n → Bool) :
    IsClopen (primePrefixCylinder n b) := by
  constructor
  · exact (isClosed_discrete ({b} : Set (Fin n → Bool))).preimage
      (continuous_primePrefixRestriction n)
  · exact (isOpen_discrete ({b} : Set (Fin n → Bool))).preimage
      (continuous_primePrefixRestriction n)

/-- Prefix projection commutes exactly with passage to the compact tail-cluster constraint. -/
theorem image_tailCluster_primePrefixRestriction
    (θ : ℕ → (ℕ → Bool)) (n : ℕ) :
    primePrefixRestriction n '' primeOrientationTailClusterSet θ =
      primeOrientationTailClusterSet (fun k => primePrefixRestriction n (θ k)) := by
  classical
  apply Set.ext
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (continuous_primePrefixRestriction n).continuousAt.mapClusterPt hx
  · intro hy
    have hfreqPrefix : ∃ᶠ k in atTop, primePrefixRestriction n (θ k) ∈ ({y} : Set _) :=
      hy.frequently ((isOpen_discrete ({y} : Set (Fin n → Bool))).mem_nhds (by simp))
    have hfreq : ∃ᶠ k in atTop, θ k ∈ primePrefixCylinder n y := by
      simpa only [primePrefixCylinder, Set.mem_preimage, Set.mem_singleton_iff] using hfreqPrefix
    obtain ⟨x, hxC, hxcluster⟩ :=
      (isClopen_primePrefixCylinder n y).1.isCompact.exists_mapClusterPt_of_frequently hfreq
    exact ⟨x, hxcluster, hxC⟩

/-- The recurring length-`n` chamber is exactly the prefix image of the complete prime-tail
constraint. -/
theorem primeRecurringPrefixChamber_eq_image
    (e : ℕ ≃ Nat.Primes) (ε : ℕ → Nat.Primes → Bool) (n : ℕ) :
    primeRecurringPatternChamber e (primePrefixOrientation ε n) =
      primePrefixRestriction n ''
        primeOrientationTailClusterSet (fun k j => ε j (e k)) := by
  symm
  simpa only [primeRecurringPatternChamber, primePrefixOrientation, primePrefixRestriction] using!
    image_tailCluster_primePrefixRestriction (fun k j => ε j (e k)) n

/-- The countable prime-tail constraint is invariant under every left shift of its orientation
coordinates. -/
def PrimeTailShiftInvariant
    (e : ℕ ≃ Nat.Primes) (ε : ℕ → Nat.Primes → Bool) : Prop :=
  ∀ x ∈ primeOrientationTailClusterSet (fun k j => ε j (e k)), ∀ m,
    (fun j => x (m + j)) ∈ primeOrientationTailClusterSet (fun k j => ε j (e k))

/-- First block of a pattern on `Fin (m + n)`. -/
def primePrefixLeftPattern {m n : ℕ} (r : Fin (m + n) → Bool) : Fin m → Bool :=
  fun i => r (Fin.castAdd n i)

/-- Second block of a pattern on `Fin (m + n)`. -/
def primePrefixRightPattern {m n : ℕ} (r : Fin (m + n) → Bool) : Fin n → Bool :=
  fun i => r (Fin.natAdd m i)

theorem primePrefixLeftPattern_mem
    (e : ℕ ≃ Nat.Primes) (ε : ℕ → Nat.Primes → Bool) (m n : ℕ)
    (r : primeRecurringPatternChamber e (primePrefixOrientation ε (m + n))) :
    primePrefixLeftPattern r.1 ∈
      primeRecurringPatternChamber e (primePrefixOrientation ε m) := by
  have hr : r.1 ∈ primePrefixRestriction (m + n) ''
      primeOrientationTailClusterSet (fun k j => ε j (e k)) :=
    (Set.ext_iff.mp (primeRecurringPrefixChamber_eq_image e ε (m + n)) r.1).mp r.2
  obtain ⟨x, hx, hxr⟩ := hr
  rw [primeRecurringPrefixChamber_eq_image]
  refine ⟨x, hx, ?_⟩
  funext i
  have hi := congrFun hxr (Fin.castAdd n i)
  simpa only [primePrefixRestriction, primePrefixLeftPattern, Fin.val_castAdd] using hi

theorem primePrefixRightPattern_mem_of_shiftInvariant
    (e : ℕ ≃ Nat.Primes) (ε : ℕ → Nat.Primes → Bool)
    (hshift : PrimeTailShiftInvariant e ε) (m n : ℕ)
    (r : primeRecurringPatternChamber e (primePrefixOrientation ε (m + n))) :
    primePrefixRightPattern r.1 ∈
      primeRecurringPatternChamber e (primePrefixOrientation ε n) := by
  have hr : r.1 ∈ primePrefixRestriction (m + n) ''
      primeOrientationTailClusterSet (fun k j => ε j (e k)) :=
    (Set.ext_iff.mp (primeRecurringPrefixChamber_eq_image e ε (m + n)) r.1).mp r.2
  obtain ⟨x, hx, hxr⟩ := hr
  rw [primeRecurringPrefixChamber_eq_image]
  refine ⟨fun j => x (m + j), hshift x hx m, ?_⟩
  funext i
  have hi := congrFun hxr (Fin.natAdd m i)
  simpa only [primePrefixRestriction, primePrefixRightPattern, Fin.val_natAdd] using hi

/-- Split a recurring `(m+n)`-prefix into its recurring left and right blocks. -/
def primePrefixPatternSplit
    (e : ℕ ≃ Nat.Primes) (ε : ℕ → Nat.Primes → Bool)
    (hshift : PrimeTailShiftInvariant e ε) (m n : ℕ) :
    primeRecurringPatternChamber e (primePrefixOrientation ε (m + n)) →
      primeRecurringPatternChamber e (primePrefixOrientation ε m) ×
        primeRecurringPatternChamber e (primePrefixOrientation ε n) :=
  fun r =>
    (⟨primePrefixLeftPattern r.1, primePrefixLeftPattern_mem e ε m n r⟩,
      ⟨primePrefixRightPattern r.1,
        primePrefixRightPattern_mem_of_shiftInvariant e ε hshift m n r⟩)

theorem primePrefixPatternSplit_injective
    (e : ℕ ≃ Nat.Primes) (ε : ℕ → Nat.Primes → Bool)
    (hshift : PrimeTailShiftInvariant e ε) (m n : ℕ) :
    Function.Injective (primePrefixPatternSplit e ε hshift m n) := by
  intro r s hrs
  apply Subtype.ext
  funext i
  rcases hsym : finSumFinEquiv.symm i with j | k
  · have hi : i = Fin.castAdd n j := by
      calc
        i = finSumFinEquiv (finSumFinEquiv.symm i) := (finSumFinEquiv.apply_symm_apply i).symm
        _ = finSumFinEquiv (Sum.inl j) := congrArg finSumFinEquiv hsym
        _ = Fin.castAdd n j := finSumFinEquiv_apply_left j
    subst i
    have hleft := congrArg (fun z => z.1.1 j) hrs
    simpa only [primePrefixPatternSplit, primePrefixLeftPattern] using hleft
  · have hi : i = Fin.natAdd m k := by
      calc
        i = finSumFinEquiv (finSumFinEquiv.symm i) := (finSumFinEquiv.apply_symm_apply i).symm
        _ = finSumFinEquiv (Sum.inr k) := congrArg finSumFinEquiv hsym
        _ = Fin.natAdd m k := finSumFinEquiv_apply_right k
    subst i
    have hright := congrArg (fun z => z.2.1 k) hrs
    simpa only [primePrefixPatternSplit, primePrefixRightPattern] using hright

/-- Shift invariance makes recurring prefix complexity submultiplicative. -/
theorem primePrefixPatternComplexity_add_le_mul_of_shiftInvariant
    (e : ℕ ≃ Nat.Primes) (ε : ℕ → Nat.Primes → Bool)
    (hshift : PrimeTailShiftInvariant e ε) (m n : ℕ) :
    primePrefixPatternComplexity e ε (m + n) ≤
      primePrefixPatternComplexity e ε m * primePrefixPatternComplexity e ε n := by
  simpa only [primePrefixPatternComplexity, Nat.card_prod] using
    Nat.card_le_card_of_injective (primePrefixPatternSplit e ε hshift m n)
      (primePrefixPatternSplit_injective e ε hshift m n)

/-- Shift invariance makes the real logarithm of prefix complexity subadditive. -/
theorem primePrefixLogComplexity_subadditive_of_shiftInvariant
    (e : ℕ ≃ Nat.Primes) (ε : ℕ → Nat.Primes → Bool)
    (hshift : PrimeTailShiftInvariant e ε) :
    Subadditive (fun n => Real.log (primePrefixPatternComplexity e ε n : ℝ)) := by
  intro m n
  have hm := primePrefixPatternComplexity_pos e ε m
  have hn := primePrefixPatternComplexity_pos e ε n
  have hmn := primePrefixPatternComplexity_pos e ε (m + n)
  have hmul := primePrefixPatternComplexity_add_le_mul_of_shiftInvariant e ε hshift m n
  have hmnR : 0 < (primePrefixPatternComplexity e ε (m + n) : ℝ) := by exact_mod_cast hmn
  calc
    Real.log (primePrefixPatternComplexity e ε (m + n) : ℝ) ≤
        Real.log
          ((primePrefixPatternComplexity e ε m * primePrefixPatternComplexity e ε n : ℕ) : ℝ) :=
      Real.log_le_log hmnR (by exact_mod_cast hmul)
    _ = Real.log (primePrefixPatternComplexity e ε m : ℝ) +
        Real.log (primePrefixPatternComplexity e ε n : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul]
      · exact_mod_cast hm.ne'
      · exact_mod_cast hn.ne'

/-- **Shift-invariant HT--Stone entropy law.**  Prefix complexity and exact Prime-Walsh
differential rank converge to one and the same entropy rate. -/
theorem primeWalshRankEntropy_tendsto_of_shiftInvariant
    (e : ℕ ≃ Nat.Primes) (ε : ℕ → Nat.Primes → Bool)
    (A : Type*) [Finite A] [Nonempty A]
    (hshift : PrimeTailShiftInvariant e ε) :
    ∃ h : ℝ,
      Tendsto
          (fun n => realNormalizedLogCard (primePrefixPatternComplexity e ε n) n)
          atTop (𝓝 h) ∧
      Tendsto
          (fun n => realNormalizedLogCard
            (primeWalshPrefixDifferentialRank e ε A n) n)
          atTop (𝓝 h) :=
  primeWalshRankEntropy_tendsto_of_subadditive e ε A
    (primePrefixLogComplexity_subadditive_of_shiftInvariant e ε hshift)

end

end GaloisForLFunctions.HTGeometry
