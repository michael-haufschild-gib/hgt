import GaloisForLFunctions.HTGeometry.TripticAtomSum
import GaloisForLFunctions.HTGeometry.TripticJetAtomShift

/-!
# The total atom sum

Summing the per-order atom sums over a bounded range of orders, in both lattice directions, gives a
single meromorphic function that is `1`-periodic everywhere, has vanishing mixed second difference
off a countable set — the union of the finitely many atoms' pole lattices and their `τ`-translates —
and whose Laurent coefficients of negative index are exactly the two transverse fields of the source.

* `rowAtomSum_periodic`, `meromorphicAt_rowAtomSum`, `rowAtomSum_mixed_eq_zero`;
* `rowAtomSumBad`, `countable_rowAtomSumBad`;
* `totalAtomSum` and its three structural properties.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

open scoped Classical

noncomputable section

variable {F : ℂ → ℂ} {τ σ : ℂ}

theorem rowAtomSum_periodic (F : ℂ → ℂ) (τ σ : ℂ) (j : ℕ) (R : Finset ℂ) (z : ℂ) :
    rowAtomSum F τ σ j R (z + 1) = rowAtomSum F τ σ j R z := by
  simp only [rowAtomSum]
  exact Finset.sum_congr rfl fun q _ => by rw [jetAtom_periodic]

theorem meromorphicAt_rowAtomSum (hσ : 0 < σ.im) (F : ℂ → ℂ) (τ : ℂ) (j : ℕ) (R : Finset ℂ)
    (z : ℂ) : MeromorphicAt (rowAtomSum F τ σ j R) z := by
  have hfun : rowAtomSum F τ σ j R
      = ∑ q ∈ R, fun w => (rowCoeff F τ (-((j : ℤ) + 1)) q /
          (((-1 : ℂ) ^ j * (j.factorial : ℂ)) * (lineCount σ R q : ℂ)))
        * jetAtom σ (q - thetaHalfPeriod σ) j w := by
    funext w
    simp only [rowAtomSum, Finset.sum_apply]
  rw [hfun]
  refine MeromorphicAt.sum fun q _ => ?_
  exact (analyticAt_const.meromorphicAt).mul (meromorphicAt_jetAtom hσ _ j z)

/-- The exceptional set of one atom sum: its poles and their `τ`-translates. -/
def rowAtomSumBad (τ σ : ℂ) (R : Finset ℂ) : Set ℂ :=
  (⋃ q ∈ (R : Set ℂ), atomPoleSet σ (q - thetaHalfPeriod σ)) ∪
    (⋃ q ∈ (R : Set ℂ), {z : ℂ | z + τ ∈ atomPoleSet σ (q - thetaHalfPeriod σ)})

theorem countable_rowAtomSumBad (τ σ : ℂ) (R : Finset ℂ) : (rowAtomSumBad τ σ R).Countable := by
  refine Set.Countable.union ?_ ?_
  · exact Set.Countable.biUnion R.countable_toSet fun q _ => countable_atomPoleSet σ _
  · refine Set.Countable.biUnion R.countable_toSet fun q _ => ?_
    have hsub : {z : ℂ | z + τ ∈ atomPoleSet σ (q - thetaHalfPeriod σ)}
        ⊆ (fun u : ℂ => u - τ) '' atomPoleSet σ (q - thetaHalfPeriod σ) := by
      intro z hz
      exact ⟨z + τ, hz, by ring⟩
    exact Set.Countable.mono hsub ((countable_atomPoleSet σ _).image _)

/-- **The atom sum has vanishing mixed second difference off its exceptional set.** -/
theorem rowAtomSum_mixed_eq_zero (hσ : 0 < σ.im) (F : ℂ → ℂ) (τ : ℂ) (j : ℕ) (R : Finset ℂ)
    {z : ℂ} (hz : z ∉ rowAtomSumBad τ σ R) :
    rowAtomSum F τ σ j R (z + τ + σ) - rowAtomSum F τ σ j R (z + τ)
      - (rowAtomSum F τ σ j R (z + σ) - rowAtomSum F τ σ j R z) = 0 := by
  have hz1 : ∀ q ∈ R, z ∉ atomPoleSet σ (q - thetaHalfPeriod σ) := by
    intro q hq hmem
    exact hz (Or.inl (Set.mem_biUnion (by exact_mod_cast hq) hmem))
  have hz2 : ∀ q ∈ R, z + τ ∉ atomPoleSet σ (q - thetaHalfPeriod σ) := by
    intro q hq hmem
    exact hz (Or.inr (Set.mem_biUnion (by exact_mod_cast hq) hmem))
  have hexp : rowAtomSum F τ σ j R (z + τ + σ) - rowAtomSum F τ σ j R (z + τ)
      - (rowAtomSum F τ σ j R (z + σ) - rowAtomSum F τ σ j R z)
      = ∑ q ∈ R, (rowCoeff F τ (-((j : ℤ) + 1)) q /
            (((-1 : ℂ) ^ j * (j.factorial : ℂ)) * (lineCount σ R q : ℂ)))
          * (jetAtom σ (q - thetaHalfPeriod σ) j (z + τ + σ)
              - jetAtom σ (q - thetaHalfPeriod σ) j (z + τ)
              - (jetAtom σ (q - thetaHalfPeriod σ) j (z + σ)
                  - jetAtom σ (q - thetaHalfPeriod σ) j z)) := by
    simp only [rowAtomSum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [hexp]
  refine Finset.sum_eq_zero fun q hq => ?_
  rw [jetAtom_mixed_eq_zero hσ _ τ j (hz1 q hq) (hz2 q hq), mul_zero]

/-- The total atom sum over a bounded range of orders, in both lattice directions. -/
def totalAtomSum (F : ℂ → ℂ) (τ σ : ℂ) (n : ℕ) (Rτ Rσ : ℕ → Finset ℂ) : ℂ → ℂ :=
  fun z => (∑ j ∈ Finset.range n, rowAtomSum F τ σ j (Rτ j) z)
    + ∑ j ∈ Finset.range n, rowAtomSum F σ τ j (Rσ j) z

theorem totalAtomSum_periodic (F : ℂ → ℂ) (τ σ : ℂ) (n : ℕ) (Rτ Rσ : ℕ → Finset ℂ) (z : ℂ) :
    totalAtomSum F τ σ n Rτ Rσ (z + 1) = totalAtomSum F τ σ n Rτ Rσ z := by
  simp only [totalAtomSum]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => rowAtomSum_periodic F τ σ j (Rτ j) z
  · exact Finset.sum_congr rfl fun j _ => rowAtomSum_periodic F σ τ j (Rσ j) z

theorem meromorphicAt_totalAtomSum (hτ : 0 < τ.im) (hσ : 0 < σ.im) (F : ℂ → ℂ) (n : ℕ)
    (Rτ Rσ : ℕ → Finset ℂ) (z : ℂ) : MeromorphicAt (totalAtomSum F τ σ n Rτ Rσ) z := by
  have hfun : totalAtomSum F τ σ n Rτ Rσ
      = (∑ j ∈ Finset.range n, rowAtomSum F τ σ j (Rτ j))
        + ∑ j ∈ Finset.range n, rowAtomSum F σ τ j (Rσ j) := by
    funext w
    simp only [totalAtomSum, Pi.add_apply, Finset.sum_apply]
  rw [hfun]
  exact (MeromorphicAt.sum fun j _ => meromorphicAt_rowAtomSum hσ F τ j (Rτ j) z).add
    (MeromorphicAt.sum fun j _ => meromorphicAt_rowAtomSum hτ F σ j (Rσ j) z)

/-- The exceptional set of the total atom sum. -/
def totalAtomSumBad (τ σ : ℂ) (n : ℕ) (Rτ Rσ : ℕ → Finset ℂ) : Set ℂ :=
  (⋃ j ∈ Finset.range n, rowAtomSumBad τ σ (Rτ j)) ∪
    ⋃ j ∈ Finset.range n, rowAtomSumBad σ τ (Rσ j)

theorem countable_totalAtomSumBad (τ σ : ℂ) (n : ℕ) (Rτ Rσ : ℕ → Finset ℂ) :
    (totalAtomSumBad τ σ n Rτ Rσ).Countable := by
  refine Set.Countable.union ?_ ?_
  · exact Set.Countable.biUnion (Finset.range n).countable_toSet
      fun j _ => countable_rowAtomSumBad τ σ (Rτ j)
  · exact Set.Countable.biUnion (Finset.range n).countable_toSet
      fun j _ => countable_rowAtomSumBad σ τ (Rσ j)

/-- **The total atom sum has vanishing mixed second difference off a countable set.** -/
theorem totalAtomSum_mixed_eq_zero (hτ : 0 < τ.im) (hσ : 0 < σ.im) (F : ℂ → ℂ) (n : ℕ)
    (Rτ Rσ : ℕ → Finset ℂ) {z : ℂ} (hz : z ∉ totalAtomSumBad τ σ n Rτ Rσ) :
    totalAtomSum F τ σ n Rτ Rσ (z + τ + σ) - totalAtomSum F τ σ n Rτ Rσ (z + τ)
      - (totalAtomSum F τ σ n Rτ Rσ (z + σ) - totalAtomSum F τ σ n Rτ Rσ z) = 0 := by
  have hz1 : ∀ j ∈ Finset.range n, z ∉ rowAtomSumBad τ σ (Rτ j) := by
    intro j hj hmem
    exact hz (Or.inl (Set.mem_biUnion (by exact_mod_cast hj) hmem))
  have hz2 : ∀ j ∈ Finset.range n, z ∉ rowAtomSumBad σ τ (Rσ j) := by
    intro j hj hmem
    exact hz (Or.inr (Set.mem_biUnion (by exact_mod_cast hj) hmem))
  have hsum1 : (∑ j ∈ Finset.range n, rowAtomSum F τ σ j (Rτ j) (z + τ + σ))
      - (∑ j ∈ Finset.range n, rowAtomSum F τ σ j (Rτ j) (z + τ))
      - ((∑ j ∈ Finset.range n, rowAtomSum F τ σ j (Rτ j) (z + σ))
        - ∑ j ∈ Finset.range n, rowAtomSum F τ σ j (Rτ j) z) = 0 := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun j hj => rowAtomSum_mixed_eq_zero hσ F τ j (Rτ j) (hz1 j hj)
  have hsum2 : (∑ j ∈ Finset.range n, rowAtomSum F σ τ j (Rσ j) (z + σ + τ))
      - (∑ j ∈ Finset.range n, rowAtomSum F σ τ j (Rσ j) (z + σ))
      - ((∑ j ∈ Finset.range n, rowAtomSum F σ τ j (Rσ j) (z + τ))
        - ∑ j ∈ Finset.range n, rowAtomSum F σ τ j (Rσ j) z) = 0 := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun j hj => rowAtomSum_mixed_eq_zero hτ F σ j (Rσ j) (hz2 j hj)
  have hswap : z + τ + σ = z + σ + τ := by ring
  simp only [totalAtomSum]
  rw [hswap] at hsum1 ⊢
  linear_combination hsum1 + hsum2

/-- Laurent coefficients are additive over a finite sum. -/
theorem laurentCoeff_finsetSum {ι : Type*} (s : Finset ι) (G : ι → ℂ → ℂ) (a : ℂ) (ℓ : ℤ)
    (hG : ∀ i ∈ s, MeromorphicAt (G i) a) :
    laurentCoeff (fun z => ∑ i ∈ s, G i z) a ℓ = ∑ i ∈ s, laurentCoeff (G i) a ℓ := by
  have h := laurentCoeff_sum s G (fun _ => 1) a ℓ hG
  simpa only [one_mul] using h

private theorem laurentCoeff_totalAtomSum_split (hτ : 0 < τ.im) (hσ : 0 < σ.im) (F : ℂ → ℂ)
    (n : ℕ) (Rτ Rσ : ℕ → Finset ℂ) (w : ℂ) (ℓ : ℤ) :
    laurentCoeff (totalAtomSum F τ σ n Rτ Rσ) w ℓ
      = (∑ j ∈ Finset.range n, laurentCoeff (rowAtomSum F τ σ j (Rτ j)) w ℓ)
        + ∑ j ∈ Finset.range n, laurentCoeff (rowAtomSum F σ τ j (Rσ j)) w ℓ := by
  have hfun : totalAtomSum F τ σ n Rτ Rσ
      = fun z => (∑ j ∈ Finset.range n, rowAtomSum F τ σ j (Rτ j) z)
        + ∑ j ∈ Finset.range n, rowAtomSum F σ τ j (Rσ j) z := rfl
  have hm1 : MeromorphicAt (fun z => ∑ j ∈ Finset.range n, rowAtomSum F τ σ j (Rτ j) z) w := by
    have hfun1 : (fun z => ∑ j ∈ Finset.range n, rowAtomSum F τ σ j (Rτ j) z)
        = ∑ j ∈ Finset.range n, rowAtomSum F τ σ j (Rτ j) := by
      funext z
      simp only [Finset.sum_apply]
    rw [hfun1]
    exact MeromorphicAt.sum fun j _ => meromorphicAt_rowAtomSum hσ F τ j (Rτ j) w
  have hm2 : MeromorphicAt (fun z => ∑ j ∈ Finset.range n, rowAtomSum F σ τ j (Rσ j) z) w := by
    have hfun2 : (fun z => ∑ j ∈ Finset.range n, rowAtomSum F σ τ j (Rσ j) z)
        = ∑ j ∈ Finset.range n, rowAtomSum F σ τ j (Rσ j) := by
      funext z
      simp only [Finset.sum_apply]
    rw [hfun2]
    exact MeromorphicAt.sum fun j _ => meromorphicAt_rowAtomSum hτ F σ j (Rσ j) w
  rw [hfun, laurentCoeff_add hm1 hm2,
    laurentCoeff_finsetSum _ _ w ℓ (fun j _ => meromorphicAt_rowAtomSum hσ F τ j (Rτ j) w),
    laurentCoeff_finsetSum _ _ w ℓ (fun j _ => meromorphicAt_rowAtomSum hτ F σ j (Rσ j) w)]

/-- **Below the order range the total atom sum has no coefficient at all.** -/
theorem laurentCoeff_totalAtomSum_of_lt (hτ : 0 < τ.im) (hσ : 0 < σ.im) (F : ℂ → ℂ) (n : ℕ)
    (Rτ Rσ : ℕ → Finset ℂ) (w : ℂ) {ℓ : ℤ} (hℓ : ℓ < 0) (hlt : ℓ < -(n : ℤ)) :
    laurentCoeff (totalAtomSum F τ σ n Rτ Rσ) w ℓ = 0 := by
  rw [laurentCoeff_totalAtomSum_split hτ hσ F n Rτ Rσ w ℓ]
  have h1 : ∀ j ∈ Finset.range n, laurentCoeff (rowAtomSum F τ σ j (Rτ j)) w ℓ = 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact laurentCoeff_rowAtomSum_of_ne_order hσ j (Rτ j) w hℓ (by omega)
  have h2 : ∀ j ∈ Finset.range n, laurentCoeff (rowAtomSum F σ τ j (Rσ j)) w ℓ = 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact laurentCoeff_rowAtomSum_of_ne_order hτ j (Rσ j) w hℓ (by omega)
  rw [Finset.sum_eq_zero h1, Finset.sum_eq_zero h2, add_zero]

/-- **Inside the order range the Laurent coefficients of the total atom sum are the two transverse
fields.** -/
theorem laurentCoeff_totalAtomSum (hτ : 0 < τ.im) (hσ : 0 < σ.im) (F : ℂ → ℂ) (n : ℕ)
    (Rτ Rσ : ℕ → Finset ℂ) (w : ℂ) (j₀ : ℕ) (hj₀ : j₀ < n)
    (hinvτ : ∀ q : ℂ, sameLine σ q w →
      rowCoeff F τ (-((j₀ : ℤ) + 1)) q = rowCoeff F τ (-((j₀ : ℤ) + 1)) w)
    (hcovτ : rowCoeff F τ (-((j₀ : ℤ) + 1)) w ≠ 0 → ∃ q ∈ Rτ j₀, sameLine σ q w)
    (hinvσ : ∀ q : ℂ, sameLine τ q w →
      rowCoeff F σ (-((j₀ : ℤ) + 1)) q = rowCoeff F σ (-((j₀ : ℤ) + 1)) w)
    (hcovσ : rowCoeff F σ (-((j₀ : ℤ) + 1)) w ≠ 0 → ∃ q ∈ Rσ j₀, sameLine τ q w) :
    laurentCoeff (totalAtomSum F τ σ n Rτ Rσ) w (-((j₀ : ℤ) + 1))
      = rowCoeff F τ (-((j₀ : ℤ) + 1)) w + rowCoeff F σ (-((j₀ : ℤ) + 1)) w := by
  have hℓ : (-((j₀ : ℤ) + 1)) < 0 := by omega
  have hmem : j₀ ∈ Finset.range n := Finset.mem_range.mpr hj₀
  rw [laurentCoeff_totalAtomSum_split hτ hσ F n Rτ Rσ w (-((j₀ : ℤ) + 1))]
  have h1 : (∑ j ∈ Finset.range n, laurentCoeff (rowAtomSum F τ σ j (Rτ j)) w
      (-((j₀ : ℤ) + 1))) = rowCoeff F τ (-((j₀ : ℤ) + 1)) w := by
    rw [Finset.sum_eq_single j₀ (fun j _ hjne =>
      laurentCoeff_rowAtomSum_of_ne_order hσ j (Rτ j) w hℓ (by
        intro hcon
        exact hjne (by omega))) (fun hcon => absurd hmem hcon)]
    exact laurentCoeff_rowAtomSum_self hσ j₀ (Rτ j₀) w hinvτ hcovτ
  have h2 : (∑ j ∈ Finset.range n, laurentCoeff (rowAtomSum F σ τ j (Rσ j)) w
      (-((j₀ : ℤ) + 1))) = rowCoeff F σ (-((j₀ : ℤ) + 1)) w := by
    rw [Finset.sum_eq_single j₀ (fun j _ hjne =>
      laurentCoeff_rowAtomSum_of_ne_order hτ j (Rσ j) w hℓ (by
        intro hcon
        exact hjne (by omega))) (fun hcon => absurd hmem hcon)]
    exact laurentCoeff_rowAtomSum_self hτ j₀ (Rσ j₀) w hinvσ hcovσ
  rw [h1, h2]

end

end GaloisForLFunctions.HTGeometry
