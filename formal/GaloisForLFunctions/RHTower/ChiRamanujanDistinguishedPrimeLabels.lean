import GaloisForLFunctions.RHTower.ChiRamanujanCriticalDistinguishedPrime
import GaloisForLFunctions.RHTower.ChiRamanujanFiniteContractionProjectors
/-!
# Distinguished prime labels and the literal physical contractions

On the entire covered band, each distinguished source entry selects precisely
its own prime. The actual two-contraction projector therefore becomes equality
exclusion on those labels, retaining their intersection. Final statements use
finite domains and require no analytic premise. Reduced rational grouping and
the growing signed cubic estimate remain separate obligations.
-/

noncomputable section
open scoped BigOperators
namespace RHTower.BAGTrace


def ramanujanDistinguishedPrimeEntry (P : Finset ℕ) (p n : ℕ) : ℝ :=
  Real.log p*(ramanujanTorsionIndicator p n-ramanujanTorsionIndicator (p^2) n)*
    ∏ q ∈ (P.filter Nat.Prime).erase p, (1-ramanujanTorsionIndicator q n)

private lemma indicator_bounds (d n : ℕ) :
    0 ≤ ramanujanTorsionIndicator d n ∧ ramanujanTorsionIndicator d n ≤ 1 := by
  unfold ramanujanTorsionIndicator
  split_ifs <;> norm_num

theorem ramanujanDistinguishedPrimeEntry_nonneg (P : Finset ℕ) {p : ℕ}
    (hp : p.Prime) (n : ℕ) : 0 ≤ ramanujanDistinguishedPrimeEntry P p n := by
  have hd : 0 ≤ ramanujanTorsionIndicator p n-ramanujanTorsionIndicator (p^2) n := by
    by_cases h2 : p^2 ∣ n
    · have h1 : p ∣ n := (dvd_pow_self p (by omega : 2 ≠ 0)).trans h2
      simp [ramanujanTorsionIndicator,h1,h2]
    · simpa [ramanujanTorsionIndicator,h2] using (indicator_bounds p n).1
  exact mul_nonneg (mul_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_le)) hd)
    (Finset.prod_nonneg (fun q _ => sub_nonneg.mpr (indicator_bounds q n).2))

private lemma entry_at_prime (P : Finset ℕ) {p n : ℕ} (hp : p.Prime) (hn : n.Prime) :
    ramanujanDistinguishedPrimeEntry P p n = if n=p then Real.log p else 0 := by
  by_cases he : n=p
  · subst n
    have hs : ¬p^2 ∣ p := by
      simpa only [pow_two] using (Nat.squarefree_iff_prime_squarefree.mp hp.squarefree) p hp
    have hprod : (∏ q ∈ (P.filter Nat.Prime).erase p, (1-ramanujanTorsionIndicator q p))=1 := by
      apply Finset.prod_eq_one
      intro q hq
      have hqp : q ≠ p := (Finset.mem_erase.mp hq).1
      have hqprime : q.Prime := (Finset.mem_filter.mp (Finset.mem_erase.mp hq).2).2
      have hd : ¬q ∣ p := fun h => hqp ((Nat.prime_dvd_prime_iff_eq hqprime hp).mp h)
      simp [ramanujanTorsionIndicator,hd]
    rw [ramanujanDistinguishedPrimeEntry,hprod]
    simp [ramanujanTorsionIndicator,hs]
  · have hd : ¬p ∣ n := fun h => he ((Nat.prime_dvd_prime_iff_eq hp hn).mp h).symm
    have hd2 : ¬p^2 ∣ n := fun h => hd ((dvd_pow_self p (by omega : 2 ≠ 0)).trans h)
    simp [ramanujanDistinguishedPrimeEntry,ramanujanTorsionIndicator,hd,hd2,he]

private lemma multiplier_range (M : ℕ) {n : ℕ} (hn : 1 < n) (hnM : n ≤ M) :
    ramanujanDistinguishedPrimeMultiplier (Finset.range (M+1)) n =
      if n.Prime then Real.log n else 0 := by
  apply Complex.ofReal_injective
  have h := (sum_ramanujanCriticalPrimeAtomWeight_fourier_distinguished
    (Finset.range (M+1)) (n : ℤ)).symm.trans
      (sum_ramanujanCriticalPrimeAtomWeight_fourier_range M hn hnM)
  simpa only [Int.natAbs_natCast] using h

private lemma entry_range {M p n : ℕ} (hp : p.Prime) (hpM : p ≤ M)
    (hn : 1 < n) (hnM : n ≤ M) :
    ramanujanDistinguishedPrimeEntry (Finset.range (M+1)) p n =
      if n=p then Real.log p else 0 := by
  by_cases hprime : n.Prime
  · exact entry_at_prime _ hp hprime
  · have hs := multiplier_range M hn hnM
    rw [if_neg hprime] at hs
    change (∑ q ∈ (Finset.range (M+1)).filter Nat.Prime,
      ramanujanDistinguishedPrimeEntry (Finset.range (M+1)) q n)=0 at hs
    have hnonneg : ∀ q ∈ (Finset.range (M+1)).filter Nat.Prime,
        0 ≤ ramanujanDistinguishedPrimeEntry (Finset.range (M+1)) q n :=
      fun q hq => ramanujanDistinguishedPrimeEntry_nonneg
        (Finset.range (M+1)) (Finset.mem_filter.mp hq).2 n
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hs p
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hp⟩)
    rw [hzero,if_neg (show n ≠ p by rintro rfl; exact hprime hp)]

abbrev RamanujanBandPrime (M : ℕ) := ↥((Finset.range (M+1)).filter Nat.Prime)
abbrev RamanujanCoveredCoordinate (M : ℕ) := ↥(Finset.Icc 2 M)

/-- Every individual distinguished source selects exactly its own physical prime. -/
theorem ramanujanDistinguishedPrimeEntry_band (M : ℕ) (p : RamanujanBandPrime M)
    (n : RamanujanCoveredCoordinate M) :
    ramanujanDistinguishedPrimeEntry (Finset.range (M+1)) p n =
      if (n : ℕ)=(p : ℕ) then Real.log (p : ℕ) else 0 := by
  have hp := Finset.mem_filter.mp p.property
  have hn := Finset.mem_Icc.mp n.property
  exact entry_range hp.2 (by have := Finset.mem_range.mp hp.1; omega) (by omega) hn.2

/-- Both literal physical contractions become equality of distinguished labels;
the intersection is retained by the same complete projector. -/
theorem ramanujanDistinguishedPrimeEntry_projector (M : ℕ)
    (p q r : RamanujanBandPrime M) (a b c : RamanujanCoveredCoordinate M)
    (x : ℝ × ℝ × ℝ) :
    ((ramanujanDistinguishedPrimeEntry (Finset.range (M+1)) p a*
      ramanujanDistinguishedPrimeEntry (Finset.range (M+1)) q b*
      ramanujanDistinguishedPrimeEntry (Finset.range (M+1)) r c : ℝ) : ℂ)*
        (ramanujanNoncontractingProjector (M+1)
          (ramanujanTripleFourierPhase ((a : ℕ),(b : ℕ),(c : ℕ)))) x =
    if (p : ℕ)=(r : ℕ) ∨ (q : ℕ)=(r : ℕ) then 0 else
      ((ramanujanDistinguishedPrimeEntry (Finset.range (M+1)) p a*
        ramanujanDistinguishedPrimeEntry (Finset.range (M+1)) q b*
        ramanujanDistinguishedPrimeEntry (Finset.range (M+1)) r c : ℝ) : ℂ)*
          ramanujanTripleFourierPhase ((a : ℕ),(b : ℕ),(c : ℕ)) x := by
  rw [ramanujanNoncontractingProjector_nat_phase M
    (Finset.mem_Icc.mp a.property).2 (Finset.mem_Icc.mp b.property).2 (Finset.mem_Icc.mp c.property).2]
  simp only [ramanujanDistinguishedPrimeEntry_band]
  by_cases ha : (a : ℕ)=(p : ℕ) <;> by_cases hb : (b : ℕ)=(q : ℕ) <;>
    by_cases hc : (c : ℕ)=(r : ℕ) <;> simp_all
  split_ifs <;> simp_all

end RHTower.BAGTrace
