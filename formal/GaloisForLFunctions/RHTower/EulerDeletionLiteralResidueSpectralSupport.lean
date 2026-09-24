import GaloisForLFunctions.RHTower.Sieve.PeriodicDFTSupport

/-!
# Spectral support of the literal finite centered residue source

At the symbolic factorial common period, the finite centered residue source
has Fourier mass only at modes resonant with at least one source modulus.
This is an exact support theorem, independent of coefficient signs.
-/

noncomputable section

namespace RHTower.Sieve

def liftedNormalizedResidue (P d : ℕ) (x : ZMod P) : ℂ :=
  ((x.val % d : ℕ) : ℂ) / (d : ℂ) -
    ((d : ℂ) - 1) / (2 * (d : ℂ))

theorem liftedNormalizedResidue_periodic {P d : ℕ} [NeZero P]
    (hdvd : d ∣ P) (x : ZMod P) :
    liftedNormalizedResidue P d (x + (d : ZMod P)) =
      liftedNormalizedResidue P d x := by
  let c : ZMod P →+* ZMod d := ZMod.castHom hdvd (ZMod d)
  have hval (y : ZMod P) : (c y).val = y.val % d := by
    change (ZMod.castHom hdvd (ZMod d) y).val = y.val % d
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  have hdz : c (d : ZMod P) = 0 := by simp [c]
  unfold liftedNormalizedResidue
  rw [← hval (x + d), ← hval x, map_add, hdz, add_zero]

def centeredSourcePeriod (P N : ℕ) (a : ℕ → ℝ) : ZMod P → ℂ :=
  ∑ d ∈ Finset.Icc 1 N,
    ((a d : ℝ) : ℂ) • liftedNormalizedResidue P d

def centeredSourcePeriodDFT (N k : ℕ) (a : ℕ → ℝ) : ℂ :=
  letI : NeZero N.factorial := ⟨(Nat.factorial_pos N).ne'⟩
  ZMod.dft (centeredSourcePeriod N.factorial N a) (k : ZMod N.factorial)

theorem dft_centeredSourcePeriod_factorial_zero_of_no_resonance
    (N k : ℕ) (a : ℕ → ℝ)
    (hnot : ∀ d ∈ Finset.Icc 1 N, ¬ N.factorial ∣ d * k) :
    centeredSourcePeriodDFT N k a = 0 := by
  letI : NeZero N.factorial := ⟨(Nat.factorial_pos N).ne'⟩
  unfold centeredSourcePeriodDFT
  unfold centeredSourcePeriod
  apply dft_sum_periodic_eq_zero_of_no_resonance
    (Finset.Icc 1 N) (fun d => ((a d : ℝ) : ℂ))
    (fun d => liftedNormalizedResidue N.factorial d) k
  · intro d hd x
    exact liftedNormalizedResidue_periodic
      (Nat.dvd_factorial (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2)
      x
  · exact hnot

/-- Every nonzero Fourier mode of the literal centered finite source resonates
with at least one residue period at the factorial common clock. -/
theorem centeredSourcePeriodDFT_nonzero_resonance
    (N k : ℕ) (a : ℕ → ℝ)
    (hne : centeredSourcePeriodDFT N k a ≠ 0) :
    ∃ d ∈ Finset.Icc 1 N, N.factorial ∣ d * k := by
  by_contra hnone
  have hnot : ∀ d ∈ Finset.Icc 1 N, ¬ N.factorial ∣ d * k := by
    intro d hd hdiv
    exact hnone ⟨d, hd, hdiv⟩
  exact hne (dft_centeredSourcePeriod_factorial_zero_of_no_resonance N k a hnot)

/-- Every nonzero source Fourier mode has reduced denominator at most the
source cutoff. This is the arithmetic Farey-support ceiling. -/
theorem centeredSourcePeriodDFT_nonzero_reduced_denominator_le
    (N k : ℕ) (a : ℕ → ℝ)
    (hne : centeredSourcePeriodDFT N k a ≠ 0) :
    N.factorial / Nat.gcd N.factorial k ≤ N := by
  obtain ⟨d, hd, hres⟩ :=
    centeredSourcePeriodDFT_nonzero_resonance N k a hne
  have hdiv := reduced_denominator_dvd_modulus_of_resonance
    (Nat.factorial_pos N) hres
  exact (Nat.le_of_dvd (Finset.mem_Icc.mp hd).1 hdiv).trans
    (Finset.mem_Icc.mp hd).2

end RHTower.Sieve
