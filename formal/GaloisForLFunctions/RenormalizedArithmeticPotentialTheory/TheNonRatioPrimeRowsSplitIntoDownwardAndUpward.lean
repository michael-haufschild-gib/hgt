import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePrimeFormCollapsesOnThePoleProfile
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheShellsRepayEveryConductor
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilMatrixDecomposesAtEveryOverlap

/-!
# The non-ratio prime rows split into downward and upward rows

Row `n` of the non-ratio prime matrix pairs the atom `n` with the atoms `j` near `n/k` (downward:
`kj ≈ n`) and near `kn` (upward: `j ≈ kn`), for every prime power `k`, with the exact ratios removed.
For a Ramanujan mode the downward row collapses by the divisor jet
`Σ_{a∣ℓ} Λ(a) c_m(ℓ/a) = c_m(ℓ) log ℓ − J_m(ℓ)`; the upward row is an affine prime window, whose
Ramanujan average `c_m(n) c_m(h)/φ(m)` produces the completed shell correction

`κ_m(c) = (2/(M φ(m))) Σ_{1≤h<c} c_m(h) ∫_{h/c}^1 G(u)/u du`.

This file fixes the two rows and the correction (`downwardPrimeRow`, `upwardPrimeRow`,
`shellCorrection`).
-/

noncomputable section

open MeasureTheory Finset
open scoped Real

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis BezoutValuationIncidence CompletedShell
open _root_.RHTower (vonMangoldtAtom)

/-- The upward non-ratio prime row: partners `j ≈ kn`, exact ratios `j = kn` removed. -/
def upwardPrimeRow (g : ℝ → ℝ) (N : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑' k : ℕ, vonMangoldtAtom k * ∑ j ∈ Icc 1 N, x j *
    (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n)))

/-- The downward non-ratio prime row: partners `j` with `kj ≈ n`, exact ratios `n = kj` removed. -/
def downwardPrimeRow (g : ℝ → ℝ) (N : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑' k : ℕ, vonMangoldtAtom k * ∑ j ∈ Icc 1 N, x j *
    (if n = k * j then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log j)))

/-- The completed shell correction of conductor `m`:
`κ_m(c) = (2/(M φ(m))) Σ_{1≤h<c} c_m(h) ∫_{h/c}^1 G(u)/u du`. -/
def shellCorrection (φ : ℝ → ℝ) (c : ℝ) (m : ℕ) : ℝ :=
  2 / ((∫ u, φ u ^ 2) * m.totient) * ∑ h ∈ Finset.Ico 1 ⌈c⌉₊,
    ramanujanLagCoefficient m h * ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u

/-- The completed conductor energy is the reference energy minus the shell correction. -/
theorem completedConductorEnergy_eq_sub_shellCorrection {φ : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    {m : ℕ} (hm : 0 < m) :
    completedConductorEnergy φ c m = completeWeilAdjunctionEnergy φ c m - shellCorrection φ c m :=
  completedConductorEnergy_eq_reference_sub_shells hc hm

/-! ### The row identity -/

section Rows

open ArithmeticLorentzianGeometry CriticalArithmeticCorrelationTheory ArithmeticElectrostatics
  ArithmeticEffectivityTheory

variable {g : ℝ → ℝ} {w : ℝ}

/-- The two Hecke pairings of two atoms are autocorrelation values of the bump. -/
theorem integral_atom_mul_atom_sub_log (g : ℝ → ℝ) (n j k : ℕ) :
    (∫ t, atom g n t * atom g j (t - Real.log k)) =
      bumpCorr g (Real.log k - (Real.log n - Real.log j)) := by
  rw [← bumpCorr_neg, bumpCorr, ← integral_sub_right_eq_self
    (fun v => g v * g (v + -(Real.log k - (Real.log n - Real.log j)))) (Real.log n)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [atom]
  ring_nf

theorem integral_atom_mul_atom_add_log (g : ℝ → ℝ) (n j k : ℕ) :
    (∫ t, atom g n t * atom g j (t + Real.log k)) =
      bumpCorr g (Real.log k - (Real.log j - Real.log n)) := by
  rw [bumpCorr, ← integral_sub_right_eq_self
    (fun v => g v * g (v + (Real.log k - (Real.log j - Real.log n)))) (Real.log n)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [atom]
  ring_nf

/-- The prime pairing of two horizon atoms minus its ratio part is the non-ratio lag series. -/
theorem primePair_atom_sub_ratio_eq_tsum (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w)
    {N n j : ℕ} (hn : n ∈ Icc 1 N) (hj : j ∈ Icc 1 N) :
    primePair (atom g n) (atom g j) - (∫ u, g u ^ 2) * weilPrimeKernel n j =
      ∑' k : ℕ, vonMangoldtAtom k *
        ((if n = k * j then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log j))) +
          (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n)))) := by
  set R := Real.log N + w + 1 with hR
  have hsn := supportedIn_atom (g := g) hgsupp hw hn
  have hsj := supportedIn_atom (g := g) hgsupp hw hj
  -- the pairing series is finitely supported
  have hvan : ∀ k, lagRange R ≤ k → (∫ t, atom g n t * atom g j (t - Real.log k)) = 0 ∧
      (∫ t, atom g n t * atom g j (t + Real.log k)) = 0 := by
    intro k hk
    have hl := two_mul_lt_abs_log_of_lagRange_le hk
    refine ⟨?_, ?_⟩
    · refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun t => ?_)
      change atom g n t * atom g j (t - Real.log k) = 0
      rw [sub_eq_add_neg]
      exact mul_shift_eq_zero_of_supportedIn hsn hsj (by rwa [abs_neg]) t
    · refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun t => ?_)
      exact mul_shift_eq_zero_of_supportedIn hsn hsj hl t
  set K := max (lagRange R) (N + 1) with hK
  have hpair : primePair (atom g n) (atom g j) = ∑ k ∈ range K, vonMangoldtAtom k *
      ((∫ t, atom g n t * atom g j (t - Real.log k)) + ∫ t, atom g n t * atom g j (t + Real.log k)) := by
    rw [primePair]
    refine tsum_eq_sum fun k hk => ?_
    have hk' : lagRange R ≤ k := by
      have : K ≤ k := by simpa using hk
      exact le_trans (le_max_left _ _) this
    rw [(hvan k hk').1, (hvan k hk').2, add_zero, mul_zero]
  have hn1 := (mem_Icc.mp hn).1
  have hj1 := (mem_Icc.mp hj).1
  have hratio : weilPrimeKernel n j = ∑ k ∈ range K, vonMangoldtAtom k *
      ((if n = k * j then 1 else 0) + (if j = k * n then 1 else 0)) := by
    have hsub : range (N + 1) ⊆ range K := range_subset_range.mpr (le_max_right _ _)
    have hext : ∀ k ∈ range K, k ∉ range (N + 1) → vonMangoldtAtom k *
        ((if n = k * j then 1 else 0) + (if j = k * n then 1 else 0)) = 0 := by
      intro k _ hk
      have hkN : N < k := by simpa using hk
      have h1 : n ≠ k * j := fun h => by have := (mem_Icc.mp hn).2; nlinarith
      have h2 : j ≠ k * n := fun h => by have := (mem_Icc.mp hj).2; nlinarith
      rw [if_neg h1, if_neg h2]; ring
    rw [← Finset.sum_subset hsub hext]
    simp only [mul_add, sum_add_distrib]
    rw [sum_vonMangoldtAtom_ratio hj1 (mem_Icc.mp hn).2, sum_vonMangoldtAtom_ratio hn1 (mem_Icc.mp hj).2,
      weilPrimeKernel_eq_add, add_comm]
  have hsum : (∑' k : ℕ, vonMangoldtAtom k *
      ((if n = k * j then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log j))) +
        (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n))))) =
      ∑ k ∈ range K, vonMangoldtAtom k *
      ((if n = k * j then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log j))) +
        (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n)))) := by
    refine tsum_eq_sum fun k hk => ?_
    have hk' : lagRange R ≤ k := by
      have : K ≤ k := by simpa using hk
      exact le_trans (le_max_left _ _) this
    have h1 := (hvan k hk').1
    have h2 := (hvan k hk').2
    rw [integral_atom_mul_atom_sub_log] at h1
    rw [integral_atom_mul_atom_add_log] at h2
    rw [h1, h2]
    split_ifs <;> simp
  rw [hsum, hpair, hratio, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_atom_mul_atom_sub_log, integral_atom_mul_atom_add_log]
  have hk1 : ∀ hk : n = k * j, Real.log k - (Real.log n - Real.log j) = 0 := by
    intro hk
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; rw [zero_mul] at hk; omega
    · rw [hk]; push_cast
      rw [Real.log_mul (by exact_mod_cast h0.ne') (by exact_mod_cast (by omega : j ≠ 0))]; ring
  have hk2 : ∀ hk : j = k * n, Real.log k - (Real.log j - Real.log n) = 0 := by
    intro hk
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; rw [zero_mul] at hk; omega
    · rw [hk]; push_cast
      rw [Real.log_mul (by exact_mod_cast h0.ne') (by exact_mod_cast (by omega : n ≠ 0))]; ring
  by_cases h1 : n = k * j <;> by_cases h2 : j = k * n
  · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2, hk1 h1, hk2 h2, bumpCorr_zero]; ring
  · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2, hk1 h1, bumpCorr_zero]; ring
  · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2, hk2 h2, bumpCorr_zero]; ring
  · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]; ring

/-- Beyond the lag range of the horizon window both lag values of two horizon atoms vanish. -/
theorem bumpCorr_lag_eq_zero (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w)
    {N n j k : ℕ} (hn : n ∈ Icc 1 N) (hj : j ∈ Icc 1 N)
    (hk : lagRange (Real.log N + w + 1) ≤ k) :
    bumpCorr g (Real.log k - (Real.log n - Real.log j)) = 0 ∧
      bumpCorr g (Real.log k - (Real.log j - Real.log n)) = 0 := by
  have hsn := supportedIn_atom (g := g) hgsupp hw hn
  have hsj := supportedIn_atom (g := g) hgsupp hw hj
  have hl := two_mul_lt_abs_log_of_lagRange_le hk
  rw [← integral_atom_mul_atom_sub_log, ← integral_atom_mul_atom_add_log]
  refine ⟨?_, ?_⟩
  · refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun t => ?_)
    change atom g n t * atom g j (t - Real.log k) = 0
    rw [sub_eq_add_neg]
    exact mul_shift_eq_zero_of_supportedIn hsn hsj (by rwa [abs_neg]) t
  · refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun t => ?_)
    exact mul_shift_eq_zero_of_supportedIn hsn hsj hl t

/-- The downward row as a finite sum over the lag range. -/
theorem downwardPrimeRow_eq_sum (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w)
    {N n : ℕ} (hn : n ∈ Icc 1 N) (x : ℕ → ℝ) :
    downwardPrimeRow g N x n = ∑ k ∈ range (lagRange (Real.log N + w + 1)), vonMangoldtAtom k *
      ∑ j ∈ Icc 1 N, x j *
        (if n = k * j then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log j))) := by
  rw [downwardPrimeRow]
  refine tsum_eq_sum fun k hk => ?_
  have hk' : lagRange (Real.log N + w + 1) ≤ k := by simpa using hk
  rw [Finset.sum_eq_zero fun j hj => by
    rw [(bumpCorr_lag_eq_zero hgsupp hw hn hj hk').1]; split_ifs <;> simp, mul_zero]

theorem upwardPrimeRow_eq_sum (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w)
    {N n : ℕ} (hn : n ∈ Icc 1 N) (x : ℕ → ℝ) :
    upwardPrimeRow g N x n = ∑ k ∈ range (lagRange (Real.log N + w + 1)), vonMangoldtAtom k *
      ∑ j ∈ Icc 1 N, x j *
        (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n))) := by
  rw [upwardPrimeRow]
  refine tsum_eq_sum fun k hk => ?_
  have hk' : lagRange (Real.log N + w + 1) ≤ k := by simpa using hk
  rw [Finset.sum_eq_zero fun j hj => by
    rw [(bumpCorr_lag_eq_zero hgsupp hw hn hj hk').2]; split_ifs <;> simp, mul_zero]

/-- **Row identity.** Each row of the non-ratio prime matrix is the downward plus the upward row,
read at the atom mass. -/
theorem fullWeilNonRatioMatrix_row_eq {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) (n : PrimeHorizonIndex N) :
    (Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) x) n =
      (downwardPrimeRow (atomDilate φ (c / N)) N (primeHorizonExtension x) n +
        upwardPrimeRow (atomDilate φ (c / N)) N (primeHorizonExtension x) n) /
          (∫ u, atomDilate φ (c / N) u ^ 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw := div_pos hc hN0
  obtain ⟨_, hgsupp, _⟩ := RenormalizedArithmeticPotentialTheory.atomDilate_facts hφ hsupp hw
  set g := atomDilate φ (c / N) with hgdef
  set G0 := ∫ u, g u ^ 2 with hG0
  set K := lagRange (Real.log N + c / N + 1) with hK
  have hnI : (n : ℕ) ∈ Icc 1 N := n.property
  -- each entry as a finite lag sum
  have hentry : ∀ j ∈ Icc 1 N, primePair (atom g n) (atom g j) - G0 * weilPrimeKernel n j =
      ∑ k ∈ range (max K (N + 1)), vonMangoldtAtom k *
        ((if (n : ℕ) = k * j then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log j))) +
          (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n)))) := by
    intro j hj
    rw [primePair_atom_sub_ratio_eq_tsum hgsupp hw.le hnI hj]
    refine tsum_eq_sum fun k hk => ?_
    have hk' : K ≤ k := by
      have : max K (N + 1) ≤ k := by simpa using hk
      exact le_trans (le_max_left _ _) this
    obtain ⟨h1, h2⟩ := bumpCorr_lag_eq_zero hgsupp hw.le hnI hj hk'
    rw [h1, h2]
    split_ifs <;> simp
  have hdown := downwardPrimeRow_eq_sum hgsupp hw.le hnI (primeHorizonExtension x)
  have hup := upwardPrimeRow_eq_sum hgsupp hw.le hnI (primeHorizonExtension x)
  -- extend the lag ranges to a common range
  have hextd : ∀ F : ℕ → ℝ, (∀ k, K ≤ k → F k = 0) →
      ∑ k ∈ range K, F k = ∑ k ∈ range (max K (N + 1)), F k := by
    intro F hF
    refine Finset.sum_subset (range_subset_range.mpr (le_max_left _ _)) fun k _ hk => hF k ?_
    simpa using hk
  rw [hextd _ (fun k hk => by
      rw [Finset.sum_eq_zero fun j hj => by
        rw [(bumpCorr_lag_eq_zero hgsupp hw.le hnI hj hk).1]; split_ifs <;> simp, mul_zero])] at hdown
  rw [hextd _ (fun k hk => by
      rw [Finset.sum_eq_zero fun j hj => by
        rw [(bumpCorr_lag_eq_zero hgsupp hw.le hnI hj hk).2]; split_ifs <;> simp, mul_zero])] at hup
  have hGpos : 0 < G0 := by
    rw [hG0, hgdef, integral_atomDilate_sq hw]; exact mul_pos hw hM
  rw [hdown, hup, ← Finset.sum_add_distrib]
  change (∑ j : PrimeHorizonIndex N, fullWeilNonRatioMatrix φ c N n j * x j) = _
  calc (∑ j : PrimeHorizonIndex N, fullWeilNonRatioMatrix φ c N n j * x j)
      = ∑ j ∈ Icc 1 N, (primePair (atom g n) (atom g j) / G0 - weilPrimeKernel n j) *
          primeHorizonExtension x j := by
        rw [← Finset.sum_coe_sort (Icc 1 N)]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [fullWeilNonRatioMatrix_apply, primeHorizonExtension_coe]
    _ = ∑ j ∈ Icc 1 N, primeHorizonExtension x j * (∑ k ∈ range (max K (N + 1)), vonMangoldtAtom k *
          ((if (n : ℕ) = k * j then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log j))) +
            (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n))))) / G0 := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [← hentry j hj]
        field_simp
    _ = _ := by
        rw [← Finset.sum_div]
        congr 1
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring

end Rows

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
