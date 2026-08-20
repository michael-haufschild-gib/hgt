/-
# The vanishing micro-spectrum family

Truncating an `ℓ^p` spectrum and correcting the first `p − 1` moments by a micro-spectrum block of
vanishing energy gives a family of finite spectra whose low moments are *exactly* the prescribed
targets, for every truncation order, and whose high moments converge to those of the original
spectrum.  This is the card's sufficiency construction, assembled.

Main results:
* `truncSpectrum`, `truncSpectrum_moment` — the truncation and its moments.
* `exists_microSpectrumFamily` — **the family with exact low moments and convergent high moments**.
-/
import GaloisForLFunctions.HTGeometry.MicroSpectrumMomentAssembly
import GaloisForLFunctions.HTGeometry.SchattenSpectralDeterminant

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The truncation of a spectrum to its first `n` entries. -/
def truncSpectrum (lam : ℕ → ℂ) (n : ℕ) : Multiset ℂ := (Multiset.range n).map lam

theorem truncSpectrum_moment (lam : ℕ → ℂ) (n : ℕ) (f : ℂ → ℂ) :
    ((truncSpectrum lam n).map f).sum = ∑ i ∈ Finset.range n, f (lam i) := by
  rw [truncSpectrum, Multiset.map_map]
  rfl

theorem truncSpectrum_moment_real (lam : ℕ → ℂ) (n : ℕ) (f : ℂ → ℝ) :
    ((truncSpectrum lam n).map f).sum = ∑ i ∈ Finset.range n, f (lam i) := by
  rw [truncSpectrum, Multiset.map_map]
  rfl

/-- The high moments of the truncation converge to the power traces of the spectrum. -/
theorem tendsto_truncSpectrum_moment {p : ℕ} (hp : 0 < p) {lam : ℕ → ℂ}
    (hlam : IsSchattenSpectrum p lam) {m : ℕ} (hm : p ≤ m) :
    Tendsto (fun n => ((truncSpectrum lam n).map fun z => z ^ m).sum) atTop
      (nhds (schattenTracePower lam m)) := by
  have hsum : Summable fun i => (lam i) ^ m := summable_pow_of_le hp hm hlam
  have htend := hsum.hasSum.tendsto_sum_nat
  refine htend.congr fun n => ?_
  rw [truncSpectrum_moment]

/-- **The vanishing micro-spectrum family.**  For every prescribed low-moment target the finite
spectra realise it exactly at every truncation order, keep a uniform energy and sup bound, and have
high moments converging to those of the original spectrum. -/
theorem exists_microSpectrumFamily {p : ℕ} (hp : 0 < p) {lam : ℕ → ℂ}
    (hlam : IsSchattenSpectrum p lam) {Bd : ℝ} (hBd : ∀ i, ‖lam i‖ ≤ Bd) (c : ℕ → ℂ) :
    ∃ Sfin : ℕ → Multiset ℂ,
      (∀ n k, 1 ≤ k → k ≤ p - 1 → ((Sfin n).map fun z => z ^ k).sum = c k) ∧
      (∀ n, ((Sfin n).map fun z => ‖z‖ ^ p).sum
        ≤ (∑' i, ‖lam i‖ ^ p) + 1) ∧
      (∀ n, ∀ z ∈ Sfin n, ‖z‖ ≤ max Bd 1) ∧
      (∀ m, p ≤ m → Tendsto (fun n => ((Sfin n).map fun z => z ^ m).sum) atTop
        (nhds (schattenTracePower lam m))) := by
  classical
  -- the correction targets at truncation order `n`
  set target : ℕ → ℕ → ℂ := fun n k =>
    c k - ((truncSpectrum lam n).map fun z => z ^ k).sum with htarget
  have hblock : ∀ n : ℕ, ∃ B : Multiset ℂ,
      (∀ k, 1 ≤ k → k ≤ p - 1 → (B.map fun z => z ^ k).sum = target n k) ∧
      (B.map fun z => ‖z‖ ^ p).sum < 1 / (n + 1 : ℝ) := by
    intro n
    exact exists_multiset_moment_realization p (p - 1) (by omega) (target n)
      (1 / (n + 1 : ℝ)) (by positivity)
  choose Bmul hBmom hBcost using hblock
  have hblocknorm : ∀ n : ℕ, ∀ z ∈ Bmul n, ‖z‖ ≤ 1 := by
    intro n z hz
    have hle : ‖z‖ ^ p ≤ ((Bmul n).map fun w => ‖w‖ ^ p).sum := by
      refine Multiset.single_le_sum (fun x hx => ?_) _ (Multiset.mem_map_of_mem _ hz)
      obtain ⟨w, -, rfl⟩ := Multiset.mem_map.mp hx
      exact pow_nonneg (norm_nonneg w) p
    have hlt1 : ‖z‖ ^ p < 1 := by
      refine lt_of_le_of_lt hle (lt_of_lt_of_le (hBcost n) ?_)
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    by_contra hcon
    rw [not_le] at hcon
    exact absurd (one_le_pow₀ hcon.le) (not_le.mpr hlt1)
  refine ⟨fun n => truncSpectrum lam n + Bmul n, ?_, ?_, ?_, ?_⟩
  · intro n k hk1 hk
    rw [Multiset.map_add, Multiset.sum_add, hBmom n k hk1 hk, htarget]
    ring
  · intro n
    rw [Multiset.map_add, Multiset.sum_add]
    have hcost : ((Bmul n).map (fun z => ‖z‖ ^ p)).sum ≤ 1 := by
      refine le_of_lt (lt_of_lt_of_le (hBcost n) ?_)
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have htrunc : ((truncSpectrum lam n).map fun z => ‖z‖ ^ p).sum ≤ ∑' i, ‖lam i‖ ^ p := by
      rw [truncSpectrum_moment_real]
      exact hlam.sum_le_tsum _ (fun i _ => pow_nonneg (norm_nonneg _) p)
    linarith
  · intro n z hz
    rcases Multiset.mem_add.mp hz with hz' | hz'
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hz'
      exact le_trans (hBd i) (le_max_left _ _)
    · exact le_trans (hblocknorm n z hz') (le_max_right _ _)
  · intro m hm
    have hzero : Tendsto (fun n => ((Bmul n).map fun z => z ^ m).sum) atTop (nhds 0) := by
      have hbound : ∀ n : ℕ, ‖((Bmul n).map fun z => z ^ m).sum‖ ≤ 1 / (n + 1 : ℝ) := by
        intro n
        have hmap : ‖((Bmul n).map fun z => z ^ m).sum‖
            ≤ ((Bmul n).map fun z => ‖z‖ ^ m).sum := by
          refine le_trans (norm_multiset_sum_le _) (le_of_eq ?_)
          rw [Multiset.map_map]
          refine congrArg Multiset.sum (Multiset.map_congr rfl fun z _ => ?_)
          exact norm_pow z m
        have hterm : ∀ z ∈ Bmul n, ‖z‖ ^ m ≤ ‖z‖ ^ p := by
          intro z hz
          exact pow_le_pow_of_le_one (norm_nonneg z) (hblocknorm n z hz) hm
        refine le_trans hmap (le_trans ?_ (le_of_lt (hBcost n)))
        exact Multiset.sum_map_le_sum_map _ _ hterm
      refine squeeze_zero_norm hbound ?_
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have hsum := (tendsto_truncSpectrum_moment hp hlam hm).add hzero
    rw [add_zero] at hsum
    refine hsum.congr fun n => ?_
    rw [Multiset.map_add, Multiset.sum_add]

end

end GaloisForLFunctions.HTGeometry
