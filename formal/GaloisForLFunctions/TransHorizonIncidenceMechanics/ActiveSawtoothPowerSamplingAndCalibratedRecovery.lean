import GaloisForLFunctions.TransHorizonIncidenceMechanics.RadicalCheckpointSignRigidityAndGaugeLaw
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Active sawtooth power sampling and calibrated recovery

At a fixed sieve horizon, active self-endpoint samples form a divisor transform
of the nonunit coefficients. An explicit Moebius inverse recovers these coefficients.
For squarefree-supported weights every sample may be moved to an arbitrarily high
common power, uniformly beyond any prescribed observation scale.
Within the squarefree-supported class only squarefree nonunit sampling bases are needed.

The finite sample kernel is exactly agreement on coefficients in [2,N]. Thus these
samples determine all additive response differences and every Dirichlet-energy
window. One harmonic scalar restores the entire visible coefficient vector and all
prefix defects, without a harmonic-null restriction.

Inverse error is at most four times the sum of divisor-indexed sample errors; this
is an l1 estimate, not a divisor-count-independent sup-norm estimate. Coefficients
outside [1,N] remain invisible to this fixed-horizon observation map.
-/

open Finset
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.BiScaleUncertainty
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
set_option autoImplicit false

/-- The self-endpoint active response is an exact divisor transform, at every horizon. -/
theorem two_mul_active_self_eq_divisor_transform (N : ℕ) (c : ℕ → ℝ) {k : ℕ}
    (hk : 1 ≤ k) :
    2 * activeCenteredSawtoothSum N c k k =
      ∑ d ∈ k.divisors, truncatedSieveWeight N (fun j => c j - c j / (j : ℝ)) d := by
  have h := activeCenteredSawtoothSum_at_self_eq_half_sieveSeq_sub N c (k - 1)
  rw [Nat.sub_add_cancel hk] at h
  calc
    _ = sieveSeq N c k - sieveSeq N (fun j => c j / (j : ℝ)) k := by linarith only [h]
    _ = sieveSeq N (fun j => c j - c j / (j : ℝ)) k := by
      simp [sieveSeq, Finset.sum_sub_distrib]
    _ = _ := sieveSeq_eq_sievedDivisorSum N _ hk

/-- Explicit inverse of the nonunit active sawtooth divisor transform. -/
def activeSawtoothMobiusLift (a : ℕ → ℝ) (d : ℕ) : ℝ :=
  (2 * (d : ℝ) / ((d : ℝ) - 1)) *
    ∑ x ∈ d.divisorsAntidiagonal, (μ x.1 : ℝ) * a x.2

/-- Recover every visible nonunit coefficient from one horizon's self-endpoint observations. -/
theorem activeSawtoothMobiusLift_recovers (N : ℕ) (c : ℕ → ℝ) {d : ℕ}
    (hd : 2 ≤ d) (hdN : d ≤ N) :
    activeSawtoothMobiusLift (fun j => activeCenteredSawtoothSum N c j j) d = c d := by
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := truncatedSieveWeight N (fun j => c j - c j / (j : ℝ)))
    (g := fun j => 2 * activeCenteredSawtoothSum N c j j)).mp
      (fun n hn => (two_mul_active_self_eq_divisor_transform N c hn).symm) d (by omega)
  have hdI : d ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, hdN⟩
  simp only [truncatedSieveWeight, if_pos hdI] at hinv
  let S := ∑ x ∈ d.divisorsAntidiagonal,
    (μ x.1 : ℝ) * activeCenteredSawtoothSum N c x.2 x.2
  have hsum : (∑ x ∈ d.divisorsAntidiagonal,
      (μ x.1 : ℝ) * (2 * activeCenteredSawtoothSum N c x.2 x.2)) = 2 * S := by
    dsimp [S]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [hsum] at hinv
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hdR1 : (d : ℝ) - 1 ≠ 0 := by
    have htwo : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hscale := congrArg (fun x : ℝ => x * (d : ℝ)) hinv
  have hcancel := div_mul_cancel₀ (c d) hdR
  change (2 * (d : ℝ) / ((d : ℝ) - 1)) * S = c d
  field_simp [hdR1]
  nlinarith only [hscale, hcancel]

/-- The same inverse uses arbitrarily high common powers for squarefree-supported weights. -/
theorem activeSawtoothMobiusLift_recovers_from_powers (N : ℕ) {c : ℕ → ℝ}
    (hc : ∀ d : ℕ, ¬ Squarefree d → c d = 0) {m d : ℕ}
    (hm : 1 ≤ m) (hd : 2 ≤ d) (hdN : d ≤ N) :
    activeSawtoothMobiusLift (fun j => activeCenteredSawtoothSum N c (j ^ m) (j ^ m)) d =
      c d := by
  rw [← activeSawtoothMobiusLift_recovers N c hd hdN]
  unfold activeSawtoothMobiusLift
  congr 1
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxpos := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)
  dsimp only
  rw [(activeCenteredSawtoothSum_pow_of_squarefree_support N hc hxpos hm).2]

/-- Agreement on nonunit coefficients determines every active sawtooth observation at the horizon. -/
theorem activeCenteredSawtoothSum_eq_of_tail_eq (N : ℕ) (c b : ℕ → ℝ)
    (h : ∀ d ∈ Finset.Icc 2 N, c d = b d) (m k : ℕ) :
    activeCenteredSawtoothSum N c m k = activeCenteredSawtoothSum N b m k := by
  unfold activeCenteredSawtoothSum
  congr 1
  refine Finset.sum_congr rfl fun d hd => ?_
  by_cases hd1 : d = 1
  · subst d
    simp [centeredDiscreteSawtooth_one]
  · have hdI := (Finset.mem_filter.mp hd).1
    rw [h d (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hdI).1; omega,
      (Finset.mem_Icc.mp hdI).2⟩)]

/-- A finite self-endpoint sample vector has precisely the unit-coefficient kernel. -/
theorem active_self_samples_eq_iff_tail_eq (N : ℕ) (c b : ℕ → ℝ) :
    (∀ j ∈ Finset.Icc 2 N, activeCenteredSawtoothSum N c j j =
      activeCenteredSawtoothSum N b j j) ↔
        ∀ d ∈ Finset.Icc 2 N, c d = b d := by
  constructor
  · intro h d hd
    have hd2 := (Finset.mem_Icc.mp hd).1
    have hdN := (Finset.mem_Icc.mp hd).2
    rw [← activeSawtoothMobiusLift_recovers N c hd2 hdN,
      ← activeSawtoothMobiusLift_recovers N b hd2 hdN]
    unfold activeSawtoothMobiusLift
    congr 1
    refine Finset.sum_congr rfl fun x hx => ?_
    dsimp only
    have hxd := Nat.snd_mem_divisors_of_mem_antidiagonal hx
    have hxpos := Nat.pos_of_mem_divisors hxd
    have hxle := (Nat.le_of_dvd (by omega : 0 < d) (Nat.dvd_of_mem_divisors hxd)).trans hdN
    by_cases hx1 : x.2 = 1
    · simp [hx1]
    · rw [h x.2 (Finset.mem_Icc.mpr ⟨by omega, hxle⟩)]
  · intro h j _
    exact activeCenteredSawtoothSum_eq_of_tail_eq N c b h j j

/-- All active sawtooth data at a fixed horizon detect exactly the visible nonunit coefficients. -/
theorem active_profile_eq_iff_tail_eq (N : ℕ) (c b : ℕ → ℝ) :
    (∀ m k, activeCenteredSawtoothSum N c m k = activeCenteredSawtoothSum N b m k) ↔
      ∀ d ∈ Finset.Icc 2 N, c d = b d := by
  constructor
  · intro h
    exact (active_self_samples_eq_iff_tail_eq N c b).mp (fun j _ => h j j)
  · intro h m k
    exact activeCenteredSawtoothSum_eq_of_tail_eq N c b h m k

/-- At every positive common exponent, power samples have exactly the same finite kernel. -/
theorem active_power_samples_eq_iff_tail_eq (N : ℕ) {c b : ℕ → ℝ}
    (hc : ∀ d : ℕ, ¬ Squarefree d → c d = 0)
    (hb : ∀ d : ℕ, ¬ Squarefree d → b d = 0) {m : ℕ} (hm : 1 ≤ m) :
    (∀ j ∈ Finset.Icc 2 N, activeCenteredSawtoothSum N c (j ^ m) (j ^ m) =
      activeCenteredSawtoothSum N b (j ^ m) (j ^ m)) ↔
        ∀ d ∈ Finset.Icc 2 N, c d = b d := by
  rw [← active_self_samples_eq_iff_tail_eq N c b]
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  have hjpos : 1 ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
  rw [(activeCenteredSawtoothSum_pow_of_squarefree_support N hc hjpos hm).2,
    (activeCenteredSawtoothSum_pow_of_squarefree_support N hb hjpos hm).2]

/-- Squarefree bases alone suffice inside the squarefree-supported weight class. -/
theorem active_squarefree_power_samples_eq_iff_tail_eq (N : ℕ) {c b : ℕ → ℝ}
    (hc : ∀ d : ℕ, ¬ Squarefree d → c d = 0)
    (hb : ∀ d : ℕ, ¬ Squarefree d → b d = 0) {m : ℕ} (hm : 1 ≤ m) :
    (∀ j ∈ Finset.Icc 2 N, Squarefree j →
      activeCenteredSawtoothSum N c (j ^ m) (j ^ m) =
        activeCenteredSawtoothSum N b (j ^ m) (j ^ m)) ↔
          ∀ d ∈ Finset.Icc 2 N, c d = b d := by
  constructor
  · intro h d hd
    by_cases hsq : Squarefree d
    · have hd2 := (Finset.mem_Icc.mp hd).1
      have hdN := (Finset.mem_Icc.mp hd).2
      rw [← activeSawtoothMobiusLift_recovers_from_powers N hc hm hd2 hdN,
        ← activeSawtoothMobiusLift_recovers_from_powers N hb hm hd2 hdN]
      unfold activeSawtoothMobiusLift
      congr 1
      refine Finset.sum_congr rfl fun x hx => ?_
      dsimp only
      have hxd := Nat.snd_mem_divisors_of_mem_antidiagonal hx
      have hxpos := Nat.pos_of_mem_divisors hxd
      have hxdvd := Nat.dvd_of_mem_divisors hxd
      have hxle := (Nat.le_of_dvd (by omega : 0 < d) hxdvd).trans hdN
      by_cases hx1 : x.2 = 1
      · simp [hx1]
      · rw [h x.2 (Finset.mem_Icc.mpr ⟨by omega, hxle⟩) (hsq.squarefree_of_dvd hxdvd)]
    · rw [hc d hsq, hb d hsq]
  · intro h j _ _
    exact activeCenteredSawtoothSum_eq_of_tail_eq N c b h (j ^ m) (j ^ m)

/-- Finite-horizon response depends only on visible coefficients. -/
theorem sieveSeq_eq_of_weight_eq_on_Icc (N k : ℕ) (c b : ℕ → ℝ)
    (h : ∀ d ∈ Finset.Icc 1 N, c d = b d) : sieveSeq N c k = sieveSeq N b k := by
  unfold sieveSeq
  exact Finset.sum_congr rfl (fun d hd => h d (Finset.mem_filter.mp hd).1)

/-- All prefix defects depend only on the same finite coefficient vector. -/
theorem sieveRenormalizedPrefixDefect_eq_of_weight_eq_on_Icc (N M : ℕ) (c b : ℕ → ℝ)
    (h : ∀ d ∈ Finset.Icc 1 N, c d = b d) :
    sieveRenormalizedPrefixDefect N M c = sieveRenormalizedPrefixDefect N M b := by
  simp only [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff,
    sieveSeq_eq_of_weight_eq_on_Icc N _ c b h]

private theorem tail_eq_unitShift_on_Icc (N : ℕ) (c b : ℕ → ℝ)
    (h : ∀ d ∈ Finset.Icc 2 N, c d = b d) :
    ∀ d ∈ Finset.Icc 1 N, c d = sieveUnitShiftWeight b (c 1 - b 1) d := by
  intro d hd
  by_cases hd1 : d = 1
  · subst d
    simp [sieveUnitShiftWeight]
  · have hd2 : 2 ≤ d := by have := (Finset.mem_Icc.mp hd).1; omega
    simp [sieveUnitShiftWeight, hd1, h d (Finset.mem_Icc.mpr ⟨hd2, (Finset.mem_Icc.mp hd).2⟩)]

/-- Equal nonunit coefficients leave exactly the unit coefficient as the harmonic-mean difference. -/
theorem finiteHarmonicSum_sub_of_tail_eq {N : ℕ} (hN : 1 ≤ N) (c b : ℕ → ℝ)
    (h : ∀ d ∈ Finset.Icc 2 N, c d = b d) :
    finiteHarmonicSum N c - finiteHarmonicSum N b = c 1 - b 1 := by
  unfold finiteHarmonicSum
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ d ∈ Finset.Icc 1 N,
      c d / (d : ℝ) - b d / (d : ℝ) = if d = 1 then c 1 - b 1 else 0 := by
    intro d hd
    by_cases hd1 : d = 1
    · subst d
      simp
    · have hd2 : 2 ≤ d := by have := (Finset.mem_Icc.mp hd).1; omega
      simp [hd1, h d (Finset.mem_Icc.mpr ⟨hd2, (Finset.mem_Icc.mp hd).2⟩)]
  rw [Finset.sum_congr rfl hterm]
  simp [hN]

/-- The harmonic scalar supplies exactly the response level missing from active data. -/
theorem sieveSeq_sub_eq_harmonic_sub_of_tail_eq (N k : ℕ) (c b : ℕ → ℝ)
    (h : ∀ d ∈ Finset.Icc 2 N, c d = b d) :
    sieveSeq N c k - sieveSeq N b k = finiteHarmonicSum N c - finiteHarmonicSum N b := by
  by_cases hN : 1 ≤ N
  · rw [finiteHarmonicSum_sub_of_tail_eq hN c b h,
      sieveSeq_eq_of_weight_eq_on_Icc N k c _ (tail_eq_unitShift_on_Icc N c b h),
      sieveSeq_unitShiftWeight hN]
    ring
  · have hN0 : N = 0 := by omega
    subst N
    simp [sieveSeq, finiteHarmonicSum]

/-- Exact all-prefix defect ambiguity left by equal active observations; no harmonic-null premise. -/
theorem sieveRenormalizedPrefixDefect_sub_of_tail_eq (N M : ℕ) (c b : ℕ → ℝ)
    (h : ∀ d ∈ Finset.Icc 2 N, c d = b d) :
    sieveRenormalizedPrefixDefect N M c - sieveRenormalizedPrefixDefect N M b =
      (finiteHarmonicSum N c - finiteHarmonicSum N b) *
        (sieveSeq N b (M + 1) - sieveSeq N b 1) := by
  by_cases hN : 1 ≤ N
  · rw [finiteHarmonicSum_sub_of_tail_eq hN c b h,
      sieveRenormalizedPrefixDefect_eq_of_weight_eq_on_Icc N M c _
        (tail_eq_unitShift_on_Icc N c b h), sieveRenormalizedPrefixDefect_unitShiftWeight]
    ring
  · have hN0 : N = 0 := by omega
    subst N
    simp [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff, sieveSeq, finiteHarmonicSum]

/-- Harmonic calibration and any common-power sample vector recover the complete visible weight. -/
theorem calibrated_active_power_samples_eq_iff_weight_eq (N : ℕ) {c b : ℕ → ℝ}
    (hc : ∀ d : ℕ, ¬ Squarefree d → c d = 0)
    (hb : ∀ d : ℕ, ¬ Squarefree d → b d = 0) {m : ℕ} (hm : 1 ≤ m) :
    (finiteHarmonicSum N c = finiteHarmonicSum N b ∧
      ∀ j ∈ Finset.Icc 2 N, Squarefree j → activeCenteredSawtoothSum N c (j ^ m) (j ^ m) =
        activeCenteredSawtoothSum N b (j ^ m) (j ^ m)) ↔
          ∀ d ∈ Finset.Icc 1 N, c d = b d := by
  rw [active_squarefree_power_samples_eq_iff_tail_eq N hc hb hm]
  constructor
  · rintro ⟨hH, htail⟩ d hd
    by_cases hd1 : d = 1
    · subst d
      have hN := (Finset.mem_Icc.mp hd).2
      have h := finiteHarmonicSum_sub_of_tail_eq hN c b htail
      rw [hH] at h
      linarith
    · exact htail d (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hd).1; omega,
        (Finset.mem_Icc.mp hd).2⟩)
  · intro h
    constructor
    · unfold finiteHarmonicSum
      exact Finset.sum_congr rfl fun d hd => by rw [h d hd]
    · intro d hd
      exact h d (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hd).1; omega,
        (Finset.mem_Icc.mp hd).2⟩)

/-- Calibrated finite power observations determine every prefix defect, at arbitrary scales. -/
theorem sieveRenormalizedPrefixDefect_eq_of_calibrated_power_samples (N M : ℕ)
    {c b : ℕ → ℝ} (hc : ∀ d : ℕ, ¬ Squarefree d → c d = 0)
    (hb : ∀ d : ℕ, ¬ Squarefree d → b d = 0) {m : ℕ} (hm : 1 ≤ m)
    (hH : finiteHarmonicSum N c = finiteHarmonicSum N b)
    (hobs : ∀ j ∈ Finset.Icc 2 N, Squarefree j → activeCenteredSawtoothSum N c (j ^ m) (j ^ m) =
      activeCenteredSawtoothSum N b (j ^ m) (j ^ m)) :
    sieveRenormalizedPrefixDefect N M c = sieveRenormalizedPrefixDefect N M b :=
  sieveRenormalizedPrefixDefect_eq_of_weight_eq_on_Icc N M c b
    ((calibrated_active_power_samples_eq_iff_weight_eq N hc hb hm).mp ⟨hH, hobs⟩)

/-- The finite power sample vector determines every additive jump without harmonic calibration. -/
theorem sieveSeq_addDiff_eq_of_active_power_samples (N k : ℕ) {c b : ℕ → ℝ}
    (hc : ∀ d : ℕ, ¬ Squarefree d → c d = 0)
    (hb : ∀ d : ℕ, ¬ Squarefree d → b d = 0) {m : ℕ} (hm : 1 ≤ m)
    (hobs : ∀ j ∈ Finset.Icc 2 N, Squarefree j → activeCenteredSawtoothSum N c (j ^ m) (j ^ m) =
      activeCenteredSawtoothSum N b (j ^ m) (j ^ m)) :
    sieveSeq N c (k + 1) - sieveSeq N c k = sieveSeq N b (k + 1) - sieveSeq N b k := by
  have htail := (active_squarefree_power_samples_eq_iff_tail_eq N hc hb hm).mp hobs
  have hnext := sieveSeq_sub_eq_harmonic_sub_of_tail_eq N (k + 1) c b htail
  have hprev := sieveSeq_sub_eq_harmonic_sub_of_tail_eq N k c b htail
  linarith only [hnext, hprev]

/-- Every additive-energy window is recovered from finite power samples alone. -/
theorem sieveDirichletWindow_eq_of_active_power_samples (N a L : ℕ) {c b : ℕ → ℝ}
    (hc : ∀ d : ℕ, ¬ Squarefree d → c d = 0)
    (hb : ∀ d : ℕ, ¬ Squarefree d → b d = 0) {m : ℕ} (hm : 1 ≤ m)
    (hobs : ∀ j ∈ Finset.Icc 2 N, Squarefree j → activeCenteredSawtoothSum N c (j ^ m) (j ^ m) =
      activeCenteredSawtoothSum N b (j ^ m) (j ^ m)) :
    (∑ j ∈ Finset.range L, (sieveSeq N c (a + j + 1) - sieveSeq N c (a + j)) ^ (2 : ℕ)) =
      ∑ j ∈ Finset.range L, (sieveSeq N b (a + j + 1) - sieveSeq N b (a + j)) ^ (2 : ℕ) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sieveSeq_addDiff_eq_of_active_power_samples N (a + j) hc hb hm hobs]

/-- The inverse amplification factor is uniformly at most four on nonunit coefficients. -/
theorem activeSawtoothMobiusLift_stability (a b : ℕ → ℝ) {d : ℕ} (hd : 2 ≤ d) :
    |activeSawtoothMobiusLift a d - activeSawtoothMobiusLift b d| ≤
      4 * ∑ x ∈ d.divisorsAntidiagonal, |a x.2 - b x.2| := by
  let K : ℝ := 2 * (d : ℝ) / ((d : ℝ) - 1)
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : 0 < (d : ℝ) - 1 := by linarith
  have hK0 : 0 ≤ K := div_nonneg (by positivity) hden.le
  have hK4 : K ≤ 4 := (div_le_iff₀ hden).mpr (by linarith)
  have heq : activeSawtoothMobiusLift a d - activeSawtoothMobiusLift b d =
      K * ∑ x ∈ d.divisorsAntidiagonal, (μ x.1 : ℝ) * (a x.2 - b x.2) := by
    unfold activeSawtoothMobiusLift
    dsimp [K]
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [heq, abs_mul, abs_of_nonneg hK0]
  calc
    _ ≤ K * ∑ x ∈ d.divisorsAntidiagonal, |(μ x.1 : ℝ) * (a x.2 - b x.2)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hK0
    _ ≤ K * ∑ x ∈ d.divisorsAntidiagonal, |a x.2 - b x.2| := by
      apply mul_le_mul_of_nonneg_left _ hK0
      apply Finset.sum_le_sum
      intro x _
      have hmu : |(μ x.1 : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := x.1))
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hmu (abs_nonneg (a x.2 - b x.2))
    _ ≤ _ := mul_le_mul_of_nonneg_right hK4 (Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- Recovery from distant power samples has no horizon- or exponent-dependent amplification factor. -/
theorem active_power_samples_coefficient_stability (N : ℕ) {c b : ℕ → ℝ}
    (hc : ∀ d : ℕ, ¬ Squarefree d → c d = 0)
    (hb : ∀ d : ℕ, ¬ Squarefree d → b d = 0) {m d : ℕ}
    (hm : 1 ≤ m) (hd : 2 ≤ d) (hdN : d ≤ N) :
    |c d - b d| ≤ 4 * ∑ x ∈ d.divisorsAntidiagonal,
      |activeCenteredSawtoothSum N c (x.2 ^ m) (x.2 ^ m) -
        activeCenteredSawtoothSum N b (x.2 ^ m) (x.2 ^ m)| := by
  rw [← activeSawtoothMobiusLift_recovers_from_powers N hc hm hd hdN,
    ← activeSawtoothMobiusLift_recovers_from_powers N hb hm hd hdN]
  exact activeSawtoothMobiusLift_stability _ _ hd

/-- One finite power-sampling scheme can lie beyond any prescribed scale and still recover every visible weight. -/
theorem exists_calibrated_power_recovery_above (N B : ℕ) :
    ∃ m : ℕ, 1 ≤ m ∧ (∀ j ∈ Finset.Icc 2 N, B < j ^ m) ∧
      ∀ c b : ℕ → ℝ, (∀ d : ℕ, ¬ Squarefree d → c d = 0) →
        (∀ d : ℕ, ¬ Squarefree d → b d = 0) →
        ((finiteHarmonicSum N c = finiteHarmonicSum N b ∧
          ∀ j ∈ Finset.Icc 2 N, Squarefree j → activeCenteredSawtoothSum N c (j ^ m) (j ^ m) =
            activeCenteredSawtoothSum N b (j ^ m) (j ^ m)) ↔
              ∀ d ∈ Finset.Icc 1 N, c d = b d) := by
  refine ⟨B + 1, by omega, ?_, ?_⟩
  · intro j hj
    have hj2 := (Finset.mem_Icc.mp hj).1
    have hpow : B + 1 < j ^ (B + 1) := Nat.lt_pow_self (by omega : 1 < j)
    omega
  · intro c b hc hb
    exact calibrated_active_power_samples_eq_iff_weight_eq N hc hb (by omega)

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
