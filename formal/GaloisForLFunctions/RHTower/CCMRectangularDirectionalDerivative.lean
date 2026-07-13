import GaloisForLFunctions.RHTower.CCMRectangularStieltjesAutocorrelation
import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowSubpowerGate

/-!
# The sharp dyadic window as a diagonal derivative of the rectangular source

Moving the rectangular width and logarithmic aperture together keeps the centre of its prime
tent fixed while increasing its radius.  The right derivative therefore reads the closed
multiplicative prime shell with coefficient one.  The matching polar derivative is the exact
square-root main term plus the decaying endpoint value.

At width `log 2 / 2`, the resulting closed shell dominates the requested half-open dyadic window.
The final theorem converts any suitable lower bound for this single right diagonal source slope
directly into the sharp von Mangoldt upper bound.
-/

open Set Filter
open scoped Topology

namespace RHTower

/-- Right derivative of a translated positive part, including its boundary atom. -/
theorem hasDerivWithinAt_max_zero_const_add_right (c : ℝ) :
    HasDerivWithinAt (fun t : ℝ => max 0 (c + t))
      (if 0 ≤ c then 1 else 0) (Ici 0) 0 := by
  by_cases hc : 0 ≤ c
  · rw [if_pos hc]
    have hlin : HasDerivAt (fun t : ℝ => c + t) 1 0 := by
      convert (hasDerivAt_const (x := (0 : ℝ)) c).add (hasDerivAt_id 0) using 1
      simp
    apply hlin.hasDerivWithinAt.congr
    · intro t ht
      rw [max_eq_right]
      simp only [mem_Ici] at ht
      linarith
    · rw [max_eq_right (by simpa using hc)]
  · rw [if_neg hc]
    have hcneg : c < 0 := lt_of_not_ge hc
    have hnhds : ∀ᶠ t in 𝓝 (0 : ℝ), t < -c :=
      Iio_mem_nhds (neg_pos.mpr hcneg)
    have htlt : ∀ᶠ t in 𝓝[Ici 0] (0 : ℝ), t < -c :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hnhds
    have heq : (fun t : ℝ => max 0 (c + t)) =ᶠ[𝓝[Ici 0] 0]
        (fun _ : ℝ => 0) := by
      filter_upwards [htlt] with t ht
      rw [max_eq_left]
      linarith
    exact (hasDerivAt_const (x := (0 : ℝ)) 0).hasDerivWithinAt.congr_of_eventuallyEq
      heq (by simp [max_eq_left hcneg.le])

/-- Along `(L,x) ↦ (L+t,x+t)`, the moving tent centre is fixed and only its radius grows. -/
theorem rectangularMovingPrimeTent_diagonal_path
    {k : ℝ} (hk : 0 < k) (L x t : ℝ) :
    rectangularMovingPrimeTent (L + t) (Real.exp (x + t)) k =
      max 0 ((L - |Real.log k - x + L|) + t) := by
  rw [rectangularMovingPrimeTent, Real.log_div (ne_of_gt hk)
    (ne_of_gt (Real.exp_pos (x + t))), Real.log_exp]
  congr 2
  ring_nf

/-- One prime tent contributes one exactly when its logarithm lies in the closed shell. -/
theorem hasDerivWithinAt_rectangularMovingPrimeTent_diagonal
    {k : ℝ} (hk : 0 < k) (L x : ℝ) :
    HasDerivWithinAt
      (fun t : ℝ => rectangularMovingPrimeTent (L + t) (Real.exp (x + t)) k)
      (if |Real.log k - x + L| ≤ L then 1 else 0) (Ici 0) 0 := by
  have h := hasDerivWithinAt_max_zero_const_add_right
    (L - |Real.log k - x + L|)
  have hcoef : (if 0 ≤ L - |Real.log k - x + L| then (1 : ℝ) else 0) =
      if |Real.log k - x + L| ≤ L then 1 else 0 := by
    simp only [sub_nonneg]
  rw [hcoef] at h
  apply h.congr
  · intro t _
    exact rectangularMovingPrimeTent_diagonal_path hk L x t
  · exact rectangularMovingPrimeTent_diagonal_path hk L x 0

/-- Finite von Mangoldt pairing of the diagonal tent derivative. -/
theorem hasDerivWithinAt_rectangularMovingPrimeTentSum_diagonal
    (L x : ℝ) (K : ℕ) :
    HasDerivWithinAt
      (fun t : ℝ =>
        rectangularMovingPrimeTentSum (L + t) (Real.exp (x + t)) K)
      (∑ k ∈ Finset.Icc 2 K,
        ArithmeticFunction.vonMangoldt k / Real.sqrt k *
          (if |Real.log k - x + L| ≤ L then 1 else 0))
      (Ici 0) 0 := by
  have hsum := HasDerivWithinAt.sum (u := Finset.Icc 2 K)
    (A := fun k t =>
      ArithmeticFunction.vonMangoldt k / Real.sqrt k *
        rectangularMovingPrimeTent (L + t) (Real.exp (x + t)) k)
    (A' := fun k =>
      ArithmeticFunction.vonMangoldt k / Real.sqrt k *
        (if |Real.log k - x + L| ≤ L then 1 else 0))
    (x := (0 : ℝ)) (s := Ici 0) (fun k hk => by
      have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
      have hkpos : (0 : ℝ) < k := by positivity
      exact (hasDerivWithinAt_rectangularMovingPrimeTent_diagonal hkpos L x).const_mul
        (ArithmeticFunction.vonMangoldt k / Real.sqrt k))
  have hfun :
      (∑ k ∈ Finset.Icc 2 K, fun t : ℝ =>
        ArithmeticFunction.vonMangoldt k / Real.sqrt k *
          rectangularMovingPrimeTent (L + t) (Real.exp (x + t)) k) =
      fun t : ℝ => rectangularMovingPrimeTentSum (L + t) (Real.exp (x + t)) K := by
    funext t
    simp only [rectangularMovingPrimeTentSum]
    rw [Finset.sum_apply]
  rw [hfun] at hsum
  exact hsum

/-- The absolute-value tent condition is the corresponding closed multiplicative shell. -/
theorem abs_log_shell_iff
    {k : ℝ} (hk : 0 < k) (L x : ℝ) :
    |Real.log k - x + L| ≤ L ↔
      Real.exp (x - 2 * L) ≤ k ∧ k ≤ Real.exp x := by
  rw [abs_le]
  constructor
  · rintro ⟨hlow, hupp⟩
    have hlogLow : x - 2 * L ≤ Real.log k := by linarith
    have hlogUpp : Real.log k ≤ x := by linarith
    constructor
    · have h := Real.exp_le_exp.mpr hlogLow
      rwa [Real.exp_log hk] at h
    · have h := Real.exp_le_exp.mpr hlogUpp
      rwa [Real.exp_log hk] at h
  · rintro ⟨hlow, hupp⟩
    have hlogLow : x - 2 * L ≤ Real.log k := by
      apply Real.exp_le_exp.mp
      rwa [Real.exp_log hk]
    have hlogUpp : Real.log k ≤ x := by
      apply Real.exp_le_exp.mp
      rwa [Real.exp_log hk]
    constructor <;> linarith

/-- Growing and decaying polar value paired with the moving rectangular prime tent. -/
noncomputable def rectangularAdjacentPolarValue (L x : ℝ) : ℝ :=
  4 * rectangularPolarAlpha L ^ 2 * Real.exp (x / 2) +
    4 * rectangularPolarBeta L ^ 2 * Real.exp (-x / 2)

/-- Exact diagonal polar derivative. -/
theorem hasDerivAt_rectangularAdjacentPolarValue_diagonal (L x : ℝ) :
    HasDerivAt
      (fun t : ℝ => rectangularAdjacentPolarValue (L + t) (x + t))
      (2 * (1 - Real.exp (-L)) * Real.exp (x / 2) +
        2 * (Real.exp L - 1) * Real.exp (-x / 2)) 0 := by
  unfold rectangularAdjacentPolarValue rectangularPolarAlpha rectangularPolarBeta
  have hLt : HasDerivAt (fun t : ℝ => L + t) 1 0 := by
    convert (hasDerivAt_const (x := (0 : ℝ)) L).add (hasDerivAt_id 0) using 1
    simp
  have hXt : HasDerivAt (fun t : ℝ => x + t) 1 0 := by
    convert (hasDerivAt_const (x := (0 : ℝ)) x).add (hasDerivAt_id 0) using 1
    simp
  have hα : HasDerivAt (fun t : ℝ => 1 - Real.exp (-(L + t) / 2))
      (Real.exp (-L / 2) / 2) 0 := by
    convert (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub
      ((hLt.neg.div_const 2).exp) using 1
    all_goals simp
    all_goals ring
  have hβ : HasDerivAt (fun t : ℝ => Real.exp ((L + t) / 2) - 1)
      (Real.exp (L / 2) / 2) 0 := by
    convert ((hLt.div_const 2).exp).sub
      (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)) using 1
    all_goals simp
    all_goals ring
  have hxpos : HasDerivAt (fun t : ℝ => Real.exp ((x + t) / 2))
      (Real.exp (x / 2) / 2) 0 := by
    convert (hXt.div_const 2).exp using 1
    all_goals simp
    all_goals ring
  have hxneg : HasDerivAt (fun t : ℝ => Real.exp (-(x + t) / 2))
      (-Real.exp (-x / 2) / 2) 0 := by
    convert (hXt.neg.div_const 2).exp using 1
    all_goals simp
    all_goals ring
  have h := (((hα.pow 2).mul hxpos).const_mul 4).add
    (((hβ.pow 2).mul hxneg).const_mul 4)
  convert h using 1
  · funext t
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
    ring
  · simp only [Pi.pow_apply, add_zero]
    ring_nf
    rw [show Real.exp (L * (-1 / 2)) ^ 2 = Real.exp (-L) by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring,
      show Real.exp (L * (1 / 2)) ^ 2 = Real.exp L by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    ring

/-- To the right of an integer logarithmic sample, the exponential floor is locally constant. -/
theorem eventually_natFloor_exp_log_add_eq
    {n : ℕ} (hn : 0 < n) :
    (fun t : ℝ => ⌊Real.exp (Real.log n + t)⌋₊) =ᶠ[𝓝[Ici 0] 0]
      (fun _ : ℝ => n) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1real : (0 : ℝ) < n + 1 := by positivity
  have hloglt : Real.log n < Real.log (n + 1) :=
    Real.strictMonoOn_log hnreal hn1real (by exact_mod_cast Nat.lt_succ_self n)
  have hnhds : ∀ᶠ t in 𝓝 (0 : ℝ),
      t < Real.log (n + 1) - Real.log n :=
    Iio_mem_nhds (sub_pos.mpr hloglt)
  have htlt : ∀ᶠ t in 𝓝[Ici 0] (0 : ℝ),
      t < Real.log (n + 1) - Real.log n :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hnhds
  filter_upwards [htlt, eventually_mem_nhdsWithin] with t ht htnonneg
  simp only [mem_Ici] at htnonneg
  apply (Nat.floor_eq_iff (Real.exp_pos _).le).mpr
  constructor
  · have h := Real.exp_le_exp.mpr (by linarith : Real.log n ≤ Real.log n + t)
    rwa [Real.exp_log hnreal] at h
  · have h := Real.exp_lt_exp.mpr
      (by linarith : Real.log n + t < Real.log (n + 1))
    rw [Real.exp_log hn1real] at h
    exact_mod_cast h

/-- Critical-weight von Mangoldt mass in the closed shell selected by a rectangular tent. -/
noncomputable def rectangularClosedPrimeShellValue (L x : ℝ) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 K,
    ArithmeticFunction.vonMangoldt k / Real.sqrt k *
      (if |Real.log k - x + L| ≤ L then 1 else 0)

/-- The right diagonal derivative of the adjacent-block source is polar slope minus the exact
closed prime shell. -/
theorem hasDerivWithinAt_criticalMellinAdjacentBlock_diagonal_logSample
    {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 ≤ L) :
    HasDerivWithinAt
      (fun t : ℝ =>
        criticalMellinAdjacentBlock (L + t) (Real.log n + t))
      (2 * (1 - Real.exp (-L)) * Real.sqrt n +
          2 * (Real.exp L - 1) / Real.sqrt n -
        rectangularClosedPrimeShellValue L (Real.log n) n)
      (Ici 0) 0 := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have htent := hasDerivWithinAt_rectangularMovingPrimeTentSum_diagonal
    L (Real.log n) n
  have hpolar :=
    (hasDerivAt_rectangularAdjacentPolarValue_diagonal L
      (Real.log n)).hasDerivWithinAt (s := Ici 0)
  have hrhs := htent.neg.add hpolar
  have hsqrt : Real.exp (Real.log n / 2) = Real.sqrt n := by
    rw [← Real.log_sqrt hnreal.le, Real.exp_log (Real.sqrt_pos.mpr hnreal)]
  have hsqrtInv : Real.exp (-Real.log n / 2) = (Real.sqrt n)⁻¹ := by
    rw [show -Real.log n / 2 = -(Real.log n / 2) by ring,
      Real.exp_neg, hsqrt]
  have hderiv :
      -rectangularClosedPrimeShellValue L (Real.log n) n +
          (2 * (1 - Real.exp (-L)) * Real.exp (Real.log n / 2) +
            2 * (Real.exp L - 1) * Real.exp (-Real.log n / 2)) =
        2 * (1 - Real.exp (-L)) * Real.sqrt n +
            2 * (Real.exp L - 1) / Real.sqrt n -
          rectangularClosedPrimeShellValue L (Real.log n) n := by
    rw [hsqrt, hsqrtInv, div_eq_mul_inv]
    ring
  rw [show (∑ k ∈ Finset.Icc 2 n,
      ArithmeticFunction.vonMangoldt k / Real.sqrt k *
        (if |Real.log k - Real.log n + L| ≤ L then 1 else 0)) =
      rectangularClosedPrimeShellValue L (Real.log n) n by rfl,
    hderiv] at hrhs
  have hfloor := eventually_natFloor_exp_log_add_eq hn
  have heq :
      (fun t : ℝ =>
        criticalMellinAdjacentBlock (L + t) (Real.log n + t)) =ᶠ[𝓝[Ici 0] 0]
      (fun t : ℝ =>
        -rectangularMovingPrimeTentSum (L + t)
            (Real.exp (Real.log n + t)) n +
          rectangularAdjacentPolarValue (L + t) (Real.log n + t)) := by
    filter_upwards [hfloor, eventually_mem_nhdsWithin] with t hfloorT ht
    simp only [mem_Ici] at ht
    rw [criticalMellinAdjacentBlock_eq_movingTent_polar
      (Real.log n + t) (L + t) (by linarith), hfloorT]
    unfold rectangularAdjacentPolarValue
    ring
  apply hrhs.congr_of_eventuallyEq heq
  simp only [add_zero, Pi.add_apply, Pi.neg_apply]
  rw [criticalMellinAdjacentBlock_eq_movingTent_polar (Real.log n) L hL,
    Real.exp_log hnreal, Nat.floor_natCast]
  unfold rectangularAdjacentPolarValue
  ring

/-- The closed derivative shell contains the requested half-open dyadic shell; the only possible
extra value is the lower endpoint. -/
theorem dyadicWeightedPrimeWindow_le_rectangularClosedPrimeShellValue
    {n : ℕ} (hn : 4 ≤ n) :
    dyadicWeightedPrimeWindow n ≤
      rectangularClosedPrimeShellValue (Real.log 2 / 2) (Real.log n) n := by
  let p : ℕ → Prop := fun k =>
    |Real.log k - Real.log n + Real.log 2 / 2| ≤ Real.log 2 / 2
  let w : ℕ → ℝ := fun k =>
    ArithmeticFunction.vonMangoldt k / Real.sqrt k
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hexplower :
      Real.exp (Real.log n - 2 * (Real.log 2 / 2)) = (n : ℝ) / 2 := by
    rw [show Real.log n - 2 * (Real.log 2 / 2) = Real.log n - Real.log 2 by ring,
      Real.exp_sub, Real.exp_log hnreal, Real.exp_log htwo]
  have hclosed :
      rectangularClosedPrimeShellValue (Real.log 2 / 2) (Real.log n) n =
        ∑ k ∈ (Finset.Icc 2 n).filter p, w k := by
    rw [rectangularClosedPrimeShellValue]
    calc
      (∑ k ∈ Finset.Icc 2 n,
          ArithmeticFunction.vonMangoldt k / Real.sqrt k *
            (if p k then 1 else 0)) =
          ∑ k ∈ Finset.Icc 2 n, if p k then w k else 0 := by
            apply Finset.sum_congr rfl
            intro k _
            by_cases hk : p k <;> simp [hk, w]
      _ = ∑ k ∈ (Finset.Icc 2 n).filter p, w k := by
        rw [Finset.sum_filter]
  rw [hclosed, dyadicWeightedPrimeWindow]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [Finset.mem_Ioc] at hk
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have hk2 : 2 ≤ k := by omega
    have hkpos : (0 : ℝ) < k := by positivity
    refine ⟨⟨hk2, hk.2⟩, ?_⟩
    dsimp only [p]
    apply (abs_log_shell_iff hkpos (Real.log 2 / 2) (Real.log n)).mpr
    rw [hexplower, Real.exp_log hnreal]
    constructor
    · have hnk : n < 2 * k := by omega
      have hnkReal : (n : ℝ) < 2 * k := by exact_mod_cast hnk
      linarith
    · exact_mod_cast hk.2
  · intro k _ _
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg k)

/-- Explicit value of the dyadic right diagonal adjacent-block derivative. -/
noncomputable def dyadicAdjacentBlockDiagonalRightSlope (n : ℕ) : ℝ :=
  2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
      2 * (Real.sqrt 2 - 1) / Real.sqrt n -
    rectangularClosedPrimeShellValue (Real.log 2 / 2) (Real.log n) n

/-- At dyadic width, the rectangular source slope has exactly the target main coefficient. -/
theorem hasDerivWithinAt_dyadicAdjacentBlock_diagonal_logSample
    {n : ℕ} (hn : 0 < n) :
    HasDerivWithinAt
      (fun t : ℝ =>
        criticalMellinAdjacentBlock (Real.log 2 / 2 + t) (Real.log n + t))
      (dyadicAdjacentBlockDiagonalRightSlope n) (Ici 0) 0 := by
  have h := hasDerivWithinAt_criticalMellinAdjacentBlock_diagonal_logSample
    hn (L := Real.log 2 / 2) (by positivity)
  have hexpL : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
    rw [← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.exp_log (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))]
  have hexpNegL : Real.exp (-(Real.log 2 / 2)) = (Real.sqrt 2)⁻¹ := by
    rw [Real.exp_neg, hexpL]
  unfold dyadicAdjacentBlockDiagonalRightSlope
  simpa only [hexpNegL, hexpL] using h

/-- A lower bound for one right diagonal slope of the rectangular adjacent-block value directly
discharges the sharp dyadic von Mangoldt upper bound. -/
theorem dyadicWeightedPrimeWindow_upper_of_adjacentBlockDiagonalRightSlope_lower
    {n : ℕ} (hn : 4 ≤ n) (C epsilon : ℝ)
    (hslope :
      2 * (Real.sqrt 2 - 1) / Real.sqrt n - C * (n : ℝ) ^ epsilon ≤
        dyadicAdjacentBlockDiagonalRightSlope n) :
    dyadicWeightedPrimeWindow n ≤
      2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
        C * (n : ℝ) ^ epsilon := by
  have hwindow := dyadicWeightedPrimeWindow_le_rectangularClosedPrimeShellValue hn
  unfold dyadicAdjacentBlockDiagonalRightSlope at hslope
  linarith

/-- The eventual all-epsilon diagonal-slope estimate discharges the existing sharp-window gate
and therefore proves RH.  The hypothesis is a relation among values of the rectangular source,
not a separately bundled prime-window proposition. -/
theorem riemannHypothesis_of_eventually_dyadicAdjacentBlockDiagonalRightSlope_lower
    {N : ℕ} (hN : 4 ≤ N)
    (hslope : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
        2 * (Real.sqrt 2 - 1) / Real.sqrt n - C * (n : ℝ) ^ epsilon ≤
          dyadicAdjacentBlockDiagonalRightSlope n) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_eventually_dyadicWeightedPrimeWindow_upper
  intro epsilon hepsilon
  obtain ⟨C, hC, htail⟩ := hslope epsilon hepsilon
  refine ⟨C, hC, fun n hn => ?_⟩
  exact dyadicWeightedPrimeWindow_upper_of_adjacentBlockDiagonalRightSlope_lower
    (hN.trans hn) C epsilon (htail n hn)

end RHTower
