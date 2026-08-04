import GaloisForLFunctions.RHTower.Sieve.ContourEdgesResidue

/-!
# The mass of the cutoff

The residue of the Chebyshev contour is `2πi·W(1)`, and `W(1)` is the Mellin transform at `s = 1`,
which is just the integral of the cutoff:

    W(1) = ∫_0^∞ w(x) dx.

Since `w` is `1` below `N`, `0` above `N + H`, and between `0` and `1` in between, that mass lies
between `N` and `N + H` — so the main term of the smoothed Chebyshev sum is `N + O(H)`, which is the
statement `ψ(x) ~ x`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Set GaloisForLFunctions.HTGeometry

/-- **The transform at `s = 1` is the mass of the cutoff.** -/
theorem mellin_smoothWeight_one {N H : ℝ} :
    mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
      = ∫ x in Ioi (0 : ℝ), ((smoothWeight N H x : ℝ) : ℂ) := by
  rw [mellin_smoothWeight_eq]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  rw [show (1 : ℂ) - 1 = 0 by ring, Complex.cpow_zero, one_mul]

/-- The cutoff's mass is at most `N + H`. -/
theorem integral_smoothWeight_le {N H : ℝ} (hN : 0 ≤ N) (hH : 0 < H) :
    (∫ x in Ioi (0 : ℝ), smoothWeight N H x) ≤ N + H := by
  have hNH : (0 : ℝ) ≤ N + H := by linarith
  have hcont : Continuous (fun x : ℝ => smoothWeight N H x) :=
    (smoothWeight_contDiff N H (n := 0)).continuous
  have h1 : IntegrableOn (fun x : ℝ => smoothWeight N H x) (Ioc 0 (N + H)) :=
    hcont.integrableOn_Ioc
  have h2 : IntegrableOn (fun x : ℝ => smoothWeight N H x) (Ioi (N + H)) := by
    refine IntegrableOn.congr_fun
      (integrableOn_zero (μ := (volume : Measure ℝ)) (s := Ioi (N + H))) ?_
      measurableSet_Ioi
    intro x hx
    exact (smoothWeight_eq_zero hH (le_of_lt hx)).symm
  have hsplitset : Ioc (0 : ℝ) (N + H) ∪ Ioi (N + H) = Ioi (0 : ℝ) :=
    Ioc_union_Ioi_eq_Ioi hNH
  rw [← hsplitset, setIntegral_union (by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact absurd hx.2 (not_le.mpr hx')) measurableSet_Ioi h1 h2]
  have hzero : ∫ x in Ioi (N + H), smoothWeight N H x = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    exact smoothWeight_eq_zero hH (le_of_lt hx)
  rw [hzero, add_zero]
  have hle : ∫ x in Ioc (0 : ℝ) (N + H), smoothWeight N H x
      ≤ ∫ _x in Ioc (0 : ℝ) (N + H), (1 : ℝ) :=
    setIntegral_mono_on h1 (continuous_const.integrableOn_Ioc)
      measurableSet_Ioc (fun x _ => smoothWeight_le_one N H x)
  refine le_trans hle (le_of_eq ?_)
  rw [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ioc, sub_zero,
    max_eq_left hNH]

/-- The cutoff is integrable on the positive half-line. -/
theorem integrableOn_smoothWeight_Ioi {N H : ℝ} (hN : 0 ≤ N) (hH : 0 < H) :
    IntegrableOn (fun x : ℝ => smoothWeight N H x) (Ioi 0) := by
  have hNH : (0 : ℝ) ≤ N + H := by linarith
  have hcont : Continuous (fun x : ℝ => smoothWeight N H x) :=
    (smoothWeight_contDiff N H (n := 0)).continuous
  have h1 : IntegrableOn (fun x : ℝ => smoothWeight N H x) (Ioc 0 (N + H)) :=
    hcont.integrableOn_Ioc
  have h2 : IntegrableOn (fun x : ℝ => smoothWeight N H x) (Ioi (N + H)) := by
    refine IntegrableOn.congr_fun
      (integrableOn_zero (μ := (volume : Measure ℝ)) (s := Ioi (N + H))) ?_
      measurableSet_Ioi
    intro x hx
    exact (smoothWeight_eq_zero hH (le_of_lt hx)).symm
  have hu := h1.union h2
  rwa [Ioc_union_Ioi_eq_Ioi hNH] at hu

/-- The cutoff's mass is at least `N`. -/
theorem le_integral_smoothWeight {N H : ℝ} (hN : 0 ≤ N) (hH : 0 < H) :
    N ≤ ∫ x in Ioi (0 : ℝ), smoothWeight N H x := by
  have hint := integrableOn_smoothWeight_Ioi hN hH
  have h1 : IntegrableOn (fun x : ℝ => smoothWeight N H x) (Ioc 0 N) :=
    hint.mono_set fun x hx => hx.1
  have h2 : IntegrableOn (fun x : ℝ => smoothWeight N H x) (Ioi N) :=
    hint.mono_set fun x hx => lt_of_le_of_lt hN hx
  have hsplitset : Ioc (0 : ℝ) N ∪ Ioi N = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi hN
  rw [← hsplitset, setIntegral_union (by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact absurd hx.2 (not_le.mpr hx')) measurableSet_Ioi h1 h2]
  have hone : ∫ x in Ioc (0 : ℝ) N, smoothWeight N H x = N := by
    have hcongr : ∫ x in Ioc (0 : ℝ) N, smoothWeight N H x
        = ∫ _x in Ioc (0 : ℝ) N, (1 : ℝ) := by
      refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
      exact smoothWeight_eq_one hH hx.2
    rw [hcongr, setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ioc, sub_zero,
      max_eq_left hN]
  have htail : (0 : ℝ) ≤ ∫ x in Ioi N, smoothWeight N H x :=
    setIntegral_nonneg measurableSet_Ioi fun x _ => smoothWeight_nonneg N H x
  linarith

end RHTower.Sieve
