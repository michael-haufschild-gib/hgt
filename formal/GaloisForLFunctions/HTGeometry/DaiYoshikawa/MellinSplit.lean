import GaloisForLFunctions.HTGeometry.DaiYoshikawa.MellinHalfLine

/-!
# Splitting a Mellin transform at `t = 1`

The analytic continuation of the spectral zeta function in Section 3.1 of Dai–Yoshikawa,
*Degeneration of Riemann surfaces and small eigenvalues of the Laplacian* (arXiv:2509.06151v2),
splits `∫_0^∞ (Θ(t) − h) t^{s−1} dt` at `t = 1` and subtracts the two-term expansion from the head.
The subtracted terms are elementary Mellin transforms,

```text
∫_0^(1 : ℕ) t^{-1} · t^{s−1} dt = 1/(s−1),        ∫_0^(1 : ℕ) t^{s−1} dt = 1/s ,
```

and they carry the two poles of `Γ(s)ζ(s)`, at `s = 1` and `s = 0`.  This file records the split
and those two evaluations.
-/

open MeasureTheory Set Filter Real Complex Topology

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

/-- The head Mellin integral as a set integral over `(0,1]`. -/
theorem mellinHead_eq_setIntegral (f : ℝ → ℂ) (s : ℂ) :
    mellinHead f s = ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • f t := by
  rw [mellinHead, mellin]
  have hcongr : ∀ t : ℝ, (t : ℂ) ^ (s - 1) • Set.indicator (Ioc (0 : ℝ) 1) f t
      = Set.indicator (Ioc (0 : ℝ) 1) (fun u : ℝ => (u : ℂ) ^ (s - 1) • f u) t := by
    intro t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]
  have hset : Ioi (0 : ℝ) ∩ Ioc (0 : ℝ) 1 = Ioc (0 : ℝ) 1 :=
    Set.inter_eq_self_of_subset_right fun t ht => ht.1
  simp only [hcongr]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc, hset]

/-- The tail Mellin integral as a set integral over `(1,∞)`. -/
theorem mellinTail_eq_setIntegral (f : ℝ → ℂ) (s : ℂ) :
    mellinTail f s = ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • f t := by
  rw [mellinTail, mellin]
  have hcongr : ∀ t : ℝ, (t : ℂ) ^ (s - 1) • Set.indicator (Ioi (1 : ℝ)) f t
      = Set.indicator (Ioi (1 : ℝ)) (fun u : ℝ => (u : ℂ) ^ (s - 1) • f u) t := by
    intro t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]
  have hset : Ioi (0 : ℝ) ∩ Ioi (1 : ℝ) = Ioi (1 : ℝ) := by
    refine Set.inter_eq_self_of_subset_right fun t ht => ?_
    exact lt_trans zero_lt_one (Set.mem_Ioi.mp ht)
  simp only [hcongr]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ioi, hset]

/-- **The Mellin transform splits at `t = 1`.** -/
theorem mellin_eq_mellinHead_add_mellinTail {f : ℝ → ℂ} {s : ℂ}
    (hhead : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t) (Ioc (0 : ℝ) 1) volume)
    (htail : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t) (Ioi (1 : ℝ)) volume) :
    mellin f s = mellinHead f s + mellinTail f s := by
  rw [mellinHead_eq_setIntegral, mellinTail_eq_setIntegral, mellin]
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi (1 : ℝ)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx' (not_lt.mpr hx.2)
  have hunion : Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi (by norm_num)
  have := MeasureTheory.setIntegral_union (μ := volume)
    (f := fun t : ℝ => (t : ℂ) ^ (s - 1) • f t) hdisj measurableSet_Ioi hhead htail
  rw [hunion] at this
  exact this

/-! ## The two subtracted terms -/

/-- `∫_0^(1 : ℕ) t^{s−1} dt = 1/s` for `Re s > 0`. -/
theorem mellinHead_one {s : ℂ} (hs : 0 < s.re) :
    mellinHead (fun _ => (1 : ℂ)) s = 1 / s :=
  (hasMellin_one_Ioc hs).2

/-- `∫_0^(1 : ℕ) t^{-1} t^{s−1} dt = 1/(s−1)` for `Re s > 1`. -/
theorem mellinHead_cpow_neg_one {s : ℂ} (hs : 1 < s.re) :
    mellinHead (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ)) s = 1 / (s - 1) := by
  have hre : 0 < s.re + ((-1 : ℂ)).re := by
    simp only [Complex.neg_re, Complex.one_re]
    linarith
  have h := (hasMellin_cpow_Ioc (-1 : ℂ) hre).2
  rw [mellinHead, h, sub_eq_add_neg]

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
