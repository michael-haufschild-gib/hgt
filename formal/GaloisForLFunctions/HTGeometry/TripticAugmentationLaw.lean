import GaloisForLFunctions.HTGeometry.RectangleResidueTheorem
import GaloisForLFunctions.HTGeometry.MeromorphicLogDerivResidue

/-!
# The mixed-value augmentation law

A `1`-periodic meromorphic function `U` whose `τ`-difference is the constant `C` has total
order-one residue `-C/(2πi)` over one period parallelogram of the lattice `ℤ + ℤτ`.

Because `1` lies in the lattice, the axis-parallel rectangle of width `1` and height `Im τ` is
already a fundamental domain, so no genuinely oblique contour is needed.  On its boundary the two
vertical edges cancel by `1`-periodicity, while the top horizontal edge differs from the bottom one
by the constant `C` after a real translation that `1`-periodicity absorbs; the boundary integral is
therefore `-C`, and the residue theorem converts it into the total residue.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Set Topology Filter MeasureTheory intervalIntegral
open scoped Interval BigOperators

/-- Two points differing by a real translation and the period `τ`. -/
private theorem shift_decomp (x y₀ : ℝ) (τ : ℂ) :
    ((x : ℂ) + ((y₀ + τ.im : ℝ) : ℂ) * I) = (((x - τ.re : ℝ) : ℂ) + (y₀ : ℂ) * I) + τ := by
  apply Complex.ext <;> simp

/-- The two vertical edges of a width-`1` rectangle cancel for a `1`-periodic function. -/
theorem vIntegral_period_eq {U : ℂ → ℂ} (hper : ∀ s : ℂ, U (s + 1) = U s) (x y₁ y₂ : ℝ) :
    VIntegral U (x + 1) y₁ y₂ = VIntegral U x y₁ y₂ := by
  have hpt : ∀ y : ℝ, U (((x + 1 : ℝ) : ℂ) + (y : ℂ) * I) = U ((x : ℂ) + (y : ℂ) * I) := by
    intro y
    have : ((x + 1 : ℝ) : ℂ) + (y : ℂ) * I = (((x : ℂ) + (y : ℂ) * I) + 1) := by
      push_cast; ring
    rw [this, hper]
  simp only [VIntegral]
  congr 1
  exact intervalIntegral.integral_congr fun y _ => hpt y

/-- **The horizontal edges differ by the mixed constant.**  For a `1`-periodic `U` with
`U(s + τ) = U s + C`, the top edge of a width-`1`, height-`Im τ` rectangle exceeds the bottom edge
by exactly `C`. -/
theorem hIntegral_top_eq {U : ℂ → ℂ} {C τ : ℂ}
    (hper : ∀ s : ℂ, U (s + 1) = U s) (hshift : ∀ s : ℂ, U (s + τ) = U s + C)
    (x₀ y₀ : ℝ)
    (hint : IntervalIntegrable (fun x : ℝ => U ((x : ℂ) + (y₀ : ℂ) * I)) volume
      (x₀ - τ.re) (x₀ - τ.re + 1)) :
    HIntegral U x₀ (x₀ + 1) (y₀ + τ.im) = HIntegral U x₀ (x₀ + 1) y₀ + C := by
  have hbot : Function.Periodic (fun x : ℝ => U ((x : ℂ) + (y₀ : ℂ) * I)) 1 := by
    intro x
    show U (((x + 1 : ℝ) : ℂ) + (y₀ : ℂ) * I) = U ((x : ℂ) + (y₀ : ℂ) * I)
    have hx : ((x + 1 : ℝ) : ℂ) + (y₀ : ℂ) * I = (((x : ℂ) + (y₀ : ℂ) * I) + 1) := by
      push_cast; ring
    rw [hx, hper]
  have hpt : ∀ x : ℝ, U ((x : ℂ) + ((y₀ + τ.im : ℝ) : ℂ) * I)
      = U (((x - τ.re : ℝ) : ℂ) + (y₀ : ℂ) * I) + C := by
    intro x
    rw [shift_decomp x y₀ τ, hshift]
  simp only [HIntegral]
  rw [intervalIntegral.integral_congr (g := fun x : ℝ =>
      U (((x - τ.re : ℝ) : ℂ) + (y₀ : ℂ) * I) + C) fun x _ => hpt x]
  rw [intervalIntegral.integral_add
    (by simpa using (hint.comp_sub_right τ.re).mono_set (by
      rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
      intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩))
    intervalIntegrable_const]
  rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => U ((x : ℂ) + (y₀ : ℂ) * I)) τ.re]
  have hshiftInt : ∫ x in (x₀ - τ.re)..(x₀ + 1 - τ.re), U ((x : ℂ) + (y₀ : ℂ) * I)
      = ∫ x in x₀..(x₀ + 1), U ((x : ℂ) + (y₀ : ℂ) * I) := by
    have h1 : x₀ + 1 - τ.re = (x₀ - τ.re) + 1 := by ring
    rw [h1]
    exact hbot.intervalIntegral_add_eq (x₀ - τ.re) x₀
  rw [hshiftInt]
  simp

/-- **The mixed-value augmentation law.**  A `1`-periodic meromorphic function whose `τ`-difference
is the constant `C` has total order-one residue `-C/(2πi)` over one fundamental rectangle of the
lattice `ℤ + ℤτ`. -/
theorem triptic_augmentation_law {U : ℂ → ℂ} {C τ : ℂ} {x₀ y₀ : ℝ} {P : Finset ℂ}
    (hτ : 0 < τ.im)
    (hper : ∀ s : ℂ, U (s + 1) = U s) (hshift : ∀ s : ℂ, U (s + τ) = U s + C)
    (hP : ∀ p ∈ P,
      Rectangle ((x₀ : ℂ) + (y₀ : ℂ) * I) (((x₀ + 1 : ℝ) : ℂ) + ((y₀ + τ.im : ℝ) : ℂ) * I) ∈ 𝓝 p)
    (hmero : ∀ p ∈ P, MeromorphicAt U p)
    (hoff : ∀ s ∈ Rectangle ((x₀ : ℂ) + (y₀ : ℂ) * I)
        (((x₀ + 1 : ℝ) : ℂ) + ((y₀ + τ.im : ℝ) : ℂ) * I), s ∉ P → AnalyticAt ℂ U s) :
    ∑ p ∈ P, laurentCoeff U p (-1) = -C / (2 * Real.pi * I) := by
  set z : ℂ := (x₀ : ℂ) + (y₀ : ℂ) * I with hz
  set w : ℂ := ((x₀ + 1 : ℝ) : ℂ) + ((y₀ + τ.im : ℝ) : ℂ) * I with hw
  have hzre : z.re = x₀ := by simp [hz]
  have hzim : z.im = y₀ := by simp [hz]
  have hwre : w.re = x₀ + 1 := by simp [hw]
  have hwim : w.im = y₀ + τ.im := by simp [hw]
  have hres := rectangleIntegral'_eq_sum_laurentCoeff (f := U) (z := z) (w := w) (P := P)
    (by rw [hzre, hwre]; linarith) (by rw [hzim, hwim]; linarith) hP hmero hoff
  -- integrability along the bottom edge, transported by periodicity
  have hborderNotP : ∀ s ∈ RectangleBorder z w, s ∉ P := by
    intro s hs hsP
    obtain ⟨hre, him⟩ := rectangle_mem_nhds_iff.mp (hP s hsP)
    exact Set.disjoint_left.mp (rectangleBorder_disjoint_singleton
      ⟨Set.ne_left_of_mem_uIoo hre, Set.ne_right_of_mem_uIoo hre,
        Set.ne_left_of_mem_uIoo him, Set.ne_right_of_mem_uIoo him⟩) hs rfl
  have hbotcont : ContinuousOn (fun x : ℝ => U ((x : ℂ) + (y₀ : ℂ) * I)) (Set.uIcc x₀ (x₀ + 1)) := by
    intro t ht
    have hmem : ((t : ℂ) + (y₀ : ℂ) * I) ∈ RectangleBorder z w := by
      have hmt := mapsTo_rectangleBorder_left_im z w (by rw [hzre, hwre]; exact ht)
      rwa [hzim] at hmt
    refine ContinuousAt.continuousWithinAt ?_
    have hU : ContinuousAt U ((t : ℂ) + (y₀ : ℂ) * I) :=
      (hoff _ (rectangleBorder_subset_rectangle z w hmem) (hborderNotP _ hmem)).continuousAt
    have hpath : ContinuousAt (fun x : ℝ => ((x : ℂ) + (y₀ : ℂ) * I)) t := by fun_prop
    exact ContinuousAt.comp (g := U) (f := fun x : ℝ => ((x : ℂ) + (y₀ : ℂ) * I)) hU hpath
  have hbotper : Function.Periodic (fun x : ℝ => U ((x : ℂ) + (y₀ : ℂ) * I)) 1 := by
    intro x
    show U (((x + 1 : ℝ) : ℂ) + (y₀ : ℂ) * I) = U ((x : ℂ) + (y₀ : ℂ) * I)
    have hx : ((x + 1 : ℝ) : ℂ) + (y₀ : ℂ) * I = (((x : ℂ) + (y₀ : ℂ) * I) + 1) := by
      push_cast; ring
    rw [hx, hper]
  have hint : IntervalIntegrable (fun x : ℝ => U ((x : ℂ) + (y₀ : ℂ) * I)) volume
      (x₀ - τ.re) (x₀ - τ.re + 1) :=
    hbotper.intervalIntegrable one_ne_zero hbotcont.intervalIntegrable _ _
  have hbdry : RectangleIntegral U z w = -C := by
    rw [RectangleIntegral, hzre, hzim, hwre, hwim,
      hIntegral_top_eq hper hshift x₀ y₀ hint, vIntegral_period_eq hper x₀ y₀ (y₀ + τ.im)]
    ring
  rw [← hres, RectangleIntegral', hbdry, smul_eq_mul]
  field_simp

/-! ### The exact charge law -/

/-- **The exact charge law.**  If the multiplicative cocycle of `Y` is `c·exp(2πinz)`, so that the
logarithmic derivative gains the constant `2πin` under the period `τ`, then the total zero/pole
order of `Y` over one fundamental rectangle of `ℤ + ℤτ` is `-n`.

A nonzero Fourier degree therefore forces nonzero total boundary charge, and conversely a divisor of
degree zero forces the exponential character to be trivial. -/
theorem triptic_charge_law {Y : ℂ → ℂ} {τ : ℂ} {n : ℤ} {x₀ y₀ : ℝ} {P : Finset ℂ}
    {ord : ℂ → ℤ}
    (hτ : 0 < τ.im)
    (hper : ∀ s : ℂ, logDeriv Y (s + 1) = logDeriv Y s)
    (hshift : ∀ s : ℂ, logDeriv Y (s + τ) = logDeriv Y s + 2 * Real.pi * I * (n : ℂ))
    (hP : ∀ p ∈ P,
      Rectangle ((x₀ : ℂ) + (y₀ : ℂ) * I) (((x₀ + 1 : ℝ) : ℂ) + ((y₀ + τ.im : ℝ) : ℂ) * I) ∈ 𝓝 p)
    (hmero : ∀ p ∈ P, MeromorphicAt (logDeriv Y) p)
    (hoff : ∀ s ∈ Rectangle ((x₀ : ℂ) + (y₀ : ℂ) * I)
        (((x₀ + 1 : ℝ) : ℂ) + ((y₀ + τ.im : ℝ) : ℂ) * I), s ∉ P → AnalyticAt ℂ (logDeriv Y) s)
    (hY : ∀ p ∈ P, MeromorphicAt Y p)
    (hord : ∀ p ∈ P, meromorphicOrderAt Y p = ord p) :
    ∑ p ∈ P, ord p = -n := by
  have hres : ∑ p ∈ P, laurentCoeff (logDeriv Y) p (-1)
      = -(2 * Real.pi * I * (n : ℂ)) / (2 * Real.pi * I) :=
    triptic_augmentation_law hτ hper hshift hP hmero hoff
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hden : (2 : ℂ) * Real.pi * I ≠ 0 := by
    simp [hpi, hI]
  have hrhs : -(2 * Real.pi * I * (n : ℂ)) / (2 * Real.pi * I) = -(n : ℂ) := by
    field_simp
  have hsum : ∑ p ∈ P, ((ord p : ℤ) : ℂ) = -(n : ℂ) := by
    rw [← hrhs, ← hres]
    refine Finset.sum_congr rfl fun p hp => ?_
    exact (laurentCoeff_logDeriv_eq_order (hY p hp) (hord p hp)).symm
  have hcast : ((∑ p ∈ P, ord p : ℤ) : ℂ) = ((-n : ℤ) : ℂ) := by
    push_cast
    exact hsum
  exact_mod_cast hcast

end GaloisForLFunctions.HTGeometry
